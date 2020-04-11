use std::rc::Rc;
use indexmap::{IndexMap, IndexSet};
use instant::{Duration, Instant};
use log::*;

use crate::{EGraph, Id, Language, Metadata, RecExpr, Rewrite, SearchMatches};

/** Faciliates running rewrites over an [`EGraph`].

One use for [`EGraph`]s is as the basis of a rewriting system.
Since an egraph never "forgets" state when applying a [`Rewrite`], you
can apply many rewrites many times quite efficiently.
After the egraph is "full" (the rewrites can no longer find new
equalities) or some other condition, the egraph compactly represents
many, many equivalent expressions.
At this point, the egraph is ready for extraction (see [`Extractor`])
which can pick the represented expression that's best according to
some cost function.

This technique is called
[equality saturation](https://www.cs.cornell.edu/~ross/publications/eqsat/)
in general.
However, there can be many challenges in implementing this "outer
loop" of applying rewrites, mostly revolving around which rules to run
and when to stop.

[`Runner`] is `egg`'s provided equality saturation engine that has
reasonable defaults and implements many useful things like saturation
checking, egraph size limits, and customizable rule
[scheduling](trait.RewriteScheduler.html).
Consider using [`Runner`] before rolling your own outer loop.

Here are some of the things [`Runner`] does for you:

- Saturation checking

  [`Runner`] checks to see if any of the rules added anything
  new to the [`EGraph`]. If none did, then it stops, returning
  [`StopReason::Saturated`](enum.StopReason.html#variant.Saturated).

- Iteration limits

  You can set a upper limit of iterations to do in case the search
  doesn't stop for some other reason. If this limit is hit, it stops with
  [`StopReason::IterationLimit`](enum.StopReason.html#variant.IterationLimit).

- [`EGraph`] size limit

  You can set a upper limit on the number of enodes in the egraph.
  If this limit is hit, it stops with
  [`StopReason::NodeLimit`](enum.StopReason.html#variant.NodeLimit).

- Time limit

  You can set a time limit on the runner.
  If this limit is hit, it stops with
  [`StopReason::TimeLimit`](enum.StopReason.html#variant.TimeLimit).

- Rule scheduling

  Some rules enable themselves, blowing up the [`EGraph`] and
  preventing other rewrites from running as many times.
  To prevent this, you can provide your own [`RewriteScheduler`] to
  govern when to run which rules.

  [`BackoffScheduler`] is the default scheduler.

[`Runner`] generates [`Iteration`]s that record some data about
each iteration.
You can add your own data to this by implementing the
[`IterationData`] trait.
[`Runner`] is generic over the [`IterationData`] that it will be in the
[`Iteration`]s, but by default it uses `()`.

[`Runner`]: struct.Runner.html
[`RewriteScheduler`]: trait.RewriteScheduler.html
[`Extractor`]: struct.Extractor.html
[`Rewrite`]: struct.Rewrite.html
[`BackoffScheduler`]: struct.BackoffScheduler.html
[`EGraph`]: struct.EGraph.html
[`Iteration`]: struct.Iteration.html
[`IterationData`]: trait.IterationData.html

# Example

```
use egg::{*, rewrite as rw};

define_language! {
    enum SimpleLanguage {
        Num(i32),
        Add = "+",
        Mul = "*",
        Symbol(String),
    }
}

let rules: &[Rewrite<SimpleLanguage, ()>] = &[
    rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),

    rw!("add-0"; "(+ ?a 0)" => "?a"),
    rw!("mul-0"; "(* ?a 0)" => "0"),
    rw!("mul-1"; "(* ?a 1)" => "?a"),
];

pub struct MyIterData {
    smallest_so_far: usize,
}

type MyRunner = Runner<SimpleLanguage, (), MyIterData>;

impl IterationData<SimpleLanguage, ()> for MyIterData {
    fn make(runner: &MyRunner) -> Self {
        let root = runner.roots[0];
        let mut extractor = Extractor::new(&runner.egraph, AstSize);
        MyIterData {
            smallest_so_far: extractor.find_best(root).0,
        }
    }
}

let start = "(+ 0 (* 1 foo))".parse().unwrap();
// Runner is customizable in the builder pattern style.
let runner = MyRunner::default()
    .with_iter_limit(10)
    .with_node_limit(10_000)
    .with_expr(&start)
    .with_scheduler(SimpleScheduler)
    .run(&rules);

// Now we can check our iteration data to make sure that the cost only
// got better over time
for its in runner.iterations.windows(2) {
    assert!(its[0].data.smallest_so_far >= its[1].data.smallest_so_far);
}

println!(
    "Stopped after {} iterations, reason: {:?}",
    runner.iterations.len(),
    runner.stop_reason
);

```
*/
pub struct Runner<L, M, IterData = ()> {
    /// The [`EGraph`](struct.EGraph.html) used.
    pub egraph: EGraph<L, M>,
    /// Data accumulated over each [`Iteration`](struct.Iteration.html).
    pub iterations: Vec<Iteration<IterData>>,
    /// The roots of expressions added by the
    /// [`with_expr`](#method.with_expr) method, in insertion order.
    pub roots: Vec<Id>,
    /// Why the `Runner` stopped. This will be `None` if it hasn't
    /// stopped yet.
    pub stop_reason: Option<StopReason>,

    rules: Vec<Rewrite<L, M>>,

    // limits
    iter_limit: usize,
    node_limit: usize,
    time_limit: Duration,

    start_time: Option<Instant>,
    scheduler: Box<dyn RewriteScheduler<L, M>>,
}

impl<L, M> Runner<L, M, ()>
where
    L: Language,
    M: Metadata<L>,
{
    /// Create a new [`Runner`](struct.Runner.html) with () as the
    /// `IterData`.
    pub fn new() -> Self {
        Self::default()
    }
}

impl<L, M, IterData> Default for Runner<L, M, IterData>
where
    L: Language,
    M: Metadata<L>,
{
    fn default() -> Self {
        Self {
            iter_limit: 30,
            node_limit: 10_000,
            time_limit: Duration::from_secs(60),

            egraph: EGraph::default(),
            roots: vec![],
            iterations: vec![],
            rules: vec![],
            stop_reason: None,

            start_time: None,
	    // TODO add scheduler support with rete
            scheduler: Box::new(SimpleScheduler{}),
        }
    }
}

/// Error returned by [`Runner`] when it stops.
///
/// [`Runner`]: struct.Runner.html
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize))]
pub enum StopReason {
    /// The egraph saturated, i.e., there was an iteration where we
    /// didn't learn anything new from applying the rules.
    Saturated,
    /// The iteration limit was hit. The data is the iteration limit.
    IterationLimit(usize),
    /// The enode limit was hit. The data is the enode limit.
    NodeLimit(usize),
    /// The time limit was hit. The data is the time limit in seconds.
    TimeLimit(f64),
}

/// Data generated by running a [`Runner`] one iteration.
///
/// If the `serde-1` feature is enabled, this implements
/// [`serde::Serialize`][ser], which is useful if you want to output
/// this as a JSON or some other format.
///
/// [`Runner`]: struct.Runner.html
/// [ser]: https://docs.rs/serde/latest/serde/trait.Serialize.html
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize))]
#[non_exhaustive]
pub struct Iteration<IterData> {
    /// The number of enodes in the egraph at the start of this
    /// iteration.
    pub egraph_nodes: usize,
    /// The number of eclasses in the egraph at the start of this
    /// iteration.
    pub egraph_classes: usize,
    /// A map from rule name to number of times it was _newly_ applied
    /// in this iteration.
    pub applied: IndexMap<String, usize>,
    /// Seconds spent searching in this iteration.
    pub search_time: f64,
    /// Seconds spent applying rules in this iteration.
    pub apply_time: f64,
    /// Seconds spent [`rebuild`](struct.EGraph.html#method.rebuild)ing
    /// the egraph in this iteration.
    pub rebuild_time: f64,
    /// The user provided annotation for this iteration
    pub data: IterData,
}

type RunnerResult<T> = std::result::Result<T, StopReason>;

impl<L, M, IterData> Runner<L, M, IterData>
where
    L: Language,
    M: Metadata<L>,
    IterData: IterationData<L, M>,
{
    /// Sets the iteration limit. Default: 30
    pub fn with_iter_limit(self, iter_limit: usize) -> Self {
        Self { iter_limit, ..self }
    }

    /// Sets the egraph size limit (in enodes). Default: 10,000
    pub fn with_node_limit(self, node_limit: usize) -> Self {
        Self { node_limit, ..self }
    }

    /// Sets the runner time limit. Default: 60 seconds
    pub fn with_time_limit(self, time_limit: Duration) -> Self {
        Self { time_limit, ..self }
    }

    /// Change out the [`RewriteScheduler`] used by this [`Runner`].
    /// The default one is [`BackoffScheduler`].
    ///
    /// [`RewriteScheduler`]: trait.RewriteScheduler.html
    /// [`BackoffScheduler`]: struct.BackoffScheduler.html
    /// [`Runner`]: struct.Runner.html
    pub fn with_scheduler(self, scheduler: impl RewriteScheduler<L, M> + 'static) -> Self {
        let scheduler = Box::new(scheduler);
        Self { scheduler, ..self }
    }

    /// Add an expression to the egraph to be run.
    ///
    /// The eclass id of this addition will be recorded in the
    /// [`roots`](struct.Runner.html#structfield.roots) field, ordered by
    /// insertion order.
    pub fn with_expr(mut self, expr: &RecExpr<L>) -> Self {
        let id = self.egraph.add_expr(expr);
        self.roots.push(id);
        self
    }

    /// Replace the [`EGraph`](struct.EGraph.html) of this `Runner`.
    pub fn with_egraph(self, egraph: EGraph<L, M>) -> Self {
        Self { egraph, ..self }
    }

    /// Replace the [`Rules`](struct.Rewrite.html) of this `Runner`.
    pub fn with_rules(mut self, mut rules: Vec<Rewrite<L, M>>) -> Self {
	for iter in 0..rules.len() {
	    let rewrite = &mut rules[iter];
	    self.egraph.rete.add_pattern(&rewrite.searcher.ast, vec![iter]);
	}
        Self { rules, ..self }
    }

    /// Run this `Runner` until it stops.
    /// After this, the field
    /// [`stop_reason`](#structfield.stop_reason) is guaranteeed to be
    /// set.
    pub fn run(mut self) -> Self {
        // TODO check that we haven't
        loop {
            if let Err(stop_reason) = self.run_one() {
                self.stop_reason = Some(stop_reason);
                break;
            }
        }
        self
    }

    fn run_one(&mut self) -> RunnerResult<()> {
        assert!(self.stop_reason.is_none());

        info!("Iteration {}", self.iterations.len());

        self.try_start();
        self.check_limits()?;

        let i = self.iterations.len();
        let egraph_nodes = self.egraph.total_size();
        let egraph_classes = self.egraph.number_of_classes();
        trace!("EGraph {:?}", self.egraph.dump());

        let search_time = Instant::now();

        let mut matches = self.egraph.rete_matches(self.rules.len());

	let mut summatches = 0;
	for m in &matches {
	    print!(" {} ", m.len());
	    summatches += m.len();
	}
	print!("Matches: {}\n", summatches);
	
        let search_time = search_time.elapsed().as_secs_f64();
        info!("Search time: {}", search_time);

	self.egraph.reset_matches();

        let apply_time = Instant::now();

        let mut applied = IndexMap::new();
        for (rw, ms) in self.rules.iter().zip(matches) {
            let total_matches: usize = ms.iter().map(|m| m.substs.len()).sum();
            if total_matches == 0 {
                continue;
            }

            debug!("Applying {} {} times", rw.name(), total_matches);

            let actually_matched = self.scheduler.apply_rewrite(i, &mut self.egraph, rw, ms);
            if actually_matched > 0 {
                if let Some(count) = applied.get_mut(rw.name()) {
                    *count += 1;
                } else {
                    applied.insert(rw.name().to_owned(), 1);
                }
                debug!("Applied {} {} times", rw.name(), actually_matched);
            }

            self.check_limits()?
        }

        let apply_time = apply_time.elapsed().as_secs_f64();
        info!("Apply time: {}", apply_time);

        let rebuild_time = Instant::now();
        self.egraph.rebuild();

        let rebuild_time = rebuild_time.elapsed().as_secs_f64();
        info!("Rebuild time: {}", rebuild_time);
        info!(
            "Size: n={}, e={}",
            self.egraph.total_size(),
            self.egraph.number_of_classes()
        );

        let saturated = applied.is_empty() && self.scheduler.can_stop(i);

        self.iterations.push(Iteration {
            applied,
            egraph_nodes,
            egraph_classes,
            search_time,
            apply_time,
            rebuild_time,
            data: IterData::make(&self),
            // best_cost,
        });

        if saturated {
            Err(StopReason::Saturated)
        } else {
            Ok(())
        }
    }

    fn try_start(&mut self) {
        self.start_time.get_or_insert_with(Instant::now);
    }

    fn check_limits(&self) -> RunnerResult<()> {
        let elapsed = self.start_time.unwrap().elapsed();
        if elapsed > self.time_limit {
            return Err(StopReason::TimeLimit(elapsed.as_secs_f64()));
        }

        let size = self.egraph.total_size();
        if size > self.node_limit {
            return Err(StopReason::NodeLimit(size));
        }

        if self.iterations.len() >= self.iter_limit {
            return Err(StopReason::IterationLimit(self.iterations.len()));
        }

        Ok(())
    }

    // /// The pre-iteration hook. If this returns an error, then the
    // /// search will stop. Useful for checking stop conditions or
    // /// updating `Runner` state.
    // ///
    // /// Default implementation simply returns `Ok(())`.
    // fn pre_step(&mut self, egraph: &mut EGraph<L, M>) -> RunnerResult<()> {
    //     info!(
    //         "\n\nIteration {}, n={}, e={}",
    //         self.i,
    //         egraph.total_size(),
    //         egraph.number_of_classes()
    //     );
    //     if self.i >= self.iter_limit {
    //         Err(StopReason::IterationLimit(self.i))
    //     } else {
    //         Ok(())
    //     }
    // }

    // fn during_step(&mut self, egraph: &EGraph<L, M>) -> RunnerResult<()> {
    //     let size = egraph.total_size();
    //     let elapsed = self.start_time.elapsed();
    //     if size > self.node_limit {
    //         Err(StopReason::NodeLimit(size))
    //     } else if elapsed > self.time_limit {
    //         Err(StopReason::TimeLimit(elapsed.as_secs_f64()))
    //     } else {
    //         Ok(())
    //     }
    // }

    // fn post_step(
    //     &mut self,
    //     iteration: &Iteration,
    //     _egraph: &mut EGraph<L, M>,
    // ) -> RunnerResult<()> {
    //     let is_banned = |s: &RuleStats| s.banned_until > self.i;
    //     let any_bans = self.stats.values().any(is_banned);

    //     self.i += 1;
    //     if !any_bans && iteration.applied.is_empty() {
    //         Err(StopReason::Saturated)
    //     } else {
    //         Ok(())
    //     }
    // }

    // /// The post-iteration hook. If this returns an error, then the
    // /// search will stop. Useful for checking stop conditions or
    // /// updating `Runner` state.
    // ///
    // /// Default implementation simply returns `Ok(())`.
    // fn post_step(
    //     &mut self,
    //     _iteration: &Iteration,
    //     _egraph: &mut EGraph<L, M>,
    // ) -> Result<(), Self::Error> {
    //     Ok(())
    // }

    // /// The intra-iteration hook. If this returns an error, then the
    // /// search will stop. Useful for checking stop conditions.
    // /// This is called after search each rule and after applying each rule.
    // ///
    // /// Default implementation simply returns `Ok(())`.
    // fn during_step(&mut self, _egraph: &EGraph<L, M>) -> Result<(), Self::Error> {
    //     Ok(())
    // }

    // /// Run the rewrites once on the egraph.
    // ///
    // /// It first searches all the rules using the [`search_rewrite`] wrapper.
    // /// Then it applies all the rules using the [`apply_rewrite`] wrapper.
    // ///
    // /// ## Expectations
    // ///
    // /// After searching or applying a rule, this should call
    // /// [`during_step`], returning immediately if it returns an error.
    // /// This should _not_ call [`pre_step`] or [`post_step`], those
    // /// should be called by the [`run`] method.
    // ///
    // /// Default implementation just calls
    // /// [`Rewrite::apply`](struct.Rewrite.html#method.apply)
    // /// and returns number of new applications.
    // ///
    // /// ## Default implementation
    // ///
    // /// The default implementation is probably good enough.
    // /// It conforms to all the above expectations, and it performs the
    // /// necessary bookkeeping to return an [`Iteration`].
    // /// It additionally performs useful logging at the debug and info
    // /// levels.
    // /// If you're using [`env_logger`](https://docs.rs/env_logger/)
    // /// (which the tests of `egg` do),
    // /// see its documentation on how to see the logs.
    // ///
    // /// [`search_rewrite`]: trait.Runner.html#method.search_rewrite
    // /// [`apply_rewrite`]: trait.Runner.html#method.apply_rewrite
    // /// [`pre_step`]: trait.Runner.html#method.pre_step
    // /// [`during_step`]: trait.Runner.html#method.during_step
    // /// [`post_step`]: trait.Runner.html#method.post_step
    // /// [`run`]: trait.Runner.html#method.run
    // /// [`Iteration`]: struct.Iteration.html
    // fn step(
    //     &mut self,
    //     egraph: &mut EGraph<L, M>,
    //     rules: &[Rewrite<L, M>],
    // ) -> RunnerResult<Iteration> {
    //     let egraph_nodes = egraph.total_size();
    //     let egraph_classes = egraph.number_of_classes();
    //     trace!("EGraph {:?}", egraph.dump());

    //     let search_time = Instant::now();

    //     let mut matches = Vec::new();
    //     for rule in rules.iter() {
    //         let ms = self.search_rewrite(egraph, rule);
    //         matches.push(ms);
    //         self.during_step(egraph)?
    //     }

    //     let search_time = search_time.elapsed().as_secs_f64();
    //     info!("Search time: {}", search_time);

    //     let apply_time = Instant::now();

    //     let mut applied = IndexMap::new();
    //     for (rw, ms) in rules.iter().zip(matches) {
    //         let total_matches: usize = ms.iter().map(|m| m.substs.len()).sum();
    //         if total_matches == 0 {
    //             continue;
    //         }

    //         debug!("Applying {} {} times", rw.name(), total_matches);

    //         let actually_matched = self.apply_rewrite(egraph, rw, ms);
    //         if actually_matched > 0 {
    //             if let Some(count) = applied.get_mut(rw.name()) {
    //                 *count += 1;
    //             } else {
    //                 applied.insert(rw.name().to_owned(), 1);
    //             }
    //             debug!("Applied {} {} times", rw.name(), actually_matched);
    //         }

    //         self.during_step(egraph)?
    //     }

    //     let apply_time = apply_time.elapsed().as_secs_f64();
    //     info!("Apply time: {}", apply_time);

    //     let rebuild_time = Instant::now();
    //     egraph.rebuild();

    //     let rebuild_time = rebuild_time.elapsed().as_secs_f64();
    //     info!("Rebuild time: {}", rebuild_time);
    //     info!(
    //         "Size: n={}, e={}",
    //         egraph.total_size(),
    //         egraph.number_of_classes()
    //     );

    //     trace!("Running post_step...");
    //     Ok(Iteration {
    //         applied,
    //         egraph_nodes,
    //         egraph_classes,
    //         search_time,
    //         apply_time,
    //         rebuild_time,
    //         // best_cost,
    //     })
    // }

    // /// Run the rewrites on the egraph until an error.
    // ///
    // /// This should call [`pre_step`], [`step`], and [`post_step`] in
    // /// a loop, in that order, until one of them returns an error.
    // /// It returns the completed [`Iteration`]s and the error that
    // /// caused it to stop.
    // ///
    // /// The default implementation does these things.
    // ///
    // /// [`pre_step`]: trait.Runner.html#method.pre_step
    // /// [`step`]: trait.Runner.html#method.step
    // /// [`post_step`]: trait.Runner.html#method.post_step
    // /// [`Iteration`]: struct.Iteration.html
    // fn run(
    //     &mut self,
    //     egraph: &mut EGraph<L, M>,
    //     rules: &[Rewrite<L, M>],
    // ) -> (Vec<Iteration>, Self::Error) {
    //     let mut iterations = vec![];
    //     let mut fn_loop = || -> Result<(), Self::Error> {
    //         loop {
    //             trace!("Running pre_step...");
    //             self.pre_step(egraph)?;
    //             trace!("Running step...");
    //             iterations.push(self.step(egraph, rules)?);
    //             trace!("Running post_step...");
    //             self.post_step(iterations.last().unwrap(), egraph)?;
    //         }
    //     };
    //     let stop_reason = fn_loop().unwrap_err();
    //     info!("Stopping {:?}", stop_reason);
    //     (iterations, stop_reason)
    // }

    // /// Given an initial expression, make and egraph and [`run`] the
    // /// rules on it.
    // ///
    // /// The default implementation does exactly this, also performing
    // /// the bookkeeping needed to return a [`RunReport`].
    // ///
    // /// [`run`]: trait.Runner.html#method.run
    // /// [`RunReport`]: struct.RunReport.html
    // fn run_expr(
    //     &mut self,
    //     initial_expr: RecExpr<L>,
    //     rules: &[Rewrite<L, M>],
    // ) -> (EGraph<L, M>, RunReport<L, Self::Error>) {
    //     // let initial_cost = calculate_cost(&initial_expr);
    //     // info!("Without empty: {}", initial_expr.pretty(80));

    //     let (mut egraph, initial_expr_eclass) = EGraph::from_expr(&initial_expr);

    //     let rules_time = Instant::now();
    //     let (iterations, stop_reason) = self.run(&mut egraph, rules);
    //     let rules_time = rules_time.elapsed().as_secs_f64();

    //     // let extract_time = Instant::now();
    //     // let best = Extractor::new(&egraph).find_best(root);
    //     // let extract_time = extract_time.elapsed().as_secs_f64();

    //     // info!("Extract time: {}", extract_time);
    //     // info!("Initial cost: {}", initial_cost);
    //     // info!("Final cost: {}", best.cost);
    //     // info!("Final: {}", best.expr.pretty(80));

    //     let report = RunReport {
    //         iterations,
    //         rules_time,
    //         // extract_time,
    //         stop_reason,
    //         // ast_size: best.expr.ast_size(),
    //         // ast_depth: best.expr.ast_depth(),
    //         initial_expr,
    //         initial_expr_eclass: egraph.find(initial_expr_eclass),
    //         // initial_cost,
    //         // final_cost: best.cost,
    //         // final_expr: best.expr,
    //     };
    //     (egraph, report)
    // }
}

/** A way to customize how a [`Runner`] runs [`Rewrite`]s.

This gives you a way to prevent certain [`Rewrite`]s from exploding
the [`EGraph`] and dominating how much time is spent while running the
[`Runner`].

[`EGraph`]: struct.EGraph.html
[`Runner`]: struct.Runner.html
[`Rewrite`]: struct.Rewrite.html
*/
#[allow(unused_variables)]
pub trait RewriteScheduler<L, M>
where
    L: Language,
    M: Metadata<L>,
{
    /// Whether or not the [`Runner`](struct.Runner.html) is allowed
    /// to say it has saturated.
    ///
    /// Default implementation just returns `true`.
    fn can_stop(&self, iteration: usize) -> bool {
        true
    }

    /// A hook allowing you to customize rewrite searching behavior.
    /// Useful to implement rule management.
    ///
    /// Default implementation just calls
    /// [`Rewrite::search`](struct.Rewrite.html#method.search).
    fn search_rewrite(
        &mut self,
        iteration: usize,
        egraph: &EGraph<L, M>,
        rewrite: &Rewrite<L, M>,
    ) -> Vec<SearchMatches> {
        rewrite.search(egraph)
    }

    /// A hook allowing you to customize rewrite application behavior.
    /// Useful to implement rule management.
    ///
    /// Default implementation just calls
    /// [`Rewrite::apply`](struct.Rewrite.html#method.apply)
    /// and returns number of new applications.
    fn apply_rewrite(
        &mut self,
        iteration: usize,
        egraph: &mut EGraph<L, M>,
        rewrite: &Rewrite<L, M>,
        matches: Vec<SearchMatches>,
    ) -> usize {
        rewrite.apply(egraph, &matches).len()
    }
}

/// A very simple [`RewriteScheduler`] that runs every rewrite every
/// time.
///
/// Using this is basically turning off rule scheduling.
/// It uses the default implementation for all [`RewriteScheduler`]
/// methods.
///
/// This is not the default scheduler; choose it with the
/// [`with_scheduler`](struct.Runner.html#method.with_scheduler)
/// method.
///
/// [`RewriteScheduler`]: trait.RewriteScheduler.html
pub struct SimpleScheduler;

impl<L, M> RewriteScheduler<L, M> for SimpleScheduler
where
    L: Language,
    M: Metadata<L>,
{
}

/// A [`RewriteScheduler`] that implements exponentional rule backoff.
///
/// For each rewrite, there exists a configurable initial match limit.
/// If a rewrite search yield more than this limit, then we ban this
/// rule for number of iterations, double its limit, and double the time
/// it will be banned next time.
///
/// This seems effective at preventing explosive rules like
/// associativity from taking an unfair amount of resources.
///
/// [`BackoffScheduler`] is configurable in the builder-pattern style.
///
/// [`RewriteScheduler`]: trait.RewriteScheduler.html
/// [`BackoffScheduler`]: struct.BackoffScheduler.html
pub struct BackoffScheduler {
    initial_match_limit: usize,
    ban_length: usize,
    stats: IndexMap<String, RuleStats>,
    dont_ban: IndexSet<String>,
}

struct RuleStats {
    times_applied: usize,
    banned_until: usize,
    times_banned: usize,
}

impl BackoffScheduler {
    /// Set the initial match limit after which a rule will be banned.
    /// Default: 1,000
    pub fn with_initial_match_limit(self, initial_match_limit: usize) -> Self {
        Self {
            initial_match_limit,
            ..self
        }
    }

    /// Set the initial ban length.
    /// Default: 5 iterations
    pub fn with_ban_length(self, ban_length: usize) -> Self {
        Self { ban_length, ..self }
    }

    /// Never ban a particular rule.
    pub fn do_not_ban(mut self, name: impl Into<String>) -> Self {
        self.dont_ban.insert(name.into());
        self
    }
}

impl Default for BackoffScheduler {
    fn default() -> Self {
        Self {
            dont_ban: Default::default(),
            stats: Default::default(),
            initial_match_limit: 1_000,
            ban_length: 5,
        }
    }
}

impl<L, M> RewriteScheduler<L, M> for BackoffScheduler
where
    L: Language,
    M: Metadata<L>,
{
    fn can_stop(&self, iteration: usize) -> bool {
        let is_banned = |s: &RuleStats| s.banned_until > iteration;
        let any_bans = self.stats.values().any(is_banned);
        !any_bans
    }

    fn search_rewrite(
        &mut self,
        iteration: usize,
        egraph: &EGraph<L, M>,
        rewrite: &Rewrite<L, M>,
    ) -> Vec<SearchMatches> {
        if let Some(limit) = self.stats.get_mut(rewrite.name()) {
            if iteration < limit.banned_until {
                debug!(
                    "Skipping {} ({}-{}), banned until {}...",
                    rewrite.name(),
                    limit.times_applied,
                    limit.times_banned,
                    limit.banned_until,
                );
                return vec![];
            }

            let matches = rewrite.search(egraph);
            let total_len: usize = matches.iter().map(|m| m.substs.len()).sum();
            let threshold = self.initial_match_limit << limit.times_banned;
            if total_len > threshold {
                let ban_length = self.ban_length << limit.times_banned;
                limit.times_banned += 1;
                limit.banned_until = iteration + ban_length;
                info!(
                    "Banning {} ({}-{}) for {} iters: {} < {}",
                    rewrite.name(),
                    limit.times_applied,
                    limit.times_banned,
                    ban_length,
                    threshold,
                    total_len,
                );
                vec![]
            } else {
                limit.times_applied += 1;
                matches
            }
        } else {
            if !self.dont_ban.contains(rewrite.name()) {
                self.stats.insert(
                    rewrite.name().into(),
                    RuleStats {
                        times_applied: 0,
                        banned_until: 0,
                        times_banned: 0,
                    },
                );
            }
            rewrite.search(egraph)
        }
    }
}

/// Custom data to inject into the [`Iteration`]s recorded by a [`Runner`]
///
/// This trait allows you to add custom data to the [`Iteration`]s
/// recorded as a [`Runner`] applies rules.
///
/// See the [`Runner`] docs for an example.
///
/// [`Runner`] is generic over the [`IterationData`] that it will be in the
/// [`Iteration`]s, but by default it uses `()`.
///
/// [`Runner`]: struct.Runner.html
/// [`Iteration`]: struct.Iteration.html
/// [`IterationData`]: trait.IterationData.html
pub trait IterationData<L, M>: Sized {
    /// Given the current [`Runner`](struct.Runner.html), make the
    /// data to be put in this [`Iteration`](struct.Iteration.html).
    fn make(runner: &Runner<L, M, Self>) -> Self;
}

impl<L, M> IterationData<L, M> for () {
    fn make(_: &Runner<L, M, Self>) -> Self {}
}
