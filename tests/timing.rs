use egg::{rewrite as rw, *};

use log::trace;
use ordered_float::NotNan;
use std::fs::File;
use std::io::{self, Write, BufReader, BufRead, Error};
use std::path::Path;
use instant::{Duration, Instant};


pub type EGraph = egg::EGraph<Math, Meta>;
pub type Rewrite = egg::Rewrite<Math, Meta>;

type Constant = NotNan<f64>;

define_language! {
    pub enum Math {
        Diff = "d",

        Constant(Constant),
        Add = "+",
        Sub = "-",
        Mul = "*",
        Div = "/",
        Pow = "pow",
        Exp = "exp",
        Log = "log",
        Sqrt = "sqrt",
        Cbrt = "cbrt",
        Fabs = "fabs",

        Log1p = "log1p",
        Expm1 = "expm1",

        RealToPosit = "real->posit",
        Variable(String),
    }
}

// You could use egg::AstSize, but this is useful for debugging, since
// it will really try to get rid of the Diff operator
struct MathCostFn;
impl egg::CostFunction<Math> for MathCostFn {
    type Cost = usize;
    fn cost(&mut self, enode: &ENode<Math, Self::Cost>) -> Self::Cost {
        let op_cost = match enode.op {
            Math::Diff => 100,
            _ => 1,
        };
        op_cost + enode.children.iter().sum::<usize>()
    }
}

#[derive(Debug, Clone)]
pub struct Meta {
    pub cost: usize,
    pub best: RecExpr<Math>,
}

fn eval(op: Math, args: &[Constant]) -> Option<Constant> {
    let a = |i| args.get(i).cloned();
    let res = match op {
        Math::Add => Some(a(0)? + a(1)?),
        Math::Sub => Some(a(0)? - a(1)?),
        Math::Mul => Some(a(0)? * a(1)?),
        Math::Div => Some(a(0)? / a(1)?),
        _ => None,
    };
    trace!("{} {:?} = {:?}", op, args, res);
    res
}

impl Metadata<Math> for Meta {
    type Error = std::convert::Infallible;
    fn merge(&self, other: &Self) -> Self {
        if self.cost <= other.cost {
            self.clone()
        } else {
            other.clone()
        }
    }

    fn make(egraph: &EGraph, enode: &ENode<Math>) -> Self {
        let meta = |i: Id| &egraph[i].metadata;
        let enode = {
            let const_args: Option<Vec<Constant>> = enode
                .children
                .iter()
                .map(|id| match meta(*id).best.as_ref().op {
                    Math::Constant(c) => Some(c),
                    _ => None,
                })
                .collect();

            const_args
                .and_then(|a| eval(enode.op.clone(), &a))
                .map(|c| ENode::leaf(Math::Constant(c)))
                .unwrap_or_else(|| enode.clone())
        };

        let best: RecExpr<_> = enode.map_children(|c| meta(c).best.clone()).into();
        let cost = MathCostFn.cost(&enode.map_children(|c| meta(c).cost));
        Self { best, cost }
    }

    fn modify(eclass: &mut EClass<Math, Self>) {
        // NOTE pruning vs not pruning is decided right here
        // not pruning would be just pushing instead of replacing
        let best = eclass.metadata.best.as_ref();
        if best.children.is_empty() {
            eclass.nodes = vec![ENode::leaf(best.op.clone())]
        }
    }
}

fn c_is_const_or_var_and_not_x(egraph: &mut EGraph, _: Id, subst: &Subst) -> bool {
    let c = "?c".parse().unwrap();
    let x = "?x".parse().unwrap();
    let is_const_or_var = egraph[subst[&c]].nodes.iter().any(|n| match n.op {
        Math::Constant(_) | Math::Variable(_) => true,
        _ => false,
    });
    is_const_or_var && subst[&x] != subst[&c]
}

fn is_not_zero(var: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let zero = enode!(Math::Constant(0.0.into()));
    move |egraph, _, subst| !egraph[subst[&var]].nodes.contains(&zero)
}

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite> { vec![
    rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
    rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
    rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

    rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    rw!("div-canon"; "(/ ?a ?b)" => "(* ?a (pow ?b -1))"),
    // rw!("canon-sub"; "(+ ?a (* -1 ?b))"   => "(- ?a ?b)"),
    // rw!("canon-div"; "(* ?a (pow ?b -1))" => "(/ ?a ?b)" if is_not_zero("?b")),

    rw!("zero-add"; "(+ ?a 0)" => "?a"),
    rw!("zero-mul"; "(* ?a 0)" => "0"),
    rw!("one-mul";  "(* ?a 1)" => "?a"),

    rw!("add-to-mul"; "(+ ?a ?a)" => "(* ?a 2)"),
    //rw!("add-zero"; "?a" => "(+ ?a 0)"),
    //rw!("mul-one";  "?a" => "(* ?a 1)"),

    rw!("cancel-sub"; "(- ?a ?a)" => "0"),
    rw!("cancel-div"; "(/ ?a ?a)" => "1"),

    rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
    rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),

    //rw!("pow-intro"; "?a" => "(pow ?a 1)"),
    rw!("pow-mul"; "(* (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (+ ?b ?c))"),
    rw!("pow0"; "(pow ?x 0)" => "1"),
    rw!("pow1"; "(pow ?x 1)" => "?x"),
    rw!("pow2"; "(pow ?x 2)" => "(* ?x ?x)"),
    #[cfg_attr(feature = "rete", ignore)]
    rw!("pow-recip"; "(pow ?x -1)" => "(/ 1 ?x)" if is_not_zero("?x")),

    rw!("d-variable"; "(d ?x ?x)" => "1"),
    #[cfg_attr(feature = "rete", ignore)]
    rw!("d-constant"; "(d ?x ?c)" => "0" if c_is_const_or_var_and_not_x),

    rw!("d-add"; "(d ?x (+ ?a ?b))" => "(+ (d ?x ?a) (d ?x ?b))"),
    rw!("d-mul"; "(d ?x (* ?a ?b))" => "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))"),

    #[cfg_attr(feature = "rete", ignore)]
    rw!("d-power";
        "(d ?x (pow ?f ?g))" =>
        "(* (pow ?f ?g)
            (+ (* (d ?x ?f)
                  (/ ?g ?f))
               (* (d ?x ?g)
                  (log ?f))))"
        if is_not_zero("?f")
    ),
]}

// The output is wrapped in a Result to allow matching on errors
// Returns an Iterator to the Reader of the lines of the file.
fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where P: AsRef<Path>, {
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

fn get_batches_from_file(filename: &str) -> Vec<Vec<RecExpr<Math>>> {
    let lines: Vec<Result<String, io::Error>> = read_lines(filename).unwrap().collect();
    let mut results: Vec<Vec<RecExpr<_>>> = vec![];
    for string_batch in lines.split(|line| line.as_ref().unwrap() == &"\"NEW BATCH\"".to_owned()) {
	let mut current_batch = vec![];
	for line in string_batch {
	    current_batch.push(line.as_ref().unwrap().parse()
			       .expect(&format!("{}{}", "Failed to parse ", &line.as_ref().unwrap())));
	}
	results.push(current_batch);
    }
    results
}

fn write_row(data_file: &mut File, row: &Vec<f64>) {
    write!(data_file, "{},{},{}\n",
	   row[0].to_string(),
	   row[1].to_string(),
	   row[2].to_string());
}

fn write_run_data(data_file: &mut File, r: &Runner<Math, Meta>) -> Vec<f64> {
    let mut search_time: f64 = 0.0;
    let mut apply_time: f64 = 0.0;
    let mut rebuild_time: f64 = 0.0;
    for iteration in &r.iterations {
	search_time += iteration.search_time;
	apply_time += iteration.apply_time;
	rebuild_time += iteration.rebuild_time;
    }
    let row = vec![search_time, apply_time, rebuild_time];
    write_row(data_file, &row);
    row
    
}

#[test] #[ignore]
fn time_egg() {
    

    let batches = get_batches_from_file("../time-regraph/exprs/math-exprs.txt");

    let mut data_file = File::create("./timing-results.txt").unwrap();
    let mut all_data: Vec<Vec<f64>> = vec![];
    let mut counter = 0;
    for batch in batches {
	print!("batch {}\n", counter);
	counter += 1;
	if(batch.len() > 0) {
	    let mut runner = Runner::new()
		.with_iter_limit(4)
		.with_rules(rules().clone());
	    for line in batch {
		runner = runner.with_expr(&line);
	    }
	    runner = runner.run();
	    let data = write_run_data(&mut data_file, &runner);
	    all_data.push(data);
	}
    }
    let mut average_file = File::create("./average.txt").unwrap();
    let mut averages = vec![];
    for j in 0..all_data[0].len() {
	let mut sum = 0.0;
	for i in 0..all_data.len() {
	    sum += all_data[i][j];
	}
	averages.push(sum / (all_data.len()) as f64);
    }
    write_row(&mut average_file, &averages);
}
