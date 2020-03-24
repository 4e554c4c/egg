use crate::{
    machine, Applier, ENode, Id, Language, Metadata, RecExpr, Searcher, Subst, Var, PatternAst, SearchMatches, unionfind::UnionFind, EClass,
};

use std::rc::Rc;
use std::vec::Vec;
use std::collections::HashMap;
use smallvec::SmallVec;
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;

/// The type of a pattern in the [`Rete`](struct.Rete.html) graph.
pub type RetePat = usize;

pub type RuleIndex = usize;

pub type ReteMatch = SmallVec<[Id; 2]>;

pub type ReteMatches = IndexMap<RetePat, Vec<ReteMatch>>;

pub fn merge_retematches(to: &mut ReteMatches, from: &mut ReteMatches) {
    for (k, mut v) in from {
	to.entry(*k)
	    .and_modify(|vec| vec.append(&mut v))
	    .or_insert(v.to_vec());
    }
}

// TODO make non public
pub enum RChild {
    Ref(RetePat),
    Var(Var),
}

//#[derive(Default)]
pub struct Rete<L> {
    pub table: Vec<(ENode<L, RChild>, Vec<RuleIndex>)>,
    // XXX use smallvec or no?
    map: HashMap<(L, usize), SmallVec<[RetePat; 2]>,>,
}

impl<L : std::hash::Hash + Eq> Default for Rete<L> {
    fn default() -> Rete<L> {
        Rete {
            table: Vec::new(),
            map: HashMap::new(),
        }
    }
}

impl<L : Language> Rete<L> {
    /// Compile `pattern` to several rete patterns and return the
    /// representative `RetePat`
    // TODO allow for expressions containing one variable
    // TODO delete duplicate patterns
    pub(crate) fn add_pattern(&mut self, pattern: &PatternAst<L>, appliers: Vec<RuleIndex>) -> RetePat {
        let expr = match pattern {
            PatternAst::ENode(expr) => expr,
            _ => panic!("Cannot create a rete pattern for a lone variable"),
        };

        let node = expr.map_children(|pattern|
            match pattern {
                PatternAst::Var(v) => RChild::Var(v),
                PatternAst::ENode(_) => RChild::Ref(self.add_pattern(&pattern, vec![]))
            });

        let op = node.op.clone();
        let idx = self.table.len();
        self.table.push((node, appliers));
        self.map.entry((op, expr.children.len()))
            .and_modify(|vec| vec.push(idx))
            .or_insert(SmallVec::from_elem(idx,1));
        idx
    }

    /// Returns all `RetePat` which match the given query
    pub fn make_node_matches(&self, node: &ENode<L>) ->  ReteMatches {
	let mut matches: ReteMatches = IndexMap::default();
	
        let retepats = self.map.get(&(node.op.clone(), node.children.len())).map_or(&[] as &[usize], |vec| vec.as_slice());
	for retepat in retepats {
	    matches.entry(*retepat)
		.and_modify(|vec| vec.push(node.children.clone()))
		.or_insert(vec![node.children.clone()]);
	}

	matches
    }

    pub fn extract_matches<M>(&self, classes: &UnionFind<Id, EClass<L, M>>, class: &EClass<L, M>) -> Vec<(Vec<RuleIndex>, Vec<Subst>)> {
	let mut res: Vec<_> = Vec::default();
	for (rpat, rms) in &class.rmatches {
	    res.push((self.table[*rpat].1.clone(), self.eclass_matches(classes, class, *rpat)));
	}
	res
    }

    pub fn eclass_matches<M>(&self, classes: &UnionFind<Id, EClass<L, M>>, class: &EClass<L, M>, rpat: RetePat) -> Vec<Subst> {
	let mut res: Vec<Subst> = Vec::default();
	let empty = Vec::new();
	let rmatches: &Vec<ReteMatch> = class.rmatches.get(&rpat).unwrap_or(&empty);
	
	if self.table[rpat].0.children.len() == 0{
	    if rmatches.len() > 0 {
		res.push(Subst::default());
	    }
	} else {
	    for rmatch in rmatches {
		res.append(&mut self.extract_from_match(classes, rmatch, rpat));
	    } 
	}
	res
    }

    pub fn extract_from_match<M>(&self, classes: &UnionFind<Id, EClass<L, M>>,rmatch: &ReteMatch, rpat: RetePat) -> Vec<Subst> {
	let lhs = &self.table[rpat].0;
	let mut new_substs = Vec::new();

	// When we substitute, find the parent because it may not be the leader any more
	let arg_substs: Vec<_> = self.table[rpat].0.children.iter().zip(rmatch)
	    .map(|(pa, ea)|
		 match pa {
		     RChild::Var(v) => vec![Subst::from_item(v.clone(), classes.find(*ea))],
		     RChild::Ref(subpat) => self.eclass_matches(classes, classes.get(*ea), *subpat),
		 }).collect();

	'outer: for ms in arg_substs.iter().multi_cartesian_product() {
	    let mut combined = ms[0].clone();
	    for m in &ms[1..] {
                for (w, id) in m.iter() {
                    if let Some(old_id) = combined.insert(w.clone(), id.clone()) {
                        if old_id != *id {
                            continue 'outer;
                        }
                    }
                }
            }
	    new_substs.push(combined);
	}
	new_substs
    }
}



#[cfg(test)]
mod tests {
    use crate::rete::{ReteMatches, merge_retematches};
    use indexmap::{IndexMap, IndexSet};
    use smallvec::{smallvec};
    
    #[test]
    fn test_merge_retematches() {
	let mut r1: ReteMatches = IndexMap::default();
	r1.entry(0).or_insert(vec![smallvec![3], smallvec![4]]);
	r1.entry(1).or_insert(vec![smallvec![5], smallvec![6]]);

	let mut r2: ReteMatches = IndexMap::default();
	r2.entry(1).or_insert(vec![smallvec![7], smallvec![8]]);
	r2.entry(2).or_insert(vec![smallvec![9]]);

	let mut result: ReteMatches = IndexMap::default();
	result.entry(0).or_insert(vec![smallvec![3], smallvec![4]]);
	result.entry(1).or_insert(vec![smallvec![5], smallvec![6], smallvec![7], smallvec![8]]);
	result.entry(2).or_insert(vec![smallvec![9]]);

	merge_retematches(&mut r1,&mut r2);
	assert_eq!(r1, result);
    }
}

