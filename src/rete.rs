use crate::{
    machine, Applier, ENode, Id, Language, Metadata, RecExpr, Searcher, Subst, Var, PatternAst, SearchMatches
};

use std::rc::Rc;
use std::vec::Vec;
use std::collections::HashMap;
use smallvec::SmallVec;
use indexmap::{IndexMap, IndexSet};

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
    Var,
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
                PatternAst::Var(_) => RChild::Var,
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
}



