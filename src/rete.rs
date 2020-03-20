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

pub type ReteMatch = SmallVec<[Id; 2]>;

pub type ReteMatches = IndexMap<RetePat, Vec<ReteMatch>>;

// TODO make non public
pub enum RChild {
    Ref(RetePat),
    Var,
}

//#[derive(Default)]
pub struct Rete<L, M> {
    pub table: Vec<(ENode<L, RChild>, Vec<Rc<dyn Applier<L, M>>>)>,
    // XXX use smallvec or no?
    map: HashMap<L, SmallVec<[RetePat; 2]>,>,
}

impl<L : std::hash::Hash + Eq, M> Default for Rete<L, M> {
    fn default() -> Rete<L, M> {
        Rete {
            table: Vec::new(),
            map: HashMap::new(),
        }
    }
}

impl<L : Language, M> Rete<L, M> {
    /// Compile `pattern` to several rete patterns and return the
    /// representative `RetePat`
    // TODO allow for expressions containing one variable
    // TODO delete duplicate patterns
    pub(crate) fn add_pattern(&mut self, pattern: &PatternAst<L>, appliers: Vec<Rc<dyn Applier<L, M>>>) -> RetePat {
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
        self.map.entry(op)
            .and_modify(|vec| vec.push(idx))
            .or_insert(SmallVec::from_elem(idx,1));
        idx
    }

    /// Returns all `RetePat` which match the given query
    pub fn search(&self, node: &ENode<L, &[RetePat]>) -> Vec<RetePat> {
        self.map.get(&node.op).map_or(&[] as &[usize], |vec| vec.as_slice())
            .iter().filter(move |&&elem| {
                let sets = &node.children;
                let current = &self.table[elem].0.children;
                if current.len() != sets.len() {
                    false
                } else {
                    current.iter().zip(sets.iter())
                        .all(|(item, set)| match item {
                            RChild::Var => true,
                            RChild::Ref(pat) => set.contains(pat),
                        })
                }
            }).copied().collect()
    }
}

