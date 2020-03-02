use crate::{
    machine, Applier, ENode, Id, Language, Metadata, RecExpr, Searcher, Subst, Var, PatternAst
};

use std::vec::Vec;
use std::collections::HashMap;
use smallvec::SmallVec;

/// The type of a pattern in the [`Rete`](struct.Rete.html) graph.
pub type RetePat = usize;

enum RChild {
    Ref(RetePat),
    Var,
}

//#[derive(Default)]
pub struct Rete<L> {
    table: Vec<(ENode<L, RChild>, Vec<Id>)>,
    // use smallvec or no?
    map: HashMap<L, SmallVec<[RetePat; 2]>,>,
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
    pub(crate) fn add_pattern(&mut self, pattern: &PatternAst<L>) -> RetePat {
        let expr = match pattern {
            PatternAst::ENode(expr) => expr,
            _ => panic!("Cannot create a rete pattern for a lone variable"),
        };

        let node = expr.map_children(|pattern|
            match pattern {
                PatternAst::Var(_) => RChild::Var,
                PatternAst::ENode(_) => RChild::Ref(self.add_pattern(&pattern))
            });

        let op = node.op.clone();
        let idx = self.table.len();
        self.table.push((node, vec![]));
        self.map.entry(op)
            .and_modify(|vec| vec.push(idx))
            .or_insert(SmallVec::from_elem(idx,1));
        idx
    }
}

