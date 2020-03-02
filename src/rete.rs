use crate::{
    machine, Applier, ENode, Id, Language, Metadata, RecExpr, Searcher, Subst, Var, PatternAst
};

use std::vec::Vec;
use std::collections::HashMap;
use smallvec::SmallVec;

pub type RetePat = usize;

pub enum RChild {
    Ref(RetePat),
    Var,
}

pub struct Rete<L: Language> {
    table: Vec<(ENode<L, RChild>, Vec<Id>)>,
    // use smallvec or no?
    map: HashMap<L, SmallVec<[RetePat; 2]>,>,
}

impl<L : Language> Rete<L> {
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

