use crate::{
    machine, Applier, ENode, Id, Language, Metadata, RecExpr, Searcher, Subst, Var, PatternAst
};

pub type RetePat = u64;

pub enum RChild {
    Ref(RetePat),
    Var(),
}

pub enum RNode<L: Language> {
    Lit(L),
    Pattern(ENode<L, RChild>),
}

pub struct Rete<L: Language> {
    table: Vec<(RNode<L>, Vec<Id>)>,
}

impl<L : Language> Rete<L> {
    pub(crate) fn add_pattern(&mut self, pattern: &PatternAst<L>) {
        unimplemented!()
    }
}

