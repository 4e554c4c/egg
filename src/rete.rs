use crate::{
    machine, Applier, ENode, Id, Language, Metadata, RecExpr, Searcher, Subst, Var, PatternAst, SearchMatches, unionfind::UnionFind, EClass,
};

use std::rc::Rc;
use std::vec::Vec;
use std::collections::HashMap;
use smallvec::SmallVec;
use smallvec::{smallvec};
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;

/// The type of a pattern in the [`Rete`](struct.Rete.html) graph.
pub type RetePat = usize;

pub type RuleIndex = usize;

pub type ReteMatch = SmallVec<[Id; 2]>;

#[derive(Clone, std::fmt::Debug)]
pub struct RSet {
    pub matches: Vec<ReteMatch>,
    pub newi: usize,
}

// from retepat leaders to all the matches for that leader
pub type ReteMatches = IndexMap<RetePat, RSet>;

pub fn merge_retematches(to: &mut ReteMatches, from: &mut ReteMatches, isjustadded: bool) {
    for (k, mut v) in from {
	to.entry(*k)
	    .and_modify(|rset|
			rset.matches.append(&mut v.matches))
	    .or_insert(RSet {
		matches: v.matches.clone(),
		newi: 0,
	    });
    }
    if !isjustadded {
	for (k, mut v) in to {
	    v.newi = 0;
	}
    }
}

// TODO make non public
#[derive(std::hash::Hash, std::cmp::PartialEq, Eq, Clone)]
pub enum RChild {
    Ref(RetePat),
    Var(Var),
}

#[derive(Clone)]
pub struct Rete<L> {
    pub table: Vec<(ENode<L, RChild>, Vec<RuleIndex>)>,
    ruledepth: Vec<usize>,
    // used when adding rules to check for duplicates
    enodetorpat: HashMap<ENode<L, RChild>, RetePat>,
    // XXX use smallvec or no?
    // a retepat leader is the first rule with a given signature to be added
    leadertorpats: Vec<SmallVec<[RetePat; 2]>>,
    rpatstoleader: Vec<RetePat>,
    map: HashMap<(L, usize), SmallVec<[RetePat; 2]>>,
}

impl<L : std::hash::Hash + Eq> Default for Rete<L> {
    fn default() -> Rete<L> {
        Rete {
            table: Vec::new(),
	    ruledepth: Vec::new(),
	    enodetorpat: HashMap::new(),
	    leadertorpats: vec![],
	    rpatstoleader: vec![],
            map: HashMap::new(),
        }
    }
}

impl<L : Language> Rete<L> {
    /// Compile `pattern` to several rete patterns and return the
    /// representative `RetePat`
    // TODO allow for expressions containing one variable
    // TODO rule compression
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

	if let Some(existing) = self.enodetorpat.get(&node) {
	    self.table[*existing].1.extend(appliers);
	    *existing
	    
	} else {

	    let depthlist = node.map_children(|rchild|
					  match rchild {
					      RChild::Ref(rpat) => self.ruledepth[rpat],
					      RChild::Var(v) => 0,
					  });
	    let depth =
		if let Some(m) = depthlist.children.iter().min() {
		    m + 1
		} else {0};
	    
	    let op = node.op.clone();
	    let op2 = node.op.clone();
	    let idx = self.table.len();
	    self.enodetorpat.entry(node.clone())
		.or_insert(idx);
            self.table.push((node, appliers));
	    self.ruledepth.push(depth);
	    self.map.entry((op, expr.children.len()))
		.and_modify(|vec| vec.push(idx))
		.or_insert(SmallVec::from_elem(idx,1));
	    let leader = self.map.get(&(op2, expr.children.len())).unwrap()[0];
	    self.leadertorpats.push(smallvec![]);
	    self.leadertorpats[leader].push(idx);
	    self.rpatstoleader.push(leader);
            idx
	}
    }
    
    /// Returns all `RetePat` which match the given query
    pub fn make_node_matches(&self, node: &ENode<L>) ->  ReteMatches {
	let mut matches: ReteMatches = IndexMap::default();
	
        match self.map.get(&(node.op.clone(), node.children.len())) {
	    Some(retepatvec) => {
		let retepat = retepatvec[0]; // leader is the first one
		matches.entry(retepat)
		    .or_insert(RSet{
			matches: vec![node.children.clone()],
			newi: 0,
		    });
		matches
	    },
	    None => matches
	}
    }

    pub fn extract_matches<M>(&self, classes: &UnionFind<Id, EClass<L, M>>, class: &EClass<L, M>) -> Vec<(Vec<RuleIndex>, Vec<Subst>)> {
	let mut res: Vec<_> = Vec::default();
	for (rpatleader, rms) in &class.rmatches {
	    let rpats = &self.leadertorpats[*rpatleader];
	    for rpat in rpats {
		if(self.table[*rpat].1.len() > 0) {
		    let matches = self.start_eclass_matches(classes, class, *rpat);
		    if matches.len() > 0 {
			res.push((self.table[*rpat].1.clone(), matches));
		    }
		}
	    }
	}
	
	res
    }

    fn start_eclass_matches<M>(&self, classes: &UnionFind<Id, EClass<L, M>>, class: &EClass<L, M>, rpat: RetePat) -> Vec<Subst> {
	let depth = self.ruledepth[rpat];
	if depth == 0 {
	    let mut res: Vec<Subst> = Vec::default();
	    let leader = self.rpatstoleader[rpat];
	    let (rmatches, newi) : (&Vec<ReteMatch>, usize) =
		if let Some(rset) = class.rmatches.get(&leader) {
		    (&rset.matches, rset.newi)
		} else {
		    return res
		};
	    
	    if self.table[rpat].0.children.len() == 0 {
		if rmatches.len() > 0 {
		    res.push(Subst::default());
		}
	    } else {
		for i in newi..rmatches.len() {
		    res.append(&mut self.extract_from_match(classes, &rmatches[i], rpat, false));
		}
	    }
	    res
	} else if depth == 1 {
	    let mut res: Vec<Subst> = Vec::default();
	    let leader = self.rpatstoleader[rpat];
	    let (rmatches, newi) : (&Vec<ReteMatch>, usize) =
		if let Some(rset) = class.rmatches.get(&leader) {
		    (&rset.matches, rset.newi)
		} else {
		    return res
		};
	    
	    if self.table[rpat].0.children.len() == 0 {
		if rmatches.len() > 0 {
		    res.push(Subst::default());
		}
	    } else {
		for i in 0..newi {
		    res.append(&mut self.extract_from_match(classes, &rmatches[i], rpat, true));
		}
		for i in newi..rmatches.len() {
		    res.append(&mut self.extract_from_match(classes, &rmatches[i], rpat, false));
		}
	    }
	    res
	} else {
	    self.eclass_matches(classes, class, rpat).0
	}
    }
    
    fn eclass_matches<M>(&self, classes: &UnionFind<Id, EClass<L, M>>, class: &EClass<L, M>, rpat: RetePat) -> (Vec<Subst>, usize) {
	let depth = self.ruledepth[rpat];
	let mut res: Vec<Subst> = Vec::default();
	let leader = self.rpatstoleader[rpat];
	let (rmatches, newi) : (&Vec<ReteMatch>, usize) =
		if let Some(rset) = class.rmatches.get(&leader) {
		    (&rset.matches, rset.newi)
		} else {
		    return (res, 0)
		};

	let mut newresults = 0;
	if self.table[rpat].0.children.len() == 0 {
	    if rmatches.len() > 0 {
		res.push(Subst::default());
	    }
	} else {
	    for i in 0..rmatches.len() {
		res.append(&mut self.extract_from_match(classes, &rmatches[i], rpat, false));
		if i+1 == newi {
		    newresults = res.len();
		}
	    }
	}
	(res, newresults)
    }

    pub fn extract_from_match<M>(&self, classes: &UnionFind<Id, EClass<L, M>>,rmatch: &ReteMatch, rpat: RetePat, justold: bool) -> Vec<Subst> {
	let mut new_substs = Vec::new();


	if justold && self.table[rpat].0.children.len() == 2 {
	    let mut arg_substs: Vec<_> = self.table[rpat].0.children.iter().zip(rmatch)
	    .map(|(pa, ea)|
		 match pa {
		     RChild::Var(v) => (vec![Subst::from_item(v.clone(), *ea)], 1),
		     RChild::Ref(subpat) => {
			 self.eclass_matches(classes, classes.get(*ea), *subpat)
		     },
		 }).collect();
	    let subs1 = &arg_substs[0].0;
	    let subs2 = &arg_substs[1].0;
	    let old1 = 0..arg_substs[0].1;
	    let new1 = arg_substs[0].1..subs1.len();
	    
	    for i in new1 {
                'outer: for m in subs2.iter() {
		    let mut combined = subs1[i].clone();
		    for (w, id) in m.iter() {
			if let Some(old_id) = combined.insert(w.clone(), id.clone()) {
                            if old_id != *id {
				continue 'outer;
                            }
			}
		    }
		    new_substs.push(combined);
                }
	    }

	    for i in old1 {
                'outer: for j in  arg_substs[1].1..subs2.len() {
		    let mut combined = subs1[i].clone();
		    let m = &subs2[j];
		    for (w, id) in m.iter() {
			if let Some(old_id) = combined.insert(w.clone(), id.clone()) {
                            if old_id != *id {
				continue 'outer;
                            }
			}
		    }
		    new_substs.push(combined);
                }
	    }
	} else {
	    let mut arg_substs: Vec<_> = self.table[rpat].0.children.iter().zip(rmatch)
	    .map(|(pa, ea)|
		 match pa {
		     RChild::Var(v) => vec![Subst::from_item(v.clone(), *ea)],
		     RChild::Ref(subpat) => {
			 self.eclass_matches(classes, classes.get(*ea), *subpat).0
		     },
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
	}
	new_substs
    }
}


/*
#[cfg(test)]
mod tests {
    use crate::rete::{ReteMatches, merge_retematches};
    use indexmap::{IndexMap, IndexSet};
    use smallvec::{smallvec};

    fn make_rset(a : Id,b: Id) -> RSet {
	RSet {
	    newi : 0,
	    matches: vec![smallvec![a], smallvec![b]],
	}
    }

    fn make_rset_1(Id a) -> RSet {
	RSet {
	    newi : 0,
	    matches: vec![smallvec![a]],
	}
    }
    
    #[test]
    fn test_merge_retematches() {
	let mut r1: ReteMatches = IndexMap::default();
	r1.entry(0).or_insert(make_rset(3, 4));
	r1.entry(1).or_insert(make_rset(5, 6));
	r1.entry(4).or_insert(make_rset_1(20));

	let mut r2: ReteMatches = IndexMap::default();
	r2.entry(1).or_insert(make_rset(7, 8));
	r2.entry(2).or_insert(make_rset_1(9));
	r2.entry(4).or_insert(make_rset_1(20));

	let mut result: ReteMatches = IndexMap::default();
	result.entry(0).or_insert(vec![smallvec![3], smallvec![4]]);
	result.entry(1).or_insert(vec![smallvec![5], smallvec![6], smallvec![7], smallvec![8]]);
	result.entry(2).or_insert(vec![smallvec![9]]);
	result.entry(4).or_insert(vec![smallvec![20], smallvec![20]]);

	merge_retematches(&mut r1,&mut r2);
	assert_eq!(r1, result);
    }
}

*/
