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

    fn make(expr: ENode<Math, &Self>) -> Self {
        let expr = {
            let const_args: Option<Vec<Constant>> = expr
                .children
                .iter()
                .map(|meta| match meta.best.as_ref().op {
                    Math::Constant(c) => Some(c),
                    _ => None,
                })
                .collect();

            const_args
                .and_then(|a| eval(expr.op.clone(), &a))
                .map(|c| ENode::leaf(Math::Constant(c)))
                .unwrap_or(expr)
        };

        let best: RecExpr<_> = expr.map_children(|c| c.best.clone()).into();
        let cost = MathCostFn.cost(&expr.map_children(|c| c.cost));
        Self { best, cost }
    }

    fn modify(eclass: &mut EClass<Math, Self>) {
        // NOTE pruning vs not pruning is decided right here
        // not pruning would be just pushing instead of replacing
        let best = eclass.metadata.best.as_ref();
        if best.children.is_empty() {
            eclass.nodes.push(ENode::leaf(best.op.clone()));
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

// rules from herbie v1.3
#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite> { vec![
    rw!("erf-odd";    "(erf (- ?x))"     =>"(- (erf ?x))"),
rw!("erf-erfc";    "(erfc ?x)"     =>"(- 1 (erf ?x))"),
rw!("erfc-erf";    "(erf ?x)"     =>"(- 1 (erfc ?x))"),
rw!("real-part";    "(re (complex ?x ?y))"     =>"?x"),
rw!("imag-part";    "(im (complex ?x ?y))"     =>"?y"),
rw!("complex-add-def";    "(+.c (complex ?a ?b) (complex ?c ?d))"     =>"(complex (+ ?a ?c) (+ ?b ?d))"),
rw!("complex-def-add";    "(complex (+ ?a ?c) (+ ?b ?d))"     =>"(+.c (complex ?a ?b) (complex ?c ?d))"),
rw!("complex-sub-def";    "(-.c (complex ?a ?b) (complex ?c ?d))"     =>"(complex (- ?a ?c) (- ?b ?d))"),
rw!("complex-def-sub";    "(complex (- ?a ?c) (- ?b ?d))"     =>"(-.c (complex ?a ?b) (complex ?c ?d))"),
rw!("complex-neg-def";    "(neg.c (complex ?a ?b))"     =>"(complex (- ?a) (- ?b))"),
rw!("complex-def-neg";    "(complex (- ?a) (- ?b))"     =>"(neg.c (complex ?a ?b))"),
rw!("complex-mul-def";    "(*.c (complex ?a ?b) (complex ?c ?d))"     =>"(complex (- (* ?a ?c) (* ?b ?d)) (+ (* ?a ?d) (* ?b ?c)))"),
rw!("complex-div-def";    "(/.c (complex ?a ?b) (complex ?c ?d))"     =>"(complex (/ (+ (* ?a ?c) (* ?b ?d)) (+ (* ?c ?c) (* ?d ?d))) (/ (- (* ?b ?c) (* ?a ?d)) (+ (* ?c ?c) (* ?d ?d))))"),
rw!("complex-conj-def";    "(conj (complex ?a ?b))"     =>"(complex ?a (- ?b))"),
rw!("if-true";    "(if TRUE ?x ?y)"     =>"?x"),
rw!("if-false";    "(if FALSE ?x ?y)"     =>"?y"),
rw!("if-same";    "(if ?a ?x ?x)"     =>"?x"),
rw!("if-not";    "(if (not ?a) ?x ?y)"     =>"(if ?a ?y ?x)"),
rw!("if-if-or";    "(if ?a ?x (if ?b ?x ?y))"     =>"(if (or ?a ?b) ?x ?y)"),
rw!("if-if-or-not";    "(if ?a ?x (if ?b ?y ?x))"     =>"(if (or ?a (not ?b)) ?x ?y)"),
rw!("if-if-and";    "(if ?a (if ?b ?x ?y) ?y)"     =>"(if (and ?a ?b) ?x ?y)"),
rw!("if-if-and-not";    "(if ?a (if ?b ?y ?x) ?y)"     =>"(if (and ?a (not ?b)) ?x ?y)"),
rw!("lt-same";    "(< ?x ?x)"     =>"FALSE"),
rw!("gt-same";    "(> ?x ?x)"     =>"FALSE"),
rw!("lte-same";    "(<= ?x ?x)"     =>"TRUE"),
rw!("gte-same";    "(>= ?x ?x)"     =>"TRUE"),
rw!("not-lt";    "(not (< ?x ?y))"     =>"(>= ?x ?y)"),
rw!("not-gt";    "(not (> ?x ?y))"     =>"(<= ?x ?y)"),
rw!("not-lte";    "(not (<= ?x ?y))"     =>"(> ?x ?y)"),
rw!("not-gte";    "(not (>= ?x ?y))"     =>"(< ?x ?y)"),
rw!("not-true";    "(not TRUE)"     =>"FALSE"),
rw!("not-false";    "(not FALSE)"     =>"TRUE"),
rw!("not-not";    "(not (not ?a))"     =>"?a"),
rw!("not-and";    "(not (and ?a ?b))"     =>"(or (not ?a) (not ?b))"),
rw!("not-or";    "(not (or ?a ?b))"     =>"(and (not ?a) (not ?b))"),
rw!("and-true-l";    "(and TRUE ?a)"     =>"?a"),
rw!("and-true-r";    "(and ?a TRUE)"     =>"?a"),
rw!("and-false-l";    "(and FALSE ?a)"     =>"FALSE"),
rw!("and-false-r";    "(and ?a FALSE)"     =>"FALSE"),
rw!("and-same";    "(and ?a ?a)"     =>"?a"),
rw!("or-true-l";    "(or TRUE ?a)"     =>"TRUE"),
rw!("or-true-r";    "(or ?a TRUE)"     =>"TRUE"),
rw!("or-false-l";    "(or FALSE ?a)"     =>"?a"),
rw!("or-false-r";    "(or ?a FALSE)"     =>"?a"),
rw!("or-same";    "(or ?a ?a)"     =>"?a"),
rw!("sinh-def";    "(sinh ?x)"     =>"(/ (- (exp ?x) (exp (- ?x))) 2)"),
rw!("cosh-def";    "(cosh ?x)"     =>"(/ (+ (exp ?x) (exp (- ?x))) 2)"),
rw!("tanh-def";    "(tanh ?x)"     =>"(/ (- (exp ?x) (exp (- ?x))) (+ (exp ?x) (exp (- ?x))))"),
rw!("tanh-def";    "(tanh ?x)"     =>"(/ (- (exp (* 2 ?x)) 1) (+ (exp (* 2 ?x)) 1))"),
rw!("tanh-def";    "(tanh ?x)"     =>"(/ (- 1 (exp (* -2 ?x))) (+ 1 (exp (* -2 ?x))))"),
rw!("sinh-cosh";    "(- (* (cosh ?x) (cosh ?x)) (* (sinh ?x) (sinh ?x)))"     =>"1"),
rw!("sinh-+-cosh";    "(+ (cosh ?x) (sinh ?x))"     =>"(exp ?x)"),
rw!("sinh---cosh";    "(- (cosh ?x) (sinh ?x))"     =>"(exp (- ?x))"),
rw!("sin-neg";    "(sin (- ?x))"     =>"(- (sin ?x))"),
rw!("cos-neg";    "(cos (- ?x))"     =>"(cos ?x)"),
rw!("tan-neg";    "(tan (- ?x))"     =>"(- (tan ?x))"),
rw!("sin-0";    "(sin 0)"     =>"0"),
rw!("cos-0";    "(cos 0)"     =>"1"),
rw!("tan-0";    "(tan 0)"     =>"0"),
rw!("cos-sin-sum";    "(+ (* (cos ?a) (cos ?a)) (* (sin ?a) (sin ?a)))"     =>"1"),
rw!("1-sub-cos";    "(- 1 (* (cos ?a) (cos ?a)))"     =>"(* (sin ?a) (sin ?a))"),
rw!("1-sub-sin";    "(- 1 (* (sin ?a) (sin ?a)))"     =>"(* (cos ?a) (cos ?a))"),
rw!("-1-add-cos";    "(+ (* (cos ?a) (cos ?a)) -1)"     =>"(- (* (sin ?a) (sin ?a)))"),
rw!("-1-add-sin";    "(+ (* (sin ?a) (sin ?a)) -1)"     =>"(- (* (cos ?a) (cos ?a)))"),
rw!("sub-1-cos";    "(- (* (cos ?a) (cos ?a)) 1)"     =>"(- (* (sin ?a) (sin ?a)))"),
rw!("sub-1-sin";    "(- (* (sin ?a) (sin ?a)) 1)"     =>"(- (* (cos ?a) (cos ?a)))"),
rw!("sin-PI/6";    "(sin (/ PI 6))"     =>"1/2"),
rw!("sin-PI/4";    "(sin (/ PI 4))"     =>"(/ (sqrt 2) 2)"),
rw!("sin-PI/3";    "(sin (/ PI 3))"     =>"(/ (sqrt 3) 2)"),
rw!("sin-PI/2";    "(sin (/ PI 2))"     =>"1"),
rw!("sin-PI";    "(sin PI)"     =>"0"),
rw!("sin-+PI";    "(sin (+ ?x PI))"     =>"(- (sin ?x))"),
rw!("sin-+PI/2";    "(sin (+ ?x (/ PI 2)))"     =>"(cos ?x)"),
rw!("cos-PI/6";    "(cos (/ PI 6))"     =>"(/ (sqrt 3) 2)"),
rw!("cos-PI/4";    "(cos (/ PI 4))"     =>"(/ (sqrt 2) 2)"),
rw!("cos-PI/3";    "(cos (/ PI 3))"     =>"1/2"),
rw!("cos-PI/2";    "(cos (/ PI 2))"     =>"0"),
rw!("cos-PI";    "(cos PI)"     =>"-1"),
rw!("cos-+PI";    "(cos (+ ?x PI))"     =>"(- (cos ?x))"),
rw!("cos-+PI/2";    "(cos (+ ?x (/ PI 2)))"     =>"(- (sin ?x))"),
rw!("tan-PI/6";    "(tan (/ PI 6))"     =>"(/ 1 (sqrt 3))"),
rw!("tan-PI/4";    "(tan (/ PI 4))"     =>"1"),
rw!("tan-PI/3";    "(tan (/ PI 3))"     =>"(sqrt 3)"),
rw!("tan-PI";    "(tan PI)"     =>"0"),
rw!("tan-+PI";    "(tan (+ ?x PI))"     =>"(tan ?x)"),
rw!("tan-+PI/2";    "(tan (+ ?x (/ PI 2)))"     =>"(- (/ 1 (tan ?x)))"),
rw!("hang-0p-tan";    "(/ (sin ?a) (+ 1 (cos ?a)))"     =>"(tan (/ ?a 2))"),
rw!("hang-0m-tan";    "(/ (- (sin ?a)) (+ 1 (cos ?a)))"     =>"(tan (/ (- ?a) 2))"),
rw!("hang-p0-tan";    "(/ (- 1 (cos ?a)) (sin ?a))"     =>"(tan (/ ?a 2))"),
rw!("hang-m0-tan";    "(/ (- 1 (cos ?a)) (- (sin ?a)))"     =>"(tan (/ (- ?a) 2))"),
rw!("hang-p-tan";    "(/ (+ (sin ?a) (sin ?b)) (+ (cos ?a) (cos ?b)))"     =>"(tan (/ (+ ?a ?b) 2))"),
rw!("hang-m-tan";    "(/ (- (sin ?a) (sin ?b)) (+ (cos ?a) (cos ?b)))"     =>"(tan (/ (- ?a ?b) 2))"),
rw!("log-E";    "(log E)"     =>"1"),
rw!("log-prod";    "(log (* ?a ?b))"     =>"(+ (log ?a) (log ?b))"),
rw!("log-div";    "(log (/ ?a ?b))"     =>"(- (log ?a) (log ?b))"),
rw!("log-rec";    "(log (/ 1 ?a))"     =>"(- (log ?a))"),
rw!("log-pow";    "(log (pow ?a ?b))"     =>"(* ?b (log ?a))"),
rw!("exp-to-pow";    "(exp (* (log ?a) ?b))"     =>"(pow ?a ?b)"),
rw!("pow-plus";    "(* (pow ?a ?b) ?a)"     =>"(pow ?a (+ ?b 1))"),
rw!("unpow1/2";    "(pow ?a 1/2)"     =>"(sqrt ?a)"),
rw!("unpow2";    "(pow ?a 2)"     =>"(* ?a ?a)"),
rw!("unpow3";    "(pow ?a 3)"     =>"(* (* ?a ?a) ?a)"),
rw!("unpow1/3";    "(pow ?a 1/3)"     =>"(cbrt ?a)"),
rw!("unpow0";    "(pow ?a 0)"     =>"1"),
rw!("pow-base-1";    "(pow 1 ?a)"     =>"1"),
rw!("unpow1";    "(pow ?a 1)"     =>"?a"),
rw!("unpow-1";    "(pow ?a -1)"     =>"(/ 1 ?a)"),
rw!("prod-exp";    "(* (exp ?a) (exp ?b))"     =>"(exp (+ ?a ?b))"),
rw!("rec-exp";    "(/ 1 (exp ?a))"     =>"(exp (- ?a))"),
rw!("div-exp";    "(/ (exp ?a) (exp ?b))"     =>"(exp (- ?a ?b))"),
rw!("exp-prod";    "(exp (* ?a ?b))"     =>"(pow (exp ?a) ?b)"),
rw!("exp-sqrt";    "(exp (/ ?a 2))"     =>"(sqrt (exp ?a))"),
rw!("exp-cbrt";    "(exp (/ ?a 3))"     =>"(cbrt (exp ?a))"),
rw!("exp-lft-sqr";    "(exp (* ?a 2))"     =>"(* (exp ?a) (exp ?a))"),
rw!("exp-lft-cube";    "(exp (* ?a 3))"     =>"(pow (exp ?a) 3)"),
rw!("exp-sum";    "(exp (+ ?a ?b))"     =>"(* (exp ?a) (exp ?b))"),
rw!("exp-neg";    "(exp (- ?a))"     =>"(/ 1 (exp ?a))"),
rw!("exp-diff";    "(exp (- ?a ?b))"     =>"(/ (exp ?a) (exp ?b))"),
rw!("exp-0";    "(exp 0)"     =>"1"),
rw!("exp-1-e";    "(exp 1)"     =>"E"),
rw!("1-exp";    "1"     =>"(exp 0)"),
rw!("e-exp-1";    "E"     =>"(exp 1)"),
rw!("rem-exp-log";    "(exp (log ?x))"     =>"?x"),
rw!("rem-log-exp";    "(log (exp ?x))"     =>"?x"),
rw!("cube-unmult";    "(* ?x (* ?x ?x))"     =>"(pow ?x 3)"),
rw!("cube-prod";    "(pow (* ?x ?y) 3)"     =>"(* (pow ?x 3) (pow ?y 3))"),
rw!("cube-div";    "(pow (/ ?x ?y) 3)"     =>"(/ (pow ?x 3) (pow ?y 3))"),
rw!("cube-mult";    "(pow ?x 3)"     =>"(* ?x (* ?x ?x))"),
rw!("rem-cube-cbrt";    "(pow (cbrt ?x) 3)"     =>"?x"),
rw!("rem-cbrt-cube";    "(cbrt (pow ?x 3))"     =>"?x"),
rw!("cube-neg";    "(pow (- ?x) 3)"     =>"(- (pow ?x 3))"),
rw!("sqr-neg";    "(* (- ?x) (- ?x))"     =>"(* ?x ?x)"),
rw!("rem-square-sqrt";    "(* (sqrt ?x) (sqrt ?x))"     =>"?x"),
rw!("rem-sqrt-square";    "(sqrt (* ?x ?x))"     =>"(fabs ?x)"),
rw!("div-sub.c";    "(/.c (-.c ?a ?b) ?c)"     =>"(-.c (/.c ?a ?c) (/.c ?b ?c))"),
rw!("times-frac.c";    "(/.c (*.c ?a ?b) (*.c ?c ?d))"     =>"(*.c (/.c ?a ?c) (/.c ?b ?d))"),
rw!("div-sub";    "(/ (- ?a ?b) ?c)"     =>"(- (/ ?a ?c) (/ ?b ?c))"),
rw!("times-frac";    "(/ (* ?a ?b) (* ?c ?d))"     =>"(* (/ ?a ?c) (/ ?b ?d))"),
rw!("+-lft-identity";    "(+ 0 ?a)"     =>"?a"),
rw!("+-rgt-identity";    "(+ ?a 0)"     =>"?a"),
rw!("--rgt-identity";    "(- ?a 0)"     =>"?a"),
rw!("sub0-neg";    "(- 0 ?a)"     =>"(- ?a)"),
rw!("remove-double-neg";    "(- (- ?a))"     =>"?a"),
rw!("*-lft-identity";    "(* 1 ?a)"     =>"?a"),
rw!("*-rgt-identity";    "(* ?a 1)"     =>"?a"),
rw!("/-rgt-identity";    "(/ ?a 1)"     =>"?a"),
rw!("mul-1-neg";    "(* -1 ?a)"     =>"(- ?a)"),
rw!("+-inverses";    "(- ?a ?a)"     =>"0"),
rw!("*-inverses";    "(/ ?a ?a)"     =>"1"),
rw!("div0";    "(/ 0 ?a)"     =>"0"),
rw!("mul0";    "(* 0 ?a)"     =>"0"),
rw!("mul0";    "(* ?a 0)"     =>"0"),
rw!("remove-double-div";    "(/ 1 (/ 1 ?a))"     =>"?a"),
rw!("rgt-mult-inverse";    "(* ?a (/ 1 ?a))"     =>"1"),
rw!("lft-mult-inverse";    "(* (/ 1 ?a) ?a)"     =>"1"),
rw!("swap-sqr";    "(* (* ?a ?b) (* ?a ?b))"     =>"(* (* ?a ?a) (* ?b ?b))"),
rw!("unswap-sqr";    "(* (* ?a ?a) (* ?b ?b))"     =>"(* (* ?a ?b) (* ?a ?b))"),
rw!("difference-of-squares";    "(- (* ?a ?a) (* ?b ?b))"     =>"(* (+ ?a ?b) (- ?a ?b))"),
rw!("difference-of-sqr-1";    "(- (* ?a ?a) 1)"     =>"(* (+ ?a 1) (- ?a 1))"),
rw!("difference-of-sqr--1";    "(+ (* ?a ?a) -1)"     =>"(* (+ ?a 1) (- ?a 1))"),
rw!("sqr-pow";    "(pow ?a ?b)"     =>"(* (pow ?a (/ ?b 2)) (pow ?a (/ ?b 2)))"),
rw!("pow-sqr";    "(* (pow ?a ?b) (pow ?a ?b))"     =>"(pow ?a (* 2 ?b))"),
rw!("distribute-lft-neg-in";    "(- (* ?a ?b))"     =>"(* (- ?a) ?b)"),
rw!("distribute-rgt-neg-in";    "(- (* ?a ?b))"     =>"(* ?a (- ?b))"),
rw!("distribute-lft-neg-out";    "(* (- ?a) ?b)"     =>"(- (* ?a ?b))"),
rw!("distribute-rgt-neg-out";    "(* ?a (- ?b))"     =>"(- (* ?a ?b))"),
rw!("distribute-neg-in";    "(- (+ ?a ?b))"     =>"(+ (- ?a) (- ?b))"),
rw!("distribute-neg-out";    "(+ (- ?a) (- ?b))"     =>"(- (+ ?a ?b))"),
rw!("distribute-frac-neg";    "(/ (- ?a) ?b)"     =>"(- (/ ?a ?b))"),
rw!("distribute-neg-frac";    "(- (/ ?a ?b))"     =>"(/ (- ?a) ?b)"),
rw!("distribute-lft-in.c";    "(*.c ?a (+.c ?b ?c))"     =>"(+.c (*.c ?a ?b) (*.c ?a ?c))"),
rw!("distribute-rgt-in.c";    "(*.c ?a (+.c ?b ?c))"     =>"(+.c (*.c ?b ?a) (*.c ?c ?a))"),
rw!("distribute-lft-out.c";    "(+.c (*.c ?a ?b) (*.c ?a ?c))"     =>"(*.c ?a (+.c ?b ?c))"),
rw!("distribute-lft-out--.c";    "(-.c (*.c ?a ?b) (*.c ?a ?c))"     =>"(*.c ?a (-.c ?b ?c))"),
rw!("distribute-rgt-out.c";    "(+.c (*.c ?b ?a) (*.c ?c ?a))"     =>"(*.c ?a (+.c ?b ?c))"),
rw!("distribute-rgt-out--.c";    "(-.c (*.c ?b ?a) (*.c ?c ?a))"     =>"(*.c ?a (-.c ?b ?c))"),
rw!("distribute-lft1-in.c";    "(+.c (*.c ?b ?a) ?a)"     =>"(*.c (+.c ?b (complex 1 0)) ?a)"),
rw!("distribute-rgt1-in.c";    "(+.c ?a (*.c ?c ?a))"     =>"(*.c (+.c ?c (complex 1 0)) ?a)"),
rw!("distribute-lft-in";    "(* ?a (+ ?b ?c))"     =>"(+ (* ?a ?b) (* ?a ?c))"),
rw!("distribute-rgt-in";    "(* ?a (+ ?b ?c))"     =>"(+ (* ?b ?a) (* ?c ?a))"),
rw!("distribute-lft-out";    "(+ (* ?a ?b) (* ?a ?c))"     =>"(* ?a (+ ?b ?c))"),
rw!("distribute-lft-out--";    "(- (* ?a ?b) (* ?a ?c))"     =>"(* ?a (- ?b ?c))"),
rw!("distribute-rgt-out";    "(+ (* ?b ?a) (* ?c ?a))"     =>"(* ?a (+ ?b ?c))"),
rw!("distribute-rgt-out--";    "(- (* ?b ?a) (* ?c ?a))"     =>"(* ?a (- ?b ?c))"),
rw!("distribute-lft1-in";    "(+ (* ?b ?a) ?a)"     =>"(* (+ ?b 1) ?a)"),
rw!("distribute-rgt1-in";    "(+ ?a (* ?c ?a))"     =>"(* (+ ?c 1) ?a)"),
rw!("count-2";    "(+ ?x ?x)"     =>"(* 2 ?x)"),
rw!("associate-+r+.c";    "(+.c ?a (+.c ?b ?c))"     =>"(+.c (+.c ?a ?b) ?c)"),
rw!("associate-+l+.c";    "(+.c (+.c ?a ?b) ?c)"     =>"(+.c ?a (+.c ?b ?c))"),
rw!("associate-+r-.c";    "(+.c ?a (-.c ?b ?c))"     =>"(-.c (+.c ?a ?b) ?c)"),
rw!("associate-+l-.c";    "(+.c (-.c ?a ?b) ?c)"     =>"(-.c ?a (-.c ?b ?c))"),
rw!("associate--r+.c";    "(-.c ?a (+.c ?b ?c))"     =>"(-.c (-.c ?a ?b) ?c)"),
rw!("associate--l+.c";    "(-.c (+.c ?a ?b) ?c)"     =>"(+.c ?a (-.c ?b ?c))"),
rw!("associate--l-.c";    "(-.c (-.c ?a ?b) ?c)"     =>"(-.c ?a (+.c ?b ?c))"),
rw!("associate--r-.c";    "(-.c ?a (-.c ?b ?c))"     =>"(+.c (-.c ?a ?b) ?c)"),
rw!("associate-*r*.c";    "(*.c ?a (*.c ?b ?c))"     =>"(*.c (*.c ?a ?b) ?c)"),
rw!("associate-*l*.c";    "(*.c (*.c ?a ?b) ?c)"     =>"(*.c ?a (*.c ?b ?c))"),
rw!("associate-*r/.c";    "(*.c ?a (/.c ?b ?c))"     =>"(/.c (*.c ?a ?b) ?c)"),
rw!("associate-*l/.c";    "(*.c (/.c ?a ?b) ?c)"     =>"(/.c (*.c ?a ?c) ?b)"),
rw!("associate-/r*.c";    "(/.c ?a (*.c ?b ?c))"     =>"(/.c (/.c ?a ?b) ?c)"),
rw!("associate-/l*.c";    "(/.c (*.c ?b ?c) ?a)"     =>"(/.c ?b (/.c ?a ?c))"),
rw!("associate-/r/.c";    "(/.c ?a (/.c ?b ?c))"     =>"(*.c (/.c ?a ?b) ?c)"),
rw!("associate-/l/.c";    "(/.c (/.c ?b ?c) ?a)"     =>"(/.c ?b (*.c ?a ?c))"),
rw!("sub-neg.c";    "(-.c ?a ?b)"     =>"(+.c ?a (neg.c ?b))"),
rw!("unsub-neg.c";    "(+.c ?a (neg.c ?b))"     =>"(-.c ?a ?b)"),
rw!("associate-+r+";    "(+ ?a (+ ?b ?c))"     =>"(+ (+ ?a ?b) ?c)"),
rw!("associate-+l+";    "(+ (+ ?a ?b) ?c)"     =>"(+ ?a (+ ?b ?c))"),
rw!("associate-+r-";    "(+ ?a (- ?b ?c))"     =>"(- (+ ?a ?b) ?c)"),
rw!("associate-+l-";    "(+ (- ?a ?b) ?c)"     =>"(- ?a (- ?b ?c))"),
rw!("associate--r+";    "(- ?a (+ ?b ?c))"     =>"(- (- ?a ?b) ?c)"),
rw!("associate--l+";    "(- (+ ?a ?b) ?c)"     =>"(+ ?a (- ?b ?c))"),
rw!("associate--l-";    "(- (- ?a ?b) ?c)"     =>"(- ?a (+ ?b ?c))"),
rw!("associate--r-";    "(- ?a (- ?b ?c))"     =>"(+ (- ?a ?b) ?c)"),
rw!("associate-*r*";    "(* ?a (* ?b ?c))"     =>"(* (* ?a ?b) ?c)"),
rw!("associate-*l*";    "(* (* ?a ?b) ?c)"     =>"(* ?a (* ?b ?c))"),
rw!("associate-*r/";    "(* ?a (/ ?b ?c))"     =>"(/ (* ?a ?b) ?c)"),
rw!("associate-*l/";    "(* (/ ?a ?b) ?c)"     =>"(/ (* ?a ?c) ?b)"),
rw!("associate-/r*";    "(/ ?a (* ?b ?c))"     =>"(/ (/ ?a ?b) ?c)"),
rw!("associate-/l*";    "(/ (* ?b ?c) ?a)"     =>"(/ ?b (/ ?a ?c))"),
rw!("associate-/r/";    "(/ ?a (/ ?b ?c))"     =>"(* (/ ?a ?b) ?c)"),
rw!("associate-/l/";    "(/ (/ ?b ?c) ?a)"     =>"(/ ?b (* ?a ?c))"),
rw!("sub-neg";    "(- ?a ?b)"     =>"(+ ?a (- ?b))"),
rw!("unsub-neg";    "(+ ?a (- ?b))"     =>"(- ?a ?b)"),
rw!("+.c-commutative";    "(+.c ?a ?b)"     =>"(+.c ?b ?a)"),
rw!("*.c-commutative";    "(*.c ?a ?b)"     =>"(*.c ?b ?a)"),
rw!("+-commutative";    "(+ ?a ?b)"     =>"(+ ?b ?a)"),
rw!("*-commutative";    "(* ?a ?b)"     =>"(* ?b ?a)"),

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

fn write_run_data(data_file: &mut File, count_verification: &mut File, iterations: &Vec<Iteration>) -> Vec<f64> {
    let mut search_time: f64 = 0.0;
    let mut apply_time: f64 = 0.0;
    let mut rebuild_time: f64 = 0.0;
    for iteration in iterations {
	write!(count_verification, "{}\n", iteration.egraph_nodes);
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
    let mut node_count_verification = File::create("./node_verification_rete.txt").unwrap();

    let mut data_file = File::create("./timing-results.txt").unwrap();
    let mut all_data: Vec<Vec<f64>> = vec![];
    let mut counter = 0;
    let node_limit = 20000;
    for batchi in 0..20 {
	let batch = &batches[batchi];
	print!("batch {}\n", counter);
	counter += 1;
	if(batch.len() > 0) {
	    let mut runner = SimpleRunner::default()
		.with_iter_limit(100000)
		.with_node_limit(node_limit)
		.with_time_limit(core::time::Duration::from_secs(2000));
	    let mut egraph = EGraph::default();
	    for line in batch {
		egraph.add_expr(&line);
	    }
	    
	    let (iters, error) = runner.run(&mut egraph, &rules());

	    let data = write_run_data(&mut data_file, &mut node_count_verification, &iters);
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
