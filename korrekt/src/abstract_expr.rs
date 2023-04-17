use halo2_proofs::{plonk::{Expression, Any, Column, Selector, Advice}, arithmetic::FieldExt, poly::Rotation};

use std::collections::HashSet;

// abstract interpretation of expressions

// simplest possible abstract domain for expressions
#[derive(Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum AbsResult {
    Variable,
    NonZero,
    Zero,
}


pub fn extract_columns<F: FieldExt>(expr: &Expression<F>) -> HashSet<(Column<Any>, Rotation)> {
    fn recursion<F: FieldExt>(dst: &mut HashSet<(Column<Any>, Rotation)>, expr: &Expression<F>) {
        match expr {
            Expression::Advice { query_index: _, column_index, rotation } => {
                let column = Column::<Advice>::new(*column_index, Advice{});
                dst.insert((column.into(), *rotation));
            }
            Expression::Sum(left, right) => {
                recursion(dst, left);
                recursion(dst, right);
            }
            Expression::Product(left, right) => {
                recursion(dst, left);
                recursion(dst, right);
            }
            Expression::Negated(expr) => recursion(dst, expr),
            Expression::Scaled(expr, _) => recursion(dst, expr),
            _ => (),
        }
    }
    let mut set = HashSet::new();
    recursion(&mut set, expr);
    set
}

pub fn eval_abstract<F: FieldExt>(expr: &Expression<F>, selectors: &HashSet<Selector>) -> AbsResult {
    match expr {
        Expression::Constant(v) => if v.is_zero().into() { AbsResult::Zero } else {  AbsResult::NonZero },
        Expression::Selector(selector) => {
            match selectors.contains(selector) {
                true => AbsResult::NonZero,
                false => AbsResult::Zero
            }
        }
        Expression::Fixed { .. } => AbsResult::Variable,
        Expression::Advice { .. } => AbsResult::Variable,
        Expression::Instance { .. } => AbsResult::Variable,
        Expression::Negated(expr)  => {
            let res = eval_abstract(expr, selectors);
            return res
        }
        Expression::Sum(left, right) => {
            let res1 = eval_abstract(left, selectors);
            let res2 = eval_abstract(right, selectors);
            match (res1, res2) {
                (AbsResult::Variable, _) => AbsResult::Variable,
                (_, AbsResult::Variable) => AbsResult::Variable,
                (AbsResult::NonZero, AbsResult::NonZero) => AbsResult::Variable,
                (AbsResult::Zero, AbsResult::Zero) => AbsResult::Zero,
                (AbsResult::Zero, AbsResult::NonZero) => AbsResult::NonZero,
                (AbsResult::NonZero, AbsResult::Zero) => AbsResult::NonZero,
            }
        }
        Expression::Product(left, right) => {
            let res1 = eval_abstract(left, selectors);
            let res2 = eval_abstract(right, selectors);
            match (res1, res2) {
                (AbsResult::Zero, _) => AbsResult::Zero,
                (_, AbsResult::Zero) => AbsResult::Zero,
                (AbsResult::NonZero, AbsResult::NonZero) => AbsResult::NonZero,
                _ => AbsResult::Variable,
            }
        }
        Expression::Scaled(expr, scale) => {
            if scale.is_zero().into() {
                return AbsResult::Zero;
            }  else {
                eval_abstract(expr, selectors)
            }
        }
    }
}