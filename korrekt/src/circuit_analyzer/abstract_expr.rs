use halo2_proofs::{
    arithmetic::Field,
    plonk::{Advice, Any, Column, Expression, Selector},
    poly::Rotation,
};

use std::collections::HashSet;

// abstract interpretation of expressions

// simplest possible abstract domain for expressions
#[derive(Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum AbsResult {
    Variable,
    NonZero,
    Zero,
}
/// Extracts columns and rotations from an expression.
///
/// This function traverses an expression tree and extracts the columns and rotations used within the expression.
/// It recursively examines the expression and adds any encountered `Expression::Advice` columns and their corresponding rotations
/// to the resulting set.
pub fn extract_columns<F: Field>(expr: &Expression<F>) -> HashSet<(Column<Any>, Rotation)> {
    fn recursion<F: Field>(dst: &mut HashSet<(Column<Any>, Rotation)>, expr: &Expression<F>) {
        match expr {
            Expression::Advice (advice_query) => {
                let column = Column{index: advice_query.column_index, column_type: Advice{}};
                dst.insert((column.into(), advice_query.rotation));
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
/// Evaluates an abstract expression and returns the abstract result.
///
/// This function evaluates an abstract expression and returns an abstract result based on the provided selectors.
/// It recursively traverses the expression tree and applies the corresponding evaluation rules to determine the result.
/// The abstract result can be one of the following: `AbsResult::Zero`, `AbsResult::NonZero`, or `AbsResult::Variable`.
///
pub fn eval_abstract<F: Field>(
    expr: &Expression<F>,
    selectors: &HashSet<Selector>,
) -> AbsResult {
    match expr {
        Expression::Constant(v) => {
            if v.is_zero().into() {
                AbsResult::Zero
            } else {
                AbsResult::NonZero
            }
        }
        Expression::Selector(selector) => match selectors.contains(selector) {
            true => AbsResult::NonZero,
            false => AbsResult::Zero,
        },
        Expression::Fixed { .. } => AbsResult::Variable,
        Expression::Advice { .. } => AbsResult::Variable,
        Expression::Instance { .. } => AbsResult::Variable,
        Expression::Negated(expr) => eval_abstract(expr, selectors),
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
                AbsResult::Zero
            } else {
                eval_abstract(expr, selectors)
            }
        }
    }
}
