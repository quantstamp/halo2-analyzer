use super::{analyzable::AnalyzableField, halo2_proofs_libs::*};
#[cfg(any(
    feature = "use_pse_halo2_proofs",
    feature = "use_axiom_halo2_proofs",
    feature = "use_scroll_halo2_proofs"
))]
use anyhow::anyhow;
use anyhow::{Context, Result};
use num::BigInt;
use num_bigint::Sign;
use std::collections::{HashMap, HashSet};

// abstract interpretation of expressions

// simplest possible abstract domain for expressions
#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone, Copy)]
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
            #[cfg(feature = "use_zcash_halo2_proofs")]
            Expression::Advice(advice_query) => {
                let column = Column {
                    index: advice_query.column_index,
                    column_type: Advice {},
                };
                dst.insert((column.into(), advice_query.rotation));
            }
            #[cfg(any(feature = "use_pse_halo2_proofs", feature = "use_axiom_halo2_proofs",))]
            Expression::Advice(advice_query) => {
                let column = Column {
                    index: advice_query.column_index,
                    column_type: Advice {
                        phase: advice_query.phase,
                    },
                };
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
pub fn eval_abstract<F: AnalyzableField>(
    expr: &Expression<F>,
    selectors: &HashSet<Selector>,
    region_begin: usize,
    region_end: usize,
    row_num: i32,
    fixed: &Vec<Vec<BigInt>>,
    cell_to_cycle_head: &HashMap<String, String>,
    cycle_abs_value: &HashMap<String, AbsResult>,
) -> Result<AbsResult> {
    let evaluation = match expr {
        Expression::Constant(v) => {
            if v.is_zero().into() {
                Ok(AbsResult::Zero)
            } else {
                Ok(AbsResult::NonZero)
            }
        }
        Expression::Selector(selector) => match selectors.contains(selector) {
            true => Ok(AbsResult::NonZero),
            false => Ok(AbsResult::Zero),
        },
        Expression::Fixed(fixed_query) => {
            let col = fixed_query.column_index;
            let row = (fixed_query.rotation.0 + row_num) as usize + region_begin;
            if col < fixed.len() && row < fixed[0].len() {
                if fixed[col][row].sign() == Sign::NoSign {
                    Ok(AbsResult::Zero)
                } else {
                    Ok(AbsResult::Variable)
                }
            } else {
                Ok(AbsResult::Variable)
            }
        }
        Expression::Advice(advice_query) => {
            let term = format!(
                "A-{}-{}",
                advice_query.column_index,
                advice_query.rotation.0 + row_num + region_begin as i32
            );
            //println!("term: {:?}", term);
            //println!("cell_to_cycle_head: {:?}", cell_to_cycle_head);
            if cell_to_cycle_head.contains_key(&term) {
                if cycle_abs_value.contains_key(&cell_to_cycle_head[&term.clone()]) {
                    //println!("cycle_abs_value[&cell_to_cycle_head[&term]]: {:?}", cycle_abs_value[&cell_to_cycle_head[&term]]);
                    return Ok(cycle_abs_value[&cell_to_cycle_head[&term]]);
                }
            }

            Ok(AbsResult::Variable)
        }
        Expression::Instance(instance_query) => {
            let term = format!(
                "I-{}-{}",
                instance_query.column_index,
                instance_query.rotation.0 + row_num + region_begin as i32
            );
            if cell_to_cycle_head.contains_key(&term) {
                if cycle_abs_value.contains_key(&cell_to_cycle_head[&term.clone()]) {
                    return Ok(cycle_abs_value[&cell_to_cycle_head[&term]]);
                }
            }

            Ok(AbsResult::Variable)
        }
        Expression::Negated(expr) => eval_abstract(
            expr,
            selectors,
            region_begin,
            region_end,
            row_num,
            fixed,
            cell_to_cycle_head,
            cycle_abs_value,
        ),
        Expression::Sum(left, right) => {
            let res1 = eval_abstract(left, selectors,region_begin,region_end, row_num, fixed, cell_to_cycle_head, cycle_abs_value).with_context(|| format!(
                                    "Failed to run abstract evaluation for polynomial at region from row: {} to {}.",
                                    region_begin, region_end
                                ))?;
            let res2 = eval_abstract(right, selectors,region_begin,region_end, row_num, fixed, cell_to_cycle_head, cycle_abs_value).with_context(|| format!(
                                    "Failed to run abstract evaluation for polynomial at region from row: {} to {}.",
                                    region_begin, region_end
                                ))?;
            match (res1, res2) {
                (AbsResult::Variable, _) => Ok(AbsResult::Variable),
                (_, AbsResult::Variable) => Ok(AbsResult::Variable),
                (AbsResult::NonZero, AbsResult::NonZero) => Ok(AbsResult::Variable),
                (AbsResult::Zero, AbsResult::Zero) => Ok(AbsResult::Zero),
                (AbsResult::Zero, AbsResult::NonZero) => Ok(AbsResult::NonZero),
                (AbsResult::NonZero, AbsResult::Zero) => Ok(AbsResult::NonZero),
            }
        }
        Expression::Product(left, right) => {
            let res1 = eval_abstract(left, selectors,region_begin,region_end, row_num, fixed, cell_to_cycle_head, cycle_abs_value).with_context(|| format!(
                                    "Failed to run abstract evaluation for polynomial at region from row: {} to {}.",
                                    region_begin, region_end
                                ))?;
            let res2 = eval_abstract(right, selectors,region_begin,region_end, row_num, fixed, cell_to_cycle_head, cycle_abs_value).with_context(|| format!(
                                    "Failed to run abstract evaluation for polynomial at region from row: {} to {}.",
                                    region_begin, region_end
                                ))?;
            match (res1, res2) {
                (AbsResult::Zero, _) => Ok(AbsResult::Zero),
                (_, AbsResult::Zero) => Ok(AbsResult::Zero),
                (AbsResult::NonZero, AbsResult::NonZero) => Ok(AbsResult::NonZero),
                _ => Ok(AbsResult::Variable),
            }
        }
        Expression::Scaled(expr, scale) => {
            if scale.is_zero().into() {
                Ok(AbsResult::Zero)
            } else {
                eval_abstract(
                    expr,
                    selectors,
                    region_begin,
                    region_end,
                    row_num,
                    fixed,
                    cell_to_cycle_head,
                    cycle_abs_value,
                )
            }
        }
        #[cfg(any(
            feature = "use_pse_halo2_proofs",
            feature = "use_axiom_halo2_proofs",
            feature = "use_scroll_halo2_proofs"
        ))]
        Expression::Challenge(_) => Err(anyhow!(
            "Challenge expression in abstract evaluation resulted in Invalid Expression"
        )),
    };
    evaluation
}
