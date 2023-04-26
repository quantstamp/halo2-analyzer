use std::collections::HashMap;
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{lookup::Argument},
};
#[derive(Debug, PartialEq)]
pub enum VerificationMethod {
    Specific,
    Random,
}

#[derive(Debug)]
pub struct VerificationInput {
    pub instances_string: HashMap<String, i64>,
    pub iterations: u128
}

#[derive(Debug)]
pub struct AnalyzerInput<F: FieldExt> {
    pub verification_method: VerificationMethod, 
    pub verification_input: VerificationInput,
    pub lookups:Vec<Argument<F>>
}

#[derive(Debug, PartialEq)]
pub enum AnalyzerOutputStatus {
    Invalid,
    Underconstrained,
    Overconstrained,
    NotUnderconstrained,
    NotUnderconstrainedLocal,
}

#[derive(Debug)]
pub struct AnalyzerOutput {
    pub output_status: AnalyzerOutputStatus
}

#[derive(Debug)]
pub enum AnalyzerType {
    UnusedGates,
    UnconstrainedCells,
    UnusedColumns,
    UnderconstrainedCircuit,
}
