use std::collections::HashMap;
#[derive(Debug, PartialEq, Eq)]
pub enum VerificationMethod {
    Specific,
    Random,
}

#[derive(Debug)]
pub struct VerificationInput {
    pub instances_string: HashMap<String, i64>,
    pub iterations: u128,
}

#[derive(Debug)]
pub struct AnalyzerInput {
    pub verification_method: VerificationMethod,
    pub verification_input: VerificationInput,
}

#[derive(Debug, PartialEq, Eq)]
pub enum AnalyzerOutputStatus {
    Invalid,
    Underconstrained,
    Overconstrained,
    NotUnderconstrained,
    NotUnderconstrainedLocal,
    UnusedCustomGates,
    NoUnusedCustomGates,
    UnconstrainedCells,
    NoUnconstrainedCells,
    UnusedColumns,
    NoUnusedColumns
}

#[derive(Debug)]
pub struct AnalyzerOutput {
    pub output_status: AnalyzerOutputStatus,
}

#[derive(Debug)]
pub enum AnalyzerType {
    UnusedGates,
    UnconstrainedCells,
    UnusedColumns,
    UnderconstrainedCircuit,
}
