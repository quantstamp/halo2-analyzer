use std::collections::HashMap;

use serde::{Deserialize, Serialize};
// #[derive(Debug, PartialEq, Eq)]
#[derive(Debug, PartialEq, Eq, Deserialize, Serialize, Clone)]
pub enum VerificationMethod {
    Specific,
    Random,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct VerificationInput {
    pub instances_string: HashMap<String, i64>,
    pub iterations: u128,
}
#[derive(Debug, PartialEq, Eq, Deserialize, Serialize, Clone)]
pub enum LookupMethod {
    Uninterpreted,
    Interpreted,
    InlineConstraints,
    Invalid
}
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct AnalyzerInput {
    pub analysis_type: AnalyzerType,
    pub verification_method: VerificationMethod,
    pub verification_input: VerificationInput,
    pub lookup_method: LookupMethod
}

#[derive(Debug, PartialEq, Eq)]
pub enum AnalyzerOutputStatus {
    Invalid,
    Underconstrained,
    Overconstrained,
    NotUnderconstrained,
    NotUnderconstrainedLocal,
    NotUnderconstrainedLocalUninterpretedLookups,
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

#[derive(Debug, Deserialize, Serialize, Clone)]
pub enum AnalyzerType {
    UnusedGates,
    UnconstrainedCells,
    UnusedColumns,
    UnderconstrainedCircuit,
}
