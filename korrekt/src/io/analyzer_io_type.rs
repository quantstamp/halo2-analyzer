use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VerificationMethod {
    Specific,
    Random,
    None
}

#[derive(Debug, PartialEq, Eq,Clone,Copy)]
pub enum LookupMethod {
    Uninterpreted,
    Interpreted,
    InlineConstraints,
    None
}
#[derive(Debug, Clone)]
pub struct AnalyzerInput {
    pub verification_method: VerificationMethod,
    pub iterations: u128,
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

#[derive(Debug, Clone)]
pub enum AnalyzerType {
    UnusedGates,
    UnconstrainedCells,
    UnusedColumns,
    UnderconstrainedCircuit,
}
