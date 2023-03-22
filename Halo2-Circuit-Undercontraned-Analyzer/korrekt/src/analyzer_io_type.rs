use std::collections::HashMap;
use z3::ast;

// #[derive(Debug)]
// pub struct RandomInput<'a> {
//     pub instances: HashMap<ast::Int<'a>, i64>,
//     pub iterations: u128
// }

// #[derive(Debug)]
// pub struct SpecificInput<'a> {
//     pub instances: HashMap<ast::Int<'a>, i64>
// }

#[derive(Debug, PartialEq)]
pub enum VerificationMethod {
    Specific,
    Random,
}

#[derive(Debug)]
pub struct VerificationInput<'a> {
    pub instances: HashMap<ast::Int<'a>, i64>,
    pub iterations: u128
}

#[derive(Debug)]
pub struct AnalyzerInput<'a> {
    pub verification_method: VerificationMethod, 
    pub verification_input: VerificationInput<'a>,
    pub z3_context: z3::Context
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