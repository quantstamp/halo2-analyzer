use std::collections::HashMap;
use std::hash::Hash;
use std::io;

use z3::ast::Ast;
use z3::{ast, SatResult, Solver};

#[derive(Debug)]
pub struct RandomInput <'a>{
    instances: HashMap<ast::Int<'a>, i64>,
    pub iterations: u128
}

#[derive(Debug)]
pub struct SpecificInput <'a>{
    pub instances: HashMap<ast::Int<'a>, i64>
}
#[derive(Debug)]

pub enum VerificationMethod {
    Specific,
    Random,
}
#[derive(Debug)]

pub enum VerificationInput<'a> {
    Specific(SpecificInput<'a>),
    Random(RandomInput<'a>)
}
#[derive(Debug)]

pub struct AnalyzerInput<'a> {
    pub verification_method: VerificationMethod, 
    pub verification_input: VerificationInput<'a>,
    pub z3_context: &'a z3::Context
}
// impl<'a> AnalyzerInput<'a> {
//     pub fn new() -> Self {
//         Self {
//             verification_method: VerificationMethod::Random,
//             verification_input: ,
//             z3_context: todo!(),
//         }
//     }
// }
pub enum AnalyzerOutputStatus {
    Invalid,
    Underconstrained,
    Overconstrained,
    NotUnderconstrained,
    NotUnderconstrainedLocal,
}


pub struct AnalyzerOutput {
    pub output_status: AnalyzerOutputStatus
}


pub fn retrieve_user_input<'a>(
    instance_cols: &HashMap<ast::Int<'a>, i64>,
    z3_context: &'a z3::Context
) -> AnalyzerInput<'a> {
    println!("You can verify the circuit for a specific public input or a random number of public inputs:");
    println!("1. verify the circuit for a specific public input!");
    println!("2. Verify for a random number of public inputs!");

    let mut menu = String::new();
    io::stdin()
        .read_line(&mut menu)
        .expect("Failed to read line");
    
    let verification_type = menu.trim().parse::<i64>().unwrap();
    let mut analyzer_input: AnalyzerInput = AnalyzerInput { verification_method: VerificationMethod::Random, verification_input: VerificationInput::Random(RandomInput { instances: HashMap::new(), iterations: 1 }), z3_context: z3_context };

    match verification_type {
        1 => {
            let mut specified_instance_cols: HashMap<ast::Int, i64> = HashMap::new();
            for mut _var in instance_cols.iter() {
                println!("Enter value for {} : ", _var.0);
                let mut input_var = String::new();
                io::stdin()
                    .read_line(&mut input_var)
                    .expect("Failed to read line");
                specified_instance_cols.insert(_var.0.clone(), input_var.trim().parse::<i64>().unwrap());
            }
            analyzer_input.verification_method = VerificationMethod::Specific;
            analyzer_input.verification_input = VerificationInput::Specific({SpecificInput { instances: specified_instance_cols }});
        }
        2 => {
            let mut input_var = String::new();
            
            println!("How many random public inputs you want to verify?");
            io::stdin()
                .read_line(&mut input_var)
                .expect("Failed to read line");

            let iterations = input_var.trim().parse::<u128>().unwrap();
            analyzer_input.verification_method = VerificationMethod::Random;
            analyzer_input.verification_input =VerificationInput::Random({ RandomInput{instances: instance_cols.clone(), iterations}});
        }
        _ => {}
    };

    analyzer_input.z3_context = z3_context;
    analyzer_input
}

pub fn output_result(analyzer_input: AnalyzerInput, analyzer_output: &AnalyzerOutput) {
    if (matches!(analyzer_output.output_status,AnalyzerOutputStatus::Underconstrained)) {
        println!("The circuit is under-constrained.");
    } else if (matches!(analyzer_output.output_status, AnalyzerOutputStatus::Overconstrained)) {
        println!("The circuit is over-constrained");
    } else if (matches!(analyzer_output.output_status, AnalyzerOutputStatus::NotUnderconstrained)) {
        println!("The circuit is not under-constrained!");
    } else if (matches!(analyzer_output.output_status, AnalyzerOutputStatus::NotUnderconstrainedLocal)) {
        if (matches!(analyzer_input.verification_method, VerificationMethod::Specific)) {
            println!("The circuit is under-constrained for this specific input.");
        } else {
            println!(
                "The circuit is not under-constrained for {} random input(s).",1
                //analyzer_input.verification_input.Random
            );
        }
    } else {
        println!("The analyzer output is invalid.");
    }
}
