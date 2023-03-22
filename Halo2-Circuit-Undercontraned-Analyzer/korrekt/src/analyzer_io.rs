
use std::{
    collections::HashMap,
    io,
};
use z3::ast;

use crate::analyzer_io_type::{
    AnalyzerInput, 
    AnalyzerOutput,
    AnalyzerOutputStatus,
    VerificationInput,
    VerificationMethod,
    VerificationMethod::Specific,
    VerificationMethod::Random,
};

pub fn retrieve_user_input<'a>(
    instance_cols: &HashMap<ast::Int<'a>, i64>,
    z3_context: &z3::Context
) -> AnalyzerInput<'a> {
    println!("You can verify the circuit for a specific public input or a random number of public inputs:");
    println!("1. verify the circuit for a specific public input!");
    println!("2. Verify for a random number of public inputs!");

    let mut menu = String::new();
    io::stdin()
        .read_line(&mut menu)
        .expect("Failed to read line");
        let verification_type = menu.trim().parse::<i64>().unwrap();
    let mut analyzer_input: AnalyzerInput = analyzer_io_type::AnalyzerInput { verification_method: VerificationMethod::Random, verification_input: analyzer_io_type::VerificationInput::Random(RandomInput { instances: HashMap::new(), iterations: 1 }), z3_context: z3_context };

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
            analyzer_input.verification_input = analyzer_io_type::VerificationInput::Specific({SpecificInput { instances: specified_instance_cols }});
 }
        2 => {
            let mut input_var = String::new();
            
            println!("How many random public inputs you want to verify?");
            io::stdin()
                .read_line(&mut input_var)
                .expect("Failed to read line");

            let iterations = input_var.trim().parse::<u128>().unwrap();
            analyzer_input.verification_method = VerificationMethod::Random;
            analyzer_input.verification_input =analyzer_io_type::VerificationInput::Random({ RandomInput{instances: instance_cols.clone(), iterations}});
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
