
use std::{
    collections::HashMap,
    io,
};

use crate::analyzer_io_type::{
    AnalyzerInput, 
    AnalyzerOutput,
    AnalyzerOutputStatus,
    VerificationInput,
    VerificationMethod,
};

pub fn retrieve_user_input(
    instance_cols_string: &HashMap<String, i64>,
) -> AnalyzerInput {
    println!("You can verify the circuit for a specific public input or a random number of public inputs:");
    println!("1. verify the circuit for a specific public input!");
    println!("2. Verify for a random number of public inputs!");

    let mut menu = String::new();
    io::stdin()
        .read_line(&mut menu)
        .expect("Failed to read line");
        let verification_type = menu.trim().parse::<i64>().unwrap();
    
    let mut analyzer_input: AnalyzerInput = AnalyzerInput { 
        verification_method: VerificationMethod::Random,
        verification_input: VerificationInput { 
            iterations: 1,
            instances_string: HashMap::new(), 
        }, 
    };

    match verification_type {
        1 => {
            let mut specified_instance_cols_string: HashMap<String, i64> = HashMap::new();

            for mut _var in instance_cols_string.iter() {
                println!("Enter value for {} : ", _var.0);
                let mut input_var = String::new();
                io::stdin()
                    .read_line(&mut input_var)
                    .expect("Failed to read line");
                specified_instance_cols_string.insert(_var.0.clone(), input_var.trim().parse::<i64>().unwrap());
            }

            analyzer_input.verification_method = VerificationMethod::Specific;
            analyzer_input.verification_input.instances_string = specified_instance_cols_string;
        }
        2 => {
            let mut input_var = String::new();
            
            println!("How many random public inputs you want to verify?");
            io::stdin()
                .read_line(&mut input_var)
                .expect("Failed to read line");

            let iterations = input_var.trim().parse::<u128>().unwrap();
            analyzer_input.verification_method = VerificationMethod::Random;
            analyzer_input.verification_input.instances_string = instance_cols_string.clone();
            analyzer_input.verification_input.iterations = iterations;
        }
        _ => {}
    };

    analyzer_input
}

pub fn output_result(analyzer_input: AnalyzerInput, analyzer_output: &AnalyzerOutput) {
    if (matches!(analyzer_output.output_status, AnalyzerOutputStatus::Underconstrained)) {
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
                "The circuit is not under-constrained for {} random input(s).",
                analyzer_input.verification_input.iterations
            );
        }
    } else {
        println!("The analyzer output is invalid.");
    }
}