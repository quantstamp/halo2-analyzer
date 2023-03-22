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
    z3_context: z3::Context
) -> AnalyzerInput<'a> {
    println!("You can verify the circuit for a specific public input or a random number of public inputs:");
    println!("1. verify the circuit for a specific public input!");
    println!("2. Verify for a random number of public inputs!");

    let mut menu = String::new();
    io::stdin()
        .read_line(&mut menu)
        .expect("Failed to read line");
    
    let analyzer_input: AnalyzerInput;
    match menu.trim() {
        "1" => {
            let mut specified_instance_cols: HashMap<ast::Int, i64> = HashMap::new();
            for mut _var in instance_cols.iter() {
                println!("Enter value for {} : ", _var.0);
                let mut input_var = String::new();
                io::stdin()
                    .read_line(&mut input_var)
                    .expect("Failed to read line");
                specified_instance_cols.insert(_var.0.clone(), input_var.trim().parse::<i64>().unwrap());
            }
            analyzer_input.verification_method = Specific;
            analyzer_input.verification_input = VerificationInput{ instances: specified_instance_cols, iterations: 0 };
        }
        "2" => {
            let mut input_var = String::new();
            
            println!("How many random public inputs you want to verify?");
            io::stdin()
                .read_line(&mut input_var)
                .expect("Failed to read line");

            let iterations = input_var.trim().parse::<u128>().unwrap();
            analyzer_input.verification_method = Random;
            analyzer_input.verification_input = VerificationInput{ instances: instance_cols.clone(), iterations: iterations };
        }
        &_ => {}
    };

    analyzer_input.z3_context = z3_context;
    analyzer_input
}

pub fn output_result(analyzer_input: AnalyzerInput, analyzer_output: AnalyzerOutput) {
    if analyzer_output.output_status == AnalyzerOutputStatus::Underconstrained {
        println!("The circuit is under-constrained.");
    } else if analyzer_output.output_status == AnalyzerOutputStatus::Overconstrained {
        println!("The circuit is over-constrained");
    } else if analyzer_output.output_status == AnalyzerOutputStatus::NotUnderconstrained {
        println!("The circuit is not under-constrained!");
    } else if analyzer_output.output_status == AnalyzerOutputStatus::NotUnderconstrainedLocal {
        if analyzer_input.verification_method == VerificationMethod::Specific {
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
