
use std::{
    collections::HashMap,
    io,
};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{lookup::Argument},
};
use crate::analyzer_io_type::{
    AnalyzerInput, 
    AnalyzerOutput,
    AnalyzerOutputStatus,
    VerificationInput,
    VerificationMethod,
    AnalyzerType,
};


pub fn retrieve_user_input_for_underconstrained<F: FieldExt>(
    instance_cols_string: &HashMap<String, i64>,
) -> AnalyzerInput<F> {
    println!("You can verify the circuit for a specific public input or a random number of public inputs:");
    println!("1. verify the circuit for a specific public input!");
    println!("2. Verify for a random number of public inputs!");

    let mut menu = String::new();
    io::stdin()
        .read_line(&mut menu)
        .expect("Failed to read line");
        let verification_type = menu.trim().parse::<i64>().unwrap();
    
    let mut analyzer_input: AnalyzerInput<F> = AnalyzerInput::<F> { 
        verification_method: VerificationMethod::Random,
        verification_input: VerificationInput { 
            iterations: 1,
            instances_string: HashMap::new(), 
        }, 
        lookups:[].to_vec()
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

pub fn output_result<F: FieldExt>(analyzer_input: AnalyzerInput<F>, analyzer_output: &AnalyzerOutput) {
    match analyzer_output.output_status {
        AnalyzerOutputStatus::Underconstrained => {
            println!("The circuit is under-constrained.");
        },
        AnalyzerOutputStatus::Overconstrained => {
            println!("The circuit is over-constrained");
        },
        AnalyzerOutputStatus::NotUnderconstrained => {
            println!("The circuit is not under-constrained!");
        },
        AnalyzerOutputStatus::NotUnderconstrainedLocal => {
            match analyzer_input.verification_method {
                VerificationMethod::Specific => {
                    println!("The circuit is not under-constrained for this specific input.");
                },
                VerificationMethod::Random => {
                    println!(
                        "The circuit is not under-constrained for {} random input(s).",
                        analyzer_input.verification_input.iterations
                    );        
                }
            }
        },
        AnalyzerOutputStatus::Invalid => {
            println!("The analyzer output is invalid.");
        },
    }
}

pub fn retrieve_user_input_for_analyzer_type() -> AnalyzerType {
    println!("Choose the mode of analysis for your circuit.");
    println!("1. Unused Gates");
    println!("2. Unused Columns");
    println!("3. Unconstrained Cells");
    println!("4. Underconstrained Circuit");

    let mut menu = String::new();
    io::stdin()
        .read_line(&mut menu)
        .expect("Failed to read line");
    let menu_int = menu.trim().parse::<i64>().unwrap();
    
    let mut analyzer_type: AnalyzerType;
    match menu_int {
        1 => {
            analyzer_type = AnalyzerType::UnusedGates;
        }
        2 => {
            analyzer_type = AnalyzerType::UnusedColumns;
        }
        3 => {
            analyzer_type = AnalyzerType::UnconstrainedCells;
        }
        4 => {
            analyzer_type = AnalyzerType::UnderconstrainedCircuit;
        }
        _ => {
            panic!("Not a valid mode of analysis.")
        }
    };
    analyzer_type
}
