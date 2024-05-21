use anyhow::{anyhow, Context, Result};
use log::info;
use std::{collections::HashMap, io};
use crate::{
    circuit_analyzer::{analyzable::AnalyzableField,halo2_proofs_libs::*},
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerOutput, AnalyzerOutputStatus, VerificationMethod
    },
};
/// Retrieves user input for underconstrained circuit analysis.
///
/// This function prompts the user to choose between verifying the circuit for a specific public input
/// or a random number of public inputs. It then collects the necessary user input based on the chosen
/// verification type and constructs an `AnalyzerInput` struct to be used in the underconstrained analysis.
///
pub fn retrieve_user_input_for_underconstrained<F: AnalyzableField>(input: &AnalyzerInput,instance_cols_string: &HashMap<String, i64>) -> Result<HashMap<String, i64>> {


    match input.verification_method {
        VerificationMethod::Specific => {
            let mut specified_instance_cols_string: HashMap<String, i64> = HashMap::new();

            for var in instance_cols_string.iter() {
                info!("Enter value for {} : ", var.0);
                let mut input_var = String::new();
                io::stdin()
                    .read_line(&mut input_var)
                    .expect("Failed to read line");
                specified_instance_cols_string
                    .insert(var.0.clone(), input_var.trim().parse::<i64>()?);
            }
            Ok(specified_instance_cols_string)
        }
        _ => Err(anyhow!("Option Is Invalid")),
    }
}
/// Outputs the result of the analysis.
///
/// This function takes an `AnalyzerInput` and `AnalyzerOutput` as input and prints the corresponding
/// result message based on the `AnalyzerOutputStatus` in the `AnalyzerOutput` struct.
///
pub fn output_result(analyzer_input: &AnalyzerInput, analyzer_output: &AnalyzerOutput) {
    match analyzer_output.output_status {
        AnalyzerOutputStatus::Underconstrained => {
            info!("The circuit is under-constrained.");
        }
        AnalyzerOutputStatus::Overconstrained => 
        {
            match analyzer_input.verification_method {
                VerificationMethod::Specific => {
                    info!("The circuit is over-constrained for this specific input.");
                }
                VerificationMethod::Random => {
                    info!(
                        "The circuit is over-constrained for {} random input(s).",
                        analyzer_input.iterations
                    );
                }
                VerificationMethod::None => {},
            }
        }
        
        AnalyzerOutputStatus::NotUnderconstrained => {
            info!("The circuit is not under-constrained!");
        }
        AnalyzerOutputStatus::NotUnderconstrainedLocal => {
            match analyzer_input.verification_method {
                VerificationMethod::Specific => {
                    info!("The circuit is not under-constrained for this specific input.");
                }
                VerificationMethod::Random => {
                    info!(
                        "The circuit is not under-constrained for {} random input(s).",
                        analyzer_input.iterations
                    );
                }
                VerificationMethod::None => {},
            }
        }
        AnalyzerOutputStatus::UnusedCustomGates => {}
        AnalyzerOutputStatus::UnconstrainedCells => {}
        AnalyzerOutputStatus::UnusedColumns => {}
        AnalyzerOutputStatus::Invalid => {
            info!("The analyzer output is invalid.");
        }
        AnalyzerOutputStatus::NoUnusedCustomGates => {}
        AnalyzerOutputStatus::NoUnconstrainedCells => {}
        AnalyzerOutputStatus::NoUnusedColumns => {}
        AnalyzerOutputStatus::NotUnderconstrainedLocalUninterpretedLookups => {
            match analyzer_input.verification_method {
                VerificationMethod::Specific => {
                    info!("\nTwo assignments found to advice columns, making the circuit under-constrained for this specific input. But the assignmets are not valid in lookup table(s)!
                    \nProbably a false positive.\n");
                }
                VerificationMethod::Random => {
                    info!(
                        "\nTwo assignments found to advice columns, making the circuit under-constrained for {} random input(s). But the assignmets are not valid in lookup table(s)!
                        \nProbably a false positive.\n",
                        analyzer_input.iterations
                    );
                }
                VerificationMethod::None => {},
            }
        },
    }
}
