use anyhow::{anyhow, Context, Result};
use log::info;
use std::{collections::HashMap, io};
use crate::{
    circuit_analyzer::{analyzable::AnalyzableField,halo2_proofs_libs::*},
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerOutput, AnalyzerOutputStatus, AnalyzerType, VerificationInput,
        VerificationMethod,
    },
};
/// Retrieves user input for underconstrained circuit analysis.
///
/// This function prompts the user to choose between verifying the circuit for a specific public input
/// or a random number of public inputs. It then collects the necessary user input based on the chosen
/// verification type and constructs an `AnalyzerInput` struct to be used in the underconstrained analysis.
///
pub fn retrieve_user_input_for_underconstrained<F: AnalyzableField>(
    instance_cols_string: &HashMap<String, i64>,
    cs: &ConstraintSystem<F>,
) -> Result<AnalyzerInput> {
    let mut lookup_uninterpreted_func = false;

    let mut has_lookup = false;
    #[cfg(any(
        feature = "use_zcash_halo2_proofs",
        feature = "use_pse_halo2_proofs",
        feature = "use_axiom_halo2_proofs",
        feature = "use_pse_v1_halo2_proofs",
    ))]
    if !cs.lookups.is_empty() {
        has_lookup = true;
    }

    #[cfg(feature = "use_scroll_halo2_proofs")]
    if !cs.lookups_map.is_empty() {
        has_lookup = true;
    }

    if has_lookup {
        println!("You can use uninterpreted functions for lookup analysis for fast analysis at the cost of potential false positives:");
        println!("1. Verify the circuit with uninterpreted functions for lookups!");
        println!("2. Verify the circuit with all lookup constraints!");
        let mut menu = String::new();
        io::stdin()
            .read_line(&mut menu)
            .expect("Failed to read line");

        let selection = menu
            .trim()
            .parse::<i32>() // Using i32 assuming the options are small integer values
            .expect("Failed to parse input as integer"); // Simplifying error handling for example

        // Setting lookup_uninterpreted_func based on selected option
        lookup_uninterpreted_func = match selection {
            1 => true,
            2 => false,
            _ => {
                println!("Invalid selection, defaulting to 'false'");
                false
            }
        };
    }
    println!("You can verify the circuit for a specific public input or a random number of public inputs:");
    println!("1. verify the circuit for a specific public input!");
    println!("2. Verify for a random number of public inputs!");

    let mut menu = String::new();
    const SPECIFIC: i64 = 1;
    const RANDOM: i64 = 2;
    io::stdin()
        .read_line(&mut menu)
        .expect("Failed to read line");
    let verification_type = menu
        .trim()
        .parse::<i64>()
        .context("Failed to retrieve verification type!")?;

    let mut analyzer_input: AnalyzerInput = AnalyzerInput {
        verification_method: VerificationMethod::Random,
        verification_input: VerificationInput {
            iterations: 1,
            instances_string: HashMap::new(),
        },
        lookup_uninterpreted_func,
    };

    match verification_type {
        SPECIFIC => {
            let mut specified_instance_cols_string: HashMap<String, i64> = HashMap::new();

            for var in instance_cols_string.iter() {
                println!("Enter value for {} : ", var.0);
                let mut input_var = String::new();
                io::stdin()
                    .read_line(&mut input_var)
                    .expect("Failed to read line");
                specified_instance_cols_string
                    .insert(var.0.clone(), input_var.trim().parse::<i64>()?);
            }

            analyzer_input.verification_method = VerificationMethod::Specific;
            analyzer_input.verification_input.instances_string = specified_instance_cols_string;
            Ok(analyzer_input)
        }
        RANDOM => {
            let mut input_var = String::new();

            println!("How many random public inputs you want to verify?");
            io::stdin()
                .read_line(&mut input_var)
                .expect("Failed to read line");

            let iterations = input_var
                .trim()
                .parse::<u128>()
                .context("Failed to retrieve number of iterations!")?;
            analyzer_input.verification_method = VerificationMethod::Random;
            analyzer_input.verification_input.instances_string = instance_cols_string.clone();
            analyzer_input.verification_input.iterations = iterations;
            Ok(analyzer_input)
        }
        _ => Err(anyhow!("Option {} Is Invalid", verification_type)),
    }
}
/// Outputs the result of the analysis.
///
/// This function takes an `AnalyzerInput` and `AnalyzerOutput` as input and prints the corresponding
/// result message based on the `AnalyzerOutputStatus` in the `AnalyzerOutput` struct.
///
pub fn output_result(analyzer_input: AnalyzerInput, analyzer_output: &AnalyzerOutput) {
    match analyzer_output.output_status {
        AnalyzerOutputStatus::Underconstrained => {
            println!("The circuit is under-constrained.");
        }
        AnalyzerOutputStatus::Overconstrained => {
            println!("The circuit is over-constrained");
        }
        AnalyzerOutputStatus::NotUnderconstrained => {
            println!("The circuit is not under-constrained!");
        }
        AnalyzerOutputStatus::NotUnderconstrainedLocal => {
            match analyzer_input.verification_method {
                VerificationMethod::Specific => {
                    println!("The circuit is not under-constrained for this specific input.");
                }
                VerificationMethod::Random => {
                    println!(
                        "The circuit is not under-constrained for {} random input(s).",
                        analyzer_input.verification_input.iterations
                    );
                }
            }
        }
        AnalyzerOutputStatus::UnusedCustomGates => {}
        AnalyzerOutputStatus::UnconstrainedCells => {}
        AnalyzerOutputStatus::UnusedColumns => {}
        AnalyzerOutputStatus::Invalid => {
            println!("The analyzer output is invalid.");
        }
        AnalyzerOutputStatus::NoUnusedCustomGates => {}
        AnalyzerOutputStatus::NoUnconstrainedCells => {}
        AnalyzerOutputStatus::NoUnusedColumns => {}
        AnalyzerOutputStatus::NotUnderconstrainedLocalUniterpretedLookups => {
            match analyzer_input.verification_method {
                VerificationMethod::Specific => {
                    println!("\nTwo assignments found to advice columns, making the circuit under-constrained for this specific input. But the assignmets are not valid in lookup table(s)!
                    \nProbably a false positive.\n");
                }
                VerificationMethod::Random => {
                    println!(
                        "\nTwo assignments found to advice columns, making the circuit under-constrained for {} random input(s). But the assignmets are not valid in lookup table(s)!
                        \nProbably a false positive.\n",
                        analyzer_input.verification_input.iterations
                    );
                }
            }
        },
    }
}
/// Retrieves user input to determine the type of analysis for the circuit.
///
/// This function prompts the user to choose the mode of analysis for the circuit and returns
/// the corresponding `AnalyzerType` enum variant.
///
pub fn retrieve_user_input_for_analyzer_type() -> Result<AnalyzerType> {
    const UNUSED_GATES: i64 = 1;
    const UNUSED_COLUMNS: i64 = 2;
    const UNCONSTRAINED_CELLS: i64 = 3;
    const UNDERCONSTRAINED_CIRCUITS: i64 = 4;

    println!("Choose the mode of analysis for your circuit.");
    println!("1. Unused Gates");
    println!("2. Unused Columns");
    println!("3. Unconstrained Cells");
    println!("4. Underconstrained Circuit");

    let mut menu = String::new();
    io::stdin()
        .read_line(&mut menu)
        .expect("Failed to read line");
    let menu_int = menu
        .trim()
        .parse::<i64>()
        .context("Failed to retrieve the type of analysis!")?;

    let analyzer_type: AnalyzerType;
    match menu_int {
        UNUSED_GATES => {
            analyzer_type = AnalyzerType::UnusedGates;
        }
        UNUSED_COLUMNS => {
            analyzer_type = AnalyzerType::UnusedColumns;
        }
        UNCONSTRAINED_CELLS => {
            analyzer_type = AnalyzerType::UnconstrainedCells;
        }
        UNDERCONSTRAINED_CIRCUITS => {
            analyzer_type = AnalyzerType::UnderconstrainedCircuit;
        }
        _ => {
            panic!("Not a valid mode of analysis.")
        }
    };
    Ok(analyzer_type)
}
