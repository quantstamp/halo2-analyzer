
#[derive(Debug)]
pub struct RandomInput {
    iterations: u128
}

#[derive(Debug)]
pub struct SpecificInput {
    instances: HashMap<ast::Int<'a>, i64>
}

enum VerificationMethod {
    Specific,
    Random,
}

enum VerificationInput {
    Specific(SpecificInput),
    Random(RandomInput)
}

#[derive(Debug)]
pub struct AnalyzerInput {
    verification_method: VerificationMethod, 
    verification_input: VerificationInput
}

#[derive(Debug)]
pub struct AnalyzerOutput {
    output_status: AnalyzerOutputStatus, 
}

enum AnalyzerOutputStatus {
    Invalid,
    Underconstrained,
    Overconstrained,
    NotUnderconstrained,
}


fn retrieve_user_input<'a>(
    instances: &HashMap<ast::Int<'a>, i64>,
) -> AnalyzerInput {
    println!("You can verify the circuit for a specific public input or a random number of public inputs:");
    println!("1. verify the circuit for a specific public input!");
    println!("2. Verify for a random number of public inputs!");

    let mut menu = String::new();
    io::stdin()
        .read_line(&mut menu)
        .expect("Failed to read line");
    
    let verification_type = menu.trim().parse::<i64>().unwrap();
    let analyzer_input: AnalyzerInput = AnalyzerInput::new();

    match verification_type {
        1 => {
            let mut specified_instances: HashMap<ast::Int, i64> = HashMap::new();
            for mut _var in instance_cols.iter() {
                println!("Enter value for {} : ", _var.0);
                let mut input_var = String::new();
                io::stdin()
                    .read_line(&mut input_var)
                    .expect("Failed to read line");
                specified_instances.insert(_var.0.clone(), input_var.trim().parse::<i64>().unwrap());
            }
            analyzer_input.verification_method = Specific;
            analyzer_input.verification_input = SpecificInput(specified_instances);
        }
        2 => {
            let mut input_var = String::new();
            
            println!("How many random public inputs you want to verify?");
            io::stdin()
                .read_line(&mut input_var)
                .expect("Failed to read line");

            let iterations = input_var.trim().parse::<u128>().unwrap();
            analyzer_input.verification_method = Random;
            analyzer_input.verification_input = RandomInput(iterations);
        }
        &_ => {}
    };

    analyzer_input
}

fn output_result(analyzer_input: AnalyzerInput, analyzer_output: AnalyzerOutput) {
    if verification_method == 1 {
        if result == 1 {
            println!("The circuit is under-constrained.");
        } else if result == 0 {
            println!("The circuit is not under-constrained for this specific input.");
        } else if result == 2 {
            println!("The circuit is not under-constrained!");
        }
    } else if verification_method == 2 {
        if result == 1 {
            println!("The circuit is under-constrained.");
        } else if result == 0 {
            if (iterations == 1) {
                println!(
                    "The circuit is not under-constrained for {} random input.",
                    iterations
                );
            } else {
                println!(
                    "The circuit is not under-constrained for {} random inputs.",
                    iterations
                );
            }
        } else if result == 2 {
            println!("The circuit is not under-constrained!");
        }
    }
}
