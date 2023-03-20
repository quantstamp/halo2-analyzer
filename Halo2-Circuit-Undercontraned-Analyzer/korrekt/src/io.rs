use z3::ast::Ast;
use z3::{ast, SatResult, Solver};

#[derive(Debug)]
pub struct RandomInput {
    instances: HashMap<ast::Int<'a>, i64>,
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
    verification_input: VerificationInput,
    z3_context: z3::Context
}

enum AnalyzerOutputStatus {
    Invalid,
    Underconstrained,
    Overconstrained,
    NotUnderconstrained,
    NotUnderconstrainedLocal,
}

#[derive(Debug)]
pub struct AnalyzerOutput {
    output_status: AnalyzerOutputStatus
}


fn retrieve_user_input<'a>(
    instance_cols: &HashMap<ast::Int<'a>, i64>,
    z3_context: z3::Context
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
            analyzer_input.verification_input = SpecificInput(specified_instance_cols);
        }
        2 => {
            let mut input_var = String::new();
            
            println!("How many random public inputs you want to verify?");
            io::stdin()
                .read_line(&mut input_var)
                .expect("Failed to read line");

            let iterations = input_var.trim().parse::<u128>().unwrap();
            analyzer_input.verification_method = Random;
            analyzer_input.verification_input = RandomInput(instance_cols, iterations);
        }
        &_ => {}
    };

    analyzer_input.z3_context = z3_context;
    analyzer_input
}

fn output_result(analyzer_input: AnalyzerInput, analyzer_output: AnalyzerOutput) {
    if (analyzer_output.output_status == AnalyzerOutputStatus.Underconstrained) {
        println!("The circuit is under-constrained.");
    } else if (analyzer_output.output_status == AnalyzerOutputStatus.Overconstrained) {
        println!("The circuit is over-constrained");
    } else if (analyzer_output.output_status == AnalyzerOutputStatus.NotUnderconstrained) {
        println!("The circuit is not under-constrained!");
    } else if (analyzer_output.output_status == AnalyzerOutputStatus.NotUnderconstrainedLocal) {
        if (analyzer_input.verification_method == VerificationMethod.Specific) {
            println!("The circuit is under-constrained for this specific input.");
        } else {
            println!(
                "The circuit is not under-constrained for {} random input(s).",
                iterations
            );
        }
    } else {
        println!("The analyzer output is invalid.");
    }
}
