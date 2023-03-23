use std::collections::HashMap;

use halo2_proofs::dev::MockProver;
use halo2_proofs::pasta::Fp as Fr;

use z3::ast;

mod abstract_expr;
mod layouter;
mod shape;
mod analyzer_io_type;
mod analyzer_io;
mod analyzer;
mod sample_circuits;

use crate::analyzer_io_type::AnalyzerInput;

fn main() {
    // This is for verifying with Mock Prover (unrelated to analyze underconstrained)
    // let public_input = Fr::from(3);
    // let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
    // prover.verify().expect("verify should work");
    
    println!("----------------------Analyzing Circuit----------------------");
    // Note: the (Fr::from(1), Fr::from(1)) in the parameters are meaning less with respect to analyze underconstrained.
    // This is the circuit with only one row 
    let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
    // This is the circuit with multiple rows. Uncomment the following to analyze the multi-row circuit.
    // let circuit = sample_circuits::MultiPlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
    let mut analyzer = analyzer::Analyzer::create_with_circuit(&circuit);
    let z3_context = z3::Context::new(&z3::Config::new());
    let instance_cols: HashMap<ast::Int, i64> =
    analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
    let analyzer_input: AnalyzerInput = analyzer_io::retrieve_user_input(&instance_cols, &z3_context);
    analyzer.analyze_underconstrained(analyzer_input);
}

#[cfg(test)]
mod integration_tests;
