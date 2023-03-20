use halo2_proofs::dev::MockProver;
use halo2_proofs::pasta::Fp as Fr;

use z3::ast::Ast;
use z3::{ast, SatResult, Solver};

mod abstract_expr;
mod layouter;
mod shape;

mod analyzer;
mod sample_circuits;

fn main() {
    // println!("----------------------Circuit----------------------");
    // let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
    // let mut analyzer = analyzer::Analyzer::create_with_circuit(&circuit);
    // let k = 5;

    // let public_input = Fr::from(3);
    // //mockprover verify passes
    // let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
    // prover.verify().expect("verify should work");
    // analyzer.analyze_underconstrained();

    println!("----------------------Multi Circuit----------------------");
    let multi_circuit = sample_circuits::MultiPlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
    let mut analyzer1 = analyzer::Analyzer::create_with_circuit(&multi_circuit);
    let z3_context = z3::Context::new(z3::Config::new());
    let instance_cols: HashMap<ast::Int, i64> =
        Self::extract_instance_cols(analyzer1.layouter.eq_table.clone(), &z3_context);
    let analyzer_input: AnalyzerInput = retrieve_user_input(instance_cols, z3_context);
    analyzer1.analyze_underconstrained(analyzer_input);


    // // This part is not relevant to the underconstrained analyzer.
    // log::debug!("running mock prover...");
    // let public_input1 = Fr::from(3);
    // let k = 5;
    // let prover1 = MockProver::<Fr>::run(k, &multi_circuit, vec![vec![public_input1]]).unwrap();
    // prover1.verify().expect("verify should work");
    // log::debug!("verified via mock prover...");

}

#[cfg(test)]
mod integration_tests;
