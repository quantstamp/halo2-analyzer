use halo2_proofs::pasta::Fp as Fr;

mod abstract_expr;
mod layouter;
mod shape;
mod analyzer_io_type;
mod analyzer_io;
mod analyzer;
mod sample_circuits;
mod smt;
mod smt_parser;

use crate::analyzer_io_type::AnalyzerInput;

fn main() {
    // This is for verifying with Mock Prover (unrelated to analyze underconstrained)
    // let public_input = Fr::from(3);
    // let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
    // prover.verify().expect("verify should work");
    
    println!("----------------------Analyzing Circuit----------------------");
    //Note: the (Fr::from(1), Fr::from(1)) in the parameters are meaningless with respect to analyze underconstrained.
    //This is the circuit with only one row 
    const COUNT: usize = 128;
    let circuit = sample_circuits::BitDecompositonUnderConstrained::<Fr, COUNT>::new([Fr::from(1); COUNT]);
    //This is the circuit with multiple rows. Uncomment the following to analyze the multi-row circuit.
    //let circuit = sample_circuits::MultiPlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
    let mut analyzer = analyzer::Analyzer::create_with_circuit(&circuit);
    let instance_cols_string = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
    let analyzer_input: AnalyzerInput = analyzer_io::retrieve_user_input(&instance_cols_string);
    analyzer.analyze_underconstrained(analyzer_input);
    
    // let k = 4;
    // let a = Fr::from(1); // F[0]
    // let b = Fr::from(1); // F[1]
    // let out = Fr::from(55); // F[9]s

    // let circuit:sample_circuits::MyCircuit<_> = sample_circuits::MyCircuit::<Fr>(PhantomData);
    // let mut public_input = vec![a, b, out];

    // let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    // prover.assert_satisfied();

    // let mut analyzer = analyzer::Analyzer::create_with_circuit(&circuit);
    // let instance_cols_strings: HashMap<ast::Int, i64> =
    // analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
    // let analyzer_input: AnalyzerInput = analyzer_io::retrieve_user_input(&instance_cols_strings);
    // analyzer.analyze_underconstrained(analyzer_input);
    // let mut f = std::fs::File::create("out.smt2").unwrap();
    // smt::write_query(&mut f);   
}

#[cfg(test)]
mod integration_tests;
