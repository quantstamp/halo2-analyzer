#[cfg(test)]
#[cfg(feature = "use_zcash_halo2_proofs")]
mod tests {
    use crate::circuit_analyzer::analyzer::Analyzer;
    use crate::io::analyzer_io_type::{AnalyzerType, LookupMethod};
    use crate::io::{
        analyzer_io_type,
        analyzer_io_type::{AnalyzerOutputStatus, VerificationMethod},
    };
    use crate::sample_circuits::zcash as sample_circuits;
    use zcash_halo2_proofs::pasta::Fp as Fr;

    use std::marker::PhantomData;

    #[test]
    fn create_zcash_analyzer_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let analyzer_setup = Analyzer::new(&circuit, k ,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

        assert!(analyzer_setup.analyzer.cs.gates.len().eq(&3));
        assert!(analyzer_setup.analyzer.cs.degree().eq(&3));
        //assert!(analyzer.cs.num_advice_columns().eq(&3));
        //assert!(analyzer.cs.num_instance_columns().eq(&1));
        //assert!(analyzer.cs.num_selectors.eq(&1) || analyzer.cs.num_fixed_columns().eq(&1));
    }

    #[test]
    fn extract_instance_cols_zcash_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let analyzer_setup = Analyzer::new(&circuit, k ,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();
        assert!(analyzer_setup.analyzer.instace_cells.len().eq(&1));
        assert!(analyzer_setup.analyzer.instace_cells.contains_key("I-0-0"));
        assert!(analyzer_setup.analyzer.instace_cells.iter().next().unwrap().1.eq(&0));
    }

    #[test]
    fn set_user_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;


        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let analyzer_setup = Analyzer::new(&circuit, k ,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();
        assert!(analyzer_setup.analyzer.instace_cells.len().eq(&1));


        assert!(analyzer_input
            .verification_method
            .eq(&VerificationMethod::Random));
        assert!(analyzer_input.iterations.eq(&5));
    }

    #[test]
    fn simple_test() {
        let circuit = sample_circuits::simple::mul::MulCircuit::<Fr>::default();
        let k: u32 = 3;

        

        

        

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

        assert!(analyzer_setup.analyzer.instace_cells.clone().len().eq(&2));

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_enough_random_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        

        

        

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();
        assert!(analyzer_setup.analyzer.instace_cells.clone().len().eq(&1));

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrained));
    }

    #[test]
    fn not_under_constrained_not_enough_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        

        

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 1,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();
        assert!(analyzer_setup.analyzer.instace_cells.clone().len().eq(&1));

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_not_enough_input_1_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        

        

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 4,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();
        assert!(analyzer_setup.analyzer.instace_cells.clone().len().eq(&1));

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    // #[test]
    // fn not_under_constrained_exact_spec_input_test() {
    //     let circuit =
    //         sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
    //         );
    //     let k: u32 = 11;

        

        

        

    //     let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
    //         verification_method: VerificationMethod::Specific,
    //         iterations: 1,
    //         lookup_method: LookupMethod::InlineConstraints,
    //     };

    //     let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

    //     assert!(analyzer_setup.analyzer.instace_cells.len().eq(&1));
    //     let mut specified_instance_cols = HashMap::new();
    //     for var in analyzer_setup.analyzer.instace_cells.iter() {
    //         specified_instance_cols.insert(var.0.clone(), 3);
    //     }

    //     let output_status = analyzer_setup.analyzer
    //         .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
    //         .unwrap()
    //         .output_status;
    //     assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    // }

    // #[test]
    // fn not_under_constrained_not_exact_spec_input_test() {
    //     let circuit =
    //         sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
    //         );
    //     let k: u32 = 11;

    //     let mut analyzer_setup = Analyzer::new(&circuit, k ,AnalyzerType::UnderconstrainedCircuit,None).unwrap();

    //     assert!(analyzer_setup.analyzer.instace_cells.len().eq(&1));
    //     let mut specified_instance_cols = HashMap::new();
    //     for var in analyzer_setup.analyzer.instace_cells.iter() {
    //         specified_instance_cols.insert(var.0.clone(), 1);
    //     }

        

    //     let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
    //         verification_method: VerificationMethod::Specific,
    //         iterations: 1,
    //         lookup_method: LookupMethod::InlineConstraints,
    //     };

    //     let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

    //     let output_status = analyzer_setup.analyzer
    //         .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
    //         .unwrap()
    //         .output_status;
    //     assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    // }

    #[test]
    fn under_constrained_enough_random_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<
                Fr,
            >::default();
        let k: u32 = 11;

        
        

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::InlineConstraints,
        };
        
        let analyzer_setup = Analyzer::new(&circuit, k ,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();
        assert!(analyzer_setup.analyzer.instace_cells.clone().len().eq(&1));

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn under_constrained_not_enough_random_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<
                Fr,
            >::default();
        let k: u32 = 11;

        

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 1,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let analyzer_setup = Analyzer::new(&circuit, k ,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();
        assert!(analyzer_setup.analyzer.instace_cells.clone().len().eq(&1));


        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    // #[test]
    // fn under_constrained_exact_spec_input_test() {
    //     let circuit =
    //         sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<
    //             Fr,
    //         >::default();
    //     let k: u32 = 11;

        

       

        

    //     let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
    //         verification_method: VerificationMethod::Specific,
    //         iterations: 1,
    //         lookup_method: LookupMethod::InlineConstraints,
    //     };

    //     let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

    //     assert!(analyzer_setup.analyzer.instace_cells.len().eq(&1));
    //     let mut specified_instance_cols = HashMap::new();
    //     for var in analyzer_setup.analyzer.instace_cells.iter() {
    //         specified_instance_cols.insert(var.0.clone(), 3);
    //     }

    //     let output_status = analyzer_setup.analyzer
    //         .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
    //         .unwrap()
    //         .output_status;
    //     assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    // }

    // #[test]
    // fn under_constrained_not_exact_spec_input_test() {
    //     let circuit =
    //         sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<
    //             Fr,
    //         >::default();
    //     let k: u32 = 11;

        

        

        

    //     let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
    //         verification_method: VerificationMethod::Specific,
    //         iterations: 1,
    //         lookup_method: LookupMethod::InlineConstraints,
    //     };

    //     let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

    //     assert!(analyzer_setup.analyzer.instace_cells.len().eq(&1));
    //     let mut specified_instance_cols = HashMap::new();
    //     for var in analyzer_setup.analyzer.instace_cells.iter() {
    //         specified_instance_cols.insert(var.0.clone(), 1);
    //     }

    //     let output_status = analyzer_setup.analyzer
    //         .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
    //         .unwrap()
    //         .output_status;
    //     assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    // }

    #[test]
    fn analyze_unused_columns_test() {
        let circuit: sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit<Fr> =
            sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit::default();
        let k = 5;

        let mut analyzer_setup = Analyzer::new(&circuit, k, AnalyzerType::UnusedColumns,None).unwrap();
        let output_status = analyzer_setup.analyzer.analyze_unused_columns().unwrap().output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::UnusedColumns));
        assert!(analyzer_setup.analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_unused_custom_gates_test() {
        let circuit: sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit<Fr> =
            sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit::default();
        let k = 5;

        //let prover = MockProver::<Fr>::run(k, &circuit, vec![]).unwrap();
        let mut analyzer_setup = Analyzer::new(&circuit, k, AnalyzerType::UnusedGates,None).unwrap();
        let output_status =analyzer_setup.analyzer
            .analyze_unused_custom_gates()
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::UnusedCustomGates));
        assert!(analyzer_setup.analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_unconstrained_cells() {
        let circuit: sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit<Fr> =
            sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit::default();
        let k = 5;

        //let prover = MockProver::<Fr>::run(k, &circuit, vec![]).unwrap();
        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnconstrainedCells,None).unwrap();
        let output_status = analyzer_setup.analyzer
            .analyze_unconstrained_cells()
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::UnconstrainedCells));
        assert!(analyzer_setup.analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_underconstrained_fibonacci_test() {
        let circuit: sample_circuits::copy_constraint::fibonacci::FibonacciCircuit<_> =
            sample_circuits::copy_constraint::fibonacci::FibonacciCircuit::<Fr>(PhantomData);
        let k: u32 = 11;
        
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        println!("output_status: {:?}", output_status);
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }
    #[test]
    fn analyze_underconstrained_fibonacci_constant_init_test() {
        let circuit = sample_circuits::copy_constraint::fibonacci_constant_init::FibonacciCircuit::<
            Fr,
        >(PhantomData);
        let k: u32 = 11;

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        println!("output_status: {:?}", output_status);
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }
    #[test]
    fn analyze_underconstrained_single_lookup_test() {
        let circuit =
            sample_circuits::lookup_circuits::lookup_underconstrained::MyCircuit::<Fr>(PhantomData);
        let k = 11;

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn analyze_underconstrained_multiple_uninterpreted_lookup_random_test() {
        let circuit =
            sample_circuits::lookup_circuits::multiple_lookups::MyCircuit::<Fr>(PhantomData);

        let k = 11;
        

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::Uninterpreted,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(
            output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocalUninterpretedLookups)
        );
    }

    #[test]
    fn analyze_underconstrained_multiple_interpreted_lookup_random_test() {
        let circuit =
            sample_circuits::lookup_circuits::multiple_lookups::MyCircuit::<Fr>(PhantomData);

        let k = 11;

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::Interpreted,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }
    #[test]
    fn analyze_underconstrained_multiple_matched_lookups_inline_random_test() {
        let circuit = sample_circuits::lookup_circuits::multiple_matched_lookups::MyCircuit::<Fr>(
            PhantomData,
        );

        let k = 11;

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();


        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }
    #[test]
    fn analyze_underconstrained_multiple_matched_lookups_interpreted_random_test() {
        let circuit = sample_circuits::lookup_circuits::multiple_matched_lookups::MyCircuit::<Fr>(
            PhantomData,
        );

        let k = 11;

        

        

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::Interpreted,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }
    #[test]
    fn analyze_underconstrained_multiple_lookup_random_test() {
        let circuit =
            sample_circuits::lookup_circuits::multiple_lookups::MyCircuit::<Fr>(PhantomData);

        let k = 11;

        

        

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            iterations: 5,
            lookup_method: LookupMethod::InlineConstraints,
        };

        let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

        let output_status = analyzer_setup.analyzer
            .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }
    // #[test]
    // fn analyze_underconstrained_uninterpreted_specific_lookup_test() {
    //     let circuit =
    //         sample_circuits::lookup_circuits::multiple_lookups::MyCircuit::<Fr>(PhantomData);
    //     let k = 11;

        

        
    //     let mut specified_instance_cols = HashMap::new();
    //     specified_instance_cols.insert("I-0-2".to_owned(), 6);
    //     specified_instance_cols.insert("I-0-1".to_owned(), 1);
    //     specified_instance_cols.insert("I-0-0".to_owned(), 1);

        

    //     let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
    //         verification_method: VerificationMethod::Specific,
    //         iterations: 1,
    //         lookup_method: LookupMethod::Uninterpreted,
    //     };

    //     let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

    //     assert!(analyzer_setup.analyzer.instace_cells.len().eq(&3));
    //     let output_status = analyzer_setup.analyzer
    //         .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
    //         .unwrap()
    //         .output_status;
    //     assert!(
    //         output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocalUninterpretedLookups)
    //     );
    // }
    // #[test]
    // fn analyze_underconstrained_interpreted_specific_lookup_test() {
    //     let circuit =
    //         sample_circuits::lookup_circuits::multiple_lookups::MyCircuit::<Fr>(PhantomData);
    //     let k = 11;
        
    //     let mut specified_instance_cols = HashMap::new();
    //     specified_instance_cols.insert("I-0-2".to_owned(), 6);
    //     specified_instance_cols.insert("I-0-1".to_owned(), 1);
    //     specified_instance_cols.insert("I-0-0".to_owned(), 1);

    //     let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
    //         verification_method: VerificationMethod::Specific,
    //         iterations: 1,
    //         lookup_method: LookupMethod::Interpreted,
    //     };

    //     let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();

    //     assert!(analyzer_setup.analyzer.instace_cells.len().eq(&3));
    //     let output_status = analyzer_setup.analyzer
    //         .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
    //         .unwrap()
    //         .output_status;
    //     assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    // }
    // #[test]
    // fn analyze_underconstrained_lookup_test() {
    //     let circuit =
    //         sample_circuits::lookup_circuits::multiple_lookups::MyCircuit::<Fr>(PhantomData);
    //     let k = 11;

        

        
    //     let mut specified_instance_cols = HashMap::new();
    //     specified_instance_cols.insert("I-0-2".to_owned(), 6);
    //     specified_instance_cols.insert("I-0-1".to_owned(), 1);
    //     specified_instance_cols.insert("I-0-0".to_owned(), 1);

        

    //     let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
    //         verification_method: VerificationMethod::Specific,
    //         iterations: 1,
    //         lookup_method: LookupMethod::InlineConstraints,
    //     };

    //     let mut analyzer_setup = Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();
    //     assert!(analyzer_setup.analyzer.instace_cells.len().eq(&3));

    //     let output_status = analyzer_setup.analyzer
    //         .analyze_underconstrained(&analyzer_input,&mut analyzer_setup.smt_file)
    //         .unwrap()
    //         .output_status;
    //     assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    // }
}
