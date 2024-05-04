// src/config.rs

use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use anyhow::{Context, Result};
use crate::io::analyzer_io_type::{AnalyzerInput, AnalyzerType, LookupMethod, VerificationInput, VerificationMethod};


impl AnalyzerInput {
    pub fn load_config<P: AsRef<Path>>(path: P) -> Result<Self> {
        let mut file = File::open(path)
            .context("Failed to open configuration file")?;
        
        let mut contents = String::new();
        file.read_to_string(&mut contents)
            .context("Failed to read configuration file")?;

        let config = toml::from_str(&contents)
            .context("Failed to parse configuration file")?;
        
        Ok(config)
    }
    
    pub fn specific_inline() -> Self {
        Self {
            analysis_type: AnalyzerType::UnderconstrainedCircuit,
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string: HashMap::new(), // This would be set by the user
                iterations: 1,
            },
            lookup_method: LookupMethod::InlineConstraints,
        }
    }

    pub fn random_inline() -> Self {
        Self {
            analysis_type: AnalyzerType::UnderconstrainedCircuit,
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: HashMap::new(),
                iterations: 5,
            },
            lookup_method: LookupMethod::InlineConstraints,
        }
    }

    pub fn random_uninterpreted() -> Self {
        Self {
            analysis_type: AnalyzerType::UnderconstrainedCircuit,
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: HashMap::new(),
                iterations: 5,
            },
            lookup_method: LookupMethod::Uninterpreted,
        }
    }

    pub fn random_interpreted() -> Self {
        Self {
            analysis_type: AnalyzerType::UnderconstrainedCircuit,
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: HashMap::new(),
                iterations: 5,
            },
            lookup_method: LookupMethod::Interpreted,
        }
    }
}
