// src/config.rs

use serde::{Deserialize, Serialize};
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
    // Default configuration for general use
    pub fn default() -> Self {
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

    // Specific predefined configurations for typical use cases
    pub fn specific_public_input_inline_lookup() -> Self {
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

    pub fn random_public_input_five_iterations_inline_lookup() -> Self {
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

    pub fn random_public_input_five_iterations_uninterpreted_lookup() -> Self {
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

    pub fn random_public_input_five_iterations_interpreted_lookup() -> Self {
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
