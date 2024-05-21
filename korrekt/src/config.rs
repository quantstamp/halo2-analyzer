use anyhow::{anyhow, Context, Result};
use std::fs::File;
use std::io::Read;
use std::path::Path;
use crate::io::analyzer_io_type::{AnalyzerInput, AnalyzerType, LookupMethod, VerificationMethod};

impl AnalyzerInput {
    pub fn load_config<P: AsRef<Path>>(path: P) -> Result<Self> {
        let mut file = File::open(path)
            .context("Failed to open configuration file")?;
        
        let mut contents = String::new();
        file.read_to_string(&mut contents)
            .context("Failed to read configuration file")?;

        let config: toml::Value = toml::from_str(&contents)
            .context("Failed to parse configuration file")?;

        let analysis_type = config["analyzer_input"]["analysis_type"]
            .as_str()
            .ok_or_else(|| anyhow!("Analysis type not found in the configuration"))?;
        
        
        let iterations = config["analyzer_input"]["iterations"]
                .as_str()
                .ok_or_else(|| anyhow!("Iterations not found in the configuration"))?
                .parse::<u128>()
                .context("Failed to parse iterations as u128")?;
        

        let lookup_method = config["analyzer_input"]["lookup_method"]
            .as_str()
            .ok_or_else(|| anyhow!("Lookup method not found in the configuration"))?;
        
        let verification_method = config["analyzer_input"]["verification_method"]
            .as_str()
            .ok_or_else(|| anyhow!("Verification method not found in the configuration"))?;
        
        Ok(AnalyzerInput {
            verification_method: Self::parse_verification_method(verification_method).unwrap(),
            lookup_method: Self::parse_lookup_method(lookup_method).unwrap(),
            iterations
        })
    }
    fn parse_analysis_type(input: &str) -> Result<AnalyzerType> {
        match input {
            "unused_gates" => Ok(AnalyzerType::UnusedGates),
            "unused_columns" => Ok(AnalyzerType::UnusedColumns),
            "unconstrained_cells" => Ok(AnalyzerType::UnconstrainedCells),
            "UnderconstrainedCircuit" => Ok(AnalyzerType::UnderconstrainedCircuit),
            _ => Err(anyhow::anyhow!("Invalid analysis type")),
        }
    }
    
    fn parse_verification_method(input: &str) -> Result<VerificationMethod> {
        match input {
            "specific" => Ok(VerificationMethod::Specific),
            "random" => Ok(VerificationMethod::Random),
            _ => Err(anyhow::anyhow!("Invalid verification method")),
        }
    }
    
    fn parse_lookup_method(input: &str) -> Result<LookupMethod> {
        match input {
            "uninterpreted" => Ok(LookupMethod::Uninterpreted),
            "interpreted" => Ok(LookupMethod::Interpreted),
            "inline" => Ok(LookupMethod::InlineConstraints),
            _ => Err(anyhow::anyhow!("Invalid lookup method")),
        }
    }
}
