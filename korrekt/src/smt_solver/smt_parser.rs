use std::collections::HashMap;
use std::str;

#[derive(Debug, PartialEq)]
pub enum Satisfiability {
    Satisfiable,
    Unsatisfiable,
}
use anyhow::{Context, Result};

#[derive(Debug, PartialEq)]
pub struct FieldElement {
    pub order: String,
    pub element: String,
}

#[derive(Debug, PartialEq)]
pub struct Variable {
    pub name: String,
    pub value: FieldElement,
}

#[derive(Debug, PartialEq)]
pub struct ModelResult {
    pub sat: Satisfiability,
    pub result: HashMap<String, Variable>,
}
/// Parses a field element from a string representation.
///
/// This function parses a string representation of a field element and constructs a `FieldElement`
/// struct containing the element value and its order.
///
fn parse_field_element_from_string(value: &str) -> Result<FieldElement> {
    // Remove #f and split by "m" to get (field element, field prime).
    let mut elements = value[2..].split('m');
    let value_str = elements.next().context("Failed to parse smt result!")?;
    let order_str = elements.next().context("Failed to parse smt result!")?;
    Ok(FieldElement {
        order: order_str.to_owned(),
        element: value_str.to_owned(),
    })
}
/// Extracts the model response from the SMT solver output.
///
/// This function parses the SMT solver output and extracts the model response, including
/// the satisfiability and variable assignments.
pub fn extract_model_response(stream: String) -> Result<ModelResult> {
    let mut lines = stream.split('\n');
    // Initializing values
    let mut satisfiability: Satisfiability = Satisfiability::Unsatisfiable;
    let mut variables: HashMap<String, Variable> = HashMap::new();
    let first_line = lines.next().context("Failed to parse smt result!")?;
    if first_line.trim() == "sat" {
        satisfiability = Satisfiability::Satisfiable;
        for line in lines {
            if line.trim() == "" {
                continue;
            }
            // Removing the parenthesis, turning ((a #f3m11)) into a #f3m11.
            let cleaned_line = line.replace(&['(', ')'][..], "");
            let mut cleaned_parts = cleaned_line.split(' ');
            let variable_name = cleaned_parts
                .next()
                .context("Failed to parse smt result!")?;
            let ff_element_string = cleaned_parts
                .next()
                .context("Failed to parse smt result!")?;
            let ff_element = parse_field_element_from_string(ff_element_string)
                .context("Error in parsing model!")?;
            let variable = Variable {
                name: variable_name.to_owned(),
                value: ff_element,
            };
            variables.insert(variable_name.to_owned(), variable);
        }
    }
    Ok(ModelResult {
        sat: satisfiability,
        result: variables,
    })
}
