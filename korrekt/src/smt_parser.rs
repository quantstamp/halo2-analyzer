use std::collections::HashMap;
use std::str;
use try_catch::catch;

#[derive(Debug, PartialEq)]
pub enum Satisfiability {
    SATISFIABLE,
    UNSATISFIABLE
}

#[derive(Debug, PartialEq)]
pub struct FieldElement {
    pub order: String,
    pub element: String,
}

#[derive(Debug, PartialEq)]
pub struct Variable {
    pub name: String,
    pub value: FieldElement
}

#[derive(Debug, PartialEq)]
pub struct ModelResult {
    pub sat: Satisfiability,
    pub result: HashMap<String, Variable>,
}

fn parse_field_element_from_string(value: &str) -> FieldElement {
    // Remove #f and split by "m" to get (field element, field prime).
    let mut elements = value[2..].split("m");
    let value_str = elements.next().unwrap();
    let order_str = elements.next().unwrap();
    let field_element = FieldElement {
        order: order_str.to_string(),
        element: value_str.to_string()
    };
    return field_element
}

pub fn extract_model_response(stream: String) -> ModelResult {
    let mut lines = stream.split("\n");
    // Initializing values
    let mut satisfiability: Satisfiability = Satisfiability::UNSATISFIABLE;
    let mut variables: HashMap::<String, Variable> = HashMap::new();
    let first_line = lines.next().unwrap();
    if first_line.trim() == "sat" {
        satisfiability = Satisfiability::SATISFIABLE;
        for line in lines {
            if line.trim() == "" {
                continue
            }
            catch! {
                try {
                    // Removing the parenthesis, turning ((a #f3m11)) into a #f3m11.
                    let cleaned_line = line.replace(&['(', ')'][..], "");
                    let mut cleaned_parts = cleaned_line.split(" ");
                    let variable_name = cleaned_parts.next().unwrap();
                    let ff_element_string = cleaned_parts.next().unwrap();
                    let ff_element = parse_field_element_from_string(ff_element_string);
                    let variable = Variable{name: variable_name.to_string(), value: ff_element};
                    variables.insert(variable_name.to_string(), variable);
                } catch err {
                    println!("Error in parsing model: {}", err)
                }
            }
        }
    }
    let model = ModelResult {
        sat: satisfiability,
        result: variables
    };
    model
}

pub fn output_model_result(model: &ModelResult) {
    println!("Satisfiability: {:?}", model.sat);
    for variable in &model.result {
        println!(
            "Variable Name: {}, Field Element: {}, Field Order: {}", 
            variable.1.name, variable.1.value.element, variable.1.value.order
        );
    }
}

// Main's Output:
// Satisfiability: SATISFIABLE
// Variable Name: a, Variable Value: FieldElement { order: 11, element: 3 }
// Variable Name: b, Variable Value: FieldElement { order: 11, element: 8 }
