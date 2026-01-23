// Calculator example expressions for the REPL
//
// Demonstrates integer arithmetic evaluation and variable binding in the Calculator theory

use super::{Example, ExampleCategory, LanguageName};

pub fn all() -> Vec<&'static Example> {
    vec![
        &SIMPLE_NUMBER,
        &ADDITION,
        &SUBTRACTION,
        &COMPLEX_EXPRESSION,
        &ASSIGNMENT,
        &VARIABLE_LOOKUP,
        &VARIABLE_IN_EXPR,
    ]
}

//=============================================================================
// EXAMPLES
//=============================================================================

pub static SIMPLE_NUMBER: Example = Example {
    name: "simple_number",
    description: "Single integer literal",
    source: "42",
    category: ExampleCategory::Simple,
    language: LanguageName::Calculator,
};

pub static ADDITION: Example = Example {
    name: "addition",
    description: "Simple addition of two numbers",
    source: "5 + 3",
    category: ExampleCategory::Simple,
    language: LanguageName::Calculator,
};

pub static SUBTRACTION: Example = Example {
    name: "subtraction",
    description: "Simple subtraction",
    source: "10 - 4",
    category: ExampleCategory::Simple,
    language: LanguageName::Calculator,
};

pub static COMPLEX_EXPRESSION: Example = Example {
    name: "complex_expr",
    description: "Multi-operator expression with left-to-right evaluation",
    source: "10 + 5 - 3 + 2",
    category: ExampleCategory::Simple,
    language: LanguageName::Calculator,
};

pub static ASSIGNMENT: Example = Example {
    name: "assignment",
    description: "Variable assignment - stores and evaluates expression",
    source: "x = 3 + 2",
    category: ExampleCategory::Simple,
    language: LanguageName::Calculator,
};

pub static VARIABLE_LOOKUP: Example = Example {
    name: "variable_lookup",
    description: "Variable reference - retrieves stored value",
    source: "x",
    category: ExampleCategory::Simple,
    language: LanguageName::Calculator,
};

pub static VARIABLE_IN_EXPR: Example = Example {
    name: "variable_in_expr",
    description: "Using variables in expressions",
    source: "y = x - 4 + 8",
    category: ExampleCategory::Simple,
    language: LanguageName::Calculator,
};
