// Example definitions and metadata for the REPL
//
// This module provides example processes for exploration,
// organized by theory and category.

pub mod ambient;
pub mod calculator;
pub mod rhocalc;

/// Metadata for an example process
pub struct Example {
    pub name: &'static str,
    pub description: &'static str,
    pub source: &'static str,
    pub category: ExampleCategory,
    pub theory: TheoryName,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TheoryName {
    RhoCalculus,
    AmbientCalculus,
    Calculator,
}

impl TheoryName {
    pub fn as_str(&self) -> &'static str {
        match self {
            TheoryName::RhoCalculus => "rhocalc",
            TheoryName::AmbientCalculus => "ambient",
            TheoryName::Calculator => "calculator",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExampleCategory {
    Simple,
    Branching,
    Complex,
    Parallel,
    Advanced,
    Performance,
    EdgeCase,
    Mobility,  // For ambient calculus
    Security,  // For ambient calculus
    MultiComm, // For rho calculus join patterns
}

impl Example {
    /// Get all examples across all theories
    pub fn all() -> Vec<&'static Example> {
        let mut examples = Vec::new();
        examples.extend(rhocalc::all());
        examples.extend(ambient::all());
        examples.extend(calculator::all());
        examples
    }

    /// Find an example by name
    pub fn by_name(name: &str) -> Option<&'static Example> {
        Self::all().into_iter().find(|e| e.name == name)
    }

    /// Get examples by category (any theory)
    pub fn by_category(cat: ExampleCategory) -> Vec<&'static Example> {
        Self::all()
            .into_iter()
            .filter(|e| e.category == cat)
            .collect()
    }

    /// Get all examples for a specific theory
    pub fn by_theory(theory: TheoryName) -> Vec<&'static Example> {
        match theory {
            TheoryName::RhoCalculus => rhocalc::all(),
            TheoryName::AmbientCalculus => ambient::all(),
            TheoryName::Calculator => calculator::all(),
        }
    }

    /// Get examples by theory and category
    pub fn by_theory_and_category(
        theory: TheoryName,
        cat: ExampleCategory,
    ) -> Vec<&'static Example> {
        Self::all()
            .into_iter()
            .filter(|e| e.theory == theory && e.category == cat)
            .collect()
    }
}
