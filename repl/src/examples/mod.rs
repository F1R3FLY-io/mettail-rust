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
    pub language: LanguageName,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LanguageName {
    RhoCalculus,
    AmbientCalculus,
    Calculator,
}

impl LanguageName {
    pub fn as_str(&self) -> &'static str {
        match self {
            LanguageName::RhoCalculus => "rhocalc",
            LanguageName::AmbientCalculus => "ambient",
            LanguageName::Calculator => "calculator",
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
    /// Get all examples across all languages
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

    /// Get examples by category (any language)
    pub fn by_category(cat: ExampleCategory) -> Vec<&'static Example> {
        Self::all()
            .into_iter()
            .filter(|e| e.category == cat)
            .collect()
    }

    /// Get all examples for a specific language
    pub fn by_language(language: LanguageName) -> Vec<&'static Example> {
        match language {
            LanguageName::RhoCalculus => rhocalc::all(),
            LanguageName::AmbientCalculus => ambient::all(),
            LanguageName::Calculator => calculator::all(),
        }
    }

    /// Get examples by language and category
    pub fn by_language_and_category(
        language: LanguageName,
        cat: ExampleCategory,
    ) -> Vec<&'static Example> {
        Self::all()
            .into_iter()
            .filter(|e| e.language == language && e.category == cat)
            .collect()
    }

    /// Get examples by language name (string) and category
    pub fn by_language_name_and_category(
        language_name: &str,
        cat: ExampleCategory,
    ) -> Vec<&'static Example> {
        Self::all()
            .into_iter()
            .filter(|e| {
                e.language.as_str().eq_ignore_ascii_case(language_name) && e.category == cat
            })
            .collect()
    }
}
