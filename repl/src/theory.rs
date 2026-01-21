use anyhow::Result;
use std::fmt;

use crate::examples::TheoryName;

/// A trait that all theories must implement to be usable in the REPL
pub trait Theory: Send + Sync {
    /// Get the name of this theory
    fn name(&self) -> TheoryName;

    /// Get the category names exported by this theory
    fn categories(&self) -> Vec<String>;

    /// Get the number of constructors
    fn constructor_count(&self) -> usize;

    /// Get the number of equations
    fn equation_count(&self) -> usize;

    /// Get the number of rewrite rules
    fn rewrite_count(&self) -> usize;

    /// Parse a term from a string (clears var cache for fresh evaluation)
    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>>;
    
    /// Parse a term for environment storage (does NOT clear var cache)
    /// This allows variables like `n` to be shared across multiple env definitions
    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>>;

    /// Run Ascent on a term and return results
    fn run_ascent(&self, term: Box<dyn Term>) -> Result<AscentResults>;

    /// Format a term as a string
    fn format_term(&self, term: &dyn Term) -> String;
    
    // === Environment Support ===
    
    /// Create a new empty environment for this theory
    fn create_env(&self) -> Box<dyn std::any::Any + Send + Sync>;
    
    /// Add a term to the environment under the given name
    /// The category is inferred from the term's category
    fn add_to_env(&self, env: &mut dyn std::any::Any, name: &str, term: &dyn Term) -> Result<()>;
    
    /// Remove a binding from the environment
    fn remove_from_env(&self, env: &mut dyn std::any::Any, name: &str) -> Result<bool>;
    
    /// Clear all bindings from the environment
    fn clear_env(&self, env: &mut dyn std::any::Any);
    
    /// Apply environment substitution to a term
    /// Returns the term with all environment variables replaced
    fn substitute_env(&self, term: &dyn Term, env: &dyn std::any::Any) -> Result<Box<dyn Term>>;
    
    /// List all environment bindings as (name, display) pairs
    fn list_env(&self, env: &dyn std::any::Any) -> Vec<(String, String)>;
    
    /// Check if the environment is empty
    fn is_env_empty(&self, env: &dyn std::any::Any) -> bool;
}

/// A trait for terms (AST nodes) that can be manipulated generically
pub trait Term: fmt::Display + fmt::Debug + Send + Sync {
    /// Clone this term into a Box
    fn clone_box(&self) -> Box<dyn Term>;

    /// Get a unique identifier for this term (for equality comparison)
    fn term_id(&self) -> u64;

    /// Check if this term is equal to another
    fn term_eq(&self, other: &dyn Term) -> bool;

    /// Get this as Any for downcasting
    fn as_any(&self) -> &dyn std::any::Any;
}

/// Results from running Ascent
#[derive(Debug, Clone)]
pub struct AscentResults {
    /// All reachable terms
    pub all_terms: Vec<TermInfo>,

    /// All rewrites (from -> to)
    pub rewrites: Vec<Rewrite>,

    /// Equivalence classes (terms related by equations)
    pub equivalences: Vec<EquivClass>,
}

/// Information about a term in the rewrite graph
#[derive(Debug, Clone)]
pub struct TermInfo {
    pub term_id: u64,
    pub display: String,
    pub is_normal_form: bool,
}

/// A rewrite from one term to another
#[derive(Debug, Clone)]
pub struct Rewrite {
    pub from_id: u64,
    pub to_id: u64,
    pub rule_name: Option<String>,
}

/// An equivalence class of terms
#[derive(Debug, Clone)]
pub struct EquivClass {
    pub term_ids: Vec<u64>,
}

impl AscentResults {
    /// Create empty results
    pub fn empty() -> Self {
        Self {
            all_terms: Vec::new(),
            rewrites: Vec::new(),
            equivalences: Vec::new(),
        }
    }

    /// Get normal forms (terms with no outgoing rewrites)
    pub fn normal_forms(&self) -> Vec<&TermInfo> {
        self.all_terms.iter().filter(|t| t.is_normal_form).collect()
    }

    /// Get rewrites from a specific term
    pub fn rewrites_from(&self, term_id: u64) -> Vec<&Rewrite> {
        self.rewrites
            .iter()
            .filter(|r| r.from_id == term_id)
            .collect()
    }

    /// Get the equivalence class containing a term
    pub fn equiv_class(&self, term_id: u64) -> Option<&EquivClass> {
        self.equivalences
            .iter()
            .find(|ec| ec.term_ids.contains(&term_id))
    }
}
