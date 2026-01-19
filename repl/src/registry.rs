use crate::theory::Theory;
use anyhow::{bail, Result};
use std::collections::HashMap;

/// Registry of available theories
pub struct TheoryRegistry {
    theories: HashMap<String, Box<dyn Theory>>,
}

impl TheoryRegistry {
    /// Create a new registry
    pub fn new() -> Self {
        Self { theories: HashMap::new() }
    }

    /// Register a theory
    pub fn register(&mut self, theory: Box<dyn Theory>) {
        let name = theory.name().as_str();
        self.theories.insert(name.to_string(), theory);
    }

    /// Get a theory by name
    pub fn get(&self, name: &str) -> Result<&dyn Theory> {
        self.theories
            .get(name)
            .map(|b| b.as_ref())
            .ok_or_else(|| anyhow::anyhow!("Theory '{}' not found", name))
    }

    /// List all available theories
    pub fn list(&self) -> Vec<&str> {
        self.theories.keys().map(|s| s.as_str()).collect()
    }

    /// Check if a theory exists
    pub fn contains(&self, name: &str) -> bool {
        self.theories.contains_key(name)
    }
}

impl Default for TheoryRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Build the default registry with all available theories
pub fn build_registry() -> Result<TheoryRegistry> {
    let mut registry = TheoryRegistry::new();

    // Register theories
    registry.register(Box::new(crate::theories::RhoCalculusTheory));
    registry.register(Box::new(crate::theories::AmbCalculusTheory));
    // registry.register(Box::new(crate::theories::CalculatorTheory));

    if registry.theories.is_empty() {
        bail!("No theories available.");
    }

    Ok(registry)
}
