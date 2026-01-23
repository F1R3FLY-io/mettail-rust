use mettail_runtime::Language;
use anyhow::{bail, Result};
use std::collections::HashMap;

// Import generated language implementations directly
use mettail_languages::ambient::AmbientLanguage;
use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::rhocalc::RhoCalcLanguage;

/// Registry of available languages
pub struct LanguageRegistry {
    languages: HashMap<String, Box<dyn Language>>,
}

impl LanguageRegistry {
    /// Create a new registry
    pub fn new() -> Self {
        Self { languages: HashMap::new() }
    }

    /// Register a language
    pub fn register(&mut self, language: Box<dyn Language>) {
        let name = language.name().to_lowercase();
        self.languages.insert(name, language);
    }

    /// Get a language by name (case-insensitive)
    pub fn get(&self, name: &str) -> Result<&dyn Language> {
        self.languages
            .get(&name.to_lowercase())
            .map(|b| b.as_ref())
            .ok_or_else(|| anyhow::anyhow!("Language '{}' not found", name))
    }

    /// List all available languages
    pub fn list(&self) -> Vec<&str> {
        self.languages.values().map(|l| l.name()).collect()
    }

    /// Check if a language exists (case-insensitive)
    pub fn contains(&self, name: &str) -> bool {
        self.languages.contains_key(&name.to_lowercase())
    }
}

impl Default for LanguageRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Build the default registry with all available languages
pub fn build_registry() -> Result<LanguageRegistry> {
    let mut registry = LanguageRegistry::new();

    // Register auto-generated language implementations
    registry.register(Box::new(AmbientLanguage));
    registry.register(Box::new(LambdaLanguage));
    registry.register(Box::new(RhoCalcLanguage));

    if registry.languages.is_empty() {
        bail!("No languages available.");
    }

    Ok(registry)
}
