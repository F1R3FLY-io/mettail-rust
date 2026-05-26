//! Registry of island language plugins.

use std::sync::Arc;

use crate::error::{Result, SpecError};
use crate::island::plugin::{IslandArtifact, IslandPlugin};
use crate::island::plugins::{RholangProcPlugin, RustIslandPlugin};
use crate::surface::IslandToken;

pub struct PluginRegistry {
    plugins: Vec<Arc<dyn IslandPlugin>>,
}

impl PluginRegistry {
    pub fn with_defaults() -> Self {
        Self {
            plugins: vec![Arc::new(RustIslandPlugin), Arc::new(RholangProcPlugin)],
        }
    }

    pub fn process(&self, token: &IslandToken) -> Result<IslandArtifact> {
        for plugin in &self.plugins {
            if plugin.lang_names().iter().any(|n| n == &token.lang) {
                return plugin.process(token);
            }
        }
        Err(SpecError::Island {
            lang: token.lang.clone(),
            message: format!("no island plugin registered for language '{}'", token.lang),
        })
    }
}

impl Default for PluginRegistry {
    fn default() -> Self {
        Self::with_defaults()
    }
}
