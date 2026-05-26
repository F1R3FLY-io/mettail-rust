//! Polyglot island processing (v1 Phase 3).

pub mod plugin;
pub mod plugins;
pub mod registry;
pub mod template;
pub mod token;

pub use plugin::{IslandArtifact, IslandPlugin, ProcGst};
pub use registry::PluginRegistry;
pub use template::{hole_count, split_template, IslandTemplate, TemplatePiece, TypedHole};
pub use token::{decode_island_body, DecodedBody};

use crate::error::Result;
use crate::surface::IslandToken;

/// Process an island token through the default plugin registry.
pub fn process_island(token: &IslandToken) -> Result<IslandArtifact> {
    PluginRegistry::with_defaults().process(token)
}
