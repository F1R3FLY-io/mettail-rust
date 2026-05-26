//! `Rust` island plugin: validates `${expr}` holes as Rust expressions.

use syn::parse_str;

use crate::error::{Result, SpecError};
use crate::island::plugin::{template_from_token, IslandArtifact, IslandPlugin};
use crate::island::template::TemplatePiece;
use crate::island::token::decode_island_body;
use crate::surface::IslandToken;

pub struct RustIslandPlugin;

impl IslandPlugin for RustIslandPlugin {
    fn lang_names(&self) -> &[&str] {
        &["Rust", "rust"]
    }

    fn process(&self, token: &IslandToken) -> Result<IslandArtifact> {
        let template = template_from_token(token);
        for piece in &template.pieces {
            if let TemplatePiece::Hole(hole) = piece {
                parse_str::<syn::Expr>(&hole.source).map_err(|e| SpecError::Island {
                    lang: token.lang.clone(),
                    message: format!("invalid Rust hole `${{{}}}`: {e}", hole.source),
                })?;
            }
        }
        let decoded = decode_island_body(&token.body)?;
        Ok(IslandArtifact::RustContext { snippet: decoded.text })
    }
}
