//! Runtime-neutral semantic grammar representation for MeTTaIL.
//!
//! Front ends lower into [`GrammarCoreV1`]. Compiler back ends consume only
//! that representation and may emit a verified [`ParserImageV1`]. The image is
//! a cache: the grammar value, not an image supplied beside it, is authoritative.

mod core;
mod dynamic;
mod image;
mod weight;

pub use core::*;
pub use dynamic::*;
pub use image::*;
pub use weight::*;
