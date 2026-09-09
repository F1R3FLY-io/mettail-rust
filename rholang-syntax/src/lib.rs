//! The existing Rholang specification compiled without a node backend.
//!
//! The source path is shared with the language collection: there is no second
//! grammar or parser implementation here. A separate Cargo identity prevents
//! backend features selected elsewhere from entering this dependency closure.

#![allow(
    clippy::cloned_ref_to_slice_refs,
    clippy::type_complexity,
    unused_imports
)]

#[path = "../../languages/src/rholang.rs"]
pub mod rholang;
