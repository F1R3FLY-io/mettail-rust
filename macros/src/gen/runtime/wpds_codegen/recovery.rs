//! Walker-side recovery emission — placeholder for future Walker-state-driven
//! recovery codegen.
//!
//! **Stage 10.5r-d (2026-05-05) status: empty.**
//!
//! Per Plan agent `ac1ca5956a3783d6c` audit, the trampoline-era
//! `wfst_recover_<Cat>` codegen (in `pipeline.rs::generate_wfst_recovery_fn`)
//! was emitted but had zero callers. The actual recovery used at runtime is
//! the wrapper-level skip-to-sync loop in
//! `wpds_codegen/facade.rs::parse_<Cat>_via_wpds_recovering`.
//!
//! All trampoline-era thread-locals (FRAME_STATE_<CAT>, RUNNING_WEIGHT_<CAT>,
//! PARENT_WEIGHT_<CAT>, BRACKET_STATE_<cat>, LAST_ERROR_POS_<cat>) +
//! per-category helpers (frame_kind_of_<cat>, running_weight_<cat>) +
//! shared `frame_kind_of_wpds()` were eliminated together with the dead
//! `wfst_recover_<Cat>` emitter. They had no live consumers post-trampoline-
//! deletion (Stage 10.6).
//!
//! When/if a future iteration wants Walker-state-aware recovery (reading
//! frame depth/kind from `walker.gss().frontier()`, running weight from
//! `walker.weight().primary()`), the implementation belongs HERE — emitting
//! a `wpds_recover_<Cat>(walker, ...)` function that takes `&WpdsWalker`
//! and queries it directly. No thread-local synthesis, no shim layer.

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

/// Emit Walker-side recovery infrastructure. Currently a no-op — recovery
/// runs at the wrapper level in `facade.rs`. Reserved as the future home
/// for `wpds_recover_<Cat>` emission when Walker-state-aware recovery is
/// designed.
pub(crate) fn emit_recovery_module(_language: &LanguageDef, _categories: &[String]) -> TokenStream {
    quote! {}
}
