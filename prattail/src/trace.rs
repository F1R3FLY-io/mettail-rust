//! Compile-time diagnostic/trace gating for the PraTTaIL walker.
//!
//! Historically every parser diagnostic was written as
//!
//! ```
//! if std::env::var_os("PRATTAIL_CGLL_FENCE_DIAG").is_some() {
//!     eprintln!("CGLL-FENCE …");
//! }
//! ```
//!
//! which compiled the `eprintln!` **and the `std::env::var*` read** into every
//! build — a hot-path branch executed on each parse step even when no
//! diagnostic was ever requested. One such site (`PRATTAIL_CGLL_REALIZE_DIAG`)
//! flooded a proptest under `RUST_LOG=debug`.
//!
//! [`trace_diag!`] moves each diagnostic behind the `walker-trace` Cargo
//! feature (OFF BY DEFAULT). It wraps a statement block so the block — env read
//! included — is present ONLY under `--features walker-trace`; the default
//! build compiles it out entirely (no branch, no env check, zero cost). Under
//! the feature, each diagnostic is still selected at runtime by its own env
//! var, exactly as before.
//!
//! Usage — wrap the whole `if env { … }` statement so the env selector stays
//! *inside* the gate:
//!
//! ```
//! # use mettail_prattail::trace_diag;
//! trace_diag! {
//!     if std::env::var_os("PRATTAIL_CGLL_FENCE_DIAG").is_some() {
//!         eprintln!("CGLL-FENCE …");
//!     }
//! }
//! ```
//!
//! For a diagnostic *value* that must remain a live binding in every build
//! (e.g. a `bool` that also feeds real control flow), do not use this macro —
//! read the env under `#[cfg(feature = "walker-trace")]` and supply an
//! off-value under `#[cfg(not(feature = "walker-trace"))]` instead, so the
//! binding still exists (as its zero/`false` default) when the feature is off.

/// Expand `$body` **only** under `--features walker-trace`; expand to nothing
/// otherwise.
///
/// The body is emitted as a `#[cfg(feature = "walker-trace")]` block statement,
/// so on the default build the tokens (including any `std::env::var*` call)
/// are removed before type-checking — the diagnostic and its env selector cost
/// exactly nothing. See the module docs for the value-carrier exception.
#[macro_export]
macro_rules! trace_diag {
    ($($body:tt)*) => {
        #[cfg(feature = "walker-trace")]
        {
            $($body)*
        }
    };
}
