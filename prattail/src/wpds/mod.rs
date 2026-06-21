//! Weighted Pushdown System (WPDS) and Simple Reset WPDA.
//!
//! Provides compile-time pushdown analysis for PraTTaIL grammars that goes beyond
//! the finite-state `PredictionWfst`. The WPDS encodes the full inter-category
//! call/return structure, enabling:
//!
//! - **Stack-aware dead-rule detection** (rules unreachable in valid stack contexts)
//! - **Exact ambiguity quantification** via stringsum over `CountingWeight`
//! - **Witness traces** explaining why a rule is dead (which calling contexts are missing)
//!
//! ## Theoretical Foundations
//!
//! Three complementary formalisms:
//!
//! 1. **Reps, Lal & Kidd (2007)** — WPDS poststar/prestar saturation for grammar-wide
//!    reachability with call/return matching. Weight domains as abstract transformers.
//! 2. **Droste, Dziadek & Kuich (2019)** — Simple reset WPDA normal form. Three stack
//!    ops (push/pop/noop), no ε-transitions, canonical `X = M₀X + Σ M₁X M₂X + E`.
//! 3. **Butoi et al. (2022)** — Direct WPDA stringsum algorithms avoiding CFG conversion.
//!    O(n³|Q|³|Γ|³) per input.
//!
//! ## Architecture
//!
//! ```text
//! LanguageSpec ──→ build_wpds() ──→ Wpds<W>
//!                                      │
//!                 ┌────────────────────┤
//!                 │                    │
//!                 ▼                    ▼
//!          poststar(BooleanWeight)   stringsum(CountingWeight)
//!          → stack-aware reachability → exact ambiguity counts
//!                 │                    │
//!                 ▼                    ▼
//!          lint.rs (Tier 5)       cost_benefit.rs (A5 refinement)
//! ```
//!
//! ## PraTTaIL Mapping
//!
//! | PDA Component | PraTTaIL Equivalent |
//! |---|---|
//! | Control locations P | `{p}` (single, "context-free process") |
//! | Stack alphabet Γ | `(category, rule_label, position)` triples |
//! | PDS rules Δ | Intraprocedural (replace), cross-category calls (push), returns (pop) |
//! | Weight function f | Semiring weight from `PredictionWfst` |

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use crate::automata::semiring::{BooleanWeight, Semiring, TropicalWeight};
use crate::wfst::PredictionWfst;
use crate::{LanguageSpec, SyntaxItemSpec};

mod types;
pub use types::*;
mod build;
pub use build::*;
mod saturation;
pub use saturation::*;
mod callgraph;
pub use callgraph::*;
mod analysis;
pub use analysis::*;

#[cfg(test)]
mod tests;
