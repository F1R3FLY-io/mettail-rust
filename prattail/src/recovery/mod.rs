//! Weighted error recovery via WFST-based minimum-cost repair.
//!
//! Replaces panic-mode "skip to first sync point" with a recovery WFST
//! that assigns costs to repair actions and uses Viterbi to find the
//! minimum-cost repair sequence.
//!
//! ## Repair Actions
//!
//! | Action | Cost | Description |
//! |--------|------|-------------|
//! | **Skip** | 0.5/token | Skip an unexpected token in the input |
//! | **Delete** | 1.0 | Delete (ignore) one token |
//! | **Substitute** | 1.5 | Replace an unexpected token with an expected one |
//! | **Insert** | 2.0 | Insert a missing expected token |
//!
//! ## Architecture
//!
//! ```text
//!   Parse error at position P
//!           │
//!           ▼
//!   RecoveryWfst::find_best_recovery(tokens, pos, sync_tokens)
//!           │
//!           ├─ Build repair lattice from current position
//!           │   - Skip edges (0.5/token each)
//!           │   - Delete edges (1.0)
//!           │   - Substitute edges (1.5, if sync token similar)
//!           │   - Insert edges (2.0, for each expected sync token)
//!           │
//!           ├─ Viterbi minimum-cost path
//!           │
//!           ▼
//!   RepairResult { action, skip_count, new_pos, cost }
//! ```
//!
//! ## Zero Overhead
//!
//! The recovery WFST is only invoked on parse error. The happy path (no errors)
//! has zero cost — no recovery structures are allocated or consulted.
//!
//! ## Derived from lling-llang
//!
//! The repair cost model draws from `lling-llang/src/applications/programming/`
//! `SyntaxRepairTransducer`. The Viterbi search is adapted from
//! `lling-llang/src/path/viterbi.rs`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::automata::semiring::{EditWeight, ProductWeight, Semiring, TropicalWeight};
use crate::token_id::{TokenId, TokenIdMap};

pub mod costs {
    use super::{EditWeight, ProductWeight, RecoveryCost, TropicalWeight};

    /// Cost per skipped token (0.5 tropical, 1 edit per token skipped).
    pub const SKIP_PER_TOKEN: TropicalWeight = TropicalWeight::new(0.5);

    /// Cost to delete one token (1.0).
    pub const DELETE: TropicalWeight = TropicalWeight::new(1.0);

    /// Cost to substitute one token for another (1.5).
    pub const SUBSTITUTE: TropicalWeight = TropicalWeight::new(1.5);

    /// Cost to insert a missing token (2.0).
    pub const INSERT: TropicalWeight = TropicalWeight::new(2.0);

    /// Maximum tokens to consider skipping before giving up (bounded lookahead).
    pub const MAX_SKIP_LOOKAHEAD: usize = 32;

    /// B2: Construct a joint RecoveryCost from tropical cost and edit count.
    #[inline]
    pub const fn joint(tropical: f64, edits: u32) -> RecoveryCost {
        ProductWeight::new(TropicalWeight::new(tropical), EditWeight::new(edits))
    }

    /// B2: Construct a joint RecoveryCost from a tropical cost and an EditWeight.
    #[inline]
    pub const fn joint_edit(tropical: f64, edit: EditWeight) -> RecoveryCost {
        ProductWeight::new(TropicalWeight::new(tropical), edit)
    }
}

mod config;
pub use config::*;
mod wfst;
pub use wfst::*;
mod viterbi;
pub use viterbi::*;
mod context;
pub use context::*;
pub(crate) use viterbi::{pick_better, pick_better_if_allowed};

#[cfg(test)]
mod tests;

#[cfg(test)]
mod proptest_tests;
