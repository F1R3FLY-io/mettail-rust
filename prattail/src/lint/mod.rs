//! Unified compile-time lint and diagnostic layer for PraTTaIL grammars.
//!
//! Routes **all** diagnostic output through [`LintDiagnostic`] structs and
//! [`format_diagnostic_colored()`] for consistent, ANSI-colorized, Rust-compiler-style
//! output. No diagnostic bypasses this system.
//!
//! ## Lint Categories
//!
//! | Prefix | Category | Source Data |
//! |--------|----------|-------------|
//! | G | Grammar structure | ParserBundle (pre-WFST) + macros crate |
//! | W | WFST-specific | Prediction WFSTs |
//! | R | Recovery | Recovery WFSTs + RecoveryConfig |
//! | C | Cross-category | Cast rules + FIRST sets |
//! | X | Composition | Composed grammar verification |
//! | P | Performance | DFA stats + WFST metrics |
//! | I | Infrastructure | Pipeline progress, env overrides, I/O |
//!
//! ## Severity Levels
//!
//! | Level | Color | Description |
//! |-------|-------|-------------|
//! | `Info` | Bold cyan | Infrastructure progress — pipeline status |
//! | `Note` | Bold cyan | Informational — no action required |
//! | `Warning` | Bold yellow | Possible issue — review recommended |
//! | `Error` | Bold red | Correctness bug — compilation may fail |
//!
//! ## Diagnostics Emitted Outside `run_lints`
//!
//! Specialized pipeline stages emit the following diagnostics via
//! [`emit_diagnostic()`]:
//!
//! | ID | Severity | Name | Description |
//! |----|----------|------|-------------|
//! | I17 | info | cd06-shared-suffix-measure | Shared decision-tree suffix measurement |
//! | I18 | info | lint-cache-hit | DB04: lint results cached, skipping lint passes |
//! | I22 | error | analysis-thread-panicked | DB03: a scoped analysis thread panicked; carries the recovered payload |
//!
//! Historical identifiers G25–G31, G35, G38, G41–G42, W09, C-AP01–C-AP05,
//! and I10 belonged to the retired Ascent macro phase. They have no production
//! emitter in the Dovetail/Rho pipeline and must not be presented as current
//! diagnostics.
//!
//! ## Display Format
//!
//! Rust-compiler-style diagnostics to stderr with ANSI colors:
//!
//! ```text
//! error[C01]: cast cycle detected: Int -> Proc -> Int
//!   = hint: break the cycle by removing one cast direction
//!
//! warning[W01]: rule `FloatToStr` in category `Str` is unreachable (dead code)
//!   = hint: remove the rule or add a unique dispatch token
//!
//! info[I01] (Ambient): transducer cascade: 8 change(s) across 3 categories (12 total iterations)
//! ```

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::binding_power::BindingPowerTable;
use crate::decision_tree::CategoryDecisionTree;
use crate::grammar::ir::{CastRule, CrossCategoryRule, RDRuleInfo};
use crate::pipeline::CategoryInfo;
use crate::prediction::{FirstSet, FollowSetInput, RuleInfo};
use crate::recovery::{RecoveryConfig, RecoveryWfst};
use crate::token_id::TokenIdMap;
use crate::wfst::PredictionWfst;
use crate::SourceLocation;
use crate::SyntaxItemSpec;

pub mod ansi {
    pub const RESET: &str = "\x1b[0m";
    pub const BOLD: &str = "\x1b[1m";
    pub const DIM: &str = "\x1b[2m";
    pub const RED: &str = "\x1b[31m";
    pub const GREEN: &str = "\x1b[32m";
    pub const YELLOW: &str = "\x1b[33m";
    pub const BLUE: &str = "\x1b[34m";
    pub const CYAN: &str = "\x1b[36m";
    pub const BOLD_RED: &str = "\x1b[1;31m";
    pub const BOLD_YELLOW: &str = "\x1b[1;33m";
    pub const BOLD_CYAN: &str = "\x1b[1;36m";
    pub const BOLD_BLUE: &str = "\x1b[1;34m";
}

mod diagnostic;
pub use diagnostic::*;
mod lints;
pub use lints::*;
mod context;
pub use context::*;
mod grouping;
pub use grouping::*;

#[cfg(test)]
mod tests;
