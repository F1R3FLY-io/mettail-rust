//! Opt-Group synthetic test grammar (2026-04-29).
//!
//! Exercises `*opt(...)` syntax in syntax patterns + term contexts — the
//! WPDS engine's `WpdaState::OptionalGroup` state, the new
//! `SymbolKind::OptionalGroupAt(u8)` marker, the
//! `WpdaStepAction::OptGroupAbsent` / `WpdaStepAction::OptGroupFinalize`
//! actions, the `SemanticBuilder.optional_stack`, and the
//! `ActionArg::Optional(Option<Vec<ActionArg>>)` runtime arg.
//!
//! Test inputs:
//!   - `if true then 1 else 2`  →  `1`
//!   - `if true then 1`         →  `1`
//!   - `if false then 1 else 2` →  `2`
//!   - `if false then 1`        →  `0`
//!
//! The IfElse rule has term context `cond:Bool, t:Int, *opt(e:Int)` and
//! syntax pattern `"if" cond "then" t *opt("else" e)`. Codegen emits
//! `Int::IfElse(Box<Bool>, Box<Int>, Option<Box<Int>>)` and the user
//! action body `if cond { t } else { e.unwrap_or(0) }`.

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: OptSmoke,

    options {
        // Task #11: this is a TEST language definition, not production, so it
        // lives in `languages/tests/definitions/` rather than in the library.
        // The key tells the macro to emit the generated suite inline (an opt-in
        // `optsmoke_generated_tests!` wrapper) and to give the simulation CLI a
        // `#[path]` prologue instead of a `mettail_languages::optsmoke` import.
        hosted_in: "tests/definitions/optsmoke.rs",
    },

    types {
        ![i32] as Int
        ![bool] as Bool
    },

    terms {
        /// Branches on a Boolean condition.
        ///
        /// When `cond` is true, evaluates `t`; otherwise evaluates `e`
        /// (or 0 if the else-branch is omitted via `*opt(...)`).
        IfElse . cond:Bool, t:Int, *opt(e:Int)
            |- "if" cond "then" t *opt("else" e) : Int
            ![{
                if cond {
                    t
                } else {
                    e.unwrap_or(0)
                }
            }] step;
    },

    equations {},

    rewrites {},
}
