//! Host binary for the test-hosted `OptSmoke` language definition.
//!
//! Task #11: `OptSmoke` is a test grammar (it exercises `*opt(...)` in syntax
//! patterns and term contexts), so its definition lives in
//! `languages/tests/definitions/optsmoke.rs`, not in the `languages` library.
//!
//! This file is its DESIGNATED HOST: it declares the definition module and is the
//! one and only invoker of the opt-in `optsmoke_generated_tests!` wrapper, which
//! materializes the macro-generated unit / prop / rewrite / analytical sections
//! that used to be written to `languages/tests/gen_optsmoke_*.rs`. Other consumers
//! (`optional_group_smoke.rs`, `doc_comment_metadata.rs`, `src/bin/simulate_optsmoke.rs`)
//! include the same definition WITHOUT invoking the wrapper, so the generated
//! tests exist exactly once across the whole suite.

#[path = "definitions/optsmoke.rs"]
mod optsmoke;

optsmoke::optsmoke_generated_tests!(crate::optsmoke);
