//! Stage 3.27a (2026-05-04) — integration test for doc-comment description
//! extraction.
//!
//! Verifies that `///` doc-comments preceding a grammar rule (in this case
//! `optsmoke::IfElse`) flow end-to-end through:
//!   parse (`ast/src/grammar.rs::parse_doc_comment`)
//!     → AST (`GrammarRule::doc_comment`)
//!     → metadata codegen (`macros/src/gen/runtime/metadata.rs`)
//!     → runtime `TermDef::description: Option<&'static str>`
//!
//! Pre-3.27a: the description was unconditionally `None`. Post-3.27a: when
//! `///` lines precede the rule in the `language! { ... }` macro DSL input,
//! the joined text (with one canonical leading space stripped per line)
//! surfaces as `Some(...)` here.
//!
//! This is the round-trip test referenced in the Stage 3.27a Plan agent
//! design (Substage E).

#![allow(unused_imports, dead_code)]

// Task #11: OptSmoke is test-hosted (see tests/definitions/optsmoke.rs).
#[path = "definitions/optsmoke.rs"]
mod optsmoke;
use optsmoke::*;
use mettail_runtime::{Language, LanguageMetadata};

#[test]
fn optsmoke_ifelse_description_round_trips() {
    let lang = OptSmokeLanguage;
    let meta = lang.metadata();
    let ifelse = meta
        .terms()
        .iter()
        .find(|t| t.name == "IfElse")
        .expect("IfElse term must be present in OptSmoke metadata");

    let desc = ifelse
        .description
        .expect("IfElse has a `///` doc comment, so description must be Some");

    // The doc comment in `languages/src/optsmoke.rs` is multi-line; the
    // first line should be present verbatim, and a blank line should be
    // preserved between the summary and the elaboration.
    assert!(
        desc.contains("Branches on a Boolean condition"),
        "description should contain the summary line; got: {:?}",
        desc,
    );
    assert!(
        desc.contains("evaluates `t`"),
        "description should preserve elaboration text; got: {:?}",
        desc,
    );
    // Multi-line joining: blank line between summary and elaboration.
    assert!(
        desc.contains("\n\n"),
        "multi-line doc comment must preserve blank lines via \\n\\n; got: {:?}",
        desc,
    );
}

#[test]
fn optsmoke_metadata_terms_nonempty() {
    let lang = OptSmokeLanguage;
    let meta = lang.metadata();
    assert!(
        !meta.terms().is_empty(),
        "OptSmoke metadata should expose at least the IfElse term",
    );
}
