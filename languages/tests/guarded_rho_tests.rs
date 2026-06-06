//! Hand-written integration tests for the GuardedRho language.
//!
//! These tests exercise the source-level predicated-types pipeline:
//! 1. Token stream → trampoline parser → standalone parse fn dispatch
//!    via `should_use_standalone_fn` (Phase 3A-T1).
//! 2. Standalone fn (`recursive.rs::write_recursive_descent_body`) hits
//!    `RDSyntaxItem::GuardExpression` and parses a `BehavioralPred`
//!    (Phase 2G).
//! 3. The parsed `BehavioralPred` becomes the runtime field on the
//!    generated `Proc::PGuardedInput` enum variant (Phase 2D).
//!
//! The auto-generated test file `gen_guardedrho.rs` skips a unit test for
//! PGuardedInput because the constructor "is too complex to construct
//! statically" — these hand-written tests fill that gap by parsing
//! source strings rather than constructing the term directly.

use mettail_languages::guardedrho::*;
use mettail_runtime::{BehavioralPred, Language, PredArg};

// ────────────────────────────────────────────────────────────────────────────
// Test helpers
// ────────────────────────────────────────────────────────────────────────────

fn parse(input: &str) -> Proc {
    Proc::parse(input).unwrap_or_else(|e| panic!("parse failed for `{}`: {}", input, e))
}

fn fresh() {
    mettail_runtime::clear_var_cache();
}

// ────────────────────────────────────────────────────────────────────────────
// Parser tests — verify the standalone fn path for guarded receive
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn guarded_input_with_relation_args_parses() {
    fresh();
    // `halts(x)` — relation call with one argument
    let term = parse("for(x <- @1 where halts(x)){ Nil }");
    assert!(
        matches!(term, Proc::PGuardedInput(..)),
        "expected PGuardedInput, got {:?}",
        term
    );
}

#[test]
fn guarded_input_with_nullary_relation_parses() {
    fresh();
    // `safe` — nullary relation (no parens after the name)
    let term = parse("for(x <- @1 where safe){ Nil }");
    assert!(
        matches!(term, Proc::PGuardedInput(..)),
        "expected PGuardedInput, got {:?}",
        term
    );
}

#[test]
fn guarded_input_with_two_arg_relation_parses() {
    fresh();
    // `eq(x, y)` — relation call with two arguments, comma-separated
    let term = parse("for(x <- @1 where eq(x, y)){ Nil }");
    assert!(
        matches!(term, Proc::PGuardedInput(..)),
        "expected PGuardedInput, got {:?}",
        term
    );
}

#[test]
fn guarded_input_predicate_field_is_relation_query() {
    fresh();
    let term = parse("for(x <- @1 where halts(x)){ Nil }");
    let Proc::PGuardedInput(_, pred, _) = &term else {
        panic!("expected PGuardedInput, got {:?}", term);
    };
    match pred {
        BehavioralPred::RelationQuery { relation_name, args, negated } => {
            assert_eq!(relation_name, "halts");
            assert_eq!(args.len(), 1);
            assert!(
                matches!(&args[0], PredArg::Var(v) if v == "x"),
                "expected PredArg::Var(\"x\"), got {:?}",
                args[0]
            );
            assert!(!*negated, "expected non-negated predicate");
        },
        other => panic!("expected RelationQuery, got {:?}", other),
    }
}

#[test]
fn guarded_input_nullary_predicate_has_zero_args() {
    fresh();
    let term = parse("for(x <- @1 where safe){ Nil }");
    let Proc::PGuardedInput(_, pred, _) = &term else {
        panic!("expected PGuardedInput, got {:?}", term);
    };
    match pred {
        BehavioralPred::RelationQuery { relation_name, args, negated } => {
            assert_eq!(relation_name, "safe");
            assert!(args.is_empty(), "expected zero args, got {:?}", args);
            assert!(!*negated);
        },
        other => panic!("expected RelationQuery, got {:?}", other),
    }
}

#[test]
fn guarded_input_two_arg_predicate_preserves_order() {
    fresh();
    let term = parse("for(x <- @1 where eq(x, y)){ Nil }");
    let Proc::PGuardedInput(_, pred, _) = &term else {
        panic!("expected PGuardedInput, got {:?}", term);
    };
    match pred {
        BehavioralPred::RelationQuery { relation_name, args, .. } => {
            assert_eq!(relation_name, "eq");
            assert_eq!(args.len(), 2);
            assert!(matches!(&args[0], PredArg::Var(v) if v == "x"));
            assert!(matches!(&args[1], PredArg::Var(v) if v == "y"));
        },
        other => panic!("expected RelationQuery, got {:?}", other),
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Channel + body extraction
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn guarded_input_channel_field_is_quoted_int() {
    fresh();
    let term = parse("for(x <- @1 where halts(x)){ Nil }");
    let Proc::PGuardedInput(channel, _, _) = &term else {
        panic!("expected PGuardedInput, got {:?}", term);
    };
    // Channel is `@1` — NQuote wrapping an integer literal
    assert!(
        matches!(channel.as_ref(), Name::NQuote(_)),
        "expected NQuote, got {:?}",
        channel
    );
}

#[test]
fn guarded_input_body_is_nil() {
    fresh();
    let term = parse("for(x <- @1 where halts(x)){ Nil }");
    let Proc::PGuardedInput(_, _, scope) = &term else {
        panic!("expected PGuardedInput, got {:?}", term);
    };
    let scope_repr = format!("{:?}", scope);
    assert!(
        scope_repr.contains("PNil"),
        "expected scope body to contain PNil, got {}",
        scope_repr
    );
}

// ────────────────────────────────────────────────────────────────────────────
// Composition with non-guarded constructors (Phase 16F-0 parser fix)
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn guarded_input_in_parallel_composition_parses() {
    fresh();
    // No braces — PPar uses delimiter-free HashBag sep-list.
    let term = parse("{ for(x <- @1 where halts(x)){ Nil } | @1!(Nil) }");
    match &term {
        Proc::PPar(bag) => {
            assert!(
                bag.len() >= 2,
                "expected PPar bag with at least 2 elements, got {}",
                bag.len()
            );
        },
        other => panic!("expected PPar, got {:?}", other),
    }
}

#[test]
fn poutput_standalone_parses_at_prefix() {
    fresh();
    // NT-first dispatch arm lets @1!(Nil) start a Proc parse.
    let term = parse("@1!(Nil)");
    match &term {
        Proc::POutput(_, _) => {},
        other => panic!("expected POutput, got {:?}", other),
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Language-trait surface — verify GuardedRhoLanguage.parse_term works
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn language_parse_term_accepts_guarded_source() {
    fresh();
    let lang = GuardedRhoLanguage;
    let result = lang.parse_term("for(x <- @1 where halts(x)){ Nil }");
    assert!(result.is_ok(), "Language::parse_term failed: {:?}", result.err());
}

#[test]
fn language_parse_term_accepts_nullary_guard() {
    fresh();
    let lang = GuardedRhoLanguage;
    let result = lang.parse_term("for(x <- @1 where safe){ Nil }");
    assert!(
        result.is_ok(),
        "Language::parse_term failed for nullary guard: {:?}",
        result.err()
    );
}

// ────────────────────────────────────────────────────────────────────────────
// Determinism — same input twice should produce equal terms
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn guarded_input_parse_is_deterministic() {
    // Verify that parsing the same source twice yields structurally equivalent
    // results. We compare by predicate field equality + variant shape rather
    // than full PartialEq, because PartialEq on the whole Proc tree currently
    // recurses through the Scope/Binder layers in a way that triggers a
    // Debug-print stack overflow if the terms diverge.
    let src = "for(x <- @1 where halts(x)){ Nil }";
    fresh();
    let a = parse(src);
    fresh();
    let b = parse(src);

    let (Proc::PGuardedInput(_, pred_a, _), Proc::PGuardedInput(_, pred_b, _)) = (&a, &b) else {
        panic!("expected both parses to be PGuardedInput");
    };

    // BehavioralPred is a free-standing leaf type with no var IDs, so its
    // PartialEq is safe to compare across two `fresh()`-separated parses.
    assert_eq!(pred_a, pred_b, "parses of the same source should produce equal predicates");
}
