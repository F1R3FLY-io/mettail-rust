//! Durable dual-mode test matrix — PARTS A, C, D of the keyword-reservation
//! (PIECE 3) anti-regression suite. Part B (opt-out) lives in
//! `gen_fortran_model_prop.rs`.
//!
//! Modes under test (identical send grammar, opposite `reserved_keywords`):
//!   • `ReservedModel`  (`auto`) — keyword `IF` reserved → `@IF!(x)` has ONE
//!     reading (`SendKw`); the variable-channel reading is removed.
//!   • `FortranModel`   (`none`) — `IF` unreserved → `@IF!(x)` has TWO readings
//!     (`SendVar(TVar("IF"))` + `SendKw`).
//!
//! Together they prove: (A) reservation collapses the keyword over-generation,
//! (C) the alternative set is deterministic/stable in both modes, and (D) the
//! per-language toggle flips exactly one reading. The reserved set is shown to
//! be grammar-derived (identifier-shaped terminals only), and RhoCalc — held
//! at `none` after the S0-kw-no-break measurement (see `rhocalc.rs`) — is
//! confirmed unregressed.

#![allow(clippy::bool_assert_comparison)]

// ─────────────────────────────────────────────────────────────────────────────
// PART A — WITH reservation (`ReservedModel`, `auto`)
// ─────────────────────────────────────────────────────────────────────────────

// Task #11 (extended 2026-07-26): the keyword-reservation FIXTURE twins are test-hosted
// (`languages/tests/definitions/`), so they are `#[path]`-included here rather than named
// through `mettail_languages::<lang>`, and the `#[cfg(feature = …)]` gates that used to
// guard each part are removed WITH the features: an unsatisfiable gate deletes the test
// silently, which is precisely the failure mode this relocation must not introduce.
//
// Neither definition emits a generated suite (`options { emit_tests: false }` — Part B is
// the HAND-WRITTEN `gen_fortran_model_prop.rs`), so no `_generated_tests!` wrapper exists
// and no designated host is needed for either.
#[path = "definitions/reserved_model.rs"]
mod reserved_model;
#[path = "definitions/fortran_model.rs"]
mod fortran_model;

mod with_reserve {
    use crate::reserved_model::*;

    fn send_readings() -> Vec<Stmt> {
        Stmt::parse_via_wpda_all("@IF!(x)")
            .expect("ReservedModel: `@IF!(x)` should parse as Stmt")
    }

    /// A.1 — keyword_channel_single: a reserved keyword in channel position
    /// yields EXACTLY one reading — the literal keyword send `SendKw`.
    #[test]
    fn keyword_channel_single_reading() {
        let readings = send_readings();
        assert_eq!(
            readings.len(),
            1,
            "reserved `@IF!(x)` must have exactly ONE reading; got {readings:?}"
        );
        assert!(
            matches!(readings[0], Stmt::SendKw(_)),
            "the single reading must be the literal keyword send `SendKw`; got {readings:?}"
        );
    }

    /// A.2 — reserved_terminal_not_free_var: the reserved terminal `IF` does
    /// NOT appear as a free variable in channel position (the `SendVar` reading
    /// with `TVar("IF")` is removed by reservation).
    #[test]
    fn reserved_terminal_not_a_free_var_channel() {
        let readings = send_readings();
        let has_var_if = readings.iter().any(|s| match s {
            Stmt::SendVar(chan, _) => matches!(chan.as_ref(), Term::TVar(_)),
            _ => false,
        });
        assert!(
            !has_var_if,
            "reservation must remove the `SendVar(TVar(\"IF\"), …)` reading; got {readings:?}"
        );
    }

    /// A.3 — keyword_in_channel_position: a plain (non-keyword) identifier IS
    /// still usable as a variable channel, so reservation is surgical — it
    /// removes only the keyword's spurious variable reading, not variables in
    /// general.
    #[test]
    fn plain_identifier_still_a_variable_channel() {
        let readings = Stmt::parse_via_wpda_all("@y!(x)")
            .expect("ReservedModel: `@y!(x)` should parse");
        assert!(
            readings.iter().any(|s| matches!(
                s,
                Stmt::SendVar(chan, _) if matches!(chan.as_ref(), Term::TVar(_))
            )),
            "a non-keyword channel `y` must still parse as a variable; got {readings:?}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// PART C — alternative-set determinism (no-functionality-lost guard), both modes
// ─────────────────────────────────────────────────────────────────────────────

/// C.1 — the materialized alternative set is deterministic across repeated
/// parses in the RESERVED mode (one reading, stable).

#[test]
fn alt_set_deterministic_reserved() {
    use crate::reserved_model as rm;
    let a = rm::Stmt::parse_via_wpda_all("@IF!(x)").expect("parse a").len();
    let b = rm::Stmt::parse_via_wpda_all("@IF!(x)").expect("parse b").len();
    assert_eq!(a, b, "reserved alt-set size must be deterministic");
    assert_eq!(a, 1, "reserved alt-set is exactly the single keyword reading");
}

/// C.2 — the materialized alternative set is deterministic across repeated
/// parses in the UNRESERVED mode (two readings, stable — full ambiguity kept).

#[test]
fn alt_set_deterministic_fortran() {
    use crate::fortran_model as f;
    let a = f::Stmt::parse_via_wpda_all("@IF!(x)").expect("parse a").len();
    let b = f::Stmt::parse_via_wpda_all("@IF!(x)").expect("parse b").len();
    assert_eq!(a, b, "unreserved alt-set size must be deterministic");
    assert_eq!(a, 2, "unreserved alt-set retains the full ambiguity (2 readings)");
}

// ─────────────────────────────────────────────────────────────────────────────
// PART D — mode-switch toggle (same grammar + terminal, opposite policy)
// ─────────────────────────────────────────────────────────────────────────────

/// D.1 — mode_switch_toggles_readings: the SAME send structure and the SAME
/// keyword `IF`, parsed by the `auto` language vs the `none` language, yields
/// 1 vs 2 readings — proving the `reserved_keywords` toggle flips exactly the
/// keyword's spurious variable reading and neither mode is silently broken.
#[cfg(all(feature = "reserved_model", feature = "fortran_model"))]
#[test]
fn mode_switch_toggles_readings() {
    use crate::fortran_model as none_lang;
    use crate::reserved_model as auto_lang;

    let reserved = auto_lang::Stmt::parse_via_wpda_all("@IF!(x)")
        .expect("auto: `@IF!(x)` parses")
        .len();
    let unreserved = none_lang::Stmt::parse_via_wpda_all("@IF!(x)")
        .expect("none: `@IF!(x)` parses")
        .len();

    assert_eq!(reserved, 1, "reserve ON → 1 reading");
    assert_eq!(unreserved, 2, "reserve OFF → 2 readings");
    assert!(
        unreserved > reserved,
        "reservation must be a strict refinement (OFF has strictly more readings)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Reserved set is GRAMMAR-DERIVED (identifier-shaped terminals only)
// ─────────────────────────────────────────────────────────────────────────────

/// The reserved set under `auto` is exactly the identifier-shaped literal
/// terminals — operators/punctuation are never reserved, and `none` reserves
/// nothing. Asserted directly against the prattail policy (no per-language
/// hardcode).
#[test]
fn reserved_set_is_grammar_derived() {
    use mettail_prattail::automata::{TerminalPattern, TokenKind};
    use mettail_prattail::ReservationPolicy;

    let terminals = vec![
        TerminalPattern { text: "IF".into(), kind: TokenKind::Fixed("IF".into()), is_keyword: true },
        TerminalPattern { text: "Nil".into(), kind: TokenKind::Fixed("Nil".into()), is_keyword: true },
        TerminalPattern { text: "true".into(), kind: TokenKind::True, is_keyword: true },
        // operators / punctuation are NOT identifier-shaped → never reserved
        TerminalPattern { text: "@".into(), kind: TokenKind::Fixed("@".into()), is_keyword: false },
        TerminalPattern { text: "!".into(), kind: TokenKind::Fixed("!".into()), is_keyword: false },
        TerminalPattern { text: "(".into(), kind: TokenKind::Fixed("(".into()), is_keyword: false },
    ];

    // `auto` reserves exactly the identifier-shaped (is_keyword) terminals.
    let auto = ReservationPolicy::auto().reserved_kinds(&terminals);
    assert!(auto.contains(&TokenKind::Fixed("IF".into())));
    assert!(auto.contains(&TokenKind::Fixed("Nil".into())));
    assert!(auto.contains(&TokenKind::True));
    assert!(!auto.contains(&TokenKind::Fixed("@".into())), "operators are not reserved");
    assert!(!auto.contains(&TokenKind::Fixed("!".into())), "operators are not reserved");
    assert!(!auto.contains(&TokenKind::Fixed("(".into())), "delimiters are not reserved");
    assert_eq!(auto.len(), 3, "exactly the three identifier-shaped keyword terminals");

    // `none` reserves nothing (full ambiguity retained).
    let none = ReservationPolicy::none().reserved_kinds(&terminals);
    assert!(none.is_empty(), "`none` must reserve nothing");

    // A per-terminal `contextual` opt-out removes exactly that terminal.
    let mut contextual = std::collections::HashSet::new();
    contextual.insert("Nil".to_string());
    let policy = ReservationPolicy {
        mode: mettail_prattail::ReservationMode::Auto,
        contextual,
    };
    let reserved = policy.reserved_kinds(&terminals);
    assert!(!reserved.contains(&TokenKind::Fixed("Nil".into())), "contextual opt-out drops Nil");
    assert!(reserved.contains(&TokenKind::Fixed("IF".into())), "others still reserved");
}

// ─────────────────────────────────────────────────────────────────────────────
// RhoCalc is unregressed at the shipped `reserved_keywords: auto`
// ─────────────────────────────────────────────────────────────────────────────

/// RhoCalc ships at `auto` (2026-07-06 flip): `Nil` is reserved, so the
/// over-generated `@Nil!(q)`-as-send-on-a-channel-variable-named-`Nil`
/// (`POutputQuoted(NVar(Free("Nil")), q)`) reading is removed — the scalar
/// `@Nil!(q)` cohort collapses 2→1 — while nullary `Nil` in prefix/operand
/// position still parses (the `NULLARY_KEYWORD_LEXFORK_SEED` lex-Fork seed
/// restores it under reservation). Guards against a regression of either the
/// flip (over-generation returns) or the lex-Fork seed (nullary `Nil` breaks).
#[cfg(feature = "rhocalc")]
#[test]
fn rhocalc_auto_reserved_unregressed() {
    use mettail_languages::rhocalc as r;

    // Nullary `Nil` in prefix/operand position still parses under reservation
    // (this is exactly what the pre-`NULLARY_KEYWORD_LEXFORK_SEED` flip broke).
    assert!(r::Proc::parse("*x | Nil").is_ok(), "`*x | Nil` must parse at `auto`");
    assert!(r::Proc::parse("@Nil!(Nil)").is_ok(), "`@Nil!(Nil)` must parse at `auto`");

    // Under `auto`, `Nil` is reserved: `@Nil!(q)` keeps ONLY the null-process
    // channel reading (the spurious send-on-variable-`Nil` reading is gone), so
    // the scalar cohort is a single reading (2→1 over-generation collapse).
    let readings = r::Proc::parse_via_wpda_all("@Nil!(q)")
        .expect("`@Nil!(q)` should parse at `auto`");
    assert_eq!(
        readings.len(),
        1,
        "at `auto`, `@Nil!(q)` collapses to 1 reading (Nil reserved); got {readings:?}"
    );
}
