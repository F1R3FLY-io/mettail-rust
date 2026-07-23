//! L9-1 gate — a minimal 2-mode modal grammar.
//!
//! This is a TEST fixture (never a production spec: it lives in `languages/tests/`,
//! NOT `languages/src/`). It exists to prove that `generate_modal_lexer_string`
//! now emits the full DAG/WFST lexer interface — `lex_dag`, `lex_weighted`,
//! `token_to_kind`, and `token_text` — that the generated WPDA parser calls.
//! Before L9-1 a modal grammar produced ~22 unresolved-name compile errors here;
//! after L9-1 the file compiles (the "22-error set" → 0).
//!
//! The grammar declares a backtick guest mode (`ident\`…\`` opener pushes
//! `guest_backtick`; a bare backtick pops; everything else is a GuestChunk). The
//! guest tokens are not yet consumed by any production (that is L9-3's
//! `SyntaxExpr::TokenKind` + L9-4's `GuestBody`); here they only need to be
//! LEXABLE so the modal codegen path is exercised end-to-end. The ordinary
//! `Num` arithmetic parses through the modal lexer's DEFAULT mode.

#![allow(unused_imports, dead_code)]

use mettail_macros::language;
use mettail_runtime::Language;

language! {
    name: L9ModalToy,

    // This grammar is defined in a TEST target, not the `mettail_languages`
    // library, so suppress the macro's side-effect file emission (the auto-
    // generated gen_*.rs / simulate / Blockly files assume a library module and
    // would otherwise break the full suite).
    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        ![i32] as Num
    },

    tokens {
        // Backtick opener: any lowercase identifier immediately followed by a
        // backtick. Longer than the colliding bare Ident, so maximal munch
        // picks the opener (the Delimiter Unambiguity Invariant, checked by the
        // L9-2 lint). Backticks are written via string-form patterns because a
        // raw backtick is not a valid Rust token inside the macro input.
        FltOpenBacktick = "[a-z]+`" push(guest_backtick) ;

        mode guest_backtick {
            FltCloseBacktick = "`" pop ;
            GuestChunk = "[^`]+" ;
        }
    },

    terms {
        AddNum . a:Num, b:Num |- a "+" b : Num ![a + b] step;
    },
}

#[test]
fn l9_modal_toy_lexer_interface_resolves() {
    // Compiling this file at all proves the modal lexer emitted lex_dag,
    // lex_weighted, token_to_kind, and token_text — the WPDA parser generated
    // for `Num` references all four (the L9 "22-error set" → 0).
    let lang = L9ModalToyLanguage;
    assert_eq!(lang.name(), "L9ModalToy");
}

#[test]
fn l9_modal_toy_default_mode_parses() {
    // An ordinary (opener-free) expression lexes/parses end-to-end through the
    // modal default mode: compute_mode_map yields all-mode-0, and lex_dag /
    // token_to_kind / token_text run over the mode-0 DAG.
    mettail_runtime::clear_var_cache();
    let term = Num::parse("1 + 2").expect("default-mode parse should succeed");
    let displayed = format!("{}", term);
    assert!(!displayed.is_empty(), "Display should be non-empty for AddNum(1, 2)");
}
