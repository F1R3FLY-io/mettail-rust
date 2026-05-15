//! Phase 4 collection parity — hand-authored tests for RhoCalc's
//! `PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc` rule.
//!
//! Verifies the collection state machine end-to-end:
//! - Open delim `{` pushes CollectionMarker, walker auto-allocates
//!   accumulator id and pushes ActionArg::CollectionId.
//! - First element parses via PrefixDispatch (state_cat_src_idx = Proc).
//! - Element-Return Pop fires the element's action; auto-splice transfers
//!   the just-built term from builder.stack to collection_stack[id].
//! - Unwinding-CollectionMarker arm transitions to CollectionLoop.
//! - CollectionLoop dispatches: separator → Consume → re-enter PrefixDispatch;
//!   close → ConsumeAndPop fires finalize action.
//! - Finalize action drains accumulator, builds HashBag<Proc>, pushes Proc::PPar.
//! - Empty collection `{ }` (with explicit `{` and `}` tokens — not PZero's `"{}"`
//!   single-token form) hits the empty-collection bootstrap in PrefixDispatch.

use mettail_languages::rhocalc::{parse_Proc_via_wpda, Proc};
use mettail_prattail::automata::TokenKind;

/// Single-element collection: `{ error }` → `Proc::PPar({Proc::Err})`.
#[test]
fn wpds_parse_ppar_single_element() {
    let kinds = vec![
        TokenKind::Fixed("{".to_string()),
        TokenKind::Fixed("error".to_string()),
        TokenKind::Fixed("}".to_string()),
    ];
    let texts = vec!["{", "error", "}"];
    let mut pos = 0usize;
    let result = parse_Proc_via_wpda(&kinds, &texts, &mut pos, 0);
    match result {
        Ok(ref par @ Proc::PPar(ref bag)) => {
            assert_eq!(bag.len(), 1, "expected 1-element bag, got {}", bag.len());
            // Sanity check: the single element is Proc::Err.
            for (item, _count) in bag.iter() {
                assert!(matches!(item, Proc::Err), "expected Proc::Err, got {:?}", item);
            }
            let _ = par;
        }
        other => panic!("expected Proc::PPar(...), got {:?}", other),
    }
    assert_eq!(pos, 3, "consumed all 3 tokens");
}

/// Two-element collection: `{ error | error }` → `Proc::PPar({Proc::Err, Proc::Err})`.
#[test]
fn wpds_parse_ppar_two_elements() {
    let kinds = vec![
        TokenKind::Fixed("{".to_string()),
        TokenKind::Fixed("error".to_string()),
        TokenKind::Fixed("|".to_string()),
        TokenKind::Fixed("error".to_string()),
        TokenKind::Fixed("}".to_string()),
    ];
    let texts = vec!["{", "error", "|", "error", "}"];
    let mut pos = 0usize;
    let result = parse_Proc_via_wpda(&kinds, &texts, &mut pos, 0);
    match result {
        Ok(Proc::PPar(ref bag)) => {
            assert_eq!(bag.len(), 2, "expected 2-element bag, got {}", bag.len());
            for (item, _count) in bag.iter() {
                assert!(matches!(item, Proc::Err), "expected Proc::Err, got {:?}", item);
            }
        }
        other => panic!("expected Proc::PPar(...), got {:?}", other),
    }
    assert_eq!(pos, 5, "consumed all 5 tokens");
}

/// Three-element collection: `{ error | error | error }`.
#[test]
fn wpds_parse_ppar_three_elements() {
    let kinds = vec![
        TokenKind::Fixed("{".to_string()),
        TokenKind::Fixed("error".to_string()),
        TokenKind::Fixed("|".to_string()),
        TokenKind::Fixed("error".to_string()),
        TokenKind::Fixed("|".to_string()),
        TokenKind::Fixed("error".to_string()),
        TokenKind::Fixed("}".to_string()),
    ];
    let texts = vec!["{", "error", "|", "error", "|", "error", "}"];
    let mut pos = 0usize;
    let result = parse_Proc_via_wpda(&kinds, &texts, &mut pos, 0);
    match result {
        Ok(Proc::PPar(ref bag)) => {
            assert_eq!(bag.len(), 3, "expected 3-element bag, got {}", bag.len());
        }
        other => panic!("expected Proc::PPar(...), got {:?}", other),
    }
    assert_eq!(pos, 7);
}

/// Empty collection: `{ }` (explicit `{` and `}` tokens, not PZero's `"{}"` single-token form).
/// Tests the empty-collection bootstrap in PrefixDispatch.
#[test]
fn wpds_parse_ppar_empty() {
    let kinds = vec![
        TokenKind::Fixed("{".to_string()),
        TokenKind::Fixed("}".to_string()),
    ];
    let texts = vec!["{", "}"];
    let mut pos = 0usize;
    let result = parse_Proc_via_wpda(&kinds, &texts, &mut pos, 0);
    match result {
        Ok(Proc::PPar(ref bag)) => {
            assert_eq!(bag.len(), 0, "expected empty bag, got {}", bag.len());
        }
        other => panic!("expected Proc::PPar(empty), got {:?}", other),
    }
    assert_eq!(pos, 2);
}
