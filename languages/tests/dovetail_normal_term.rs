//! Regression tests for `RhoCalcLanguage::dovetail_normal_term` — the typed
//! Dovetail normal-form reconstruction (macro extension E2). These exercise the
//! e-graph→AST reconstruction arms added for `Collection`/`Binder`/`MultiBinder`
//! variants (the inverse of the typed lowering), covering the four ground-truth
//! cases from the E2 spec:
//!   1. `@("OUT")!(int(1+2,8))`        → Ok, formats `@("OUT")!(3)` (Regular reconstruction)
//!   2. `{ @("OUT")!(int(1+2,8)) }`    → Ok                          (PPar HashBag/Collection arm)
//!   3. `{ int(1,8) | int(1,8) }`      → Ok, 2-element bag           (multiplicity preserved)
//!   4. `new x in {x!(int(1+2,8))}`     → Ok, ≡α `new x in {x!(3)}`    (PNew MultiBinder arm)
//!
//! See `docs/design/dovetail-rho-macro-extensions/00-design-and-ledger.md` (E2).

use mettail_languages::rhocalc::RhoCalcLanguage;
use mettail_runtime::Language;

const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 1_000_000;

/// Parse `src`, run `dovetail_normal_term`, and return the formatted normal form (or panic).
fn normal_form(src: &str) -> String {
    let lang = RhoCalcLanguage;
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    let nf = RhoCalcLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("dovetail_normal_term({src:?}) returned Err: {e}"));
    lang.format_term(nf.as_ref())
}

#[test]
fn reconstructs_fold_inside_output() {
    // (1) Regular (POutput) reconstruction wrapping a folded `int(1+2,8)` → `3`.
    let got = normal_form("@(\"OUT\")!(int(1+2,8))");
    assert_eq!(got, "@(\"OUT\")!(3)", "fold must reduce inside the surrounding POutput");
}

#[test]
fn reconstructs_ppar_collection() {
    // (2) The PPar HashBag/Collection arm must reconstruct (the surrounding par is what matters).
    let src = "{ @(\"OUT\")!(int(1+2,8)) }";
    let lang = RhoCalcLanguage;
    let term = lang.parse_term(src).expect("parse PPar");
    let nf = RhoCalcLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES);
    assert!(nf.is_ok(), "PPar Collection reconstruction must be Ok: {:?}", nf.err());
}

#[test]
fn collection_multiplicity_is_preserved() {
    // (3) `{ int(1,8) | int(1,8) }` → a 2-element bag (multiplicity 2 must survive).
    // `int(1,8)` folds to the literal `1`; the AC bag therefore holds two copies of `1`.
    let src = "{ int(1,8) | int(1,8) }";
    let got = normal_form(src);
    let inner = got.trim();
    // Strip the outer `{` `}` if present, then split on the PPar separator `|`.
    let body = inner
        .strip_prefix('{')
        .and_then(|s| s.strip_suffix('}'))
        .unwrap_or(inner);
    let members: Vec<&str> = body
        .split('|')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect();
    assert_eq!(
        members.len(),
        2,
        "multiplicity must be preserved: a 2-element bag must reconstruct two members, got {members:?} from {got:?}"
    );
    assert!(
        members.iter().all(|m| *m == "1"),
        "both members must be the reduced literal `1`, got {members:?}"
    );
}

#[test]
fn reconstructs_pnew_binder_alpha_equivalently() {
    // (4) `new x in {x!(int(1+2,8))}` → PNew binder reconstruction; the body fold reduces
    //     `int(1+2,8)` to `3` (a width-8 `CastInt`). The reconstructed binder is FRESH (FIX-A
    //     erased the original binder identity), so the result is α-equivalent to
    //     `new x in {x!(3)}`, rendered with the fresh binder as `_`: `new _ in{x!(3)}`.
    //
    //     GOLDEN MOVE (2026-07-24, official-Rholang paren-drop): this string was
    //     `new(_)in{x!(3)}` while `PNew`'s syntax pattern still carried the grouping
    //     parens. Dropping them changes the RENDERING mechanically and only there:
    //       * `"new"` is now immediately followed by the `xs.*sep(",")` repetition, so
    //         Display emits a trailing space (`new ` not `new`) — without it the output
    //         re-lexes as the single Ident `new_` and the roundtrip breaks;
    //       * `"in"` is now immediately preceded by that repetition, so Display emits a
    //         leading space (` in`) for the same anti-glom reason;
    //       * the `(` / `)` literals are simply gone.
    //     `in{` keeps no space because `{` is not an identifier character, so it cannot
    //     glom. The rendered term is unchanged (same `PNew` / same body); only its
    //     spelling moved. Roundtrip is pinned in `rhocalc_new_official_syntax.rs`.
    //
    //     Comparison method: the generated `<Lang>Term::term_eq` is plain field-wise `PartialEq`
    //     (binder pretty-name + `FreeVar` unique_id), NOT moniker's α-aware `Scope::term_eq`, so a
    //     fresh-binder reconstruction never `==` a named-binder term. We use the `format_term`
    //     round-trip the E2 spec offers, PLUS a rigorous α-equivalence cross-check: reducing the
    //     already-folded sibling `new x in {x!(int(3,8))}` must yield the IDENTICAL normal form
    //     (identical NFs ⇒ the same α-class).
    let src = "new x in {x!(int(1+2,8))}";
    let lang = RhoCalcLanguage;
    let term = lang.parse_term(src).expect("parse PNew");
    let nf = RhoCalcLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("dovetail_normal_term({src:?}) returned Err: {e}"));
    let nf_fmt = lang.format_term(nf.as_ref());

    // (4a) PNew binder arm fired and the body fold reduced; fresh binder renders as `_`.
    assert_eq!(
        nf_fmt, "new _ in{x!(3)}",
        "PNew reconstruction must fold the body and render the fresh binder as `_`"
    );

    // (4b) Fixed point under a second `dovetail_normal_term` (format round-trip is stable).
    let reparsed = lang.parse_term(&nf_fmt).expect("re-parse PNew normal form");
    let nf2 = RhoCalcLanguage::dovetail_normal_term(reparsed.as_ref(), MAX_ITERS, MAX_NODES)
        .expect("re-reduce PNew normal form");
    assert_eq!(
        lang.format_term(nf2.as_ref()),
        nf_fmt,
        "PNew normal form must be a fixed point of dovetail_normal_term"
    );

    // (4c) Rigorous α-equivalence: the already-folded sibling reduces to the SAME normal form.
    let sibling_src = "new x in {x!(int(3,8))}";
    let sibling = lang.parse_term(sibling_src).expect("parse sibling");
    let sibling_nf = RhoCalcLanguage::dovetail_normal_term(sibling.as_ref(), MAX_ITERS, MAX_NODES)
        .expect("reduce sibling");
    assert_eq!(
        lang.format_term(sibling_nf.as_ref()),
        nf_fmt,
        "reducing the already-folded sibling must yield the same α-class normal form"
    );
}
