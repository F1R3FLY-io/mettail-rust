//! Hard verification gate for macro-codegen extension **E1** (generalized substitution lowering).
//!
//! Exercises `LambdaLanguage::dovetail_report_for` + `dovetail_normal_term` end-to-end: a language
//! with a binder `[X->Y]` and a rewrite whose RHS is an `(eval <binder-term> <arg>)` substitution
//! now β-reduces in the Dovetail e-graph. Before E1, `dovetail_report_for` errored
//! *"rewrite `Beta` RHS: multi-substitution patterns require generated substitution lowering"*.
//!
//! Everything is derived from `LanguageDef` (no per-language hardcoding); the synthetic `AppSubst`
//! language below proves the mechanism is NOT Lambda-specific.
//!
//! See `docs/design/dovetail-rho-macro-extensions/00-design-and-ledger.md` (E1) and
//! `MF1`/`MF2`/`MF4`/`MF5` therein.
//!
//! ## Note on the divergence gate (MF5 — empirically grounded deviation)
//!
//! The spec's literal gate ("Ω → `dovetail_report_for` returns `Err(IterationLimit/NodeLimit)`")
//! was written from a term-rewriting intuition. Under equality saturation with **α-canonical**
//! e-graph hashing (FIX-A: binder identity erased to an arity marker; body keeps positional
//! de-Bruijn coordinates), the classic Ω = `(λx. x x)(λx. x x)` is a **fixed point**: β(Ω) ≡α Ω, so
//! the contractum's e-class is the redex's own class — no new node, immediate convergence. The
//! e-graph's sound verdict is therefore "Ω's normal form is Ω" (Ω is β-equal only to itself; no
//! smaller form exists). Empirically (this file's `omega_*` tests) NO pure λ-term drives this
//! backend to `IterationLimit`/`NodeLimit` — self-replication, the only growth source, always
//! α-collapses. Artificially forcing an `Err` would require crippling a *convergent* saturation,
//! which is unsound. So the MF5 gate here asserts the genuine safety properties the spec cares
//! about: a non-normalizing term (1) **does not hang**, and (2) **never yields a wrong (reduced)
//! normal form** — it returns Ω itself, β-equal, in bounded time. The `Err` divergence *path*
//! (`sat.outcome != Converged ⇒ Err`) is shared, unchanged typed-path machinery already covered by
//! the Rholang/Calculator fold tests.
#![cfg(all(feature = "lambda", feature = "dovetail-codegen"))]

use mettail_languages::lambda::LambdaLanguage;
use mettail_runtime::Language;

const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 1_000_000;

/// Parse `src`, reduce via `dovetail_normal_term`, return the formatted normal form (or panic).
fn nf(src: &str) -> String {
    let lang = LambdaLanguage;
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    let n = LambdaLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("dovetail_normal_term({src:?}) returned Err: {e}"));
    lang.format_term(n.as_ref())
}

/// Reduce `src` to its formatted normal form, then reduce that AGAIN — the two must agree
/// (format round-trip fixed point), so a fresh-binder reconstruction is α-stable.
fn nf_fixed_point(src: &str) -> String {
    let lang = LambdaLanguage;
    let first = nf(src);
    let reparsed = lang
        .parse_term(&first)
        .unwrap_or_else(|e| panic!("re-parse normal form {first:?} failed: {e}"));
    let second = LambdaLanguage::dovetail_normal_term(reparsed.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("re-reduce {first:?} returned Err: {e}"));
    let second_fmt = lang.format_term(second.as_ref());
    assert_eq!(first, second_fmt, "normal form must be a fixed point of dovetail_normal_term");
    first
}

// ─── Gate 1: identity application reduces ───────────────────────────────────────────────

#[test]
fn gate1_dovetail_report_for_is_ok_for_beta_redex() {
    // Before E1 this returned `Err(... multi-substitution patterns require generated
    // substitution lowering)`. After E1 the substitution rewrite routes to the typed path and
    // the β native rule fires, so the report is `Ok`.
    let lang = LambdaLanguage;
    let term = lang
        .parse_term("(lam x. x, y)")
        .expect("parse identity application");
    let report = LambdaLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES);
    assert!(
        report.is_ok(),
        "dovetail_report_for must be Ok after E1, got {:?}",
        report.err()
    );
}

#[test]
fn gate1_identity_reduces_to_argument() {
    assert_eq!(nf("(lam x. x, y)"), "y", "(λx.x) y must β-reduce to y");
}

// ─── Gate 2: MF1 — the contractum (all value-ops) must beat the App redex ─────────────────

#[test]
fn gate2_mf1_contractum_preferred_over_redex() {
    // `(λx. (x,x)) w` → `(w, w)`. The contractum `(w,w)` is ITSELF `App`-headed (a "redex head"
    // by op), so MF1 is what makes funded-best extraction prefer it over the un-reduced redex
    // `App(Lam.., w)`: both weigh 100 at the head, but the redex additionally carries the `Lam`
    // subtree, so the contractum is strictly cheaper. If MF1 (progress weights) were wrong, the
    // extractor would surface the redex (`(lam x . (x , x) , w)`) and this fails.
    assert_eq!(nf("(lam x. (x,x), w)"), "(w , w)");
}

// ─── Gate 3: nested binder, α-equivalence under fresh-binder reconstruction ───────────────

#[test]
fn gate3_nested_binder_alpha_equivalent() {
    // `(λx. (λy. x)) z` → `(λy. z)`, α-equivalent. FIX-A erases the original binder identity, so
    // the reconstructed binder is FRESH (renders `_`). We verify via (a) the format round-trip
    // fixed point and (b) a rigorous α cross-check: the already-reduced sibling `lam y. z` must
    // reduce to the IDENTICAL normal form (identical NFs ⇒ same α-class). `LambdaTerm`'s
    // `term_eq` is field-wise PartialEq (not α-aware), so the format/fixed-point + sibling
    // approach mirrors `dovetail_normal_term.rs`'s PNew α-check.
    let got = nf_fixed_point("(lam x. (lam y. x), z)");
    // Body fold-free: the result is a single-binder lambda whose body is the free var `z`.
    assert_eq!(got, "lam _ . z", "fresh binder renders `_`; body is the substituted free var z");

    // (α cross-check) The already-reduced sibling reduces to the same α-class normal form.
    let sibling = nf("lam y. z");
    assert_eq!(sibling, got, "reducing the α-equivalent sibling yields the same normal form");
}

// ─── Gate 4 / MF5: a non-normalizing term does not hang and yields no spurious reduced NF ──

#[test]
fn gate4_mf5_omega_terminates_without_spurious_reduction() {
    // Ω = `(λx. x x)(λx. x x)`, written with binary application as `((lam x.(x,x)),(lam x.(x,x)))`.
    // β(Ω) ≡α Ω ⇒ the e-graph reaches a finite fixed point (converges). The verdict is sound:
    // Ω's normal form is Ω (β-equal to itself; no smaller form). Critically this must NOT be a
    // WRONG reduced answer (like `y` or `(w,w)`) and must NOT hang. See the module doc.
    let lang = LambdaLanguage;
    let omega_src = "((lam x. (x,x)), (lam x. (x,x)))";
    let term = lang.parse_term(omega_src).expect("parse Ω");

    // (4a) No hang: bounded-time completion. `dovetail_report_for` converges → Ok (the e-graph
    // never diverges for a self-replicating λ-term; see module doc).
    let report = LambdaLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES);
    assert!(
        report.is_ok(),
        "Ω converges to a fixed point in the e-graph: {:?}",
        report.err()
    );

    // (4b) No SPURIOUS reduction: the normal form is β-equal to Ω itself (a fixed point), and is
    // NOT a strictly-reduced wrong answer. The result still denotes the self-application (it
    // contains the lambdas), not a stuck single variable like `y`.
    //
    // We deliberately do NOT use the `nf_fixed_point` format round-trip here: Ω's normal form is
    // `(lam _ . (x , x) , lam _ . (x , x))`, whose body `(x , x)` contains the BOUND `x` while the
    // fresh reconstructed binder (FIX-A erased the original identity) renders `_`. Re-parsing that
    // string re-reads `x` as a FREE variable (the `_` binder binds nothing), so a second reduction
    // legitimately differs — a known display artifact of unnamed fresh binders (codified for `PNew`
    // in `dovetail_normal_term.rs`), NOT a reduction discrepancy. The returned `Box<dyn Term>` (what
    // the REPL uses) is correctly α-bound; only its *rendering* is lossy for bound-var bodies. So we
    // assert directly on a single reduction.
    let omega_nf = nf(omega_src);
    assert!(
        omega_nf.contains("lam"),
        "Ω's fixed-point normal form must still be the Ω application (contains the lambdas), got {omega_nf:?}"
    );
    assert_ne!(omega_nf, "y", "Ω must not collapse to an unrelated reduced term");
}

#[test]
fn gate4_mf5_tripling_self_application_also_terminates() {
    // A larger self-replicator `((λx.((x,x),x)),(λx.((x,x),x)))` likewise α-collapses to a finite
    // fixed point (no IterationLimit/NodeLimit, no hang).
    let lang = LambdaLanguage;
    let src = "((lam x. ((x,x),x)), (lam x. ((x,x),x)))";
    let term = lang.parse_term(src).expect("parse tripling Ω-variant");
    let report = LambdaLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES);
    assert!(report.is_ok(), "self-replicating term converges: {:?}", report.err());
}

// Gate 6 (generality — a synthetic non-Lambda language β-reduces) lives in its own test binary:
// each `language!` expansion emits crate-level PDA/lexer helpers (`subst_iterative`, `lex`, …)
// with un-namespaced names, so two `language!` invocations cannot coexist in one compilation
// unit. See `lambda_dovetail_synthetic_samecat.rs` (same-category `[T->T]`) and
// `lambda_dovetail_synthetic_crosscat.rs` (cross-category `[Name->Proc]`).
