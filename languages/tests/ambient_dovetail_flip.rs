//! Ambient + the in-engine AC machinery: status and the binder/freshness gate.
//!
//! Ambient's AC reduction RULES — `InRule`/`OutRule`/`OpenRule` over the
//! parallel `PPar` soup — lower IN-ENGINE through the P4 `AcApp` matcher +
//! associative flattening (validated directly in `dovetail`'s `rules.rs` unit
//! tests over hand-built e-graphs).
//!
//! A *full* Ambient flip through the generated Dovetail report compiler is not
//! yet reachable, and this test pins down exactly why so the gap is auditable:
//! Ambient's structural-congruence EQUATIONS carry the `PNew ^x` binder
//! (`NewComm`) and freshness side conditions (`ScopeExtrusion`, `InNew`,
//! `OutNew`, `OpenNew`, `AmbNew`). The generated compiler FAILS CLOSED on those
//! unlowered families rather than fabricating a complete report. Unlike a
//! process calculus (rhocalc/guarded_rho, whose binders/COMM delegate to the
//! host RSpace via `RhoNativeJoin`), Ambient has no host: its binders + freshness
//! must be lowered IN-ENGINE before it can flip. That binder/freshness lowering
//! is the remaining work; the AC half is done.
#![cfg(all(feature = "ambient", feature = "dovetail-codegen"))]

use mettail_languages::ambient::AmbientLanguage;
use mettail_runtime::Language;

#[test]
fn ambient_dovetail_compiler_fails_closed_on_unlowered_binder_and_freshness_equations() {
    let lang = AmbientLanguage;
    // A well-formed OpenRule redex `{ open(n, 0) | n[0] }` parses fine — the AC
    // rule itself is lowerable; the rejection below is about the *equations*.
    let term = lang
        .parse_term("{ open(n, 0) | n [ 0 ] }")
        .expect("Ambient parses an open redex");
    let err = AmbientLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect_err("Ambient still needs in-engine binder + freshness lowering for its equations");
    assert!(
        err.contains("binder lowering"),
        "fail-closed error must name the unlowered `PNew` binder family: {err}"
    );
    assert!(
        err.contains("side conditions"),
        "fail-closed error must name the unlowered freshness side conditions: {err}"
    );
}
