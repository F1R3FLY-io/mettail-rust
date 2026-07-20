//! A-S5.4b — host-path semantics pins for the REDECLARED Ambient `OutRule` (AM-1, USER approved;
//! `ma_theory_alignment.md` CORRECTED section).
//!
//! Cardelli–Gordon (Red Out): `m[n[out m.P | Q] | R] → n[P | Q] | m[R]` — the residual `R` stays
//! INSIDE `m`. The production declaration is now
//!
//!     OutRule . |- (PAmb M (PPar {(PAmb N (PPar {(POut M P), ...rest1})), ...rest2}))
//!         ~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M (PPar {...rest2}))});
//!
//! replacing the pre-A-S5.4b shape whose `R`-element + top-spliced `...rest2` EJECTED the residual
//! through the ambient membrane (not derivable in C-G) and could never fire on a singleton body.
//! The Dovetail backend still executes Ambient until A-S5.6, so these pins exercise BOTH host
//! surfaces:
//!
//!   * the GENERATED untyped compiler end-to-end (`dovetail_report_for` — the exact `exec`
//!     machinery), pinning WHICH subjects fire and HOW MANY WAYS (the report exposes rule firings
//!     and completeness; its extraction keeps the funded-best ORIGINAL derivation, so the reduct
//!     SHAPE is pinned on the engine surface below);
//!   * the Dovetail ENGINE (`dovetail::rules`, the e-graph the generated compiler saturates),
//!     with the OutRule lowered exactly as the generated `pattern_to_dovetail` +
//!     `lower_ac_collection` lower the redeclared declaration (root `app(amb)` over an
//!     `ac(par, [nested], Some(rest2))` operand; RHS `ac(par, [n-reduct, m-reduct], None)` with
//!     the rest-only inner bag `ac(par, [], Some(rest2))` riding the m-reduct) — asserting the
//!     REDUCT SHAPE structurally via e-class equivalence (`eg.equiv`), never pretty-strings.
//!
//! Pre-A-S5.4b observed reality (probe log `as54b_probe_out_prechange.log`): the singleton
//! `m[{n[{out(m,0)}]}]` fired NOTHING (stuck — `rule_firings: []`); the 3-element body fired
//! OutRule TWICE (one ejection per choice of the `R` element); the 2-element body fired once.
#![cfg(all(feature = "ambient", feature = "dovetail-codegen"))]

use dovetail::egraph::{EGraph, ENode};
use dovetail::rules::{Pattern, RewriteRule, SaturationOutcome};
use mettail_languages::ambient::AmbientLanguage;
use mettail_runtime::Language;

/// The total OutRule firing count of a complete generated-compiler report for `src`.
fn out_rule_firing_count(src: &str) -> usize {
    let lang = AmbientLanguage;
    let term = lang.parse_term(src).expect("the Ambient subject parses");
    let report = AmbientLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("the generated Ambient Dovetail compiler produces a report");
    assert!(report.is_complete(), "the Out reduction saturates Complete for {src:?}");
    report
        .rule_firings
        .iter()
        .filter(|firing| firing.label.as_deref() == Some("Ambient::rewrite::OutRule"))
        .map(|firing| firing.count)
        .sum()
}

/// (b) THE SINGLETON FIRES: `m[{n[{out(m,0)}]}]` was STUCK pre-A-S5.4b (the ejection-shaped rule
/// required a separate `R` element; C-G fires the singleton via (Struct Zero Par)). The
/// redeclaration's empty-rest legality discharges that: exactly ONE firing.
#[test]
fn out_rule_singleton_fires_on_the_generated_path() {
    assert_eq!(
        out_rule_firing_count("m [ { n [ { out(m, 0) } ] } ]"),
        1,
        "the redeclared OutRule fires the singleton body exactly once \
         (pre-A-S5.4b: zero firings — the stuck-singleton divergence from (Red Out))"
    );
}

/// (a) NO BOUNDARY EJECTION MULTIPLICITY: the 3-element parent body fired TWICE pre-A-S5.4b (one
/// ejection per choice of the `R` element — `{a,b}` split across the membrane). The redeclared
/// rule keeps the WHOLE residual inside `m`, so there is exactly ONE way to fire.
#[test]
fn out_rule_three_element_body_fires_exactly_one_way_on_the_generated_path() {
    assert_eq!(
        out_rule_firing_count("m [ { n [ { out(m, 0) } ] | a [ 0 ] | b [ 0 ] } ]"),
        1,
        "the redeclared OutRule fires the 3-element body exactly once — the whole residual \
         {{a[0], b[0]}} rides ...rest2 into m (pre-A-S5.4b: two ejection firings)"
    );
}

/// (c) THE 2-ELEMENT REGRESSION SUBJECT STILL FIRES (once, as before): the corpus form where the
/// ejection difference never manifested (a single residual element lands with `m` either way).
#[test]
fn out_rule_two_element_body_still_fires_once_on_the_generated_path() {
    assert_eq!(
        out_rule_firing_count("m [ { n [ { out(m, 0) } ] | r } ]"),
        1,
        "the 2-element regression subject fires exactly once, unchanged by the redeclaration"
    );
}

// ─── The ENGINE-level structural reduct pins (e-class equivalence, never pretty-strings) ────────

/// The redeclared `OutRule`, lowered EXACTLY as the generated untyped compiler lowers the
/// production declaration (`pattern_to_dovetail` + `lower_ac_collection`): the LHS is the wrapper
/// `app(amb, [M, ac(par, [nested n-ambient], Some(rest2))])` and the RHS keeps the residual inside
/// `m` as the rest-only inner bag `ac(par, [], Some(rest2))` — empty rest legal.
fn redeclared_out_rule() -> RewriteRule<String> {
    RewriteRule {
        lhs: Pattern::app(
            "amb".into(),
            vec![
                Pattern::var("M"),
                Pattern::ac(
                    "par".into(),
                    vec![Pattern::app(
                        "amb".into(),
                        vec![
                            Pattern::var("N"),
                            Pattern::ac(
                                "par".into(),
                                vec![Pattern::app(
                                    "out".into(),
                                    vec![Pattern::var("M"), Pattern::var("P")],
                                )],
                                Some("rest1".into()),
                            ),
                        ],
                    )],
                    Some("rest2".into()),
                ),
            ],
        ),
        rhs: Pattern::ac(
            "par".into(),
            vec![
                Pattern::app(
                    "amb".into(),
                    vec![
                        Pattern::var("N"),
                        Pattern::ac("par".into(), vec![Pattern::var("P")], Some("rest1".into())),
                    ],
                ),
                Pattern::app(
                    "amb".into(),
                    vec![
                        Pattern::var("M"),
                        Pattern::ac("par".into(), Vec::new(), Some("rest2".into())),
                    ],
                ),
            ],
            None,
        ),
        label: Some("OutRule".into()),
    }
}

/// Add a canonical `par` bag node over `children` (the engine's canonical-bag idiom: children
/// sorted by canonical class key).
fn add_par_bag(eg: &mut EGraph<String>, mut children: Vec<dovetail::egraph::EClassId>) -> dovetail::egraph::EClassId {
    children.sort_by_cached_key(|&child| eg.canonical_class_key(child));
    eg.add(ENode::new("par".into(), children))
}

/// (a) STRUCTURAL: `m[{n[{out(m,p)}], a, b}]` reduces to `{n[{p}], m[{a, b}]}` — the residual
/// `{a, b}` KEPT INSIDE `m` — and is NOT equivalent to the pre-A-S5.4b ejected form
/// `{n[{p}], m[a], b}`.
#[test]
fn out_rule_three_element_reduct_keeps_the_residual_inside_m() {
    let mut eg = EGraph::<String>::new();
    let m = eg.add(ENode::leaf("m".into()));
    let n = eg.add(ENode::leaf("n".into()));
    let p = eg.add(ENode::leaf("p".into()));
    let a = eg.add(ENode::leaf("a".into()));
    let b = eg.add(ENode::leaf("b".into()));
    let out = eg.add(ENode::new("out".into(), vec![m, p]));
    let inner_bag = add_par_bag(&mut eg, vec![out]);
    let n_amb = eg.add(ENode::new("amb".into(), vec![n, inner_bag]));
    let outer_bag = add_par_bag(&mut eg, vec![n_amb, a, b]);
    let subject = eg.add(ENode::new("amb".into(), vec![m, outer_bag]));
    eg.rebuild();

    let report = eg.saturate(&[redeclared_out_rule()], 20);
    assert_eq!(report.outcome, SaturationOutcome::Converged, "the Out reduction saturates");

    // Expected reduct: { amb(n, {p}), amb(m, {a, b}) } — the residual INSIDE m.
    let p_found = eg.find(p);
    let p_bag = add_par_bag(&mut eg, vec![p_found]);
    let n_found = eg.find(n);
    let n_reduct = eg.add(ENode::new("amb".into(), vec![n_found, p_bag]));
    let a_found = eg.find(a);
    let b_found = eg.find(b);
    let m_body = add_par_bag(&mut eg, vec![a_found, b_found]);
    let m_found = eg.find(m);
    let m_reduct = eg.add(ENode::new("amb".into(), vec![m_found, m_body]));
    let expected = add_par_bag(&mut eg, vec![n_reduct, m_reduct]);
    assert!(
        eg.equiv(subject, expected),
        "m[{{n[{{out(m,p)}}], a, b}}] must reduce with {{a, b}} KEPT INSIDE m"
    );

    // The pre-A-S5.4b EJECTED form (R = a inside m, b at the top) must NOT be derivable.
    let m_over_a = eg.add(ENode::new("amb".into(), vec![m_found, a_found]));
    let ejected = add_par_bag(&mut eg, vec![n_reduct, m_over_a, b_found]);
    assert!(
        !eg.equiv(subject, ejected),
        "no boundary ejection: the residual never lands OUTSIDE the m membrane"
    );
}

/// (b) STRUCTURAL: the singleton `m[{n[{out(m,p)}]}]` FIRES to `{n[{p}], m[{}]}` (`m[{}]` — the
/// documented `{}`/`0` fragment stand-in for C-G's `m[0]`). Pre-A-S5.4b this subject was STUCK.
#[test]
fn out_rule_singleton_reduct_is_n_p_beside_empty_m() {
    let mut eg = EGraph::<String>::new();
    let m = eg.add(ENode::leaf("m".into()));
    let n = eg.add(ENode::leaf("n".into()));
    let p = eg.add(ENode::leaf("p".into()));
    let out = eg.add(ENode::new("out".into(), vec![m, p]));
    let inner_bag = add_par_bag(&mut eg, vec![out]);
    let n_amb = eg.add(ENode::new("amb".into(), vec![n, inner_bag]));
    let outer_bag = add_par_bag(&mut eg, vec![n_amb]);
    let subject = eg.add(ENode::new("amb".into(), vec![m, outer_bag]));
    eg.rebuild();

    let report = eg.saturate(&[redeclared_out_rule()], 20);
    assert_eq!(report.outcome, SaturationOutcome::Converged, "the Out reduction saturates");

    // Expected reduct: { amb(n, {p}), amb(m, {}) } — the empty-rest instantiation.
    let p_found = eg.find(p);
    let p_bag = add_par_bag(&mut eg, vec![p_found]);
    let n_found = eg.find(n);
    let n_reduct = eg.add(ENode::new("amb".into(), vec![n_found, p_bag]));
    let empty_bag = add_par_bag(&mut eg, Vec::new());
    let m_found = eg.find(m);
    let m_reduct = eg.add(ENode::new("amb".into(), vec![m_found, empty_bag]));
    let expected = add_par_bag(&mut eg, vec![n_reduct, m_reduct]);
    assert!(
        eg.equiv(subject, expected),
        "the singleton m[{{n[{{out(m,p)}}]}}] must fire to {{n[{{p}}], m[{{}}]}} (was stuck \
         pre-A-S5.4b)"
    );
}

/// (c) STRUCTURAL: the 2-element regression subject `m[{n[{out(m,p)}], r}]` reduces to
/// `{n[{p}], m[{r}]}` — the residual stays with `m` exactly as before (no ejection manifested at
/// two elements either way); the redeclaration's ONE term-level shift is pinned EXPLICITLY: the
/// m-body is now the BAG `{r}` (the `...rest2` image), not the pre-A-S5.4b bare `R = r`
/// (`m[r]` and `m[{r}]` are distinct terms in this fragment — the documented bag-body
/// convention).
#[test]
fn out_rule_two_element_reduct_keeps_r_inside_m_as_a_bag() {
    let mut eg = EGraph::<String>::new();
    let m = eg.add(ENode::leaf("m".into()));
    let n = eg.add(ENode::leaf("n".into()));
    let p = eg.add(ENode::leaf("p".into()));
    let r = eg.add(ENode::leaf("r".into()));
    let out = eg.add(ENode::new("out".into(), vec![m, p]));
    let inner_bag = add_par_bag(&mut eg, vec![out]);
    let n_amb = eg.add(ENode::new("amb".into(), vec![n, inner_bag]));
    let outer_bag = add_par_bag(&mut eg, vec![n_amb, r]);
    let subject = eg.add(ENode::new("amb".into(), vec![m, outer_bag]));
    eg.rebuild();

    let report = eg.saturate(&[redeclared_out_rule()], 20);
    assert_eq!(report.outcome, SaturationOutcome::Converged, "the Out reduction saturates");

    // Expected reduct: { amb(n, {p}), amb(m, {r}) } — r kept with m, bag-bodied.
    let p_found = eg.find(p);
    let p_bag = add_par_bag(&mut eg, vec![p_found]);
    let n_found = eg.find(n);
    let n_reduct = eg.add(ENode::new("amb".into(), vec![n_found, p_bag]));
    let r_found = eg.find(r);
    let r_bag = add_par_bag(&mut eg, vec![r_found]);
    let m_found = eg.find(m);
    let m_reduct = eg.add(ENode::new("amb".into(), vec![m_found, r_bag]));
    let expected = add_par_bag(&mut eg, vec![n_reduct, m_reduct]);
    assert!(
        eg.equiv(subject, expected),
        "the 2-element subject must reduce to {{n[{{p}}], m[{{r}}]}} — the residual with m"
    );

    // The bag-body convention shift, explicit: the pre-A-S5.4b reduct wrapped r BARE (`m[r]`);
    // the redeclared rule wraps the residual BAG (`m[{r}]`). The bare form is NOT derivable.
    let m_over_bare_r = eg.add(ENode::new("amb".into(), vec![m_found, r_found]));
    let bare_form = add_par_bag(&mut eg, vec![n_reduct, m_over_bare_r]);
    assert!(
        !eg.equiv(subject, bare_form),
        "the redeclared rule produces the bag-bodied m[{{r}}], never the bare-bodied m[r] \
         (the documented convention shift from the ejection-shaped declaration)"
    );
}
