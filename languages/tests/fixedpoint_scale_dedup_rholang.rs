//! Fixed-point scale identity and explicit-rescaling gates in the consensus language.
//!
//! Equal-number literals with different declared scales used to collapse in Dovetail's hashcons,
//! making fixed-point division depend on which spelling appeared first. Work item #200 separated
//! their identities. These tests measure that repair through Rholang's production normalization
//! path and establish `fixed(value, places)` as the explicit migration operation required by the
//! upstream same-scale precondition.
#![cfg(all(feature = "rholang", feature = "dovetail-codegen"))]

use mettail_languages::rholang::RholangLanguage;
use mettail_runtime::Language;

const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 200_000;

fn normal_form(src: &str) -> Result<String, String> {
    mettail_runtime::clear_var_cache();
    let lang = RholangLanguage;
    let term = lang
        .parse_term(src)
        .map_err(|e| format!("parse error: {e}"))?;
    let normal = RholangLanguage::dovetail_normal_term(term.as_ref(), MAX_ITERS, MAX_NODES)
        .map_err(|e| format!("dovetail_normal_term error: {e}"))?;
    Ok(format!("{normal}"))
}

/// Every binary operation has equal-scale operands, so refusal cannot make the gate vacuous.
/// Both divide operands need a lower-scale sibling to reproduce the original identity defect.
const Q0_SAME_SCALE: &str = "fixed((7.00p2 - 3.00p2), 2) + (7.00p2 / 3.00p2)";
const Q1_LOWER_SCALE_FIRST: &str = "fixed((7.0p1 - 3.0p1), 2) + (7.00p2 / 3.00p2)";
const Q2_LOWER_SCALE_LAST: &str = "(7.00p2 / 3.00p2) + fixed((7.0p1 - 3.0p1), 2)";
const Q3_DIFFERENT_VALUE: &str = "fixed((5.0p1 - 1.0p1), 2) + (7.00p2 / 3.00p2)";

/// The quotient is independent of equal-number sibling literals and their textual order.
#[test]
fn rholang_answer_must_not_depend_on_an_equal_value_sibling() {
    let q0 = normal_form(Q0_SAME_SCALE).expect("Q0");
    let q1 = normal_form(Q1_LOWER_SCALE_FIRST).expect("Q1");
    let q2 = normal_form(Q2_LOWER_SCALE_LAST).expect("Q2");
    let q3 = normal_form(Q3_DIFFERENT_VALUE).expect("Q3");

    assert_eq!(q0, "6.33p2", "control: 4.00p2 + 2.33p2");
    assert_eq!(q1, q0, "★ THE FIX: `6.3p1` before #200 — measured, not assumed");
    assert_eq!(q2, q1, "★ …and order-independent");
    assert_eq!(q3, q0, "control (b-negative)");
}

/// ★★ `fixed(x, w)` — rholang's only scale-repair operator — was a NO-OP for every
/// value-preserving width, because the rescaled result was `Eq`-equal to its own input and the
/// extractor handed back the un-rescaled first-inserted representative. Work item #200 repairs
/// it. See `fixedpoint_scale_dedup_ab::the_rescale_operator_is_no_longer_erased_by_its_own_input`
/// for the full measured correlation table; this pins the consensus lane specifically, because
/// this is the escape hatch used by the scale-equality precondition from work item #186.
#[test]
fn rholang_rescale_operator_is_no_longer_erased_by_its_own_input() {
    for (src, want) in [
        ("fixed(3.0p1, 2)", "3.00p2"),
        ("fixed(3p0, 2)", "3.00p2"),
        ("fixed(1.25p2, 4)", "1.2500p4"),
        ("fixed(1.20p2, 1)", "1.2p1"),
    ] {
        assert_eq!(
            normal_form(src).expect("the rescale must evaluate"),
            want,
            "`{src}` must actually rescale; before #200 it answered its own un-rescaled input",
        );
    }
    assert_eq!(
        normal_form("fixed(0p0, 2)").expect("rescale"),
        "0.00p2",
        "zero must retain the scale requested by the explicit conversion",
    );
}
