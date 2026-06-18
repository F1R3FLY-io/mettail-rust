mod support;

use dovetail::egraph::{EGraph, ENode};
use dovetail::extract::{ExtractionCompleteness, Extractor};
use dovetail::rules::{Pattern, RewriteRule, SaturationOutcome};
use rigail::TropicalWeight;

use support::semantic_weight;

fn leaf(eg: &mut EGraph<String>, op: impl Into<String>) -> dovetail::egraph::EClassId {
    eg.add(ENode::leaf(op.into()))
}

fn app(
    eg: &mut EGraph<String>,
    op: impl Into<String>,
    children: Vec<dovetail::egraph::EClassId>,
) -> dovetail::egraph::EClassId {
    eg.add(ENode::new(op.into(), children))
}

#[test]
fn replay_calculator_step_native_handler_shape() {
    for (left, right) in [(-8, 5), (0, 0), (7, 11), (31, -9)] {
        let mut eg = EGraph::<String>::new();
        let l = leaf(&mut eg, format!("Int({left})"));
        let r = leaf(&mut eg, format!("Int({right})"));
        let root = app(&mut eg, "AddInt", vec![l, r]);
        let expected_value = left + right;
        let expected = leaf(&mut eg, format!("Int({expected_value})"));

        let rule = RewriteRule {
            lhs: Pattern::app(
                "AddInt".into(),
                vec![Pattern::leaf(format!("Int({left})")), Pattern::leaf(format!("Int({right})"))],
            ),
            rhs: Pattern::leaf(format!("Int({expected_value})")),
            label: Some("calculator_addint_native_result".into()),
        };
        let report = eg.saturate(&[rule], 4);

        assert_eq!(report.outcome, SaturationOutcome::Converged);
        assert!(eg.equiv(root, expected));

        let mut extractor = Extractor::new(&eg, semantic_weight);
        let best_result = extractor.kth(root, 0);
        let expected_completeness = if expected_value == left || expected_value == right {
            ExtractionCompleteness::BoundedByCycleCut
        } else {
            ExtractionCompleteness::Complete
        };
        assert_eq!(best_result.completeness, expected_completeness);
        let best = best_result.value.expect("native result derivation");
        assert_eq!(best.op, format!("Int({expected_value})"));
        assert_eq!(best.weight, TropicalWeight::new(0.0));

        let mut funded_extractor = Extractor::new(&eg, semantic_weight);
        let funded_best = funded_extractor.funded_best(root);
        assert_eq!(funded_best.completeness, ExtractionCompleteness::Complete);
        assert_eq!(
            funded_best
                .value
                .expect("funded native result derivation")
                .op,
            format!("Int({expected_value})")
        );
    }
}

#[test]
fn replay_lambda_beta_lowering_shape() {
    let mut eg = EGraph::<String>::new();
    let body = leaf(&mut eg, "body");
    let arg = leaf(&mut eg, "arg");
    let lam = app(&mut eg, "Lam", vec![body]);
    let root = app(&mut eg, "App", vec![lam, arg]);
    let expected = app(&mut eg, "beta_result", vec![body, arg]);

    let beta = RewriteRule {
        lhs: Pattern::app(
            "App".into(),
            vec![Pattern::app("Lam".into(), vec![Pattern::var("body")]), Pattern::var("arg")],
        ),
        rhs: Pattern::app("beta_result".into(), vec![Pattern::var("body"), Pattern::var("arg")]),
        label: Some("lambda_beta".into()),
    };
    let report = eg.saturate(&[beta], 4);

    assert_eq!(report.outcome, SaturationOutcome::Converged);
    assert!(eg.equiv(root, expected));
}

#[test]
fn replay_ambient_fixed_arity_collection_lowering_shape() {
    let mut eg = EGraph::<String>::new();
    let n = leaf(&mut eg, "Name(n)");
    let p = leaf(&mut eg, "Proc(p)");
    let q = leaf(&mut eg, "Proc(q)");
    let rest = leaf(&mut eg, "Proc(rest)");
    let open = app(&mut eg, "Open", vec![n, p]);
    let ambient = app(&mut eg, "Amb", vec![n, q]);
    let root = app(&mut eg, "Par3", vec![open, ambient, rest]);
    let expected = app(&mut eg, "Par3", vec![p, q, rest]);

    let open_rule = RewriteRule {
        lhs: Pattern::app(
            "Par3".into(),
            vec![
                Pattern::app("Open".into(), vec![Pattern::var("n"), Pattern::var("p")]),
                Pattern::app("Amb".into(), vec![Pattern::var("n"), Pattern::var("q")]),
                Pattern::var("rest"),
            ],
        ),
        rhs: Pattern::app(
            "Par3".into(),
            vec![Pattern::var("p"), Pattern::var("q"), Pattern::var("rest")],
        ),
        label: Some("ambient_open_fixed_arity".into()),
    };
    let report = eg.saturate(&[open_rule], 4);

    assert_eq!(report.outcome, SaturationOutcome::Converged);
    assert!(eg.equiv(root, expected));
}

#[test]
fn replay_congruence_premise_as_egraph_closure_shape() {
    let mut eg = EGraph::<String>::new();
    let source = leaf(&mut eg, "S0");
    let target = leaf(&mut eg, "S1");
    let context = leaf(&mut eg, "R");
    let source_context = app(&mut eg, "EqInt", vec![source, context]);
    let target_context = app(&mut eg, "EqInt", vec![target, context]);

    let premise = RewriteRule {
        lhs: Pattern::leaf("S0".into()),
        rhs: Pattern::leaf("S1".into()),
        label: Some("premise_step".into()),
    };
    let report = eg.saturate(&[premise], 4);

    assert_eq!(report.outcome, SaturationOutcome::Converged);
    assert!(eg.equiv(source, target));
    assert!(eg.equiv(source_context, target_context));
}
