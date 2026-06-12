use dovetail::egraph::{EGraph, ENode};
use dovetail::rules::{Pattern, RewriteRule, SaturationOutcome};
use dovetail::space::{Fired, InMemSpace, Match, TupleSpace};

fn parity_cases() -> usize {
    std::env::var("DOVETAIL_PARITY_CASES")
        .ok()
        .and_then(|raw| raw.parse::<usize>().ok())
        .filter(|cases| *cases > 0)
        .unwrap_or(64)
}

fn next(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn small_i32(seed: &mut u64) -> i32 {
    (next(seed) % 81) as i32 - 40
}

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

fn calculator_step_native_case(left: i32, right: i32) {
    let mut eg = EGraph::<String>::new();
    let l = leaf(&mut eg, format!("Calculator::Int({left})"));
    let r = leaf(&mut eg, format!("Calculator::Int({right})"));
    let root = app(&mut eg, "Calculator::AddInt", vec![l, r]);
    let expected_value = left + right;
    let expected = leaf(&mut eg, format!("Calculator::Int({expected_value})"));

    let lowered_native_rule = RewriteRule {
        lhs: Pattern::app(
            "Calculator::AddInt".into(),
            vec![
                Pattern::leaf(format!("Calculator::Int({left})")),
                Pattern::leaf(format!("Calculator::Int({right})")),
            ],
        ),
        rhs: Pattern::leaf(format!("Calculator::Int({expected_value})")),
        label: Some("Calculator::AddInt/native".into()),
    };

    let report = eg.saturate(&[lowered_native_rule], 4);
    assert_eq!(report.outcome, SaturationOutcome::Converged);
    assert!(eg.equiv(root, expected));
}

fn lambda_beta_case(case_idx: usize) {
    let mut eg = EGraph::<String>::new();
    let body = leaf(&mut eg, format!("Lambda::body({case_idx})"));
    let arg = leaf(&mut eg, format!("Lambda::arg({case_idx})"));
    let lam = app(&mut eg, "Lambda::Lam", vec![body]);
    let root = app(&mut eg, "Lambda::App", vec![lam, arg]);
    let expected = app(&mut eg, "Lambda::eval", vec![body, arg]);

    let beta = RewriteRule {
        lhs: Pattern::app(
            "Lambda::App".into(),
            vec![
                Pattern::app("Lambda::Lam".into(), vec![Pattern::var("body")]),
                Pattern::var("arg"),
            ],
        ),
        rhs: Pattern::app("Lambda::eval".into(), vec![Pattern::var("body"), Pattern::var("arg")]),
        label: Some("Lambda::Beta".into()),
    };

    let report = eg.saturate(&[beta], 4);
    assert_eq!(report.outcome, SaturationOutcome::Converged);
    assert!(eg.equiv(root, expected));
}

fn ambient_open_case(case_idx: usize) {
    let mut eg = EGraph::<String>::new();
    let n = leaf(&mut eg, format!("Ambient::Name({case_idx})"));
    let p = leaf(&mut eg, format!("Ambient::Proc(p{case_idx})"));
    let q = leaf(&mut eg, format!("Ambient::Proc(q{case_idx})"));
    let rest = leaf(&mut eg, format!("Ambient::Proc(rest{case_idx})"));
    let open = app(&mut eg, "Ambient::Open", vec![n, p]);
    let ambient = app(&mut eg, "Ambient::Amb", vec![n, q]);
    let root = app(&mut eg, "Ambient::Par3", vec![open, ambient, rest]);
    let expected = app(&mut eg, "Ambient::Par3", vec![p, q, rest]);

    let open_rule = RewriteRule {
        lhs: Pattern::app(
            "Ambient::Par3".into(),
            vec![
                Pattern::app("Ambient::Open".into(), vec![Pattern::var("n"), Pattern::var("p")]),
                Pattern::app("Ambient::Amb".into(), vec![Pattern::var("n"), Pattern::var("q")]),
                Pattern::var("rest"),
            ],
        ),
        rhs: Pattern::app(
            "Ambient::Par3".into(),
            vec![Pattern::var("p"), Pattern::var("q"), Pattern::var("rest")],
        ),
        label: Some("Ambient::Open".into()),
    };

    let report = eg.saturate(&[open_rule], 4);
    assert_eq!(report.outcome, SaturationOutcome::Converged);
    assert!(eg.equiv(root, expected));
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RhoPat {
    Any,
    Exact(String),
}

struct RhoMatcher;

impl Match<RhoPat, String> for RhoMatcher {
    type Bindings = String;

    fn matches(&self, pat: &RhoPat, data: &String) -> Option<Self::Bindings> {
        match pat {
            RhoPat::Any => Some(data.clone()),
            RhoPat::Exact(expected) => (expected == data).then(|| data.clone()),
        }
    }
}

fn rho_comm_case(case_idx: usize) {
    let mut space = InMemSpace::<String, RhoPat, String, String, RhoMatcher>::new(RhoMatcher);
    let chan = format!("rho-channel-{}", case_idx % 5);
    let datum = format!("rho-data-{case_idx}");
    let cont = format!("rho-cont-{case_idx}");

    assert_eq!(space.produce(chan.clone(), datum.clone()), None);
    assert_eq!(space.parked_data(&chan), 1);
    assert_eq!(
        space.consume(chan.clone(), RhoPat::Exact(datum.clone()), cont.clone()),
        Some(Fired {
            partner: datum.clone(),
            bindings: datum.clone(),
        })
    );
    assert_eq!(space.parked_data(&chan), 0);

    assert_eq!(
        space.consume(chan.clone(), RhoPat::Any, cont.clone()),
        None,
        "second consume parks when no datum is waiting"
    );
    assert_eq!(space.parked_conts(&chan), 1);
    assert_eq!(
        space.produce(chan, datum.clone()),
        Some(Fired { partner: cont, bindings: datum })
    );
}

#[test]
fn dovetail_handles_representative_mettail_rewrite_shapes() {
    let mut seed = 0xd07e_7a11_u64;
    for case_idx in 0..parity_cases() {
        let left = small_i32(&mut seed);
        let right = small_i32(&mut seed);

        calculator_step_native_case(left, right);
        lambda_beta_case(case_idx);
        ambient_open_case(case_idx);
        rho_comm_case(case_idx);
    }
}
