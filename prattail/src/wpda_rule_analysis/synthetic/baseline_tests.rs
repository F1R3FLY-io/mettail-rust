use super::*;
use proptest::prelude::*;
use std::cell::RefCell;
use std::rc::Rc;

struct VectorKind(Rc<RefCell<Vec<String>>>);

impl Clone for VectorKind {
    fn clone(&self) -> Self {
        self.0.borrow_mut().push("clone-vector".to_string());
        Self(Rc::clone(&self.0))
    }
}

struct BinderAdapter {
    events: Rc<RefCell<Vec<String>>>,
    has_binder: bool,
}

impl SynthesisAdapter for BinderAdapter {
    type SourceUser = ();
    type SourceType = &'static str;
    type RulePayload = SyntheticRule<VectorKind>;
    type CollectionKind = VectorKind;

    fn clone_user(&mut self, _: &()) -> Self::RulePayload {
        panic!("binder fixtures contain no user rules")
    }

    fn normalize_user(&mut self, _: &mut Self::RulePayload) {
        panic!("binder fixtures contain no user rules to normalize")
    }

    fn first_item_is_var(&mut self, rule: &Self::RulePayload) -> bool {
        self.events
            .borrow_mut()
            .push(format!("scan:{}", rule.label));
        matches!(
            rule.items.first(),
            Some(LegacyAtomicItem::NonTerminal { kind: LegacyAtomicKind::Var, .. })
        )
    }

    fn materialize_synthetic(&mut self, rule: Self::RulePayload) -> Self::RulePayload {
        self.events
            .borrow_mut()
            .push(format!("emit:{}:{}", rule.category, rule.label));
        rule
    }

    fn has_literal_block(&mut self, source: &&'static str) -> bool {
        self.events.borrow_mut().push(format!("probe:{source}"));
        false
    }

    fn literal_label(&mut self, _: &&'static str) -> String {
        panic!("binder fixtures have no native types")
    }

    fn collection(&mut self, _: &&'static str) -> CollectionRecipe<VectorKind> {
        panic!("binder fixtures have no collection declarations")
    }

    fn var_label(&mut self, source: &&'static str) -> String {
        self.events.borrow_mut().push(format!("var-label:{source}"));
        format!("{source}Var")
    }

    fn declares_binder(&mut self) -> bool {
        self.events.borrow_mut().push("binders".to_string());
        self.has_binder
    }
}

fn declaration<'input>(
    source: &'input &'static str,
    is_data: bool,
) -> TypeInput<'input, &'static str> {
    TypeInput {
        name: (*source).to_string(),
        is_data,
        admits_variables: !is_data,
        has_native: false,
        has_collection: false,
        source,
    }
}

#[test]
fn synthetic_binder_baseline_false_gate_has_no_pair_or_vector_work() {
    let name = "A";
    let events = Rc::new(RefCell::new(Vec::new()));
    let mut adapter = BinderAdapter {
        events: Rc::clone(&events),
        has_binder: false,
    };
    let rows = build_per_category_rules(
        &["A".to_string()],
        &[],
        &[declaration(&name, false)],
        VectorKind(Rc::clone(&events)),
        &mut adapter,
    );
    assert_eq!(rows[0].len(), 1);
    assert_eq!(rows[0][0].label, "AVar");
    assert_eq!(*events.borrow(), ["probe:A", "var-label:A", "emit:A:AVar", "binders"]);
}

#[test]
fn synthetic_binder_baseline_missing_domain_and_all_pairs_precede_lambdas() {
    let names = ["A", "Missing", "B", "Closed"];
    let types = [
        declaration(&names[0], false),
        declaration(&names[1], false),
        declaration(&names[2], false),
        declaration(&names[3], true),
    ];
    let events = Rc::new(RefCell::new(Vec::new()));
    let mut adapter = BinderAdapter {
        events: Rc::clone(&events),
        has_binder: true,
    };
    let rows = build_per_category_rules(
        &["B".to_string(), "A".to_string(), "Closed".to_string()],
        &[],
        &types,
        VectorKind(Rc::clone(&events)),
        &mut adapter,
    );
    assert_eq!(
        *events.borrow(),
        [
            "probe:A",
            "probe:B",
            "var-label:A",
            "emit:A:AVar",
            "var-label:B",
            "emit:B:BVar",
            "binders",
            "emit:A:ApplyA",
            "clone-vector",
            "emit:A:MApplyA",
            "emit:A:ApplyMissing",
            "clone-vector",
            "emit:A:MApplyMissing",
            "emit:A:ApplyB",
            "clone-vector",
            "emit:A:MApplyB",
            "emit:B:ApplyA",
            "clone-vector",
            "emit:B:MApplyA",
            "emit:B:ApplyMissing",
            "clone-vector",
            "emit:B:MApplyMissing",
            "emit:B:ApplyB",
            "clone-vector",
            "emit:B:MApplyB",
            "emit:A:LamA",
            "emit:B:LamB",
        ]
    );
    assert!(rows[2].is_empty(), "data declarations do not enter either binder axis");
    for (row, home) in [(&rows[0], "B"), (&rows[1], "A")] {
        assert_eq!(row.len(), 8);
        let apply = &row[3];
        assert_eq!(apply.label, "ApplyMissing");
        assert_eq!(apply.category, home);
        let params = apply
            .term_context
            .as_ref()
            .expect("Apply retains its two parameters");
        assert!(matches!(&params[1], SyntheticParam::Simple {
            name, ty: SyntheticType::Base(domain)
        } if name == "x" && domain == "Missing"));
        assert!(matches!(
            apply.syntax_pattern.as_ref().expect("Apply retains syntax").first(),
            Some(InfixSyntaxShape::Literal(token)) if token == "$missing"
        ));
        let mapply = &row[4];
        assert_eq!(mapply.label, "MApplyMissing");
        assert!(matches!(
            mapply.syntax_pattern.as_ref().expect("MApply retains syntax").first(),
            Some(InfixSyntaxShape::Literal(token)) if token == "$$missing("
        ));
        assert_eq!(row[7].label, format!("Lam{home}"));
    }
}

#[test]
fn noadmit_object_is_a_higher_order_result_but_never_a_binder_domain() {
    let names = ["Open", "ClosedObject"];
    let open = declaration(&names[0], false);
    let mut closed = declaration(&names[1], false);
    closed.admits_variables = false;
    let events = Rc::new(RefCell::new(Vec::new()));
    let mut adapter = BinderAdapter {
        events: Rc::clone(&events),
        has_binder: true,
    };
    let rows = build_per_category_rules(
        &["Open".into(), "ClosedObject".into()],
        &[],
        &[open, closed],
        VectorKind(Rc::clone(&events)),
        &mut adapter,
    );
    let open_labels: Vec<_> = rows[0].iter().map(|rule| rule.label.as_str()).collect();
    let closed_labels: Vec<_> = rows[1].iter().map(|rule| rule.label.as_str()).collect();
    assert_eq!(open_labels, ["OpenVar", "ApplyOpen", "MApplyOpen", "LamOpen"]);
    assert_eq!(closed_labels, ["ApplyOpen", "MApplyOpen"]);
    assert!(!events
        .borrow()
        .iter()
        .any(|event| event.contains("ClosedObjectVar")));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]
    #[test]
    fn every_generated_higher_order_domain_admits_variables(
        admissions in proptest::collection::vec(any::<bool>(), 1..8)
    ) {
        let names = ["T0", "T1", "T2", "T3", "T4", "T5", "T6"];
        let categories: Vec<_> = names[..admissions.len()]
            .iter()
            .map(|name| (*name).to_string())
            .collect();
        let types: Vec<_> = admissions
            .iter()
            .enumerate()
            .map(|(index, admitted)| {
                let mut row = declaration(&names[index], false);
                row.admits_variables = *admitted;
                row
            })
            .collect();
        let events = Rc::new(RefCell::new(Vec::new()));
        let mut adapter = BinderAdapter { events: Rc::clone(&events), has_binder: true };
        let rows = build_per_category_rules(
            &categories,
            &[],
            &types,
            VectorKind(Rc::clone(&events)),
            &mut adapter,
        );
        for (home_index, home) in categories.iter().enumerate() {
            let labels: std::collections::BTreeSet<_> = rows[home_index]
                .iter()
                .map(|rule| rule.label.as_str())
                .collect();
            prop_assert_eq!(labels.contains(format!("{home}Var").as_str()), admissions[home_index]);
            prop_assert_eq!(labels.contains(format!("Lam{home}").as_str()), admissions[home_index]);
            for (domain_index, domain) in categories.iter().enumerate() {
                prop_assert_eq!(
                    labels.contains(format!("Apply{domain}").as_str()),
                    admissions[domain_index]
                );
                prop_assert_eq!(
                    labels.contains(format!("MApply{domain}").as_str()),
                    admissions[domain_index]
                );
            }
        }
    }
}

#[test]
fn synthetic_binder_baseline_duplicate_declarations_repeat_pairs_and_lambda_pass() {
    let name = "A";
    let types = [declaration(&name, false), declaration(&name, false)];
    let events = Rc::new(RefCell::new(Vec::new()));
    let mut adapter = BinderAdapter {
        events: Rc::clone(&events),
        has_binder: true,
    };
    let rows = build_per_category_rules(
        &["A".to_string()],
        &[],
        &types,
        VectorKind(Rc::clone(&events)),
        &mut adapter,
    );
    assert_eq!(
        *events.borrow(),
        [
            "probe:A",
            "probe:A",
            "var-label:A",
            "emit:A:AVar",
            "scan:AVar",
            "binders",
            "emit:A:ApplyA",
            "clone-vector",
            "emit:A:MApplyA",
            "emit:A:ApplyA",
            "clone-vector",
            "emit:A:MApplyA",
            "emit:A:ApplyA",
            "clone-vector",
            "emit:A:MApplyA",
            "emit:A:ApplyA",
            "clone-vector",
            "emit:A:MApplyA",
            "emit:A:LamA",
            "emit:A:LamA",
        ]
    );
    assert_eq!(rows[0].len(), 11);
}
