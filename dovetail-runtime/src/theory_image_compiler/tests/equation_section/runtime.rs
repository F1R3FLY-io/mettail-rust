//! Model-derived executable controls through the existing compiled-rule engine.
//! The small structural oracle is test-only and never evaluates guest rewrites.

mod collections;

use super::super::source_image_correspondence::{changed_literal, rich_literals};
use super::*;
use crate::{
    EquationSectionFailure, EquationSectionFailureKind, EquationSectionLimits,
    EquationSectionReport, SourceEquationSection,
};
use dovetail::key::FramedSemanticOperator;
use dovetail::rules::SaturationOutcome;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Zero,
    Unit,
    Alt,
    Product,
    Closure,
    Atom,
    Pair,
    Plus,
    Optional,
    Repeat,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Tree(Op, Vec<Tree>);

fn leaf(op: Op) -> Tree {
    Tree(op, Vec::new())
}

fn unary(op: Op, child: Tree) -> Tree {
    Tree(op, vec![child])
}

fn binary(op: Op, left: Tree, right: Tree) -> Tree {
    Tree(op, vec![left, right])
}

fn operator(fixture: &SectionFixture, op: Op) -> FramedSemanticOperator {
    theory_operator_to_machine(&TheoryImageOperatorV1::Constructor(operator_id(fixture, op)))
}

fn operator_id(fixture: &SectionFixture, op: Op) -> TheoryConstructorId {
    match op {
        Op::Zero => fixture.roles.zero,
        Op::Unit => fixture.roles.unit,
        Op::Alt => fixture.roles.alternative,
        Op::Product => fixture.roles.product,
        Op::Closure => fixture.roles.closure,
        other => {
            let suffix = match other {
                Op::Atom => "OtherConstant",
                Op::Pair => "OtherBinary",
                Op::Plus => "Plus",
                Op::Optional => "Optional",
                Op::Repeat => "Repeat",
                _ => unreachable!("distinguished roles were handled above"),
            };
            // The parent fixture declares these opaque constructors already.
            let prefix = fixture.names[0]
                .strip_suffix("Zero")
                .expect("parent fixture uses a common generated prefix");
            constructor_id(&fixture.language, &format!("{prefix}{suffix}"))
        },
    }
}

fn limits() -> EquationSectionLimits {
    EquationSectionLimits {
        term: SemanticInputLimits {
            work: 1_000_000,
            nodes: 4_096,
            bytes: 16 * 1024 * 1024,
        },
        egraph_nodes: 4_096,
        saturation_iterations: 128,
        unfolded_occurrences: 100_000,
    }
}

fn admit(graph: EGraph<FramedSemanticOperator>, root: EClassId) -> SemanticTransitionInput {
    match SemanticTransitionInput::admit(graph, root, limits().term, || false) {
        SemanticInputDecision::Proven(input) => input,
        SemanticInputDecision::Refuted(reason) => panic!("test tree admission refused: {reason:?}"),
        SemanticInputDecision::Undetermined { reason, .. } => {
            panic!("test tree admission did not complete: {reason:?}")
        },
    }
}

fn add_tree(
    fixture: &SectionFixture,
    graph: &mut EGraph<FramedSemanticOperator>,
    tree: &Tree,
) -> EClassId {
    // The test generator bounds recursion. Hash-consing deliberately shares
    // equal children; the production occurrence check must still count edges.
    let children = tree
        .1
        .iter()
        .map(|child| add_tree(fixture, graph, child))
        .collect();
    graph.add(ENode::new(operator(fixture, tree.0), children))
}

fn input(fixture: &SectionFixture, tree: &Tree) -> SemanticTransitionInput {
    let mut graph = EGraph::new();
    let root = add_tree(fixture, &mut graph, tree);
    admit(graph, root)
}

fn normalize<C: FnMut() -> bool>(
    fixture: &SectionFixture,
    semantic: &TheorySemanticImageV1,
    input: SemanticTransitionInput,
    limits: EquationSectionLimits,
    cancel: C,
) -> Result<EquationSectionReport, EquationSectionFailure> {
    let certificate = semantic
        .check_source_equation_section(
            &fixture.language,
            fixture.roles,
            TheoryImageAdmissionLimits::default(),
        )
        .expect("runtime test has a valid source/image pair")
        .expect("runtime test has the complete admitted roster");
    let section = SourceEquationSection::restore(&certificate)
        .expect("the existing rule engine restores the witnessed orientations");
    section.normalize(input, limits, cancel)
}

fn success(result: Result<EquationSectionReport, EquationSectionFailure>) -> EquationSectionReport {
    match result {
        Ok(report) => report,
        Err(failure) => panic!(
            "section normalization failed: {:?}, boundary work {}",
            failure.reason, failure.boundary_work
        ),
    }
}

fn failure(
    result: Result<EquationSectionReport, EquationSectionFailure>,
) -> EquationSectionFailure {
    match result {
        Ok(_) => panic!("the refused operation must not publish a normal form"),
        Err(failure) => failure,
    }
}

fn assert_report(report: &EquationSectionReport, expected: &SemanticTransitionInput) {
    assert_eq!(report.normal_form.exact_key(), expected.exact_key());
    assert!(!report.phases.is_empty(), "every result retains its engine phases");
    for (index, phase) in report.phases.iter().enumerate() {
        assert_eq!(phase.saturation.outcome, SaturationOutcome::Converged);
        assert_eq!(phase.raw_irreducibility.outcome, SaturationOutcome::Converged);
        assert_eq!(phase.raw_irreducibility.stats.total_merges, 0);
        if index + 1 < report.phases.len() {
            let probe = phase
                .collection_irreducibility
                .as_ref()
                .expect("only a positive collection probe continues to another phase");
            assert!(probe.stats.total_merges > 0);
        } else if let Some(probe) = &phase.collection_irreducibility {
            assert_eq!(probe.outcome, SaturationOutcome::Converged);
            assert_eq!(probe.stats.total_merges, 0);
        }
    }
    assert!(report.boundary_work > 0);
    assert!(report.boundary_work <= limits().term.work);
    // This is an adapter-boundary receipt, not a count of engine matcher,
    // saturation, inside-weight, or extraction work.
}

fn reference(tree: &Tree) -> Tree {
    let children: Vec<_> = tree.1.iter().map(reference).collect();
    match (tree.0, children.as_slice()) {
        (Op::Alt, [left, right]) if *left == leaf(Op::Zero) => right.clone(),
        (Op::Alt, [left, right]) if *right == leaf(Op::Zero) || left == right => left.clone(),
        (Op::Product, [left, right]) if *left == leaf(Op::Zero) || *right == leaf(Op::Zero) => {
            leaf(Op::Zero)
        },
        (Op::Product, [left, right]) if *left == leaf(Op::Unit) => right.clone(),
        (Op::Product, [left, right]) if *right == leaf(Op::Unit) => left.clone(),
        (Op::Closure, [child]) if *child == leaf(Op::Zero) || *child == leaf(Op::Unit) => {
            leaf(Op::Unit)
        },
        (Op::Closure, [child]) if child.0 == Op::Closure => child.clone(),
        _ => Tree(tree.0, children),
    }
}

fn trees() -> impl Strategy<Value = Tree> {
    prop::sample::select(vec![leaf(Op::Zero), leaf(Op::Unit), leaf(Op::Atom)]).prop_recursive(
        4,
        40,
        2,
        |inner| {
            prop_oneof![
                (inner.clone(), inner.clone()).prop_map(|(left, right)| binary(
                    Op::Alt,
                    left,
                    right
                )),
                (inner.clone(), inner.clone()).prop_map(|(left, right)| binary(
                    Op::Product,
                    left,
                    right
                )),
                (inner.clone(), inner.clone()).prop_map(|(left, right)| binary(
                    Op::Pair,
                    left,
                    right
                )),
                inner.clone().prop_map(|child| unary(Op::Closure, child)),
                inner.clone().prop_map(|child| unary(Op::Plus, child)),
                inner.clone().prop_map(|child| unary(Op::Optional, child)),
                inner.prop_map(|child| unary(Op::Repeat, child)),
            ]
        },
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn section_runtime_matches_structural_reference_and_is_idempotent(
        term in trees(),
        salt in any::<u16>(),
        declaration_rotation in 0usize..42,
        equation_order in any::<[u8; 10]>(),
        reversed in any::<[bool; 10]>(),
        shared in any::<bool>(),
        variable in 0u32..3,
    ) {
        let fixture = section_fixture(&SectionCase {
            salt, declaration_rotation, equation_order, reversed, shared, variable,
            reverse_declarations: true, duplicate: Some(2), ..SectionCase::default()
        });
        let semantic = compiled_section(&fixture.language);
        let expected = input(&fixture, &reference(&term));
        let first = success(normalize(&fixture, &semantic, input(&fixture, &term), limits(), || false));
        assert_report(&first, &expected);
        let first_work = first.boundary_work;
        let second = success(normalize(&fixture, &semantic, first.normal_form, limits(), || false));
        assert_report(&second, &expected);
        prop_assert_eq!(second.phases[0].saturation.stats.total_merges, 0);
        prop_assert!(second.boundary_work >= first_work, "readmission retains the already-spent boundary prefix");
    }

    #[test]
    fn section_runtime_normalizes_nested_terms_in_a_selected_non_equation_sort(
        term in trees(),
        salt in any::<u16>(),
        declaration_rotation in 0usize..42,
        reverse_declarations in any::<bool>(),
        wrapper_arity in 1usize..=5,
    ) {
        let mut fixture = section_fixture(&SectionCase {
            salt, declaration_rotation, reverse_declarations, ..SectionCase::default()
        });
        let carrier_name = format!("Other_{salt}");
        let carrier = TheorySortId(u32::try_from(
            fixture.language.theory.sorts.iter()
                .position(|sort| sort.name == carrier_name)
                .expect("the generated non-equation carrier is declared"),
        ).expect("bounded sort roster"));
        prop_assert_ne!(carrier, fixture.roles.sort);
        let wrapper_name = format!("section_{salt}_CarrierEnvelope");
        fixture.language.theory.constructors.push(TheoryConstructorV1 {
            name: wrapper_name.clone(),
            domain: vec![fixture.sort.clone(); wrapper_arity],
            codomain: carrier_name,
        });
        let wrapper_id = constructor_id(&fixture.language, &wrapper_name);
        let wrapper = theory_operator_to_machine(&TheoryImageOperatorV1::Constructor(wrapper_id));
        let semantic = compiled_section(&fixture.language);
        let certificate = semantic.check_source_equation_section(
            &fixture.language, fixture.roles, TheoryImageAdmissionLimits::default(),
        ).expect("the extended source/image pair is valid")
            .expect("the original equation roster remains complete");
        let section = SourceEquationSection::restore(&certificate)
            .expect("the existing engine restores the same section");
        let wrap = |tree: &Tree| {
            let mut graph = EGraph::new();
            let child = add_tree(&fixture, &mut graph, tree);
            let root = graph.add(ENode::new(wrapper.clone(), vec![child; wrapper_arity]));
            admit(graph, root)
        };
        let term = unary(Op::Plus, binary(Op::Alt, leaf(Op::Zero), term));
        let expected = wrap(&reference(&term));
        let first = success(section.normalize_in_sort(wrap(&term), carrier, limits(), || false));
        assert_report(&first, &expected);
        prop_assert!(first.phases[0].saturation.stats.total_merges > 0);
        let [outer] = first.normal_form.egraph().nodes(first.normal_form.root()) else {
            return Err(TestCaseError::fail("the selected result has one exact outer constructor"));
        };
        prop_assert_eq!(&outer.op, &wrapper);
        prop_assert_eq!(outer.children.len(), wrapper_arity);
        prop_assert_eq!(semantic.constructors.iter()
            .find(|constructor| constructor.id == wrapper_id)
            .expect("the retained constructor is source-declared").codomain, carrier);
        let second = success(section.normalize_in_sort(first.normal_form, carrier, limits(), || false));
        assert_report(&second, &expected);
        prop_assert_eq!(second.phases[0].saturation.stats.total_merges, 0);
        let unknown = TheorySortId(u32::try_from(fixture.language.theory.sorts.len())
            .expect("bounded sort roster"));
        for wrong_sort in [fixture.roles.sort, unknown] {
            let refused = failure(section.normalize_in_sort(wrap(&term), wrong_sort, limits(), || false));
            prop_assert_eq!(refused.reason,
                EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::InvalidImageEvidence));
        }
        let refused = failure(section.normalize(second.normal_form, limits(), || false));
        prop_assert_eq!(refused.reason,
            EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::InvalidImageEvidence));
    }

    #[test]
    fn section_runtime_counts_repeated_shared_edges_at_exact_occurrence_limits(depth in 1u32..=7) {
        let fixture = section_fixture(&SectionCase::default());
        let semantic = compiled_section(&fixture.language);
        let shared_input = || {
            let mut graph = EGraph::new();
            let mut root = graph.add(ENode::leaf(operator(&fixture, Op::Atom)));
            for _ in 0..depth {
                root = graph.add(ENode::new(operator(&fixture, Op::Pair), vec![root, root]));
            }
            let input = admit(graph, root);
            assert_eq!(input.egraph().node_count(), depth as usize + 1);
            input
        };
        let occurrences = (1u64 << (depth + 1)) - 1;
        let mut exact = limits();
        exact.unfolded_occurrences = occurrences;
        let output = success(normalize(&fixture, &semantic, shared_input(), exact, || false));
        assert_report(&output, &shared_input());
        let mut short = limits();
        short.unfolded_occurrences = occurrences - 1;
        let refused = failure(normalize(&fixture, &semantic, shared_input(), short, || false));
        prop_assert!(matches!(refused.reason, EquationSectionFailureKind::OccurrenceLimitExceeded));
        prop_assert!(refused.boundary_work <= limits().term.work);
    }
}

#[test]
fn section_runtime_executes_all_ten_laws_in_opaque_ordered_contexts() {
    let fixture = section_fixture(&SectionCase {
        salt: 41,
        declaration_rotation: 7,
        reversed: [true; 10],
        shared: false,
        variable: 2,
        ..SectionCase::default()
    });
    let semantic = compiled_section(&fixture.language);
    let x = leaf(Op::Atom);
    let zero = leaf(Op::Zero);
    let unit = leaf(Op::Unit);
    let star = unary(Op::Closure, x.clone());
    let examples = [
        (binary(Op::Alt, zero.clone(), x.clone()), x.clone()),
        (binary(Op::Alt, x.clone(), zero.clone()), x.clone()),
        (binary(Op::Alt, x.clone(), x.clone()), x.clone()),
        (binary(Op::Product, zero.clone(), x.clone()), zero.clone()),
        (binary(Op::Product, x.clone(), zero.clone()), zero.clone()),
        (binary(Op::Product, unit.clone(), x.clone()), x.clone()),
        (binary(Op::Product, x.clone(), unit.clone()), x.clone()),
        (unary(Op::Closure, zero), unit.clone()),
        (unary(Op::Closure, unit), leaf(Op::Unit)),
        (unary(Op::Closure, star.clone()), star),
    ];
    for (redex, contractum) in examples {
        // These constructors have no expansion equations. Their ordered
        // children remain opaque contexts while redexes beneath them collapse.
        let context =
            |term| binary(Op::Pair, unary(Op::Plus, term), unary(Op::Optional, x.clone()));
        let expected = input(&fixture, &context(contractum));
        let report = success(normalize(
            &fixture,
            &semantic,
            input(&fixture, &context(redex)),
            limits(),
            || false,
        ));
        assert_report(&report, &expected);
        assert!(report.phases[0].saturation.stats.total_merges > 0);
    }
}

#[test]
fn section_runtime_keeps_plus_optional_repeat_and_order_opaque() {
    let fixture = section_fixture(&SectionCase::default());
    let semantic = compiled_section(&fixture.language);
    let term = binary(
        Op::Pair,
        unary(Op::Plus, unary(Op::Optional, leaf(Op::Atom))),
        unary(Op::Repeat, leaf(Op::Unit)),
    );
    let expected = input(&fixture, &term);
    let report =
        success(normalize(&fixture, &semantic, input(&fixture, &term), limits(), || false));
    assert_report(&report, &expected);
    assert_eq!(report.phases[0].saturation.stats.total_merges, 0);
    let swapped = binary(Op::Pair, term.1[1].clone(), term.1[0].clone());
    assert_ne!(report.normal_form.exact_key(), input(&fixture, &swapped).exact_key());
}

#[test]
fn section_runtime_extracts_finite_results_from_retained_cyclic_redexes() {
    let fixture = section_fixture(&SectionCase::default());
    let semantic = compiled_section(&fixture.language);
    let atom = leaf(Op::Atom);
    let mut term = unary(Op::Closure, atom.clone());
    for _ in 0..5 {
        term = unary(Op::Closure, binary(Op::Alt, term.clone(), term));
    }
    let expected = input(&fixture, &unary(Op::Closure, atom));
    let report =
        success(normalize(&fixture, &semantic, input(&fixture, &term), limits(), || false));
    assert_report(&report, &expected);
    assert!(report.phases[0].saturation.stats.total_merges > 0);
    assert_eq!(report.normal_form.egraph().node_count(), 2);
}

#[test]
fn section_runtime_has_no_schema_depth_limit_on_opaque_contexts() {
    let fixture = section_fixture(&SectionCase::default());
    let semantic = compiled_section(&fixture.language);
    let mut term = binary(Op::Alt, leaf(Op::Zero), leaf(Op::Atom));
    let mut expected = leaf(Op::Atom);
    for _ in 0..48 {
        term = unary(Op::Plus, term);
        expected = unary(Op::Plus, expected);
    }
    let report =
        success(normalize(&fixture, &semantic, input(&fixture, &term), limits(), || false));
    assert_report(&report, &input(&fixture, &expected));
}

#[test]
fn section_runtime_refuses_ground_but_ill_typed_inputs() {
    let fixture = section_fixture(&SectionCase::default());
    let semantic = compiled_section(&fixture.language);
    for malformed in 0..4 {
        let mut graph = EGraph::new();
        let root = match malformed {
            0 => graph.add(ENode::leaf(operator(&fixture, Op::Alt))),
            1 => graph.add(ENode::leaf(theory_operator_to_machine(
                &TheoryImageOperatorV1::Constructor(constructor_id(&fixture.language, "Zero")),
            ))),
            2 => {
                let wrong = graph.add(ENode::leaf(theory_operator_to_machine(
                    &TheoryImageOperatorV1::Constructor(constructor_id(&fixture.language, "Zero")),
                )));
                graph.add(ENode::new(operator(&fixture, Op::Closure), vec![wrong]))
            },
            _ => graph.add(ENode::leaf(FramedSemanticOperator::new(99, vec![b"foreign".to_vec()]))),
        };
        // Exact-key admission is intentionally distinct from source typing.
        let refused =
            failure(normalize(&fixture, &semantic, admit(graph, root), limits(), || false));
        assert!(matches!(
            refused.reason,
            EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::InvalidImageEvidence)
        ));
        assert!(refused.boundary_work <= limits().term.work);
    }
}

#[test]
fn section_runtime_refuses_cancelled_exhausted_and_nonconverged_operations() {
    let fixture = section_fixture(&SectionCase::default());
    let semantic = compiled_section(&fixture.language);
    let term = binary(Op::Alt, leaf(Op::Zero), leaf(Op::Atom));
    let cancelled =
        failure(normalize(&fixture, &semantic, input(&fixture, &term), limits(), || true));
    assert!(matches!(
        cancelled.reason,
        EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::Cancelled)
    ));
    let mut no_work = limits();
    no_work.term.work = 0;
    let admitted = input(&fixture, &term);
    let admission_work = admitted.admission_work();
    let exhausted = failure(normalize(&fixture, &semantic, admitted, no_work, || false));
    assert!(matches!(
        exhausted.reason,
        EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::WorkBudgetExhausted)
    ));
    // Admission predates this call. A smaller ceiling refuses new work but
    // cannot erase the already-spent prefix from its receipt.
    assert_eq!(exhausted.boundary_work, admission_work);
    let mut no_iterations = limits();
    no_iterations.saturation_iterations = 0;
    let stopped =
        failure(normalize(&fixture, &semantic, input(&fixture, &term), no_iterations, || false));
    assert!(matches!(
        stopped.reason,
        EquationSectionFailureKind::Saturation(SaturationOutcome::IterationLimit)
    ));
    let mut no_occurrences = limits();
    no_occurrences.unfolded_occurrences = 0;
    let refused = failure(normalize(
        &fixture,
        &semantic,
        input(&fixture, &leaf(Op::Atom)),
        no_occurrences,
        || false,
    ));
    assert!(matches!(refused.reason, EquationSectionFailureKind::OccurrenceLimitExceeded));
}

#[test]
fn section_runtime_refuses_node_and_term_boundaries_without_publication() {
    let fixture = section_fixture(&SectionCase::default());
    let semantic = compiled_section(&fixture.language);
    let atom = leaf(Op::Atom);
    let mut no_nodes = limits();
    no_nodes.egraph_nodes = 0;
    let refused =
        failure(normalize(&fixture, &semantic, input(&fixture, &atom), no_nodes, || false));
    assert_eq!(
        refused.reason,
        EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::EGraphNodeBudgetExhausted)
    );
    // The atom plus the two required constants exactly funds the private
    // graph; one fewer node refuses while seeding, before engine execution.
    let mut exact = limits();
    exact.egraph_nodes = 3;
    let report = success(normalize(&fixture, &semantic, input(&fixture, &atom), exact, || false));
    assert_report(&report, &input(&fixture, &atom));
    exact.egraph_nodes = 2;
    let refused = failure(normalize(&fixture, &semantic, input(&fixture, &atom), exact, || false));
    assert_eq!(
        refused.reason,
        EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::EGraphNodeBudgetExhausted)
    );
    for nodes in [true, false] {
        let mut bound = limits();
        if nodes {
            bound.term.nodes = 0;
        } else {
            bound.term.bytes = 0;
        }
        let refused =
            failure(normalize(&fixture, &semantic, input(&fixture, &atom), bound, || false));
        assert_eq!(
            refused.reason,
            EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::InputLimitExceeded)
        );
        assert!(refused.boundary_work <= limits().term.work);
    }
}

#[test]
fn section_runtime_preserves_cumulative_work_at_exact_boundary() {
    let fixture = section_fixture(&SectionCase::default());
    let semantic = compiled_section(&fixture.language);
    let term = binary(Op::Alt, leaf(Op::Zero), leaf(Op::Atom));
    let complete =
        success(normalize(&fixture, &semantic, input(&fixture, &term), limits(), || false));
    let mut exact = limits();
    exact.term.work = complete.boundary_work;
    let replay = success(normalize(&fixture, &semantic, input(&fixture, &term), exact, || false));
    assert_eq!(replay.boundary_work, complete.boundary_work);
    assert_eq!(replay.normal_form.exact_key(), complete.normal_form.exact_key());
    exact.term.work -= 1;
    let refused = failure(normalize(&fixture, &semantic, input(&fixture, &term), exact, || false));
    assert_eq!(
        refused.reason,
        EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::WorkBudgetExhausted)
    );
    assert!(refused.boundary_work <= exact.term.work);

    let admitted = input(&fixture, &term);
    let prefix = admitted.admission_work();
    let mut polls = 0;
    let refused = failure(normalize(&fixture, &semantic, admitted, limits(), || {
        polls += 1;
        polls == 3
    }));
    assert_eq!(
        refused.reason,
        EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::Cancelled)
    );
    assert!(
        refused.boundary_work > prefix,
        "earlier boundary work survives later cancellation"
    );
}

struct LiteralSection {
    fixture: SectionFixture,
    sorts: [TheorySortId; 8],
    wrapper: TheoryConstructorId,
}

fn literal_section(salt: u16, literals: &[TheoryLiteralV1]) -> LiteralSection {
    let mut fixture = section_fixture(&SectionCase {
        salt,
        declaration_rotation: usize::from(salt),
        shared: false,
        reversed: [true; 10],
        ..SectionCase::default()
    });
    // Add only the literal carriers required by the shared generator, not a
    // second rich-form grammar. Unit has no source-admissible grammar carrier.
    let mut declarations = BTreeMap::new();
    for (name, carrier, builtin) in [
        ("String", TheoryLiteralCarrierV1::String, BuiltinCarrier::String),
        ("Bytes", TheoryLiteralCarrierV1::Bytes, BuiltinCarrier::Bytes),
        ("Integer", TheoryLiteralCarrierV1::Integer, BuiltinCarrier::Integer),
        ("Float", TheoryLiteralCarrierV1::Float, BuiltinCarrier::Float),
        ("Boolean", TheoryLiteralCarrierV1::Boolean, BuiltinCarrier::Boolean),
        ("Rational", TheoryLiteralCarrierV1::Rational, BuiltinCarrier::Rational),
        ("Fixed", TheoryLiteralCarrierV1::FixedPoint, BuiltinCarrier::FixedPoint),
    ] {
        let source_name = format!("section_literal_{salt}_{name}");
        fixture.language.grammar.categories.push(Category {
            id: CategoryId(
                u32::try_from(fixture.language.grammar.categories.len())
                    .expect("bounded literal category roster"),
            ),
            name: source_name.clone(),
            carrier: Carrier::Builtin(builtin),
            primary: false,
            admits_variables: false,
        });
        let id = TheorySortId(
            u32::try_from(fixture.language.theory.sorts.len())
                .expect("bounded literal sort roster"),
        );
        fixture.language.theory.sorts.push(TheorySortV1 {
            name: source_name.clone(),
            kind: TheorySortKindV1::Syntax { literal: Some(carrier) },
        });
        declarations.insert(name, (source_name, id));
    }
    let literal_names =
        ["String", "Bytes", "Integer", "Float", "Boolean", "Integer", "Rational", "Fixed"];
    assert_eq!(literals.len(), literal_names.len());
    let sorts = literal_names.map(|name| declarations[name].1);
    let wrapper_name = format!("section_literal_{salt}_Envelope");
    let mut domain = vec![fixture.sort.clone()];
    domain.extend(
        literal_names
            .iter()
            .map(|&name| declarations[name].0.clone()),
    );
    fixture
        .language
        .theory
        .constructors
        .push(TheoryConstructorV1 {
            name: wrapper_name.clone(),
            domain,
            codomain: fixture.sort.clone(),
        });
    let wrapper = constructor_id(&fixture.language, &wrapper_name);

    // Compile the generated payloads in a real source arena too. This ordinary
    // rewrite is not part of the ten-equation section's execution roster.
    let prefix = fixture.names[0]
        .strip_suffix("Zero")
        .expect("parent role prefix");
    let mut terms = vec![TheoryTermNodeV1 {
        sort: fixture.sort.clone(),
        form: TheoryTermFormV1::Constructor {
            constructor: format!("{prefix}OtherConstant"),
            arguments: Vec::new(),
        },
    }];
    for (literal, name) in literals.iter().zip(literal_names) {
        terms.push(TheoryTermNodeV1 {
            sort: declarations[name].0.clone(),
            form: TheoryTermFormV1::Literal(literal.clone()),
        });
    }
    terms.push(TheoryTermNodeV1 {
        sort: fixture.sort.clone(),
        form: TheoryTermFormV1::Constructor {
            constructor: wrapper_name,
            arguments: (0..9).map(TheoryTermId).collect(),
        },
    });
    terms.push(TheoryTermNodeV1 {
        sort: fixture.sort.clone(),
        form: TheoryTermFormV1::Constructor {
            constructor: fixture.names[1].clone(),
            arguments: Vec::new(),
        },
    });
    terms.push(TheoryTermNodeV1 {
        sort: fixture.sort.clone(),
        form: TheoryTermFormV1::Constructor {
            constructor: fixture.names[3].clone(),
            arguments: vec![TheoryTermId(10), TheoryTermId(9)],
        },
    });
    fixture.language.theory.rewrites.push(TheoryRewriteV1 {
        name: format!("section-literal-source-{salt}"),
        arena: TheoryRuleArenaV1 {
            variables: Vec::new(),
            terms,
            premises: Vec::new(),
            premise_roots: Vec::new(),
        },
        left: TheoryTermId(11),
        right: TheoryTermId(9),
    });
    LiteralSection { fixture, sorts, wrapper }
}

fn literal_input(
    source: &LiteralSection,
    literals: &[TheoryLiteralV1],
    distinct: Option<&[TheoryLiteralV1]>,
    collapsing: bool,
) -> SemanticTransitionInput {
    let fixture = &source.fixture;
    let mut graph = EGraph::new();
    let pack = |graph: &mut EGraph<FramedSemanticOperator>, values: &[TheoryLiteralV1]| {
        let atom = graph.add(ENode::leaf(operator(fixture, Op::Atom)));
        let first = if collapsing {
            let zero = graph.add(ENode::leaf(operator(fixture, Op::Zero)));
            graph.add(ENode::new(operator(fixture, Op::Alt), vec![zero, atom]))
        } else {
            atom
        };
        let mut children = vec![first];
        for (value, sort) in values.iter().zip(source.sorts) {
            children.push(graph.add(ENode::leaf(theory_operator_to_machine(
                &TheoryImageOperatorV1::Literal { sort, value: value.clone() },
            ))));
        }
        graph.add(ENode::new(
            theory_operator_to_machine(&TheoryImageOperatorV1::Constructor(source.wrapper)),
            children,
        ))
    };
    let mut root = pack(&mut graph, literals);
    if let Some(values) = distinct {
        let other = pack(&mut graph, values);
        root = graph.add(ENode::new(operator(fixture, Op::Alt), vec![root, other]));
    }
    if collapsing {
        root = graph.add(ENode::new(operator(fixture, Op::Alt), vec![root, root]));
        let unit = graph.add(ENode::leaf(operator(fixture, Op::Unit)));
        root = graph.add(ENode::new(operator(fixture, Op::Product), vec![unit, root]));
    }
    admit(graph, root)
}

fn assert_literal_pack(
    source: &LiteralSection,
    output: &SemanticTransitionInput,
    root: EClassId,
    values: &[TheoryLiteralV1],
) {
    let [wrapper] = output.egraph().nodes(root) else {
        panic!("selected wrapper is exact")
    };
    assert_eq!(
        wrapper.op,
        theory_operator_to_machine(&TheoryImageOperatorV1::Constructor(source.wrapper))
    );
    assert_eq!(
        wrapper.children.len(),
        9,
        "ordered scalar fields and context child remain separate"
    );
    let [atom] = output.egraph().nodes(wrapper.children[0]) else {
        panic!("opaque context child is exact")
    };
    assert_eq!(atom.op, operator(&source.fixture, Op::Atom));
    for (index, (value, sort)) in values.iter().zip(source.sorts).enumerate() {
        let [literal] = output.egraph().nodes(wrapper.children[index + 1]) else {
            panic!("selected literal is exact")
        };
        assert!(literal.children.is_empty());
        assert_eq!(
            literal.op,
            theory_operator_to_machine(&TheoryImageOperatorV1::Literal {
                sort,
                value: value.clone()
            }),
            "literal variant {index} retains its exact sort, tag and payload bytes"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(16))]

    #[test]
    fn section_runtime_preserves_all_eight_literal_payloads_and_distinguishes_changed_bytes(
        salt in any::<u16>(), values in rich_literals(),
    ) {
        let source = literal_section(salt, &values);
        let semantic = compiled_section(&source.fixture.language);
        let expected = literal_input(&source, &values, None, false);
        let report = success(normalize(&source.fixture, &semantic, literal_input(&source, &values, None, true), limits(), || false));
        assert_report(&report, &expected);
        assert_literal_pack(&source, &report.normal_form, report.normal_form.root(), &values);
        prop_assert!(report.phases[0].saturation.stats.total_merges > 0);

        for index in 0..values.len() {
            let mut distinct = values.clone();
            distinct[index] = changed_literal(&values[index]);
            prop_assert_ne!(&distinct[index], &values[index]);
            prop_assert!(mettail_grammar_core::is_canonical_theory_literal(&distinct[index]));
            let expected = literal_input(&source, &values, Some(&distinct), false);
            let report = success(normalize(&source.fixture, &semantic,
                literal_input(&source, &values, Some(&distinct), true), limits(), || false));
            assert_report(&report, &expected);
            let [alternative] = report.normal_form.egraph().nodes(report.normal_form.root()) else {
                return Err(TestCaseError::fail("distinct literal envelopes have one exact outer node"));
            };
            prop_assert_eq!(&alternative.op, &operator(&source.fixture, Op::Alt));
            prop_assert_eq!(alternative.children.len(), 2, "payload inequality prevents idempotent collapse");
            prop_assert_ne!(alternative.children[0], alternative.children[1]);
            assert_literal_pack(&source, &report.normal_form, alternative.children[0], &values);
            assert_literal_pack(&source, &report.normal_form, alternative.children[1], &distinct);
        }
    }
}
