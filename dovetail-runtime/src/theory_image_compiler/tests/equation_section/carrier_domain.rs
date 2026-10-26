//! Correspondence for SourceEquationCarrierDomain's typed, stable-key domain.
//! All signatures come from source-valid compiled images. Paired source
//! builders use the existing canonicalizer; there is no test normalizer here.

use super::super::source_image_correspondence::{changed_literal, rich_literals};
use super::*;
use crate::{EquationSectionFailureKind, EquationSectionLimits, SourceEquationSection};
use dovetail::key::FramedSemanticOperator;
use dovetail::rules::SaturationOutcome;
use mettail_grammar_core::{PathMapModeV1, VerifiedSourceEquationSectionV1};

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

fn sort_id(fixture: &SectionFixture, name: &str) -> TheorySortId {
    TheorySortId(
        u32::try_from(
            fixture
                .language
                .theory
                .sorts
                .iter()
                .position(|sort| sort.name == name)
                .expect("source fixture declares the requested sort"),
        )
        .expect("bounded fixture sort roster"),
    )
}

fn declare_sort(fixture: &mut SectionFixture, name: &str, kind: TheorySortKindV1) {
    fixture
        .language
        .theory
        .sorts
        .push(TheorySortV1 { name: name.into(), kind });
}

fn opaque(fixture: &mut SectionFixture, name: &str) {
    declare_sort(fixture, name, TheorySortKindV1::Opaque { abi: format!("test/carrier/{name}") });
}

fn constructor(fixture: &mut SectionFixture, name: &str, domain: Vec<String>, result: &str) {
    fixture
        .language
        .theory
        .constructors
        .push(TheoryConstructorV1 {
            name: name.into(),
            domain,
            codomain: result.into(),
        });
}

fn keyed(fixture: &mut SectionFixture, name: &str, kind: CollectionKind, key: &str, value: &str) {
    let pair = format!("{name}Entry");
    declare_sort(
        fixture,
        &pair,
        TheorySortKindV1::Product { factors: vec![key.into(), value.into()] },
    );
    declare_sort(
        fixture,
        name,
        TheorySortKindV1::Collection {
            kind,
            key: Some(key.into()),
            element: pair,
        },
    );
}

fn reorder(fixture: &mut SectionFixture, rotation: usize, reverse: bool) {
    let sorts = &mut fixture.language.theory.sorts;
    let count = sorts.len();
    sorts.rotate_left(rotation % count);
    let constructors = &mut fixture.language.theory.constructors;
    let count = constructors.len();
    constructors.rotate_left(rotation % count);
    if reverse {
        sorts.reverse();
        constructors.reverse();
    }
    fixture.roles = SourceEquationSectionRolesV1 {
        sort: sort_id(fixture, &fixture.sort),
        zero: constructor_id(&fixture.language, &fixture.names[0]),
        unit: constructor_id(&fixture.language, &fixture.names[1]),
        alternative: constructor_id(&fixture.language, &fixture.names[2]),
        product: constructor_id(&fixture.language, &fixture.names[3]),
        closure: constructor_id(&fixture.language, &fixture.names[4]),
    };
}

fn source_certificate<'a>(
    fixture: &'a SectionFixture,
    semantic: &'a TheorySemanticImageV1,
) -> VerifiedSourceEquationSectionV1<'a> {
    semantic
        .check_source_equation_section(
            &fixture.language,
            fixture.roles,
            TheoryImageAdmissionLimits::default(),
        )
        .expect("source and compiled image authenticate before carrier admission")
        .expect("the exact equation roster is complete")
}

fn has_domain(fixture: &SectionFixture, root: &str) -> bool {
    let semantic = compiled_section(&fixture.language);
    let source = source_certificate(fixture, &semantic);
    let section = SourceEquationSection::restore(&source).expect("restore the source section");
    let root = sort_id(fixture, root);
    let report = section
        .check_carrier_domain(root, limits().term, || false)
        .expect("well-formed carrier admission completes within the fixture budget");
    assert!(report.boundary_work > 0);
    if let Some(certificate) = &report.certificate {
        assert!(std::ptr::eq(certificate.source_section(), &source));
        assert!(std::ptr::eq(certificate.source_section().language(), &fixture.language));
        assert!(std::ptr::eq(certificate.source_section().semantic_image(), &semantic));
        assert_eq!(certificate.root_sort(), root);
    }
    report.certificate.is_some()
}

// This arena only writes source syntax. Compilation, construction, collection
// ordering, and section execution all use the production implementation.
struct Arena<'a> {
    fixture: &'a SectionFixture,
    terms: Vec<TheoryTermNodeV1>,
    variables: Vec<TheoryVariableV1>,
}

impl Arena<'_> {
    fn push(&mut self, sort: &str, form: TheoryTermFormV1) -> TheoryTermId {
        let id = TheoryTermId(u32::try_from(self.terms.len()).expect("bounded source arena"));
        self.terms
            .push(TheoryTermNodeV1 { sort: sort.into(), form });
        id
    }

    fn app(&mut self, name: &str, arguments: Vec<TheoryTermId>) -> TheoryTermId {
        let id = constructor_id(&self.fixture.language, name);
        let result = self.fixture.language.theory.constructors[id.0 as usize]
            .codomain
            .clone();
        self.push(&result, TheoryTermFormV1::Constructor { constructor: name.into(), arguments })
    }

    fn role(&mut self, role: usize, arguments: Vec<TheoryTermId>) -> TheoryTermId {
        self.app(&self.fixture.names[role].clone(), arguments)
    }

    fn unit(&mut self, redex: bool) -> TheoryTermId {
        let unit = self.role(1, Vec::new());
        if redex {
            let zero = self.role(0, Vec::new());
            self.role(2, vec![zero, unit])
        } else {
            unit
        }
    }

    fn product(&mut self, sort: &str, factors: Vec<TheoryTermId>) -> TheoryTermId {
        self.push(sort, TheoryTermFormV1::Product { factors })
    }

    fn collection(
        &mut self,
        sort: &str,
        mode: Option<PathMapModeV1>,
        elements: Vec<TheoryTermId>,
    ) -> TheoryTermId {
        self.push(
            sort,
            TheoryTermFormV1::Collection {
                elements,
                remainder: None,
                pathmap_mode: mode,
            },
        )
    }
}

fn add_builder(
    fixture: &mut SectionFixture,
    root: &str,
    name: &str,
    build: impl FnOnce(&mut Arena<'_>) -> TheoryTermId,
) {
    constructor(fixture, name, Vec::new(), root);
    let mut arena = Arena {
        fixture,
        terms: Vec::new(),
        variables: Vec::new(),
    };
    let right = build(&mut arena);
    let left = arena.app(name, Vec::new());
    let source = TheoryRuleArenaV1 {
        variables: arena.variables,
        terms: arena.terms,
        premises: Vec::new(),
        premise_roots: Vec::new(),
    };
    fixture.language.theory.rewrites.push(TheoryRewriteV1 {
        name: name.into(),
        arena: source,
        left,
        right,
    });
}

fn admit(graph: EGraph<FramedSemanticOperator>, root: EClassId) -> SemanticTransitionInput {
    match SemanticTransitionInput::admit(graph, root, limits().term, || false) {
        SemanticInputDecision::Proven(input) => input,
        SemanticInputDecision::Refuted(reason) => panic!("constructed input refused: {reason:?}"),
        SemanticInputDecision::Undetermined { reason, .. } => {
            panic!("constructed input unfinished: {reason:?}")
        },
    }
}

fn constructed(
    fixture: &SectionFixture,
    semantic: &TheorySemanticImageV1,
    root: &str,
    seed: &str,
) -> SemanticTransitionInput {
    let mut graph = EGraph::new();
    let node = graph.add(ENode::leaf(theory_operator_to_machine(
        &TheoryImageOperatorV1::Constructor(constructor_id(&fixture.language, seed)),
    )));
    let matcher = SemanticTransitionMatcher::restore(semantic).expect("restore source builder");
    let rights = LanguageRights::from_rights([LanguageRight::Reduce]);
    let (decision, work) = matcher.execute_rewrite_step_roster_accounted(
        SemanticRelationExecutionRequest {
            image: semantic,
            relation_sort: sort_id(fixture, root),
            granted_rights: &rights,
            input: admit(graph, node),
            limits: normalization_limits(),
        },
        || false,
    );
    let steps = match decision {
        SemanticTransitionDecision::ProvenSteps(steps) => steps,
        SemanticTransitionDecision::Refuted(reason) => panic!("source builder refused: {reason:?}"),
        SemanticTransitionDecision::Undetermined { reason, .. } => {
            panic!("source builder unfinished: {reason:?}")
        },
        _ => panic!("source builder must return the complete one-step roster"),
    };
    assert_eq!(steps.work, work);
    assert_eq!(
        steps.occurrences.len(),
        1,
        "the complete roster contains exactly the designated builder"
    );
    let (graph, occurrences) = steps.into_parts();
    admit(graph, occurrences[0].output)
}

fn assert_normalizes(
    section: &SourceEquationSection<'_>,
    root: TheorySortId,
    input: SemanticTransitionInput,
    expected: &SemanticTransitionInput,
) {
    let report = section
        .normalize_in_sort(input, root, limits(), || false)
        .expect("the admitted typed domain has a bounded successful fixture run");
    assert_eq!(report.normal_form.exact_key(), expected.exact_key());
    for phase in &report.phases {
        assert_eq!(phase.saturation.outcome, SaturationOutcome::Converged);
        assert_eq!(phase.raw_irreducibility.outcome, SaturationOutcome::Converged);
        assert_eq!(phase.raw_irreducibility.stats.total_merges, 0);
    }
    let rerun = section
        .normalize_in_sort(report.normal_form, root, limits(), || false)
        .expect("successful completion is idempotent in the selected sort");
    assert_eq!(rerun.normal_form.exact_key(), expected.exact_key());
    assert_eq!(rerun.phases[0].saturation.stats.total_merges, 0);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(16))]

    // contextual_equations_preserve_selected_carrier and arbitrary_product_keeps_every_factor.
    #[test]
    fn carrier_domain_preserves_renamed_reordered_arbitrary_product_contexts(
        salt in any::<u16>(), rotation in 0usize..100, reverse in any::<bool>(),
        arity in 1usize..=9, constructor_arity in 1usize..=6,
        equation_order in any::<[u8; 10]>(), orientations in any::<[bool; 10]>(),
    ) {
        let mut fixture = section_fixture(&SectionCase {
            salt, equation_order, reversed: orientations, ..SectionCase::default()
        });
        let root = format!("Other_{salt}");
        let product = format!("CarrierProduct_{salt}");
        let wrapper = format!("CarrierWrapper_{salt}");
        let equation = fixture.sort.clone();
        declare_sort(&mut fixture, &product, TheorySortKindV1::Product { factors: vec![equation; arity] });
        constructor(&mut fixture, &wrapper, vec![product.clone(); constructor_arity], &root);
        for (seed, redex) in [("before", true), ("after", false)] {
            add_builder(&mut fixture, &root, seed, |arena| {
                let factors = (0..arity).map(|_| arena.unit(redex)).collect();
                let product = arena.product(&product, factors);
                arena.app(&wrapper, vec![product; constructor_arity])
            });
        }
        reorder(&mut fixture, rotation, reverse);
        let semantic = compiled_section(&fixture.language);
        let certificate = source_certificate(&fixture, &semantic);
        let section = SourceEquationSection::restore(&certificate).expect("restore section");
        let selected = sort_id(&fixture, &root);
        prop_assert_ne!(selected, fixture.roles.sort);
        let admission = section.check_carrier_domain(selected, limits().term, || false).expect("admission completes");
        let domain = admission.certificate.expect("all product factors are retained and no unstable key is reachable");
        prop_assert_eq!(domain.root_sort(), selected);
        prop_assert!(std::ptr::eq(domain.source_section(), &certificate));
        assert_normalizes(&section, selected,
            constructed(&fixture, &semantic, &root, "before"),
            &constructed(&fixture, &semantic, &root, "after"));
    }

    // StableKeySorts quantifies over reachable keyed operators, not all source sorts.
    #[test]
    fn carrier_domain_ignores_unreachable_keyed_sorts_but_refuses_each_reachable_product_factor(
        salt in any::<u16>(), arity in 1usize..=9, rotation in 0usize..100,
        reverse in any::<bool>(), pathmap in any::<bool>(),
    ) {
        let mut fixture = section_fixture(&SectionCase { salt, ..SectionCase::default() });
        let equation = fixture.sort.clone();
        let root = format!("Other_{salt}");
        let kind = if pathmap { CollectionKind::PathMap } else { CollectionKind::Map };
        keyed(&mut fixture, "UnsafeKeys", kind, &equation, &equation);
        opaque(&mut fixture, "Inert");
        declare_sort(&mut fixture, "Envelope", TheorySortKindV1::Product { factors: vec!["Inert".into(); arity] });
        constructor(&mut fixture, "SelectEnvelope", vec!["Envelope".into()], &root);
        reorder(&mut fixture, rotation, reverse);
        prop_assert!(has_domain(&fixture, &root));
        prop_assert!(has_domain(&fixture, &equation));
        prop_assert!(!has_domain(&fixture, "UnsafeKeys"));
        // The generator is bounded; production admission has no arity cap.
        for position in 0..arity {
            let mut changed = fixture.language.clone();
            let sort = changed.theory.sorts.iter_mut().find(|sort| sort.name == "Envelope").expect("product sort");
            let TheorySortKindV1::Product { factors } = &mut sort.kind else { unreachable!() };
            factors[position] = "UnsafeKeys".into();
            let changed_fixture = SectionFixture { language: changed, roles: fixture.roles, sort: fixture.sort.clone(), names: fixture.names.clone(), expected: Vec::new() };
            prop_assert!(!has_domain(&changed_fixture, &root), "factor {} of {} must be traversed", position, arity);
        }
    }

    // substitution_keeps_reverse_function_dependency: Key -> HiddenFn exists
    // solely because substitution returns Key, even with inert domain/body sorts.
    #[test]
    fn carrier_domain_checks_hidden_function_constructors_through_reverse_substitution(
        salt in any::<u16>(), rotation in 0usize..100, multiple in any::<bool>(),
        pathmap in any::<bool>(),
    ) {
        let mut fixture = section_fixture(&SectionCase { salt, ..SectionCase::default() });
        let equation = fixture.sort.clone();
        opaque(&mut fixture, "Key");
        opaque(&mut fixture, "Argument");
        declare_sort(&mut fixture, "HiddenFn", TheorySortKindV1::Function {
            domain: "Argument".into(), codomain: "Key".into(), multiple,
        });
        keyed(&mut fixture, "Selected", if pathmap { CollectionKind::PathMap } else { CollectionKind::Map }, "Key", &equation);
        reorder(&mut fixture, rotation, multiple);
        prop_assert!(has_domain(&fixture, "Selected"));
        constructor(&mut fixture, "FunctionWithEquation", vec![equation], "HiddenFn");
        prop_assert!(!has_domain(&fixture, "Selected"));
    }

    // abstraction_keeps_binder_then_body: both child sorts participate, and
    // multiple-binder metadata must not erase either dependency.
    #[test]
    fn carrier_domain_checks_both_function_positions_and_every_collection_element(
        salt in any::<u16>(), multiple in any::<bool>(), rotation in 0usize..100,
    ) {
        for position in 0..2 {
            let mut fixture = section_fixture(&SectionCase { salt, ..SectionCase::default() });
            let equation = fixture.sort.clone();
            opaque(&mut fixture, "Inert");
            keyed(&mut fixture, "Unsafe", CollectionKind::Map, &equation, &equation);
            declare_sort(&mut fixture, "Function", TheorySortKindV1::Function {
                domain: if position == 0 { "Unsafe" } else { "Inert" }.into(),
                codomain: if position == 1 { "Unsafe" } else { "Inert" }.into(), multiple,
            });
            reorder(&mut fixture, rotation, multiple);
            prop_assert!(!has_domain(&fixture, "Function"));
        }
        for kind in [CollectionKind::List, CollectionKind::Bag, CollectionKind::Set] {
            let mut fixture = section_fixture(&SectionCase { salt, ..SectionCase::default() });
            let equation = fixture.sort.clone();
            keyed(&mut fixture, "Unsafe", CollectionKind::PathMap, &equation, &equation);
            declare_sort(&mut fixture, "Selected", TheorySortKindV1::Collection { kind, key: None, element: "Unsafe".into() });
            reorder(&mut fixture, rotation, multiple);
            prop_assert!(!has_domain(&fixture, "Selected"));
        }
    }
}

#[test]
fn carrier_domain_map_entries_use_physical_products_without_ordinary_pair_constructors() {
    let mut fixture = section_fixture(&SectionCase::default());
    let equation = fixture.sort.clone();
    opaque(&mut fixture, "StableKey");
    keyed(&mut fixture, "UnreachableBadMap", CollectionKind::Map, &equation, &equation);
    keyed(&mut fixture, "SelectedMap", CollectionKind::Map, "StableKey", &equation);
    keyed(&mut fixture, "SelectedPathMap", CollectionKind::PathMap, "StableKey", &equation);
    for name in ["SelectedMap", "SelectedPathMap"] {
        let pair = format!("{name}Entry");
        constructor(
            &mut fixture,
            &format!("{name}OrdinaryPair"),
            vec!["UnreachableBadMap".into()],
            &pair,
        );
        assert!(
            !has_domain(&fixture, &pair),
            "ordinary pair values can use the extra constructor"
        );
        assert!(
            has_domain(&fixture, name),
            "physical entries require the Product signature only"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(12))]

    // canonical_input_with_stable_key_sorts_is_in_domain, typed_key_domain_is_closed,
    // and stable_selected_carrier_successful_results_agree, including all modes.
    #[test]
    fn carrier_domain_stable_keys_complete_for_every_collection_and_pathmap_mode(
        salt in any::<u16>(), repeats in 1usize..=5, reverse in any::<bool>(), rotation in 0usize..100,
    ) {
        for (kind, mode) in [
            (CollectionKind::List, None),
            (CollectionKind::Bag, None),
            (CollectionKind::Set, None),
            (CollectionKind::Map, None),
            (CollectionKind::PathMap, Some(PathMapModeV1::NeutralEmpty)),
            (CollectionKind::PathMap, Some(PathMapModeV1::Set)),
            (CollectionKind::PathMap, Some(PathMapModeV1::Map)),
        ] {
            let mut fixture = section_fixture(&SectionCase { salt, ..SectionCase::default() });
            let equation = fixture.sort.clone();
            opaque(&mut fixture, "Key");
            constructor(&mut fixture, "FirstKey", Vec::new(), "Key");
            constructor(&mut fixture, "SecondKey", Vec::new(), "Key");
            if matches!(kind, CollectionKind::Map | CollectionKind::PathMap) {
                keyed(&mut fixture, "Selected", kind, "Key", &equation);
            } else {
                declare_sort(&mut fixture, "Selected", TheorySortKindV1::Collection { kind, key: None, element: equation.clone() });
            }
            for (seed, redex) in [("before", true), ("after", false)] {
                add_builder(&mut fixture, "Selected", seed, |arena| {
                    let mut elements = match (kind, mode) {
                        (CollectionKind::PathMap, Some(PathMapModeV1::NeutralEmpty)) => Vec::new(),
                        (CollectionKind::PathMap, Some(PathMapModeV1::Set)) => {
                            vec![arena.app("FirstKey", Vec::new()), arena.app("SecondKey", Vec::new())]
                        },
                        (CollectionKind::Map | CollectionKind::PathMap, _) => {
                            let first = arena.app("FirstKey", Vec::new());
                            let second = arena.app("SecondKey", Vec::new());
                            let value = arena.unit(redex);
                            let zero = arena.role(0, Vec::new());
                            vec![arena.product("SelectedEntry", vec![first, value]),
                                arena.product("SelectedEntry", vec![second, zero])]
                        },
                        _ => {
                            let value = arena.unit(redex);
                            let zero = arena.role(0, Vec::new());
                            let mut entries = vec![value; repeats];
                            entries.push(zero);
                            entries
                        },
                    };
                    // Lists retain authored order. Other collection inputs may
                    // arrive in different orders and still have the same result.
                    if reverse && (redex || kind == CollectionKind::List) { elements.reverse(); }
                    arena.collection("Selected", mode, elements)
                });
            }
            reorder(&mut fixture, rotation, reverse);
            let semantic = compiled_section(&fixture.language);
            let source = source_certificate(&fixture, &semantic);
            let section = SourceEquationSection::restore(&source).expect("restore source section");
            let selected = sort_id(&fixture, "Selected");
            prop_assert!(section.check_carrier_domain(selected, limits().term, || false)
                .expect("stable-key admission").certificate.is_some());
            let expected = constructed(&fixture, &semantic, "Selected", "after");
            let expected_count = match (kind, mode) {
                (CollectionKind::List | CollectionKind::Bag, _) => repeats + 1,
                (CollectionKind::PathMap, Some(PathMapModeV1::NeutralEmpty)) => 1,
                (CollectionKind::PathMap, _) => 3,
                _ => 2,
            };
            prop_assert_eq!(expected.root_subroot().child_count(), Some(expected_count));
            if let Some(mode) = mode {
                let marker = expected.root_subroot().child(0).expect("PathMap retains its mode child");
                let expected_marker = theory_operator_to_machine(
                    &TheoryImageOperatorV1::PathMapMode { sort: selected, mode },
                );
                prop_assert_eq!(marker.operator(), Some(&expected_marker));
                prop_assert_eq!(marker.child_count(), Some(0));
            }
            assert_normalizes(&section, selected,
                constructed(&fixture, &semantic, "Selected", "before"), &expected);
        }
    }

    #[test]
    fn carrier_domain_function_binders_and_substitution_keep_typed_children(
        salt in any::<u16>(), multiple in any::<bool>(), rotation in 0usize..100,
    ) {
        let mut fixture = section_fixture(&SectionCase { salt, ..SectionCase::default() });
        let equation = fixture.sort.clone();
        let root = format!("Other_{salt}");
        opaque(&mut fixture, "Binder");
        constructor(&mut fixture, "BinderValue", Vec::new(), "Binder");
        declare_sort(&mut fixture, "Function", TheorySortKindV1::Function {
            domain: "Binder".into(), codomain: equation.clone(), multiple,
        });
        constructor(&mut fixture, "Envelope", vec!["Function".into(), equation.clone()], &root);
        // Authentic source terms compile the abstraction and substitution.
        // A progressing Product(Unit, substitution) -> substitution source
        // rewrite remains outside the section's equation-only execution roster.
        let mut arena = Arena { fixture: &fixture, terms: Vec::new(), variables: vec![
            TheoryVariableV1 { id: TheoryVariableId(0), name: "binder".into(), sort: "Binder".into(), role: TheoryVariableRoleV1::Binder },
            TheoryVariableV1 { id: TheoryVariableId(1), name: "body".into(), sort: equation.clone(), role: TheoryVariableRoleV1::Input },
        ] };
        let body = arena.push(&equation, TheoryTermFormV1::Variable(TheoryVariableId(1)));
        let abstraction = arena.push("Function", TheoryTermFormV1::Abstraction { binder: TheoryVariableId(0), body });
        let argument = arena.app("BinderValue", Vec::new());
        let substitution = arena.push(&equation, TheoryTermFormV1::Substitution { abstraction, argument });
        let unit = arena.role(1, Vec::new());
        let wrapped = arena.role(3, vec![unit, substitution]);
        let source_arena = TheoryRuleArenaV1 { variables: arena.variables, terms: arena.terms, premises: Vec::new(), premise_roots: Vec::new() };
        fixture.language.theory.rewrites.push(TheoryRewriteV1 { name: "unwrap-function-substitution".into(), arena: source_arena, left: wrapped, right: substitution });
        reorder(&mut fixture, rotation, multiple);
        let semantic = compiled_section(&fixture.language);
        let certificate = source_certificate(&fixture, &semantic);
        let section = SourceEquationSection::restore(&certificate).expect("restore section");
        let selected = sort_id(&fixture, &root);
        let function = sort_id(&fixture, "Function");
        for sort in [selected, function, fixture.roles.sort] {
            prop_assert!(section.check_carrier_domain(sort, limits().term, || false).expect("typed carrier admission").certificate.is_some());
        }
        let input = |redex| {
            let mut graph = EGraph::new();
            let mut add = |operator, children| graph.add(ENode::new(theory_operator_to_machine(&operator), children));
            let binder = add(TheoryImageOperatorV1::Constructor(constructor_id(&fixture.language, "BinderValue")), Vec::new());
            let unit = add(TheoryImageOperatorV1::Constructor(fixture.roles.unit), Vec::new());
            let body = if redex {
                let zero = add(TheoryImageOperatorV1::Constructor(fixture.roles.zero), Vec::new());
                add(TheoryImageOperatorV1::Constructor(fixture.roles.alternative), vec![zero, unit])
            } else { unit };
            let abstraction = add(TheoryImageOperatorV1::Abstraction { sort: function }, vec![binder, body]);
            let substitution = add(TheoryImageOperatorV1::Substitution { sort: fixture.roles.sort, function }, vec![abstraction, binder]);
            let root = add(TheoryImageOperatorV1::Constructor(constructor_id(&fixture.language, "Envelope")), vec![abstraction, substitution]);
            admit(graph, root)
        };
        assert_normalizes(&section, selected, input(true), &input(false));
    }
}

fn literal_sorts(fixture: &mut SectionFixture) -> [String; 8] {
    for (name, carrier, builtin) in [
        ("String", TheoryLiteralCarrierV1::String, BuiltinCarrier::String),
        ("Bytes", TheoryLiteralCarrierV1::Bytes, BuiltinCarrier::Bytes),
        ("Integer", TheoryLiteralCarrierV1::Integer, BuiltinCarrier::Integer),
        ("Float", TheoryLiteralCarrierV1::Float, BuiltinCarrier::Float),
        ("Boolean", TheoryLiteralCarrierV1::Boolean, BuiltinCarrier::Boolean),
        ("Rational", TheoryLiteralCarrierV1::Rational, BuiltinCarrier::Rational),
        ("Fixed", TheoryLiteralCarrierV1::FixedPoint, BuiltinCarrier::FixedPoint),
    ] {
        fixture.language.grammar.categories.push(Category {
            id: CategoryId(
                u32::try_from(fixture.language.grammar.categories.len())
                    .expect("bounded literal categories"),
            ),
            name: name.into(),
            carrier: Carrier::Builtin(builtin),
            primary: false,
            admits_variables: false,
        });
        declare_sort(fixture, name, TheorySortKindV1::Syntax { literal: Some(carrier) });
    }
    ["String", "Bytes", "Integer", "Float", "Boolean", "Integer", "Rational", "Fixed"]
        .map(str::to_owned)
}

fn literal_pack(
    arena: &mut Arena<'_>,
    sorts: &[String; 8],
    values: &[TheoryLiteralV1],
    redex: bool,
) -> TheoryTermId {
    let mut children = Vec::with_capacity(values.len() + 1);
    for (sort, value) in sorts.iter().zip(values) {
        children.push(arena.push(sort, TheoryTermFormV1::Literal(value.clone())));
    }
    children.push(arena.unit(redex));
    arena.product("LiteralCarrier", children)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(12))]

    // source_literal_projection_retains_payload_and_carrier. The exact payload
    // checks prevent the paired builders from hiding any accidental erasure.
    #[test]
    fn carrier_domain_preserves_all_literal_payloads_without_identifying_changed_bytes(
        salt in any::<u16>(), rotation in 0usize..100, values in rich_literals(),
    ) {
        let mut fixture = section_fixture(&SectionCase { salt, ..SectionCase::default() });
        let sorts = literal_sorts(&mut fixture);
        let mut factors = sorts.to_vec();
        factors.push(fixture.sort.clone());
        declare_sort(&mut fixture, "LiteralCarrier", TheorySortKindV1::Product { factors });
        add_builder(&mut fixture, "LiteralCarrier", "before", |arena| literal_pack(arena, &sorts, &values, true));
        add_builder(&mut fixture, "LiteralCarrier", "after", |arena| literal_pack(arena, &sorts, &values, false));
        for index in 0..values.len() {
            let mut changed = values.clone();
            changed[index] = changed_literal(&changed[index]);
            add_builder(&mut fixture, "LiteralCarrier", &format!("changed_{index}"), |arena| literal_pack(arena, &sorts, &changed, false));
        }
        reorder(&mut fixture, rotation, true);
        let semantic = compiled_section(&fixture.language);
        let source = source_certificate(&fixture, &semantic);
        let section = SourceEquationSection::restore(&source).expect("restore section");
        let root = sort_id(&fixture, "LiteralCarrier");
        prop_assert!(section.check_carrier_domain(root, limits().term, || false).expect("literal domain admission").certificate.is_some());
        let expected = constructed(&fixture, &semantic, "LiteralCarrier", "after");
        for (index, (sort, value)) in sorts.iter().zip(&values).enumerate() {
            let child = expected.root_subroot().child(index).expect("literal product factor");
            let expected_literal = theory_operator_to_machine(&TheoryImageOperatorV1::Literal {
                sort: sort_id(&fixture, sort), value: value.clone(),
            });
            prop_assert_eq!(child.operator(), Some(&expected_literal));
            prop_assert_eq!(child.child_count(), Some(0));
            let changed = constructed(&fixture, &semantic, "LiteralCarrier", &format!("changed_{index}"));
            prop_assert_ne!(expected.exact_key(), changed.exact_key(), "changed literal {} stays distinct", index);
            assert_normalizes(&section, root,
                constructed(&fixture, &semantic, "LiteralCarrier", &format!("changed_{index}")), &changed);
        }
        assert_normalizes(&section, root, constructed(&fixture, &semantic, "LiteralCarrier", "before"), &expected);
    }

    // A failed sufficient whole-carrier check does not prohibit bounded runs.
    // The same valid carrier also contains the model's collapsing-key counterexample.
    #[test]
    fn carrier_domain_absent_evidence_allows_bounded_success_but_never_hides_key_collision(
        salt in any::<u16>(), rotation in 0usize..100,
    ) {
        for (kind, mode) in [
            (CollectionKind::Map, None),
            (CollectionKind::PathMap, Some(PathMapModeV1::Map)),
            (CollectionKind::PathMap, Some(PathMapModeV1::Set)),
        ] {
            let mut fixture = section_fixture(&SectionCase { salt, ..SectionCase::default() });
            let equation = fixture.sort.clone();
            keyed(&mut fixture, "Selected", kind, &equation, &equation);
            for (seed, redex, collision) in [("before", true, false), ("after", false, false), ("collision", true, true)] {
                add_builder(&mut fixture, "Selected", seed, |arena| {
                    let key = arena.unit(redex);
                    let unit = if collision { arena.unit(false) } else { key };
                    let mut elements = if mode == Some(PathMapModeV1::Set) {
                        vec![key]
                    } else {
                        let value = arena.role(0, Vec::new());
                        vec![arena.product("SelectedEntry", vec![key, value])]
                    };
                    if collision {
                        let other = if mode == Some(PathMapModeV1::Set) { unit } else {
                            let different_value = arena.role(1, Vec::new());
                            arena.product("SelectedEntry", vec![unit, different_value])
                        };
                        elements.push(other);
                    }
                    arena.collection("Selected", mode, elements)
                });
            }
            reorder(&mut fixture, rotation, false);
            let semantic = compiled_section(&fixture.language);
            let source = source_certificate(&fixture, &semantic);
            let section = SourceEquationSection::restore(&source).expect("restore section");
            let root = sort_id(&fixture, "Selected");
            prop_assert!(section.check_carrier_domain(root, limits().term, || false)
                .expect("valid but unsupported carrier").certificate.is_none());
            assert_normalizes(&section, root, constructed(&fixture, &semantic, "Selected", "before"),
                &constructed(&fixture, &semantic, "Selected", "after"));
            let failure = section.normalize_in_sort(constructed(&fixture, &semantic, "Selected", "collision"), root, limits(), || false)
                .expect_err("distinct keys that collapse must refuse publication");
            prop_assert_eq!(failure.reason, EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::InvalidImageEvidence));
        }
    }
}

#[test]
fn carrier_domain_certificate_retains_owner_and_selected_root_and_rejects_unknown_ids() {
    let fixture = section_fixture(&SectionCase::default());
    let semantic = compiled_section(&fixture.language);
    let source = source_certificate(&fixture, &semantic);
    let section = SourceEquationSection::restore(&source).expect("restore section");
    let other = sort_id(&fixture, "Other_0");
    assert_ne!(other, fixture.roles.sort);
    for root in [fixture.roles.sort, other] {
        let report = section
            .check_carrier_domain(root, limits().term, || false)
            .expect("known root");
        let certificate = report.certificate.expect("both roots have stable domains");
        assert_eq!(certificate.root_sort(), root);
        assert!(std::ptr::eq(certificate.source_section(), &source));
        assert!(std::ptr::eq(certificate.source_section().language(), &fixture.language));
        assert!(std::ptr::eq(certificate.source_section().semantic_image(), &semantic));
    }
    for root in [TheorySortId(u32::MAX), TheorySortId(semantic.sorts.len() as u32)] {
        let failure = section
            .check_carrier_domain(root, limits().term, || false)
            .expect_err("unknown root is not optional evidence");
        assert_eq!(
            failure.reason,
            EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::InvalidImageEvidence)
        );
        assert!(failure.boundary_work <= limits().term.work);
    }
    let mut changed = fixture.language.clone();
    changed.theory.equations[0]
        .name
        .push_str("_different_owner");
    changed
        .validate()
        .expect("changed owner is independently source-valid");
    assert!(semantic
        .check_source_equation_section(
            &changed,
            fixture.roles,
            TheoryImageAdmissionLimits::default()
        )
        .is_err());
    let changed_image = compiled_section(&changed);
    let changed_source = changed_image
        .check_source_equation_section(
            &changed,
            fixture.roles,
            TheoryImageAdmissionLimits::default(),
        )
        .expect("new owner authenticates against its own image")
        .expect("unchanged equation schema");
    let changed_section =
        SourceEquationSection::restore(&changed_source).expect("restore separately owned section");
    let changed_certificate = changed_section
        .check_carrier_domain(other, limits().term, || false)
        .expect("separate owner admission")
        .certificate
        .expect("stable domain");
    assert!(std::ptr::eq(changed_certificate.source_section(), &changed_source));
    assert!(!std::ptr::eq(changed_certificate.source_section(), &source));
    assert!(std::ptr::eq(changed_certificate.source_section().language(), &changed));
}

#[test]
fn carrier_domain_exact_work_and_storage_bounds_and_cancellation_publish_no_partial_certificate() {
    let mut fixture = section_fixture(&SectionCase::default());
    let equation = fixture.sort.clone();
    opaque(&mut fixture, "Key");
    keyed(&mut fixture, "Selected", CollectionKind::PathMap, "Key", &equation);
    let semantic = compiled_section(&fixture.language);
    let source = source_certificate(&fixture, &semantic);
    let section = SourceEquationSection::restore(&source).expect("restore section");
    let root = sort_id(&fixture, "Selected");
    let mut polls = 0;
    let complete = section
        .check_carrier_domain(root, limits().term, || {
            polls += 1;
            false
        })
        .expect("baseline admission");
    assert!(complete.certificate.is_some());
    assert!(complete.boundary_work > 0);
    let exact = SemanticInputLimits {
        work: complete.boundary_work,
        ..limits().term
    };
    let replay = section
        .check_carrier_domain(root, exact, || false)
        .expect("exact work budget succeeds");
    assert!(replay.certificate.is_some());
    assert_eq!(replay.boundary_work, complete.boundary_work);
    let short = SemanticInputLimits {
        work: complete.boundary_work - 1,
        ..limits().term
    };
    let failure = section
        .check_carrier_domain(root, short, || false)
        .expect_err("one-under work never returns evidence");
    assert_eq!(
        failure.reason,
        EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::WorkBudgetExhausted)
    );
    assert!(failure.boundary_work <= short.work);

    // Discover the public storage boundary without duplicating the private
    // allocation formula; then exercise its exact and one-under endpoints.
    for nodes in [true, false] {
        let with_bound = |bound| {
            let mut bounded = limits().term;
            if nodes {
                bounded.nodes = bound;
            } else {
                bounded.bytes = bound;
            }
            bounded
        };
        let mut low = 0;
        let mut high = if nodes {
            limits().term.nodes
        } else {
            limits().term.bytes
        };
        while low < high {
            let middle = low + (high - low) / 2;
            match section.check_carrier_domain(root, with_bound(middle), || false) {
                Ok(report) => {
                    assert!(report.certificate.is_some());
                    high = middle;
                },
                Err(failure) => {
                    assert_eq!(
                        failure.reason,
                        EquationSectionFailureKind::Boundary(
                            SemanticMatchUndetermined::InputLimitExceeded
                        )
                    );
                    low = middle + 1;
                },
            }
        }
        assert!(low > 0);
        assert!(section
            .check_carrier_domain(root, with_bound(low), || false)
            .expect("exact storage bound")
            .certificate
            .is_some());
        let failure = section
            .check_carrier_domain(root, with_bound(low - 1), || false)
            .expect_err("one-under storage refuses evidence");
        assert_eq!(
            failure.reason,
            EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::InputLimitExceeded)
        );
        assert!(failure.boundary_work <= limits().term.work);
    }
    assert!(polls > 1, "admission must poll throughout its traversal");
    for stop_at in [1, polls] {
        let mut seen = 0;
        let failure = section
            .check_carrier_domain(root, limits().term, || {
                seen += 1;
                seen >= stop_at
            })
            .expect_err("early and late cancellation never publish partial evidence");
        assert_eq!(
            failure.reason,
            EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::Cancelled)
        );
        assert!(failure.boundary_work <= complete.boundary_work);
        if stop_at > 1 {
            assert!(failure.boundary_work > 0);
        }
    }
}
