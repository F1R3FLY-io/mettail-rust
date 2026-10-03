//! Differential checks for the checked, uncoalesced rewrite roster.
//!
//! The finite/complete boundary and equal-target multiplicity are modeled in
//! `formal/rocq/runtime_grammar/theories/SemanticNormalization.v` by
//! `checked_roster_is_complete_ordered_and_bound` and
//! `equal_target_distinct_valid_rules_need_distinct_trace_edges`.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use dovetail::egraph::{EGraph, ENode};
use mettail_dovetail_runtime::{
    compile_theory_semantic_image, theory_operator_to_machine, ProvenSemanticRewriteSteps,
    SemanticInputDecision, SemanticInputLimits, SemanticMatchUndetermined, SemanticPremiseReceipt,
    SemanticRelationExecutionRequest, SemanticTransitionDecision, SemanticTransitionInput,
    SemanticTransitionLimits, SemanticTransitionMatcher,
};
use mettail_grammar_core::{
    Associativity, BuiltinCarrier, Carrier, Category, CategoryId, ConstructorId, EffectDeclV1,
    FieldSource, GrammarCoreV1, LanguageCoreV1, LanguageRight, LanguageRights, Precedence,
    Production, ProductionClass, ProductionId, ReductionPlan, SemanticActionExecutionV1,
    SemanticActionV1, SemanticEffectClassV1, SyntaxItem, TheoryConstructorId, TheoryConstructorV1,
    TheoryImageAdmissionLimits, TheoryImageOperatorV1, TheoryIntrinsicV1, TheoryLiteralCarrierV1,
    TheoryLiteralV1, TheoryPremiseFormV1, TheoryPremiseId, TheoryPremiseNodeV1, TheoryProfileV1,
    TheoryRewriteV1, TheoryRuleArenaV1, TheoryRuleReferenceV1, TheorySortId, TheorySortKindV1,
    TheorySortV1, TheoryTermFormV1, TheoryTermId, TheoryTermNodeV1, TheoryVariableId,
    TheoryVariableRoleV1, TheoryVariableV1, LANGUAGE_CORE_ABI_CURRENT,
};

fn term(name: &str, arguments: Vec<TheoryTermId>) -> TheoryTermNodeV1 {
    TheoryTermNodeV1 {
        sort: "Expr".into(),
        form: TheoryTermFormV1::Constructor { constructor: name.into(), arguments },
    }
}

fn variable_term() -> TheoryTermNodeV1 {
    TheoryTermNodeV1 {
        sort: "Expr".into(),
        form: TheoryTermFormV1::Variable(TheoryVariableId(0)),
    }
}

fn rewrite(name: &str, target: &str) -> TheoryRewriteV1 {
    let mut terms = vec![
        variable_term(),
        term("Zero", vec![]),
        term("Add", vec![TheoryTermId(1), TheoryTermId(0)]),
    ];
    let right = if target == "identity" {
        TheoryTermId(0)
    } else {
        terms.push(term("Wrap", vec![TheoryTermId(0)]));
        TheoryTermId(3)
    };
    TheoryRewriteV1 {
        name: name.into(),
        arena: TheoryRuleArenaV1 {
            variables: vec![TheoryVariableV1 {
                id: TheoryVariableId(0),
                name: "x".into(),
                sort: "Expr".into(),
                role: TheoryVariableRoleV1::Input,
            }],
            terms,
            premises: vec![],
            premise_roots: vec![],
        },
        left: TheoryTermId(2),
        right,
    }
}

fn fixture(extra: &[&str], literal: bool) -> LanguageCoreV1 {
    let mut grammar = GrammarCoreV1::new("LookaheadKernelDiff");
    grammar.categories.push(Category {
        id: CategoryId(0),
        name: "Expr".into(),
        carrier: if literal {
            Carrier::Builtin(BuiltinCarrier::Boolean)
        } else {
            Carrier::Dynamic
        },
        primary: true,
        admits_variables: true,
    });
    for (id, name, arity) in [(0, "Zero", 0), (1, "Wrap", 1), (2, "Add", 2)] {
        let fields: Vec<_> = (0..arity)
            .map(|index| FieldSource::Input(index as u16))
            .collect();
        grammar.productions.push(Production {
            authored: None,
            id: ProductionId(id),
            constructor: ConstructorId(id),
            label: name.into(),
            result: CategoryId(0),
            syntax: (0..arity)
                .map(|index| SyntaxItem::Category {
                    category: CategoryId(0),
                    slot: format!("arg{index}"),
                })
                .collect(),
            precedence: Precedence {
                binding_power: None,
                associativity: Associativity::NonAssociative,
                shares_previous_level: false,
            },
            classification: ProductionClass::default(),
            reduction: id,
            provenance: None,
        });
        grammar.reductions.push(ReductionPlan {
            output_category: CategoryId(0),
            constructor: ConstructorId(id),
            input_arity: arity as u16,
            fields,
            evaluation: None,
            evaluation_mode: None,
            tier: None,
        });
    }
    let mut theory = mettail_grammar_core::TheoryCoreV1::structural();
    theory.profile = TheoryProfileV1::Oslf;
    theory.sorts.push(TheorySortV1 {
        name: "Expr".into(),
        kind: TheorySortKindV1::Syntax {
            literal: literal.then_some(TheoryLiteralCarrierV1::Boolean),
        },
    });
    theory.constructors = [("Zero", 0), ("Wrap", 1), ("Add", 2)]
        .into_iter()
        .map(|(name, arity)| TheoryConstructorV1 {
            name: name.into(),
            domain: vec!["Expr".into(); arity],
            codomain: "Expr".into(),
        })
        .collect();
    theory.rewrites.push(rewrite("add-zero", "identity"));
    for (index, target) in extra.iter().enumerate() {
        theory
            .rewrites
            .push(rewrite(&format!("alternative-{index}"), target));
    }
    theory.effects.push(EffectDeclV1 {
        name: "pure".into(),
        class: SemanticEffectClassV1::Pure,
        requires: vec![],
        emits: vec![],
    });
    theory.actions.push(SemanticActionV1 {
        id: "reduce-add-zero".into(),
        domain: vec!["Expr".into()],
        codomain: "Expr".into(),
        transition: TheoryRuleReferenceV1::Rewrite("add-zero".into()),
        effect: "pure".into(),
        effect_class: SemanticEffectClassV1::Pure,
        required_rights: LanguageRights::from_rights([LanguageRight::Reduce]),
        grade: "Expr".into(),
        execution: SemanticActionExecutionV1::OneStep,
    });
    LanguageCoreV1 {
        abi: LANGUAGE_CORE_ABI_CURRENT,
        grammar,
        theory,
    }
}

fn input(layers: usize, literal: bool) -> SemanticTransitionInput {
    let mut graph = EGraph::new();
    let zero = graph.add(ENode::leaf(theory_operator_to_machine(
        &TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
    )));
    let mut root = if literal {
        graph.add(ENode::leaf(theory_operator_to_machine(&TheoryImageOperatorV1::Literal {
            sort: TheorySortId(0),
            value: TheoryLiteralV1::Boolean(true),
        })))
    } else {
        zero
    };
    for _ in 0..layers {
        root = graph.add(ENode::new(
            theory_operator_to_machine(&TheoryImageOperatorV1::Constructor(TheoryConstructorId(2))),
            vec![zero, root],
        ));
    }
    admit(graph, root)
}

fn admit(
    graph: EGraph<dovetail::key::FramedSemanticOperator>,
    root: dovetail::egraph::EClassId,
) -> SemanticTransitionInput {
    match SemanticTransitionInput::admit(
        graph,
        root,
        SemanticInputLimits {
            work: 100_000,
            nodes: 512,
            bytes: 256 * 1024,
        },
        || false,
    ) {
        SemanticInputDecision::Proven(input) => input,
        _ => panic!("finite test state must be admitted"),
    }
}

fn limits() -> SemanticTransitionLimits {
    SemanticTransitionLimits {
        work: 1_000_000,
        normalization_steps: 64,
        outputs: 64,
        frontier: 256,
        proofs: 256,
        proof_nodes: 256,
        term_nodes: 512,
        term_bytes: 256 * 1024,
        output_nodes: 512,
        output_bytes: 256 * 1024,
    }
}

fn step(
    matcher: &SemanticTransitionMatcher,
    image: &mettail_grammar_core::TheorySemanticImageV1,
    rights: &LanguageRights,
    input: SemanticTransitionInput,
    limits: SemanticTransitionLimits,
) -> ProvenSemanticRewriteSteps {
    let (decision, charged) = matcher.execute_rewrite_step_roster_accounted(
        SemanticRelationExecutionRequest {
            image,
            relation_sort: TheorySortId(0),
            granted_rights: rights,
            input,
            limits,
        },
        || false,
    );
    match decision {
        SemanticTransitionDecision::ProvenSteps(roster) => {
            assert_eq!(roster.work, charged);
            roster
        },
        _ => panic!("finite step roster must be complete"),
    }
}

// Replaying a path lets each proof occurrence take ownership of its exact
// successor e-graph; the public result deliberately does not clone that graph.
fn roster_at_path(
    matcher: &SemanticTransitionMatcher,
    image: &mettail_grammar_core::TheorySemanticImageV1,
    rights: &LanguageRights,
    layers: usize,
    literal: bool,
    path: &[usize],
) -> ProvenSemanticRewriteSteps {
    let mut current = input(layers, literal);
    for &ordinal in path {
        let roster = step(matcher, image, rights, current, limits());
        let (graph, occurrences) = roster.into_parts();
        let occurrence = occurrences
            .get(ordinal)
            .expect("recorded edge still exists");
        assert_eq!(occurrence.ordinal, ordinal);
        current = admit(graph, occurrence.output);
    }
    step(matcher, image, rights, current, limits())
}

fn compare_finite_closure(extra: &[&str], layers: usize, literal: bool, intrinsic: bool) {
    let mut language = fixture(extra, literal);
    if intrinsic {
        language.grammar.categories.push(Category {
            id: CategoryId(1),
            name: "Bool".into(),
            carrier: Carrier::Builtin(BuiltinCarrier::Boolean),
            primary: false,
            admits_variables: false,
        });
        language.theory.sorts.push(TheorySortV1 {
            name: "Bool".into(),
            kind: TheorySortKindV1::Syntax {
                literal: Some(TheoryLiteralCarrierV1::Boolean),
            },
        });
        let arena = &mut language.theory.rewrites[0].arena;
        arena.variables.push(TheoryVariableV1 {
            id: TheoryVariableId(1),
            name: "same".into(),
            sort: "Bool".into(),
            role: TheoryVariableRoleV1::Derived,
        });
        arena.premises.push(TheoryPremiseNodeV1 {
            form: TheoryPremiseFormV1::Intrinsic(TheoryIntrinsicV1::ExactTermEq {
                left: TheoryVariableId(0),
                right: TheoryVariableId(0),
                output: TheoryVariableId(1),
            }),
        });
        arena.premise_roots.push(TheoryPremiseId(0));
    }
    let image = compile_theory_semantic_image(&language, TheoryImageAdmissionLimits::default())
        .expect("finite theory image");
    let matcher = SemanticTransitionMatcher::restore(&image).expect("checked matcher");
    let rights = LanguageRights::from_rights([LanguageRight::Reduce]);
    let initial = roster_at_path(&matcher, &image, &rights, layers, literal, &[]);
    if intrinsic {
        assert_eq!(initial.occurrences.len(), 1);
        assert!(initial.occurrences[0]
            .receipt
            .premises
            .iter()
            .any(|premise| matches!(premise, SemanticPremiseReceipt::Intrinsic { .. })));
    }
    let initial_proofs: BTreeMap<Vec<u8>, Vec<_>> =
        initial
            .occurrences
            .iter()
            .fold(BTreeMap::new(), |mut groups, occurrence| {
                groups
                    .entry(occurrence.receipt.after.clone())
                    .or_default()
                    .push(occurrence.receipt.clone());
                groups
            });
    for (ordinal, occurrence) in initial.occurrences.iter().enumerate() {
        assert_eq!(occurrence.ordinal, ordinal);
        assert_eq!(occurrence.receipt.before, initial.input);
        assert_eq!(occurrence.output_sort, TheorySortId(0));
    }
    if extra.contains(&"identity") && layers > 0 {
        let equal_target_proofs = initial_proofs
            .values()
            .find(|proofs| proofs.len() >= 2)
            .expect("two authored rules must reach one exact target");
        assert_ne!(equal_target_proofs[0].rule, equal_target_proofs[1].rule);
    }

    let mut pending = VecDeque::from([Vec::<usize>::new()]);
    let mut normal_keys = BTreeSet::new();
    let mut trace_count = 0;
    while let Some(path) = pending.pop_front() {
        assert!(path.len() <= layers + 1, "fixture unexpectedly rewrites forever");
        let roster = roster_at_path(&matcher, &image, &rights, layers, literal, &path);
        if roster.occurrences.is_empty() {
            normal_keys.insert(roster.input);
            trace_count += 1;
        } else {
            for occurrence in &roster.occurrences {
                let mut next = path.clone();
                next.push(occurrence.ordinal);
                pending.push_back(next);
            }
        }
    }
    let (decision, charged) = matcher.execute_rewrite_relation_accounted(
        SemanticRelationExecutionRequest {
            image: &image,
            relation_sort: TheorySortId(0),
            granted_rights: &rights,
            input: input(layers, literal),
            limits: limits(),
        },
        || false,
    );
    let SemanticTransitionDecision::ProvenRelation(normalized) = decision else {
        panic!("whole normalization must finish for the finite fixture")
    };
    assert_eq!(normalized.work, charged);
    let normalized_keys: BTreeSet<_> = normalized
        .normal_forms()
        .iter()
        .map(|form| form.receipt.output.clone())
        .collect();
    assert_eq!(normal_keys, normalized_keys);
    for form in normalized.normal_forms() {
        if let Some(first) = form.receipt.normalization_hops.first() {
            let mut actual = first.exhaustive_proofs.clone();
            let mut expected = initial_proofs
                .get(&first.after)
                .expect("first hop in roster")
                .clone();
            actual.sort();
            expected.sort();
            assert_eq!(actual, expected, "whole normalizer lost a first-hop proof");
        } else {
            assert!(initial.occurrences.is_empty());
        }
    }
    assert!(trace_count >= normal_keys.len());
    if extra.contains(&"identity") && layers > 0 {
        assert!(trace_count > normal_keys.len(), "equal targets need separate paths");
    }
}

#[test]
fn finite_typed_theories_agree_after_closure_without_losing_proofs() {
    for extra in [&[][..], &["identity"][..], &["wrap"][..], &["identity", "wrap"][..]] {
        for layers in 0..=3 {
            compare_finite_closure(extra, layers, false, false);
        }
    }
    compare_finite_closure(&[], 12, false, false);
}

#[test]
fn literal_root_has_a_checked_empty_roster_and_zero_hop_normal_form() {
    compare_finite_closure(&[], 0, true, false);
}

#[test]
fn intrinsic_premise_has_the_same_proof_in_roster_and_normalizer() {
    compare_finite_closure(&[], 1, false, true);
}

#[test]
fn finite_equivalence_requires_sufficient_normalization_resources() {
    let language = fixture(&[], false);
    let image = compile_theory_semantic_image(&language, TheoryImageAdmissionLimits::default())
        .expect("resource fixture");
    let matcher = SemanticTransitionMatcher::restore(&image).expect("checked matcher");
    let rights = LanguageRights::from_rights([LanguageRight::Reduce]);
    let one_step = step(&matcher, &image, &rights, input(2, false), limits());
    assert_eq!(one_step.occurrences.len(), 1);
    let (decision, _) = matcher.execute_rewrite_relation_accounted(
        SemanticRelationExecutionRequest {
            image: &image,
            relation_sort: TheorySortId(0),
            granted_rights: &rights,
            input: input(2, false),
            limits: SemanticTransitionLimits { normalization_steps: 0, ..limits() },
        },
        || false,
    );
    assert!(matches!(
        decision,
        SemanticTransitionDecision::Undetermined {
            reason: SemanticMatchUndetermined::NormalizationStepLimitExceeded,
            ..
        }
    ));
    let (decision, _) = matcher.execute_rewrite_step_roster_accounted(
        SemanticRelationExecutionRequest {
            image: &image,
            relation_sort: TheorySortId(0),
            granted_rights: &rights,
            input: input(2, false),
            limits: SemanticTransitionLimits { work: 0, ..limits() },
        },
        || false,
    );
    assert!(matches!(
        decision,
        SemanticTransitionDecision::Undetermined {
            reason: SemanticMatchUndetermined::WorkBudgetExhausted,
            ..
        }
    ));
    let (decision, _) = matcher.execute_rewrite_step_roster_accounted(
        SemanticRelationExecutionRequest {
            image: &image,
            relation_sort: TheorySortId(0),
            granted_rights: &rights,
            input: input(2, false),
            limits: SemanticTransitionLimits { work: one_step.work - 1, ..limits() },
        },
        || false,
    );
    assert!(matches!(decision, SemanticTransitionDecision::Undetermined { .. }));
}
