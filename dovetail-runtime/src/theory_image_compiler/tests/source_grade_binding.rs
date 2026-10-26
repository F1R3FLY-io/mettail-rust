//! Completion uses the premise-extended substitution for both RHS and grade.

use super::*;
use crate::SemanticPremiseReceipt;
use dovetail::key::FramedSemanticOperator;
use mettail_grammar_core::CostGradeRuleV1;

fn premise_grade_fixture(
    equation_count: usize,
    declaration_rotation: usize,
    reverse_variables: bool,
    reverse_variable_nodes: bool,
    reverse_rewrites: bool,
    reverse_grade_rows: bool,
) -> (LanguageCoreV1, TheoryVariableId, TheoryVariableId) {
    let mut language = costed_fixture();
    // A typed internal grade constructor needs no new syntax production.
    // Existing continued-profile labels remain unrelated fixture metadata.
    language.theory.constructors.push(TheoryConstructorV1 {
        name: "SigOfExpr".into(),
        domain: vec!["Expr".into()],
        codomain: "Sig".into(),
    });
    let source = TheoryVariableId(u32::from(reverse_variables));
    let target = TheoryVariableId(1 - source.0);
    let source_term = TheoryTermId(u32::from(reverse_variable_nodes));
    let target_term = TheoryTermId(1 - source_term.0);
    let variables = (0..2)
        .map(|id| TheoryVariableV1 {
            id: TheoryVariableId(id),
            name: if id == source.0 { "source" } else { "target" }.into(),
            sort: "Expr".into(),
            role: if id == source.0 {
                TheoryVariableRoleV1::Input
            } else {
                TheoryVariableRoleV1::Derived
            },
        })
        .collect();
    let mut terms = (0..2)
        .map(|index| {
            term_variable(if index == source_term.0 {
                source.0
            } else {
                target.0
            })
        })
        .collect::<Vec<_>>();
    terms.push(term_constructor("Wrap", vec![source_term]));
    terms.push(TheoryTermNodeV1 {
        sort: "Sig".into(),
        form: TheoryTermFormV1::Constructor {
            constructor: "SigOfExpr".into(),
            arguments: vec![target_term],
        },
    });
    language.theory.rewrites.push(TheoryRewriteV1 {
        name: "premise-grade-step".into(),
        arena: TheoryRuleArenaV1 {
            variables,
            terms,
            premises: vec![TheoryPremiseNodeV1 {
                form: TheoryPremiseFormV1::Transition { source, target },
            }],
            premise_roots: vec![TheoryPremiseId(0)],
        },
        left: TheoryTermId(2),
        right: target_term,
    });
    language.theory.actions[0].id = "reduce-premise-grade".into();
    language.theory.actions[0].transition =
        TheoryRuleReferenceV1::Rewrite("premise-grade-step".into());
    let cost = language.theory.cost.as_mut().unwrap();
    cost.grade_rules.push(CostGradeRuleV1 {
        rewrite: "premise-grade-step".into(),
        term: TheoryTermId(3),
    });
    if reverse_grade_rows {
        cost.grade_rules.reverse();
    }
    if reverse_rewrites {
        language.theory.rewrites.reverse();
    }
    let equation = language.theory.equations[0].clone();
    language.theory.equations = (0..equation_count)
        .map(|index| {
            let mut equation = equation.clone();
            equation.name = format!("commutative-{index}");
            equation
        })
        .collect();
    let sort_count = language.theory.sorts.len();
    language
        .theory
        .sorts
        .rotate_left(declaration_rotation % sort_count);
    let constructor_count = language.theory.constructors.len();
    language
        .theory
        .constructors
        .rotate_left(declaration_rotation % constructor_count);
    (language, source, target)
}

fn input_limits() -> SemanticInputLimits {
    SemanticInputLimits {
        work: 10_000,
        nodes: 128,
        bytes: 64 * 1024,
    }
}

// Construct only ground test data through the existing e-graph/input boundary.
// `redex` inserts the actual add-zero LHS, never a second rewrite evaluator.
fn fixture_input(
    language: &LanguageCoreV1,
    internal_leaf: bool,
    depth: usize,
    redex: bool,
    outer: Option<&str>,
) -> SemanticTransitionInput {
    let constructor = |name: &str| {
        let index = language
            .theory
            .constructors
            .iter()
            .position(|constructor| constructor.name == name)
            .expect("declared test constructor");
        theory_operator_to_machine(&TheoryImageOperatorV1::Constructor(TheoryConstructorId(
            index as u32,
        )))
    };
    let mut graph: EGraph<FramedSemanticOperator> = EGraph::new();
    let zero = graph.add(ENode::leaf(constructor("Zero")));
    let mut root = if internal_leaf {
        graph.add(ENode::leaf(constructor("InternalExpr")))
    } else {
        zero
    };
    for _ in 0..depth {
        root = graph.add(ENode::new(constructor("Wrap"), vec![root]));
    }
    if redex {
        root = graph.add(ENode::new(constructor("Add"), vec![zero, root]));
    }
    if let Some(outer) = outer {
        root = graph.add(ENode::new(constructor(outer), vec![root]));
    }
    match SemanticTransitionInput::admit(graph, root, input_limits(), || false) {
        SemanticInputDecision::Proven(input) => input,
        _ => panic!("small declared ground fixture must admit"),
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    #[test]
    fn checked_cost_premise_derived_rhs_and_grade_share_the_completed_substitution(
        internal_leaf in any::<bool>(),
        depth in 0usize..=5,
        equation_count in 0usize..=3,
        declaration_rotation in 0usize..8,
        reverse_variables in any::<bool>(),
        reverse_variable_nodes in any::<bool>(),
        reverse_rewrites in any::<bool>(),
        reverse_grade_rows in any::<bool>(),
    ) {
        let (language, source, target) = premise_grade_fixture(
            equation_count,
            declaration_rotation,
            reverse_variables,
            reverse_variable_nodes,
            reverse_rewrites,
            reverse_grade_rows,
        );
        language.validate().expect("premise-bound RHS and grade are source-valid");
        let admission = TheoryImageAdmissionLimits::default();
        let image = compile_theory_semantic_image(&language, admission).unwrap();
        let cost = mettail_grammar_core::CostImageV1::compile(&language, &image, admission)
            .unwrap()
            .expect("costed fixture");
        let verified = cost.verified(&language, &image, admission).unwrap();
        let matcher = SemanticTransitionMatcher::restore(&image).unwrap();
        let rights = LanguageRights::from_rights([LanguageRight::Reduce]);
        let limits = normalization_limits();
        let program = image.rules.iter().find(|rule| rule.name == "premise-grade-step").unwrap();
        let child = image.rules.iter().find(|rule| rule.name == "add-zero").unwrap();
        let source_index = language.theory.rewrites.iter()
            .position(|rule| rule.name == "premise-grade-step").unwrap();
        prop_assert_eq!(program.origin, TheoryRuleOriginV1::Rewrite { source: source_index as u32 });
        prop_assert_eq!(program.id.0 as usize, 2 * equation_count + source_index);
        prop_assert_eq!(image.actions[0].transitions.as_slice(), &[program.id]);
        prop_assert_eq!(verified.grade_root(program.id), Some(TheoryTermId(3)));

        let expected_output = fixture_input(&language, internal_leaf, depth, false, None);
        let expected_grade = fixture_input(&language, internal_leaf, depth, false, Some("SigOfExpr"));
        let initial_binding_grade = fixture_input(&language, internal_leaf, depth, true, Some("SigOfExpr"));
        prop_assert_ne!(expected_grade.exact_key(), initial_binding_grade.exact_key());
        let successful_input = || fixture_input(&language, internal_leaf, depth, true, Some("Wrap"));
        let expected_input = successful_input().exact_key().as_bytes().to_vec();
        let expected_premises = vec![SemanticPremiseReceipt::Transition {
            rule: program.id,
            premise: program.premise_roots[0],
            child_rule: child.id,
        }];
        let expected_resource = SemanticResourceReceipt::Checked {
            grade_sort: verified.grade_sort(),
            grade: expected_grade.exact_key().as_bytes().to_vec(),
            cost_image_fingerprint: verified.fingerprint(),
        };
        let (decision, charged) = matcher.execute_costed_action_accounted(
            SemanticActionExecutionRequest {
                image: &image,
                action: image.actions[0].id,
                granted_rights: &rights,
                input: successful_input(),
                limits,
            },
            verified,
            || false,
        );
        let SemanticTransitionDecision::Proven(proven) = decision else {
            return Err(TestCaseError::fail("the completed premise must supply both RHS and grade"));
        };
        prop_assert_eq!(proven.work, charged);
        prop_assert_eq!(proven.transitions.len(), 1);
        let transition = &proven.transitions[0];
        prop_assert_eq!(transition.receipt.rule, program.id);
        prop_assert_eq!(&transition.receipt.input, &expected_input);
        prop_assert_eq!(transition.receipt.output.as_slice(), expected_output.exact_key().as_bytes());
        prop_assert_eq!(&transition.receipt.premises, &expected_premises);
        prop_assert_eq!(&transition.receipt.resource, &expected_resource);
        prop_assert_eq!(transition.substitution.iter().len(), 2);
        let target_root = transition.substitution.get(target).expect("premise-derived binding");
        let source_root = transition.substitution.get(source).expect("initial matcher binding");
        prop_assert!(proven.egraph().equiv(transition.output, target_root));
        prop_assert!(!proven.egraph().equiv(source_root, target_root));
        let (retained, _) = proven.admit_grade_at(0, input_limits(), || false);
        let SemanticInputDecision::Proven(retained) = retained else {
            return Err(TestCaseError::fail("source grade must retain its actual checked graph root"));
        };
        prop_assert_eq!(retained.exact_key(), expected_grade.exact_key());

        let relation_sort = image.actions[0].codomain;
        let (decision, charged) = matcher.execute_costed_rewrite_step_roster_accounted(
            SemanticRelationExecutionRequest {
                image: &image,
                relation_sort,
                granted_rights: &rights,
                input: successful_input(),
                limits,
            },
            verified,
            || false,
        );
        let SemanticTransitionDecision::ProvenSteps(roster) = decision else {
            return Err(TestCaseError::fail("the complete roster must retain the same source-bound grade"));
        };
        prop_assert_eq!(roster.work, charged);
        prop_assert_eq!(&roster.input, &expected_input);
        prop_assert_eq!(roster.occurrences.len(), 1);
        let occurrence = &roster.occurrences[0];
        prop_assert_eq!(occurrence.ordinal, 0);
        prop_assert_eq!(occurrence.receipt.rule, program.id);
        prop_assert_eq!(occurrence.receipt.after.as_slice(), expected_output.exact_key().as_bytes());
        prop_assert_eq!(&occurrence.receipt.premises, &expected_premises);
        prop_assert_eq!(&occurrence.resource, &expected_resource);
        let (retained, _) = roster.admit_grade_at(0, input_limits(), || false);
        let SemanticInputDecision::Proven(retained) = retained else {
            return Err(TestCaseError::fail("roster must retain the completed grade root"));
        };
        prop_assert_eq!(retained.exact_key(), expected_grade.exact_key());

        // The outer LHS still matches, but its bound source is an irreducible
        // leaf. Neither the named action nor the exhaustive roster can publish
        // an RHS or grade made from the absent Derived binding.
        let unmet_input = || fixture_input(&language, internal_leaf, 0, false, Some("Wrap"));
        let (decision, charged) = matcher.execute_costed_action_accounted(
            SemanticActionExecutionRequest {
                image: &image,
                action: image.actions[0].id,
                granted_rights: &rights,
                input: unmet_input(),
                limits,
            },
            verified,
            || false,
        );
        prop_assert!(matches!(decision, SemanticTransitionDecision::Refuted(SemanticMatchRefutation::PremiseRefuted)));
        prop_assert!(charged > 0 && charged <= limits.work);
        let (decision, charged) = matcher.execute_costed_rewrite_step_roster_accounted(
            SemanticRelationExecutionRequest {
                image: &image,
                relation_sort,
                granted_rights: &rights,
                input: unmet_input(),
                limits,
            },
            verified,
            || false,
        );
        let SemanticTransitionDecision::ProvenSteps(roster) = decision else {
            return Err(TestCaseError::fail("an unmet premise has a checked empty roster"));
        };
        prop_assert_eq!(roster.work, charged);
        prop_assert!(roster.occurrences.is_empty());
    }
}
