//! Generated correspondence for private child frames and saved ForAll scopes.

use super::*;
use crate::{ProvenSemanticTransitions, SemanticPremiseReceipt};
use dovetail::key::FramedSemanticOperator;

// The same textual names and numeric slots intentionally recur in different
// frames. Only the source arena and frame-local binding own their meanings.
fn declarations(
    roles: &[(&str, TheoryVariableRoleV1)],
    rotation: usize,
    salt: u16,
) -> (Vec<TheoryVariableV1>, Vec<TheoryVariableId>) {
    let ids = (0..roles.len())
        .map(|index| TheoryVariableId(((index + rotation) % roles.len()) as u32))
        .collect::<Vec<_>>();
    let mut variables = roles
        .iter()
        .zip(&ids)
        .map(|((sort, role), &id)| TheoryVariableV1 {
            id,
            name: format!("renamed_{salt}_{}", id.0),
            sort: (*sort).into(),
            role: *role,
        })
        .collect::<Vec<_>>();
    variables.sort_by_key(|variable| variable.id);
    (variables, ids)
}

fn transition(source: TheoryVariableId, target: TheoryVariableId) -> TheoryPremiseNodeV1 {
    TheoryPremiseNodeV1 {
        form: TheoryPremiseFormV1::Transition { source, target },
    }
}

fn compile_scope_fixture(language: &LanguageCoreV1) -> TheorySemanticImageV1 {
    language
        .validate()
        .expect("generated scoped source must validate unchanged");
    compile_theory_semantic_image(language, TheoryImageAdmissionLimits::default())
        .expect("compile the existing frame machine's source image")
}

fn rule_id(image: &TheorySemanticImageV1, name: &str) -> TheoryRuleProgramId {
    image
        .rules
        .iter()
        .find(|rule| rule.name == name)
        .unwrap()
        .id
}

fn completed(
    image: &TheorySemanticImageV1,
    input: SemanticTransitionInput,
) -> ProvenSemanticTransitions {
    let matcher = SemanticTransitionMatcher::restore(image).unwrap();
    let rights = LanguageRights::from_rights([LanguageRight::Reduce]);
    let (decision, work) = matcher.execute_action_accounted(
        SemanticActionExecutionRequest {
            image,
            action: image.actions[0].id,
            granted_rights: &rights,
            input,
            limits: normalization_limits(),
        },
        || false,
    );
    match decision {
        SemanticTransitionDecision::Proven(proven) => {
            assert_eq!(proven.work, work);
            assert_eq!(proven.transitions.len(), 1);
            proven
        },
        SemanticTransitionDecision::Undetermined { reason, .. } => {
            panic!("scoped execution: {reason:?}")
        },
        SemanticTransitionDecision::Refuted(reason) => panic!("scoped execution: {reason:?}"),
        _ => panic!("named action must return its own completed frame"),
    }
}

fn assert_unpublished(image: &TheorySemanticImageV1, input: impl Fn() -> SemanticTransitionInput) {
    let matcher = SemanticTransitionMatcher::restore(image).unwrap();
    let rights = LanguageRights::from_rights([LanguageRight::Reduce]);
    assert!(matches!(
        matcher.execute_action(
            SemanticActionExecutionRequest {
                image,
                action: image.actions[0].id,
                granted_rights: &rights,
                input: input(),
                limits: normalization_limits(),
            },
            || false,
        ),
        SemanticTransitionDecision::Refuted(SemanticMatchRefutation::PremiseRefuted)
    ));
    let (decision, work) = matcher.execute_rewrite_step_roster_accounted(
        SemanticRelationExecutionRequest {
            image,
            relation_sort: image.actions[0].codomain,
            granted_rights: &rights,
            input: input(),
            limits: normalization_limits(),
        },
        || false,
    );
    let SemanticTransitionDecision::ProvenSteps(roster) = decision else {
        panic!("an exhaustively refuted scoped branch must have an empty roster")
    };
    assert_eq!(roster.work, work);
    assert!(roster.occurrences.is_empty());
}

// Ground fixture construction only: no matching, substitution, or evaluation.
struct Ground {
    graph: EGraph<FramedSemanticOperator>,
    zero: EClassId,
}

impl Ground {
    fn new() -> Self {
        let mut graph = EGraph::new();
        let zero = graph.add(ENode::leaf(theory_operator_to_machine(
            &TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
        )));
        Self { graph, zero }
    }

    fn constructor(&mut self, id: u32, children: Vec<EClassId>) -> EClassId {
        self.graph.add(ENode::new(
            theory_operator_to_machine(&TheoryImageOperatorV1::Constructor(TheoryConstructorId(
                id,
            ))),
            children,
        ))
    }

    fn wraps(&mut self, depth: usize) -> EClassId {
        let mut root = self.zero;
        for _ in 0..depth {
            root = self.constructor(1, vec![root]);
        }
        root
    }

    fn sums(&mut self, depth: usize) -> EClassId {
        let mut root = self.zero;
        for _ in 0..depth {
            root = self.constructor(2, vec![root, self.zero]);
        }
        root
    }

    fn list(&mut self, children: Vec<EClassId>) -> EClassId {
        self.graph.add(ENode::new(
            theory_operator_to_machine(&TheoryImageOperatorV1::Collection {
                sort: TheorySortId(1),
                element: TheorySortId(0),
                kind: CollectionKind::List,
            }),
            children,
        ))
    }

    fn admit(self, root: EClassId) -> SemanticTransitionInput {
        match SemanticTransitionInput::admit(
            self.graph,
            root,
            SemanticInputLimits {
                work: 20_000,
                nodes: 256,
                bytes: 64 * 1024,
            },
            || false,
        ) {
            SemanticInputDecision::Proven(input) => input,
            _ => panic!("small ground scoped fixture must admit"),
        }
    }
}

fn private_child_fixture(
    parent_rotation: usize,
    child_rotation: usize,
    salt: u16,
) -> (LanguageCoreV1, Vec<TheoryVariableId>) {
    use TheoryVariableRoleV1::{Derived, Input};
    let mut language = fixture();
    let (variables, child) = declarations(
        &[
            ("Expr", Input),
            ("Expr", Input),
            ("Expr", Input),
            ("Expr", Derived),
            ("Expr", Derived),
        ],
        child_rotation,
        salt,
    );
    // Child: Wrap(Add(local, Add(source, extra))). Both transitions must
    // finish; the scratch result is private and deliberately absent from RHS.
    language.theory.rewrites.push(TheoryRewriteV1 {
        name: "private-child".into(),
        arena: TheoryRuleArenaV1 {
            variables,
            terms: vec![
                term_variable(child[0].0),
                term_variable(child[1].0),
                term_variable(child[2].0),
                term_variable(child[3].0),
                term_constructor("Add", vec![TheoryTermId(0), TheoryTermId(2)]),
                term_constructor("Add", vec![TheoryTermId(1), TheoryTermId(4)]),
                term_constructor("Wrap", vec![TheoryTermId(5)]),
                term_constructor("Add", vec![TheoryTermId(3), TheoryTermId(1)]),
            ],
            premises: vec![transition(child[0], child[3]), transition(child[2], child[4])],
            premise_roots: vec![TheoryPremiseId(0), TheoryPremiseId(1)],
        },
        left: TheoryTermId(6),
        right: TheoryTermId(7),
    });
    let (variables, parent) =
        declarations(&[("Expr", Input), ("Expr", Input), ("Expr", Derived)], parent_rotation, salt);
    language.theory.rewrites.push(TheoryRewriteV1 {
        name: "private-parent".into(),
        arena: TheoryRuleArenaV1 {
            variables,
            terms: vec![
                term_variable(parent[0].0),
                term_variable(parent[1].0),
                term_variable(parent[2].0),
                term_constructor("Wrap", vec![TheoryTermId(0)]),
                term_constructor("Add", vec![TheoryTermId(1), TheoryTermId(3)]),
                term_constructor("Add", vec![TheoryTermId(0), TheoryTermId(1)]),
                term_constructor("Add", vec![TheoryTermId(2), TheoryTermId(5)]),
            ],
            premises: vec![transition(parent[0], parent[2])],
            premise_roots: vec![TheoryPremiseId(0)],
        },
        left: TheoryTermId(4),
        right: TheoryTermId(6),
    });
    language.theory.actions[0].transition = TheoryRuleReferenceV1::Rewrite("private-parent".into());
    (language, parent)
}

fn private_child_input(
    result_depth: usize,
    kept_depth: usize,
    local_depth: usize,
    extra_depth: usize,
    fail_later: bool,
    expected: bool,
) -> SemanticTransitionInput {
    let mut ground = Ground::new();
    let result = ground.sums(result_depth);
    let kept = ground.wraps(kept_depth + 1);
    let local = ground.wraps(local_depth + 1);
    let scratch = ground.sums(extra_depth + 1);
    let source = ground.constructor(2, vec![ground.zero, result]);
    let extra = if fail_later {
        ground.wraps(1)
    } else {
        ground.constructor(2, vec![ground.zero, scratch])
    };
    let source_extra = ground.constructor(2, vec![source, extra]);
    let local_pair = ground.constructor(2, vec![local, source_extra]);
    let child = ground.constructor(1, vec![local_pair]);
    let root = if expected {
        let child_output = ground.constructor(2, vec![result, local]);
        let retained = ground.constructor(2, vec![child, kept]);
        ground.constructor(2, vec![child_output, retained])
    } else {
        let wrapped_child = ground.constructor(1, vec![child]);
        ground.constructor(2, vec![kept, wrapped_child])
    };
    ground.admit(root)
}

fn forall_derived_fixture(rotation: usize, salt: u16) -> (LanguageCoreV1, Vec<TheoryVariableId>) {
    use TheoryVariableRoleV1::{Derived, Input, Quantified, Remainder};
    let mut language = fixture();
    language.theory.sorts.push(TheorySortV1 {
        name: "ListExpr".into(),
        kind: TheorySortKindV1::Collection {
            kind: CollectionKind::List,
            key: None,
            element: "Expr".into(),
        },
    });
    let (variables, slots) = declarations(
        &[
            ("Expr", Input),
            ("ListExpr", Remainder),
            ("Expr", Quantified),
            ("Expr", Derived),
        ],
        rotation,
        salt,
    );
    language.theory.rewrites.push(TheoryRewriteV1 {
        name: "forall-then-outer".into(),
        arena: TheoryRuleArenaV1 {
            variables,
            terms: vec![
                term_variable(slots[0].0),
                TheoryTermNodeV1 {
                    sort: "ListExpr".into(),
                    form: TheoryTermFormV1::Collection {
                        elements: vec![TheoryTermId(0)],
                        remainder: Some(slots[1]),
                        pathmap_mode: None,
                    },
                },
                term_variable(slots[3].0),
                TheoryTermNodeV1 {
                    sort: "ListExpr".into(),
                    form: TheoryTermFormV1::Collection {
                        elements: vec![TheoryTermId(0), TheoryTermId(2)],
                        remainder: Some(slots[1]),
                        pathmap_mode: None,
                    },
                },
            ],
            premises: vec![
                transition(slots[2], slots[3]),
                TheoryPremiseNodeV1 {
                    form: TheoryPremiseFormV1::ForAll {
                        collection: slots[1],
                        parameter: slots[2],
                        body: TheoryPremiseId(0),
                    },
                },
                transition(slots[0], slots[3]),
            ],
            premise_roots: vec![TheoryPremiseId(1), TheoryPremiseId(2)],
        },
        left: TheoryTermId(1),
        right: TheoryTermId(3),
    });
    let action = &mut language.theory.actions[0];
    action.domain = vec!["ListExpr".into()];
    action.codomain = "ListExpr".into();
    action.grade = "ListExpr".into();
    action.transition = TheoryRuleReferenceV1::Rewrite("forall-then-outer".into());
    (language, slots)
}

fn forall_input(
    count: usize,
    offset: usize,
    head_depth: usize,
    failing_element: Option<usize>,
    failing_outer: bool,
    expected: bool,
) -> SemanticTransitionInput {
    let mut ground = Ground::new();
    let head_result = ground.wraps(head_depth + 1);
    let head = if failing_outer {
        ground.zero
    } else {
        ground.constructor(2, vec![ground.zero, head_result])
    };
    let mut elements = vec![head];
    if expected {
        elements.push(head_result);
    }
    for index in 0..count {
        let result = ground.sums(offset + index + 1);
        let element = if failing_element == Some(index) {
            ground.zero
        } else {
            ground.constructor(2, vec![ground.zero, result])
        };
        elements.push(element);
    }
    let root = ground.list(elements);
    ground.admit(root)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn generated_nested_return_keeps_child_derived_and_local_bindings_private(
        parent_rotation in 0usize..3, child_rotation in 0usize..5, salt in any::<u16>(),
        result_depth in 0usize..4, kept_depth in 0usize..4,
        local_depth in 0usize..4, extra_depth in 0usize..4,
    ) {
        let (language, slots) = private_child_fixture(parent_rotation, child_rotation, salt);
        let image = compile_scope_fixture(&language);
        let expected = private_child_input(result_depth, kept_depth, local_depth, extra_depth, false, true);
        let proven = completed(&image, private_child_input(result_depth, kept_depth, local_depth, extra_depth, false, false));
        let output = &proven.transitions[0];
        prop_assert_eq!(output.receipt.output.as_slice(), expected.exact_key().as_bytes());
        prop_assert_eq!(output.substitution.iter().map(|(id, _)| id).collect::<Vec<_>>(),
            vec![TheoryVariableId(0), TheoryVariableId(1), TheoryVariableId(2)]);
        for child_only in [TheoryVariableId(3), TheoryVariableId(4)] {
            prop_assert_eq!(output.substitution.get(child_only), None);
        }
        // Every parent value is present in RHS, so exact output equality also
        // checks that colliding child slots did not replace either input.
        let [root] = proven.egraph().nodes(output.output) else {
            return Err(TestCaseError::fail("one exact result node"));
        };
        let [retained] = proven.egraph().nodes(root.children[1]) else {
            return Err(TestCaseError::fail("one exact retained-input pair"));
        };
        for (slot, value) in [(slots[2], root.children[0]), (slots[0], retained.children[0]), (slots[1], retained.children[1])] {
            prop_assert!(proven.egraph().equiv(output.substitution.get(slot).unwrap(), value));
        }
        let parent = rule_id(&image, "private-parent");
        let child = rule_id(&image, "private-child");
        let base = rule_id(&image, "add-zero");
        prop_assert_eq!(output.receipt.rule, parent);
        prop_assert_eq!(&output.receipt.premises, &vec![
            SemanticPremiseReceipt::Transition { rule: child, premise: 0, child_rule: base },
            SemanticPremiseReceipt::Transition { rule: child, premise: 1, child_rule: base },
            SemanticPremiseReceipt::Transition { rule: parent, premise: 0, child_rule: child },
        ]);
        // First child premise succeeds and binds its private target; only the
        // later scratch premise fails. No parent result or prefix is published.
        assert_unpublished(&image, || private_child_input(result_depth, kept_depth, local_depth, extra_depth, true, false));
    }

    #[test]
    fn generated_forall_restores_derived_bindings_before_each_element_and_outer_premise(
        rotation in 0usize..4, salt in any::<u16>(), count in 2usize..=4,
        offset in 0usize..3, head_depth in 0usize..4, failure_seed in any::<usize>(),
    ) {
        let (language, slots) = forall_derived_fixture(rotation, salt);
        let image = compile_scope_fixture(&language);
        let expected = forall_input(count, offset, head_depth, None, false, true);
        let proven = completed(&image, forall_input(count, offset, head_depth, None, false, false));
        let output = &proven.transitions[0];
        prop_assert_eq!(output.receipt.output.as_slice(), expected.exact_key().as_bytes());
        prop_assert_eq!(output.substitution.iter().len(), 3);
        prop_assert_eq!(output.substitution.get(slots[2]), None);
        let [root] = proven.egraph().nodes(output.output) else {
            return Err(TestCaseError::fail("one exact list result"));
        };
        prop_assert_eq!(root.children.len(), count + 2);
        prop_assert!(proven.egraph().equiv(output.substitution.get(slots[0]).unwrap(), root.children[0]));
        prop_assert!(proven.egraph().equiv(output.substitution.get(slots[3]).unwrap(), root.children[1]));
        let [tail] = proven.egraph().nodes(output.substitution.get(slots[1]).unwrap()) else {
            return Err(TestCaseError::fail("the saved outer remainder survives"));
        };
        prop_assert_eq!(&tail.children, &root.children[2..]);
        let parent = rule_id(&image, "forall-then-outer");
        let base = rule_id(&image, "add-zero");
        let mut premises = vec![SemanticPremiseReceipt::Transition { rule: parent, premise: 0, child_rule: base }; count];
        premises.push(SemanticPremiseReceipt::ForAll { rule: parent, premise: 1, elements: count as u32 });
        premises.push(SemanticPremiseReceipt::Transition { rule: parent, premise: 2, child_rule: base });
        prop_assert_eq!(output.receipt.rule, parent);
        prop_assert_eq!(&output.receipt.premises, &premises);
        // Distinct body results must be forgotten: the SAME Derived slot is
        // fresh in every element, and again for the later outer transition.
        let failing = 1 + failure_seed % (count - 1);
        assert_unpublished(&image, || forall_input(count, offset, head_depth, Some(failing), false, false));
        assert_unpublished(&image, || forall_input(count, offset, head_depth, None, true, false));
    }
}
