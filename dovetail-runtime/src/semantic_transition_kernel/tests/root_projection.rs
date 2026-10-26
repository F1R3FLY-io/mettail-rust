use super::*;
use mettail_grammar_core::{TheoryImageVariableV1, TheoryVariableRoleV1};
use proptest::prelude::*;

fn evaluator<'a, C: FnMut() -> bool>(
    image: &'a TheorySemanticImageV1,
    egraph: &'a EGraph<FramedSemanticOperator>,
    is_cancelled: C,
) -> HornEvaluator<'a, C> {
    HornEvaluator {
        image,
        egraph,
        work: 0,
        work_limit: 100_000,
        ground_key_nodes: usize::MAX,
        ground_key_bytes: usize::MAX,
        ground_key_limit_reason: SemanticMatchUndetermined::WorkBudgetExhausted,
        is_cancelled,
        synthetic_terms: Vec::new(),
        lexical_scopes: Vec::new(),
        collection_states: Vec::new(),
        comprehension_states: Vec::new(),
        derived_collections: Vec::new(),
        next_activation: 0,
    }
}

fn declaration(id: u32, role: u8) -> TheoryImageVariableV1 {
    TheoryImageVariableV1 {
        id: TheoryVariableId(id),
        sort: TheorySortId(1),
        role: match role % 5 {
            0 => TheoryVariableRoleV1::Input,
            1 => TheoryVariableRoleV1::Binder,
            2 => TheoryVariableRoleV1::Derived,
            3 => TheoryVariableRoleV1::Remainder,
            _ => TheoryVariableRoleV1::Quantified,
        },
    }
}

fn integer(graph: &mut EGraph<FramedSemanticOperator>, value: i64) -> HornTermRef {
    let class = add(
        graph,
        TheoryImageOperatorV1::Literal {
            sort: TheorySortId(1),
            value: TheoryLiteralV1::Integer(i128::from(value)),
        },
        vec![],
    );
    HornTermRef::Ground { class, sort: TheorySortId(1) }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn root_projection_matches_chronological_values_and_declaration_order(
        roles in proptest::collection::vec(0u8..5, 0..12),
        updates in proptest::collection::vec((0u8..3, 0u32..16, any::<i16>()), 0..64),
        root in 0u64..100,
    ) {
        let image = signature_image();
        let mut rule = comprehension_image().rules.remove(0);
        rule.variables = roles.iter().enumerate().map(|(id, role)| declaration(id as u32, *role)).collect();
        let mut graph = EGraph::new();
        let mut history = Vec::new();
        let mut expected_by_id = BTreeMap::new();
        for (index, (offset, variable, value)) in updates.into_iter().enumerate() {
            let term = integer(&mut graph, i64::from(value));
            let activation = root + u64::from(offset);
            let observed = if index % 2 == 0 {
                let alias = ScopedClauseVariable { activation: root + 100, variable: TheoryVariableId(100 + index as u32) };
                history.push((alias, term));
                HornTermRef::Variable { variable: alias, sort: TheorySortId(1) }
            } else { term };
            history.push((ScopedClauseVariable { activation, variable: TheoryVariableId(variable) }, observed));
            if activation == root { expected_by_id.insert(TheoryVariableId(variable), term); }
        }
        let expected = rule.variables.iter().filter_map(|declaration| expected_by_id.get(&declaration.id).map(|term| (declaration.id, *term))).collect::<Vec<_>>();
        let mut evaluator = evaluator(&image, &graph, || false);
        let actual = evaluator.project_transition_substitution(&rule, root, &history).unwrap();
        prop_assert_eq!(&actual, &expected);
        prop_assert_eq!(actual.iter().map(|(id, _)| *id).collect::<BTreeSet<_>>().len(), actual.len());
        for declaration in &mut rule.variables { declaration.role = TheoryVariableRoleV1::Binder; }
        prop_assert_eq!(evaluator.project_transition_substitution(&rule, root, &history).unwrap(), expected);
    }

    #[test]
    fn root_projection_keeps_bound_binders_and_omits_fresh_lexical_bindings(
        count in 1u32..12, root_seed in 0u64..100, salt in any::<i16>(),
    ) {
        let image = signature_image();
        let mut rule = comprehension_image().rules.remove(0);
        rule.variables = (0..count).map(|id| declaration(id, 1)).collect();
        let mut graph = EGraph::new();
        let root_term = integer(&mut graph, i64::from(salt));
        let local_term = integer(&mut graph, i64::from(salt) + 1);
        let mut evaluator = evaluator(&image, &graph, || false);
        evaluator.next_activation = root_seed;
        let root = evaluator.fresh_activation().unwrap();
        let parameters = rule.variables.iter().map(|declaration| declaration.id).collect::<Vec<_>>();
        let (scope, first) = evaluator.push_lexical_scope(None, &parameters).unwrap();
        let (nested_scope, second) = evaluator.push_lexical_scope(Some(scope), &parameters).unwrap();
        let mut history = parameters.iter().step_by(2).map(|variable| (ScopedClauseVariable { activation: root, variable: *variable }, root_term)).collect::<Vec<_>>();
        let expected = history.iter().map(|(key, term)| (key.variable, *term)).collect::<Vec<_>>();
        let locals = first.iter().chain(&second).map(|key| (*key, local_term)).collect::<Vec<_>>();
        prop_assert!(locals.iter().all(|(key, _)| key.activation != root));
        prop_assert_ne!(first[0].activation, second[0].activation);
        for (index, parameter) in parameters.iter().enumerate() {
            prop_assert_eq!(evaluator.scoped_clause_variable(root, Some(nested_scope), *parameter).unwrap(), second[index]);
            prop_assert_eq!(evaluator.scoped_clause_variable(root, Some(scope), *parameter).unwrap(), first[index]);
            prop_assert_eq!(evaluator.scoped_clause_variable(root, None, *parameter).unwrap(), ScopedClauseVariable { activation: root, variable: *parameter });
        }
        let free = TheoryVariableId(count);
        prop_assert_eq!(evaluator.scoped_clause_variable(root, Some(nested_scope), free).unwrap(), ScopedClauseVariable { activation: root, variable: free });
        history.extend_from_slice(&locals);
        prop_assert_eq!(evaluator.project_transition_substitution(&rule, root, &history).unwrap(), expected);
        prop_assert!(evaluator.project_transition_substitution(&rule, root, &locals).unwrap().is_empty());
    }

    #[test]
    fn root_projection_grounding_failure_returns_no_partial_result(count in 1u32..12, selected in any::<u8>()) {
        let failure = u32::from(selected) % count;
        let image = signature_image();
        let mut rule = comprehension_image().rules.remove(0);
        rule.variables = (0..count).map(|id| declaration(id, (id % 5) as u8)).collect();
        let mut graph = EGraph::new();
        let term = integer(&mut graph, 7);
        let invalid = HornTermRef::Variable { variable: ScopedClauseVariable { activation: 0, variable: TheoryVariableId(count) }, sort: TheorySortId(1) };
        let history = (0..count).map(|id| (ScopedClauseVariable { activation: 0, variable: TheoryVariableId(id) }, if id == failure { invalid } else { term })).collect::<Vec<_>>();
        let before = history.clone();
        let mut evaluator = evaluator(&image, &graph, || false);
        prop_assert_eq!(evaluator.project_transition_substitution(&rule, 0, &history), Err(SemanticMatchUndetermined::InvalidImageEvidence));
        prop_assert_eq!(&history, &before);
        rule.variables.truncate(failure as usize);
        prop_assert_eq!(evaluator.project_transition_substitution(&rule, 0, &history).unwrap().len(), failure as usize);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(16))]

    #[test]
    fn root_projection_refuses_each_work_and_cancellation_cut(count in 1u32..8) {
        let image = signature_image();
        let mut rule = comprehension_image().rules.remove(0);
        rule.variables = (0..count).map(|id| declaration(id, (id % 5) as u8)).collect();
        let mut graph = EGraph::new();
        let term = integer(&mut graph, 7);
        let history = (0..count).map(|id| (ScopedClauseVariable { activation: 0, variable: TheoryVariableId(id) }, term)).collect::<Vec<_>>();
        let before = history.clone();
        let mut callback_count = 0;
        let mut complete = evaluator(&image, &graph, || { callback_count += 1; false });
        let expected = complete.project_transition_substitution(&rule, 0, &history).unwrap();
        let total_work = complete.work;
        drop(complete);
        for cut in 0..=total_work {
            let mut limited = evaluator(&image, &graph, || false);
            limited.work_limit = cut;
            let result = limited.project_transition_substitution(&rule, 0, &history);
            if cut == total_work { prop_assert_eq!(result, Ok(expected.clone())); }
            else { prop_assert_eq!(result, Err(SemanticMatchUndetermined::WorkBudgetExhausted)); }
        }
        for cut in 0..=callback_count {
            let mut calls = 0;
            let mut cancelled = evaluator(&image, &graph, || { let stop = calls == cut; calls += 1; stop });
            let result = cancelled.project_transition_substitution(&rule, 0, &history);
            if cut == callback_count { prop_assert_eq!(result, Ok(expected.clone())); }
            else { prop_assert_eq!(result, Err(SemanticMatchUndetermined::Cancelled)); }
        }
        prop_assert_eq!(history, before);
    }
}
