use super::*;
use crate::wpda_rule_analysis::authored::AuthoredRuleReader;
use crate::wpda_rule_analysis::binder::rule::BinderRuleReader;
use crate::wpda_rule_analysis::synthetic::{
    build_per_category_rules, CollectionRecipe, SynthesisAdapter, TypeInput,
};
use mettail_grammar_core::TermParamReader;

// Recipes come from the unchanged shared builder, not a test implementation
// of synthesis. This adapter supplies only two small source observations.
struct RecipeCollector;

impl SynthesisAdapter for RecipeCollector {
    type SourceUser = ();
    type SourceType = &'static str;
    type RulePayload = SyntheticRule<CollectionKind>;
    type CollectionKind = CollectionKind;

    fn clone_user(&mut self, _: &()) -> Self::RulePayload {
        panic!("fixture has no user rules")
    }
    fn normalize_user(&mut self, _: &mut Self::RulePayload) {
        panic!("fixture has no user rules")
    }
    fn first_item_is_var(&mut self, rule: &Self::RulePayload) -> bool {
        matches!(
            rule.items.first(),
            Some(LegacyAtomicItem::NonTerminal { kind: LegacyAtomicKind::Var, .. })
        )
    }
    fn materialize_synthetic(&mut self, rule: Self::RulePayload) -> Self::RulePayload {
        rule
    }
    fn has_literal_block(&mut self, _: &&'static str) -> bool {
        false
    }
    fn literal_label(&mut self, _: &&'static str) -> String {
        "NumLit".into()
    }
    fn collection(&mut self, _: &&'static str) -> CollectionRecipe<CollectionKind> {
        CollectionRecipe {
            kind: CollectionKind::List,
            label: "ListLit".into(),
            element_category: "Expr".into(),
            open: "list(".into(),
            close: ")".into(),
            separator: ",".into(),
        }
    }
    fn var_label(&mut self, source: &&'static str) -> String {
        format!("{source}Var")
    }
    fn declares_binder(&mut self) -> bool {
        true
    }
}

fn recipes() -> Vec<SyntheticRule<CollectionKind>> {
    let expr = "Expr";
    let list = "List";
    build_per_category_rules(
        &[expr.into(), list.into()],
        &[],
        &[
            TypeInput {
                name: expr.into(),
                is_data: false,
                has_native: true,
                has_collection: false,
                source: &expr,
            },
            TypeInput {
                name: list.into(),
                is_data: false,
                has_native: true,
                has_collection: true,
                source: &list,
            },
        ],
        CollectionKind::List,
        &mut RecipeCollector,
    )
    .into_iter()
    .flatten()
    .collect()
}

fn recipe(label: &str) -> SyntheticRule<CollectionKind> {
    recipes()
        .into_iter()
        .find(|rule| rule.label == label)
        .expect("fixture builder emits the requested original recipe")
}

fn seed() -> AuthoredRuleStore {
    let mut store = AuthoredRuleStore::new();
    for (spelling, equality_class) in [("Expr", 3), ("f", 37), ("x", 50), ("p", 91), ("elems", 101)]
    {
        store
            .try_push(AuthoredNode::Name(AuthoredName {
                spelling: spelling.into(),
                equality_class,
            }))
            .expect("source names are valid arena nodes");
    }
    store
}

fn rule(store: &AuthoredRuleStore, id: AuthoredRuleId) -> &AuthoredRule {
    match store.get(id.0) {
        Some(AuthoredNode::Rule(rule)) => rule,
        other => panic!("expected materialized Rule, found {other:?}"),
    }
}

fn parameter(store: &AuthoredRuleStore, rule_id: AuthoredRuleId, index: usize) -> &AuthoredParam {
    let id = rule(store, rule_id)
        .term_context
        .expect("generated context is present");
    let Some(AuthoredNode::Params(params)) = store.get(id.0) else {
        panic!("context handle points to Params")
    };
    match store.get(params[index].0) {
        Some(AuthoredNode::Param(param)) => param,
        other => panic!("expected Param, found {other:?}"),
    }
}

fn name_spelling(store: &AuthoredRuleStore, id: AuthoredNameId) -> &str {
    match store.get(id.0) {
        Some(AuthoredNode::Name(name)) => &name.spelling,
        other => panic!("expected retained Name, found {other:?}"),
    }
}

fn base_category(store: &AuthoredRuleStore, id: AuthoredTypeId) -> &str {
    match store.get(id.0) {
        Some(AuthoredNode::Type(AuthoredType::Base(name))) => name_spelling(store, *name),
        other => panic!("expected retained Base type, found {other:?}"),
    }
}

fn admitted(
    session: AuthoredNormalizationSession,
    recipe: SyntheticRule<CollectionKind>,
) -> (AuthoredNormalizationSession, AuthoredRuleId) {
    session
        .materialize_synthetic(recipe, |_| Ok::<_, ()>(()))
        .expect("original synthetic recipe materializes in the checked session")
}

#[test]
fn owned_synthetic_all_six_recipe_families_use_existing_reader_and_preserve_prefix() {
    let original = seed();
    let mut session = AuthoredNormalizationSession::new(original.clone());
    let mut outputs = Vec::new();
    for recipe in recipes() {
        let expected = (
            recipe.label.clone(),
            recipe.category.clone(),
            recipe.term_context.is_some(),
            recipe.syntax_pattern.is_some(),
        );
        let (next, id) = admitted(session, recipe);
        session = next;
        outputs.push((expected, id));
    }
    let store = session.store();
    store
        .validate()
        .expect("all synthesized children precede their owners");
    for index in 0..original.len() {
        assert_eq!(store.get(index as u32), original.get(index as u32));
    }
    assert_eq!(store.declarations(), original.declarations());
    assert_eq!(session.original_len, original.len());
    let reader = AuthoredRuleReader::new(store).expect("existing reader accepts generated store");
    for ((label, category, has_params, has_syntax), id) in &outputs {
        assert_eq!(reader.label(*id).to_string(), *label);
        assert_eq!(reader.category(*id).to_string(), *category);
        assert_eq!(reader.term_context(*id).is_some(), *has_params);
        assert_eq!(reader.syntax_pattern(*id).is_some(), *has_syntax);
    }
    let id = |label: &str| {
        outputs
            .iter()
            .find(|((name, _, _, _), _)| name == label)
            .map(|(_, id)| *id)
            .expect("all six original recipe families are present")
    };
    assert!(matches!(
        rule(store, id("NumLit")).items.as_slice(),
        [AuthoredLegacyItem::NonTerminal { kind: NonTerminalKind::Category, .. }]
    ));
    assert!(matches!(
        rule(store, id("ExprVar")).items.as_slice(),
        [AuthoredLegacyItem::NonTerminal { kind: NonTerminalKind::Var, .. }]
    ));
    for label in ["ListLit", "ApplyExpr", "MApplyExpr", "LamExpr"] {
        let context = reader
            .term_context(id(label))
            .expect("non-atomic recipe context present");
        assert!(reader.params_len(context) > 0);
    }
    for label in ["ListLit", "MApplyExpr"] {
        let syntax_id = reader
            .syntax_pattern(id(label))
            .expect("collection syntax is present");
        let Some(AuthoredNode::Syntax(syntax)) = store.get(syntax_id.0) else {
            panic!("syntax handle references its original sequence")
        };
        let operations: Vec<_> = syntax
            .iter()
            .filter_map(|item| match item {
                AuthoredSyntax::Op(id) => Some(id),
                _ => None,
            })
            .collect();
        assert_eq!(operations.len(), 1);
        assert!(matches!(store.get(operations[0].0), Some(AuthoredNode::Operation(
            AuthoredOperation::Sep { separator, source: None, .. }
        )) if separator == ","));
    }
    for index in 0..2 {
        let AuthoredParam::Simple { name, ty } = parameter(store, id("ApplyExpr"), index) else {
            panic!("Apply retains two simple parameters")
        };
        assert_eq!(*name, AuthoredNameId(if index == 0 { 1 } else { 2 }));
        assert_eq!(
            store.get(ty.0),
            Some(&AuthoredNode::Type(AuthoredType::Base(AuthoredNameId(0))))
        );
    }
    // Distinct home/domain observations catch accidental substitution that an
    // Expr/Expr application cannot detect. These are original builder recipes.
    for label in ["ApplyList", "MApplyList"] {
        let rule_id = id(label);
        assert_eq!(reader.category(rule_id).to_string(), "Expr");
        let AuthoredParam::Simple { name, ty } = parameter(store, rule_id, 0) else {
            panic!("cross-category application has a simple function parameter")
        };
        assert_eq!(name_spelling(store, *name), "f");
        assert_eq!(base_category(store, *ty), "Expr");
        let AuthoredParam::Simple { name, ty } = parameter(store, rule_id, 1) else {
            panic!("cross-category application has a simple argument parameter")
        };
        if label == "ApplyList" {
            assert_eq!(name_spelling(store, *name), "x");
            assert_eq!(base_category(store, *ty), "List");
        } else {
            assert_eq!(name_spelling(store, *name), "xs");
            let Some(AuthoredNode::Type(AuthoredType::Collection { kind, element })) =
                store.get(ty.0)
            else {
                panic!("MApplyList retains its collection argument type")
            };
            assert_eq!(*kind, CollectionKind::List);
            assert_eq!(base_category(store, *element), "List");
        }

        let syntax_id = rule(store, rule_id)
            .syntax_pattern
            .expect("cross-category application has original syntax");
        let Some(AuthoredNode::Syntax(syntax)) = store.get(syntax_id.0) else {
            panic!("application syntax handle references its ordered sequence")
        };
        let observed: Vec<_> = syntax
            .iter()
            .map(|item| match item {
                AuthoredSyntax::Literal(text) => ("literal", text.as_str(), ""),
                AuthoredSyntax::Param(name) => ("param", name_spelling(store, *name), ""),
                AuthoredSyntax::Op(operation) => match store.get(operation.0) {
                    Some(AuthoredNode::Operation(AuthoredOperation::Sep {
                        collection,
                        separator,
                        source: None,
                    })) => ("sep", name_spelling(store, *collection), separator.as_str()),
                    other => panic!("expected source-free application Sep, found {other:?}"),
                },
                other => panic!("unexpected application syntax observation: {other:?}"),
            })
            .collect();
        let expected = if label == "ApplyList" {
            vec![
                ("literal", "$list", ""),
                ("literal", "(", ""),
                ("param", "f", ""),
                ("literal", ",", ""),
                ("param", "x", ""),
                ("literal", ")", ""),
            ]
        } else {
            vec![
                ("literal", "$$list(", ""),
                ("param", "f", ""),
                ("literal", ",", ""),
                ("sep", "xs", ","),
                ("literal", ")", ""),
            ]
        };
        assert_eq!(observed, expected, "{label} retains complete syntax order");
    }
    let AuthoredParam::Simple { ty, .. } = parameter(store, id("ListLit"), 0) else {
        panic!("collection recipe has one simple parameter")
    };
    assert!(matches!(
        store.get(ty.0),
        Some(AuthoredNode::Type(AuthoredType::Collection { kind: CollectionKind::List, .. }))
    ));
    let AuthoredParam::Simple { ty, .. } = parameter(store, id("MApplyExpr"), 1) else {
        panic!("MApply has an xs collection parameter")
    };
    assert!(matches!(
        store.get(ty.0),
        Some(AuthoredNode::Type(AuthoredType::Collection { kind: CollectionKind::List, .. }))
    ));
    let AuthoredParam::Abstraction { binder, body, ty } = parameter(store, id("LamExpr"), 0) else {
        panic!("Lam has the original abstraction parameter")
    };
    assert_eq!((*binder, *body), (AuthoredNameId(2), AuthoredNameId(3)));
    let Some(AuthoredNode::Type(AuthoredType::Arrow { domain, codomain })) = store.get(ty.0) else {
        panic!("Lam retains both arrow children")
    };
    for child in [domain, codomain] {
        assert_eq!(
            store.get(child.0),
            Some(&AuthoredNode::Type(AuthoredType::Base(AuthoredNameId(0))))
        );
    }
}

#[test]
fn owned_synthetic_none_and_present_empty_sequences_remain_distinct() {
    for params in [false, true] {
        for syntax in [false, true] {
            let mut input = recipe("ExprVar");
            input.term_context = params.then(Vec::new);
            input.syntax_pattern = syntax.then(Vec::new);
            let mut sequence_nodes = Vec::new();
            let (session, id) = AuthoredNormalizationSession::new(seed())
                .materialize_synthetic(input, |event| {
                    if let AuthoredNormalizationEvent::Append(node) = event {
                        match node {
                            AuthoredNode::Params(items) => {
                                assert!(items.is_empty());
                                sequence_nodes.push("params");
                            },
                            AuthoredNode::Syntax(items) => {
                                assert!(items.is_empty());
                                sequence_nodes.push("syntax");
                            },
                            AuthoredNode::Rule(_) => sequence_nodes.push("rule"),
                            _ => {},
                        }
                    }
                    Ok::<_, ()>(())
                })
                .expect("presence fixture materializes");
            assert_eq!(rule(session.store(), id).term_context.is_some(), params);
            assert_eq!(rule(session.store(), id).syntax_pattern.is_some(), syntax);
            let mut expected = Vec::new();
            if params {
                expected.push("params");
            }
            if syntax {
                expected.push("syntax");
            }
            expected.push("rule");
            assert_eq!(sequence_nodes, expected);
        }
    }
}

#[test]
fn owned_synthetic_reuses_one_name_index_and_orders_abstraction_names_before_type_nodes() {
    let (session, _) = admitted(AuthoredNormalizationSession::new(seed()), recipe("ExprVar"));
    let mut trace = Vec::new();
    let (session, id) = session
        .materialize_synthetic(recipe("LamExpr"), |event| {
            match event {
                AuthoredNormalizationEvent::NameNode(_) => {
                    panic!("existing session must not rebuild name index")
                },
                AuthoredNormalizationEvent::NameLookup(text) => trace.push(format!("name:{text}")),
                AuthoredNormalizationEvent::Append(AuthoredNode::Type(_)) => {
                    trace.push("type".into())
                },
                _ => {},
            }
            Ok::<_, ()>(())
        })
        .expect("second recipe reuses the original session");
    assert_eq!(
        trace,
        [
            "name:Expr",
            "name:x",
            "name:p",
            "name:Expr",
            "name:Expr",
            "type",
            "type",
            "type",
            "name:LamExpr",
            "name:x",
            "name:p"
        ]
    );
    let original_len = session.original_len;
    assert!(id.0 as usize >= original_len);
    assert!(matches!(session.normalize(id, |_| Ok::<_, ()>(())),
        Err(AuthoredNormalizationError::InvalidOriginalRule(found)) if found == id));
}

#[test]
fn owned_synthetic_denial_at_every_event_stops_suffix_without_returning_session() {
    let mut full = Vec::new();
    AuthoredNormalizationSession::new(seed())
        .materialize_synthetic(recipe("LamExpr"), |event| {
            full.push(format!("{event:?}"));
            Ok::<_, usize>(())
        })
        .expect("baseline materialization succeeds");
    for denied in 0..full.len() {
        let mut observed = Vec::new();
        let result = AuthoredNormalizationSession::new(seed()).materialize_synthetic(
            recipe("LamExpr"),
            |event| {
                let index = observed.len();
                observed.push(format!("{event:?}"));
                if index == denied {
                    Err(index)
                } else {
                    Ok(())
                }
            },
        );
        assert!(
            matches!(result, Err(AuthoredNormalizationError::Admission(index)) if index == denied)
        );
        assert_eq!(observed, full[..=denied], "denied event has no executed suffix");
    }
}

#[test]
fn owned_synthetic_unsupported_shapes_return_explicit_errors() {
    let mut legacy = recipe("ExprVar");
    legacy.items.push(LegacyAtomicItem::Other);
    assert!(matches!(
        AuthoredNormalizationSession::new(seed())
            .materialize_synthetic(legacy, |_| Ok::<_, ()>(())),
        Err(AuthoredNormalizationError::UnsupportedSyntheticLegacyItem)
    ));
    let mut syntax = recipe("LamExpr");
    syntax
        .syntax_pattern
        .as_mut()
        .expect("Lam syntax exists")
        .push(InfixSyntaxShape::Other);
    assert!(matches!(
        AuthoredNormalizationSession::new(seed())
            .materialize_synthetic(syntax, |_| Ok::<_, ()>(())),
        Err(AuthoredNormalizationError::UnsupportedSyntheticSyntax)
    ));
}
