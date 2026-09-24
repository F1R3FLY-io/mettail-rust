use super::*;
use mettail_grammar_core::{
    AuthoredCategoryDeclaration, AuthoredCollectionDeclaration, AuthoredDeclarations, AuthoredName,
    AuthoredNameId, AuthoredNode, AuthoredOperation, AuthoredOperationId, AuthoredParam,
    AuthoredParamId, AuthoredParamsId, AuthoredRule, AuthoredRuleId, AuthoredRuleStore,
    AuthoredSyntax, AuthoredSyntaxId, AuthoredType, AuthoredTypeId, CollectionKind,
    SourceObservation,
};
use std::cell::Cell;
use std::convert::Infallible;

fn push(store: &mut AuthoredRuleStore, node: AuthoredNode) -> u32 {
    store.try_push(node).expect("typed fixture append")
}

fn name(store: &mut AuthoredRuleStore, spelling: &str, equality_class: u32) -> AuthoredNameId {
    AuthoredNameId(push(
        store,
        AuthoredNode::Name(AuthoredName {
            spelling: spelling.into(),
            equality_class,
        }),
    ))
}

fn header(categories: Vec<AuthoredCategoryDeclaration>) -> AuthoredDeclarations {
    AuthoredDeclarations {
        categories,
        tokens: vec![],
        global_tokens: vec![],
        modes: vec![],
    }
}

fn declaration(
    name: AuthoredNameId,
    kind: Option<CollectionKind>,
    separator: Option<&str>,
) -> AuthoredCategoryDeclaration {
    AuthoredCategoryDeclaration {
        name,
        native: None,
        collection: kind.map(|kind| AuthoredCollectionDeclaration {
            kind,
            open: None,
            close: None,
            separator: None,
            key_value_separator: separator.map(str::to_owned),
        }),
        byte_observation: SourceObservation::Unavailable,
        literal_observation: SourceObservation::Unavailable,
        element_observation: SourceObservation::Unavailable,
    }
}

fn fixture() -> (AuthoredRuleStore, AuthoredRuleId, AuthoredNameId, AuthoredNameId) {
    let mut store = AuthoredRuleStore::new();
    let label = name(&mut store, "Constructor", 0);
    let category = name(&mut store, "Home", 1);
    let wrong_category = name(&mut store, "Home", 99);
    let element = name(&mut store, "Element", 2);
    let parameter = name(&mut store, "items", 3);
    // This boundary compares spelling; declaration lookup instead uses identity.
    let sep_parameter = name(&mut store, "items", 4);
    let element = AuthoredTypeId(push(&mut store, AuthoredNode::Type(AuthoredType::Base(element))));
    let collection = AuthoredTypeId(push(
        &mut store,
        AuthoredNode::Type(AuthoredType::Collection { kind: CollectionKind::List, element }),
    ));
    let param = AuthoredParamId(push(
        &mut store,
        AuthoredNode::Param(AuthoredParam::Simple { name: parameter, ty: collection }),
    ));
    let params = AuthoredParamsId(push(&mut store, AuthoredNode::Params(vec![param])));
    let sep = AuthoredOperationId(push(
        &mut store,
        AuthoredNode::Operation(AuthoredOperation::Sep {
            collection: sep_parameter,
            separator: ";;".into(),
            source: None,
        }),
    ));
    let syntax = AuthoredSyntaxId(push(
        &mut store,
        AuthoredNode::Syntax(vec![
            AuthoredSyntax::Literal("open".into()),
            AuthoredSyntax::Op(sep),
            AuthoredSyntax::Literal("close".into()),
        ]),
    ));
    let rule = AuthoredRuleId(push(
        &mut store,
        AuthoredNode::Rule(AuthoredRule {
            label,
            category,
            term_context: Some(params),
            syntax_pattern: Some(syntax),
            items: vec![],
        }),
    ));
    (store, rule, category, wrong_category)
}

#[test]
fn missing_header_refuses_before_admission_or_rule_access() {
    let store = AuthoredRuleStore::new();
    let reader = AuthoredRuleReader::new(&store).expect("valid empty arena");
    let called = Cell::new(false);
    let result = derive_authored_collection(&reader, AuthoredRuleId(u32::MAX), |_, _, _| {
        called.set(true);
        Ok::<_, Infallible>(())
    });
    assert!(matches!(result, Err(AuthoredCollectionError::MissingDeclarations)));
    assert!(!called.get());
}

#[test]
fn admission_denial_precedes_rule_observation() {
    let store = AuthoredRuleStore::new()
        .with_declarations(header(vec![]))
        .expect("typed header");
    let reader = AuthoredRuleReader::new(&store).expect("valid arena");
    let called = Cell::new(0);
    let result =
        derive_authored_collection(&reader, AuthoredRuleId(u32::MAX), |seen, rule, decls| {
            assert!(std::ptr::eq(seen, &reader));
            assert_eq!(rule, AuthoredRuleId(u32::MAX));
            assert!(std::ptr::eq(decls, store.declarations().expect("same header")));
            called.set(called.get() + 1);
            Err("denied")
        });
    assert!(matches!(result, Err(AuthoredCollectionError::Admission("denied"))));
    assert_eq!(called.get(), 1);
}

#[test]
fn declaration_identity_and_kind_differ_from_parameter_spelling_and_kind() {
    for kind in [
        CollectionKind::List,
        CollectionKind::Bag,
        CollectionKind::Set,
        CollectionKind::Map,
        CollectionKind::PathMap,
    ] {
        for separator in [None, Some(""), Some("=>")] {
            let (store, rule, category, wrong) = fixture();
            let store = store
                .with_declarations(header(vec![
                    declaration(wrong, Some(CollectionKind::Map), Some("wrong")),
                    declaration(category, Some(kind), separator),
                    declaration(category, Some(CollectionKind::Map), Some("later")),
                ]))
                .expect("source declaration roster");
            let reader = AuthoredRuleReader::new(&store).expect("valid reader");
            let called = Cell::new(0);
            let shape = derive_authored_collection(&reader, rule, |_, _, _| {
                called.set(called.get() + 1);
                Ok::<_, Infallible>(())
            })
            .expect("admitted derivation")
            .expect("spelling-matched collection");
            assert_eq!(called.get(), 1);
            assert_eq!(shape.open_token, "open");
            assert!(!shape.has_synth_paren);
            assert_eq!(shape.close, "close");
            assert_eq!(shape.separator, ";;");
            assert_eq!(shape.element_cat, "Element");
            assert_eq!(shape.coll_kind, mettail_ast::types::CollectionType::Vec);
            assert_eq!(shape.label, "Constructor");
            let expected = match kind {
                CollectionKind::Map | CollectionKind::PathMap => Some(separator.unwrap_or(":")),
                _ => None,
            };
            assert_eq!(shape.pair_separator.as_deref(), expected);
        }
    }
}

#[test]
fn first_matching_noncollection_blocks_duplicate_and_absence_has_no_default() {
    for include_noncollection in [false, true] {
        let (store, rule, category, wrong) = fixture();
        let mut declarations = vec![declaration(wrong, Some(CollectionKind::Map), Some("wrong"))];
        if include_noncollection {
            declarations.push(declaration(category, None, None));
            declarations.push(declaration(category, Some(CollectionKind::Map), Some("later")));
        }
        let store = store
            .with_declarations(header(declarations))
            .expect("typed header");
        let reader = AuthoredRuleReader::new(&store).expect("valid reader");
        let shape = derive_authored_collection(&reader, rule, |_, _, _| Ok::<_, Infallible>(()))
            .expect("admitted derivation")
            .expect("collection shape");
        assert_eq!(shape.pair_separator, None);
    }
}

#[test]
fn shared_pair_separator_callback_is_lazy_and_preserves_empty_override() {
    use mettail_ast::types::CollectionType;
    for kind in [
        CollectionType::Vec,
        CollectionType::HashBag,
        CollectionType::HashSet,
        CollectionType::HashMap,
        CollectionType::PathMap,
    ] {
        for declared in [None, Some(""), Some("=>")] {
            let calls = Cell::new(0);
            let actual = kv_sep_for(&kind, || {
                calls.set(calls.get() + 1);
                declared
            });
            let is_pair = matches!(kind, CollectionType::HashMap | CollectionType::PathMap);
            assert_eq!(calls.get(), usize::from(is_pair));
            let expected = if is_pair {
                Some(declared.unwrap_or(":"))
            } else {
                None
            };
            assert_eq!(actual.as_deref(), expected);
        }
    }
}
