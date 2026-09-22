//! Borrow the original macro reader's observations for flat owned retention.
//!
//! The shared core Enter/Finish worker owns traversal, memoization, equality
//! classes, and checked append. This adapter observes only one existing node at
//! a time; it neither clones the AST nor normalizes/reconstructs source syntax.
//! Pointer/length identities exist only during this immutable borrow. They are
//! never serialized. Macro input is already owned by the trusted frontend;
//! this adapter does not establish runtime resource-admission policy.

use super::binder::MacroBinderSyntaxReader;
use mettail_ast::grammar::{
    DelimitedRegionKind, GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam,
};
use mettail_ast::types::{CollectionType, TypeExpr};
use mettail_grammar_core::*;
use mettail_prattail::wpda_rule_analysis::binder::optional::{
    BinderSyntaxObservation, BinderSyntaxReader, OptionalOperationObservation,
};
use mettail_prattail::wpda_rule_analysis::binder::rule::{
    BinderRuleReader, BinderTypeObservation, MapZipObservation,
};
use mettail_prattail::wpda_rule_analysis::binder::term_param::{
    TermParamObservation, TermParamReader,
};
use syn::Ident;

#[derive(Clone, Copy)]
enum Handle<'syntax> {
    Rule(&'syntax GrammarRule),
    Name(&'syntax Ident),
    Type(&'syntax TypeExpr),
    Param(&'syntax TermParam),
    Params(&'syntax [TermParam]),
    Names(&'syntax [Ident]),
    Syntax(&'syntax [SyntaxExpr]),
    Operation(&'syntax PatternOp),
}

struct MacroSource<'syntax> {
    _rules: &'syntax [GrammarRule],
    reader: MacroBinderSyntaxReader,
}

fn collection_kind(kind: &CollectionType) -> CollectionKind {
    match kind {
        CollectionType::HashBag => CollectionKind::Bag,
        CollectionType::HashSet => CollectionKind::Set,
        CollectionType::Vec => CollectionKind::List,
        CollectionType::HashMap => CollectionKind::Map,
        CollectionType::PathMap => CollectionKind::PathMap,
    }
}

fn name_id(name: &Ident) -> AuthoredNameId<Handle<'_>> {
    AuthoredNameId(Handle::Name(name))
}

impl<'syntax> AuthoredCaptureSource for MacroSource<'syntax> {
    type Handle = Handle<'syntax>;
    type Identity = (usize, usize);
    type NameKey = &'syntax Ident;
    type Error = String;

    fn identity(&self, handle: Self::Handle) -> Self::Identity {
        // The core memo additionally keys every identity by its expected tag.
        // Length distinguishes slices sharing an initial address. Empty slices
        // may share identity because their shallow observation is identical.
        match handle {
            Handle::Rule(rule) => (std::ptr::from_ref(rule) as usize, 1),
            Handle::Name(name) => (std::ptr::from_ref(name) as usize, 1),
            Handle::Type(ty) => (std::ptr::from_ref(ty) as usize, 1),
            Handle::Param(param) => (std::ptr::from_ref(param) as usize, 1),
            Handle::Operation(operation) => (std::ptr::from_ref(operation) as usize, 1),
            Handle::Params(params) => (params.as_ptr() as usize, params.len()),
            Handle::Names(names) => (names.as_ptr() as usize, names.len()),
            Handle::Syntax(syntax) => (syntax.as_ptr() as usize, syntax.len()),
        }
    }

    fn shallow(
        &mut self,
        handle: Self::Handle,
    ) -> Result<AuthoredNode<Self::Handle, Self::NameKey>, String> {
        let reader = &self.reader;
        Ok(match handle {
            Handle::Rule(rule) => {
                let mut items = Vec::with_capacity(rule.items.len());
                for item in &rule.items {
                    items.push(match item {
                        GrammarItem::Terminal(text) => AuthoredLegacyItem::Terminal(text.clone()),
                        GrammarItem::NonTerminal { ident, kind } => {
                            AuthoredLegacyItem::NonTerminal { ident: name_id(ident), kind: *kind }
                        },
                        GrammarItem::Binder { category } => {
                            AuthoredLegacyItem::Binder { category: name_id(category) }
                        },
                        GrammarItem::Collection {
                            coll_type,
                            element_type,
                            separator,
                            delimiters,
                        } => AuthoredLegacyItem::Collection {
                            kind: collection_kind(coll_type),
                            element: name_id(element_type),
                            separator: separator.clone(),
                            open: delimiters.as_ref().map(|(open, _)| open.clone()),
                            close: delimiters.as_ref().map(|(_, close)| close.clone()),
                        },
                    });
                }
                AuthoredNode::Rule(AuthoredRule {
                    label: name_id(reader.label(rule)),
                    category: name_id(reader.category(rule)),
                    term_context: reader
                        .term_context(rule)
                        .map(|params| AuthoredParamsId(Handle::Params(params))),
                    syntax_pattern: reader
                        .syntax_pattern(rule)
                        .map(|syntax| AuthoredSyntaxId(Handle::Syntax(syntax))),
                    items,
                })
            },
            Handle::Name(name) => AuthoredNode::Name(AuthoredName {
                spelling: name.to_string(),
                equality_class: name,
            }),
            Handle::Type(ty) => AuthoredNode::Type(match reader.ty(ty) {
                BinderTypeObservation::Base(name) => AuthoredType::Base(name_id(name)),
                BinderTypeObservation::Collection { coll_type, element } => {
                    AuthoredType::Collection {
                        kind: collection_kind(coll_type),
                        element: AuthoredTypeId(Handle::Type(element)),
                    }
                },
                BinderTypeObservation::Map { key, value } => AuthoredType::Map {
                    key: AuthoredTypeId(Handle::Type(key)),
                    value: AuthoredTypeId(Handle::Type(value)),
                },
                BinderTypeObservation::Arrow { codomain } => AuthoredType::Arrow {
                    codomain: AuthoredTypeId(Handle::Type(codomain)),
                },
                BinderTypeObservation::Other(_) => AuthoredType::Unsupported { tag: 0 },
            }),
            Handle::Param(param) => AuthoredNode::Param(match reader.param(param) {
                TermParamObservation::Simple { name, ty } => AuthoredParam::Simple {
                    name: name_id(name),
                    ty: AuthoredTypeId(Handle::Type(ty)),
                },
                TermParamObservation::GuardBody { name } => {
                    AuthoredParam::GuardBody { name: name_id(name) }
                },
                TermParamObservation::Abstraction { binder, body, ty } => {
                    AuthoredParam::Abstraction {
                        binder: name_id(binder),
                        body: name_id(body),
                        ty: AuthoredTypeId(Handle::Type(ty)),
                    }
                },
                TermParamObservation::MultiAbstraction { binder, body, ty } => {
                    AuthoredParam::MultiAbstraction {
                        binder: name_id(binder),
                        body: name_id(body),
                        ty: AuthoredTypeId(Handle::Type(ty)),
                    }
                },
                TermParamObservation::Optional { params } => AuthoredParam::Optional {
                    params: AuthoredParamsId(Handle::Params(params)),
                },
            }),
            Handle::Params(params) => {
                let mut values = Vec::with_capacity(reader.params_len(params));
                for index in 0..reader.params_len(params) {
                    values.push(AuthoredParamId(Handle::Param(
                        reader
                            .param_at(params, index)
                            .expect("original reader parameter index is in bounds"),
                    )));
                }
                AuthoredNode::Params(values)
            },
            Handle::Names(names) => {
                let mut values = Vec::with_capacity(reader.names_len(names));
                for index in 0..reader.names_len(names) {
                    values.push(name_id(
                        reader
                            .name_at(names, index)
                            .expect("original reader name index is in bounds"),
                    ));
                }
                AuthoredNode::Names(values)
            },
            Handle::Syntax(syntax) => {
                let mut values = Vec::with_capacity(reader.sequence_len(syntax));
                for index in 0..reader.sequence_len(syntax) {
                    values.push(
                        match reader
                            .at(syntax, index)
                            .expect("original reader syntax index is in bounds")
                        {
                            BinderSyntaxObservation::Literal(text) => {
                                AuthoredSyntax::Literal(text.to_owned())
                            },
                            BinderSyntaxObservation::Param(name) => {
                                AuthoredSyntax::Param(name_id(name))
                            },
                            BinderSyntaxObservation::TokenKind { name, bind } => {
                                AuthoredSyntax::TokenKind {
                                    name: name_id(name),
                                    bind: bind.map(name_id),
                                }
                            },
                            BinderSyntaxObservation::GuestBody { open, close, bind, kind } => {
                                AuthoredSyntax::GuestBody {
                                    open: name_id(open),
                                    close: name_id(close),
                                    bind: name_id(bind),
                                    kind: match kind {
                                        DelimitedRegionKind::Flt => {
                                            AuthoredDelimitedRegionKind::Flt
                                        },
                                    },
                                }
                            },
                            BinderSyntaxObservation::Op(operation) => AuthoredSyntax::Op(
                                AuthoredOperationId(Handle::Operation(operation)),
                            ),
                        },
                    );
                }
                AuthoredNode::Syntax(values)
            },
            Handle::Operation(operation) => {
                AuthoredNode::Operation(match reader.operation(operation) {
                    OptionalOperationObservation::Opt { inner } => AuthoredOperation::Opt {
                        inner: AuthoredSyntaxId(Handle::Syntax(inner)),
                    },
                    OptionalOperationObservation::Sep { collection, separator, source } => {
                        AuthoredOperation::Sep {
                            collection: name_id(collection),
                            separator: separator.to_owned(),
                            source: source
                                .map(|operation| AuthoredOperationId(Handle::Operation(operation))),
                        }
                    },
                    OptionalOperationObservation::Other(original) => match reader
                        .map_zip_operation(original)
                    {
                        MapZipObservation::Map { source, params, body } => AuthoredOperation::Map {
                            source: AuthoredOperationId(Handle::Operation(source)),
                            params: AuthoredNamesId(Handle::Names(params)),
                            body: AuthoredSyntaxId(Handle::Syntax(body)),
                        },
                        MapZipObservation::Zip { left, right } => AuthoredOperation::Zip {
                            left: name_id(left),
                            right: name_id(right),
                        },
                        MapZipObservation::Other(_) => AuthoredOperation::Unsupported { tag: 0 },
                    },
                })
            },
        })
    }
}

/// Retain one complete macro rule roster before its syntax is lowered. The
/// frontend transport integration is separate; this function changes no rule.
pub(crate) fn capture_rules(rules: &[GrammarRule]) -> Result<CapturedAuthoredNodes, String> {
    let mut source = MacroSource {
        _rules: rules,
        reader: MacroBinderSyntaxReader,
    };
    let roots: Vec<_> = rules
        .iter()
        .map(|rule| (AuthoredNodeTag::Rule, Handle::Rule(rule)))
        .collect();
    capture_authored_nodes(&mut source, &roots, |_, _| Ok::<_, String>(()))
        .map_err(|error| format!("cannot retain macro authored rules: {error:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::rule_fixture;
    use mettail_prattail::wpda_rule_analysis::authored::AuthoredRuleReader;
    use mettail_prattail::wpda_rule_analysis::binder::rule::classify_binder_in;
    use proc_macro2::Span;
    use std::cell::RefCell;

    fn id(name: &str) -> Ident {
        Ident::new(name, Span::call_site())
    }
    fn base(name: &str) -> TypeExpr {
        TypeExpr::Base(id(name))
    }
    fn literal(text: &str) -> SyntaxExpr {
        SyntaxExpr::Literal(text.to_owned())
    }
    fn param(name: &str) -> SyntaxExpr {
        SyntaxExpr::Param(id(name))
    }
    fn simple(name: &str, ty: TypeExpr) -> TermParam {
        TermParam::Simple { name: id(name), ty }
    }
    fn collection(kind: CollectionType, category: &str) -> TypeExpr {
        TypeExpr::Collection {
            coll_type: kind,
            element: Box::new(base(category)),
        }
    }
    fn sep(name: &str) -> SyntaxExpr {
        SyntaxExpr::Op(PatternOp::Sep {
            collection: id(name),
            separator: ",".into(),
            source: None,
        })
    }
    fn rule(params: Vec<TermParam>, syntax: Vec<SyntaxExpr>) -> GrammarRule {
        GrammarRule {
            term_context: Some(params),
            syntax_pattern: Some(syntax),
            ..rule_fixture(id("Projection"), id("Expr"))
        }
    }

    // Invoke the SAME original classifier for each reader, including its lazy
    // callback sites. Debug compares every descriptor field without requiring
    // a new semantic equality implementation for BinderShape.
    fn descriptor<'s, R: BinderRuleReader<'s>>(
        reader: &'s R,
        rule: R::Rule,
    ) -> (bool, String, Vec<String>)
    where
        <R as BinderSyntaxReader<'s>>::Name: std::fmt::Display,
    {
        let trace = RefCell::new(Vec::new());
        let shape = classify_binder_in(
            reader,
            rule,
            || {
                trace.borrow_mut().push("delimiters".into());
            },
            |open| {
                trace.borrow_mut().push(format!("guest:{open}"));
                vec!["Nested".into()]
            },
            |kind, ()| {
                trace.borrow_mut().push(format!("kv:{kind:?}"));
                Some(":".into())
            },
        );
        (shape.is_some(), format!("{shape:?}"), trace.into_inner())
    }

    #[test]
    fn capture_macro_original_classifier_and_callback_correspondence() {
        // Fixtures use the original binder projection baseline constructors.
        let mut fixtures = vec![
            rule(vec![], vec![SyntaxExpr::TokenKind { name: id("Word"), bind: None }]),
            rule(vec![], vec![SyntaxExpr::TokenKind { name: id("Word"), bind: Some(id("word")) }]),
            rule(
                vec![TermParam::GuardBody { name: id("guest") }],
                vec![
                    literal("guest"),
                    SyntaxExpr::GuestBody {
                        open: id("Open"),
                        close: id("Close"),
                        bind: id("guest"),
                        kind: DelimitedRegionKind::Flt,
                    },
                ],
            ),
            rule(
                vec![
                    simple("names", collection(CollectionType::Vec, "Name")),
                    simple("body", base("Expr")),
                ],
                vec![
                    literal("start"),
                    SyntaxExpr::Op(PatternOp::Opt {
                        inner: vec![sep("names"), literal("]"), param("body")],
                    }),
                ],
            ),
            rule(
                vec![
                    simple("prefix", collection(CollectionType::Vec, "Expr")),
                    TermParam::MultiAbstraction {
                        binder: id("xs"),
                        body: id("body"),
                        ty: TypeExpr::Arrow {
                            domain: Box::new(base("HiddenDomain")),
                            codomain: Box::new(base("Expr")),
                        },
                    },
                    simple("names", collection(CollectionType::HashSet, "Name")),
                ],
                vec![
                    literal("start"),
                    sep("prefix"),
                    literal(";"),
                    SyntaxExpr::Op(PatternOp::Sep {
                        collection: id("ignored"),
                        separator: ",".into(),
                        source: Some(Box::new(PatternOp::Map {
                            source: Box::new(PatternOp::Zip { left: id("names"), right: id("xs") }),
                            params: vec![id("n"), id("x")],
                            body: vec![param("x"), literal("?"), param("n")],
                        })),
                    }),
                    literal(")"),
                    param("body"),
                ],
            ),
            rule(
                vec![],
                vec![literal("unsupported"), SyntaxExpr::Op(PatternOp::Var(id("hidden")))],
            ),
            rule(
                vec![TermParam::Optional {
                    params: vec![simple("value", base("Expr"))],
                }],
                vec![
                    literal("optional"),
                    SyntaxExpr::Op(PatternOp::Opt { inner: vec![param("value")] }),
                ],
            ),
        ];
        for kind in [
            CollectionType::HashBag,
            CollectionType::HashSet,
            CollectionType::Vec,
            CollectionType::HashMap,
            CollectionType::PathMap,
        ] {
            fixtures.push(rule(
                vec![simple("items", collection(kind, "Expr"))],
                vec![literal("["), sep("items"), literal("]")],
            ));
        }
        for value in ["Name", "Expr"] {
            fixtures.push(rule(
                vec![simple(
                    "items",
                    TypeExpr::Map {
                        key: Box::new(base("Name")),
                        value: Box::new(base(value)),
                    },
                )],
                vec![literal("["), sep("items"), literal("]")],
            ));
        }
        let captured = capture_rules(&fixtures).expect("original classifier fixtures must capture");
        let owned = AuthoredRuleReader::new(&captured.store)
            .expect("captured classifier fixtures must admit the original reader");
        let original = MacroBinderSyntaxReader;
        for (index, (source, root)) in fixtures.iter().zip(&captured.roots).enumerate() {
            let expected = descriptor(&original, source);
            assert_eq!(descriptor(&owned, AuthoredRuleId(*root)), expected, "fixture {index}");
            if [0, 3, 4].contains(&index) {
                assert!(expected.0, "acceptance witness {index}");
            }
            if index == 5 {
                assert!(!expected.0, "unsupported operation must remain rejected");
            }
        }
    }

    #[test]
    fn capture_macro_independent_presence_and_original_name_equality() {
        let names = [
            id("Same"),
            Ident::new("Same", Span::mixed_site()),
            Ident::new_raw("Same", Span::call_site()),
            id("Different"),
        ];
        let mut fixtures = Vec::new();
        for (index, label) in names.iter().enumerate() {
            fixtures.push(GrammarRule {
                label: label.clone(),
                category: names[(index + 1) % names.len()].clone(),
                term_context: (index & 1 != 0).then(Vec::new),
                syntax_pattern: (index & 2 != 0).then(Vec::new),
                ..rule_fixture(id("unused"), id("unused"))
            });
        }
        let captured =
            capture_rules(&fixtures).expect("presence and equality fixtures must capture");
        let owned = AuthoredRuleReader::new(&captured.store)
            .expect("captured presence fixtures must admit the original reader");
        let original = MacroBinderSyntaxReader;
        for (index, source) in fixtures.iter().enumerate() {
            let root = AuthoredRuleId(captured.roots[index]);
            assert_eq!(owned.term_context(root).is_some(), source.term_context.is_some());
            assert_eq!(owned.syntax_pattern(root).is_some(), source.syntax_pattern.is_some());
            assert_eq!(owned.label(root).to_string(), source.label.to_string());
            assert_eq!(owned.category(root).to_string(), source.category.to_string());
            if let Some(params) = owned.term_context(root) {
                assert_eq!(owned.params_len(params), 0);
            }
            if let Some(syntax) = owned.syntax_pattern(root) {
                assert_eq!(owned.sequence_len(syntax), 0);
            }
            assert_eq!(descriptor(&owned, root), descriptor(&original, source));
            for (other_index, other) in fixtures.iter().enumerate() {
                let other_root = AuthoredRuleId(captured.roots[other_index]);
                assert_eq!(
                    owned.names_equal(owned.label(root), owned.category(other_root)),
                    original.names_equal(original.label(source), original.category(other))
                );
            }
        }
        let AuthoredNode::Rule(first) = captured
            .store
            .get(captured.roots[0])
            .expect("first captured root must exist")
        else {
            panic!("first captured rule root changed tag")
        };
        let AuthoredNode::Rule(second) = captured
            .store
            .get(captured.roots[1])
            .expect("second captured root must exist")
        else {
            panic!("second captured rule root changed tag")
        };
        assert_ne!(first.label, second.label, "equal source names retain occurrence handles");
    }

    #[test]
    fn capture_macro_legacy_payloads_are_not_reclassified_or_normalized() {
        let kinds = [
            AuthoredNonTerminalKind::Var,
            AuthoredNonTerminalKind::Integer,
            AuthoredNonTerminalKind::Boolean,
            AuthoredNonTerminalKind::StringLiteral,
            AuthoredNonTerminalKind::FloatLiteral,
            AuthoredNonTerminalKind::Ident,
            AuthoredNonTerminalKind::Category,
        ];
        let mut source = rule_fixture(id("Legacy"), id("Expr"));
        source
            .items
            .push(GrammarItem::Terminal("raw\\n text".into()));
        for kind in kinds {
            source
                .items
                .push(GrammarItem::NonTerminal { ident: id("Expr"), kind });
        }
        source
            .items
            .push(GrammarItem::Binder { category: id("Name") });
        for (index, kind) in [
            CollectionType::HashBag,
            CollectionType::HashSet,
            CollectionType::Vec,
            CollectionType::HashMap,
            CollectionType::PathMap,
        ]
        .into_iter()
        .enumerate()
        {
            source.items.push(GrammarItem::Collection {
                coll_type: kind,
                element_type: id("Expr"),
                separator: "::".into(),
                delimiters: (index % 2 == 0).then(|| (String::new(), "]".into())),
            });
        }
        let captured =
            capture_rules(std::slice::from_ref(&source)).expect("legacy fixture must capture");
        let AuthoredNode::Rule(retained) = captured
            .store
            .get(captured.roots[0])
            .expect("legacy captured root must exist")
        else {
            panic!("legacy captured rule root changed tag")
        };
        let name = |name: AuthoredNameId| {
            let AuthoredNode::Name(value) = captured
                .store
                .get(name.0)
                .expect("legacy name reference must resolve")
            else {
                panic!("legacy name reference changed tag")
            };
            value.spelling.as_str()
        };
        assert!(retained.term_context.is_none() && retained.syntax_pattern.is_none());
        assert_eq!(retained.items.len(), source.items.len());
        for (original, owned) in source.items.iter().zip(&retained.items) {
            match (original, owned) {
                (GrammarItem::Terminal(a), AuthoredLegacyItem::Terminal(b)) => assert_eq!(a, b),
                (
                    GrammarItem::NonTerminal { ident, kind },
                    AuthoredLegacyItem::NonTerminal { ident: other, kind: other_kind },
                ) => {
                    assert_eq!(ident.to_string(), name(*other));
                    assert_eq!(kind, other_kind);
                },
                (
                    GrammarItem::Binder { category },
                    AuthoredLegacyItem::Binder { category: other },
                ) => assert_eq!(category.to_string(), name(*other)),
                (
                    GrammarItem::Collection {
                        coll_type,
                        element_type,
                        separator,
                        delimiters,
                    },
                    AuthoredLegacyItem::Collection {
                        kind,
                        element,
                        separator: other_separator,
                        open,
                        close,
                    },
                ) => {
                    assert_eq!(collection_kind(coll_type), *kind);
                    assert_eq!(element_type.to_string(), name(*element));
                    assert_eq!(separator, other_separator);
                    assert_eq!(delimiters.as_ref().map(|pair| &pair.0), open.as_ref());
                    assert_eq!(delimiters.as_ref().map(|pair| &pair.1), close.as_ref());
                },
                _ => panic!("legacy variant changed"),
            }
        }
    }

    #[test]
    fn capture_macro_unsupported_identity_and_unobserved_interiors() {
        let fixture = rule(
            vec![
                simple(
                    "refined",
                    TypeExpr::Refined {
                        var: id("HiddenRefinedVar"),
                        base: Box::new(base("HiddenRefinedBase")),
                        predicate_repr: "hidden predicate".into(),
                    },
                ),
                simple("multi", TypeExpr::MultiBinder(Box::new(base("HiddenMulti")))),
                TermParam::Abstraction {
                    binder: id("x"),
                    body: id("body"),
                    ty: TypeExpr::Arrow {
                        domain: Box::new(base("HiddenDomain")),
                        codomain: Box::new(base("Expr")),
                    },
                },
                TermParam::Optional {
                    params: vec![TermParam::GuardBody { name: id("guest") }],
                },
            ],
            vec![
                SyntaxExpr::Op(PatternOp::Var(id("HiddenOperation"))),
                SyntaxExpr::Op(PatternOp::Var(id("AnotherHiddenOperation"))),
                SyntaxExpr::GuestBody {
                    open: id("Open"),
                    close: id("Close"),
                    bind: id("guest"),
                    kind: DelimitedRegionKind::Flt,
                },
            ],
        );
        let captured = capture_rules(std::slice::from_ref(&fixture))
            .expect("unsupported reader observations must remain capturable");
        let mut unsupported_types = Vec::new();
        let mut unsupported_operations = Vec::new();
        let mut names = Vec::new();
        let mut saw_abstraction = false;
        let mut saw_optional = false;
        for index in 0..captured.store.len() {
            match captured
                .store
                .get(index as u32)
                .expect("enumerated captured node must exist")
            {
                AuthoredNode::Name(name) => names.push(name.spelling.as_str()),
                AuthoredNode::Type(AuthoredType::Unsupported { tag }) => {
                    assert_eq!(*tag, 0);
                    unsupported_types.push(index);
                },
                AuthoredNode::Operation(AuthoredOperation::Unsupported { tag }) => {
                    assert_eq!(*tag, 0);
                    unsupported_operations.push(index);
                },
                AuthoredNode::Param(AuthoredParam::Abstraction { .. }) => saw_abstraction = true,
                AuthoredNode::Param(AuthoredParam::Optional { .. }) => saw_optional = true,
                _ => {},
            }
        }
        assert_eq!(unsupported_types.len(), 2);
        assert_eq!(unsupported_operations.len(), 2);
        assert!(saw_abstraction && saw_optional);
        for hidden in [
            "HiddenRefinedVar",
            "HiddenRefinedBase",
            "HiddenMulti",
            "HiddenDomain",
            "HiddenOperation",
            "AnotherHiddenOperation",
        ] {
            assert!(!names.contains(&hidden), "must not descend into unobserved {hidden}");
        }
        for visible in ["Expr", "Open", "Close", "guest"] {
            assert!(names.contains(&visible));
        }
        let reader = AuthoredRuleReader::new(&captured.store)
            .expect("unsupported opaque handles must admit the original reader");
        for index in unsupported_types {
            assert!(
                matches!(reader.ty(AuthoredTypeId(index as u32)), BinderTypeObservation::Other(id) if id.0 == index as u32)
            );
        }
        for index in unsupported_operations {
            assert!(
                matches!(reader.map_zip_operation(AuthoredOperationId(index as u32)), MapZipObservation::Other(id) if id.0 == index as u32)
            );
        }
    }
}
