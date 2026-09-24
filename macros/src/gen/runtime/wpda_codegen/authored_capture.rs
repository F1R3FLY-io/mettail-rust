//! Borrow the original macro reader's observations for flat owned retention.
//!
//! The shared core Enter/Finish worker owns traversal, memoization, equality
//! classes, and checked append. This adapter observes only one existing node at
//! a time; it neither clones the AST nor normalizes/reconstructs source syntax.
//! Pointer/length identities exist only during this immutable borrow. They are
//! never serialized. Macro input is already owned by the trusted frontend;
//! this adapter does not establish runtime resource-admission policy.

use super::binder::MacroBinderSyntaxReader;
use crate::gen::native::NativeTypeFromSynType;
use mettail_ast::grammar::{
    AstTermParamReader, DelimitedRegionKind, GrammarItem, GrammarRule, PatternOp, SyntaxExpr,
    TermParam,
};
use mettail_ast::language::NativeKindFromSynType;
use mettail_ast::types::{CollectionType, TypeExpr};
use mettail_grammar_core::context_items::ContextItemsReader;
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

pub(super) fn collection_kind(kind: &CollectionType) -> CollectionKind {
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
                    source_body_present: SourceObservation::Known(rule.rust_code.is_some()),
                    explicit_fold: SourceObservation::Known(
                        rule.eval_mode == Some(mettail_ast::types::EvalMode::Fold),
                    ),
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
                BinderTypeObservation::Arrow { codomain } => {
                    let (domain, _) = AstTermParamReader
                        .arrow(ty)
                        .expect("the original arrow observation has its original domain");
                    AuthoredType::Arrow {
                        domain: AuthoredTypeId(Handle::Type(domain)),
                        codomain: AuthoredTypeId(Handle::Type(codomain)),
                    }
                },
                BinderTypeObservation::Other(_) => match AstTermParamReader.multi_binder(ty) {
                    Some(inner) => AuthoredType::MultiBinder {
                        inner: AuthoredTypeId(Handle::Type(inner)),
                    },
                    None => AuthoredType::Unsupported { tag: 0 },
                },
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
#[cfg(test)]
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

/// Retain declarations through the same name roots and source-equality table
/// as the rules. These are the parser's actual TokenDef names, not inferred
/// names reconstructed from a normalized token family or native carrier.
pub(crate) fn capture_language(
    language: &mettail_ast::language::LanguageDef,
) -> Result<CapturedAuthoredNodes, String> {
    // The original shallow probe returns an owned Ident. Keep those exact
    // observations alive through capture, using its existing Ident equality.
    // No source or native type is reconstructed from a rendered spelling.
    let elements: Vec<_> = language
        .types
        .iter()
        .map(|category| {
            category
                .native_type
                .as_ref()
                .and_then(mettail_ast::language::element_ident_from_native_type)
        })
        .collect();
    capture_language_with_elements(language, &elements)
}

fn capture_language_with_elements<'syntax>(
    language: &'syntax mettail_ast::language::LanguageDef,
    elements: &'syntax [Option<Ident>],
) -> Result<CapturedAuthoredNodes, String> {
    let categories = language
        .types
        .iter()
        .zip(elements)
        .map(|(category, element)| AuthoredCategoryDeclaration {
            name: name_id(&category.name),
            native: category
                .native_type
                .as_ref()
                .map(mettail_ast::language::NativeKind::from_syn_type),
            byte_observation: SourceObservation::Known(
                category
                    .native_type
                    .as_ref()
                    .is_some_and(crate::gen::native::is_byte_vector),
            ),
            literal_observation: SourceObservation::Known(category.native_type.as_ref().map(
                |native| {
                    LiteralNativeObservation::ExactNativeType(NativeType::from_syn_type(native))
                },
            )),
            element_observation: SourceObservation::Known(element.as_ref().map(name_id)),
            collection: category.collection_kind.as_ref().map(|collection| {
                let delimiters = collection.delimiters();
                AuthoredCollectionDeclaration {
                    kind: collection_kind(&collection.coll_type()),
                    open: Some(delimiters.open.clone()),
                    close: Some(delimiters.close.clone()),
                    separator: Some(delimiters.sep.clone()),
                    key_value_separator: delimiters.key_val_sep.clone(),
                }
            }),
        })
        .collect();
    let count = language
        .mode_defs
        .iter()
        .try_fold(language.token_defs.len(), |count, mode| {
            count.checked_add(mode.token_defs.len())
        })
        .ok_or("source token count overflow")?;
    let mut tokens = Vec::with_capacity(count);
    let mut append = |token: &'syntax mettail_ast::language::TokenDef| -> Result<u32, String> {
        let index = u32::try_from(tokens.len()).map_err(|_| "source token index overflow")?;
        tokens.push(AuthoredTokenDeclaration {
            name: name_id(&token.name),
            category: token.category.as_ref().map(name_id),
            from_literals: token.from_literals,
            has_evaluation: token.rust_code.is_some(),
            push: token.push_mode.as_ref().map(name_id),
        });
        Ok(index)
    };
    let global_tokens = language
        .token_defs
        .iter()
        .map(&mut append)
        .collect::<Result<_, _>>()?;
    let modes = language
        .mode_defs
        .iter()
        .map(|mode| {
            Ok(AuthoredModeDeclaration {
                name: name_id(&mode.name),
                tokens: mode
                    .token_defs
                    .iter()
                    .map(&mut append)
                    .collect::<Result<_, String>>()?,
            })
        })
        .collect::<Result<_, String>>()?;
    let declarations = AuthoredDeclarations { categories, tokens, global_tokens, modes };
    let roots: Vec<_> = language
        .terms
        .iter()
        .map(|rule| (AuthoredNodeTag::Rule, Handle::Rule(rule)))
        .collect();
    let mut source = MacroSource {
        _rules: &language.terms,
        reader: MacroBinderSyntaxReader,
    };
    capture_authored_declarations(&mut source, &roots, declarations, |_, _| Ok::<_, String>(()))
        .map_err(|error| format!("cannot retain macro authored declarations: {error:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::rule_fixture;
    use mettail_prattail::wpda_rule_analysis::authored::AuthoredRuleReader;
    use mettail_prattail::wpda_rule_analysis::binder::rule::classify_binder_in;
    use proc_macro2::Span;
    use quote::quote;
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
        let mut multi_types = Vec::new();
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
                AuthoredNode::Type(AuthoredType::MultiBinder { .. }) => multi_types.push(index),
                AuthoredNode::Operation(AuthoredOperation::Unsupported { tag }) => {
                    assert_eq!(*tag, 0);
                    unsupported_operations.push(index);
                },
                AuthoredNode::Param(AuthoredParam::Abstraction { .. }) => saw_abstraction = true,
                AuthoredNode::Param(AuthoredParam::Optional { .. }) => saw_optional = true,
                _ => {},
            }
        }
        assert_eq!(unsupported_types.len(), 1);
        assert_eq!(multi_types.len(), 1);
        assert_eq!(unsupported_operations.len(), 2);
        assert!(saw_abstraction && saw_optional);
        for hidden in [
            "HiddenRefinedVar",
            "HiddenRefinedBase",
            "HiddenOperation",
            "AnotherHiddenOperation",
        ] {
            assert!(!names.contains(&hidden), "must not descend into unobserved {hidden}");
        }
        for visible in ["Expr", "Open", "Close", "guest", "HiddenMulti", "HiddenDomain"] {
            assert!(names.contains(&visible));
        }
        let reader = AuthoredRuleReader::new(&captured.store)
            .expect("unsupported opaque handles must admit the original reader");
        for index in unsupported_types.into_iter().chain(multi_types) {
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

    fn declaration_language(
        source: proc_macro2::TokenStream,
    ) -> mettail_ast::language::LanguageDef {
        syn::parse2(source).expect("original authored declaration fixture parses")
    }

    fn retained_name(store: &AuthoredRuleStore, id: AuthoredNameId) -> &AuthoredName {
        let AuthoredNode::Name(name) = store
            .get(id.0)
            .expect("retained name belongs to this store")
        else {
            panic!("retained declaration name changed its node tag");
        };
        name
    }

    #[test]
    fn capture_native_observations_use_original_byte_type_and_element_probes() {
        let natives: Vec<syn::Type> = vec![
            syn::parse_quote!(i8),
            syn::parse_quote!(i16),
            syn::parse_quote!(i32),
            syn::parse_quote!(i64),
            syn::parse_quote!(i128),
            syn::parse_quote!(isize),
            syn::parse_quote!(u8),
            syn::parse_quote!(u16),
            syn::parse_quote!(u32),
            syn::parse_quote!(u64),
            syn::parse_quote!(u128),
            syn::parse_quote!(usize),
            syn::parse_quote!(f32),
            syn::parse_quote!(f64),
            syn::parse_quote!(bool),
            syn::parse_quote!(String),
            syn::parse_quote!(CanonicalBigInt),
            syn::parse_quote!(CanonicalBigRat),
            syn::parse_quote!(CanonicalFixedPoint),
            syn::parse_quote!(Vec<Expr>),
            syn::parse_quote!(Vec<u8>),
            syn::parse_quote!(HashBag<Expr>),
            syn::parse_quote!(HashSet<Expr>),
            syn::parse_quote!(HashMapLit<Key, Value>),
            syn::parse_quote!(HashMap<Key, Value>),
            syn::parse_quote!(custom::HashSetLit<Expr>),
            syn::parse_quote!(custom::PathMapLit<Key, Value>),
            syn::parse_quote!(Vec<Option<Expr>>),
            syn::parse_quote!([u8; 2]),
            syn::parse_quote!(&str),
        ];
        for native in natives {
            let mut language = declaration_language(quote! {
                name: Observed, types { Expr }, terms { }
            });
            language.types[0].native_type = Some(native.clone());
            let captured = capture_language(&language).expect("capture original source");
            let row = &captured.store.declarations().expect("header").categories[0];
            let byte = crate::gen::native::is_byte_vector(&native);
            assert_eq!(row.byte_observation, SourceObservation::Known(byte));
            assert_eq!(
                row.literal_observation,
                SourceObservation::Known(Some(LiteralNativeObservation::ExactNativeType(
                    NativeType::from_syn_type(&native)
                )))
            );
            let expected_element = mettail_ast::language::element_ident_from_native_type(&native);
            let SourceObservation::Known(element) = row.element_observation else {
                panic!("macro source probe is available");
            };
            assert_eq!(
                element.map(|id| retained_name(&captured.store, id).spelling.as_str()),
                expected_element
                    .as_ref()
                    .map(|id| id.to_string())
                    .as_deref()
            );
            let original = crate::gen::generate_literal_label(&native).to_string();
            let SourceObservation::Known(Some(observation)) = &row.literal_observation else {
                panic!("source has a native type");
            };
            let retained = constructor_labels::generate_literal_label_observed(
                || byte,
                || observation.clone(),
                str::to_owned,
            );
            assert_eq!(retained, original);
        }
        let language = declaration_language(quote! {
            name: Absent, types { Expr }, terms { }
        });
        let captured = capture_language(&language).expect("capture absent native");
        let row = &captured.store.declarations().expect("header").categories[0];
        assert_eq!(row.byte_observation, SourceObservation::Known(false));
        assert_eq!(row.literal_observation, SourceObservation::Known(None));
        assert_eq!(row.element_observation, SourceObservation::Known(None));
    }

    #[test]
    fn capture_macro_declaration_zero_rules_keep_native_delimiters_and_name_equality() {
        // Reuse the original AST declaration-observation source forms. Capture
        // is checked independently from final lexer/category association.
        let language = declaration_language(quote! {
            name: Retained,
            types {
                Plain ![UserPayload] as Wrapped ![i8] as Tiny ![u32] as Wide
                ![UserPayload] as Map ["map-open", "map-close", ";", "=>"]
                ![UserPayload] as List ["", "]", "|"]
            },
            literals {
                Tiny { pattern: "tiny"; eval: ![tiny_eval(text)]; }
                Wide { pattern: "wide"; eval: ![wide_eval(text)]; }
            },
            terms { }
        });
        assert!(language.terms.is_empty());
        let captured = capture_language(&language).expect("declaration-only source captures");
        assert!(captured.roots.is_empty(), "declaration names are not rule roots");
        let header = captured
            .store
            .declarations()
            .expect("zero-rule capture retains its header");
        assert_eq!(header.categories.len(), 6);
        assert_eq!(
            header
                .categories
                .iter()
                .map(|category| category.native)
                .collect::<Vec<_>>(),
            [
                None,
                Some(NativeKind::Other),
                Some(NativeKind::Int8),
                Some(NativeKind::UInt32),
                Some(NativeKind::Other),
                Some(NativeKind::Other),
            ]
        );
        assert_eq!(
            header.categories[4].collection,
            Some(AuthoredCollectionDeclaration {
                kind: CollectionKind::Map,
                open: Some("map-open".into()),
                close: Some("map-close".into()),
                separator: Some(";".into()),
                key_value_separator: Some("=>".into()),
            })
        );
        assert_eq!(
            header.categories[5].collection,
            Some(AuthoredCollectionDeclaration {
                kind: CollectionKind::List,
                open: Some(String::new()),
                close: Some("]".into()),
                separator: Some("|".into()),
                key_value_separator: None,
            })
        );
        assert_eq!(header.global_tokens, [0, 1]);
        let mut names: Vec<_> = language
            .types
            .iter()
            .zip(&header.categories)
            .map(|(source, retained)| (&source.name, retained.name))
            .collect();
        for (source, retained) in language.token_defs.iter().zip(&header.tokens) {
            names.push((&source.name, retained.name));
            assert_eq!(retained.from_literals, source.from_literals);
            assert_eq!(retained.has_evaluation, source.rust_code.is_some());
            assert_eq!(retained.category.is_some(), source.category.is_some());
            if let (Some(source), Some(retained)) = (&source.category, retained.category) {
                names.push((source, retained));
            }
        }
        for (original, retained) in &names {
            assert_eq!(retained_name(&captured.store, *retained).spelling, original.to_string());
            for (other_original, other_retained) in &names {
                assert_eq!(
                    retained_name(&captured.store, *retained).equality_class
                        == retained_name(&captured.store, *other_retained).equality_class,
                    original == other_original,
                    "retained equality must follow original Ident equality, not occurrence IDs",
                );
            }
        }
        assert_ne!(header.tokens[0].name, header.tokens[1].name);
        assert_eq!(retained_name(&captured.store, header.tokens[0].name).spelling, "Integer");
        assert_eq!(
            retained_name(&captured.store, header.tokens[0].name).equality_class,
            retained_name(&captured.store, header.tokens[1].name).equality_class,
        );
    }

    #[test]
    fn capture_macro_declaration_zero_rule_owner_survives_actual_core_bridge() {
        let language = declaration_language(quote! {
            name: EmptyRetained,
            types { Plain data Closed },
            terms { }
        });
        let spec = crate::gen::syntax::parser::prattail_bridge::language_def_to_spec(&language)
            .expect("zero-rule language uses the original specification bridge");
        assert!(spec.rules.is_empty());
        let owner = spec
            .authored
            .as_ref()
            .expect("declarations retain an owner without rules");
        let core = spec
            .to_grammar_core()
            .expect("declaration-only specification lowers to Core");
        assert!(core.productions.is_empty());
        assert_eq!(core.authored.as_ref(), Some(owner.as_ref()));
        let bindings = core
            .authored_bindings
            .as_ref()
            .expect("retained declarations have final bindings");
        assert_eq!(bindings.categories, [CategoryId(0), CategoryId(1)]);
        assert!(bindings.tokens.is_empty() && bindings.modes.is_empty());
        assert!(core.categories[0].admits_variables);
        assert!(!core.categories[1].admits_variables);
        core.validate()
            .expect("zero-rule owner and associations validate");
    }

    #[test]
    fn capture_macro_declaration_bridge_preserves_coalesced_and_dual_token_routes() {
        let language = declaration_language(quote! {
            name: LiteralRoutes,
            types { ![i8] as Tiny ![u32] as Wide ![CanonicalBigRat] as Rat },
            literals {
                Tiny { pattern: "tiny"; eval: ![tiny_eval(text)]; }
                Wide { pattern: "wide"; eval: ![wide_eval(text)]; }
                Rat { pattern: "ratio"; eval: ![ratio_eval(text)]; }
            },
            terms { }
        });
        let spec = crate::gen::syntax::parser::prattail_bridge::language_def_to_spec(&language)
            .expect("literal routes use original lowering and family classification");
        let core = spec
            .to_grammar_core()
            .expect("actual token append and coalescing sites bind rows");
        let store = core
            .authored
            .as_ref()
            .expect("literal source owner survives");
        let header = store
            .declarations()
            .expect("literal source header survives");
        let bindings = core
            .authored_bindings
            .as_ref()
            .expect("actual bridge completed associations");
        assert_eq!(header.global_tokens, [0, 1, 2]);
        assert_eq!(bindings.tokens.len(), 3);
        let tiny = &bindings.tokens[0];
        let wide = &bindings.tokens[1];
        let rational = &bindings.tokens[2];
        assert_eq!(tiny.direct, wide.direct, "two source declarations share one builtin family");
        assert_eq!(core.tokens[tiny.direct.0 as usize].name, "Integer");
        assert!(tiny.typed_literal.is_none() && wide.typed_literal.is_none());
        let typed = rational
            .typed_literal
            .expect("original BigRat lowering emits a typed route");
        assert_ne!(typed, rational.direct, "direct and typed routes must not be conflated");
        assert_eq!(core.tokens[rational.direct.0 as usize].name, "Rat");
        assert_eq!(core.tokens[typed.0 as usize].name, "Rational/Rat");
        assert_eq!(retained_name(store, header.tokens[2].name).spelling, "Rat");
        assert_eq!(
            core.tokens
                .iter()
                .filter(|token| token.name == "Integer")
                .count(),
            1
        );
        for route in [tiny.direct, wide.direct, rational.direct, typed] {
            assert!(core.modes[0].token_ids.contains(&route));
        }
        core.validate()
            .expect("coalesced and dual final routes validate");
    }

    #[test]
    fn capture_macro_declaration_bridge_qualifies_modes_without_rewriting_source_names() {
        let language = declaration_language(quote! {
            name: ModeRoutes,
            types { Proc },
            tokens {
                Open = "open" push(body);
                raw mode body {
                    Chunk = "chunk";
                    Nested = "nested" push(body);
                    Leave = "leave" pop;
                }
                mode other { Chunk = "other" push(body); }
            },
            terms { }
        });
        let spec = crate::gen::syntax::parser::prattail_bridge::language_def_to_spec(&language)
            .expect("mode source uses the original specification bridge");
        let core = spec
            .to_grammar_core()
            .expect("mode token append sites produce their real IDs");
        let store = core.authored.as_ref().expect("mode source owner survives");
        let header = store.declarations().expect("mode source header survives");
        let bindings = core
            .authored_bindings
            .as_ref()
            .expect("mode associations finished");
        assert_eq!(header.global_tokens, [0]);
        assert_eq!(header.modes[0].tokens, [1, 2, 3]);
        assert_eq!(header.modes[1].tokens, [4]);
        assert_eq!(bindings.modes, [ModeId(1), ModeId(2)]);
        let expected = ["Open", "body/Chunk", "body/Nested", "body/Leave", "other/Chunk"];
        for (index, expected) in expected.into_iter().enumerate() {
            let binding = &bindings.tokens[index];
            assert!(binding.typed_literal.is_none());
            let token = &core.tokens[binding.direct.0 as usize];
            assert_eq!(token.name, expected);
            assert!(core.modes[token.mode.0 as usize]
                .token_ids
                .contains(&token.id));
        }
        assert_ne!(bindings.tokens[1].direct, bindings.tokens[4].direct);
        assert_eq!(retained_name(store, header.tokens[1].name).spelling, "Chunk");
        assert_eq!(retained_name(store, header.tokens[4].name).spelling, "Chunk");
        assert_eq!(
            retained_name(store, header.tokens[1].name).equality_class,
            retained_name(store, header.tokens[4].name).equality_class
        );
        for source in [0, 2, 4] {
            let push = header.tokens[source]
                .push
                .expect("source token retains its push target");
            assert_eq!(
                retained_name(store, push).equality_class,
                retained_name(store, header.modes[0].name).equality_class
            );
            assert_eq!(
                core.tokens[bindings.tokens[source].direct.0 as usize]
                    .transition
                    .push,
                Some(bindings.modes[0])
            );
        }
        assert!(
            core.tokens[bindings.tokens[3].direct.0 as usize]
                .transition
                .pop
        );
        assert!(core.modes[bindings.modes[0].0 as usize].raw);
        assert!(!core.modes[bindings.modes[1].0 as usize].raw);
        core.validate()
            .expect("source mode names and final qualified memberships validate");
    }
}
