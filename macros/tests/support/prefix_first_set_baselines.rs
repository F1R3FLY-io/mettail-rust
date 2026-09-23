//! Original FIRST behavior snapshots, before moving its implementation.
//! Expected token rows include ordering and both provenance fields; these are
//! relocation baselines, not a claim that FIRST completely describes a language.

use super::*;
use mettail_ast::grammar::{rule_fixture, DelimitedRegionKind, SyntaxExpr, TermParam};
use mettail_ast::language::{CategoryRole, CollectionCategory, CollectionDelimiters, LangType};
use mettail_ast::types::TypeExpr;
use proc_macro2::Span;
use syn::parse_quote;

type Row = (String, Option<String>, Option<String>, bool);

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn language() -> LanguageDef {
    LanguageDef {
        name: ident("FirstBaseline"),
        options: Default::default(),
        extends_names: Vec::new(),
        include_names: Vec::new(),
        mixin_names: Vec::new(),
        types: Vec::new(),
        refinement_types: Vec::new(),
        token_defs: Vec::new(),
        mode_defs: Vec::new(),
        sync_constraints: Vec::new(),
        tree_invariants: Vec::new(),
        terms: Vec::new(),
        equations: Vec::new(),
        rewrites: Vec::new(),
        logic: None,
        guard_config: None,
    }
}

fn category(name: &str, role: CategoryRole) -> LangType {
    LangType {
        name: ident(name),
        role,
        native_type: None,
        collection_kind: None,
    }
}

fn terminal(label: &str, category: &str, text: &str) -> GrammarRule {
    GrammarRule {
        items: vec![GrammarItem::Terminal(text.into())],
        ..rule_fixture(ident(label), ident(category))
    }
}

fn projection(label: &str, category: &str, source: &str) -> GrammarRule {
    GrammarRule {
        term_context: Some(vec![TermParam::Simple {
            name: ident("x"),
            ty: TypeExpr::Base(ident(source)),
        }]),
        syntax_pattern: Some(vec![SyntaxExpr::Param(ident("x"))]),
        ..rule_fixture(ident(label), ident(category))
    }
}

fn row(pattern: TokenStream, guard: Option<TokenStream>, leading: Option<&str>, var: bool) -> Row {
    (
        pattern.to_string(),
        guard.map(|g| g.to_string()),
        leading.map(str::to_string),
        var,
    )
}

fn fixed(text: &str) -> Row {
    row(
        quote! { Some(mettail_prattail::automata::TokenKind::Fixed(__kw)) },
        Some(quote! { __kw == #text }),
        Some(text),
        false,
    )
}

fn rows(category: &str, language: &LanguageDef) -> Vec<Row> {
    first_set_of_category(category, language)
        .into_iter()
        .map(|token| {
            (
                token.pattern.to_string(),
                token.extra_guard.map(|g| g.to_string()),
                token.leading_literal,
                token.is_var_contribution,
            )
        })
        .collect()
}

#[test]
fn first_set_baseline_fifo_cycles_duplicates_and_undeclared_sources() {
    let mut language = language();
    language.types = ["A", "B", "C", "D"]
        .into_iter()
        .map(|name| category(name, CategoryRole::Data))
        .collect();
    language.terms = vec![
        projection("AB", "A", "B"),
        terminal("AWord", "A", "a"),
        projection("AC", "A", "C"),
        projection("AU", "A", "Undeclared"),
        projection("BD", "B", "D"),
        terminal("BWord", "B", "b"),
        projection("CD", "C", "D"),
        terminal("CWord", "C", "c"),
        terminal("UWord", "Undeclared", "u"),
        projection("DA", "D", "A"),
        terminal("DWord", "D", "d"),
        terminal("RepeatedA", "D", "a"),
    ];
    assert_eq!(rows("A", &language), ["a", "b", "c", "u", "d"].map(fixed));
    assert_eq!(rows("Undeclared", &language), vec![fixed("u")]);
}

#[test]
fn first_set_baseline_syntax_presence_controls_each_distinct_fallback() {
    let mut language = language();
    language.types = vec![category("A", CategoryRole::Data), category("B", CategoryRole::Data)];
    let mut absent = terminal("Absent", "A", "legacy");
    absent.syntax_pattern = None;
    let mut empty = terminal("Empty", "A", "hidden_empty");
    empty.syntax_pattern = Some(Vec::new());
    let mut param = terminal("Param", "A", "hidden_param");
    param.syntax_pattern = Some(vec![SyntaxExpr::Param(ident("x"))]);
    let mut literal = terminal("Literal", "A", "hidden_literal");
    literal.syntax_pattern = Some(vec![SyntaxExpr::Literal("preferred".into())]);
    language.terms = vec![absent, empty, param, literal];
    assert_eq!(
        category_leading_literals("A", &language),
        ["legacy".to_string(), "preferred".to_string()]
            .into_iter()
            .collect()
    );

    for syntax in [None, Some(Vec::new()), Some(vec![SyntaxExpr::Param(ident("x"))])] {
        let present_param = syntax.as_ref().is_some_and(|items| !items.is_empty());
        let rule = GrammarRule {
            syntax_pattern: syntax,
            items: vec![GrammarItem::NonTerminal {
                ident: ident("B"),
                kind: NonTerminalKind::Category,
            }],
            ..rule_fixture(ident("Fallback"), ident("A"))
        };
        assert!(matches!(classify_atomic(&rule, &language), AtomicShape::NonAtomic));
        language.terms = vec![rule, terminal("BWord", "B", "b")];
        assert_eq!(
            rows("A", &language),
            if present_param {
                vec![fixed("b")]
            } else {
                Vec::new()
            }
        );
    }
}

#[test]
fn first_set_baseline_binder_leading_category_precedes_legacy_category() {
    let mut language = language();
    language.types = ["A", "B", "C"]
        .into_iter()
        .map(|name| category(name, CategoryRole::Data))
        .collect();
    let mut rule = projection("BinderLeading", "A", "B");
    rule.syntax_pattern
        .as_mut()
        .expect("judgement syntax exists")
        .push(SyntaxExpr::Literal("!".into()));
    rule.items = vec![GrammarItem::NonTerminal {
        ident: ident("C"),
        kind: NonTerminalKind::Category,
    }];
    assert!(matches!(classify_atomic(&rule, &language), AtomicShape::NonAtomic));
    assert_eq!(
        super::super::binder::classify_binder_in(&rule, &language)
            .expect("original binder accepts category-led literal tail")
            .leading_category,
        Some("B".into())
    );
    language.terms = vec![rule, terminal("BWord", "B", "b"), terminal("CWord", "C", "c")];
    assert_eq!(rows("A", &language), vec![fixed("b")]);
}

#[test]
fn first_set_baseline_any_first_legacy_var_suppresses_synthetic_var() {
    let mut language = language();
    language.types = vec![category("Open", CategoryRole::Object)];
    assert_eq!(
        rows("Open", &language),
        vec![row(
            quote! { Some(mettail_prattail::automata::TokenKind::Ident) },
            None,
            None,
            true
        )]
    );
    let rule = GrammarRule {
        items: vec![
            GrammarItem::NonTerminal {
                ident: ident("Different"),
                kind: NonTerminalKind::Var,
            },
            GrammarItem::Terminal("tail".into()),
        ],
        ..rule_fixture(ident("NotAtomicVar"), ident("Open"))
    };
    assert!(matches!(classify_atomic(&rule, &language), AtomicShape::NonAtomic));
    language.terms.push(rule);
    assert_eq!(rows("Open", &language), Vec::new());
}

#[test]
fn first_set_baseline_capture_and_guest_preserve_distinct_quote_keys() {
    let mut language = language();
    language.types = vec![category("A", CategoryRole::Object)];
    language.terms = vec![
        GrammarRule {
            term_context: Some(Vec::new()),
            syntax_pattern: Some(vec![SyntaxExpr::TokenKind { name: ident("Ident"), bind: None }]),
            ..rule_fixture(ident("Captured"), ident("A"))
        },
        GrammarRule {
            term_context: Some(Vec::new()),
            syntax_pattern: Some(vec![SyntaxExpr::GuestBody {
                open: ident("Ident"),
                close: ident("Close"),
                bind: ident("body"),
                kind: DelimitedRegionKind::Flt,
            }]),
            ..rule_fixture(ident("Guest"), ident("A"))
        },
    ];
    let kind_name = "Ident";
    assert_eq!(
        rows("A", &language),
        vec![
            row(quote! { Some(mettail_prattail::automata::TokenKind::Ident) }, None, None, true),
            row(
                quote! { Some(ref __kind) },
                Some(quote! {
                    mettail_prattail::automata::token_kind_matches_capture_name(
                        #kind_name,
                        __kind,
                    )
                }),
                None,
                false,
            ),
            row(
                quote! { Some(mettail_prattail::automata::TokenKind::Custom(ref __k)) },
                Some(quote! { __k == #kind_name }),
                None,
                false,
            ),
        ]
    );
}

#[test]
fn first_set_baseline_builtin_scalar_quotes_keep_boolean_union_one_row() {
    let mut language = language();
    language.types = vec![category("A", CategoryRole::Data)];
    language.terms = [
        NonTerminalKind::Boolean,
        NonTerminalKind::StringLiteral,
        NonTerminalKind::FloatLiteral,
    ]
    .into_iter()
    .enumerate()
    .map(|(index, kind)| GrammarRule {
        items: vec![GrammarItem::NonTerminal { ident: ident("ignored"), kind }],
        ..rule_fixture(ident(&format!("Scalar{index}")), ident("A"))
    })
    .collect();
    assert_eq!(
        rows("A", &language),
        vec![
            row(
                quote! {
                    Some(mettail_prattail::automata::TokenKind::True)
                    | Some(mettail_prattail::automata::TokenKind::False)
                    | Some(mettail_prattail::automata::TokenKind::BooleanLit)
                },
                None,
                None,
                false,
            ),
            row(
                quote! { Some(mettail_prattail::automata::TokenKind::StringLit) },
                None,
                None,
                false
            ),
            row(quote! { Some(mettail_prattail::automata::TokenKind::Float) }, None, None, false),
        ]
    );
}

#[test]
fn first_set_baseline_first_declaration_and_collection_trim_all_trailing_opens() {
    let mut language = language();
    let mut collection = category("C", CategoryRole::Data);
    for open in ["list(((", "((("] {
        collection.collection_kind = Some(CollectionCategory::List(CollectionDelimiters {
            open: open.into(),
            close: ")".into(),
            sep: ",".into(),
            key_val_sep: None,
        }));
        language.types = vec![collection.clone()];
        assert_eq!(rows("C", &language), vec![fixed(open.trim_end_matches('('))]);
        language
            .types
            .insert(0, category("C", CategoryRole::Object));
        assert_eq!(
            rows("C", &language),
            vec![row(
                quote! { Some(mettail_prattail::automata::TokenKind::Ident) },
                None,
                None,
                true
            )]
        );
    }
}

#[test]
fn first_set_baseline_native_seed_order_dedup_and_bigint_context() {
    let mut language = language();
    let mut native = category("Num", CategoryRole::Data);
    native.native_type = Some(parse_quote!(i32));
    language.types.push(native);
    language.terms = vec![
        terminal("Word", "Num", "word"),
        GrammarRule {
            items: vec![GrammarItem::NonTerminal {
                ident: ident("Integer"),
                kind: NonTerminalKind::Integer,
            }],
            ..rule_fixture(ident("LegacyInteger"), ident("Num"))
        },
    ];
    let category_name = "Num";
    let typed = row(
        quote! { Some(mettail_prattail::automata::TokenKind::IntegerLit(__cat)) },
        Some(quote! { __cat == #category_name }),
        None,
        false,
    );
    let custom = row(
        quote! { Some(mettail_prattail::automata::TokenKind::Custom(__cat)) },
        Some(quote! { __cat == #category_name }),
        None,
        false,
    );
    let bare = row(
        quote! { Some(mettail_prattail::automata::TokenKind::Integer) },
        None,
        None,
        false,
    );
    assert_eq!(rows("Num", &language), vec![typed.clone(), custom.clone(), bare, fixed("word")]);
    language.types[0].native_type = Some(parse_quote!(CanonicalBigInt));
    language.terms.clear();
    assert_eq!(rows("Num", &language), vec![typed, custom]);
}
