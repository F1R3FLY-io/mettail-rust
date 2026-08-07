use super::*;
use proc_macro2::{Delimiter, Group, Span, TokenStream, TokenTree};
use quote::quote;
use std::fmt::Write;
use syn::Ident;

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn convert_pattern_op_recursive(
    op: &PatternOp,
    context: &[TermParam],
    cat_names: &[String],
    items: &mut Vec<SyntaxItemSpec>,
) {
    match op {
        PatternOp::Sep { collection, separator, source } => {
            if let Some(source_op) = source {
                convert_chained_sep(source_op, separator, context, cat_names, items);
                return;
            }
            let coll_name = collection.to_string();
            let is_multi_binder = context.iter().any(|param| {
                matches!(param, TermParam::MultiAbstraction { binder, .. }
                    if binder.to_string() == coll_name)
            });
            if is_multi_binder {
                items.push(SyntaxItemSpec::BinderCollection {
                    param_name: coll_name,
                    separator: separator.clone(),
                });
            } else {
                let (element_category, kind, key_val_separator) =
                    find_collection_info(&coll_name, context);
                items.push(SyntaxItemSpec::Collection {
                    param_name: coll_name,
                    element_category,
                    separator: separator.clone(),
                    key_val_separator,
                    kind,
                });
            }
        },
        PatternOp::Zip { left, right } => {
            items.push(classify_param_from_context(&left.to_string(), context, cat_names));
            items.push(classify_param_from_context(&right.to_string(), context, cat_names));
        },
        PatternOp::Map { body, .. } => {
            for expr in body {
                convert_expr_recursive(expr, context, cat_names, items);
            }
        },
        PatternOp::Opt { inner } => {
            let mut inner_items = Vec::new();
            for expr in inner {
                convert_expr_recursive(expr, context, cat_names, &mut inner_items);
            }
            items.push(SyntaxItemSpec::Optional { inner: inner_items });
        },
        PatternOp::Var(name) => {
            items.push(SyntaxItemSpec::IdentCapture { param_name: name.to_string() });
        },
    }
}

fn convert_expr_recursive(
    expr: &SyntaxExpr,
    context: &[TermParam],
    cat_names: &[String],
    items: &mut Vec<SyntaxItemSpec>,
) {
    match expr {
        SyntaxExpr::Literal(text) => items.push(SyntaxItemSpec::Terminal(text.clone())),
        SyntaxExpr::Param(name) => {
            items.push(classify_param_from_context(&name.to_string(), context, cat_names));
        },
        SyntaxExpr::Op(op) => convert_pattern_op_recursive(op, context, cat_names, items),
        SyntaxExpr::TokenKind { name, bind } => {
            let kind_name = name.to_string();
            let param_name = bind
                .as_ref()
                .map(ToString::to_string)
                .unwrap_or_else(|| format!("__tok_{kind_name}"));
            items.push(SyntaxItemSpec::TokenKindCapture { kind_name, param_name });
        },
        SyntaxExpr::GuestBody { open, bind, .. } => {
            items.push(SyntaxItemSpec::TokenKindCapture {
                kind_name: open.to_string(),
                param_name: bind.to_string(),
            });
        },
    }
}

fn snapshot(items: &[SyntaxItemSpec], out: &mut String) {
    for item in items {
        match item {
            SyntaxItemSpec::Terminal(text) => write!(out, "terminal({text:?});").unwrap(),
            SyntaxItemSpec::NonTerminal { category, param_name } => {
                write!(out, "nonterminal({category:?},{param_name:?});").unwrap();
            },
            SyntaxItemSpec::IdentCapture { param_name } => {
                write!(out, "ident({param_name:?});").unwrap();
            },
            SyntaxItemSpec::TokenKindCapture { param_name, kind_name } => {
                write!(out, "token({kind_name:?},{param_name:?});").unwrap();
            },
            SyntaxItemSpec::Binder { param_name, category, is_multi } => {
                write!(out, "binder({param_name:?},{category:?},{is_multi});").unwrap();
            },
            SyntaxItemSpec::Collection {
                param_name,
                element_category,
                separator,
                kind,
                key_val_separator,
            } => {
                write!(
                    out,
                    "collection({param_name:?},{element_category:?},{separator:?},{kind:?},{key_val_separator:?});"
                )
                .unwrap();
            },
            SyntaxItemSpec::Sep { body, separator, kind } => {
                write!(out, "sep({separator:?},{kind:?})[").unwrap();
                snapshot(std::slice::from_ref(body.as_ref()), out);
                out.push_str("];");
            },
            SyntaxItemSpec::Map { body_items } => {
                out.push_str("map[");
                snapshot(body_items, out);
                out.push_str("];");
            },
            SyntaxItemSpec::Zip {
                left_name,
                right_name,
                left_category,
                right_category,
                body,
            } => {
                write!(
                    out,
                    "zip({left_name:?},{right_name:?},{left_category:?},{right_category:?})["
                )
                .unwrap();
                snapshot(std::slice::from_ref(body.as_ref()), out);
                out.push_str("];");
            },
            SyntaxItemSpec::BinderCollection { param_name, separator } => {
                write!(out, "binder_collection({param_name:?},{separator:?});").unwrap();
            },
            SyntaxItemSpec::Optional { inner } => {
                out.push_str("optional[");
                snapshot(inner, out);
                out.push_str("];");
            },
            SyntaxItemSpec::GuardExpression { param_name } => {
                write!(out, "guard({param_name:?});").unwrap();
            },
        }
    }
}

fn collect_constructor_idents_recursive(
    tokens: &TokenStream,
    known_labels: &HashSet<String>,
    labels: &mut HashSet<String>,
) {
    for token in tokens.clone() {
        match token {
            TokenTree::Ident(ident) => {
                let name = ident.to_string();
                if known_labels.contains(&name) {
                    labels.insert(name);
                }
            },
            TokenTree::Group(group) => {
                collect_constructor_idents_recursive(&group.stream(), known_labels, labels);
            },
            _ => {},
        }
    }
}

#[test]
fn pattern_conversion_pda_matches_recursive_equation() {
    let context = vec![
        TermParam::Simple {
            name: ident("xs"),
            ty: TypeExpr::Collection {
                coll_type: CollectionType::Vec,
                element: Box::new(TypeExpr::Base(ident("Proc"))),
            },
        },
        TermParam::MultiAbstraction {
            binder: ident("names"),
            body: ident("body"),
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::MultiBinder(Box::new(TypeExpr::Base(ident("Name"))))),
                codomain: Box::new(TypeExpr::Base(ident("Proc"))),
            },
        },
    ];
    let categories = vec!["Proc".to_string(), "Name".to_string()];
    let fixture = PatternOp::Map {
        source: Box::new(PatternOp::Var(ident("xs"))),
        params: vec![ident("x")],
        body: vec![
            SyntaxExpr::Literal("begin".to_string()),
            SyntaxExpr::Param(ident("body")),
            SyntaxExpr::Op(PatternOp::Zip { left: ident("xs"), right: ident("names") }),
            SyntaxExpr::Op(PatternOp::Opt {
                inner: vec![
                    SyntaxExpr::Op(PatternOp::Sep {
                        collection: ident("xs"),
                        separator: ",".to_string(),
                        source: None,
                    }),
                    SyntaxExpr::Op(PatternOp::Sep {
                        collection: ident("names"),
                        separator: ";".to_string(),
                        source: None,
                    }),
                    SyntaxExpr::TokenKind { name: ident("Word"), bind: None },
                    SyntaxExpr::GuestBody {
                        open: ident("Open"),
                        close: ident("Close"),
                        bind: ident("guest"),
                    },
                ],
            }),
            SyntaxExpr::Op(PatternOp::Var(ident("tail"))),
        ],
    };

    let mut actual = Vec::new();
    convert_pattern_op(&fixture, &context, &categories, &mut actual);
    let mut expected = Vec::new();
    convert_pattern_op_recursive(&fixture, &context, &categories, &mut expected);
    let mut actual_snapshot = String::new();
    let mut expected_snapshot = String::new();
    snapshot(&actual, &mut actual_snapshot);
    snapshot(&expected, &mut expected_snapshot);
    assert_eq!(actual_snapshot, expected_snapshot);
}

#[test]
fn pattern_conversion_pda_handles_20k_nesting_on_a_256k_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut op = PatternOp::Var(ident("leaf"));
            for _ in 0..20_000 {
                op = PatternOp::Opt { inner: vec![SyntaxExpr::Op(op)] };
            }
            let mut items = Vec::new();
            convert_pattern_op(&op, &[], &[], &mut items);
            let mut depth = 0;
            let mut cursor = items.as_slice();
            while let [SyntaxItemSpec::Optional { inner }] = cursor {
                depth += 1;
                cursor = inner.as_slice();
            }
            assert_eq!(depth, 20_000);
            assert!(matches!(cursor, [SyntaxItemSpec::IdentCapture { param_name }] if param_name == "leaf"));
        })
        .expect("spawn low-stack pattern-conversion gate")
        .join()
        .expect("pattern conversion must not consume nesting-proportional native stack");
}

#[test]
fn token_group_walk_matches_recursive_equation_and_handles_20k_nesting() {
    let known: HashSet<_> = ["Outer", "Inner"].into_iter().map(str::to_string).collect();
    let shallow: TokenStream = quote! { Outer(other(Inner)) };
    let mut actual = HashSet::new();
    let mut expected = HashSet::new();
    collect_constructor_idents_from_token_stream(&shallow, &known, &mut actual);
    collect_constructor_idents_recursive(&shallow, &known, &mut expected);
    assert_eq!(actual, expected);

    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let mut tokens: TokenStream =
                std::iter::once(TokenTree::Ident(ident("Inner"))).collect();
            for _ in 0..20_000 {
                let group = Group::new(Delimiter::Parenthesis, tokens);
                tokens = std::iter::once(TokenTree::Group(group)).collect();
            }
            let mut labels = HashSet::new();
            collect_constructor_idents_from_token_stream(&tokens, &known, &mut labels);
            assert_eq!(labels, HashSet::from(["Inner".to_string()]));
            std::mem::forget(tokens);
        })
        .expect("spawn low-stack token-group gate")
        .join()
        .expect("token-group walk must not consume nesting-proportional native stack");
}
