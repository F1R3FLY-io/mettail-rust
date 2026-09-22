//! Baselines against the original macro Parikh helpers before their extraction.

use super::*;
use mettail_ast::grammar::{rule_fixture, DelimitedRegionKind};
use mettail_ast::types::CollectionType;
use proc_macro2::Span;
use syn::Ident;

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn base(name: &str) -> TypeExpr {
    TypeExpr::Base(ident(name))
}

fn simple(name: &str, category: &str) -> TermParam {
    TermParam::Simple { name: ident(name), ty: base(category) }
}

fn literal(text: &str) -> SyntaxExpr {
    SyntaxExpr::Literal(text.into())
}

fn param(name: &str) -> SyntaxExpr {
    SyntaxExpr::Param(ident(name))
}

fn rule(category: &str, context: Vec<TermParam>, syntax: Option<Vec<SyntaxExpr>>) -> GrammarRule {
    GrammarRule {
        term_context: Some(context),
        syntax_pattern: syntax,
        ..rule_fixture(ident("Rule"), ident(category))
    }
}

fn language(terms: Vec<GrammarRule>) -> LanguageDef {
    LanguageDef {
        name: ident("ParikhBaseline"),
        options: Default::default(),
        extends_names: vec![],
        include_names: vec![],
        mixin_names: vec![],
        types: vec![],
        refinement_types: vec![],
        token_defs: vec![],
        mode_defs: vec![],
        sync_constraints: vec![],
        tree_invariants: vec![],
        terms,
        equations: vec![],
        rewrites: vec![],
        logic: None,
        guard_config: None,
    }
}

fn infix(trigger: &str, result: &str) -> GrammarRule {
    rule(
        result,
        vec![simple("a", "Operand"), simple("b", "Operand")],
        Some(vec![param("a"), literal(trigger), param("b")]),
    )
}

fn alpha() -> Alphabet {
    Alphabet {
        trigger_bit: HashMap::from([("early".into(), 0), ("late".into(), 1)]),
        coarse_bit: 2,
    }
}

fn reference(category: &str, target: &str) -> GrammarRule {
    rule(category, vec![simple("p", target)], Some(vec![param("p")]))
}

#[test]
fn original_alphabet_sorts_deduplicates_caps_at_127_and_preserves_coarse_class() {
    let mut terms: Vec<_> = (0..130)
        .rev()
        .map(|index| infix(&format!("trigger{index:03}"), "Result"))
        .collect();
    terms.push(infix("trigger007", "Result"));
    terms.push(infix("not_cross_category", "Operand"));
    terms.push(rule("Result", vec![], Some(vec![literal("not_an_infix")])));
    let alphabet = build_alphabet(&language(terms));
    assert_eq!(alphabet.trigger_bit.len(), 127);
    assert_eq!(alphabet.coarse_bit, 127);
    for index in 0..127 {
        assert_eq!(alphabet.class_of_terminal(&format!("trigger{index:03}")), index as u8);
    }
    for terminal in [
        "trigger127",
        "trigger128",
        "trigger129",
        "not_cross_category",
        "not_an_infix",
        "unknown",
    ] {
        assert_eq!(alphabet.class_of_terminal(terminal), 127);
        assert_eq!(alphabet.mask_of_terminal(terminal), 1u128 << 127);
    }
    assert_eq!(alphabet.top(), u128::MAX);
    let empty = build_alphabet(&language(vec![]));
    assert_eq!(empty.coarse_bit, 0);
    assert_eq!(empty.top(), 1);
    assert_eq!(empty.mask_of_terminal("anything"), 1);
}

#[test]
fn original_parameter_map_is_top_level_ordered_last_supported_write_wins() {
    let arrow = |codomain| TypeExpr::Arrow {
        domain: Box::new(base("IgnoredDomain")),
        codomain: Box::new(codomain),
    };
    let fixture = rule(
        "Result",
        vec![
            simple("x", "First"),
            TermParam::Abstraction {
                binder: ident("binder"),
                body: ident("x"),
                ty: arrow(base("Second")),
            },
            TermParam::Simple {
                name: ident("x"),
                ty: TypeExpr::Collection {
                    coll_type: CollectionType::Vec,
                    element: Box::new(base("IgnoredCollection")),
                },
            },
            TermParam::Optional {
                params: vec![simple("hidden", "IgnoredOptional"), simple("x", "IgnoredOverwrite")],
            },
            TermParam::GuardBody { name: ident("guard") },
            TermParam::Simple {
                name: ident("arrow_simple"),
                ty: arrow(base("IgnoredArrow")),
            },
            TermParam::Abstraction {
                binder: ident("bad_binder"),
                body: ident("bad_body"),
                ty: base("NotAnArrow"),
            },
            TermParam::MultiAbstraction {
                binder: ident("many"),
                body: ident("x"),
                ty: arrow(base("Final")),
            },
            TermParam::MultiAbstraction {
                binder: ident("nested"),
                body: ident("x"),
                ty: arrow(TypeExpr::Collection {
                    coll_type: CollectionType::Vec,
                    element: Box::new(base("NestedCodomain")),
                }),
            },
            simple("y", "Other"),
        ],
        None,
    );
    assert_eq!(
        param_categories(&fixture),
        HashMap::from([("x".into(), "Final".into()), ("y".into(), "Other".into()),])
    );
    let absent = rule_fixture(ident("Absent"), ident("Result"));
    assert!(param_categories(&absent).is_empty());
    assert!(param_categories(&rule("Result", vec![], None)).is_empty());
}

#[test]
fn original_expression_observations_and_suffix_union_keep_nullable_payloads() {
    let alphabet = alpha();
    let params = HashMap::from([
        ("present".into(), "Nullable".into()),
        ("missing_category".into(), "Absent".into()),
    ]);
    let must = HashMap::from([("Nullable".into(), 2)]);
    let nullable = HashMap::from([("Nullable".into(), true)]);
    let observe = |expr: &SyntaxExpr| expr_must(expr, &params, &must, &nullable, &alphabet);
    assert_eq!(observe(&literal("early")), (false, 1));
    assert_eq!(observe(&literal("unknown")), (false, 4));
    assert_eq!(observe(&SyntaxExpr::TokenKind { name: ident("late"), bind: None }), (false, 2));
    assert_eq!(
        observe(&SyntaxExpr::GuestBody {
            open: ident("early"),
            close: ident("late"),
            bind: ident("body"),
            kind: DelimitedRegionKind::Flt
        }),
        (false, 1)
    );
    assert_eq!(observe(&param("present")), (true, 2));
    assert_eq!(observe(&param("missing_category")), (false, 0));
    assert_eq!(observe(&param("unknown")), (true, 0));
    for op in [
        PatternOp::Opt { inner: vec![literal("early")] },
        PatternOp::Sep {
            collection: ident("present"),
            separator: "early".into(),
            source: None,
        },
        PatternOp::Map {
            source: Box::new(PatternOp::Var(ident("present"))),
            params: vec![ident("p")],
            body: vec![literal("late")],
        },
        PatternOp::Zip {
            left: ident("present"),
            right: ident("present"),
        },
        PatternOp::Var(ident("present")),
    ] {
        assert_eq!(observe(&SyntaxExpr::Op(op)), (true, 0));
    }
    let syntax = vec![literal("early"), param("present"), param("unknown")];
    // Freeze the actual original OR, which ignores the nullable flag. Do not
    // silently rewrite it as a nullable-filtering algorithm during relocation.
    assert_eq!(rule_suffix_must(&syntax, 0, &params, &must, &nullable, &alphabet), 3);
    assert_eq!(rule_suffix_must(&syntax, 1, &params, &must, &nullable, &alphabet), 2);
    assert_eq!(rule_suffix_must(&syntax, 2, &params, &must, &nullable, &alphabet), 0);
    assert_eq!(rule_suffix_must(&syntax, 3, &params, &must, &nullable, &alphabet), 0);
    assert_eq!(rule_suffix_must(&syntax, 99, &params, &must, &nullable, &alphabet), 0);
}

#[test]
fn original_fixpoints_distinguish_ungrounded_grounded_nullable_empty_and_synthetic() {
    let categories: Vec<String> = [
        "CycleA",
        "CycleB",
        "GroundA",
        "GroundB",
        "NullA",
        "NullB",
        "Empty",
        "Synthetic",
        "EmptySyntax",
        "Alternatives",
    ]
    .into_iter()
    .map(str::to_string)
    .collect();
    let per_cat = vec![
        vec![reference("CycleA", "CycleB")],
        vec![reference("CycleB", "CycleA")],
        vec![reference("GroundA", "GroundB")],
        vec![
            reference("GroundB", "GroundA"),
            rule("GroundB", vec![], Some(vec![literal("early")])),
        ],
        vec![reference("NullA", "NullB")],
        vec![
            reference("NullB", "NullA"),
            rule(
                "NullB",
                vec![],
                Some(vec![SyntaxExpr::Op(PatternOp::Opt { inner: vec![literal("late")] })]),
            ),
        ],
        vec![],
        vec![rule("Synthetic", vec![], None)],
        vec![rule("EmptySyntax", vec![], Some(vec![]))],
        vec![
            rule("Alternatives", vec![], Some(vec![literal("early")])),
            rule("Alternatives", vec![], Some(vec![literal("late")])),
        ],
    ];
    let (must, nullable) = compute_category_must(&per_cat, &categories, &alpha());
    assert_eq!(
        must,
        HashMap::from([
            ("CycleA".into(), 7),
            ("CycleB".into(), 7),
            ("GroundA".into(), 1),
            ("GroundB".into(), 1),
            ("NullA".into(), 0),
            ("NullB".into(), 0),
            ("Empty".into(), 0),
            ("Synthetic".into(), 4),
            ("EmptySyntax".into(), 4),
            ("Alternatives".into(), 0),
        ])
    );
    for category in &categories {
        assert_eq!(nullable[category], category == "NullA" || category == "NullB", "{category}");
    }
}

fn emitted_function(tokens: &TokenStream, name: &str) -> syn::ItemFn {
    syn::parse2::<syn::File>(tokens.clone())
        .expect("valid emitted Rust")
        .items
        .into_iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == name => Some(function),
            _ => None,
        })
        .expect("expected emitted function")
}

fn integer(expression: &syn::Expr) -> u128 {
    match expression {
        syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(value), .. }) => {
            value.base10_parse().expect("integer value")
        },
        _ => panic!("expected emitted integer"),
    }
}

fn emitted_rows(tokens: &TokenStream) -> Vec<((u16, u16, u8), u128)> {
    let function = emitted_function(tokens, "WPDA_MUST_MASK");
    let [syn::Stmt::Expr(syn::Expr::Match(dispatch), _)] = function.block.stmts.as_slice() else {
        panic!("expected one match expression");
    };
    let mut rows = Vec::new();
    for arm in &dispatch.arms {
        match &arm.pat {
            syn::Pat::Tuple(tuple) => {
                let values: Vec<u128> = tuple
                    .elems
                    .iter()
                    .map(|pattern| match pattern {
                        syn::Pat::Lit(syn::ExprLit { lit: syn::Lit::Int(value), .. }) => {
                            value.base10_parse().expect("index literal")
                        },
                        _ => panic!("expected literal tuple index"),
                    })
                    .collect();
                assert_eq!(values.len(), 3);
                rows.push((
                    (values[0] as u16, values[1] as u16, values[2] as u8),
                    integer(&arm.body),
                ));
            },
            syn::Pat::Wild(_) => assert_eq!(integer(&arm.body), 0),
            _ => panic!("unexpected emitted row pattern"),
        }
    }
    rows
}

#[test]
fn original_suffix_rows_keep_nonzero_position_wrap_overwrites_and_sorted_emission() {
    let authored = language(vec![infix("late", "Result"), infix("early", "Result")]);
    let mut syntax: Vec<_> = (0..258)
        .map(|_| SyntaxExpr::Op(PatternOp::Var(ident("unmodeled"))))
        .collect();
    syntax[0] = literal("early");
    syntax[256] = literal("late");
    let normalized = vec![vec![
        rule("Bucket", vec![], Some(syntax)),
        rule("Bucket", vec![], None),
        rule("Bucket", vec![], Some(vec![])),
        rule("Bucket", vec![], Some(vec![param("unknown")])),
    ]];
    let emission = build_parikh_model(&authored, &["Bucket".into()], &normalized);
    assert_eq!(emission.trigger_class_count, 2);
    assert_eq!(emission.alphabet_size, 3);
    assert_eq!(emission.must_entry_count, 256);
    let rows = emitted_rows(&emission.tokens);
    assert_eq!(rows.len(), 256);
    for (position, row) in rows.iter().enumerate() {
        // Position256 replaces position0's original early|late obligation.
        assert_eq!(*row, ((0, 0, position as u8), 2));
    }
    let function = emitted_function(&emission.tokens, "WPDA_PARIKH_CLASS_OF");
    let [syn::Stmt::Expr(syn::Expr::Match(dispatch), _)] = function.block.stmts.as_slice() else {
        panic!("expected class dispatch match");
    };
    assert_eq!(dispatch.arms.len(), 3);
    for (arm, (text, bit)) in dispatch.arms.iter().zip([("early", 0), ("late", 1)]) {
        let (_, guard) = arm.guard.as_ref().expect("trigger guard");
        let syn::Expr::Binary(comparison) = guard.as_ref() else {
            panic!("trigger equality");
        };
        let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(value), .. }) =
            comparison.right.as_ref()
        else {
            panic!("trigger string");
        };
        assert_eq!(value.value(), text);
        assert_eq!(integer(&arm.body), bit);
    }
    assert!(matches!(dispatch.arms[2].pat, syn::Pat::Wild(_)));
    assert_eq!(integer(&dispatch.arms[2].body), 2);
}

#[test]
fn original_zero_suffix_does_not_erase_an_earlier_colliding_position_key() {
    let authored = language(vec![infix("early", "Result")]);
    let mut syntax: Vec<_> = (0..257).map(|_| param("unknown")).collect();
    syntax[0] = literal("early");
    let emission = build_parikh_model(
        &authored,
        &["Bucket".into()],
        &[vec![rule("Bucket", vec![], Some(syntax))]],
    );
    assert_eq!(emission.must_entry_count, 1);
    assert_eq!(emitted_rows(&emission.tokens), vec![((0, 0, 0), 1)]);
}
