use mettail_ast::{
    grammar::{PatternOp, SyntaxExpr, TermParam},
    types::TypeExpr,
};
use proc_macro2::{Ident, Span};

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn nested_optional_param(depth: usize) -> TermParam {
    let mut param = TermParam::Simple {
        name: ident("x"),
        ty: TypeExpr::Base(ident("Term")),
    };
    for _ in 0..depth {
        param = TermParam::Optional { params: vec![param] };
    }
    param
}

fn optional_param_depth(mut param: &TermParam) -> usize {
    let mut depth = 0;
    loop {
        match param {
            TermParam::Optional { params } => {
                assert_eq!(params.len(), 1);
                param = &params[0];
                depth += 1;
            },
            TermParam::Simple { name, ty } => {
                assert_eq!(name, "x");
                assert!(matches!(ty, TypeExpr::Base(category) if category == "Term"));
                return depth;
            },
            _ => panic!("expected an Optional/Single TermParam chain"),
        }
    }
}

fn nested_optional_syntax(depth: usize) -> SyntaxExpr {
    let mut expr = SyntaxExpr::Literal("leaf".to_string());
    for _ in 0..depth {
        expr = SyntaxExpr::Op(PatternOp::Opt { inner: vec![expr] });
    }
    expr
}

fn optional_syntax_depth(mut expr: &SyntaxExpr) -> usize {
    let mut depth = 0;
    loop {
        match expr {
            SyntaxExpr::Op(PatternOp::Opt { inner }) => {
                assert_eq!(inner.len(), 1);
                expr = &inner[0];
                depth += 1;
            },
            SyntaxExpr::Literal(value) => {
                assert_eq!(value, "leaf");
                return depth;
            },
            _ => panic!("expected an Op/Opt/SyntaxExpr chain"),
        }
    }
}

#[test]
fn grammar_lifecycle_debug_preserves_derived_shapes() {
    let param = TermParam::Optional {
        params: vec![TermParam::GuardBody { name: ident("guard") }],
    };
    assert_eq!(
        format!("{param:?}"),
        "Optional { params: [GuardBody { name: Ident { sym: guard } }] }",
    );
    assert_eq!(
        format!("{param:#?}"),
        "Optional {\n    params: [\n        GuardBody {\n            name: Ident {\n                sym: guard,\n            },\n        },\n    ],\n}",
    );

    let expr = SyntaxExpr::Op(PatternOp::Opt {
        inner: vec![SyntaxExpr::Literal("leaf".to_string())],
    });
    assert_eq!(format!("{expr:?}"), "Op(Opt { inner: [Literal(\"leaf\")] })");
    assert_eq!(
        format!("{expr:#?}"),
        "Op(\n    Opt {\n        inner: [\n            Literal(\n                \"leaf\",\n            ),\n        ],\n    },\n)",
    );

    let op = PatternOp::Map {
        source: Box::new(PatternOp::Sep {
            collection: ident("xs"),
            separator: ",".to_string(),
            source: Some(Box::new(PatternOp::Zip { left: ident("xs"), right: ident("ys") })),
        }),
        params: vec![ident("x"), ident("y")],
        body: vec![
            SyntaxExpr::Param(ident("x")),
            SyntaxExpr::TokenKind {
                name: ident("Comma"),
                bind: Some(ident("comma")),
            },
            SyntaxExpr::GuestBody {
                open: ident("Open"),
                close: ident("Close"),
                bind: ident("guest"),
            },
        ],
    };
    assert_eq!(format!("{op:?}"), format!("{:?}", op.clone()));
    assert_eq!(format!("{op:#?}"), format!("{:#?}", op.clone()));
}

#[test]
fn grammar_lifecycle_handles_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("grammar-ast-lifecycle-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let param = nested_optional_param(DEPTH);
            let cloned = param.clone();
            assert_eq!(optional_param_depth(&param), DEPTH);
            assert_eq!(optional_param_depth(&cloned), DEPTH);
            let rendered = format!("{param:?}");
            assert!(rendered.starts_with("Optional { params: [Optional"));
            assert!(rendered
                .contains("Simple { name: Ident { sym: x }, ty: Base(Ident { sym: Term }) }"));
            drop(cloned);
            drop(param);

            let expr = nested_optional_syntax(DEPTH);
            let cloned = expr.clone();
            assert_eq!(optional_syntax_depth(&expr), DEPTH);
            assert_eq!(optional_syntax_depth(&cloned), DEPTH);
            let rendered = format!("{expr:?}");
            assert!(rendered.starts_with("Op(Opt { inner: [Op(Opt"));
            assert!(rendered.contains("Literal(\"leaf\")"));
            drop(cloned);
            drop(expr);
        })
        .expect("small-stack grammar lifecycle thread must spawn")
        .join()
        .expect("grammar AST lifecycle must not overflow the native stack");
}
