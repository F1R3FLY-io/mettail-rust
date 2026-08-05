use mettail_ast::{
    language::LanguageDef,
    pattern::{Pattern, PatternTerm},
};
use proc_macro2::{Ident, Span};
use std::collections::HashSet;

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn leaf() -> Pattern {
    Pattern::Term(PatternTerm::Apply {
        constructor: ident("Leaf"),
        args: Vec::new(),
    })
}

fn nested_apply(depth: usize) -> Pattern {
    let mut pattern = leaf();
    for _ in 0..depth {
        pattern = Pattern::Term(PatternTerm::Apply {
            constructor: ident("Node"),
            args: vec![pattern],
        });
    }
    pattern
}

fn apply_depth(pattern: &Pattern) -> usize {
    let mut depth = 0;
    let mut pattern = pattern;
    loop {
        let Pattern::Term(PatternTerm::Apply { constructor, args }) = pattern else {
            panic!("expected an Apply chain");
        };
        if constructor == "Leaf" {
            assert!(args.is_empty());
            return depth;
        }
        assert_eq!(constructor, "Node");
        assert_eq!(args.len(), 1);
        depth += 1;
        pattern = &args[0];
    }
}

fn nested_multi_subst(depth: usize) -> Pattern {
    let mut scope = Pattern::Term(PatternTerm::Var(ident("free")));
    for _ in 0..depth {
        scope = Pattern::Term(PatternTerm::MultiSubst {
            scope: Box::new(scope),
            replacements: Vec::new(),
        });
    }
    scope
}

fn multi_subst_depth(term: &PatternTerm) -> usize {
    let mut depth = 0;
    let mut term = term;
    loop {
        match term {
            PatternTerm::MultiSubst { scope, replacements } => {
                assert!(replacements.is_empty());
                let Pattern::Term(inner) = scope.as_ref() else {
                    panic!("expected a PatternTerm scope");
                };
                depth += 1;
                term = inner;
            },
            PatternTerm::Var(name) => {
                assert_eq!(name, "free");
                return depth;
            },
            _ => panic!("expected a MultiSubst chain"),
        }
    }
}

#[test]
fn compact_and_alternate_debug_preserve_the_derived_shape() {
    let pattern = nested_apply(1);
    assert_eq!(
        format!("{pattern:?}"),
        "Term(Apply { constructor: Ident { sym: Node }, args: [Term(Apply { constructor: Ident { sym: Leaf }, args: [] })] })",
    );
    assert_eq!(
        format!("{pattern:#?}"),
        "Term(\n    Apply {\n        constructor: Ident {\n            sym: Node,\n        },\n        args: [\n            Term(\n                Apply {\n                    constructor: Ident {\n                        sym: Leaf,\n                    },\n                    args: [],\n                },\n            ),\n        ],\n    },\n)",
    );
}

#[test]
fn deep_pattern_lifecycle_and_queries_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("pattern-lifecycle-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let language = syn::parse_str::<LanguageDef>(
                r#"
                    name: PatternStack,
                    types { Term }
                    terms {
                        Leaf . |- "leaf" : Term ;
                        Node . child:Term |- "node" child : Term ;
                    }
                    equations {}
                    rewrites {}
                "#,
            )
            .expect("stack-safety fixture language must parse");

            let pattern = nested_apply(DEPTH);
            let cloned = pattern.clone();
            assert_eq!(apply_depth(&pattern), DEPTH);
            assert_eq!(apply_depth(&cloned), DEPTH);
            assert!(pattern.free_vars().is_empty());
            assert!(pattern.var_occurrences().is_empty());
            assert!(pattern.is_ground_pattern(&language));
            assert_eq!(pattern.category(&language).map(ToString::to_string), Some("Term".into()));
            let mut labels = HashSet::new();
            pattern.collect_constructor_labels(&mut labels);
            assert_eq!(labels, HashSet::from(["Leaf".to_string(), "Node".to_string()]));
            let debug = format!("{pattern:?}");
            assert!(debug.starts_with("Term(Apply { constructor: Ident { sym: Node }"));
            assert!(debug.ends_with("] })"));
            assert!(debug.len() > DEPTH * 16);
            drop(cloned);
            drop(pattern);

            let pattern = nested_multi_subst(DEPTH);
            let Pattern::Term(term) = &pattern else {
                unreachable!("the construction always produces a term")
            };
            let cloned = term.clone();
            assert_eq!(multi_subst_depth(&term), DEPTH);
            assert_eq!(multi_subst_depth(&cloned), DEPTH);
            assert_eq!(term.free_vars(), HashSet::from(["free".to_string()]));
            assert!(term.category(&language).is_none());
            let _ = term.span();
            drop(cloned);
            drop(pattern);
        })
        .expect("small-stack Pattern lifecycle thread must spawn");
    handle
        .join()
        .expect("Pattern lifecycle and queries must not overflow the native stack");
}
