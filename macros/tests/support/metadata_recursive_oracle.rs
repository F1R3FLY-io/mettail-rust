//! Test-only recursive equations superseded by the metadata rendering PDAs.
//! Only bounded corpus values are passed to these functions.

use super::*;

fn recursive_type_expr_to_string(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Base(ident) => ident.to_string(),
        TypeExpr::Collection { coll_type, element } => format!(
            "{}({})",
            collection_type_name(coll_type),
            recursive_type_expr_to_string(element)
        ),
        TypeExpr::Map { key, value } => format!(
            "HashMap({}, {})",
            recursive_type_expr_to_string(key),
            recursive_type_expr_to_string(value)
        ),
        TypeExpr::Arrow { domain, codomain } => format!(
            "[{} -> {}]",
            recursive_type_expr_to_string(domain),
            recursive_type_expr_to_string(codomain)
        ),
        TypeExpr::MultiBinder(inner) => format!("{}*", recursive_type_expr_to_string(inner)),
        TypeExpr::Refined { base, .. } => recursive_type_expr_to_string(base),
    }
}

/// Whether `rule` renders as exactly its single argument and nothing else.
///
/// This classifier and the comparator below are test oracles, not production
/// metadata traversal. Keeping them under `tests/support` prevents the source
/// recursion census from mistaking their bounded recursive equation for a live
/// runtime path.
fn is_display_transparent(rule: &GrammarRule) -> bool {
    match &rule.syntax_pattern {
        Some(syntax_pattern) => {
            syntax_pattern.len() == 1 && matches!(syntax_pattern[0], SyntaxExpr::Param(_))
        },
        None => rule.items.len() == 1 && matches!(rule.items[0], GrammarItem::NonTerminal { .. }),
    }
}

fn erase_transparent<'a>(pattern: &'a Pattern, language: &LanguageDef) -> &'a Pattern {
    let mut current = pattern;
    loop {
        let Pattern::Term(PatternTerm::Apply { constructor, args }) = current else {
            return current;
        };
        if args.len() != 1 {
            return current;
        }
        let Some(rule) = language.get_constructor(constructor) else {
            return current;
        };
        if !is_display_transparent(rule) {
            return current;
        }
        current = &args[0];
    }
}

/// Structural equality after erasing display-transparent wrappers.
pub(super) fn equal_modulo_transparent(a: &Pattern, b: &Pattern, language: &LanguageDef) -> bool {
    let (a, b) = (erase_transparent(a, language), erase_transparent(b, language));
    match (a, b) {
        (Pattern::Term(x), Pattern::Term(y)) => match (x, y) {
            (PatternTerm::Var(u), PatternTerm::Var(v)) => u == v,
            (
                PatternTerm::Apply { constructor: cx, args: ax },
                PatternTerm::Apply { constructor: cy, args: ay },
            ) => {
                cx == cy
                    && ax.len() == ay.len()
                    && ax
                        .iter()
                        .zip(ay.iter())
                        .all(|(p, q)| equal_modulo_transparent(p, q, language))
            },
            _ => false,
        },
        _ => false,
    }
}

struct RecursiveRuleBp {
    own_left_bp: u8,
    child_min_bps: Vec<u8>,
}

fn recursive_rule_bp(
    label: &str,
    arg_slots: usize,
    bp: &crate::gen::syntax::display::BpLookup,
) -> Option<RecursiveRuleBp> {
    if let Some(info) = bp.infix.get(label) {
        let child_min_bps = if info.is_postfix {
            vec![info.left_bp; arg_slots]
        } else if info.is_mixfix {
            (0..arg_slots)
                .map(|index| {
                    if index == 0 {
                        info.left_bp
                    } else if index + 1 == arg_slots {
                        info.right_bp
                    } else {
                        0
                    }
                })
                .collect()
        } else {
            (0..arg_slots)
                .map(|index| {
                    if index == 0 {
                        info.left_bp
                    } else {
                        info.right_bp
                    }
                })
                .collect()
        };
        return Some(RecursiveRuleBp { own_left_bp: info.left_bp, child_min_bps });
    }
    bp.prefix.get(label).map(|prefix| RecursiveRuleBp {
        own_left_bp: prefix.prefix_bp,
        child_min_bps: vec![prefix.prefix_bp; arg_slots],
    })
}

fn recursive_child_min_bp(bp: Option<&RecursiveRuleBp>, index: usize) -> u8 {
    bp.and_then(|bp| bp.child_min_bps.get(index).copied())
        .unwrap_or(0)
}

fn recursive_syntax_pattern_to_string(pattern: &[SyntaxExpr]) -> String {
    let mut result = String::new();
    for expression in pattern {
        match expression {
            SyntaxExpr::Literal(text) => result.push_str(text),
            SyntaxExpr::Param(ident) => result.push_str(&ident.to_string()),
            SyntaxExpr::Op(operation) => {
                result.push_str(&recursive_pattern_op_to_string(operation));
            },
            SyntaxExpr::TokenKind { name, bind } => {
                if let Some(bind) = bind {
                    result.push_str(&bind.to_string());
                    result.push('@');
                }
                result.push_str(&name.to_string());
            },
            SyntaxExpr::GuestBody { open, close, bind, kind } => {
                result.push_str(&format!("*{}({bind},{open},{close})", kind.intrinsic()));
            },
        }
    }
    result
}

fn recursive_pattern_op_to_string(operation: &PatternOp) -> String {
    match operation {
        PatternOp::Sep { collection, separator, source } => {
            if let Some(source) = source {
                format!("{}, ...", recursive_chained_element_pattern(source))
            } else {
                format!("{collection} {separator} ...")
            }
        },
        PatternOp::Var(ident) => ident.to_string(),
        PatternOp::Opt { inner } => {
            format!("[{}]", recursive_syntax_pattern_to_string(inner))
        },
        PatternOp::Zip { left, right } => format!("({left}, {right})"),
        PatternOp::Map { params, body, .. } => {
            let body = recursive_syntax_pattern_to_string(body);
            let params = params.iter().map(ToString::to_string).collect::<Vec<_>>();
            if params.len() > 1 {
                body
            } else {
                format!("|{}| {body}", params.join(", "))
            }
        },
    }
}

fn recursive_chained_element_pattern(operation: &PatternOp) -> String {
    match operation {
        PatternOp::Map { body, .. } => recursive_syntax_pattern_to_string(body),
        _ => "...".to_owned(),
    }
}

fn recursive_nullary_surface(name: &syn::Ident, ctx: RenderCtx<'_>) -> Option<String> {
    let rule = ctx.language.get_constructor(name)?;
    let takes_arguments = match (&rule.term_context, &rule.syntax_pattern) {
        (Some(term_context), _) => !term_context.is_empty(),
        (None, _) => rule.items.iter().any(|item| {
            matches!(
                item,
                GrammarItem::NonTerminal { .. }
                    | GrammarItem::Collection { .. }
                    | GrammarItem::Binder { .. }
            )
        }),
    };
    if takes_arguments {
        return None;
    }
    Some(match &rule.syntax_pattern {
        Some(syntax) => recursive_apply_args_to_syntax(syntax, &[], ctx, None),
        None => recursive_build_syntax_from_grammar(rule, &[], ctx, None),
    })
}

fn recursive_render_pattern(pattern: &Pattern, ctx: RenderCtx<'_>, min_bp: u8) -> String {
    match pattern {
        Pattern::Term(term) => recursive_render_term(term, ctx, min_bp),
        Pattern::Collection { elements, rest, .. } => {
            let mut parts = elements
                .iter()
                .map(|element| recursive_render_pattern(element, ctx, 0))
                .collect::<Vec<_>>();
            if let Some(rest) = rest {
                parts.push(format!("...{rest}"));
            }
            format!("{{{}}}", parts.join(" | "))
        },
        Pattern::Map { collection, params, body } => format!(
            "{}.*map(|{}| {})",
            recursive_render_pattern(collection, ctx, 0),
            params
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", "),
            recursive_render_pattern(body, ctx, 0),
        ),
        Pattern::Zip { first, second } => format!(
            "*zip({}, {})",
            recursive_render_pattern(first, ctx, 0),
            recursive_render_pattern(second, ctx, 0),
        ),
        Pattern::IndexedVec { collection, index, element } => {
            format!("{collection}[{index} := {}]", recursive_render_pattern(element, ctx, 0),)
        },
    }
}

fn recursive_render_term(term: &PatternTerm, ctx: RenderCtx<'_>, min_bp: u8) -> String {
    match term {
        PatternTerm::Var(name) => {
            recursive_nullary_surface(name, ctx).unwrap_or_else(|| name.to_string())
        },
        PatternTerm::Apply { constructor, args } => {
            if let Some(rule) = ctx
                .language
                .terms
                .iter()
                .find(|rule| &rule.label == constructor)
            {
                let bp = recursive_rule_bp(&constructor.to_string(), args.len(), ctx.bp);
                let rendered = match &rule.syntax_pattern {
                    Some(syntax) => recursive_apply_args_to_syntax(syntax, args, ctx, bp.as_ref()),
                    None => recursive_build_syntax_from_grammar(rule, args, ctx, bp.as_ref()),
                };
                if bp.as_ref().is_some_and(|bp| bp.own_left_bp < min_bp) {
                    format!("({rendered})")
                } else {
                    rendered
                }
            } else if args.is_empty() {
                constructor.to_string()
            } else {
                let args = args
                    .iter()
                    .map(|argument| recursive_render_pattern(argument, ctx, 0))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("({constructor} {args})")
            }
        },
        PatternTerm::Lambda { binder, body } => {
            format!("^{binder}.{{{}}}", recursive_render_pattern(body, ctx, 0))
        },
        PatternTerm::MultiLambda { binders, body } => format!(
            "^[{}].{{{}}}",
            binders
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", "),
            recursive_render_pattern(body, ctx, 0),
        ),
        PatternTerm::Subst { term, var, replacement } => format!(
            "{}[{}/{var}]",
            recursive_render_pattern(term, ctx, 0),
            recursive_render_pattern(replacement, ctx, 0),
        ),
        PatternTerm::MultiSubst { scope, replacements } => format!(
            "{}[{}]",
            recursive_render_pattern(scope, ctx, 0),
            replacements
                .iter()
                .map(|replacement| recursive_render_pattern(replacement, ctx, 0))
                .collect::<Vec<_>>()
                .join(", "),
        ),
    }
}

fn recursive_apply_args_to_syntax(
    syntax: &[SyntaxExpr],
    args: &[Pattern],
    ctx: RenderCtx<'_>,
    bp: Option<&RecursiveRuleBp>,
) -> String {
    let mut result = String::new();
    let mut args = args.iter();
    let mut slot = 0;
    let mut current_lambda: Option<&Pattern> = None;
    for expression in syntax {
        match expression {
            SyntaxExpr::Literal(text) => result.push_str(text),
            SyntaxExpr::TokenKind { name, .. } => result.push_str(&name.to_string()),
            SyntaxExpr::GuestBody { open, .. } => result.push_str(&open.to_string()),
            SyntaxExpr::Param(ident) => {
                let ident = ident.to_string();
                if let Some(Pattern::Term(PatternTerm::Lambda { binder, body })) = current_lambda {
                    if ident == binder.to_string() {
                        result.push_str(&ident);
                        continue;
                    }
                    result.push_str(&recursive_render_pattern(body, ctx, 0));
                    current_lambda = None;
                    continue;
                }
                if let Some(argument) = args.next() {
                    let inherited = recursive_child_min_bp(bp, slot);
                    slot += 1;
                    if let Pattern::Term(PatternTerm::Lambda { binder, .. }) = argument {
                        current_lambda = Some(argument);
                        result.push_str(&binder.to_string());
                    } else {
                        result.push_str(&recursive_render_pattern(argument, ctx, inherited));
                    }
                }
            },
            SyntaxExpr::Op(operation) => {
                if let PatternOp::Sep { separator, source, .. } = operation {
                    if let Some(argument) = args.next() {
                        slot += 1;
                        if source.is_some() {
                            result.push_str(&recursive_pattern_op_to_string(operation));
                        } else {
                            result.push_str(&recursive_render_collection(argument, separator, ctx));
                        }
                    } else {
                        result.push_str(&recursive_pattern_op_to_string(operation));
                    }
                } else {
                    result.push_str(&recursive_pattern_op_to_string(operation));
                }
            },
        }
    }
    result
}

fn recursive_render_collection(pattern: &Pattern, separator: &str, ctx: RenderCtx<'_>) -> String {
    match pattern {
        Pattern::Collection { elements, rest, .. } => {
            let mut parts = elements
                .iter()
                .map(|element| recursive_render_pattern(element, ctx, 0))
                .collect::<Vec<_>>();
            if let Some(rest) = rest {
                parts.push(format!("...{rest}"));
            }
            parts.join(&format!(" {separator} "))
        },
        _ => recursive_render_pattern(pattern, ctx, 0),
    }
}

fn recursive_build_syntax_from_grammar(
    rule: &GrammarRule,
    args: &[Pattern],
    ctx: RenderCtx<'_>,
    bp: Option<&RecursiveRuleBp>,
) -> String {
    let mut result = String::new();
    let mut args = args.iter();
    let mut slot = 0;
    for item in &rule.items {
        match item {
            GrammarItem::Terminal(text) => result.push_str(text),
            GrammarItem::NonTerminal { .. } => {
                if let Some(argument) = args.next() {
                    let inherited = recursive_child_min_bp(bp, slot);
                    slot += 1;
                    result.push_str(&recursive_render_pattern(argument, ctx, inherited));
                }
            },
            GrammarItem::Collection { delimiters, .. } => {
                if let Some(argument) = args.next() {
                    slot += 1;
                    let inner = recursive_render_pattern(argument, ctx, 0);
                    if let Some((open, close)) = delimiters {
                        result.push_str(&format!("{open}{inner}{close}"));
                    } else {
                        result.push_str(&inner);
                    }
                }
            },
            GrammarItem::Binder { category } => {
                result.push_str(&category.to_string().to_lowercase());
            },
        }
    }
    result
}

fn ident(name: &str) -> syn::Ident {
    syn::Ident::new(name, proc_macro2::Span::call_site())
}

fn variable(name: &str) -> Pattern {
    Pattern::Term(PatternTerm::Var(ident(name)))
}

#[test]
fn metadata_type_expr_pda_matches_recursive_equations_on_all_variants() {
    for coll_type in [
        CollectionType::HashBag,
        CollectionType::HashSet,
        CollectionType::Vec,
        CollectionType::HashMap,
        CollectionType::PathMap,
    ] {
        let ty = TypeExpr::Collection {
            coll_type,
            element: Box::new(TypeExpr::Base(ident("Proc"))),
        };
        assert_eq!(type_expr_to_string(&ty), recursive_type_expr_to_string(&ty));
    }

    let mut ty = TypeExpr::Base(ident("T"));
    for depth in 0..64 {
        ty = match depth % 5 {
            0 => TypeExpr::Arrow {
                domain: Box::new(TypeExpr::Base(ident("D"))),
                codomain: Box::new(ty),
            },
            1 => TypeExpr::MultiBinder(Box::new(ty)),
            2 => TypeExpr::Map {
                key: Box::new(TypeExpr::Base(ident("K"))),
                value: Box::new(ty),
            },
            3 => TypeExpr::Collection {
                coll_type: CollectionType::PathMap,
                element: Box::new(ty),
            },
            _ => TypeExpr::Refined {
                var: ident("x"),
                base: Box::new(ty),
                predicate_repr: "test-only predicate".to_owned(),
            },
        };
        assert_eq!(
            type_expr_to_string(&ty),
            recursive_type_expr_to_string(&ty),
            "TypeExpr rendering diverged at bounded depth {}",
            depth + 1,
        );
    }
}

#[test]
fn metadata_render_pdas_match_recursive_equations_across_the_bundled_corpus() {
    let mut syntax_patterns = 0usize;
    let mut pattern_sides = 0usize;
    for language in crate::gen::capture::bundled_corpus::bundled_languages() {
        let definition = &language.def;
        for rule in &definition.terms {
            if let Some(syntax) = &rule.syntax_pattern {
                syntax_patterns += 1;
                assert_eq!(
                    syntax_pattern_to_string(syntax),
                    recursive_syntax_pattern_to_string(syntax),
                    "syntax-string PDA diverged for {} constructor {}",
                    language.tag,
                    rule.label,
                );
            }
        }

        let bp = build_reflection_bp(definition).unwrap_or_else(|rejection| {
            panic!("bundled {} binding-power table must build: {rejection}", language.tag)
        });
        let ctx = RenderCtx { language: definition, bp: &bp };
        for (kind, left, right) in definition
            .equations
            .iter()
            .map(|equation| {
                (format!("equation {}", equation.name), &equation.left, &equation.right)
            })
            .chain(definition.rewrites.iter().map(|rewrite| {
                (format!("rewrite {}", rewrite.name), &rewrite.left, &rewrite.right)
            }))
        {
            for (side, pattern) in [("left", left), ("right", right)] {
                pattern_sides += 1;
                assert_eq!(
                    render_pattern(pattern, ctx, 0),
                    recursive_render_pattern(pattern, ctx, 0),
                    "pattern renderer PDA diverged for {} {kind} {side}",
                    language.tag,
                );
            }
        }
    }
    assert!(
        syntax_patterns >= 50,
        "only {syntax_patterns} syntax patterns reached the oracle"
    );
    assert!(pattern_sides >= 600, "only {pattern_sides} rule sides reached the oracle");
}

#[test]
fn metadata_render_pdas_match_recursive_equations_on_bounded_nested_shapes() {
    let monoid = crate::gen::capture::bundled_corpus::bundled_language("Monoid").def;
    let bp = build_reflection_bp(&monoid).expect("Monoid binding powers build");
    let ctx = RenderCtx { language: &monoid, bp: &bp };

    let mut syntax = SyntaxExpr::Literal("x".to_owned());
    for _ in 0..64 {
        syntax = SyntaxExpr::Op(PatternOp::Opt { inner: vec![syntax] });
    }
    assert_eq!(
        syntax_pattern_to_string(std::slice::from_ref(&syntax)),
        recursive_syntax_pattern_to_string(std::slice::from_ref(&syntax)),
    );

    let mut pattern = variable("X");
    for depth in 0..64 {
        pattern = match depth % 5 {
            0 => Pattern::Term(PatternTerm::Lambda {
                binder: ident("x"),
                body: Box::new(pattern),
            }),
            1 => Pattern::Collection {
                coll_type: Some(CollectionType::HashBag),
                elements: vec![pattern],
                rest: Some(ident("r")),
            },
            2 => Pattern::Map {
                collection: Box::new(pattern),
                params: vec![ident("x")],
                body: Box::new(variable("x")),
            },
            3 => Pattern::Zip {
                first: Box::new(pattern),
                second: Box::new(variable("Y")),
            },
            _ => Pattern::Term(PatternTerm::Subst {
                term: Box::new(pattern),
                var: ident("x"),
                replacement: Box::new(variable("Y")),
            }),
        };
    }
    assert_eq!(render_pattern(&pattern, ctx, 0), recursive_render_pattern(&pattern, ctx, 0),);
}

#[test]
fn metadata_render_pdas_traverse_twenty_thousand_levels_on_a_small_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("metadata-renderer-small-stack".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let monoid = crate::gen::capture::bundled_corpus::bundled_language("Monoid").def;
            let bp = build_reflection_bp(&monoid).expect("Monoid binding powers build");
            let ctx = RenderCtx { language: &monoid, bp: &bp };

            let mut operator = variable("X");
            for _ in 0..DEPTH {
                operator = Pattern::Term(PatternTerm::Apply {
                    constructor: ident("Mul"),
                    args: vec![variable("X"), operator],
                });
            }
            let rendered = render_pattern(&operator, ctx, 0);
            assert!(rendered.len() > DEPTH);
            drop(rendered);
            drop(operator);

            let mut mixed = variable("X");
            for depth in 0..DEPTH {
                mixed = match depth % 5 {
                    0 => Pattern::Term(PatternTerm::Lambda {
                        binder: ident("x"),
                        body: Box::new(mixed),
                    }),
                    1 => Pattern::Collection {
                        coll_type: Some(CollectionType::HashBag),
                        elements: vec![mixed],
                        rest: None,
                    },
                    2 => Pattern::Map {
                        collection: Box::new(mixed),
                        params: vec![ident("x")],
                        body: Box::new(variable("x")),
                    },
                    3 => Pattern::Zip {
                        first: Box::new(mixed),
                        second: Box::new(variable("Y")),
                    },
                    _ => Pattern::Term(PatternTerm::Subst {
                        term: Box::new(mixed),
                        var: ident("x"),
                        replacement: Box::new(variable("Y")),
                    }),
                };
            }
            let rendered = render_pattern(&mixed, ctx, 0);
            assert!(rendered.len() > DEPTH);
            drop(rendered);
            drop(mixed);

            let mut syntax = SyntaxExpr::Literal("x".to_owned());
            for _ in 0..DEPTH {
                syntax = SyntaxExpr::Op(PatternOp::Opt { inner: vec![syntax] });
            }
            let rendered = syntax_pattern_to_string(std::slice::from_ref(&syntax));
            assert_eq!(rendered.len(), DEPTH * 2 + 1);
            drop(rendered);
            drop(syntax);

            let mut ty = TypeExpr::Base(ident("T"));
            for depth in 0..DEPTH {
                ty = match depth % 5 {
                    0 => TypeExpr::Arrow {
                        domain: Box::new(TypeExpr::Base(ident("D"))),
                        codomain: Box::new(ty),
                    },
                    1 => TypeExpr::MultiBinder(Box::new(ty)),
                    2 => TypeExpr::Map {
                        key: Box::new(TypeExpr::Base(ident("K"))),
                        value: Box::new(ty),
                    },
                    3 => TypeExpr::Collection {
                        coll_type: CollectionType::PathMap,
                        element: Box::new(ty),
                    },
                    _ => TypeExpr::Refined {
                        var: ident("x"),
                        base: Box::new(ty),
                        predicate_repr: "deep test predicate".to_owned(),
                    },
                };
            }
            let rendered = type_expr_to_string(&ty);
            assert!(rendered.len() > DEPTH);
            drop(rendered);
            drop(ty);
        })
        .expect("spawn metadata renderer small-stack worker")
        .join()
        .expect("metadata renderer PDAs must not overflow the native stack");
}
