//! Bounded recursive specifications for the vendored Ascent PDAs.
//!
//! Only shallow equivalence fixtures call these functions. Deep tests call
//! production implementations exclusively.

use super::*;
use crate::vendored::utils::token_stream_replace_macro_idents;
use proc_macro2::{Delimiter, Group, TokenTree};

fn rule_summary_recursive(rule: &RuleNode) -> String {
    fn summarize_item(node: &BodyItemNode) -> String {
        match node {
            BodyItemNode::Generator(generator) => format!(
                "for_{}",
                pat_to_ident(&generator.pattern)
                    .map(|ident| ident.to_string())
                    .unwrap_or_default()
            ),
            BodyItemNode::Clause(clause) => clause.rel.to_string(),
            BodyItemNode::Call(call) => format!("call(..) with {}", call.schema_name),
            BodyItemNode::Disjunction(disjunction) => format!(
                "({})",
                disjunction
                    .disjuncts
                    .iter()
                    .map(|conjunction| { conjunction.iter().map(summarize_item).join(",") })
                    .join("|")
            ),
            BodyItemNode::Cond(_) => "if_".to_string(),
            BodyItemNode::Agg(aggregate) => {
                format!("agg {}", agg_in_goal_summary(&aggregate.in_goal))
            },
            BodyItemNode::Negation(negation) => {
                format!("! {}", negation_goal_summary(&negation.goal))
            },
            BodyItemNode::MacroInvocation(invocation) => {
                format!("{:?}!(..)", invocation.mac.path)
            },
        }
    }

    let heads = rule
        .head_clauses
        .iter()
        .map(|head| match head {
            HeadItemNode::MacroInvocation(invocation) => {
                format!("{:?}!(..)", invocation.mac.path)
            },
            HeadItemNode::HeadClause(clause) => clause.rel.to_string(),
        })
        .join(", ");
    format!("{heads} <-- {}", rule.body_items.iter().map(summarize_item).join(", "))
}

fn desugar_disjunctions_recursive(rule: RuleNode) -> Vec<RuleNode> {
    fn item(item: &BodyItemNode) -> Vec<Vec<BodyItemNode>> {
        match item {
            BodyItemNode::Generator(_)
            | BodyItemNode::Clause(_)
            | BodyItemNode::Call(_)
            | BodyItemNode::Cond(_)
            | BodyItemNode::Agg(_)
            | BodyItemNode::Negation(_) => vec![vec![item.clone()]],
            BodyItemNode::Disjunction(disjunction) => disjunction
                .disjuncts
                .iter()
                .flat_map(|branch| sequence(&branch.iter().cloned().collect_vec()))
                .collect(),
            BodyItemNode::MacroInvocation(invocation) => {
                panic!("unexpected macro invocation: {:?}", invocation.mac.path)
            },
        }
    }

    fn sequence(items: &[BodyItemNode]) -> Vec<Vec<BodyItemNode>> {
        if items.is_empty() {
            return vec![Vec::new()];
        }
        let prefixes = sequence(&items[..items.len() - 1]);
        let suffixes = item(&items[items.len() - 1]);
        let mut result = Vec::new();
        for prefix in prefixes {
            for suffix in &suffixes {
                let mut combined = prefix.clone();
                combined.extend(suffix.iter().cloned());
                result.push(combined);
            }
        }
        result
    }

    sequence(&rule.body_items)
        .into_iter()
        .map(|body_items| RuleNode {
            body_items,
            head_clauses: rule.head_clauses.clone(),
        })
        .collect()
}

fn bound_vars_recursive(item: &BodyItemNode) -> Vec<Ident> {
    match item {
        BodyItemNode::Generator(generator) => pattern_get_vars(&generator.pattern),
        BodyItemNode::Agg(aggregate) => pattern_get_vars(&aggregate.pat),
        BodyItemNode::Clause(clause) => clause
            .args
            .iter()
            .flat_map(BodyClauseArg::get_vars)
            .collect(),
        BodyItemNode::Call(call) => call.args.iter().flat_map(BodyClauseArg::get_vars).collect(),
        BodyItemNode::Negation(_) | BodyItemNode::MacroInvocation(_) => Vec::new(),
        BodyItemNode::Disjunction(disjunction) => disjunction
            .disjuncts
            .iter()
            .flat_map(|branch| branch.iter().flat_map(bound_vars_recursive))
            .collect(),
        BodyItemNode::Cond(clause) => clause.bound_vars(),
    }
}

fn visit_bound_vars_recursive(item: &mut BodyItemNode, visitor: &mut dyn FnMut(&mut Ident)) {
    match item {
        BodyItemNode::Generator(generator) => {
            pattern_visit_vars_mut(&mut generator.pattern, visitor)
        },
        BodyItemNode::Agg(aggregate) => pattern_visit_vars_mut(&mut aggregate.pat, visitor),
        BodyItemNode::Clause(clause) => {
            for argument in &mut clause.args {
                match argument {
                    BodyClauseArg::Pat(pattern) => {
                        pattern_visit_vars_mut(&mut pattern.pattern, visitor)
                    },
                    BodyClauseArg::Expr(expression) => {
                        if let Some(ident) = expr_to_ident_mut(expression) {
                            visitor(ident);
                        }
                    },
                }
            }
        },
        BodyItemNode::Call(call) => {
            for argument in &mut call.args {
                match argument {
                    BodyClauseArg::Pat(pattern) => {
                        pattern_visit_vars_mut(&mut pattern.pattern, visitor)
                    },
                    BodyClauseArg::Expr(expression) => {
                        if let Some(ident) = expr_to_ident_mut(expression) {
                            visitor(ident);
                        }
                    },
                }
            }
        },
        BodyItemNode::Negation(_) | BodyItemNode::MacroInvocation(_) => {},
        BodyItemNode::Disjunction(disjunction) => {
            for branch in &mut disjunction.disjuncts {
                for item in branch {
                    visit_bound_vars_recursive(item, visitor);
                }
            }
        },
        BodyItemNode::Cond(clause) => match clause {
            CondClause::IfLet(clause) => pattern_visit_vars_mut(&mut clause.pattern, visitor),
            CondClause::If(_) => {},
            CondClause::Let(clause) => pattern_visit_vars_mut(&mut clause.pattern, visitor),
        },
    }
}

fn visit_expr_vars_recursive(
    item: &mut BodyItemNode,
    visitor: &mut dyn FnMut(&mut Ident),
    visit_macro_idents: bool,
) {
    let visit = |expression: &mut Expr, visitor: &mut dyn FnMut(&mut Ident)| {
        expr_visit_free_vars_mut(expression, visitor);
        if visit_macro_idents {
            expr_visit_idents_in_macros_mut(expression, visitor);
        }
    };
    match item {
        BodyItemNode::Generator(generator) => visit(&mut generator.expr, visitor),
        BodyItemNode::Agg(aggregate) => {
            agg_in_goal_visit_exprs_mut(&mut aggregate.in_goal, &mut |expression| {
                visit(expression, visitor)
            });
            if let AggregatorNode::Expr(expression) = &mut aggregate.aggregator {
                visit(expression, visitor);
            }
        },
        BodyItemNode::Clause(clause) => {
            for argument in &mut clause.args {
                if let BodyClauseArg::Expr(expression) = argument {
                    visit(expression, visitor);
                }
            }
        },
        BodyItemNode::Negation(negation) => {
            negation_goal_visit_exprs_mut(&mut negation.goal, &mut |expression| {
                visit(expression, visitor)
            });
        },
        BodyItemNode::Disjunction(disjunction) => {
            for branch in &mut disjunction.disjuncts {
                for item in branch {
                    visit_expr_vars_recursive(item, visitor, visit_macro_idents);
                }
            }
        },
        BodyItemNode::Cond(clause) => match clause {
            CondClause::IfLet(clause) => visit(&mut clause.exp, visitor),
            CondClause::If(clause) => visit(&mut clause.cond, visitor),
            CondClause::Let(clause) => visit(&mut clause.exp, visitor),
        },
        BodyItemNode::Call(call) => {
            visit(&mut call.rel_expr, visitor);
            for argument in &mut call.args {
                if let BodyClauseArg::Expr(expression) = argument {
                    visit(expression, visitor);
                }
            }
        },
        BodyItemNode::MacroInvocation(invocation) => {
            update(&mut invocation.mac.tokens, |tokens| {
                token_stream_replace_ident(tokens, visitor)
            });
        },
    }
}

fn replace_macro_idents_recursive(
    input: TokenStream,
    replacements: &HashMap<Ident, TokenStream>,
) -> TokenStream {
    fn replace(
        tokens: TokenStream,
        replacements: &HashMap<Ident, TokenStream>,
        output: &mut Vec<TokenTree>,
    ) {
        let mut pending_dollar = None;
        for token in tokens {
            if let Some(dollar) = pending_dollar.take() {
                if let TokenTree::Ident(ident) = &token {
                    if let Some(replacement) = replacements.get(ident) {
                        output.extend(replacement.clone());
                        continue;
                    }
                }
                output.push(dollar);
            }
            match token {
                TokenTree::Punct(ref punctuation) if punctuation.as_char() == '$' => {
                    pending_dollar = Some(token)
                },
                TokenTree::Group(group) => output.push(TokenTree::Group(Group::new(
                    group.delimiter(),
                    replace_macro_idents_recursive(group.stream(), replacements),
                ))),
                token => output.push(token),
            }
        }
        if let Some(dollar) = pending_dollar {
            output.push(dollar);
        }
    }

    let mut output = Vec::new();
    replace(input, replacements, &mut output);
    output.into_iter().collect()
}

fn parse_rule(source: &str) -> RuleNode {
    crate::parse_ascent_program_text(source)
        .expect("valid Ascent rule")
        .rules
        .into_iter()
        .next()
        .expect("the fixture contains one rule")
}

fn singleton_disjunction(item: BodyItemNode) -> BodyItemNode {
    let mut conjunction = Punctuated::new();
    conjunction.push_value(item);
    let mut disjuncts = Punctuated::new();
    disjuncts.push_value(conjunction);
    BodyItemNode::Disjunction(DisjunctionNode {
        paren: syn::token::Paren::default(),
        disjuncts,
    })
}

fn disjunction(branches: Vec<Vec<BodyItemNode>>) -> BodyItemNode {
    let branch_count = branches.len();
    let mut disjuncts = Punctuated::new();
    for (branch_index, items) in branches.into_iter().enumerate() {
        let item_count = items.len();
        let mut conjunction = Punctuated::new();
        for (item_index, item) in items.into_iter().enumerate() {
            conjunction.push_value(item);
            if item_index + 1 != item_count {
                conjunction.push_punct(<Token![,]>::default());
            }
        }
        disjuncts.push_value(conjunction);
        if branch_index + 1 != branch_count {
            disjuncts.push_punct(DisjunctionToken::Or(<Token![|]>::default()));
        }
    }
    BodyItemNode::Disjunction(DisjunctionNode {
        paren: syn::token::Paren::default(),
        disjuncts,
    })
}

fn shallow_rule() -> RuleNode {
    let mut rule = parse_rule("result(x) <-- edge(q);");
    rule.body_items = vec![
        disjunction(vec![
            vec![syn::parse_str("left(x)").unwrap(), syn::parse_str("right(y)").unwrap()],
            vec![syn::parse_str("inner(z)").unwrap()],
        ]),
        syn::parse_str("edge(q)").unwrap(),
    ];
    rule
}

fn nested_item(depth: usize) -> BodyItemNode {
    let mut item = syn::parse_str::<BodyItemNode>("edge(value)").expect("valid body item");
    for _ in 0..depth {
        item = singleton_disjunction(item);
    }
    item
}

#[test]
fn ascent_pdas_match_the_bounded_recursive_specifications() {
    let iterative = rule_desugar_disjunction_nodes(shallow_rule());
    let recursive = desugar_disjunctions_recursive(shallow_rule());
    assert_eq!(
        iterative.iter().map(rule_node_summary).collect::<Vec<_>>(),
        recursive
            .iter()
            .map(rule_summary_recursive)
            .collect::<Vec<_>>()
    );

    let mut iterative_item = shallow_rule().body_items.remove(0);
    let mut recursive_item = iterative_item.clone();
    assert_eq!(
        body_item_get_bound_vars(&iterative_item)
            .into_iter()
            .map(|ident| ident.to_string())
            .collect::<Vec<_>>(),
        bound_vars_recursive(&recursive_item)
            .into_iter()
            .map(|ident| ident.to_string())
            .collect::<Vec<_>>()
    );

    let mut iterative_bound_order = Vec::new();
    body_item_visit_bound_vars_mut(&mut iterative_item, &mut |ident| {
        iterative_bound_order.push(ident.to_string())
    });
    let mut recursive_bound_order = Vec::new();
    visit_bound_vars_recursive(&mut recursive_item, &mut |ident| {
        recursive_bound_order.push(ident.to_string())
    });
    assert_eq!(iterative_bound_order, recursive_bound_order);

    let mut iterative_expr_order = Vec::new();
    body_item_visit_exprs_free_vars_mut(
        &mut iterative_item,
        &mut |ident| iterative_expr_order.push(ident.to_string()),
        true,
    );
    let mut recursive_expr_order = Vec::new();
    visit_expr_vars_recursive(
        &mut recursive_item,
        &mut |ident| recursive_expr_order.push(ident.to_string()),
        true,
    );
    assert_eq!(iterative_expr_order, recursive_expr_order);

    let input: TokenStream = "($x, nested!([$y]), $missing)".parse().unwrap();
    let replacements = HashMap::from([
        (Ident::new("x", Span::call_site()), quote!(alpha + beta)),
        (Ident::new("y", Span::call_site()), quote!(gamma)),
    ]);
    assert_eq!(
        token_stream_replace_macro_idents(input.clone(), &replacements).to_string(),
        replace_macro_idents_recursive(input, &replacements).to_string()
    );
}

#[test]
fn ascent_pdas_and_lifecycle_handle_twenty_thousand_disjunction_levels() {
    std::thread::Builder::new()
        .name("ascent-pda-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let item = nested_item(DEPTH);
            let cloned = item.clone();
            let mut rule = parse_rule("result(x) <-- edge(value);");
            rule.body_items = vec![cloned];
            let summary = rule_node_summary(&rule);
            assert!(summary.starts_with("result <-- "));
            assert_eq!(summary.matches('(').count(), DEPTH);

            let mut visited = Vec::new();
            let mut traversed = item;
            body_item_visit_bound_vars_mut(&mut traversed, &mut |ident| {
                visited.push(ident.to_string())
            });
            assert_eq!(visited, ["value"]);

            let desugared = rule_desugar_disjunction_nodes(rule);
            assert_eq!(desugared.len(), 1);
            assert_eq!(rule_node_summary(&desugared[0]), "result <-- edge");
        })
        .expect("the small-stack Ascent thread must spawn")
        .join()
        .expect("Ascent PDAs and lifecycle operations must not overflow a 256 KiB stack");
}

#[test]
fn macro_expansion_accepts_finite_chains_beyond_the_removed_limit_and_rejects_cycles() {
    let mut source = String::new();
    source.push_str("relation edge(i32); relation out(i32);\n");
    source.push_str("macro m0() { edge(x) }\n");
    for index in 1..=150 {
        source.push_str(&format!("macro m{index}() {{ m{}!() }}\n", index - 1));
    }
    source.push_str("out(x) <-- m150!();");
    let program = crate::parse_ascent_program_text(&source).expect("finite macro chain parses");
    let desugared = desugar_ascent_program(program)
        .expect("finite macro chains are not recursion and have no depth limit");
    assert_eq!(desugared.rules.len(), 1);
    assert_eq!(rule_node_summary(&desugared.rules[0]), "out <-- edge");

    let cyclic = crate::parse_ascent_program_text(
        "relation out(i32); macro a() { b!() } macro b() { a!() } out(x) <-- a!();",
    )
    .expect("cyclic macro program parses before expansion");
    let error = match desugar_ascent_program(cyclic) {
        Ok(_) => panic!("recursive macros must fail exactly"),
        Err(error) => error,
    };
    assert!(error
        .to_string()
        .contains("recursively defined Ascent macro"));
}

#[test]
fn macro_expansion_handles_twenty_thousand_head_and_body_links() {
    std::thread::Builder::new()
        .name("ascent-macro-expansion-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut source = String::from("relation edge(i32);\nmacro m0() { edge(x) }\n");
            for index in 1..=DEPTH {
                source.push_str(&format!("macro m{index}() {{ m{}!() }}\n", index - 1));
            }
            source.push_str(&format!("m{DEPTH}!() <-- m{DEPTH}!();"));

            let program = crate::parse_ascent_program_text(&source)
                .expect("the finite macro chain must parse");
            let desugared = desugar_ascent_program(program)
                .expect("finite macro chains have no traversal-depth limit");
            assert_eq!(desugared.rules.len(), 1);
            assert_eq!(rule_node_summary(&desugared.rules[0]), "edge <-- edge");
        })
        .expect("the small-stack macro-expansion thread must spawn")
        .join()
        .expect("macro expansion must not overflow a 256 KiB stack");
}

#[test]
fn token_replacement_handles_twenty_thousand_group_levels() {
    std::thread::Builder::new()
        .name("token-replacement-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut tokens: TokenStream = "$x".parse().unwrap();
            for _ in 0..20_000 {
                tokens = TokenTree::Group(Group::new(Delimiter::Parenthesis, tokens)).into();
            }
            let replacements =
                HashMap::from([(Ident::new("x", Span::call_site()), quote!(replacement))]);
            let output = token_stream_replace_macro_idents(tokens, &replacements);
            assert_eq!(output.into_iter().count(), 1);
        })
        .expect("the small-stack token-replacement thread must spawn")
        .join()
        .expect("token replacement must not overflow a 256 KiB stack");
}
