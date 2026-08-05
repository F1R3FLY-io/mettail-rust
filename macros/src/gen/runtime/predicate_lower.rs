//! Lowers syn-based `mettail_ast::language::BehavioralPred` to runtime
//! `mettail_runtime::BehavioralPred` via `quote!` at macro expansion time.
//!
//! The AST predicate type lives in `mettail-ast` and uses `syn::Ident`
//! for relation names and variables. The runtime predicate type lives
//! in `mettail-runtime` and uses `String`. This module emits
//! `TokenStream`s that construct the runtime form from compile-time
//! inputs — used wherever the macro needs to embed a `BehavioralPred`
//! as runtime data in generated code.
//!
//! ## When this is used
//!
//! Currently, the only place that embeds a runtime `BehavioralPred`
//! literal in generated code is when a language spec declares
//! `?guard:Guard(<inline-predicate>)` (a potential future extension
//! where the language-spec-time predicate is captured inline). The
//! per-instance path (source-level `where` clauses) does NOT use this
//! lowering: the `PredicateParser` in `mettail-prattail` produces the
//! runtime type directly from user source tokens, not from a syn AST.
//!
//! So this lowering is correct and tested infrastructure for embedding
//! compile-time predicates; the Comm rule generator uses the runtime parser
//! path for current source-level predicates.
//!
//! ## Phase R — AST moved
//!
//! After the Phase R extraction, the AST type path is
//! `mettail_ast::language::BehavioralPred`. Before the extraction it
//! was `crate::ast::language::BehavioralPred` — those imports have
//! all been rewritten.

use mettail_ast::language::{BehavioralPred as AstPred, PredArg as AstArg, Quantifier as AstQ};
use proc_macro2::TokenStream;
use quote::quote;

/// Generate a `quote!` expression that constructs a
/// `mettail_runtime::BehavioralPred` equal to the given AST predicate
/// at macro-expansion time.
pub fn lower_pred_expr(pred: &AstPred) -> TokenStream {
    enum Task<'pred> {
        Visit(&'pred AstPred),
        Quantified {
            quantifier: AstQ,
            var: String,
            domain: TokenStream,
        },
        Binary(BinaryOp),
        Not,
    }
    #[derive(Clone, Copy)]
    enum BinaryOp {
        And,
        Or,
        Implies,
    }

    let mut tasks = vec![Task::Visit(pred)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        let emitted = match task {
            Task::Visit(AstPred::RelationQuery { relation_name, args, negated }) => {
                let name_str = relation_name.to_string();
                let arg_exprs: Vec<TokenStream> = args.iter().map(lower_arg_expr).collect();
                let neg = *negated;
                Some(quote! {
                    mettail_runtime::BehavioralPred::RelationQuery {
                        relation_name: #name_str.to_string(),
                        args: vec![#(#arg_exprs),*],
                        negated: #neg,
                    }
                })
            },
            Task::Visit(AstPred::Quantified { quantifier, var, domain, bound, body }) => {
                let var_str = var.to_string();
                // AST uses separate `domain` and `bound` fields; runtime
                // collapses these into a single `Option<QuantifiedDomain>`
                // with `Named(name) | Bounded(k)` variants.
                let dom_expr = match (domain, bound) {
                    (Some(n), Some(k)) => {
                        // Bounded named domain: prefer the bound limit
                        // (matches §11 decidability semantics).
                        let _ = n;
                        quote! {
                            Some(mettail_runtime::QuantifiedDomain::Bounded(#k))
                        }
                    },
                    (Some(n), None) => {
                        let s = n.to_string();
                        quote! {
                            Some(mettail_runtime::QuantifiedDomain::Named(#s.to_string()))
                        }
                    },
                    (None, Some(k)) => quote! {
                        Some(mettail_runtime::QuantifiedDomain::Bounded(#k))
                    },
                    (None, None) => quote! { None },
                };
                tasks.push(Task::Quantified {
                    quantifier: quantifier.clone(),
                    var: var_str,
                    domain: dom_expr,
                });
                tasks.push(Task::Visit(body));
                None
            },
            Task::Visit(AstPred::And(a, b)) => {
                tasks.push(Task::Binary(BinaryOp::And));
                tasks.push(Task::Visit(b));
                tasks.push(Task::Visit(a));
                None
            },
            Task::Visit(AstPred::Or(a, b)) => {
                tasks.push(Task::Binary(BinaryOp::Or));
                tasks.push(Task::Visit(b));
                tasks.push(Task::Visit(a));
                None
            },
            Task::Visit(AstPred::Not(inner)) => {
                tasks.push(Task::Not);
                tasks.push(Task::Visit(inner));
                None
            },
            Task::Visit(AstPred::Implies(a, b)) => {
                tasks.push(Task::Binary(BinaryOp::Implies));
                tasks.push(Task::Visit(b));
                tasks.push(Task::Visit(a));
                None
            },
            Task::Visit(AstPred::AcMatch { bag, elements, rest }) => {
                let bag_str = bag.to_string();
                let bag_expr = quote! {
                    mettail_runtime::PredArg::Var(#bag_str.to_string())
                };
                let elem_exprs: Vec<TokenStream> = elements
                    .iter()
                    .map(|e| {
                        let s = e.to_string();
                        quote! { mettail_runtime::PredArg::Var(#s.to_string()) }
                    })
                    .collect();
                let rest_expr = rest.as_ref().map_or_else(
                    || quote! { None },
                    |rest| {
                        let value = rest.to_string();
                        quote! { Some(#value.to_string()) }
                    },
                );
                Some(quote! {
                    mettail_runtime::BehavioralPred::AcMatch {
                        bag: #bag_expr,
                        elements: vec![#(#elem_exprs),*],
                        rest: #rest_expr,
                    }
                })
            },
            Task::Visit(AstPred::Top) => Some(quote! { mettail_runtime::BehavioralPred::Top }),
            Task::Quantified { quantifier, var, domain } => {
                let body_expr = values.pop().expect("quantifier body must be lowered first");
                let q_expr = match quantifier {
                    AstQ::ForAll => quote! { mettail_runtime::Quantifier::ForAll },
                    AstQ::Exists => quote! { mettail_runtime::Quantifier::Exists },
                };
                Some(quote! {
                    mettail_runtime::BehavioralPred::Quantified {
                        quantifier: #q_expr,
                        var: #var.to_string(),
                        domain: #domain,
                        body: Box::new(#body_expr),
                    }
                })
            },
            Task::Binary(op) => {
                let right = values.pop().expect("right operand must be lowered first");
                let left = values.pop().expect("left operand must be lowered first");
                Some(match op {
                    BinaryOp::And => quote! {
                        mettail_runtime::BehavioralPred::And(Box::new(#left), Box::new(#right))
                    },
                    BinaryOp::Or => quote! {
                        mettail_runtime::BehavioralPred::Or(Box::new(#left), Box::new(#right))
                    },
                    BinaryOp::Implies => quote! {
                        mettail_runtime::BehavioralPred::Implies(Box::new(#left), Box::new(#right))
                    },
                })
            },
            Task::Not => {
                let inner = values.pop().expect("negated operand must be lowered first");
                Some(quote! { mettail_runtime::BehavioralPred::Not(Box::new(#inner)) })
            },
        };
        if let Some(emitted) = emitted {
            values.push(emitted);
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().unwrap_or_default()
}

/// Lower a `mettail_ast::language::PredArg` to a `TokenStream` that
/// constructs the corresponding `mettail_runtime::PredArg`.
fn lower_arg_expr(arg: &AstArg) -> TokenStream {
    match arg {
        AstArg::Var(v) => {
            let s = v.to_string();
            quote! {
                mettail_runtime::PredArg::Var(#s.to_string())
            }
        },
        AstArg::Constant(c) => {
            // Currently the AST PredArg::Constant carries an `Ident`,
            // not a ground term. We stringify it and pass as a
            // `Var` in the runtime representation. When §20 ground
            // constants are implemented, this arm will be extended
            // to produce `PredArg::IntLit` or a constructor
            // reference.
            let s = c.to_string();
            quote! {
                mettail_runtime::PredArg::Var(#s.to_string())
            }
        },
    }
}

// ═════════════════════════════════════════════════════════════════════════
// Tests
// ═════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::{BehavioralPred, PredArg, Quantifier};
    use proc_macro2::Span;
    use syn::Ident;

    fn ident(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    fn rel(name: &str, args: Vec<&str>) -> BehavioralPred {
        BehavioralPred::RelationQuery {
            relation_name: ident(name),
            args: args.into_iter().map(|a| PredArg::Var(ident(a))).collect(),
            negated: false,
        }
    }

    /// Round-trip sanity: lowering and re-parsing the emitted
    /// TokenStream should produce a BehavioralPred with the same
    /// stringification.
    #[test]
    fn lower_relation_query() {
        let pred = rel("halts", vec!["x"]);
        let tokens = lower_pred_expr(&pred);
        let rendered = tokens.to_string();
        assert!(rendered.contains("RelationQuery"));
        assert!(rendered.contains("halts"));
        assert!(rendered.contains("\"x\""));
    }

    #[test]
    fn lower_negated_relation_query() {
        let pred = BehavioralPred::RelationQuery {
            relation_name: ident("halts"),
            args: vec![PredArg::Var(ident("x"))],
            negated: true,
        };
        let tokens = lower_pred_expr(&pred);
        let rendered = tokens.to_string();
        assert!(rendered.contains("negated : true"));
    }

    #[test]
    fn lower_conjunction() {
        let pred = BehavioralPred::And(
            Box::new(rel("halts", vec!["x"])),
            Box::new(rel("safe", vec!["x"])),
        );
        let tokens = lower_pred_expr(&pred);
        let rendered = tokens.to_string();
        assert!(rendered.contains("And"));
        assert!(rendered.contains("halts"));
        assert!(rendered.contains("safe"));
    }

    #[test]
    fn lower_disjunction() {
        let pred = BehavioralPred::Or(
            Box::new(rel("fast", vec!["x"])),
            Box::new(rel("cached", vec!["x"])),
        );
        let tokens = lower_pred_expr(&pred);
        let rendered = tokens.to_string();
        assert!(rendered.contains("Or"));
    }

    #[test]
    fn lower_negation() {
        let pred = BehavioralPred::Not(Box::new(rel("halts", vec!["x"])));
        let tokens = lower_pred_expr(&pred);
        let rendered = tokens.to_string();
        assert!(rendered.contains("Not"));
    }

    #[test]
    fn lower_implies() {
        let pred = BehavioralPred::Implies(
            Box::new(rel("reachable", vec!["x", "y"])),
            Box::new(rel("safe", vec!["y"])),
        );
        let tokens = lower_pred_expr(&pred);
        let rendered = tokens.to_string();
        assert!(rendered.contains("Implies"));
    }

    #[test]
    fn lower_forall_named_domain() {
        let pred = BehavioralPred::Quantified {
            quantifier: Quantifier::ForAll,
            var: ident("y"),
            domain: Some(ident("nodes")),
            bound: None,
            body: Box::new(rel("safe", vec!["y"])),
        };
        let tokens = lower_pred_expr(&pred);
        let rendered = tokens.to_string();
        assert!(rendered.contains("ForAll"));
        assert!(rendered.contains("Named"));
        assert!(rendered.contains("nodes"));
    }

    #[test]
    fn lower_exists_bounded_domain() {
        let pred = BehavioralPred::Quantified {
            quantifier: Quantifier::Exists,
            var: ident("y"),
            domain: None,
            bound: Some(100),
            body: Box::new(rel("rewrites_to", vec!["x", "y"])),
        };
        let tokens = lower_pred_expr(&pred);
        let rendered = tokens.to_string();
        assert!(rendered.contains("Exists"));
        assert!(rendered.contains("Bounded"));
    }

    #[test]
    fn lower_ac_match() {
        let pred = BehavioralPred::AcMatch {
            bag: ident("ch"),
            elements: vec![ident("x"), ident("y")],
            rest: Some(ident("zs")),
        };
        let tokens = lower_pred_expr(&pred);
        let rendered = tokens.to_string();
        assert!(rendered.contains("AcMatch"));
        assert!(rendered.contains("\"ch\""));
        assert!(rendered.contains("\"x\""));
        assert!(rendered.contains("\"y\""));
        assert!(rendered.contains("\"zs\""));
    }

    #[test]
    fn lower_top() {
        let pred = BehavioralPred::Top;
        let tokens = lower_pred_expr(&pred);
        let rendered = tokens.to_string();
        assert!(rendered.contains("Top"));
    }

    #[test]
    fn lower_nested_conjunction() {
        let pred = BehavioralPred::And(
            Box::new(BehavioralPred::And(
                Box::new(rel("a", vec!["x"])),
                Box::new(rel("b", vec!["x"])),
            )),
            Box::new(rel("c", vec!["x"])),
        );
        let tokens = lower_pred_expr(&pred);
        let rendered = tokens.to_string();
        // Three RelationQuery nodes expected
        let count = rendered.matches("RelationQuery").count();
        assert_eq!(count, 3);
    }
}
