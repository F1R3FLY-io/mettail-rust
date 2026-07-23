//! L9-3 — token-kind capture field layout (the single source of truth for
//! variant field ORDER when a rule contains one or more `v@Tok` captures).
//!
//! # Why this module exists
//!
//! A `v@Tok` capture (`SyntaxExpr::TokenKind`) adds a `std::string::String`
//! field to the rule's AST variant — the matched token's text, extracted by
//! the walker via `as_token_text()`. Unlike ordinary term-context params, a
//! capture is declared in the SYNTAX PATTERN (after `|-`), not the term
//! context. Every emitter that DEFINES or PATTERN-MATCHES the variant
//! (`gen/types/enums.rs`, `gen/term_ops/subst.rs::variant_kind_from_term_context`,
//! and the bespoke walkers in `gen/native/eval.rs`, `gen/syntax/display.rs`,
//! `gen/syntax/var_inference.rs`, `gen/term_gen/*`, …) must agree on the field
//! order EXACTLY, or the generated pattern arity/positions drift — and because
//! a capture String and a `StringLiteral`-typed param field are the SAME Rust
//! type, a positional drift would SILENTLY SWAP them (no compile error). To
//! make swaps impossible we compute the layout ONCE here and have every seam
//! consume it.
//!
//! # The order (proven consistent with the constructor)
//!
//! The construction site (`gen/runtime/wpda_codegen/binder.rs`) builds the
//! variant as `Cat::Label(non_scope_fields…, scope?)`, where the non-scope
//! fields are in the walker's `action_args` order = SYNTAX-PATTERN ENCOUNTER
//! ORDER (a leading `sp[0]` capture is interned first; then `sp[1..]`), and a
//! binder `Scope` (if any) is appended LAST (binder.rs:3004-3011 / :3338).
//! `capture_layout` reproduces exactly that: walk the syntax pattern in order
//! collecting non-scope fields (captures → [`CaptureFieldKind::TokenText`],
//! simple params → [`CaptureFieldKind::Term`], `?guard` slots →
//! [`CaptureFieldKind::Predicate`]); a single `#opt(...)` group recurses with
//! `optional = true`; an abstraction / multi-abstraction contributes the
//! trailing [`CaptureScope`]. Because sp-order is also what enums.rs and the
//! constructor use, all producers and consumers stay positionally aligned.

use mettail_ast::grammar::{PatternOp, SyntaxExpr, TermParam};
use mettail_ast::types::TypeExpr;
use std::collections::HashSet;

/// One non-scope variant field contributed by a capture-bearing rule, in
/// syntax-pattern encounter order.
#[derive(Clone)]
pub(crate) struct CaptureField<'a> {
    /// The name bound to this field: a capture's `bind` (or the synthesized
    /// `__tok_<Kind>` for an `@`-less capture), or a term-param's name. Used by
    /// the walkers (eval / display) to bind the field in the match pattern and
    /// reference it in user `![...]` code; ignored by the type/`FieldInfo`
    /// producers (which only need the kind).
    pub(crate) name: String,
    pub(crate) kind: CaptureFieldKind<'a>,
    /// True when this field lives inside a `#opt(...)` group → its runtime type
    /// is `Option<…>` and the pattern binding is `Option`-wrapped.
    pub(crate) optional: bool,
}

/// The nature of a non-scope capture-rule field.
#[derive(Clone)]
pub(crate) enum CaptureFieldKind<'a> {
    /// A `v@Tok` capture → a bare `std::string::String` leaf.
    TokenText,
    /// A `Simple` term-param at this syntax position → its declared type.
    Term(&'a TypeExpr),
    /// A `?guard:Guard` predicate slot → a `BehavioralPred` leaf.
    Predicate,
}

/// The trailing binder `Scope` field of a capture rule that ALSO binds
/// (`^x.body` / `^[xs].body`). Appended after all non-scope fields.
pub(crate) struct CaptureScope<'a> {
    /// True for `^[xs].body` (multi-binder `Scope<Vec<Binder>, …>`).
    pub(crate) multi: bool,
    /// The abstraction's arrow type `[Domain -> Codomain]`.
    pub(crate) ty: &'a TypeExpr,
}

/// The full ordered field layout of a capture-bearing rule.
pub(crate) struct CaptureLayout<'a> {
    pub(crate) non_scope: Vec<CaptureField<'a>>,
    pub(crate) scope: Option<CaptureScope<'a>>,
}

/// Compute the capture field layout for a rule, or `None` if the syntax
/// pattern contains no `v@Tok` capture (in which case every seam keeps its
/// byte-identical capture-free path).
pub(crate) fn capture_layout<'a>(
    term_context: &'a [TermParam],
    syntax_pattern: &'a [SyntaxExpr],
) -> Option<CaptureLayout<'a>> {
    let has_capture = syntax_pattern
        .iter()
        .any(|e| matches!(e, SyntaxExpr::TokenKind { .. }));
    if !has_capture {
        return None;
    }

    // Trailing Scope: a multi-abstraction wins over a single abstraction
    // (mirrors variant_kind_from_term_context's precedence).
    let scope = term_context
        .iter()
        .find_map(|p| match p {
            TermParam::MultiAbstraction { ty, .. } => Some(CaptureScope { multi: true, ty }),
            _ => None,
        })
        .or_else(|| {
            term_context.iter().find_map(|p| match p {
                TermParam::Abstraction { ty, .. } => Some(CaptureScope { multi: false, ty }),
                _ => None,
            })
        });

    // Abstraction binder+body names are consumed by the Scope, not emitted as
    // standalone non-scope fields, so skip them when they appear in the pattern.
    let mut abstraction_names: HashSet<String> = HashSet::new();
    for p in term_context {
        if let TermParam::Abstraction { binder, body, .. }
        | TermParam::MultiAbstraction { binder, body, .. } = p
        {
            abstraction_names.insert(binder.to_string());
            abstraction_names.insert(body.to_string());
        }
    }

    let mut non_scope: Vec<CaptureField<'a>> = Vec::new();
    walk_pattern(
        syntax_pattern,
        term_context,
        &abstraction_names,
        false,
        &mut non_scope,
    );

    Some(CaptureLayout { non_scope, scope })
}

/// Recursively find a term param by name, descending into `Optional` groups.
fn find_param<'a>(term_context: &'a [TermParam], name: &str) -> Option<&'a TermParam> {
    for p in term_context {
        match p {
            TermParam::Simple { name: n, .. } if n.to_string() == name => return Some(p),
            TermParam::GuardBody { name: n } if n.to_string() == name => return Some(p),
            TermParam::Optional { params } => {
                if let Some(found) = find_param(params, name) {
                    return Some(found);
                }
            },
            _ => {},
        }
    }
    None
}

fn walk_pattern<'a>(
    exprs: &'a [SyntaxExpr],
    term_context: &'a [TermParam],
    abstraction_names: &HashSet<String>,
    optional: bool,
    out: &mut Vec<CaptureField<'a>>,
) {
    for expr in exprs {
        match expr {
            SyntaxExpr::Literal(_) => {},
            SyntaxExpr::TokenKind { name, bind } => {
                let field_name = bind
                    .as_ref()
                    .map(|b| b.to_string())
                    .unwrap_or_else(|| format!("__tok_{}", name));
                out.push(CaptureField {
                    name: field_name,
                    kind: CaptureFieldKind::TokenText,
                    optional,
                });
            },
            SyntaxExpr::Param(id) => {
                let n = id.to_string();
                if abstraction_names.contains(&n) {
                    // Folds into the trailing Scope.
                    continue;
                }
                match find_param(term_context, &n) {
                    Some(TermParam::Simple { ty, .. }) => out.push(CaptureField {
                        name: n,
                        kind: CaptureFieldKind::Term(ty),
                        optional,
                    }),
                    Some(TermParam::GuardBody { .. }) => out.push(CaptureField {
                        name: n,
                        kind: CaptureFieldKind::Predicate,
                        optional,
                    }),
                    _ => {},
                }
            },
            SyntaxExpr::Op(PatternOp::Opt { inner }) => {
                walk_pattern(inner, term_context, abstraction_names, true, out);
            },
            // Sep/Zip/Map meta-ops never co-occur with a capture in a single
            // rule (collection rules are classified separately and never carry
            // a TokenKind trigger); nothing to contribute here.
            SyntaxExpr::Op(_) => {},
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::SyntaxExpr;
    use mettail_ast::types::TypeExpr;
    use proc_macro2::Span;
    use syn::Ident;

    fn id(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    #[test]
    fn no_capture_returns_none() {
        // A capture-free rule keeps every seam on its byte-identical path.
        let tc = vec![TermParam::Simple { name: id("a"), ty: TypeExpr::Base(id("Num")) }];
        let sp = vec![SyntaxExpr::Param(id("a"))];
        assert!(capture_layout(&tc, &sp).is_none());
    }

    #[test]
    fn captures_only_are_in_syntax_order() {
        // `"tag" w@Word` → one TokenText field named `w`.
        let sp = vec![
            SyntaxExpr::Literal("tag".into()),
            SyntaxExpr::TokenKind { name: id("Word"), bind: Some(id("w")) },
        ];
        let layout = capture_layout(&[], &sp).expect("has a capture");
        assert!(layout.scope.is_none());
        assert_eq!(layout.non_scope.len(), 1);
        assert_eq!(layout.non_scope[0].name, "w");
        assert!(matches!(layout.non_scope[0].kind, CaptureFieldKind::TokenText));
    }

    #[test]
    fn capture_adjacent_to_string_param_does_not_swap() {
        // F.1 no-swap: `w@Word s` where `s:StringLiteral` — BOTH fields lower to
        // `String`. The layout MUST bind strictly by syntax position: `w`
        // (capture, from the pattern) first, then `s` (param, from the context).
        let tc = vec![TermParam::Simple { name: id("s"), ty: TypeExpr::Base(id("StringLiteral")) }];
        let sp = vec![
            SyntaxExpr::TokenKind { name: id("Word"), bind: Some(id("w")) },
            SyntaxExpr::Param(id("s")),
        ];
        let layout = capture_layout(&tc, &sp).expect("has a capture");
        assert!(layout.scope.is_none());
        assert_eq!(layout.non_scope.len(), 2);
        // Position 0 is the capture `w`; position 1 is the param `s`. A swap
        // would reverse these (and be silent, since both are `String`).
        assert_eq!(layout.non_scope[0].name, "w");
        assert!(matches!(layout.non_scope[0].kind, CaptureFieldKind::TokenText));
        assert_eq!(layout.non_scope[1].name, "s");
        assert!(matches!(layout.non_scope[1].kind, CaptureFieldKind::Term(_)));
    }

    #[test]
    fn capture_with_abstraction_puts_scope_last() {
        // F.1 full-support: `"lam" w@Word x . body` with `^x.body:[Num -> Num]`
        // → non-scope [TokenText w], trailing Scope (binder x + body fold in).
        let tc = vec![TermParam::Abstraction {
            binder: id("x"),
            body: id("body"),
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::Base(id("Num"))),
                codomain: Box::new(TypeExpr::Base(id("Num"))),
            },
        }];
        let sp = vec![
            SyntaxExpr::Literal("lam".into()),
            SyntaxExpr::TokenKind { name: id("Word"), bind: Some(id("w")) },
            SyntaxExpr::Param(id("x")),
            SyntaxExpr::Literal(".".into()),
            SyntaxExpr::Param(id("body")),
        ];
        let layout = capture_layout(&tc, &sp).expect("has a capture");
        assert_eq!(layout.non_scope.len(), 1, "only the capture is a non-scope field");
        assert_eq!(layout.non_scope[0].name, "w");
        let scope = layout.scope.expect("abstraction yields a trailing Scope");
        assert!(!scope.multi);
    }
}
