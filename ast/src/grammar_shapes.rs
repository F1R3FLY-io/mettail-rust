//! Built-in grammar-rule shape recognizers — pure structural predicates.
//!
//! **Stage 3.27d-pre + 3.13 + 3.27d + 3.27f shared infrastructure (2026-04-30).**
//! Relocated from `mettail-macros` into `mettail-ast` (2026-06-15) so the
//! auto-injection codegen they support can live next to the `LanguageDef`
//! definition and be replayed at runtime by `reconstruct_language_def`.
//!
//! This module is the single source of truth for:
//!
//! 1. **Shape recognizers** — pure structural predicates over `GrammarRule`.
//!    Used by both Stage 3.27d (G-PREFIX-BP) and Stage 3.27f
//!    (G-INTEGER-OVERFLOW-FORK) plus Stage 3.13 (auto-injection codegen).
//!    No dependency on `BuiltinTypeLattice`.
//!
//! ## Why a shared module?
//!
//! The shape recognizer for unary-prefix rules and the shape recognizer
//! for simple cross-cat projection rules share the same `tc.len() == 1`
//! single-Simple-param invariant — they branch on one extra check
//! (whether `T == rule.category` or not). Putting them in one module
//! consolidates the underlying invariant test and makes future
//! built-in-aware features have a single place to look.
//!
//! ## Future-proof contract
//!
//! Adding a new built-in type (e.g., `Decimal128`):
//! 1. Add `NativeKind::Decimal128` variant to `ast/src/language.rs`.
//! 2. Update `from_syn_type` arm.
//! 3. Add lossless edges to `BuiltinTypeLattice` impl
//!    (`Decimal128 -> [CanonicalBigRat]` etc.).
//! 4. Update `standard_token_variant`.
//!
//! No code change in `binder.rs`, `prefix.rs`, `infix.rs`, or
//! `semantic_actions.rs` is needed for the shared shape recognizers.

use crate::grammar::{GrammarRule, SyntaxExpr, TermParam};
use crate::types::{EvalMode, TypeExpr};
use std::collections::HashSet;

/// Recognized shape of a unary-prefix rule.
///
/// Returned by `classify_unary_prefix_shape` when the rule matches
/// the pattern `Label . a:T |- "literal" a : T;` with a single Simple
/// parameter, no binder/guard/opt-group, and `T == rule.category`.
#[derive(Debug, Clone)]
pub struct UnaryPrefixShape {
    /// The trigger literal (e.g., `"-"`, `"bitnot"`, `"not"`).
    pub trigger: String,
    /// The operand category (== `rule.category`).
    pub operand_category: String,
}

/// Recognized shape of a simple single-param cross-cat projection rule.
///
/// Returned by `classify_simple_projection_shape` when the rule matches
/// the pattern `Label . v:Source |- v : Target;` with a single Simple
/// parameter, no syntax literals, and `Source != Target`.
///
/// Examples: `IntToBigInt . i:Int |- i : BigInt`,
/// `ProcInt . i:Int |- i : Proc`.
///
/// **Used by:** Stage 3.13 auto-injection, which detects user-defined
/// projections and skips synthesizing duplicates.
#[derive(Debug, Clone)]
pub struct SimpleProjectionShape {
    /// The source category (the operand's type).
    pub source_category: String,
    /// The target category (== `rule.category`).
    pub target_category: String,
}

/// Classify a `GrammarRule` as a unary-prefix rule, if it matches.
///
/// **Predicate (all must hold):**
/// - `term_context.len() == 1`
/// - `syntax_pattern.len() == 2`
/// - `tc[0] = TermParam::Simple { name, ty: TypeExpr::Base(T) }`
/// - `sp[0] = SyntaxExpr::Literal(trigger)`
/// - `sp[1] = SyntaxExpr::Param(name)` with `name == param_name from tc[0]`
/// - `T == rule.category`
///
/// **Excluded by construction:**
/// - Binder rules (would require `Abstraction` / `MultiAbstraction` / `GuardBody`)
/// - Opt-group rules (`Optional` term param)
/// - Mixfix rules (sp.len() != 2)
/// - Cross-cat projections (handled by `classify_simple_projection_shape`)
/// - Function-call-form prefixes (e.g., `negate(x)` — different sp shape)
///
/// **Returns** `None` for non-unary-prefix shapes (the common case).
pub fn classify_unary_prefix_shape(rule: &GrammarRule) -> Option<UnaryPrefixShape> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;

    if tc.len() != 1 || sp.len() != 2 {
        return None;
    }

    let (param_name, ty) = match &tc[0] {
        TermParam::Simple { name, ty } => (name.to_string(), ty),
        _ => return None,
    };

    let operand_category = match ty {
        TypeExpr::Base(t) => t.to_string(),
        _ => return None,
    };

    if operand_category != rule.category.to_string() {
        return None;
    }

    let trigger = match &sp[0] {
        SyntaxExpr::Literal(lit) => lit.clone(),
        _ => return None,
    };

    match &sp[1] {
        SyntaxExpr::Param(p) if p.to_string() == param_name => {},
        _ => return None,
    }

    Some(UnaryPrefixShape { trigger, operand_category })
}

/// Classify a `GrammarRule` as a simple cross-cat projection rule, if
/// it matches.
///
/// **Predicate (all must hold):**
/// - `term_context.len() == 1`
/// - `syntax_pattern.len() == 1`
/// - `tc[0] = TermParam::Simple { name, ty: TypeExpr::Base(T) }`
/// - `sp[0] = SyntaxExpr::Param(name)` with same name as tc[0]
/// - `T != rule.category` (cross-cat — same-cat would be a no-op rule)
///
/// **Used by:** Stage 3.13 detects user-supplied injections; Stage 3.27f
/// finds projection rules through which to emit promotion-Fork branches.
pub fn classify_simple_projection_shape(rule: &GrammarRule) -> Option<SimpleProjectionShape> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;

    if tc.len() != 1 || sp.len() != 1 {
        return None;
    }

    let (param_name, ty) = match &tc[0] {
        TermParam::Simple { name, ty } => (name.to_string(), ty),
        _ => return None,
    };

    let source_category = match ty {
        TypeExpr::Base(t) => t.to_string(),
        _ => return None,
    };

    let target_category = rule.category.to_string();

    if source_category == target_category {
        return None;
    }

    match &sp[0] {
        SyntaxExpr::Param(p) if p.to_string() == param_name => {},
        _ => return None,
    }

    Some(SimpleProjectionShape { source_category, target_category })
}

/// Recognized shape of a **fold-alias** (sugar) rule: a `fold` rule whose
/// `![...]` action is a PURE constructor re-wrap of its own parameters into a
/// canonical node of the rule's own category.
///
/// Returned by [`classify_fold_alias_shape`] when ALL of the following hold:
/// - `eval_mode == Some(EvalMode::Fold)` and the rule carries a `![...]` code
///   block (`rust_code`),
/// - `term_context` is present and entirely `Simple { ty: Base(_) }` params
///   (no collection `Vec(..)` / binder `^[..]` / optional params), and
/// - the code block, after unwrapping a single-tail-expression block, is a
///   tree composed ONLY of:
///   - category-variant constructor calls `Type::Variant(args…)` (PascalCase
///     last segment),
///   - smart-pointer wraps `Arc::new(…)` / `Box::new(…)` / `Rc::new(…)`,
///   - nullary-variant paths (e.g. `Proc::PZero`), and
///   - `param.clone()` leaves over the rule's own parameters,
///   rooted at a constructor of the rule's OWN category whose variant is NOT
///   the rule's own label (so a self-reconstruction / identity fold is rejected
///   and reconstruction terminates).
///
/// ## Examples (RhoCalc)
///
/// Classified (sugar ≡ a structural re-wrap of its fold target):
/// - `POutputShort . p:Proc, q:Proc |- "@" p "!" "(" q ")" : Proc
///   ![{ Proc::POutput(Arc::new(Name::NQuote(Arc::new(p.clone()))),
///   Arc::new(q.clone())) }] fold;`  re-wraps to `POutput(NQuote(p), q)`.
/// - `NQuoteShort . p:Proc |- "@" p : Name ![{ Name::NQuote(Arc::new(p.clone()))
///   }] fold;`  re-wraps to `NQuote(p)`.
/// - `NQuoteNil . |- "@" "Nil" : Name ![{ Name::NQuote(Arc::new(Proc::PZero)) }]
///   fold;`  re-wraps to `NQuote(PZero)`.
///
/// NOT classified (conservatively excluded — never collapse non-equivalent reads):
/// - `POutputQuoted` — calls `name_pattern_to_proc(&n)` (a non-constructor fn).
/// - `PForUser` / `GuardThen` / `CommWhere` — call helper fns and/or have a
///   `Vec(..)` param.
/// - `PPersistOutput2Plus`, `InputBindPolyadic` — `let`-block building a `Vec`.
/// - `NParen` — identity `n.clone()` (root is not a constructor call).
/// - `InputBind` / `InputBindQuoted` / … — self-fold (root variant == label).
///
/// ## Used by
///
/// `semantic_hash` codegen (`macros/.../term_ops/semantic_hash.rs`): a
/// fold-alias variant hashes its RECONSTRUCTED canonical node, so the runtime
/// realize-dedup collapses a sugar reading with its fold target (both are
/// eval-identical — e.g. `@("c")!(q)` parsed as `POutputShort(c, q)` vs
/// `POutput(NQuote(c), q)`). The fold body IS the evaluator's own action, so
/// canonicalizing only sugar≡target is observational-equivalence-preserving by
/// construction; genuinely distinct sends keep distinct parameters and so keep
/// distinct hashes.
#[derive(Debug, Clone)]
pub struct FoldAliasShape {
    /// The category produced by the fold (== `rule.category`, == the root
    /// constructor's type segment).
    pub target_category: String,
}

/// Classify a `GrammarRule` as a [`FoldAliasShape`], if it matches. See the
/// struct docs for the full predicate. Returns `None` for the common case
/// (non-fold rules, computational folds, collection/binder folds, self-folds).
pub fn classify_fold_alias_shape(rule: &GrammarRule) -> Option<FoldAliasShape> {
    // (1) Must be a `fold` rule carrying a `![...]` code block.
    if rule.eval_mode != Some(EvalMode::Fold) {
        return None;
    }
    let code = &rule.rust_code.as_ref()?.code;

    // (2) All term-context params must be `Simple { ty: Base(_) }` — the basis
    // for the trivial 1:1 field↔param mapping the reconstruction relies on.
    // Excludes collection (`Vec(..)`) and binder (`^[..]`) rules.
    let tc = rule.term_context.as_ref()?;
    let mut param_names: HashSet<String> = HashSet::with_capacity(tc.len());
    for p in tc {
        match p {
            TermParam::Simple { name, ty: TypeExpr::Base(_) } => {
                param_names.insert(name.to_string());
            },
            _ => return None,
        }
    }

    // (3) The body must be a pure constructor re-wrap rooted at a constructor of
    // the rule's OWN category, whose variant is not the rule's own label.
    let cat = rule.category.to_string();
    let label = rule.label.to_string();
    if !is_fold_alias_root(code, &cat, &label, &param_names) {
        return None;
    }

    Some(FoldAliasShape { target_category: cat })
}

/// Unwrap a `{ tail_expr }` block / parenthesization / invisible group down to
/// its single inner expression. Returns `None` when the block has any
/// statement (e.g. a `let`) or is not exactly one tail expression — such bodies
/// are never pure re-wraps.
fn unwrap_single_expr(expr: &syn::Expr) -> Option<&syn::Expr> {
    match expr {
        syn::Expr::Block(b) if b.block.stmts.len() == 1 => match &b.block.stmts[0] {
            // syn 2.x: a trailing tail expression is `Stmt::Expr(_, None)`.
            syn::Stmt::Expr(inner, None) => unwrap_single_expr(inner),
            _ => None,
        },
        syn::Expr::Paren(p) => unwrap_single_expr(&p.expr),
        syn::Expr::Group(g) => unwrap_single_expr(&g.expr),
        other => Some(other),
    }
}

/// The ROOT of a fold-alias body: must be a constructor call
/// `root_cat::Variant(args…)` where `Variant != rule_label` (rejects identity /
/// self-folds and guarantees reconstruction terminates) and every argument is a
/// pure re-wrap node.
fn is_fold_alias_root(
    expr: &syn::Expr,
    root_cat: &str,
    rule_label: &str,
    params: &HashSet<String>,
) -> bool {
    let Some(e) = unwrap_single_expr(expr) else {
        return false;
    };
    match e {
        syn::Expr::Call(call) => match constructor_path(&call.func) {
            Some((type_seg, variant_seg))
                if type_seg == root_cat && variant_seg != rule_label =>
            {
                call.args.iter().all(|a| is_fold_alias_node(a, params))
            },
            _ => false,
        },
        _ => false,
    }
}

/// A pure re-wrap node (recursive): a category-variant constructor call, a
/// smart-pointer `new`, a `param.clone()` leaf, a nullary-variant path, or a
/// bare param reference. Anything else (free-function calls, `let`/closures/
/// control flow, other method calls, references) makes the body impure.
fn is_fold_alias_node(expr: &syn::Expr, params: &HashSet<String>) -> bool {
    match expr {
        syn::Expr::Call(call) => {
            // `Arc::new(x)` / `Box::new(x)` / `Rc::new(x)` — recurse the wrapped expr.
            if is_smart_ptr_new(&call.func) {
                return call.args.len() == 1 && is_fold_alias_node(&call.args[0], params);
            }
            // `Type::Variant(args…)` — a constructor of any category. Recurse args.
            if constructor_path(&call.func).is_some() {
                return call.args.iter().all(|a| is_fold_alias_node(a, params));
            }
            false
        },
        // `param.clone()` — the only permitted method call.
        syn::Expr::MethodCall(mc) => {
            mc.method == "clone" && mc.args.is_empty() && is_param_ref(&mc.receiver, params)
        },
        // A nullary-variant path (`Proc::PZero`) or a bare param reference.
        syn::Expr::Path(p) => {
            is_nullary_variant_path(&p.path) || is_single_ident_in(&p.path, params)
        },
        syn::Expr::Paren(p) => is_fold_alias_node(&p.expr, params),
        syn::Expr::Group(g) => is_fold_alias_node(&g.expr, params),
        _ => false,
    }
}

/// If `func` is a `≥2`-segment path whose LAST segment is a PascalCase
/// identifier with no generic arguments, return `(second_last_segment,
/// last_segment)` — interpreted as a `Type::Variant` enum constructor. Returns
/// `None` for free functions (snake_case last segment) and single-segment paths.
fn constructor_path(func: &syn::Expr) -> Option<(String, String)> {
    let syn::Expr::Path(p) = func else {
        return None;
    };
    let segs = &p.path.segments;
    if segs.len() < 2 {
        return None;
    }
    let last = segs.last()?;
    if !matches!(last.arguments, syn::PathArguments::None) {
        return None;
    }
    let last_str = last.ident.to_string();
    if !is_pascal_case(&last_str) {
        return None;
    }
    let type_seg = segs[segs.len() - 2].ident.to_string();
    Some((type_seg, last_str))
}

/// Whether `func` is `Arc::new` / `Box::new` / `Rc::new` (possibly fully
/// qualified, e.g. `std::sync::Arc::new`).
fn is_smart_ptr_new(func: &syn::Expr) -> bool {
    let syn::Expr::Path(p) = func else {
        return false;
    };
    let segs = &p.path.segments;
    if segs.len() < 2 {
        return false;
    }
    if segs.last().map(|s| s.ident == "new").unwrap_or(false) {
        let owner = segs[segs.len() - 2].ident.to_string();
        return owner == "Arc" || owner == "Box" || owner == "Rc";
    }
    false
}

/// A path expression naming a nullary enum variant: `≥2` segments, last is a
/// PascalCase identifier with no generic arguments (e.g. `Proc::PZero`).
fn is_nullary_variant_path(path: &syn::Path) -> bool {
    let segs = &path.segments;
    if segs.len() < 2 {
        return false;
    }
    segs.last()
        .map(|s| {
            matches!(s.arguments, syn::PathArguments::None) && is_pascal_case(&s.ident.to_string())
        })
        .unwrap_or(false)
}

/// Whether `expr` is a bare single-ident path naming one of `params` (the
/// receiver position of an admissible `param.clone()`).
fn is_param_ref(expr: &syn::Expr, params: &HashSet<String>) -> bool {
    match expr {
        syn::Expr::Path(p) => is_single_ident_in(&p.path, params),
        syn::Expr::Paren(p) => is_param_ref(&p.expr, params),
        syn::Expr::Group(g) => is_param_ref(&g.expr, params),
        _ => false,
    }
}

/// Whether `path` is a single identifier contained in `params`.
fn is_single_ident_in(path: &syn::Path, params: &HashSet<String>) -> bool {
    path.get_ident().map(|id| params.contains(&id.to_string())).unwrap_or(false)
}

/// A PascalCase (UpperCamelCase) identifier starts with an ASCII uppercase
/// letter — the convention that separates enum-variant constructors
/// (`POutput`, `NQuote`, `PZero`) from free functions (`name_pattern_to_proc`,
/// `new`, `clone`).
fn is_pascal_case(s: &str) -> bool {
    s.chars().next().map(|c| c.is_ascii_uppercase()).unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::{GrammarRule, SyntaxExpr, TermParam};
    use crate::types::TypeExpr;
    use proc_macro2::Span;
    use syn::Ident;

    fn ident(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    /// Build a minimal GrammarRule with judgement-style fields populated.
    fn make_rule(
        label: &str,
        category: &str,
        term_context: Vec<TermParam>,
        syntax_pattern: Vec<SyntaxExpr>,
    ) -> GrammarRule {
        GrammarRule {
            label: ident(label),
            category: ident(category),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(term_context),
            syntax_pattern: Some(syntax_pattern),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
        }
    }

    fn simple_param(name: &str, ty: &str) -> TermParam {
        TermParam::Simple {
            name: ident(name),
            ty: TypeExpr::Base(ident(ty)),
        }
    }

    #[test]
    fn detects_canonical_neg_int_prefix() {
        // Neg . a:Int |- "-" a : Int
        let rule = make_rule(
            "Neg",
            "Int",
            vec![simple_param("a", "Int")],
            vec![SyntaxExpr::Literal("-".to_string()), SyntaxExpr::Param(ident("a"))],
        );
        let shape = classify_unary_prefix_shape(&rule).expect("should classify");
        assert_eq!(shape.trigger, "-");
        assert_eq!(shape.operand_category, "Int");
    }

    #[test]
    fn detects_bitnot_int_prefix() {
        // BitNotInt . a:Int |- "bitnot" a : Int
        let rule = make_rule(
            "BitNotInt",
            "Int",
            vec![simple_param("a", "Int")],
            vec![SyntaxExpr::Literal("bitnot".to_string()), SyntaxExpr::Param(ident("a"))],
        );
        let shape = classify_unary_prefix_shape(&rule).expect("should classify");
        assert_eq!(shape.trigger, "bitnot");
    }

    #[test]
    fn rejects_cross_cat_projection_as_prefix() {
        // ProcInt . i:Int |- i : Proc — single-param projection, NOT prefix
        let rule = make_rule(
            "ProcInt",
            "Proc",
            vec![simple_param("i", "Int")],
            vec![SyntaxExpr::Param(ident("i"))],
        );
        assert!(classify_unary_prefix_shape(&rule).is_none());
        let proj = classify_simple_projection_shape(&rule).expect("should classify");
        assert_eq!(proj.source_category, "Int");
        assert_eq!(proj.target_category, "Proc");
    }

    #[test]
    fn rejects_binary_infix_as_prefix() {
        // Add . l:Int, r:Int |- l "+" r : Int
        let rule = make_rule(
            "Add",
            "Int",
            vec![simple_param("l", "Int"), simple_param("r", "Int")],
            vec![
                SyntaxExpr::Param(ident("l")),
                SyntaxExpr::Literal("+".to_string()),
                SyntaxExpr::Param(ident("r")),
            ],
        );
        assert!(classify_unary_prefix_shape(&rule).is_none());
        assert!(classify_simple_projection_shape(&rule).is_none());
    }

    #[test]
    fn rejects_same_cat_simple_param_as_projection() {
        // A no-op `Identity . v:Int |- v : Int` (hypothetical) — not a
        // valid cross-cat projection.
        let rule = make_rule(
            "Identity",
            "Int",
            vec![simple_param("v", "Int")],
            vec![SyntaxExpr::Param(ident("v"))],
        );
        assert!(classify_simple_projection_shape(&rule).is_none());
    }

    #[test]
    fn rejects_legacy_old_style_rule() {
        // Old-style BNF rule has `term_context: None` — recognizer must
        // return None even if the pattern superficially matches.
        let rule = GrammarRule {
            label: ident("PAmb"),
            category: ident("Proc"),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
        };
        assert!(classify_unary_prefix_shape(&rule).is_none());
        assert!(classify_simple_projection_shape(&rule).is_none());
    }

    #[test]
    fn rejects_param_name_mismatch_in_prefix() {
        // sp[1] = Param("b") but tc[0].name = "a" — invalid pattern.
        let rule = make_rule(
            "BadNeg",
            "Int",
            vec![simple_param("a", "Int")],
            vec![SyntaxExpr::Literal("-".to_string()), SyntaxExpr::Param(ident("b"))],
        );
        assert!(classify_unary_prefix_shape(&rule).is_none());
    }

    // ── classify_fold_alias_shape ────────────────────────────────────────────

    /// Build a `fold` rule with a `![code]` action body for the fold-alias tests.
    fn fold_rule(
        label: &str,
        category: &str,
        term_context: Vec<TermParam>,
        code: syn::Expr,
    ) -> GrammarRule {
        let mut rule = make_rule(label, category, term_context, Vec::new());
        rule.rust_code = Some(crate::types::RustCodeBlock { code });
        rule.eval_mode = Some(crate::types::EvalMode::Fold);
        rule
    }

    #[test]
    fn detects_poutputshort_fold_alias() {
        // POutputShort . p:Proc, q:Proc |- "@" p "!" "(" q ")" : Proc
        //   ![{ Proc::POutput(Arc::new(Name::NQuote(Arc::new(p.clone()))),
        //                     Arc::new(q.clone())) }] fold;
        let rule = fold_rule(
            "POutputShort",
            "Proc",
            vec![simple_param("p", "Proc"), simple_param("q", "Proc")],
            syn::parse_quote! {{
                Proc::POutput(
                    std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                    std::sync::Arc::new(q.clone()),
                )
            }},
        );
        let shape = classify_fold_alias_shape(&rule).expect("POutputShort is a fold-alias");
        assert_eq!(shape.target_category, "Proc");
    }

    #[test]
    fn detects_nquotenil_zero_param_fold_alias() {
        // NQuoteNil . |- "@" "Nil" : Name ![{ Name::NQuote(Arc::new(Proc::PZero)) }] fold;
        let rule = fold_rule(
            "NQuoteNil",
            "Name",
            Vec::new(),
            syn::parse_quote! {{ Name::NQuote(std::sync::Arc::new(Proc::PZero)) }},
        );
        let shape = classify_fold_alias_shape(&rule).expect("NQuoteNil is a fold-alias");
        assert_eq!(shape.target_category, "Name");
    }

    #[test]
    fn rejects_self_fold_identity() {
        // A fold whose root reconstructs its OWN variant must be rejected (it is
        // identity-shaped and would make hash-reconstruction non-terminating).
        let rule = fold_rule(
            "InputBindQuoted",
            "InputBind",
            vec![simple_param("pat", "Proc"), simple_param("n", "Name")],
            syn::parse_quote! {{
                InputBind::InputBindQuoted(
                    std::sync::Arc::new(pat.clone()),
                    std::sync::Arc::new(n.clone()),
                )
            }},
        );
        assert!(classify_fold_alias_shape(&rule).is_none());
    }

    #[test]
    fn rejects_helper_fn_fold() {
        // POutputQuoted calls `name_pattern_to_proc(&n)` — a non-constructor fn —
        // so it is NOT a pure re-wrap and must be rejected.
        let rule = fold_rule(
            "POutputQuoted",
            "Proc",
            vec![simple_param("n", "Name"), simple_param("q", "Proc")],
            syn::parse_quote! {{
                Proc::POutput(
                    std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(
                        crate::rhocalc::receive::name_pattern_to_proc(&n),
                    ))),
                    std::sync::Arc::new(q.clone()),
                )
            }},
        );
        assert!(classify_fold_alias_shape(&rule).is_none());
    }

    #[test]
    fn rejects_non_fold_rule() {
        // Same body, but `eval_mode` is not `Fold` ⇒ not a fold-alias.
        let mut rule = fold_rule(
            "NQuoteShort",
            "Name",
            vec![simple_param("p", "Proc")],
            syn::parse_quote! {{ Name::NQuote(std::sync::Arc::new(p.clone())) }},
        );
        rule.eval_mode = None;
        assert!(classify_fold_alias_shape(&rule).is_none());
        // With a `Fold` mode it IS a fold-alias (positive control).
        rule.eval_mode = Some(crate::types::EvalMode::Fold);
        assert!(classify_fold_alias_shape(&rule).is_some());
    }

    #[test]
    fn rejects_wrong_root_category_fold() {
        // The root constructor must produce the rule's OWN category. A `Name`-
        // category rule whose body builds a `Proc` is rejected.
        let rule = fold_rule(
            "Weird",
            "Name",
            vec![simple_param("p", "Proc")],
            syn::parse_quote! {{ Proc::POutput(std::sync::Arc::new(p.clone()), std::sync::Arc::new(p.clone())) }},
        );
        assert!(classify_fold_alias_shape(&rule).is_none());
    }
}
