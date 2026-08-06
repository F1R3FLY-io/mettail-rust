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

use crate::grammar::{GrammarItem, GrammarRule, SyntaxExpr, TermParam};
use crate::language::LanguageDef;
use crate::types::{CollectionType, EvalMode, TypeExpr};
use std::collections::HashSet;

// ═══════════════════════════════════════════════════════════════════════════════
// Binder declaration — the ONE predicate that answers "does this bind?"
// ═══════════════════════════════════════════════════════════════════════════════

/// Whether a single `TermParam` — or anything nested inside it — binds a variable.
///
/// The two binding forms are the abstraction params, spelled `^x.body:[D -> C]`
/// ([`TermParam::Abstraction`]) and `^[xs].body:[D* -> C]`
/// ([`TermParam::MultiAbstraction`]). Neither [`TermParam::Simple`] nor
/// [`TermParam::GuardBody`] binds: a guard slot carries a `BehavioralPred`, which
/// scrutinises the term it guards and introduces no name.
///
/// ★ [`TermParam::Optional`] is the case a flat `iter().any(matches!(…))` gets wrong.
/// `#opt(…)` is a *container* of params, so an abstraction can sit one level down —
/// `#opt(^x.body:[D -> C])` declares a binder that a non-recursive scan cannot see.
/// No grammar in the corpus spells that today (measured: the recursive and flat forms
/// agree on all 54 declared languages), so recursing changes no current answer. It is
/// written recursively because the shape is *already legal* in the parser
/// (`ast/src/grammar.rs::parse_term_param` accepts nested params), so the flat form is
/// a hole waiting for the first grammar that steps in it, not a simplification.
pub fn param_declares_binder(param: &TermParam) -> bool {
    match param {
        TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. } => true,
        TermParam::Optional { params } => params.iter().any(param_declares_binder),
        TermParam::Simple { .. } | TermParam::GuardBody { .. } => false,
    }
}

/// Whether a single grammar rule binds a variable.
///
/// A rule reaches codegen in one of two styles, and each spells binding its own way:
///
/// | style | where binding is spelled | recognized by |
/// |---|---|---|
/// | judgement (`Lam . ^x.body:[T -> T] \|- … : T ;`) | `term_context` params | [`param_declares_binder`] |
/// | legacy positional (`Lam . "λ" <Name> "." Proc ;`) | `items` | [`GrammarItem::Binder`] |
///
/// Both are consulted, unconditionally. An earlier copy of this predicate consulted
/// `items` only via `term_context.as_ref().map(…).unwrap_or_else(…)` — i.e. only when
/// `term_context` was `None` — which silently ignores a `GrammarItem::Binder` on any
/// rule that also carries a term context. That is `false` for every rule in the corpus
/// today (measured: the union and the either/or forms agree on all 54 languages), but
/// the either/or form encodes an assumption about the two styles being mutually
/// exclusive that nothing in `ast/src/grammar.rs` enforces.
pub fn rule_declares_binder(rule: &GrammarRule) -> bool {
    let binds_in_context = rule
        .term_context
        .as_ref()
        .is_some_and(|params| params.iter().any(param_declares_binder));
    let binds_in_items = rule
        .items
        .iter()
        .any(|item| matches!(item, GrammarItem::Binder { .. }));
    binds_in_context || binds_in_items
}

/// **Does this language declare any binder?**
///
/// This is the demand signal for the auto-injected higher-order-logic (HOL) variant
/// family — `Lam{D}` / `MLam{D}` / `Apply{D}` / `MApply{D}` — read by
/// `macros/src/logic/common.rs::compute_hol_domain_pairs` (which every HOL emitter
/// keys off) and by
/// `macros/src/gen/runtime/wpda_codegen/synthetic.rs::synthesize_grammar_rules`
/// (which emits the family's surface syntax).
///
/// ## Why this is the right question
///
/// The family is meta-level abstraction machinery: `Lam{D}` introduces a binding, and
/// `Apply{D}` β-reduces against it (`macros/src/gen/term_ops/normalize.rs`). A language
/// that never binds a variable can never build a `Lam{D}`, so it can never *reduce* an
/// `Apply{D}` either — the whole family is inert. Binding is therefore not a proxy for
/// demand; it is demand.
///
/// ## ★ Why it is DERIVED and not a list of language names
///
/// The answer is computed from the language's own declaration — the abstraction params
/// of its grammar rules — so a grammar that starts or stops binding is reclassified by
/// the same edit that changes it. A hand-maintained roster of "the languages with
/// binders" would be a mirror of a computable domain, and this repository has watched
/// that shape fail repeatedly (see
/// `ast/tests/language_name_keyed_artifacts.rs`, which exists because
/// `const BUNDLED_LANGUAGES` failed open three times before it was replaced by a walk).
///
/// ## Composition
///
/// Callers must evaluate this on the **post-composition** definition. `extends` /
/// `includes` / `mixins` merge a base's `terms` in, so a language that declares no
/// abstraction itself can inherit one. Both production call sites satisfy this: the
/// macro applies `merge::apply_*` before codegen, and
/// `auto_inject::reconstruct_language_def` replays those same passes.
pub fn declares_binder(language: &LanguageDef) -> bool {
    language.terms.iter().any(rule_declares_binder)
}

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

    if rule.category != operand_category {
        return None;
    }

    let trigger = match &sp[0] {
        SyntaxExpr::Literal(lit) => lit.clone(),
        _ => return None,
    };

    match &sp[1] {
        SyntaxExpr::Param(p) if *p == param_name => {},
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
        SyntaxExpr::Param(p) if *p == param_name => {},
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
///
///   rooted at a constructor of the rule's OWN category whose variant is NOT
///   the rule's own label (so a self-reconstruction / identity fold is rejected
///   and reconstruction terminates).
///
/// ## Examples (Rholang)
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
    /// ★ SURFACE SYNONYMY (2026-07-26) — the LABEL of the root constructor the body
    /// re-wraps into (`NQuoteShort` ⇒ `"NQuote"`, `POutputShort` ⇒ `"POutput"`).
    ///
    /// This is what makes the alias relation a GRAPH rather than a predicate: the
    /// synonymy classes of a category are the connected components of
    /// `alias ──▶ target_label`, and every member of a component denotes the same term
    /// under the language's own fold. Consumed by the Display canonical-member routing
    /// (`macros/src/gen/syntax/synonymy.rs`).
    pub target_label: String,
    /// ★ THE TOTAL INVERSE, when it exists. `Some(v)` iff EVERY argument of the root
    /// constructor is a bare parameter wrap (`Arc::new(p.clone())` / `p.clone()` / `p`)
    /// and the parameters used are a PERMUTATION of the rule's own term context — i.e.
    /// the alias is a pure RENAMING of the target, `alias(a₀…aₙ) ≡ Target(a_{v₀}…a_{vₙ})`.
    ///
    /// `v[i]` is the alias-parameter index that supplies the target's `i`-th field.
    ///
    /// **Why this exactly, and why a partial alias is different in kind.** A general
    /// fold-alias is a partial SECTION of its target: `POutputShort(p, q)` reconstructs
    /// `POutput(NQuote(p), q)`, so it names only those `POutput`s whose channel is a
    /// quotation — routing an arbitrary `POutput(NVar x, q)` "through" it is not merely
    /// awkward, it is undefined. A RENAMING alias is a BIJECTION onto its target, so the
    /// routing is total and needs no runtime test. `NQuoteShort ⇒ Some([0])`;
    /// `POutputShort` (argument 0 is a `NQuote(…)` wrap) and `NQuoteNil` (argument 0 is
    /// the literal `Proc::PZero`) both ⇒ `None`.
    pub renaming_inverse: Option<Vec<usize>>,
}

/// ★ SURFACE SYNONYMY (2026-07-26) — an **INERT GROUPING** rule: a bracket pair that
/// wraps a term of its own category and evaluates to that term unchanged.
///
/// Rholang's instance is `NParen . n:Name |- "(" n ")" : Name ![{ n.clone() }] fold;`.
///
/// It is NOT a [`FoldAliasShape`] — [`classify_fold_alias_shape`] deliberately rejects an
/// identity body, because its consumer (`semantic_hash` reconstruction) needs a body that
/// terminates at a DIFFERENT constructor. Inert grouping is the complementary shape: the
/// body terminates at the parameter itself, so the rule denotes a term it does not build.
///
/// Its synonymy class is `{ Grouping(x), x }` for every `x` of the category, which is a
/// class with no second RULE to nominate — the canonical member is the WRAPPED TERM, by
/// construction rather than by declaration. `Display` therefore renders it transparently
/// (forwarding the inherited binding-power threshold), and the parser's own transparent
/// grouping re-inserts the brackets wherever a fence or a precedence threshold demands
/// them. See `macros/src/gen/syntax/synonymy.rs`.
#[derive(Debug, Clone)]
pub struct InertGroupingShape {
    /// The single parameter's name (== the category, == what the body clones).
    pub param: String,
    /// The opening bracket literal (`"("`).
    pub open: String,
    /// The closing bracket literal (`")"`).
    pub close: String,
}

/// Classify a `GrammarRule` as an [`InertGroupingShape`], if it matches.
///
/// **Predicate (all must hold):**
/// - `eval_mode == Some(EvalMode::Fold)` with a `![…]` body,
/// - `term_context` is exactly one `Simple { ty: Base(C) }` with `C == rule.category`,
/// - `syntax_pattern` is exactly `[Literal(open), Param(that param), Literal(close)]`,
/// - the body is exactly `param.clone()` or the bare `param` — the IDENTITY.
///
/// Derived from the rule alone: no label, bracket or language is named.
pub fn classify_inert_grouping_shape(rule: &GrammarRule) -> Option<InertGroupingShape> {
    if rule.eval_mode != Some(EvalMode::Fold) {
        return None;
    }
    let code = &rule.rust_code.as_ref()?.code;
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    if tc.len() != 1 || sp.len() != 3 {
        return None;
    }
    // `Ident` compares by symbol, so the two guards below are allocation-free. The
    // parameter is rendered ONCE, after both have passed, rather than stringifying every
    // ident this classifier looks at — it is called for every rule of every language.
    let (param_ident, ty) = match &tc[0] {
        TermParam::Simple { name, ty } => (name, ty),
        _ => return None,
    };
    match ty {
        TypeExpr::Base(t) if *t == rule.category => {},
        _ => return None,
    }
    let (open, close) = match (&sp[0], &sp[1], &sp[2]) {
        (SyntaxExpr::Literal(o), SyntaxExpr::Param(p), SyntaxExpr::Literal(c))
            if p == param_ident =>
        {
            (o.clone(), c.clone())
        },
        _ => return None,
    };
    // The body must be the IDENTITY on that parameter.
    let param = param_ident.to_string();
    let mut params = HashSet::with_capacity(1);
    params.insert(param.clone());
    let body = unwrap_single_expr(code)?;
    let is_identity = match body {
        syn::Expr::MethodCall(mc) => {
            mc.method == "clone" && mc.args.is_empty() && is_param_ref(&mc.receiver, &params)
        },
        syn::Expr::Path(p) => is_single_ident_in(&p.path, &params),
        _ => false,
    };
    if !is_identity {
        return None;
    }
    Some(InertGroupingShape { param, open, close })
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
    let mut param_order: Vec<String> = Vec::with_capacity(tc.len());
    for p in tc {
        match p {
            TermParam::Simple { name, ty: TypeExpr::Base(_) } => {
                param_names.insert(name.to_string());
                param_order.push(name.to_string());
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

    // (4) SURFACE SYNONYMY (2026-07-26): the root constructor's VARIANT is the class edge,
    // and its argument list decides whether the alias is a total RENAMING of the target.
    // Both are read off the same expression `is_fold_alias_root` just validated, so they
    // cannot disagree with it.
    let root = unwrap_single_expr(code)?;
    let syn::Expr::Call(root_call) = root else {
        return None;
    };
    let (_, target_label) = constructor_path(&root_call.func)?;
    let renaming_inverse = renaming_inverse_of(root_call, &param_order);

    Some(FoldAliasShape {
        target_category: cat,
        target_label,
        renaming_inverse,
    })
}

/// The [`FoldAliasShape::renaming_inverse`] of a validated fold-alias root call: `Some(v)`
/// iff every argument is a BARE parameter wrap and the parameters used are a permutation
/// of `param_order`. `v[i]` is the alias-parameter index supplying the target's `i`-th
/// field.
///
/// A "bare parameter wrap" is a (possibly smart-pointer-nested) `p.clone()` or `p`; a
/// constructor call anywhere on the spine (`Arc::new(Name::NQuote(Arc::new(p.clone())))`)
/// or a nullary-variant leaf (`Proc::PZero`) makes the argument non-bare and the alias
/// merely a partial section — see the field's own documentation for why that distinction
/// is the one that matters.
fn renaming_inverse_of(root_call: &syn::ExprCall, param_order: &[String]) -> Option<Vec<usize>> {
    if root_call.args.len() != param_order.len() {
        return None;
    }
    let mut inverse = Vec::with_capacity(root_call.args.len());
    for arg in &root_call.args {
        let name = bare_param_wrap_name(arg)?;
        inverse.push(param_order.iter().position(|p| *p == name)?);
    }
    // A permutation: every alias parameter is used exactly once.
    let mut seen = vec![false; param_order.len()];
    for &i in &inverse {
        if seen[i] {
            return None;
        }
        seen[i] = true;
    }
    Some(inverse)
}

/// The parameter name a BARE wrap bottoms at: `p`, `p.clone()`, `Arc::new(p.clone())`, …
/// `None` if the spine passes through a constructor call, a nullary variant, or anything
/// else.
fn bare_param_wrap_name(expr: &syn::Expr) -> Option<String> {
    let mut cursor = expr;
    loop {
        cursor = match cursor {
            syn::Expr::Call(call) if is_smart_ptr_new(&call.func) && call.args.len() == 1 => {
                &call.args[0]
            },
            syn::Expr::MethodCall(call) if call.method == "clone" && call.args.is_empty() => {
                &call.receiver
            },
            syn::Expr::Reference(reference) => &reference.expr,
            syn::Expr::Paren(paren) => &paren.expr,
            syn::Expr::Group(group) => &group.expr,
            syn::Expr::Path(path) if path.path.segments.len() == 1 && path.qself.is_none() => {
                return Some(path.path.segments[0].ident.to_string());
            },
            _ => return None,
        };
    }
}

/// Unwrap a `{ tail_expr }` block / parenthesization / invisible group down to
/// its single inner expression. Returns `None` when the block has any
/// statement (e.g. a `let`) or is not exactly one tail expression — such bodies
/// are never pure re-wraps.
fn unwrap_single_expr(expr: &syn::Expr) -> Option<&syn::Expr> {
    let mut cursor = expr;
    loop {
        cursor = match cursor {
            syn::Expr::Block(block) if block.block.stmts.len() == 1 => {
                match &block.block.stmts[0] {
                    // syn 2.x: a trailing tail expression is `Stmt::Expr(_, None)`.
                    syn::Stmt::Expr(inner, None) => inner,
                    _ => return None,
                }
            },
            syn::Expr::Paren(paren) => &paren.expr,
            syn::Expr::Group(group) => &group.expr,
            other => return Some(other),
        };
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
            Some((type_seg, variant_seg)) if type_seg == root_cat && variant_seg != rule_label => {
                call.args.iter().all(|a| is_fold_alias_node(a, params))
            },
            _ => false,
        },
        _ => false,
    }
}

/// A pure re-wrap node: a category-variant constructor call, a
/// smart-pointer `new`, a `param.clone()` leaf, a nullary-variant path, or a
/// bare param reference. Anything else (free-function calls, `let`/closures/
/// control flow, other method calls, references) makes the body impure.
fn is_fold_alias_node(expr: &syn::Expr, params: &HashSet<String>) -> bool {
    let mut work = vec![expr];
    while let Some(node) = work.pop() {
        match node {
            syn::Expr::Call(call) => {
                if is_smart_ptr_new(&call.func) {
                    if call.args.len() != 1 {
                        return false;
                    }
                    work.push(&call.args[0]);
                } else if constructor_path(&call.func).is_some() {
                    // Reverse only the new slice so last-in/first-out visitation remains
                    // argument-left-to-right, matching `Iterator::all`'s short circuit.
                    let start = work.len();
                    work.extend(call.args.iter());
                    work[start..].reverse();
                } else {
                    return false;
                }
            },
            // `param.clone()` — the only permitted method call.
            syn::Expr::MethodCall(call) => {
                if call.method != "clone"
                    || !call.args.is_empty()
                    || !is_param_ref(&call.receiver, params)
                {
                    return false;
                }
            },
            // A nullary-variant path (`Proc::PZero`) or a bare param reference.
            syn::Expr::Path(path) => {
                if !is_nullary_variant_path(&path.path) && !is_single_ident_in(&path.path, params) {
                    return false;
                }
            },
            syn::Expr::Paren(paren) => work.push(&paren.expr),
            syn::Expr::Group(group) => work.push(&group.expr),
            _ => return false,
        }
    }
    true
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
    let mut cursor = expr;
    loop {
        cursor = match cursor {
            syn::Expr::Path(path) => return is_single_ident_in(&path.path, params),
            syn::Expr::Paren(paren) => &paren.expr,
            syn::Expr::Group(group) => &group.expr,
            _ => return false,
        };
    }
}

/// Whether `path` is a single identifier contained in `params`.
fn is_single_ident_in(path: &syn::Path, params: &HashSet<String>) -> bool {
    path.get_ident()
        .map(|id| params.contains(&id.to_string()))
        .unwrap_or(false)
}

/// A PascalCase (UpperCamelCase) identifier starts with an ASCII uppercase
/// letter — the convention that separates enum-variant constructors
/// (`POutput`, `NQuote`, `PZero`) from free functions (`name_pattern_to_proc`,
/// `new`, `clone`).
fn is_pascal_case(s: &str) -> bool {
    s.chars()
        .next()
        .map(|c| c.is_ascii_uppercase())
        .unwrap_or(false)
}

// ── Fold-alias POLYADIC-SEND shape (trailing-Vec, arity ≥2) ──────────────────
//
// Residual #11-1 (2026-07-14). The scalar [`classify_fold_alias_shape`] above
// requires EVERY param be `Simple { Base(_) }` (grammar_shapes.rs:242) and the
// body be a SINGLE tail expression (`unwrap_single_expr`) — so it REJECTS the
// polyadic send sugars (`@p!(a, bs…)`), whose term-context ends in a `Vec`
// "rest" param and whose body BUILDS the payload `Vec` with `let`-statements
// before the tail constructor. Those sugars are nonetheless PURE channel-rewrap
// aliases of a canonical polyadic send: the `@`-projection-isolation prologue
// emits a THIRD, receiver-led reading `POLY_CANON(NQuoteShort(p), a, bs)` for
// `@p!(a,bs)` that is the SAME rho term as the `…Short2Plus(p, a, bs)` sugar, so
// realize-dedup's `semantic_hash` must fold the two (facade 3→2 = walker; see
// `ProjectionIsolation.v` T7 `fallthrough_refines`). This classifier recognizes
// that shape by PURE STRUCTURE — no constructor / type / language name is ever
// matched — so it fires only where the grammar exhibits the shape (rholang's
// send family today) and is byte-inert for every other language.

/// Recognized shape of a **fold-alias polyadic-send** (sugar OR canonical) rule.
///
/// Returned by [`classify_fold_alias_send_shape`]. The struct carries the pieces
/// a `semantic_hash` reconstruction needs: the rewrap-channel expression, the
/// pairing key (`scalar_target_label`), and whether the rule is the CANONICAL
/// pairing target (`channel_is_bare_param == true`) or a channel-rewrap SUGAR to
/// fold (`false`).
#[derive(Debug, Clone)]
pub struct FoldAliasSendShape {
    /// The category produced by the fold (== `rule.category`).
    pub target_category: String,
    /// The variant label of the body's TAIL scalar constructor (e.g. `POutput`
    /// for the send family, `PPersistOutput` for persist). The pairing key that
    /// matches a channel-rewrap SUGAR to its bare-channel CANONICAL sibling —
    /// both lower to the same scalar target. READ FROM THE GRAMMAR BODY; never a
    /// hardcoded constructor name.
    pub scalar_target_label: String,
    /// The channel argument lifted VERBATIM from the body tail's FIRST argument
    /// (`Arc::new(Name::NQuote(Arc::new(p.clone())))` for a `…Short2Plus` sugar;
    /// `Arc::new(n.clone())` for the canonical `…2Plus`). It is a pure,
    /// param-bottomed constructor-wrap; the macros-side reconstruction splices it
    /// as the canonical's channel field and derives the operand smart-pointer
    /// from its outer `…::new`.
    pub channel_expr: syn::Expr,
    /// The single term-context parameter the channel wrap bottoms at (`p` / `n`).
    /// For the send shape this is ALWAYS the first param (asserted).
    pub channel_param: String,
    /// `true` iff the channel is a BARE param quote (`Arc::new(n.clone())`, no
    /// intermediate constructor) — i.e. this rule is the CANONICAL pairing TARGET
    /// (`…2Plus`), NOT a sugar to fold. `false` iff there is ≥1 constructor
    /// between the smart-pointer and the param leaf (`NQuote(p.clone())`) — a
    /// SUGAR (`…Short2Plus`). The macros-side pairing uses this both to select
    /// the reconstruction target and to realize the A1c SELF-EXCLUSION guard
    /// (a canonical is bare, a sugar is not, so `POLY_CANON.label != sugar.label`
    /// automatically — no self-reconstruction / ∞ codegen recursion).
    pub channel_is_bare_param: bool,
}

/// Classify a `GrammarRule` as a [`FoldAliasSendShape`], if it matches. Returns
/// `None` for the common case (any rule not exhibiting the trailing-Vec send
/// shape). Every check is GENERIC (structural) — the predicate keys on grammar
/// SHAPE, not on any constructor / type / language name.
///
/// **Predicate (all must hold):**
/// - **(0)** `eval_mode == Fold` and a `![...]` body is present.
/// - **(1)** term-context = one-or-more leading `Simple { Base(_) }` param(s)
///   followed by EXACTLY ONE trailing `Simple { Collection { Vec, _ } }` "rest"
///   param (total arity ≥2). This is precisely the shape the scalar classifier
///   rejects at grammar_shapes.rs:242.
/// - **(2)** the body's TAIL expression (after any leading `let`-statements) is a
///   constructor call `Cat::Scalar(chan, …)` of the rule's OWN category with ≥1
///   argument. `chan` = the tail's first argument.
/// - **(3)** [**A1a PURITY**] `chan` passes [`is_fold_alias_node`] — a pure
///   constructor / smart-pointer / `param.clone()` wrap with NO free-function
///   call. This EXCLUDES the `*Quoted*` sugars, whose channel routes through the
///   snake_case free fn `name_pattern_to_proc` (⇒ impure ⇒ they stay structural,
///   preserving the Quoted twin the ruling keeps at 2).
/// - **(4)** [**A1b PARAM-BOTTOMED**] `chan`'s single-argument wrap spine bottoms
///   at a term-context PARAMETER (`p.clone()` / bare `n`), NOT a nullary-variant
///   literal. This is the refinement bare [`is_fold_alias_node`] LACKS (it
///   accepts a nullary-variant leaf as pure): it EXCLUDES the `*Nil*` sugars,
///   whose channel bottoms at `Proc::PZero` (∉ params) — folding them would
///   over-prune (`@Nil!(0,1)` 3→1).
/// - **(5)** the channel-source param is the FIRST param (the universal
///   `@ chan ! ( ops )` send shape) — asserted so the macros-side reconstruction
///   can align operands to the canonical's fields by order.
///
/// The **A1c SELF-EXCLUSION** guard (`POLY_CANON.label != rule.label`, which
/// keeps the canonical `…2Plus` OUT of the fold set and prevents ∞ codegen
/// recursion) is applied by the macros-side pairing via `channel_is_bare_param`,
/// mirroring the `variant_seg != rule_label` guard at grammar_shapes.rs:293.
pub fn classify_fold_alias_send_shape(rule: &GrammarRule) -> Option<FoldAliasSendShape> {
    // (0) Must be a `fold` rule carrying a `![...]` code block.
    if rule.eval_mode != Some(EvalMode::Fold) {
        return None;
    }
    let code = &rule.rust_code.as_ref()?.code;

    // (1) term-context: ≥1 leading `Simple { Base(_) }` then EXACTLY ONE trailing
    // `Simple { Collection { Vec } }`. `split_last` isolates the "rest" param.
    let tc = rule.term_context.as_ref()?;
    let (last, leading) = tc.split_last()?;
    if leading.is_empty() {
        // arity ≥2 required (≥1 leading channel/operand + the Vec rest).
        return None;
    }
    let mut params: HashSet<String> = HashSet::with_capacity(tc.len());
    for p in leading {
        match p {
            TermParam::Simple { name, ty: TypeExpr::Base(_) } => {
                params.insert(name.to_string());
            },
            _ => return None,
        }
    }
    match last {
        TermParam::Simple {
            name,
            ty: TypeExpr::Collection { coll_type: CollectionType::Vec, .. },
        } => {
            params.insert(name.to_string());
        },
        _ => return None,
    }

    // (2) body TAIL = `Cat::Scalar(chan, …)` of the rule's OWN category, ≥1 arg.
    let cat = rule.category.to_string();
    let tail = block_tail_expr(code)?;
    let syn::Expr::Call(call) = tail else {
        return None;
    };
    let (type_seg, variant_seg) = constructor_path(&call.func)?;
    if type_seg != cat {
        return None;
    }
    let channel_expr = call.args.first()?.clone();

    // (3) A1a PURITY — the channel is a pure constructor/smart-ptr/param.clone
    // wrap (no free-fn call). Excludes `*Quoted*` (npt).
    if !is_fold_alias_node(&channel_expr, &params) {
        return None;
    }

    // (4) A1b PARAM-BOTTOMED — the wrap spine bottoms at a PARAM, not a nullary
    // variant literal. Excludes `*Nil*` (`NQuote(PZero)`).
    let channel_param = channel_wrap_leaf_param(&channel_expr, &params)?;

    // (5) the channel-source param must be the FIRST param (send shape).
    let first_name = match &tc[0] {
        TermParam::Simple { name, .. } => name.to_string(),
        _ => return None,
    };
    if channel_param != first_name {
        return None;
    }

    let channel_is_bare_param = !channel_wrap_has_constructor(&channel_expr);

    Some(FoldAliasSendShape {
        target_category: cat,
        scalar_target_label: variant_seg,
        channel_expr,
        channel_param,
        channel_is_bare_param,
    })
}

/// Return the TAIL expression of a `{ stmt; …; tail }` block, skipping any
/// leading statements (unlike [`unwrap_single_expr`], which requires EXACTLY one
/// tail expression). Used for the send-sugar shape whose body BUILDS a payload
/// `Vec` with `let`-statements before the tail constructor call. Recurses through
/// paren/group wrappers. Returns `None` if the block's last statement is not a
/// tail expression (e.g. it carries a trailing `;`).
fn block_tail_expr(expr: &syn::Expr) -> Option<&syn::Expr> {
    let mut cursor = expr;
    loop {
        cursor = match cursor {
            syn::Expr::Block(block) => match block.block.stmts.last()? {
                // syn 2.x: a trailing tail expression is `Stmt::Expr(_, None)`.
                syn::Stmt::Expr(inner, None) => inner,
                _ => return None,
            },
            syn::Expr::Paren(paren) => &paren.expr,
            syn::Expr::Group(group) => &group.expr,
            other => return Some(other),
        };
    }
}

/// Follow a channel-wrap's SINGLE-argument spine (smart-pointer `new` /
/// single-arg constructor / paren/group) to its leaf. Returns `Some(param_name)`
/// iff the leaf is a `param.clone()` or a bare param reference in `params` (the
/// channel is "param-bottomed"); returns `None` if the leaf is a nullary-variant
/// literal (e.g. `Proc::PZero`) or the spine branches / bottoms at anything else.
///
/// This is the A1b refinement bare [`is_fold_alias_node`] LACKS: it distinguishes
/// a RECEIVER-PARAM quote (`NQuote(p.clone())`, foldable — has a param twin) from
/// a LITERAL-channel quote (`NQuote(PZero)`, NOT foldable — no param twin, its
/// reading is the standalone `*Nil*` structural variant).
fn channel_wrap_leaf_param(expr: &syn::Expr, params: &HashSet<String>) -> Option<String> {
    let mut cursor = expr;
    loop {
        cursor = match cursor {
            syn::Expr::Call(call)
                if is_smart_ptr_new(&call.func) || constructor_path(&call.func).is_some() =>
            {
                if call.args.len() != 1 {
                    return None;
                }
                &call.args[0]
            },
            // `param.clone()` — the param-bottomed leaf.
            syn::Expr::MethodCall(call) if call.method == "clone" && call.args.is_empty() => {
                let syn::Expr::Path(path) = &*call.receiver else {
                    return None;
                };
                return path
                    .path
                    .get_ident()
                    .map(|id| id.to_string())
                    .filter(|name| params.contains(name));
            },
            // A bare single-ident param reference (e.g. `n`). A `≥2`-segment path
            // (`Proc::PZero`, a nullary variant) has no `get_ident()` ⇒ `None` ⇒ NOT
            // param-bottomed (the A1b exclusion of the `*Nil*` channels).
            syn::Expr::Path(path) => {
                return path
                    .path
                    .get_ident()
                    .map(|id| id.to_string())
                    .filter(|name| params.contains(name));
            },
            syn::Expr::Paren(paren) => &paren.expr,
            syn::Expr::Group(group) => &group.expr,
            _ => return None,
        };
    }
}

/// Whether a channel-wrap spine contains at least one enum-variant CONSTRUCTOR
/// call between the outer smart-pointer and the param leaf. `Arc::new(n.clone())`
/// (a BARE param quote, the CANONICAL `…2Plus` channel) has none ⇒ `false`;
/// `Arc::new(NQuote(Arc::new(p.clone())))` (a channel-rewrap SUGAR) has the
/// `NQuote` constructor ⇒ `true`. Used to set `channel_is_bare_param`, which the
/// macros-side pairing uses to tell canonicals from sugars.
fn channel_wrap_has_constructor(expr: &syn::Expr) -> bool {
    let mut cursor = expr;
    loop {
        cursor = match cursor {
            syn::Expr::Call(call) => {
                if is_smart_ptr_new(&call.func) {
                    if call.args.len() != 1 {
                        return false;
                    }
                    &call.args[0]
                } else {
                    return constructor_path(&call.func).is_some();
                }
            },
            syn::Expr::Paren(paren) => &paren.expr,
            syn::Expr::Group(group) => &group.expr,
            _ => return false,
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::{rule_fixture, GrammarRule, SyntaxExpr, TermParam};
    use crate::types::TypeExpr;
    use proc_macro2::Span;
    use syn::Ident;

    fn ident(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    /// Build a minimal GrammarRule with judgement-style fields populated. Everything these
    /// shape classifiers do NOT read comes from `rule_fixture`, which holds each field's
    /// documented default (`grammar.rs`).
    fn make_rule(
        label: &str,
        category: &str,
        term_context: Vec<TermParam>,
        syntax_pattern: Vec<SyntaxExpr>,
    ) -> GrammarRule {
        GrammarRule {
            term_context: Some(term_context),
            syntax_pattern: Some(syntax_pattern),
            ..rule_fixture(ident(label), ident(category))
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
        // return None even if the pattern superficially matches. That is already the
        // fixture's default shape, so nothing needs overriding.
        let rule = rule_fixture(ident("PAmb"), ident("Proc"));
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
                        crate::rholang::receive::name_pattern_to_proc(&n),
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

    // ── classify_fold_alias_send_shape (Residual #11-1) ──────────────────────

    /// A `Simple { Collection { Vec, Base(elem) } }` "rest" param, e.g. `bs:Vec(Proc)`.
    fn vec_param(name: &str, elem: &str) -> TermParam {
        TermParam::Simple {
            name: ident(name),
            ty: TypeExpr::Collection {
                coll_type: crate::types::CollectionType::Vec,
                element: Box::new(TypeExpr::Base(ident(elem))),
            },
        }
    }

    #[test]
    fn detects_poutputshort2plus_send_alias() {
        // POutputShort2Plus . p:Proc, a:Proc, bs:Vec(Proc)
        //   |- "@" p "!" "(" a "," bs.*sep(",") ")" : Proc
        //   ![{ let mut items…; Proc::POutput(NQuote(p), mk_proc_list(items)) }] fold;
        // A channel-rewrap SUGAR: channel `Arc::new(Name::NQuote(Arc::new(p.clone())))`
        // is pure + param-bottomed + has a constructor ⇒ classifies as a SUGAR.
        let rule = fold_rule(
            "POutputShort2Plus",
            "Proc",
            vec![simple_param("p", "Proc"), simple_param("a", "Proc"), vec_param("bs", "Proc")],
            syn::parse_quote! {{
                let mut items = Vec::with_capacity(1 + bs.len());
                items.push(a.clone());
                items.extend(bs.clone());
                Proc::POutput(
                    std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone()))),
                    std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
                )
            }},
        );
        let shape =
            classify_fold_alias_send_shape(&rule).expect("Short2Plus is a fold-alias-send sugar");
        assert_eq!(shape.target_category, "Proc");
        assert_eq!(shape.scalar_target_label, "POutput"); // derived from the body, not hardcoded
        assert_eq!(shape.channel_param, "p");
        assert!(!shape.channel_is_bare_param, "the sugar channel wraps p in NQuote (not bare)");
    }

    #[test]
    fn detects_poutput2plus_canonical_bare_channel() {
        // POutput2Plus . n:Name, a:Proc, bs:Vec(Proc) — the CANONICAL: bare-param
        // channel `Arc::new(n.clone())` (no intermediate constructor) ⇒ the
        // pairing TARGET, excluded from folding by A1c self-exclusion.
        let rule = fold_rule(
            "POutput2Plus",
            "Proc",
            vec![simple_param("n", "Name"), simple_param("a", "Proc"), vec_param("bs", "Proc")],
            syn::parse_quote! {{
                let mut items = Vec::with_capacity(1 + bs.len());
                items.push(a.clone());
                items.extend(bs.clone());
                Proc::POutput(
                    std::sync::Arc::new(n.clone()),
                    std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
                )
            }},
        );
        let shape =
            classify_fold_alias_send_shape(&rule).expect("POutput2Plus classifies (as canonical)");
        assert_eq!(shape.scalar_target_label, "POutput");
        assert_eq!(shape.channel_param, "n");
        assert!(shape.channel_is_bare_param, "the canonical channel is a bare param quote");
    }

    #[test]
    fn rejects_quoted2plus_impure_npt_channel() {
        // POutputQuoted2Plus — channel routes through the snake_case free fn
        // `name_pattern_to_proc` ⇒ IMPURE ⇒ A1a rejects (keeps the Quoted twin).
        let rule = fold_rule(
            "POutputQuoted2Plus",
            "Proc",
            vec![simple_param("n", "Name"), simple_param("a", "Proc"), vec_param("bs", "Proc")],
            syn::parse_quote! {{
                let mut items = Vec::with_capacity(1 + bs.len());
                items.push(a.clone());
                items.extend(bs.clone());
                Proc::POutput(
                    std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(
                        crate::rholang::receive::name_pattern_to_proc(&n),
                    ))),
                    std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
                )
            }},
        );
        assert!(classify_fold_alias_send_shape(&rule).is_none());
    }

    #[test]
    fn rejects_nil2plus_nullary_variant_channel() {
        // POutputNil2Plus — channel bottoms at `Proc::PZero` (a nullary variant,
        // ∉ params) ⇒ A1b PARAM-BOTTOMED rejects (folding would over-prune
        // `@Nil!(0,1)` 3→1, dropping the Nil/Short twin). Note it is pure yet
        // still rejected — this is the refinement bare `is_fold_alias_node` lacks.
        let rule = fold_rule(
            "POutputNil2Plus",
            "Proc",
            vec![simple_param("a", "Proc"), vec_param("bs", "Proc")],
            syn::parse_quote! {{
                let mut items = Vec::with_capacity(1 + bs.len());
                items.push(a.clone());
                items.extend(bs.clone());
                Proc::POutput(
                    std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(Proc::PZero))),
                    std::sync::Arc::new(crate::rholang::runtime::mk_proc_list(items)),
                )
            }},
        );
        assert!(classify_fold_alias_send_shape(&rule).is_none());
    }

    #[test]
    fn rejects_scalar_short_as_send_no_trailing_vec() {
        // POutputShort (scalar `@p!(q)`) has NO trailing Vec param ⇒ NOT a
        // polyadic-send shape (the scalar `classify_fold_alias_shape` handles it).
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
        assert!(classify_fold_alias_send_shape(&rule).is_none());
    }

    /// ★ GENERALITY (Residual #11-1 generality guard). A SYNTHETIC, non-rholang
    /// grammar (categories `Widget`/`Chan`, constructors `Emit`/`Wrap`/`Zero`,
    /// helper `synthetic_helper`) exhibiting the SAME fold-alias-send SHAPE — a
    /// sugar re-expressing a canonical with a constructor-wrapped PARAM channel
    /// plus passed-through Vec operands. The classifier recognizes it PURELY by
    /// structure (proving it keys on shape, not on rholang names), and rejects
    /// the free-fn-channel and literal-channel siblings by the SAME A1a / A1b
    /// gates. No name in this test appears anywhere in rholang.
    #[test]
    fn generality_synthetic_non_rholang_send_alias() {
        // Sugar: `WrapSend . w:Widget, x:Widget, xs:Vec(Widget)` re-expressing
        // the canonical `Emit` with the channel `Chan::Wrap(w)`.
        let sugar = fold_rule(
            "WrapSend",
            "Widget",
            vec![
                simple_param("w", "Widget"),
                simple_param("x", "Widget"),
                vec_param("xs", "Widget"),
            ],
            syn::parse_quote! {{
                let mut acc = Vec::with_capacity(1 + xs.len());
                acc.push(x.clone());
                acc.extend(xs.clone());
                Widget::Emit(
                    std::sync::Arc::new(Chan::Wrap(std::sync::Arc::new(w.clone()))),
                    std::sync::Arc::new(some_crate::mk_widget_list(acc)),
                )
            }},
        );
        let shape = classify_fold_alias_send_shape(&sugar)
            .expect("synthetic sugar classifies by structure");
        assert_eq!(shape.target_category, "Widget");
        assert_eq!(shape.scalar_target_label, "Emit"); // derived from THIS body
        assert_eq!(shape.channel_param, "w");
        assert!(!shape.channel_is_bare_param);

        // Canonical: `EmitMulti` with a BARE-param channel `n` — classifies as
        // the pairing target (bare), never itself folded.
        let canonical = fold_rule(
            "EmitMulti",
            "Widget",
            vec![
                simple_param("n", "Chan"),
                simple_param("x", "Widget"),
                vec_param("xs", "Widget"),
            ],
            syn::parse_quote! {{
                let mut acc = Vec::with_capacity(1 + xs.len());
                acc.push(x.clone());
                acc.extend(xs.clone());
                Widget::Emit(
                    std::sync::Arc::new(n.clone()),
                    std::sync::Arc::new(some_crate::mk_widget_list(acc)),
                )
            }},
        );
        let cshape =
            classify_fold_alias_send_shape(&canonical).expect("synthetic canonical classifies");
        assert_eq!(cshape.scalar_target_label, "Emit");
        assert!(cshape.channel_is_bare_param, "bare-param channel ⇒ canonical/pairing target");

        // Free-fn-channel sibling — channel routes through a snake_case free fn
        // ⇒ A1a PURITY rejects (the SAME gate that excludes rholang `*Quoted*`).
        let impure = fold_rule(
            "WrapSendImpure",
            "Widget",
            vec![
                simple_param("w", "Widget"),
                simple_param("x", "Widget"),
                vec_param("xs", "Widget"),
            ],
            syn::parse_quote! {{
                let mut acc = Vec::with_capacity(1 + xs.len());
                acc.push(x.clone());
                acc.extend(xs.clone());
                Widget::Emit(
                    std::sync::Arc::new(Chan::Wrap(std::sync::Arc::new(some_crate::synthetic_helper(&w)))),
                    std::sync::Arc::new(some_crate::mk_widget_list(acc)),
                )
            }},
        );
        assert!(
            classify_fold_alias_send_shape(&impure).is_none(),
            "free-fn channel must be rejected by A1a purity",
        );

        // Literal-channel sibling — channel bottoms at a nullary variant
        // `Widget::Zero` (∉ params) ⇒ A1b PARAM-BOTTOMED rejects (the SAME gate
        // that excludes rholang `*Nil*`).
        let literal = fold_rule(
            "WrapSendLit",
            "Widget",
            vec![simple_param("x", "Widget"), vec_param("xs", "Widget")],
            syn::parse_quote! {{
                let mut acc = Vec::with_capacity(1 + xs.len());
                acc.push(x.clone());
                acc.extend(xs.clone());
                Widget::Emit(
                    std::sync::Arc::new(Chan::Wrap(std::sync::Arc::new(Widget::Zero))),
                    std::sync::Arc::new(some_crate::mk_widget_list(acc)),
                )
            }},
        );
        assert!(
            classify_fold_alias_send_shape(&literal).is_none(),
            "literal (nullary-variant) channel must be rejected by A1b param-bottomed",
        );
    }
}

#[cfg(test)]
#[path = "../tests/support/grammar_shapes_recursive_oracle.rs"]
mod recursive_oracle;
