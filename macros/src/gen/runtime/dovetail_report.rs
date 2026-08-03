//! Dovetail report helper generation.
//!
//! This concern emits AST-first lowering from macro-expanded `LanguageDef`
//! data into the runtime Dovetail API. It never reconstructs a language from
//! rendered syntax strings: constructor labels, categories, rules, and
//! patterns come directly from the parsed language definition.

use std::collections::HashSet;

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::language::{Equation, LanguageDef, Premise, RewriteRule};
use mettail_ast::pattern::{Pattern as AstPattern, PatternTerm};
use mettail_ast::types::CollectionType;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Ident, LitStr};

use crate::gen::runtime::disposition::{LoweringDisposition, LoweringOutcome};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_runtime::{LoweredConstructKind, LoweredConstructOrigin, LoweringLane};

pub(crate) mod ac;
pub(crate) mod op_enum;
pub(crate) mod reconstruct;
pub(crate) mod typed_lowering;
pub(crate) mod typed_report;
pub(crate) mod withholding;

/// Whether a language gets the typed-`L` Dovetail path (Increment 2/3 + E1). A language needs
/// the typed path when it has either:
///
///   1. **a non-native-output `fold`** — a `fold` term rule whose OUTPUT category has no native
///      type (e.g. Rholang's `int(..)`/`+`/`concat` casts that return `Proc`). Such folds reduce
///      nowhere on the `EGraph<String>` path (their `![{..}]` bodies were emitted only into the
///      retired Ascent backend); OR
///   2. **(E1.1) a substitution rewrite** — a rewrite whose RHS is a β-style `Subst`/`MultiSubst`
///      replacement ([`is_substitution_rewrite`]). The contractum is a NEW typed term the runtime
///      must reconstruct from the e-graph, run a generated `substitute_<cat>`/`multi_substitute_<cat>`
///      on, and re-add — exactly the typed-path machinery (`saturate_with_native` + a native-rule
///      dispatcher + reconstruction). On the `EGraph<String>` path such a rewrite is rejected
///      (`dovetail_report_for` errors), leaving the language (e.g. Lambda) with no reducer.
///
/// Languages with neither (BaseMath; native-output-only fold languages like Calculator) keep the
/// existing `EGraph<String>` path unchanged. Renamed from `needs_typed_fold_path` (the path is no
/// longer fold-only); the old name is retained as a thin alias for any external caller.
pub(crate) fn needs_typed_dovetail_path(language: &LanguageDef) -> bool {
    let has_native_fold = language.terms.iter().any(|rule| {
        rule.eval_mode == Some(mettail_ast::types::EvalMode::Fold)
            && language
                .get_type(&rule.category)
                .map_or(true, |t| t.native_type.is_none())
    });
    let has_substitution_rewrite = language
        .rewrites
        .iter()
        .any(|rw| is_substitution_rewrite(language, rw).is_some());
    // Stage 3e: a native SYSTEM PROCESS (a `fold` whose native-SCALAR output the Rho scalar path
    // rejects — e.g. `PowInt : Int`, BigInt arithmetic) reduces to its host-computed value on the
    // TYPED fold path (the native rule + op enum). The `has_native_fold` gate above deliberately
    // skips native-scalar-output folds (historically the retired Ascent backend ran them), so a
    // language whose ONLY reducing rule is such a native process would otherwise take the untyped
    // String path — where the native fold never fires, leaving the redex un-reduced with no
    // rewrite justification for the native σ-injection to read. Its materialized dispatch receiver
    // (`rho_net_native_injection_sites`) signals exactly this: the native process must fire on the
    // typed path. (Byte-identical for every language with no native injection site.)
    let has_native_system_process =
        !mettail_rholang_codegen::rho_net_native_injection_sites(language).is_empty();
    // Stage 3f: a native SCALAR FOLD (`AddInt`, `SubInt` — a `fold` whose native-SCALAR output the
    // Rho scalar path DOES lower to an in-Rho contract, so it is classified `NativeFold` rather than
    // the rejected `NativeSystemProcess`) reduces to its host-computed value on the TYPED fold path
    // (the native rule + op enum), for the SAME reason as `has_native_system_process`: the
    // `has_native_fold` gate above deliberately skips native-scalar-output folds, so a pure
    // scalar-fold language (e.g. `NativeFoldDemo`) would otherwise take the untyped String path —
    // where the fold reduces but records NO rewrite justification (empirically: `#justifications =
    // 0`), leaving the native-fold σ-injection with no firing (and no contractum) to read. Its
    // materialized `NativeFold` dispatch receiver (`rho_net_native_fold_injection_sites`) signals
    // exactly this: the native scalar fold must fire on the typed path. (Byte-identical for every
    // language with no native-fold injection site — the Calculator already reaches the typed path
    // via its non-native-output Proc-cast folds, so its `||` result is unchanged.)
    let has_native_fold_rewrite =
        !mettail_rholang_codegen::rho_net_native_fold_injection_sites(language).is_empty();
    // (A-3) A canonical single-receive Rholang COMMUNICATION rule ([`is_comm_rewrite`]) is a
    // TYPED native firing: its `(PPar { (PFor N cont), (POutput N Q), ...rest })` LHS is a
    // NON-LINEAR AC pattern (Blocker 2) over a BINDER element (the substitution `cont[Q/y]` needs
    // the typed native lane), and its RHS nests a `MultiSubst` in an AC `PPar` (Blocker 1) — none
    // of which the `EGraph<String>` path lowers. Routing it typed makes `dovetail_report_for`
    // produce the Comm justification (σ + contractum) the runtime Comm σ-injection reads, removing
    // the hand-built-σ deviation. Byte-identical for every language with no Comm rewrite.
    let has_comm_rewrite = language
        .rewrites
        .iter()
        .any(|rw| is_comm_rewrite(language, rw).is_some());
    // (Stage 3d) A STRUCTURAL non-linear AC rewrite ([`is_structural_ac_rewrite`], the Ambient
    // `OpenRule` `{(open N P), N[Q], ...rest} ~> {P, Q, ...rest}`) is a TYPED native firing for the
    // same reasons as Comm — its LHS is a NON-LINEAR AC pattern (Blocker 2) the `EGraph<String>`
    // path records no justification for, and its RHS nests a structural bag in an AC `PPar`
    // (Blocker 1) — so routing it typed makes `dovetail_report_for` produce the OpenRule
    // justification the runtime structural-AC σ-injection reads.
    //
    // GATED on `!should_emit_binder_congruence`: a language whose reduction ALSO needs the untyped
    // path's binder-congruence float (the full `Ambient`, with its `PNew` binder + `new`-floating
    // equations, whose `InRule`/`OutRule` also reduce via the untyped String-AC) MUST stay on the
    // untyped path — the typed lane has no binder float. Such a language cannot install on the Rho
    // backend anyway (its nested `InRule`/`OutRule` stay `Unsupported`), so the structural-AC Rho
    // firing is delivered by a binder-free generated language (`AmbDemo`), which this gate routes
    // typed while keeping the full `Ambient` byte-identical on the untyped path.
    let has_structural_ac_rewrite = language
        .rewrites
        .iter()
        .any(|rw| is_structural_ac_rewrite(language, rw).is_some())
        && !crate::gen::runtime::binder_congruence::should_emit_binder_congruence(language);
    // (Stage 4) A DEPTH-2 NESTED structural non-linear AC rewrite ([`is_nested_structural_ac_rewrite`],
    // the Ambient `InRule`/`OutRule`) is a TYPED native firing for the SAME reasons as the flat
    // structural-AC `OpenRule` — its LHS is a NON-LINEAR AC pattern (the `EGraph<String>` path records
    // no justification) and its RHS nests a bag in an AC `PPar` — so routing it typed makes
    // `dovetail_report_for` produce the In/Out justification (σ + contractum) the runtime nested
    // structural-AC σ-injection reads. GATED on `!should_emit_binder_congruence` (identical to the
    // flat gate): the full `Ambient` (PNew binder + `new`-floating equations) MUST stay on the untyped
    // path — its In/Out are delivered in Rho by the binder-free `InOutDemo`, which this gate routes
    // typed while keeping the full `Ambient` byte-identical on the untyped path.
    let has_nested_structural_ac_rewrite = language
        .rewrites
        .iter()
        .any(|rw| is_nested_structural_ac_rewrite(language, rw).is_some())
        && !crate::gen::runtime::binder_congruence::should_emit_binder_congruence(language);
    // ★★★ (#195) A language declaring a WITHHELD congruence (`| S ~/> T |-`) MUST take the
    // typed path, and the reason is structural rather than a preference.
    //
    // Withholding is honoured by lowering the severed field to a payload-verbatim leaf
    // (Theorem W1: an e-graph can only withhold propagation at a position that holds no
    // child e-class id). On the typed path that leaf is `FieldWithheld<Cat>(Arc<Cat>)`, which
    // `reconstruct::withheld_reconstruct` inverts with a `clone()` — total and lossless. The
    // `EGraph<String>` path has no typed op-enum to hang a payload-bearing variant on and no
    // reconstructor to invert one with, so severance there could only be spelled as the LOSSY
    // `FieldOpaque(Debug)` leaf — which would make every term containing a withheld field a
    // STUCK RECONSTRUCTION, exactly the Turing failure (`languages/tests/turing.rs`): a
    // non-invertible carrier breaks `dovetail_normal_term` for terms with no redex at all.
    //
    // Routing typed makes the invertible carrier available by construction, so the untyped
    // path never has to spell severance and no `compile_error!` about paths is needed.
    //
    // ⚠ Includes REFUSED withholdings (`WithholdingSet::is_empty` covers both), so a language
    // whose only `~/>` declaration the classifier refused still takes the path that emits the
    // refusal's `compile_error!`.
    //
    // ⚠ BYTE-IDENTICAL FOR EVERY SHIPPED LANGUAGE: no production grammar declares `~/>`
    // (Ambient/Calculator/Json/Lambda/Monoid/Pi/Rholang/Turing: zero), so this disjunct is
    // `false` throughout the corpus and no language's path assignment moves.
    let has_withheld_congruence = !withholding::classify_withholdings(language).is_empty();
    has_native_fold
        || has_substitution_rewrite
        || has_native_system_process
        || has_native_fold_rewrite
        || has_comm_rewrite
        || has_structural_ac_rewrite
        || has_nested_structural_ac_rewrite
        || has_withheld_congruence
}

/// Backward-compatible alias for [`needs_typed_dovetail_path`] (the typed path is no longer
/// fold-only after E1; this preserves the historical name for any out-of-module reference).
pub(crate) fn needs_typed_fold_path(language: &LanguageDef) -> bool {
    needs_typed_dovetail_path(language)
}

/// (E1.2) A rewrite recognized as a generalized **substitution rewrite** — a β-style replacement
/// whose contractum is produced by running a generated `substitute_<cat>`/`multi_substitute_<cat>`
/// on a reconstructed binder body. Everything here is derived from `LanguageDef`; there is NO
/// per-language hardcoding (no `App`/`Lam` literal, no `name == "Lambda"`).
#[derive(Debug, Clone)]
pub(crate) struct SubstRewrite {
    /// The rewrite's name/label (`<Lang>::rewrite::<name>` for the native-rule label).
    pub(crate) label: String,
    /// The whole LHS pattern (`rw.left`). The native-rule LHS is derived from it by
    /// [`subst_rewrite_native_lhs`], binding `scope_var` to the WHOLE binder node.
    pub(crate) left: AstPattern,
    /// The single scope variable — bound by the `binder_label` constructor in `left`, and the
    /// `scope` of the RHS `Subst`/`MultiSubst`.
    pub(crate) scope_var: Ident,
    /// The replacement argument variables (RHS `replacements`), in order. Each is a plain `Var`
    /// occurring in `left`; `repl_vars.len()` is the substitution arity.
    pub(crate) repl_vars: Vec<Ident>,
    /// The matched binder constructor label (a `VariantKind::Binder`/`MultiBinder` whose body the
    /// `scope_var` denotes) — reconstruction matches `binder_cat::binder_label(scope)`.
    pub(crate) binder_label: Ident,
    /// The binder constructor's category (the category `binder_label` constructs).
    pub(crate) binder_cat: Ident,
    /// The bound-variable (domain) category — the `substitute_<binder_cat_lc>` replacement type
    /// and the `&binder.0` free-variable type.
    pub(crate) binder_var_cat: Ident,
    /// The body (codomain) category — `build_<body_cat>_d` reconstructs the scope body, the result
    /// of substitution is a `body_cat`, re-added via `__mettail_dovetail_add_<body_cat>`.
    pub(crate) body_cat: Ident,
    /// Whether the matched binder is a `MultiBinder` (`multi_substitute_*` with an arity assert)
    /// vs a single `Binder` (`substitute_*`, arity-1).
    pub(crate) multi: bool,
    /// The outermost constructor of `left` (the redex head, e.g. `App`) — its op-enum variant
    /// (`op_variant_ident`) joins the MF1 redex-head set so extraction prefers the contractum.
    pub(crate) head_label: Ident,
    /// The category of the `head_label` constructor (for `op_variant_ident`).
    pub(crate) head_cat: Ident,
}

/// (E1.2 — MF4, shape-guarded) Classify a rewrite as a [`SubstRewrite`], or `None`.
///
/// Accepts ONLY the precise β-substitution shape, fail-closed on everything else (verified to
/// REJECT Rholang's `Comm`, whose RHS nests the `MultiSubst` inside an AC `PPar` and whose
/// replacement is a `Map`):
///
///  - premises are congruence-only (every other premise kind is a side condition the structural
///    saturation cannot discharge);
///  - the RHS is *exactly* a `Pattern::Term(MultiSubst { scope: Var, .. })` or
///    `Pattern::Term(Subst { term: Var, .. })` — the substitution is the WHOLE RHS, never nested
///    inside `Apply`/`Collection`/`Map`/`Zip`;
///  - exactly one scope variable (single binder), and the scope is a bare `Var`;
///  - every replacement is a plain `Var` (the supported, fully-general case) — `Map`/`Zip`/
///    `Collection` replacements (Rholang's `qs.*map(..)`) are rejected;
///  - the LHS contains NO collection metapattern anywhere (no AC-collection-nested redex);
///  - the `scope_var` is bound by a `Binder`/`MultiBinder` constructor position in the LHS —
///    i.e. `left` contains an `Apply { constructor: C, args: [Var(scope_var)] }` where `C` is a
///    `VariantKind::Binder`/`MultiBinder` of its category (resolved via
///    `collect_category_variants`). This yields `binder_label`/`binder_cat`/`binder_var_cat`/
///    `body_cat`/`multi`.
pub(crate) fn is_substitution_rewrite(
    language: &LanguageDef,
    rw: &RewriteRule,
) -> Option<SubstRewrite> {
    // Premises: congruence-only (same gate as the structural lowering).
    if !rw.premises.iter().all(premise_supported) {
        return None;
    }

    // RHS must be EXACTLY a top-level Subst/MultiSubst (not nested in Apply/Collection/Map/Zip).
    let AstPattern::Term(rhs_term) = &rw.right else {
        return None;
    };
    let (scope_pat, repl_pats): (&AstPattern, Vec<&AstPattern>) = match rhs_term {
        PatternTerm::MultiSubst { scope, replacements } => {
            (scope.as_ref(), replacements.iter().collect())
        },
        // Single `Subst { term, var, replacement }` is the 3-arg form; `term` is the scope body,
        // and `var`/`replacement` give a single (var ↦ replacement) pair. We accept only the
        // shape where `term` is a bare scope `Var` and there is one replacement, mirroring the
        // MultiSubst arity-1 case (the general 2-arg `(eval <var> <arg>)` always parses to a
        // MultiSubst; the 3-arg `Subst` is the legacy form).
        PatternTerm::Subst { term, replacement, .. } => (term.as_ref(), vec![replacement.as_ref()]),
        _ => return None,
    };

    // Scope is a bare variable.
    let AstPattern::Term(PatternTerm::Var(scope_var)) = scope_pat else {
        return None;
    };

    // Every replacement is a plain `Var` (Map/Zip/Collection replacements rejected — this is what
    // excludes Rholang's `qs.*map(|q| (NQuote q))`).
    let mut repl_vars: Vec<Ident> = Vec::with_capacity(repl_pats.len());
    for rp in &repl_pats {
        match rp {
            AstPattern::Term(PatternTerm::Var(v)) => repl_vars.push(v.clone()),
            _ => return None,
        }
    }
    if repl_vars.is_empty() {
        return None;
    }

    // LHS must contain no collection metapattern anywhere (no AC-collection-nested redex).
    if pattern_contains_collection(&rw.left) {
        return None;
    }

    // `scope_var` must be bound by a `Binder`/`MultiBinder` constructor position in the LHS.
    let binder = find_binder_scope(language, &rw.left, scope_var)?;

    // The redex head: the outermost constructor of the LHS.
    let AstPattern::Term(PatternTerm::Apply { constructor: head_label, .. }) = &rw.left else {
        return None;
    };
    let head_cat = language.category_of_constructor(head_label)?.clone();

    Some(SubstRewrite {
        label: format!("{}::rewrite::{}", language.name, rw.name),
        left: rw.left.clone(),
        scope_var: scope_var.clone(),
        repl_vars,
        binder_label: binder.binder_label,
        binder_cat: binder.binder_cat,
        binder_var_cat: binder.binder_var_cat,
        body_cat: binder.body_cat,
        multi: binder.multi,
        head_label: head_label.clone(),
        head_cat,
    })
}

/// The binder constructor a scope variable is bound by, resolved from the LHS.
struct BinderScope {
    binder_label: Ident,
    binder_cat: Ident,
    binder_var_cat: Ident,
    body_cat: Ident,
    multi: bool,
}

/// Find the `Binder`/`MultiBinder` constructor that binds `scope_var` in `pattern` — an
/// `Apply { constructor: C, args: [Var(scope_var)] }` where `C` is a `VariantKind::Binder`/
/// `MultiBinder` of its category. Searches recursively through `Apply` argument positions (the
/// binder may be nested under the redex head, e.g. `(App (Lam fun) arg)`). Returns the binder's
/// label, its category, the bound-variable (domain) category, the body (codomain) category, and
/// whether it is a multi-binder.
fn find_binder_scope(
    language: &LanguageDef,
    pattern: &AstPattern,
    scope_var: &Ident,
) -> Option<BinderScope> {
    let AstPattern::Term(term) = pattern else {
        return None;
    };
    let PatternTerm::Apply { constructor, args } = term else {
        return None;
    };

    // Is THIS apply the binder binding `scope_var`? It must be a binder constructor whose sole
    // argument is exactly `Var(scope_var)`.
    if let [AstPattern::Term(PatternTerm::Var(v))] = args.as_slice() {
        if v == scope_var {
            if let Some(cat) = language.category_of_constructor(constructor) {
                for variant in collect_category_variants(cat, language) {
                    match variant {
                        VariantKind::Binder { label, binder_cat, body_cat, .. }
                            if &label == constructor =>
                        {
                            return Some(BinderScope {
                                binder_label: label,
                                binder_cat: cat.clone(),
                                binder_var_cat: binder_cat,
                                body_cat,
                                multi: false,
                            });
                        },
                        VariantKind::MultiBinder { label, binder_cat, body_cat, .. }
                            if &label == constructor =>
                        {
                            return Some(BinderScope {
                                binder_label: label,
                                binder_cat: cat.clone(),
                                binder_var_cat: binder_cat,
                                body_cat,
                                multi: true,
                            });
                        },
                        _ => {},
                    }
                }
            }
        }
    }

    // Otherwise recurse into the argument patterns.
    for arg in args {
        if let Some(found) = find_binder_scope(language, arg, scope_var) {
            return Some(found);
        }
    }
    None
}

/// Whether a pattern contains a `Pattern::Collection`/`Map`/`Zip` metapattern anywhere (used to
/// reject an AC-collection-nested substitution-rewrite LHS — MF4).
fn pattern_contains_collection(pattern: &AstPattern) -> bool {
    match pattern {
        AstPattern::Collection { .. }
        | AstPattern::Map { .. }
        | AstPattern::Zip { .. }
        // An indexed element IS a collection touch: the rule reaches into a `Vec`
        // payload, so it needs the same collection-comprehension lowering path.
        | AstPattern::IndexedVec { .. } => true,
        AstPattern::Term(term) => match term {
            PatternTerm::Apply { args, .. } => args.iter().any(pattern_contains_collection),
            PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
                pattern_contains_collection(body)
            },
            PatternTerm::Subst { term, replacement, .. } => {
                pattern_contains_collection(term) || pattern_contains_collection(replacement)
            },
            PatternTerm::MultiSubst { scope, replacements } => {
                pattern_contains_collection(scope)
                    || replacements.iter().any(pattern_contains_collection)
            },
            PatternTerm::Var(_) => false,
        },
    }
}

/// (A-3) One structured element of a Comm rule's AC bag LHS — a constructor applied to bare
/// variables (e.g. `(PFor N cont)`, `(POutput N Q)`).
#[derive(Debug, Clone)]
pub(crate) struct CommElementInfo {
    /// The element constructor label (e.g. `PFor`).
    pub(crate) constructor: Ident,
    /// The category the constructor builds (e.g. `Proc`).
    pub(crate) category: Ident,
    /// The bare-variable arguments, in LHS order. A trailing `^x.body` binder-scope argument
    /// contributes its BODY variable (see [`comm_structured_element`]), so `args.last()` is the
    /// scope variable under either spelling.
    pub(crate) args: Vec<Ident>,
    /// Whether the LAST argument was written as an EXPLICIT binder abstraction `^x.body` (the
    /// omnibus π spelling `(PIn n ^x.p)`) rather than a bare scope variable (`(PFor N cont)`).
    /// Both lower to the SAME `[pre…, BinderArity(1), body]` element pattern — the pattern binder
    /// name `x` is α-irrelevant because the dispatch arm rebuilds a FRESH binder before
    /// substituting — so this only records the surface form (and marks the argument as a binder
    /// SCOPE, which may never be spliced raw into a reduct).
    pub(crate) scope_is_explicit_lambda: bool,
    /// Whether this element is a single `Binder` constructor whose SCOPE (last arg) is the
    /// substitution scope var (the receive continuation `cont`).
    pub(crate) is_binder: bool,
}

/// (A-3 / D10) One fixed element of a Comm rule's AC bag REDUCT, in RHS order.
///
/// The reduct is a bag `op{ r_0, …, r_{m-1}, ...rest }` with `m ≥ 1` elements, EXACTLY ONE of which
/// is the host-computed substitution; the others are σ-delivered LHS variables. `m = 1` is the
/// ASYNCHRONOUS communication `op{ (eval cont Q), ...rest }` (Rholang/`CommDemo`); `m = 2` is the
/// SYNCHRONOUS π communication `op{ (eval ^x.p m), q, ...rest }` — the output's continuation `q`
/// runs in parallel with the substituted receive continuation (`c!x.P | c?y.Q ⇒ P | Q{x/y}`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CommReductElement {
    /// The HOST-COMPUTED substitution element `(eval scope arg)` — `cont[Q/y]`. Exactly one reduct
    /// element is of this kind (the lane's defining feature); the dispatch arm binds it to the
    /// reserved `__comm_reduct` σ slot.
    Substitution,
    /// A σ-DELIVERED reduct element: a bare LHS-element argument variable, spliced straight from the
    /// AC match's σ (never host-computed) — exactly as [`StructuralAcRewrite::reduct_vars`]. It may
    /// never be a binder SCOPE (splicing an open body would let the bound variable escape), which
    /// [`is_comm_rewrite`] enforces.
    Var(Ident),
}

/// (A-3) The canonical single-receive Rholang COMMUNICATION rule, classified for typed-native
/// lowering:
///
/// ```text
/// op{ (Recv N cont), (Send N Q), ...rest }  ~>  op{ (eval cont Q), ...rest }              (m = 1)
/// op{ (Recv N ^y.cont), (Send N Q P), ...rest }  ~>  op{ (eval ^y.cont Q), P, ...rest }   (m = 2)
/// ```
///
/// i.e. `for(y <- N){ cont } | N!(Q) ~> cont[Q/y]` (asynchronous output) and its SYNCHRONOUS dual
/// `N?y.cont | N!Q.P ~> cont[Q/y] | P` (the omnibus π `Comm`, `omnibus.tex:1988-1989`), spliced back
/// into the residual bag. The two structured elements share the NON-LINEAR channel var `N` (once
/// each); one element is a single `Binder` whose scope is `cont` (written either as a bare scope
/// variable or as an explicit `^y.cont` abstraction); and the RHS is a with-rest bag over the SAME
/// `op` + `rest` whose `m ≥ 1` fixed elements are EXACTLY ONE single-argument substitution
/// `(eval cont Q)` plus `m - 1` bare LHS variables. This is the shape the shared `comm_rule_shape`
/// un-skips to a `CommRewrite` σ-receiver; classifying it here routes it onto the TYPED native lane
/// so `dovetail_report_for` produces the Comm justification (σ + contractum) the injection reads.
/// Everything is derived from `LanguageDef` (no per-language hardcoding); it fail-closes on every
/// other shape (verified to REJECT the β `is_substitution_rewrite` shape and any structural AC).
#[derive(Debug, Clone)]
pub(crate) struct CommRewrite {
    /// `<Lang>::rewrite::<name>` — the native-rule label (matches the Comm σ-receiver's label).
    pub(crate) label: String,
    /// The AC bag operator constructor (e.g. `PPar`) …
    pub(crate) op_label: Ident,
    /// … and the category it builds (e.g. `Proc`) — the reduced bag's category.
    pub(crate) op_cat: Ident,
    /// The two structured elements (LHS order); exactly one has `is_binder == true`.
    pub(crate) elements: Vec<CommElementInfo>,
    /// The index (0/1) of the binder element within `elements`.
    pub(crate) binder_element_index: usize,
    /// The shared non-linear channel variable `N`.
    pub(crate) nonlinear_var: Ident,
    /// The `...rest` remainder variable.
    pub(crate) rest_var: Ident,
    /// The substitution scope variable (= the binder element's scope arg = `cont`).
    pub(crate) scope_var: Ident,
    /// The substitution replacement variable (= the sent name `Q`).
    pub(crate) arg_var: Ident,
    /// (D10) The `m ≥ 1` reduct elements in RHS order — exactly one
    /// [`CommReductElement::Substitution`] plus `m - 1` σ-delivered
    /// [`CommReductElement::Var`]s. `[Substitution]` is the asynchronous single-element reduct the
    /// lane originally admitted; `[Substitution, Var(q)]` is the omnibus π synchronous reduct.
    pub(crate) reduct_elements: Vec<CommReductElement>,
    /// The bound-variable (domain) category of the binder element (e.g. `Name`) — selects the
    /// generated `substitute_<binder_var_cat>` and the `build_<binder_var_cat>_d` for the arg.
    pub(crate) binder_var_cat: Ident,
    /// The body (codomain) category of the binder element (e.g. `Proc`) — the reconstructed body
    /// category, the substitution result category, and the reduced bag's element category.
    pub(crate) body_cat: Ident,
}

/// Extract `op{ elements, ...rest }` from a constructor applied to a SINGLE HashBag collection
/// (accepting `None` — inferred from the constructor's grammar — or an explicit `HashBag`, exactly
/// as the shared `ac_rule_shape`/`collection_apply`). Returns the op constructor, the element
/// patterns, and the optional `rest` remainder variable.
fn comm_collection_apply(pattern: &AstPattern) -> Option<(&Ident, &[AstPattern], Option<&Ident>)> {
    let AstPattern::Term(PatternTerm::Apply { constructor, args }) = pattern else {
        return None;
    };
    let [AstPattern::Collection { coll_type, elements, rest }] = args.as_slice() else {
        return None;
    };
    match coll_type {
        None | Some(CollectionType::HashBag) => {},
        Some(_) => return None,
    }
    Some((constructor, elements.as_slice(), rest.as_ref()))
}

/// A structured element `C(v_0, …, v_{m-1})` — a constructor applied to bare variables. Returns
/// `None` for a bare variable or any non-variable argument.
///
/// (D10) The LAST argument may ALSO be an EXPLICIT single binder abstraction `^x.body` whose body is
/// a bare variable — the omnibus π spelling `(PIn n ^x.p)` (`omnibus.tex:1988`) of the same element
/// the Rholang/`CommDemo` rules write as a bare scope variable `(PFor N cont)`. It is admitted ONLY
/// when `C` is a single `VariantKind::Binder` of its category, i.e. only where the element really
/// does lower to the FIX-A `[pre-scope children…, BinderArity(1), body]` node whose LAST child is
/// the binder BODY. Under that condition the two spellings produce the SAME element pattern
/// ([`typed_report::comm_element_pattern`] binds the last arg to the BODY class either way) and the
/// SAME reduct (the dispatch arm rebuilds a FRESH binder before substituting, so the pattern's
/// binder name `x` is α-irrelevant — it never reaches the generated code). A `^x.body` in any other
/// position, a `^[xs].body` multi-binder, a non-variable body, or a non-`Binder` constructor all
/// fail closed.
fn comm_structured_element(
    language: &LanguageDef,
    pattern: &AstPattern,
) -> Option<CommElementInfo> {
    let AstPattern::Term(PatternTerm::Apply { constructor, args }) = pattern else {
        return None;
    };
    let category = language.category_of_constructor(constructor)?.clone();
    let mut vars: Vec<Ident> = Vec::with_capacity(args.len());
    let mut scope_is_explicit_lambda = false;
    for (index, arg) in args.iter().enumerate() {
        match arg {
            AstPattern::Term(PatternTerm::Var(v)) => vars.push(v.clone()),
            // `^x.body` — admitted only as the LAST argument of a single-`Binder` constructor.
            AstPattern::Term(PatternTerm::Lambda { body, .. })
                if index + 1 == args.len()
                    && constructor_is_single_binder(language, &category, constructor) =>
            {
                let AstPattern::Term(PatternTerm::Var(body_var)) = body.as_ref() else {
                    return None;
                };
                vars.push(body_var.clone());
                scope_is_explicit_lambda = true;
            },
            _ => return None,
        }
    }
    Some(CommElementInfo {
        constructor: constructor.clone(),
        category,
        args: vars,
        scope_is_explicit_lambda,
        is_binder: false,
    })
}

/// Whether `constructor` is a single [`VariantKind::Binder`] (NOT a `MultiBinder`) of `category` —
/// the gate that admits an explicit `^x.body` scope argument in [`comm_structured_element`] and the
/// same predicate the binder-element selection in [`is_comm_rewrite`] re-derives (with its binder /
/// body categories).
fn constructor_is_single_binder(
    language: &LanguageDef,
    category: &Ident,
    constructor: &Ident,
) -> bool {
    collect_category_variants(category, language)
        .into_iter()
        .any(
            |variant| matches!(variant, VariantKind::Binder { label, .. } if &label == constructor),
        )
}

/// The unique variable shared by EVERY element, exactly once in each — the non-linear channel
/// variable `N`. Returns `None` unless exactly one such variable exists (mirrors
/// `rho_net_lower::unique_shared_variable`, kept self-contained).
fn comm_unique_shared_var(elements: &[CommElementInfo]) -> Option<Ident> {
    let mut shared: Option<Ident> = None;
    let first = elements.first()?;
    for candidate in &first.args {
        let appears_once_in_all = elements
            .iter()
            .all(|element| element.args.iter().filter(|v| *v == candidate).count() == 1);
        if appears_once_in_all && shared.replace(candidate.clone()).is_some() {
            return None; // a second shared variable — ambiguous non-linear guard.
        }
    }
    shared
}

/// The RHS substitution element `(eval scope arg)` — a `MultiSubst`/`Subst` whose scope and single
/// replacement are bare variables. Returns `(scope_var, arg_var)`.
fn comm_subst_element(pattern: &AstPattern) -> Option<(Ident, Ident)> {
    let AstPattern::Term(term) = pattern else {
        return None;
    };
    let (scope, arg): (&AstPattern, &AstPattern) = match term {
        PatternTerm::MultiSubst { scope, replacements } if replacements.len() == 1 => {
            (scope.as_ref(), &replacements[0])
        },
        PatternTerm::Subst { term, replacement, .. } => (term.as_ref(), replacement.as_ref()),
        _ => return None,
    };
    match (scope, arg) {
        (
            AstPattern::Term(PatternTerm::Var(scope_var)),
            AstPattern::Term(PatternTerm::Var(arg_var)),
        ) => Some((scope_var.clone(), arg_var.clone())),
        _ => None,
    }
}

/// (A-3 / D10) Classify a rewrite as the canonical single-receive Rholang COMMUNICATION rule
/// ([`CommRewrite`]), or `None`. Fail-closed on every other shape: a non-HashBag collection, ≠2
/// structured elements, 0/≥2 shared variables, an RHS that is not a with-rest bag over the SAME op +
/// rest, an RHS with ≠1 substitution element, an RHS non-substitution element that is not a bare LHS
/// variable or that is a binder SCOPE, or a scope that is not the last arg of a single `Binder`
/// element.
///
/// # (D10) Reduct arity
///
/// The reduct bag admits `m ≥ 1` fixed elements: EXACTLY ONE substitution `(eval scope arg)` plus
/// `m - 1` bare LHS variables delivered straight from the AC match's σ. `m = 1` is the ASYNCHRONOUS
/// output (Rholang / `CommDemo`: `op{ (eval cont Q), ...rest }`); `m = 2` is the omnibus's
/// SYNCHRONOUS π `Comm` (`omnibus.tex:1988-1989`)
///
/// ```text
/// (PPar {(PIn n ^x.p), (POut n m q), ...rest})  ~>  (PPar {(eval ^x.p m), q, ...rest})
/// ```
///
/// whose output `n!m.q` carries the continuation `q`, so the contractum is the PARALLEL COMPOSITION
/// `p[m/x] | q` — which is exactly what the reduct bag `op{…}` means, `op` being the AC (HashBag)
/// parallel operator the LHS already matched over. The arity-1 restriction was never a semantic
/// constraint on the contractum: it was the shape the lane was first written for.
///
/// A σ-delivered reduct element may NOT be a binder SCOPE (the last argument of an element whose
/// constructor is a `Binder`/`MultiBinder`): splicing a raw binder body into the reduct would let
/// the bound variable escape its binder. That is the ONE genuinely semantic side condition the
/// generalization adds, and it fails closed.
pub(crate) fn is_comm_rewrite(language: &LanguageDef, rw: &RewriteRule) -> Option<CommRewrite> {
    // Premises: congruence-only (same gate as the structural lowering).
    if !rw.premises.iter().all(premise_supported) {
        return None;
    }

    // LHS: op{ E0, E1, ...rest } — a with-rest HashBag with exactly two structured elements.
    let (op_label, lhs_elements, lhs_rest) = comm_collection_apply(&rw.left)?;
    let rest_var = lhs_rest?.clone();
    if lhs_elements.len() != 2 {
        return None;
    }
    let mut elements: Vec<CommElementInfo> = Vec::with_capacity(2);
    for element in lhs_elements {
        elements.push(comm_structured_element(language, element)?);
    }

    // The shared non-linear channel variable.
    let nonlinear_var = comm_unique_shared_var(&elements)?;

    // RHS: op{ r_0, …, r_{m-1}, ...rest } — the SAME op + rest, `m ≥ 1` fixed elements.
    let (rhs_op, rhs_elements, rhs_rest) = comm_collection_apply(&rw.right)?;
    let rhs_rest = rhs_rest?;
    if rhs_op != op_label || rhs_elements.is_empty() || rhs_rest != &rest_var {
        return None;
    }

    // EXACTLY ONE substitution element; every other fixed element is a bare variable.
    let mut subst_slot: Option<(Ident, Ident)> = None;
    let mut reduct_elements: Vec<CommReductElement> = Vec::with_capacity(rhs_elements.len());
    for element in rhs_elements {
        match comm_subst_element(element) {
            Some(pair) => {
                if subst_slot.replace(pair).is_some() {
                    return None; // ≥2 substitutions — an ambiguous host-computed reduct.
                }
                reduct_elements.push(CommReductElement::Substitution);
            },
            // Not a substitution ⇒ it must be a bare variable (the structural, σ-delivered case).
            None => match element {
                AstPattern::Term(PatternTerm::Var(var)) => {
                    reduct_elements.push(CommReductElement::Var(var.clone()))
                },
                _ => return None,
            },
        }
    }
    // No substitution at all ⇒ this is a STRUCTURAL AC rewrite, not a Comm (mutual exclusion).
    let (scope_var, arg_var) = subst_slot?;

    // The substitution's scope + arg, and every σ-delivered reduct element, must be LHS variables
    // (supplied by the AC match's σ). Materialized up front so the binder marking below may take
    // `elements` mutably.
    let lhs_vars: HashSet<String> = elements
        .iter()
        .flat_map(|element| element.args.iter())
        .map(|var| var.to_string())
        .collect();
    if !lhs_vars.contains(&scope_var.to_string()) || !lhs_vars.contains(&arg_var.to_string()) {
        return None;
    }

    // The binder element: the one whose SCOPE (last arg) is `scope_var` AND whose constructor is a
    // single `Binder` variant of its category. Its bound-variable (`binder_cat`) and body
    // (`body_cat`) categories select the substitution + reconstruction fns.
    let mut binder_info: Option<(usize, Ident, Ident)> = None;
    for (index, element) in elements.iter().enumerate() {
        if element.args.last() != Some(&scope_var) {
            continue;
        }
        for variant in collect_category_variants(&element.category, language) {
            if let VariantKind::Binder { label, binder_cat, body_cat, .. } = variant {
                if label == element.constructor {
                    binder_info = Some((index, binder_cat, body_cat));
                }
            }
        }
    }
    let (binder_element_index, binder_var_cat, body_cat) = binder_info?;
    elements[binder_element_index].is_binder = true;

    // A σ-delivered reduct element must be an LHS variable that is NOT a binder SCOPE — splicing a
    // raw binder body into the reduct would let its bound variable escape (the substitution element
    // is the ONLY sound way to consume a scope).
    let binder_scope_vars: HashSet<String> = elements
        .iter()
        .filter(|element| {
            element.scope_is_explicit_lambda
                || collect_category_variants(&element.category, language)
                    .into_iter()
                    .any(|variant| match variant {
                        VariantKind::Binder { label, .. }
                        | VariantKind::MultiBinder { label, .. } => label == element.constructor,
                        _ => false,
                    })
        })
        .filter_map(|element| element.args.last())
        .map(|scope| scope.to_string())
        .collect();
    for reduct in &reduct_elements {
        let CommReductElement::Var(var) = reduct else {
            continue;
        };
        if !lhs_vars.contains(&var.to_string()) || binder_scope_vars.contains(&var.to_string()) {
            return None;
        }
    }

    let op_cat = language.category_of_constructor(op_label)?.clone();

    Some(CommRewrite {
        label: format!("{}::rewrite::{}", language.name, rw.name),
        op_label: op_label.clone(),
        op_cat,
        elements,
        binder_element_index,
        nonlinear_var,
        rest_var,
        scope_var,
        arg_var,
        reduct_elements,
        binder_var_cat,
        body_cat,
    })
}

/// (Stage 3d) A STRUCTURAL non-linear AC rewrite — the Ambient-calculus `OpenRule`
/// `op{ E0, E1, ...rest } ~> op{ r0, …, r_{m-1}, ...rest }` — classified for typed-native lowering.
/// It is the [`CommRewrite`] shape MINUS the substitution: the two structured elements share the
/// non-linear channel `N`, and the reduct is a PURE STRUCTURAL restructuring (each RHS fixed element
/// `r_j` is a bare LHS-element argument variable — supplied directly by the firing's σ, never
/// host-computed). Everything is derived from `LanguageDef` (no per-language hardcoding); it
/// fail-closes on every other shape (verified to REJECT the β `is_substitution_rewrite` shape and the
/// `is_comm_rewrite` substitution shape).
#[derive(Debug, Clone)]
pub(crate) struct StructuralAcRewrite {
    /// `<Lang>::rewrite::<name>` — the native-rule label (matches the structural-AC σ-receiver's label).
    pub(crate) label: String,
    /// The AC bag operator constructor (e.g. `PPar`) …
    pub(crate) op_label: Ident,
    /// … and the category it builds (e.g. `Proc`) — the reduced bag's category.
    pub(crate) op_cat: Ident,
    /// The `k` structured elements (LHS order); all non-binder.
    pub(crate) elements: Vec<CommElementInfo>,
    /// The shared non-linear channel variable `N`.
    pub(crate) nonlinear_var: Ident,
    /// The `...rest` remainder variable.
    pub(crate) rest_var: Ident,
    /// The `m` RHS fixed element variables, in RHS order — each a bare LHS-element argument (e.g.
    /// `[P, Q]`). The dispatch splices `op{ σ[r0], …, σ[r_{m-1}], ...rest }`.
    pub(crate) reduct_vars: Vec<Ident>,
}

/// (Stage 3d) Classify a rewrite as a STRUCTURAL non-linear AC rewrite ([`StructuralAcRewrite`]), or
/// `None`. Fail-closed on every other shape: a non-HashBag collection, <2 structured elements, a
/// binder element, 0/≥2 shared variables, an RHS that is not a with-rest bag over the SAME op + rest,
/// an RHS fixed element that is NOT a bare variable (the Comm substitution case), or an RHS reduct
/// variable that is not an LHS-element argument.
pub(crate) fn is_structural_ac_rewrite(
    language: &LanguageDef,
    rw: &RewriteRule,
) -> Option<StructuralAcRewrite> {
    // Premises: congruence-only (same gate as the structural lowering).
    if !rw.premises.iter().all(premise_supported) {
        return None;
    }

    // LHS: op{ E0, …, ...rest } — a with-rest HashBag with ≥2 structured elements.
    let (op_label, lhs_elements, lhs_rest) = comm_collection_apply(&rw.left)?;
    let rest_var = lhs_rest?.clone();
    if lhs_elements.len() < 2 {
        return None;
    }
    let mut elements: Vec<CommElementInfo> = Vec::with_capacity(lhs_elements.len());
    for element in lhs_elements {
        let info = comm_structured_element(language, element)?;
        // A structured element must be a plain (non-binder) constructor — a binder element lowers to
        // the 3-child `[pre, BinderArity, body]` node, which the flat element pattern would not
        // match; such a rule is a Comm/substitution shape, handled on its own lane.
        for variant in collect_category_variants(&info.category, language) {
            match variant {
                VariantKind::Binder { label, .. } | VariantKind::MultiBinder { label, .. }
                    if label == info.constructor =>
                {
                    return None;
                },
                _ => {},
            }
        }
        elements.push(info);
    }

    // The shared non-linear channel variable.
    let nonlinear_var = comm_unique_shared_var(&elements)?;

    // RHS: op{ r0, …, ...rest } — the SAME op + rest, all-bare-variable fixed elements (NO subst).
    let (rhs_op, rhs_elements, rhs_rest) = comm_collection_apply(&rw.right)?;
    let rhs_rest = rhs_rest?;
    if rhs_op != op_label || rhs_elements.is_empty() || rhs_rest != &rest_var {
        return None;
    }
    let mut reduct_vars: Vec<Ident> = Vec::with_capacity(rhs_elements.len());
    for element in rhs_elements {
        let AstPattern::Term(PatternTerm::Var(var)) = element else {
            return None; // a substitution / constructor element ⇒ not a structural restructuring.
        };
        reduct_vars.push(var.clone());
    }

    // Every reduct variable must be a bare argument of some LHS element (supplied by the AC match's σ).
    let is_lhs_var = |name: &Ident| elements.iter().any(|e| e.args.iter().any(|v| v == name));
    if !reduct_vars.iter().all(is_lhs_var) {
        return None;
    }

    let op_cat = language.category_of_constructor(op_label)?.clone();

    Some(StructuralAcRewrite {
        label: format!("{}::rewrite::{}", language.name, rw.name),
        op_label: op_label.clone(),
        op_cat,
        elements,
        nonlinear_var,
        rest_var,
        reduct_vars,
    })
}

/// (Stage 4) A DEPTH-2 NESTED structural non-linear AC rewrite (the Ambient `InRule`/`OutRule`,
/// `{ n[{in(m,P), ...q}], m[R], ...s } ~> { m[{ n[{P, ...q}], R }], ...s }` and its `out` dual)
/// classified for typed-native lowering. It GENERALIZES [`StructuralAcRewrite`]: an outer element
/// whose argument is itself a HashBag carrying the capability, sharing a CROSS-LEVEL non-linear
/// channel `M`. Its LHS + RHS lower through the ordinary [`pattern_to_dovetail`] (which already
/// handles the nested `AcApp` + `App` structure), and its dispatch instantiates the re-assembled RHS.
#[derive(Debug, Clone)]
pub(crate) struct NestedStructuralAcRewrite {
    /// `<Lang>::rewrite::<name>` — the native-rule label (matches the nested structural-AC σ-receiver).
    pub(crate) label: String,
    /// The whole LHS pattern — the native-rule LHS ([`pattern_to_dovetail`], which handles nesting).
    pub(crate) left: AstPattern,
    /// The whole RHS pattern — the dispatch arm instantiates it (`pattern_to_dovetail` + `instantiate`).
    pub(crate) right: AstPattern,
    /// The CONSUMED constructor heads `(category, constructor)` — the LHS heads MINUS the RHS heads
    /// (e.g. `PIn` for `InRule`, `POut` for `OutRule`; the PERSISTING `PAmb`/`PPar` are excluded).
    /// These join the MF1 redex-head set so funded 1-best extraction prefers the restructured
    /// contractum over the un-reduced redex (a bag still carrying the consumed capability is heavier).
    pub(crate) consumed_heads: Vec<(Ident, Ident)>,
}

/// Collect every `PatternTerm::Apply` constructor label in `pattern` (recursing through `Apply` args
/// and `Collection` elements). Used to compute the CONSUMED redex heads (LHS constructors MINUS RHS
/// constructors) for the nested structural-AC extraction preference.
fn collect_apply_constructors(pattern: &AstPattern, out: &mut HashSet<String>) {
    match pattern {
        AstPattern::Term(PatternTerm::Apply { constructor, args }) => {
            out.insert(constructor.to_string());
            for arg in args {
                collect_apply_constructors(arg, out);
            }
        },
        AstPattern::Collection { elements, .. } => {
            for element in elements {
                collect_apply_constructors(element, out);
            }
        },
        _ => {},
    }
}

/// (Stage 4) Classify a rewrite as a DEPTH-2 NESTED structural non-linear AC rewrite
/// ([`NestedStructuralAcRewrite`], the Ambient `InRule`/`OutRule`), or `None`. The shape check
/// delegates to the SINGLE-SOURCE-OF-TRUTH `mettail_rholang_codegen::is_nested_structural_ac_rewrite`
/// (so the Dovetail report path and the Rho lowering agree byte-for-byte on which rewrites are nested
/// firings) — it rejects the flat `OpenRule` (no nested element), a Comm/substitution, and any
/// non-nested shape. Premises must be congruence-only (same gate as every structural lowering).
pub(crate) fn is_nested_structural_ac_rewrite(
    language: &LanguageDef,
    rw: &RewriteRule,
) -> Option<NestedStructuralAcRewrite> {
    if !rw.premises.iter().all(premise_supported) {
        return None;
    }
    if !mettail_rholang_codegen::is_nested_structural_ac_rewrite(&rw.left, &rw.right, language) {
        return None;
    }
    // Consumed heads = (constructor heads in LHS) \ (constructor heads in RHS), each with its
    // category (for `op_variant_ident`). `PPar`/`PAmb` persist (appear in both), so only the
    // dissolved capability (`PIn`/`POut`) remains — the head whose disappearance marks the firing.
    let mut left_heads: HashSet<String> = HashSet::new();
    collect_apply_constructors(&rw.left, &mut left_heads);
    let mut right_heads: HashSet<String> = HashSet::new();
    collect_apply_constructors(&rw.right, &mut right_heads);
    let mut consumed_heads: Vec<(Ident, Ident)> = Vec::new();
    for head in &left_heads {
        if right_heads.contains(head) {
            continue;
        }
        let head_ident = format_ident!("{}", head);
        let category = language.category_of_constructor(&head_ident)?.clone();
        consumed_heads.push((category, head_ident));
    }
    Some(NestedStructuralAcRewrite {
        label: format!("{}::rewrite::{}", language.name, rw.name),
        left: rw.left.clone(),
        right: rw.right.clone(),
        consumed_heads,
    })
}

/// Whether any `PatternTerm::Subst`/`MultiSubst` appears anywhere in a pattern (recursing
/// through `Apply`/`Lambda`/`MultiLambda`/`Collection`/`Map`/`Zip` and the substitution
/// sub-patterns themselves). A substitution in a rewrite RHS means the language performs
/// β-style replacement, whose contractum is a NEW typed term that the runtime must
/// reconstruct from the e-graph — hence `dovetail_normal_term` is meaningful for it.
///
/// This is a self-contained structural detector for the MF7 gate; it deliberately does NOT
/// depend on E1's stricter `is_substitution_rewrite` shape-classifier (E1 is a separate
/// surface). Being more permissive here is safe: it can only enable `dovetail_normal_term`,
/// which is itself fail-closed (`Err` on a stuck reconstruction).
fn pattern_contains_substitution(pattern: &AstPattern) -> bool {
    match pattern {
        AstPattern::Term(term) => pattern_term_contains_substitution(term),
        AstPattern::Collection { elements, .. } => {
            elements.iter().any(pattern_contains_substitution)
        },
        AstPattern::Map { collection, body, .. } => {
            pattern_contains_substitution(collection) || pattern_contains_substitution(body)
        },
        AstPattern::Zip { first, second } => {
            pattern_contains_substitution(first) || pattern_contains_substitution(second)
        },
        AstPattern::IndexedVec { element, .. } => pattern_contains_substitution(element),
    }
}

fn pattern_term_contains_substitution(term: &PatternTerm) -> bool {
    match term {
        PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. } => true,
        PatternTerm::Apply { args, .. } => args.iter().any(pattern_contains_substitution),
        PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
            pattern_contains_substitution(body)
        },
        PatternTerm::Var(_) => false,
    }
}

/// Whether a generated language should also expose `dovetail_normal_term` (E2.2) — the method
/// that reduces a term to a typed Dovetail normal form and reconstructs it as a typed AST term
/// (rather than the `dovetail_report_for` report projection).
///
/// MF7 gate (generic; derived entirely from `LanguageDef` — no per-language hardcoding):
/// emit it iff the language
///   1. has a **substitution rewrite** (a rewrite whose RHS contains a `Subst`/`MultiSubst`),
///      i.e. it performs β-style replacement producing a fresh typed contractum; OR
///   2. has a **typed-path structural rewrite/equation** — a non-congruence rewrite, or any
///      equation (equations are structural rewrites the typed path turns into bidirectional
///      `RewriteRule`s); these can rewrite a term into a different typed normal form (e.g.
///      Rholang's `Comm`/`PNew` AC equations); OR
///   3. **declares a Rho/RhoMachine backend capability**. Raw `language!` codegen advertises
///      `NO_RUNTIME_BACKEND_CAPABILITIES` in metadata (backends are installed by runtime
///      wrappers, not the macro), so the closest `LanguageDef`-level signal is a `guards {
///      channels { … } }` block (channels + join patterns are the Rho-style COMM substrate).
///
/// A pure scalar-fold language (native-output folds only, no structural rewrites/equations, no
/// substitution, no channels — e.g. Calculator) satisfies none of these and is NOT given the
/// method. (Such a language also never reaches the typed-fold path at all — it stays on the
/// `EGraph<String>` path — so the gate is doubly fail-closed for it.)
pub(crate) fn needs_normal_term(language: &LanguageDef) -> bool {
    let has_substitution_rewrite = language
        .rewrites
        .iter()
        .any(|rw| pattern_contains_substitution(&rw.right));

    let has_structural_rewrite_or_equation =
        language.rewrites.iter().any(|rw| !rw.is_congruence_rule())
            || !language.equations.is_empty();

    let declares_rho_backend = language
        .guard_config
        .as_ref()
        .and_then(|gc| gc.channels.as_ref())
        .is_some_and(|ch| !ch.channel_categories.is_empty() || !ch.join_patterns.is_empty());

    has_substitution_rewrite || has_structural_rewrite_or_equation || declares_rho_backend
}

fn to_snake(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 4);
    for (i, ch) in s.chars().enumerate() {
        if ch.is_ascii_uppercase() {
            if i > 0 {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

fn lit(value: &str) -> LitStr {
    LitStr::new(value, Span::call_site())
}

fn constructor_label(language: &LanguageDef, constructor: &Ident) -> Result<String, String> {
    let category = language
        .category_of_constructor(constructor)
        .ok_or_else(|| format!("constructor `{constructor}` has no category"))?;
    Ok(format!("{}::{}::{}", language.name, category, constructor))
}

fn category_lowering_fn(category: &Ident) -> Ident {
    format_ident!("__mettail_dovetail_add_{}", to_snake(&category.to_string()))
}

/// The e-graph operator expression for a constructor in a rewrite-rule pattern. With
/// `enum_id = None` (the `EGraph<String>` path) it is the `"Lang::Cat::Ctor"` label string;
/// with `enum_id = Some(L)` (the typed fold path) it is the typed op variant `L::<Cat>_<Ctor>`,
/// so `RewriteRule<L>` patterns match the typed lowering's nodes.
fn constructor_op_expr(
    language: &LanguageDef,
    constructor: &Ident,
    enum_id: Option<&Ident>,
) -> Result<TokenStream, String> {
    match enum_id {
        None => {
            let label = lit(&constructor_label(language, constructor)?);
            Ok(quote! { #label.to_string() })
        },
        Some(enum_id) => {
            let category = language
                .category_of_constructor(constructor)
                .ok_or_else(|| format!("constructor `{constructor}` has no category"))?;
            let variant = op_enum::op_variant_ident(&category, constructor);
            Ok(quote! { #enum_id::#variant })
        },
    }
}

fn opaque_leaf_expr(label: TokenStream, payload: TokenStream) -> TokenStream {
    quote! {
        eg.add(::dovetail::egraph::ENode::leaf(format!("{}::{:?}", #label, #payload)))
    }
}

/// Lower an associative-commutative bag (`HashBag<ElemCat>`) to an n-ary
/// [`dovetail::egraph::ENode`] whose children are the lowered bag elements (each
/// with multiplicity) SORTED by `canonical_class_key`.
///
/// Sorting yields the deterministic canonical (sorted) bag order; the stored
/// order is only a HINT — the AC matcher recomputes the multiset key fresh from
/// current union-find representatives at match time (R1), so a later `rebuild`
/// re-canonicalization cannot lose AC matches.
///
/// `bag_expr` must evaluate to a value exposing `len()` and
/// `iter_elements() -> impl Iterator<Item = &ElemCat>` (the `HashBag` API).
/// `element_add` is the element category's `__mettail_dovetail_add_<cat>` fn.
fn ac_bag_lowering(label: &LitStr, element_add: &Ident, bag_expr: TokenStream) -> TokenStream {
    quote! {
        {
            let __bag = #bag_expr;
            let mut __children: Vec<::dovetail::egraph::EClassId> =
                ::std::vec::Vec::with_capacity(__bag.len());
            for __elem in __bag.iter_elements() {
                __children.push(#element_add(eg, __elem));
            }
            // Canonical (sorted) bag order; cache each key (one computation each).
            __children.sort_by_cached_key(|__c| eg.canonical_class_key(*__c));
            eg.add(::dovetail::egraph::ENode::new(#label.to_string(), __children))
        }
    }
}

/// (#101) The e-graph CARRIER a collection type gets on the typed fold path. TOTAL over
/// [`CollectionType`] with **no wildcard**, so a new container must be classified here before
/// it can be lowered at all.
///
/// This replaces the former `coll_type_is_ac_bag` boolean, whose defect was not its answer but
/// its ARITY: two outcomes cannot express three carriers, so every non-`HashBag` container was
/// forced through the one lossy leaf and a `Vec` — which has a perfectly good stored order —
/// was indistinguishable from a `HashMap`, which has none.
///
/// | container | carrier | why |
/// |---|---|---|
/// | `HashBag` | [`AcBag`](CollectionCarrier::AcBag) | the genuine AC multiset (commutative, with multiplicity), so sorting its lowered children by canonical key is sound and the AC matcher may permute them |
/// | `Vec` | [`OrderedSeq`](CollectionCarrier::OrderedSeq) | ordered and non-commutative: its `Debug` is deterministic AND `Eq`-agreeing, so the whole value can be carried VERBATIM in a labelled leaf and read back losslessly |
/// | `HashSet` / `HashMap` / `PathMap` | [`Opaque`](CollectionCarrier::Opaque) | ★ DELIBERATE. `Debug` does not agree with `Eq` for these — which is exactly why [`op_enum::literal_payload_write_content`] routes Bag/Map/Set through their SORTED `Display` — so there is no stored order to invert. A labelled leaf over their `Debug` would claim an inverse that does not exist. |
///
/// ⚠ `None` (a field with no recorded container) is `Opaque` for the same reason as the last
/// row: without knowing the container we cannot claim an inverse. In practice it is
/// unreachable — [`crate::gen::term_ops::subst::variant_kind_from_items`] always records a
/// `coll_type` for a collection field — so this is a fail-closed default, not a live case.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CollectionCarrier {
    /// `HashBag` — an n-ary AC bag node whose children the AC matcher may permute.
    AcBag,
    /// `Vec` — a payload-bearing ORDERED leaf (`FieldSeq<Elem>(Vec<Elem>)`), invertible.
    OrderedSeq,
    /// `HashSet` / `HashMap` / `PathMap` — the lossy `FieldOpaque(Debug)` spine leaf, with no
    /// inverse. A fold parameter of one of these is DECLINED, naming the type.
    Opaque,
}

/// Classify a collection type's carrier. THE single classification; every other predicate in
/// this module is a projection of it, so the AC lane and the ordered lane cannot drift apart.
pub(crate) fn collection_carrier(coll_type: Option<&CollectionType>) -> CollectionCarrier {
    match coll_type {
        Some(CollectionType::HashBag) => CollectionCarrier::AcBag,
        Some(CollectionType::Vec) => CollectionCarrier::OrderedSeq,
        Some(CollectionType::HashSet)
        | Some(CollectionType::HashMap)
        | Some(CollectionType::PathMap)
        | None => CollectionCarrier::Opaque,
    }
}

/// Whether a collection type is an associative-commutative MULTISET that gets the
/// n-ary canonical bag lowering — the `AcBag` projection of [`collection_carrier`].
///
/// ⚠ This is the predicate the **`EGraph<String>`** path consumes, and it is deliberately
/// coarser than the carrier: on that path `Vec` keeps the prior opaque-leaf lowering, because
/// the String path has no typed op-enum to hang a labelled `FieldSeq` variant on and no
/// reconstructor to invert it with. The ~30 untyped-path languages (`Json`'s 52 `Vec<` fields,
/// `Ambient`'s 8) therefore emit byte-identical output across #101 — that identity is the
/// change's strongest control.
fn coll_type_is_ac_bag(coll_type: Option<&CollectionType>) -> bool {
    matches!(collection_carrier(coll_type), CollectionCarrier::AcBag)
}

fn field_child_expr(
    owner_label: &str,
    field_index: usize,
    field: &FieldInfo,
    field_var: &Ident,
) -> TokenStream {
    let none_label = lit(&format!("{owner_label}::field{field_index}::None"));
    let opaque_label = lit(&format!("{owner_label}::field{field_index}::opaque"));
    let collection_label = lit(&format!("{owner_label}::field{field_index}::collection"));
    let child_fn = category_lowering_fn(&field.category);
    let field_kind = NonTerminalKind::classify(&field.category.to_string());
    if field_kind.is_builtin() {
        let leaf = opaque_leaf_expr(quote! { #opaque_label }, quote! { #field_var });
        return quote! { #leaf };
    }

    if field.is_optional {
        if field.is_predicate || field.is_opaque_leaf() {
            // L9-3: an optional token-text capture (`Option<String>`) → present
            // text is an opaque leaf, absence a distinct nullary leaf.
            let leaf = opaque_leaf_expr(quote! { #opaque_label }, quote! { __pred });
            return quote! {
                match #field_var.as_ref() {
                    Some(__pred) => #leaf,
                    None => eg.add(::dovetail::egraph::ENode::leaf(#none_label.to_string())),
                }
            };
        }
        if field.is_collection {
            if coll_type_is_ac_bag(field.coll_type.as_ref()) {
                // Optional n-ary AC bag field (HashBag): lower the present bag
                // to a sorted-by-canonical-key child list (mirrors the
                // VariantKind::Collection lowering); a missing collection is a
                // distinct nullary leaf.
                let body = ac_bag_lowering(&collection_label, &child_fn, quote! { __values });
                return quote! {
                    match #field_var.as_ref() {
                        Some(__values) => #body,
                        None => eg.add(::dovetail::egraph::ENode::leaf(#none_label.to_string())),
                    }
                };
            }
            let leaf = opaque_leaf_expr(quote! { #collection_label }, quote! { __values });
            return quote! {
                match #field_var.as_ref() {
                    Some(__values) => #leaf,
                    None => eg.add(::dovetail::egraph::ENode::leaf(#none_label.to_string())),
                }
            };
        }
        return quote! {
            match #field_var.as_ref() {
                Some(__inner) => #child_fn(eg, __inner.as_ref()),
                None => eg.add(::dovetail::egraph::ENode::leaf(#none_label.to_string())),
            }
        };
    }

    if field.is_predicate || field.is_opaque_leaf() {
        // L9-3: a token-text capture (`String`) lowers to an opaque e-graph leaf
        // — a token's text is atomic data, never a recursible subterm (mirrors
        // the predicate leaf; branch BEFORE reading `category`).
        let leaf = opaque_leaf_expr(quote! { #opaque_label }, quote! { #field_var });
        return quote! { #leaf };
    }

    if field.is_collection {
        if coll_type_is_ac_bag(field.coll_type.as_ref()) {
            // Non-optional n-ary AC bag field (HashBag): lower to a
            // sorted-by-canonical-key child list (same as VariantKind::Collection).
            return ac_bag_lowering(&collection_label, &child_fn, quote! { #field_var });
        }
        let leaf = opaque_leaf_expr(quote! { #collection_label }, quote! { #field_var });
        return quote! { #leaf };
    }

    quote! { #child_fn(eg, #field_var.as_ref()) }
}

fn regular_arm(
    language: &LanguageDef,
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
) -> TokenStream {
    let owner = format!("{}::{}::{}", language.name, category, label);
    let owner_lit = lit(&owner);
    let field_vars: Vec<Ident> = (0..fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let child_exprs: Vec<TokenStream> = fields
        .iter()
        .zip(field_vars.iter())
        .enumerate()
        .map(|(i, (field, var))| field_child_expr(&owner, i, field, var))
        .collect();
    quote! {
        #category::#label(#(#field_vars),*) => {
            let __children = vec![#(#child_exprs),*];
            eg.add(::dovetail::egraph::ENode::new(#owner_lit.to_string(), __children))
        }
    }
}

fn binder_arm(
    language: &LanguageDef,
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    multi: bool,
) -> TokenStream {
    let owner = format!("{}::{}::{}", language.name, category, label);
    let owner_lit = lit(&owner);
    let binder_label = lit(&format!("{owner}::binder"));
    let pre_vars: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("field_{i}"))
        .collect();
    let scope_var = format_ident!("scope");
    let pre_child_exprs: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(pre_vars.iter())
        .enumerate()
        .map(|(i, (field, var))| field_child_expr(&owner, i, field, var))
        .collect();
    let body_fn = category_lowering_fn(category);
    // (FIX-A) The binder position is lowered to an ANONYMOUS, arity-only marker
    // — never the binder's `FreeVar` identity. moniker `Binder`'s `Debug`/`Hash`
    // expose the `FreeVar`'s `unique_id` (a process-global counter freshened by
    // every `unbind`), so a `{:?}` label leaked a run-varying, alpha-irrelevant
    // value into the e-graph `content_key`. The body (lowered via `unsafe_body`)
    // already carries the de-Bruijn `BoundVar{scope,binder}` coordinates that
    // alpha-canonically identify each bound occurrence, so the binder position
    // must contribute only its arity.
    let binder_child = if multi {
        quote! {
            eg.add(::dovetail::egraph::ENode::leaf(format!(
                "{}::arity::{}",
                #binder_label,
                #scope_var.unsafe_pattern().len()
            )))
        }
    } else {
        quote! {
            eg.add(::dovetail::egraph::ENode::leaf(format!(
                "{}::arity::1",
                #binder_label
            )))
        }
    };

    quote! {
        #category::#label(#(#pre_vars,)* #scope_var) => {
            let __binder = #binder_child;
            let __body = #body_fn(eg, #scope_var.unsafe_body().as_ref());
            let __children = vec![#(#pre_child_exprs,)* __binder, __body];
            eg.add(::dovetail::egraph::ENode::new(#owner_lit.to_string(), __children))
        }
    }
}

fn category_lowering(language: &LanguageDef, category: &Ident) -> TokenStream {
    let fn_name = category_lowering_fn(category);
    let arms: Vec<TokenStream> = collect_category_variants(category, language)
        .into_iter()
        .map(|variant| match variant {
            // ★ #141 G5 — see `VariantKind::Refused`.
            VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
            VariantKind::Var { label } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                quote! {
                    #category::#label(value) => {
                        eg.add(::dovetail::egraph::ENode::leaf(format!("{}::{:?}", #owner, value)))
                    }
                }
            },
            // Stage 0 identity — STAYS.
            VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                quote! {
                    #category::#label(value) => {
                        eg.add(::dovetail::egraph::ENode::leaf(format!("{}::{:?}", #owner, value)))
                    }
                }
            },
            VariantKind::Nullary { label } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                quote! {
                    #category::#label => {
                        eg.add(::dovetail::egraph::ENode::leaf(#owner.to_string()))
                    }
                }
            },
            VariantKind::Regular { label, fields } => {
                regular_arm(language, category, &label, &fields)
            },
            VariantKind::Collection { label, element_cat, coll_type } => {
                let owner = lit(&format!("{}::{}::{}", language.name, category, label));
                if coll_type_is_ac_bag(Some(&coll_type)) {
                    // n-ary AC bag lowering (HashBag). See `ac_bag_lowering`.
                    let element_add = category_lowering_fn(&element_cat);
                    let body = ac_bag_lowering(&owner, &element_add, quote! { values });
                    quote! {
                        #category::#label(values) => #body
                    }
                } else {
                    // Non-AC collection (Vec/HashSet/HashMap): opaque leaf
                    // (unchanged prior behavior — the AC engine consumes only
                    // HashBag bag nodes today).
                    quote! {
                        #category::#label(values) => {
                            eg.add(::dovetail::egraph::ENode::leaf(format!(
                                "{}::{:?}",
                                #owner,
                                values,
                            )))
                        }
                    }
                }
            },
            VariantKind::Binder { label, pre_scope_fields, .. } => {
                binder_arm(language, category, &label, &pre_scope_fields, false)
            },
            VariantKind::MultiBinder { label, pre_scope_fields, .. } => {
                binder_arm(language, category, &label, &pre_scope_fields, true)
            },
        })
        .collect();

    quote! {
        fn #fn_name(
            eg: &mut ::dovetail::egraph::EGraph<String>,
            term: &#category,
        ) -> ::dovetail::egraph::EClassId {
            match term {
                #(#arms),*
            }
        }
    }
}

fn pattern_to_dovetail(
    language: &LanguageDef,
    pattern: &AstPattern,
    enum_id: Option<&Ident>,
) -> Result<TokenStream, String> {
    match pattern {
        AstPattern::Term(term) => pattern_term_to_dovetail(language, term, enum_id),
        // A collection directly under a constructor is lowered to an AC bag in
        // the `PatternTerm::Apply` arm (which supplies the operator label). A
        // bare/nested collection with no enclosing constructor has no operator and
        // is not produced by the current grammar — fail closed.
        AstPattern::Collection { .. } => {
            Err("a collection metapattern must be the argument of a constructor (AC bag); a bare collection has no operator".into())
        },
        AstPattern::Map { .. } => {
            Err("map metapatterns require collection-comprehension lowering".into())
        },
        AstPattern::Zip { .. } => {
            Err("zip metapatterns require collection-comprehension lowering".into())
        },
        AstPattern::IndexedVec { .. } => {
            Err("indexed-vec metapatterns require collection-comprehension lowering".into())
        },
    }
}

fn pattern_term_to_dovetail(
    language: &LanguageDef,
    term: &PatternTerm,
    enum_id: Option<&Ident>,
) -> Result<TokenStream, String> {
    match term {
        PatternTerm::Var(var) => {
            if let Some(rule) = language.get_constructor(var) {
                let op = constructor_op_expr(language, &rule.label, enum_id)?;
                Ok(quote! { ::dovetail::rules::Pattern::leaf(#op) })
            } else {
                let name = lit(&var.to_string());
                Ok(quote! { ::dovetail::rules::Pattern::var(#name) })
            }
        },
        PatternTerm::Apply { constructor, args } => {
            // A constructor whose SOLE argument is a collection metapattern
            // `{ ... }` (e.g. Ambient `(PPar { P, Q, ...rest })`) lowers to an AC
            // bag pattern, with the constructor as the AC operator. The collection
            // has no constructor of its own (see `Pattern::Collection`). The AC
            // lowering is representation-uniform (A-1): on the `EGraph<String>` path
            // (`enum_id = None`) the operator is the label string; on the typed fold
            // path (`enum_id = Some(L)`) it is the typed op variant `L::<Cat>_<Ctor>`,
            // so an `AcApp` LHS matches the typed lowering's n-ary bag node (Rholang's
            // / CommDemo's `PPar`). `ac::lower_ac_collection` threads `enum_id` to both
            // the operator and the `fixed` sub-patterns.
            if let [AstPattern::Collection { .. }] = args.as_slice() {
                return ac::lower_ac_collection(language, constructor, &args[0], enum_id);
            }
            let op = constructor_op_expr(language, constructor, enum_id)?;
            let args = args
                .iter()
                .map(|arg| pattern_to_dovetail(language, arg, enum_id))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(quote! {
                ::dovetail::rules::Pattern::app(#op, vec![#(#args),*])
            })
        },
        PatternTerm::Lambda { .. } => Err("lambda patterns require binder lowering".into()),
        PatternTerm::MultiLambda { .. } => {
            Err("multi-lambda patterns require binder lowering".into())
        },
        PatternTerm::Subst { .. } => {
            Err("substitution patterns require generated substitution lowering".into())
        },
        PatternTerm::MultiSubst { .. } => {
            Err("multi-substitution patterns require generated substitution lowering".into())
        },
    }
}

/// (E1.4) The native-rule LHS pattern for a substitution rewrite, lowered over the typed op-enum.
///
/// The LHS is `rw.left` with the binder sub-pattern collapsed: the `Apply { constructor:
/// binder_label, args: [Var(scope_var)] }` node is replaced by a bare `Var(scope_var)`, so the
/// pattern variable `scope_var` binds the WHOLE binder e-class (the lowered binder node carries an
/// arity marker + body — two children — which a `Pattern::app(binder, [var])` would NOT match
/// positionally; binding the whole node is also exactly what the dispatch arm needs, since it
/// reconstructs `scope_var` back to the typed binder term and matches `binder_cat::binder_label`).
/// Every other position lowers via the ordinary [`pattern_to_dovetail`].
fn subst_rewrite_native_lhs(
    language: &LanguageDef,
    sr: &SubstRewrite,
    enum_id: &Ident,
) -> Result<TokenStream, String> {
    let collapsed = collapse_binder_scope(&sr.left, &sr.binder_label, &sr.scope_var);
    pattern_to_dovetail(language, &collapsed, Some(enum_id))
}

/// Replace the `Apply { constructor: binder_label, args: [Var(scope_var)] }` sub-pattern with a
/// bare `Var(scope_var)`, recursively. Pure structural rewrite of the metapattern (used only to
/// synthesize the native-rule LHS).
fn collapse_binder_scope(
    pattern: &AstPattern,
    binder_label: &Ident,
    scope_var: &Ident,
) -> AstPattern {
    match pattern {
        AstPattern::Term(PatternTerm::Apply { constructor, args }) => {
            // The binder node binding `scope_var` collapses to the scope variable itself.
            if constructor == binder_label {
                if let [AstPattern::Term(PatternTerm::Var(v))] = args.as_slice() {
                    if v == scope_var {
                        return AstPattern::Term(PatternTerm::Var(scope_var.clone()));
                    }
                }
            }
            let new_args = args
                .iter()
                .map(|a| collapse_binder_scope(a, binder_label, scope_var))
                .collect();
            AstPattern::Term(PatternTerm::Apply {
                constructor: constructor.clone(),
                args: new_args,
            })
        },
        // Substitution rewrites have no collection/map/zip/lambda LHS (rejected by the detector),
        // so every other node is returned unchanged.
        other => other.clone(),
    }
}

/// ★★ (#195) Whether a DECLARED congruence names a position the e-graph closure **cannot
/// reach**, and if so why — the *under-reach* half of
/// `languages/tests/congruence_declaration_witness.rs`'s measurement, turned from a comment
/// into a value in the reflected metadata.
///
/// # The intuition
///
/// Congruence closure propagates a merge of a CHILD E-CLASS into every enclosing e-node.
/// A declaration `| S ~> T |- (C … S …) ~> (C … T …)` therefore describes something the
/// closure actually does **iff** the position `S` occupies holds a child e-class *that some
/// rule can merge*. Two field shapes hold no such thing:
///
///  * a **collection field** whose carrier is `OrderedSeq` (`FieldSeq<Elem>`) or `Opaque`
///    (`FieldOpaque`): the whole container travels inside ONE nullary leaf whose content is
///    fixed bytes, so no rewrite can ever produce a `T` for its `S`;
///  * a **non-category leaf** — a builtin, a `?g:Guard` predicate slot, or a `v@Tok` /
///    `*flt` capture: same reason, one fixed-content leaf.
///
/// In both cases the declaration is *dead*: it asks for propagation through a position no
/// step can occur at. Reporting `DeliveredElsewhere { EGraphCongruenceClosure }` for one
/// was the lane claiming coverage it does not have — a declaration that reads load-bearing
/// and is not, which is exactly #195's complaint. It is now `Declined`, naming the carrier.
///
/// # ⚠ What this deliberately does NOT flag
///
/// Returns `None` — i.e. *the existing `DeliveredElsewhere` claim stands* — for every
/// position that genuinely holds a mergeable child e-class, including the two the corpus is
/// full of:
///
///  * an **AC bag member** (`(PPar {S, ...rest})`, `ParCong`): bag elements ARE the
///    constructor's e-node children, so the closure reaches them;
///  * a **binder body** (`(PNew ^[xs].S)`, `NewCong`): the body IS a child e-class.
///
/// and for any pattern shape it cannot analyse, which fails **open** on purpose: a false
/// `Declined` would be a new wrong claim, and the pre-#195 claim is the one the witness
/// measured to be true for every reachable position.
///
/// ★ BEHAVIOUR-NEUTRAL BY CONSTRUCTION. Both outcomes emit ZERO rewrite rules, on every
/// lane. This function changes only which *disposition* is recorded, so no program's
/// reduction can move because of it.
fn congruence_position_unreachable(language: &LanguageDef, rw: &RewriteRule) -> Option<String> {
    let (source, _target) = rw.congruence_premise()?;
    let AstPattern::Term(PatternTerm::Apply { constructor, args }) = &rw.left else {
        return None;
    };
    let field_index = args
        .iter()
        .position(|arg| matches!(arg, AstPattern::Term(PatternTerm::Var(v)) if v == source))?;
    let fields = regular_constructor_fields(language, constructor)?;
    if args.len() != fields.len() {
        return None;
    }
    let field = &fields[field_index];
    let carrier_note = if field.is_collection {
        match collection_carrier(field.coll_type.as_ref()) {
            // An AC bag's members ARE the e-node's children: the closure reaches them.
            CollectionCarrier::AcBag => return None,
            CollectionCarrier::OrderedSeq => "an ordered `FieldSeq` carrier leaf",
            CollectionCarrier::Opaque => "an unordered `FieldOpaque` carrier leaf",
        }
    } else if NonTerminalKind::classify(&field.category.to_string()).is_builtin() {
        "a builtin `FieldOpaque` leaf"
    } else if field.is_predicate {
        "a semantic-predicate `FieldOpaque` leaf"
    } else if field.is_opaque_leaf() {
        "a capture `FieldTokenText`/`FieldOpaque` leaf"
    } else {
        return None;
    };
    Some(format!(
        "declares a congruence into `{constructor}` field {field_index} (`{source}`), which \
         lowers to {carrier_note} rather than to a child e-class. Congruence closure propagates a \
         merge of a CHILD e-class into its parents; a fixed-content leaf can never be merged, so \
         no step can occur at this position and the declaration is DEAD on this lane. This is the \
         under-reach `languages/tests/congruence_declaration_witness.rs` measures with its \
         SEVERED probe. To make the position an evaluation context, give it a child e-class (a \
         scalar category field, or an AC `HashBag` container); to state that it is deliberately \
         not one, declare `| {source} ~/> …` instead of `| {source} ~> …`"
    ))
}

/// The positional field list of `constructor` if it is a `Regular` constructor of some
/// declared category. Shared by [`congruence_position_unreachable`] and
/// [`withholding::classify_withholdings`], so the two polarities analyse positions the
/// same way.
fn regular_constructor_fields(
    language: &LanguageDef,
    constructor: &Ident,
) -> Option<Vec<FieldInfo>> {
    for ty in &language.types {
        for variant in collect_category_variants(&ty.name, language) {
            if let VariantKind::Regular { label, fields } = variant {
                if label == *constructor {
                    return Some(fields);
                }
            }
        }
    }
    None
}

fn premise_supported(premise: &Premise) -> bool {
    // EXHAUSTIVE over every `Premise` variant (no catch-all): only a congruence
    // premise is supplied by the e-graph congruence closure; all side-condition
    // premises (freshness, relation queries, universals, behavioral / synthetic
    // guards) require evidence the structural saturation does not model, so they
    // fail closed. Mirrors `GeneratedReportCompiler.premise_supported`.
    match premise {
        Premise::Congruence { .. } => true,
        // ★ (#195) A WITHHELD congruence is likewise supplied by the e-graph lane — not by
        // its closure but by SEVERANCE of the named position (`withholding::
        // classify_withholdings`), which needs no evidence at rule-lowering time. It is
        // therefore `true` on the same grounds its positive twin is: no side condition.
        //
        // ⚠ `lower_rewrite` tests `rw.withholds_congruence()` BEFORE it reaches the
        // structural lowering, so a `true` here can never let a withholding be emitted as
        // an identity rewrite rule. That ordering is load-bearing and pinned by
        // `a_withholding_emits_no_rewrite_rule`.
        Premise::CongruenceWithheld { .. } => true,
        Premise::Freshness(_) => false,
        Premise::RelationQuery { .. } => false,
        Premise::ForAll { .. } => false,
        Premise::BehavioralGuard(_) => false,
        Premise::SyntheticInjGuard { .. } => false,
    }
}

/// The disposition-recording lowering of ONE declared equation.
///
/// An equation lowers to up to TWO structural rules — a forward orientation and a reverse one
/// — and the two can fare differently, so each gets its own disposition. Every branch below
/// records one: the old code recorded a `String` on three of the six and recorded *nothing* on
/// the other three, which is precisely how an equation could stop being lowered without any
/// reader being able to tell.
///
/// The `Ok(_) => { … }` arms are the interesting ones. They are reached when the pattern lowers
/// perfectly well but the side is a bare metavariable, in which case that orientation is
/// deliberately not emitted — a rule `?x ⟶ f(?x)` matches every e-class and would rewrite the
/// whole e-graph. That is a legitimate decision, so it is [`LoweringOutcome::Suppressed`] rather
/// than [`LoweringOutcome::Declined`]; but it was previously invisible, and the OTHER
/// orientation may well have been declined, which is how an equation could vanish entirely
/// while every recorded excuse mentioned only one of its two halves.
fn lower_equation(
    language: &LanguageDef,
    eq: &Equation,
    enum_id: Option<&Ident>,
) -> (Vec<TokenStream>, Vec<LoweringDisposition>) {
    let mut out = Vec::new();
    let mut dispositions = Vec::new();
    let declined = |reason: String| {
        LoweringDisposition::declined(
            LoweredConstructKind::Equation,
            eq.name.to_string(),
            LoweredConstructOrigin::Declared,
            reason,
            true,
        )
    };
    if !eq.premises.iter().all(premise_supported) {
        // Both orientations die together: the premise is a property of the equation.
        dispositions.push(declined("has side conditions".to_string()));
        return (out, dispositions);
    }

    match pattern_to_dovetail(language, &eq.left, enum_id) {
        Ok(left) if !eq.left.is_just_variable() => {
            match pattern_to_dovetail(language, &eq.right, enum_id) {
                Ok(right) => {
                    let label_text = format!("{}::equation::{}::forward", language.name, eq.name);
                    let label = lit(&label_text);
                    out.push(quote! {
                        ::dovetail::rules::RewriteRule {
                            lhs: #left,
                            rhs: #right,
                            label: Some(#label.to_string()),
                        }
                    });
                    dispositions.push(LoweringDisposition::delivered(
                        LoweredConstructKind::Equation,
                        eq.name.to_string(),
                        LoweredConstructOrigin::Declared,
                        label_text,
                    ));
                },
                Err(reason) => dispositions.push(declined(format!("RHS: {reason}"))),
            }
        },
        Ok(_) => dispositions.push(LoweringDisposition::suppressed(
            LoweredConstructKind::Equation,
            eq.name.to_string(),
            LoweredConstructOrigin::Declared,
            "forward orientation elided: the LHS is a bare metavariable, so the rule would \
             match every e-class",
        )),
        Err(reason) => dispositions.push(declined(format!("LHS: {reason}"))),
    }

    match pattern_to_dovetail(language, &eq.right, enum_id) {
        Ok(right) if !eq.right.is_just_variable() => {
            match pattern_to_dovetail(language, &eq.left, enum_id) {
                Ok(left) => {
                    let label_text = format!("{}::equation::{}::reverse", language.name, eq.name);
                    let label = lit(&label_text);
                    out.push(quote! {
                        ::dovetail::rules::RewriteRule {
                            lhs: #right,
                            rhs: #left,
                            label: Some(#label.to_string()),
                        }
                    });
                    dispositions.push(LoweringDisposition::delivered(
                        LoweredConstructKind::Equation,
                        eq.name.to_string(),
                        LoweredConstructOrigin::Declared,
                        label_text,
                    ));
                },
                Err(reason) => dispositions.push(declined(format!("reverse RHS: {reason}"))),
            }
        },
        Ok(_) => dispositions.push(LoweringDisposition::suppressed(
            LoweredConstructKind::Equation,
            eq.name.to_string(),
            LoweredConstructOrigin::Declared,
            "reverse orientation elided: the RHS is a bare metavariable, so the reversed rule \
             would match every e-class",
        )),
        Err(reason) => dispositions.push(declined(format!("reverse LHS: {reason}"))),
    }

    (out, dispositions)
}

/// The disposition-recording lowering of ONE declared rewrite.
///
/// ★ THE ANTI-VACUITY POINT OF THE WHOLE MECHANISM LIVES HERE. Five of this function's
/// early returns used to be `return (Vec::new(), Vec::new())` — no rule, no excuse — and they
/// are the OVERWHELMING MAJORITY case: for the bundled Rholang, 400 of 461 declared rewrites
/// leave through the congruence branch alone. Those five returns are correct: another lane
/// really does cover the rewrite. But because they were spelled the same way as a silent drop,
/// no test could distinguish "covered elsewhere" from "covered nowhere", and turning silence
/// into an error would have produced 400 false positives.
///
/// Each of the five now returns [`LoweringOutcome::DeliveredElsewhere`] naming the covering
/// lane, so the distinction is a fact in the generated metadata rather than a comment.
///
/// # ★★★ (#195) THE THREE STATES OF CONGRUENCE PROPAGATION MEET HERE
///
/// Before #195 this function had **two** answers for a congruence-shaped rule and they were
/// the same answer: every rule satisfying `is_congruence_rule()` left through the single
/// `DeliveredElsewhere { EGraphCongruenceClosure }` branch below, and a rule declaring
/// *nothing* also produced no rule. So "the author asked for propagation here" and "the
/// author has no opinion" were indistinguishable, and "the author refused propagation here"
/// was **unspellable**. `languages/tests/congruence_declaration_witness.rs` measured the
/// consequence in both directions: an *undeclared* scalar position reduced anyway
/// (over-reach) while a `Vec`-carrier position did not, declared or otherwise
/// (under-reach).
///
/// The three answers are now distinct, and each is a VALUE in the reflected metadata:
///
/// | declaration | branch | disposition |
/// |---|---|---|
/// | `\| S ~/> T \|-` — **withheld** | [`withholding`] | `Suppressed`, naming the severed position (or `Declined`, naming why the lane cannot honour it) |
/// | `\| S ~> T \|-` — **declared** | the congruence branch | `DeliveredElsewhere { EGraphCongruenceClosure }` when the closure REACHES the position; `Declined` naming the carrier when it does not |
/// | nothing declared | not reached | the intrinsic closure — the sensible default, unchanged |
fn lower_rewrite(
    language: &LanguageDef,
    rw: &RewriteRule,
    enum_id: Option<&Ident>,
) -> (Vec<TokenStream>, Vec<LoweringDisposition>) {
    let origin = if rw.is_auto_injected {
        LoweredConstructOrigin::AutoInjected
    } else {
        LoweredConstructOrigin::Declared
    };
    let elsewhere = |lane: LoweringLane, note: &str| {
        vec![LoweringDisposition::delivered_elsewhere(
            LoweredConstructKind::Rewrite,
            rw.name.to_string(),
            origin,
            lane,
            note,
        )]
    };
    let declined = |reason: String| {
        vec![LoweringDisposition::declined(
            LoweredConstructKind::Rewrite,
            rw.name.to_string(),
            origin,
            reason,
            true,
        )]
    };
    if !rw.premises.iter().all(premise_supported) {
        return (Vec::new(), declined("has side conditions".to_string()));
    }
    // ★★★ (#195) STATE 3 — a DECLARED WITHHOLDING. Handled FIRST, and before
    // `is_congruence_rule()`, because a withholding is neither a rule of this lane nor a
    // rule of any other: it is discharged by SEVERING the named position in the lowering
    // (`withholding::classify_withholdings` → `typed_lowering::field_child_expr_typed`).
    // Emitting the conclusion it spells out would build the very step the author denied.
    if rw.withholds_congruence() {
        let set = withholding::classify_withholdings(language);
        let mine: Vec<LoweringDisposition> = set
            .dispositions()
            .into_iter()
            .filter(|d| d.construct == rw.name.to_string())
            .collect();
        // ⚠ NON-VACUITY FLOOR. `classify_withholdings` is total over the rewrites — every
        // `~/>` rule yields either a severed position or a named refusal — so this vector
        // is non-empty by construction. Asserting it here rather than trusting it means a
        // future classifier that silently dropped a shape would fail LOUDLY instead of
        // reintroducing #195's exact defect (a declaration that reads load-bearing and is
        // not) one level up.
        if mine.is_empty() {
            return (
                Vec::new(),
                declined(format!(
                    "declares a withheld congruence (`| S ~/> T |-`) that the withholding \
                     classifier neither severed nor refused. That is a GENERATOR defect, not a \
                     grammar defect: `withholding::classify_withholdings` must be total over \
                     `{}`",
                    rw.name
                )),
            );
        }
        return (Vec::new(), mine);
    }
    if rw.is_congruence_rule() {
        // ★★ (#195) STATE 1 — a DECLARED congruence. The e-graph congruence closure supplies
        // context closure after the premise-free kernel rewrite has merged the child
        // e-class, so no explicit rule is emitted.
        //
        // ★ WHAT CHANGED. This branch used to make that claim UNCONDITIONALLY, for all 142
        // of Rholang's augmented congruences. It is not unconditionally true: the closure
        // reaches a position only if the position holds a CHILD E-CLASS, and a position
        // whose field lowers to one carrier leaf (an unordered collection's `FieldOpaque`,
        // an ordered collection's `FieldSeq`) holds no child e-class — so a congruence
        // declared into such a position is DECLARED AND NOT HONOURED. That is the
        // under-reach half of `congruence_declaration_witness.rs`'s measurement, and
        // reporting `DeliveredElsewhere` for it was the lane claiming coverage it does not
        // have. It now `Declined`s, naming the carrier.
        if let Some(reason) = congruence_position_unreachable(language, rw) {
            return (Vec::new(), declined(reason));
        }
        return (
            Vec::new(),
            elsewhere(
                LoweringLane::EGraphCongruenceClosure,
                "congruence closure propagates the kernel rewrite's child-e-class merge \
                 through every enclosing e-node, so an explicit rule would duplicate it",
            ),
        );
    }
    // (E1.3) A substitution rewrite is NOT a structural `RewriteRule` — it is lowered as a
    // native rule + dispatcher arm by `typed_report::generate_native_rules_and_dispatch`
    // (own op-id, own arm), so it must emit NOTHING here and add NOTHING to `unsupported`
    // (it is fully supported, just on the native lane). This branch is reached only on the
    // typed path (`enum_id.is_some()`); on the `EGraph<String>` path a substitution rewrite
    // never appears, because the language is routed to the typed path by
    // `needs_typed_dovetail_path`. (Gated on `enum_id.is_some()` defensively so the String
    // path's behavior is byte-identical.)
    if enum_id.is_some() && is_substitution_rewrite(language, rw).is_some() {
        return (
            Vec::new(),
            elsewhere(
                LoweringLane::TypedNativeSubstitution,
                "lowered as a native rule + dispatcher arm whose contractum a generated \
                 `substitute_*`/`multi_substitute_*` computes",
            ),
        );
    }
    // (A-3) A Comm rewrite is likewise NOT a structural `RewriteRule` — it is lowered as a typed
    // native rule + dispatch arm (`typed_report`), so it emits NOTHING here and adds NOTHING to
    // `unsupported`. Gated on `enum_id.is_some()` (typed path only); the `EGraph<String>` path
    // never routes a Comm rewrite (`needs_typed_dovetail_path` routes it typed), so this is
    // defensively byte-identical for the String path.
    if enum_id.is_some() && is_comm_rewrite(language, rw).is_some() {
        return (
            Vec::new(),
            elsewhere(
                LoweringLane::TypedNativeComm,
                "lowered as a native rule + dispatch arm: a non-linear AC LHS over a binder \
                 element whose RHS nests a substitution in an AC bag",
            ),
        );
    }
    // (Stage 3d) A structural non-linear AC rewrite (Ambient `OpenRule`) is likewise NOT a structural
    // `RewriteRule` — it is lowered as a typed native rule + dispatch arm (`typed_report`), so it
    // emits NOTHING here. Gated on `enum_id.is_some()` (typed path only); the `EGraph<String>` path
    // never routes a structural-AC rewrite (it stays a String-path AC `RewriteRule` for the untyped
    // binder-handler `Ambient`), so this is defensively byte-identical for the String path.
    if enum_id.is_some() && is_structural_ac_rewrite(language, rw).is_some() {
        return (
            Vec::new(),
            elsewhere(
                LoweringLane::TypedNativeStructuralAc,
                "lowered as a native rule + dispatch arm: a flat structural non-linear AC \
                 rewrite",
            ),
        );
    }
    // (Stage 4) A DEPTH-2 nested structural non-linear AC rewrite (Ambient `InRule`/`OutRule`) is
    // likewise NOT a structural `RewriteRule` — it is lowered as a typed native rule + dispatch arm
    // (`typed_report`), so it emits NOTHING here. Gated on `enum_id.is_some()` (typed path only); the
    // `EGraph<String>` path never routes a nested structural-AC rewrite (it stays a String-path AC
    // `RewriteRule` for the untyped binder-handler `Ambient`), so this is defensively byte-identical
    // for the String path.
    if enum_id.is_some() && is_nested_structural_ac_rewrite(language, rw).is_some() {
        return (
            Vec::new(),
            elsewhere(
                LoweringLane::TypedNativeNestedStructuralAc,
                "lowered as a native rule + dispatch arm: a depth-2 nested structural \
                 non-linear AC rewrite",
            ),
        );
    }

    match (
        pattern_to_dovetail(language, &rw.left, enum_id),
        pattern_to_dovetail(language, &rw.right, enum_id),
    ) {
        (Ok(lhs), Ok(rhs)) => {
            let label_text = format!("{}::rewrite::{}", language.name, rw.name);
            let label = lit(&label_text);
            (
                vec![quote! {
                    ::dovetail::rules::RewriteRule {
                        lhs: #lhs,
                        rhs: #rhs,
                        label: Some(#label.to_string()),
                    }
                }],
                vec![LoweringDisposition::delivered(
                    LoweredConstructKind::Rewrite,
                    rw.name.to_string(),
                    origin,
                    label_text,
                )],
            )
        },
        (Err(reason), _) => (Vec::new(), declined(format!("LHS: {reason}"))),
        (_, Err(reason)) => (Vec::new(), declined(format!("RHS: {reason}"))),
    }
}

/// The structural rule vector for a language, plus ★ THE DISPOSITION OF EVERY DECLARED
/// EQUATION AND REWRITE that produced it.
///
/// This function is the single PRODUCER of lowering outcomes; it has five consumers, and four
/// of them used to write `let (rules, _unsupported) = rule_block(…)`. The second return value
/// is no longer a list of excuses that a consumer may reasonably ignore — it is the complete
/// record of what became of every construct, which is exactly what a consumer must not drop.
///
/// One post-pass runs over the equations: a `Declined` equation is offered to the BINDER-FLOAT
/// lane ([`reclassify_binder_float_equations`]) before the answer is final, because an equation
/// whose LHS carries a `Lambda` metapattern is refused *here* while being discharged in full by
/// the generated binder-congruence normal form.
fn rule_block(
    language: &LanguageDef,
    enum_id: Option<&Ident>,
) -> (TokenStream, Vec<LoweringDisposition>) {
    let mut rules = Vec::new();
    let mut dispositions = Vec::new();
    for eq in &language.equations {
        let (lowered, mut recorded) = lower_equation(language, eq, enum_id);
        rules.extend(lowered);
        reclassify_binder_float_equations(language, eq, &mut recorded);
        dispositions.append(&mut recorded);
    }
    for rw in &language.rewrites {
        let (lowered, mut recorded) = lower_rewrite(language, rw, enum_id);
        rules.extend(lowered);
        dispositions.append(&mut recorded);
    }

    (quote! { vec![#(#rules),*] }, dispositions)
}

/// ★ THE LOWERING-DISPOSITION INVENTORY of a language — the single derivation every consumer
/// shares, and the one the generated metadata publishes.
///
/// One entry per declared equation ORIENTATION (an equation lowers forward and reverse
/// independently, and the two can fare differently), one per declared rewrite, and one per
/// declared `fold`. The `enum_id` presence must match the path the language actually takes,
/// because five of `lower_rewrite`'s branches are typed-path-only: on the `EGraph<String>` path
/// a substitution/Comm/structural-AC rewrite is lowered structurally rather than handed to the
/// typed native dispatcher, so claiming the native lane covers it would be a lie for exactly
/// the languages that do not have one.
///
/// The fold half is path-dependent for the same reason, and in the same direction:
///
///   * TYPED path — [`typed_report::collect_fold_rules`] walks the folds and says, per fold,
///     whether the native dispatcher took it;
///   * `EGraph<String>` path — the report generator never walks folds at all. Every fold that
///     reaches this path has a NATIVE output category (a non-native-output fold forces the
///     typed path through `needs_typed_dovetail_path`), so it is run by the host native
///     evaluator that `complete_native_dovetail_report_for_language` reaches before structural
///     saturation. That is [`LoweringLane::HostNativeEvaluation`], and it is delivery, not
///     silence.
///
/// ★ #141 G9 — also returns the census REFUSAL (`compile_error!` tokens, EMPTY
/// when every declared construct is disposed). This function's product is a
/// macro-time record, so it has no output of its own to hang a diagnostic on; the
/// boundary (`macros/src/lib.rs`) splices what it returns into the expansion.
pub(crate) fn lowering_disposition_inventory(
    language: &LanguageDef,
) -> (Vec<LoweringDisposition>, TokenStream) {
    let typed = needs_typed_dovetail_path(language);
    let enum_id = typed.then(|| op_enum::op_enum_ident(language));
    let (_rules, mut dispositions) = rule_block(language, enum_id.as_ref());

    if typed {
        let (_folds, fold_dispositions) = typed_report::collect_fold_rules(language);
        dispositions.extend(fold_dispositions);
    } else {
        for rule in &language.terms {
            if rule.eval_mode != Some(mettail_ast::types::EvalMode::Fold) {
                continue;
            }
            dispositions.push(LoweringDisposition::delivered_elsewhere(
                LoweredConstructKind::Fold,
                rule.label.to_string(),
                LoweredConstructOrigin::Declared,
                LoweringLane::HostNativeEvaluation,
                "run by the host native evaluator reached before structural saturation; every \
                 fold on this path has a native output category, because a non-native-output \
                 fold routes the language to the typed path",
            ));
        }
    }

    let refusal = crate::gen::runtime::disposition::every_construct_disposed_or_refusal(
        language,
        &dispositions,
        true,
        "lowering_disposition_inventory",
    );
    (dispositions, refusal)
}

/// Re-attribute an equation the structural lowering declined, when the BINDER-FLOAT lane
/// covers it.
///
/// A binder-shaped equation (`ν x. ν y. P = ν y. ν x. P`, or a float-across-constructor law
/// such as `C(…, ν x. P, …) = ν x. C(…, P, …)`) cannot lower structurally: its pattern carries
/// a `Lambda` metapattern, on which `pattern_to_dovetail` fails closed. Recording that as a
/// declination is *wrong* in two different ways at once, and the two wrongs are different from
/// each other:
///
///   * a FLOAT-ACROSS-CONSTRUCTOR law is discharged in full by the generated binder-congruence
///     normal form, which floats binders outward before the in-engine reduction runs — so it is
///     [`LoweringLane::BinderCongruenceFloat`]'s, delivered;
///   * a BINDER-BINDER COMMUTATION law (`NewComm`) is deliberately left underived. The host's
///     α-canonical-key minimization is not Match-expressible and redex exposure is
///     NewComm-invariant, so the float normal form is unique *up to* the NewComm run
///     permutation and reordering buys nothing. That is a recorded decision (Q-NC), not an
///     omission — hence [`LoweringOutcome::Suppressed`], with the decision named.
///
/// `classify_equation_float_disposition` fails closed on any language for which the float
/// handler is not generated, so this can never claim coverage from a handler that does not
/// exist.
fn reclassify_binder_float_equations(
    language: &LanguageDef,
    eq: &Equation,
    dispositions: &mut [LoweringDisposition],
) {
    use mettail_rholang_codegen::rho_net_lower::{
        classify_equation_float_disposition, EquationFloatDisposition,
    };

    let float = classify_equation_float_disposition(language, eq);
    if float == EquationFloatDisposition::NotFloatFamily {
        return;
    }
    for disposition in dispositions.iter_mut() {
        if !disposition.is_declined() {
            continue;
        }
        disposition.legacy_diagnostic = false;
        disposition.outcome = match float {
            EquationFloatDisposition::FloatAcrossConstructor => {
                LoweringOutcome::DeliveredElsewhere {
                    lane: LoweringLane::BinderCongruenceFloat,
                    note: "discharged by the generated binder-congruence normal form, which \
                           floats binders outward before the in-engine reduction"
                        .to_string(),
                }
            },
            EquationFloatDisposition::BinderCommutation => LoweringOutcome::Suppressed {
                reason: "user decision Q-NC: in-Rho binder-commutation reordering is \
                         deliberately omitted — the host's alpha-canonical-key minimization is \
                         not Match-expressible, and redex exposure is commutation-invariant, so \
                         the float normal form is unique up to the commutation run permutation"
                    .to_string(),
            },
            EquationFloatDisposition::NotFloatFamily => continue,
        };
    }
}

/// Generate feature-gated helpers that compile generated typed AST terms into
/// checked `RuntimeDovetailRunReport` values.
pub fn generate_dovetail_report(language: &LanguageDef) -> TokenStream {
    // Fold-bearing languages (non-native-output `fold`s — Rholang's Proc casts/arith) take the
    // typed-`L` path: a typed op-enum + native-rewrite dispatcher that actually reduces folds.
    // Every other language keeps the `EGraph<String>` path below, byte-for-byte unchanged.
    if needs_typed_fold_path(language) {
        return typed_report::generate_typed_dovetail_report(language);
    }
    let name = &language.name;
    let language_struct = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let language_lit = lit(&name.to_string());
    let category_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|ty| category_lowering(language, &ty.name))
        .collect();
    // ★ PRODUCTION CONSUMER 1 of 4. This is the ONE site that historically did anything at
    // all with the second return value, and even here it only reached the generated code on
    // languages without a binder-congruence float (`should_emit_binder` blanks `native_gate`
    // below).
    // `legacy_unsupported_messages` reconstructs exactly the strings the old
    // `unsupported: Vec<String>` carried — in declaration order, from the `Declined`
    // dispositions that carry a legacy diagnostic — so this generated body is byte-identical
    // to the one that shipped before dispositions existed.
    let (rules, dispositions) = rule_block(language, None);
    // ★ #141 G9 — EMPTY unless a declared construct left the lowering with no
    // disposition, in which case it is a `compile_error!` naming the constructs.
    let disposition_refusal =
        crate::gen::runtime::disposition::every_construct_disposed_or_refusal(
            language,
            &dispositions,
            false,
            "generate_dovetail_report (EGraph<String> path)",
        );
    let unsupported_lits: Vec<LitStr> =
        crate::gen::runtime::disposition::legacy_unsupported_messages(&dispositions)
            .iter()
            .map(|message| lit(message))
            .collect();
    let primary_type = language
        .types
        .first()
        .map(|ty| ty.name.clone())
        .expect("language has at least one type");
    let primary_add = category_lowering_fn(&primary_type);

    // Inc 2/3: a host-less language with a binder handler (e.g. Ambient) floats
    // its `new`s outward (the binder congruences) BEFORE the in-engine AC
    // reduction, rather than failing closed on the unlowered equations. The
    // floated term is what gets lowered into the e-graph; the AC rules match the
    // soup under the floated news, so no peel/re-wrap is needed.
    let should_emit_binder =
        crate::gen::runtime::binder_congruence::should_emit_binder_congruence(language);
    let source_expr: TokenStream = if should_emit_binder {
        quote! { __source }
    } else {
        quote! { typed_term.0 }
    };

    let root_block = if language.types.len() > 1 {
        let inner_enum = format_ident!("{}TermInner", name);
        let mut arms = Vec::new();
        for ty in &language.types {
            let cat = &ty.name;
            let add_fn = category_lowering_fn(cat);
            arms.push(quote! {
                #inner_enum::#cat(value) => {
                    __roots.push(#add_fn(&mut eg, value));
                }
            });
        }
        quote! {
            for __alt in #source_expr.all_alts() {
                match __alt {
                    #(#arms)*
                    #inner_enum::Ambiguous(_) => unreachable!(
                        "all_alts() returns flat alternatives, not nested Ambiguous"
                    ),
                }
            }
        }
    } else {
        quote! {
            __roots.push(#primary_add(&mut eg, &#source_expr));
        }
    };

    // For a handler language the binder congruences are discharged by the float
    // (so there is no fail-closed gate and no native-eval short-circuit); the
    // floated term flows straight into the e-graph AC reduction. For every other
    // language the existing native-eval + fail-closed gate is preserved exactly.
    let native_gate: TokenStream = if should_emit_binder {
        quote! {}
    } else {
        quote! {
            if let Ok(report) =
                ::mettail_dovetail_runtime::complete_native_dovetail_report_for_language(
                    &#language_struct,
                    term,
                )
            {
                return Ok(report);
            }

            let unsupported: &[&str] = &[#(#unsupported_lits),*];
            if !unsupported.is_empty() {
                return Err(format!(
                    "generated Dovetail compiler for language {} needs specialized lowering before structural saturation can be complete: {}",
                    #language_lit,
                    unsupported.join("; "),
                ));
            }
        }
    };
    let source_binding: TokenStream = if should_emit_binder {
        quote! {
            // Inc 2: float `new`s outward (binder congruences) before AC
            // reduction. `binder_congruence_nf_term` returns `None` when there is
            // no floatable redex, in which case the original term is lowered.
            let __source = typed_term.0.binder_congruence_nf_term()
                .unwrap_or_else(|| typed_term.0.clone());
        }
    } else {
        quote! {}
    };

    // Epic 4 (R-4): a language whose rewrites lower to a base-rewrite σ-receiver is
    // a "rho-net-rewrite" language — its Dovetail report additionally carries the
    // resolved σ provenance a runtime Rho σ-injection reads. Every other language
    // (scalar / rholang-typed-path / no base rewrite) keeps `rewrite_justifications`
    // empty, so its report stays byte-identical. The decision is made here, at
    // generation time, from the same σ-receiver derivation the runtime uses.
    //
    // Stage AC-U3: an un-skipped HashBag AC rewrite (`RhoNetLoweredRule::AcRewrite`) is a
    // firing site too — its `rho_net_ac_injection_sites` entry drives the runtime AC
    // σ-injection — so a language whose ONLY rewrites are AC rewrites (e.g. AcDemo) must
    // ALSO carry the resolved σ provenance, or the AC injection F-fn has no firing to read.
    // Stage 3a: a contextual (congruence) rewrite that materialized to an atomic JOIN is a
    // firing site too — its `rho_net_contextual_injection_sites` entry drives the runtime
    // contextual σ-injection, which reconstructs the reduced hole from the PREMISE firing's
    // σ — so a language with a contextual join must ALSO carry the resolved σ provenance, or
    // the contextual injection F-fn has no premise firing to read. (For a language that also
    // has a base rewrite the base-site gate already fires; this widens it to the
    // contextual-only signal for completeness.)
    // Stage 3c: a binder/β-substitution rewrite that materialized to a `SubstRewrite`
    // σ-receiver is a firing site too — its `rho_net_subst_injection_sites` entry drives the
    // runtime subst σ-injection, which reads the firing's CONTRACTUM (the host-computed reduct)
    // from `rewrite_justifications` — so a language whose ONLY rewrites are binder rewrites (e.g.
    // LambdaDemo) must ALSO carry the resolved σ provenance, or the subst injection F-fn has no
    // firing (and no contractum) to read.
    // Stage 3e: a `fold` native system process that materialized to a `NativeSystemProcessRewrite`
    // dispatch receiver is a firing site too — its `rho_net_native_injection_sites` entry drives
    // the runtime native σ-injection, which reads the firing's CONTRACTUM (the trusted handler's
    // native value) from `rewrite_justifications` — so a language whose ONLY reducing rules are
    // native processes (e.g. NativeDemo) must ALSO carry the resolved σ provenance, or the native
    // injection F-fn has no firing (and no contractum) to read.
    // Stage 3f: a native SCALAR FOLD (`AddInt`) that materialized to a `NativeFold` dispatch
    // receiver is a firing site too — its `rho_net_native_fold_injection_sites` entry drives the
    // runtime native-fold σ-injection, which reads the firing's CONTRACTUM (the reduced value) from
    // `rewrite_justifications`. (A pure scalar-fold language routes to the TYPED path, so this
    // non-typed gate is defensive/symmetric with the native-system-process disjunct above.)
    let populate_rewrite_justifications =
        !mettail_rholang_codegen::rho_net_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_ac_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_contextual_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_subst_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_native_injection_sites(language).is_empty()
            || !mettail_rholang_codegen::rho_net_native_fold_injection_sites(language).is_empty();
    let report_projection: TokenStream = if populate_rewrite_justifications {
        quote! {
            // Bare-ify a generated e-graph op / rule label to its source identity:
            // the THIRD "::"-delimited segment — the constructor / rule NAME slot —
            // NOT the last segment (a blind rsplit would wrongly take the literal
            // value "42" out of "{lang}::{cat}::IntLit::42"). This targets the label
            // slot per node-kind: nullary/regular/collection/binder ops are exactly
            // "{lang}::{cat}::{ctor}" (segment 2 = ctor); a var/literal leaf appends
            // a "::{value:?}" suffix (segment 2 is still the ctor); a rewrite label
            // is "{lang}::rewrite::{name}" (segment 2 = name).
            fn __mettail_bareify_label(__label: &str) -> String {
                __label.split("::").nth(2).unwrap_or(__label).to_string()
            }
            fn __mettail_bareify_subterm(
                __subterm: &mut mettail_runtime::RuntimeReflectedSubterm,
            ) {
                __subterm.constructor = __mettail_bareify_label(&__subterm.constructor);
                for __child in &mut __subterm.children {
                    __mettail_bareify_subterm(__child);
                }
            }
            fn __mettail_bareify_rewrite_justifications(
                __justifications: &mut Vec<mettail_runtime::RuntimeRewriteJustification>,
            ) {
                for __justification in __justifications.iter_mut() {
                    __justification.rule_label = __mettail_bareify_label(&__justification.rule_label);
                    for (_, __subterm) in __justification.sigma.iter_mut() {
                        __mettail_bareify_subterm(__subterm);
                    }
                    // Stage 3c: the contractum (the reduct a subst σ-injection reflects) carries
                    // the same "{lang}::{cat}::{ctor}" op labels as σ, so bare-ify it identically
                    // — a runtime injection reflects each constructor as `mettail.term.{fp}.{ctor}`.
                    if let ::core::option::Option::Some(__contractum) =
                        __justification.contractum.as_mut()
                    {
                        __mettail_bareify_subterm(__contractum);
                    }
                }
            }

            let mut report = ::dovetail::report::report_from_extraction_with_rule_firings(
                ::dovetail::extract::Extraction {
                    value: __derivations,
                    completeness: __completeness,
                },
                sat.rule_firings,
            );
            // Resolve σ while the e-graph is still live, under the SAME constant cost
            // model the roots were extracted with (`sat.rule_firings` is moved above,
            // but the distinct `rewrite_justifications` field is still available).
            report.rewrite_justifications = ::dovetail::report::resolve_rewrite_justifications(
                &eg,
                &sat.rewrite_justifications,
                |_| ::rigail::TropicalWeight(0.0),
            );
            let mut runtime_report = ::mettail_dovetail_runtime::project_dovetail_report(&report);
            // R-4 owns the bare-ification: the projected σ carries the generated
            // "{lang}::{cat}::{ctor}" op labels and the "{lang}::rewrite::{name}" rule
            // label; a runtime σ-injection reflects each constructor as
            // `mettail.term.{fp}.{ctor}` and matches the fired rule to its bare
            // σ-receiver label, so both must be bare source identities.
            __mettail_bareify_rewrite_justifications(&mut runtime_report.rewrite_justifications);
            runtime_report
                .validate_shape()
                .map_err(|err| format!("generated Dovetail report for language {} is malformed: {err}", #language_lit))?;
            Ok(runtime_report)
        }
    } else {
        quote! {
            let report = ::dovetail::report::report_from_extraction_with_rule_firings(
                ::dovetail::extract::Extraction {
                    value: __derivations,
                    completeness: __completeness,
                },
                sat.rule_firings,
            );
            let runtime_report = ::mettail_dovetail_runtime::project_dovetail_report(&report);
            runtime_report
                .validate_shape()
                .map_err(|err| format!("generated Dovetail report for language {} is malformed: {err}", #language_lit))?;
            Ok(runtime_report)
        }
    };

    quote! {
        // ★ #141 G9 — the disposition census's refusal. EMPTY unless a declared
        // construct left this lowering with no account of itself.
        #disposition_refusal
        #[cfg(feature = "dovetail-codegen")]
        impl #language_struct {
            /// Compile this language's generated typed AST into a checked
            /// runtime Dovetail report.
            ///
            /// The compiler is derived from the same macro-expanded
            /// `LanguageDef` as the AST constructors. Rholang-looking or
            /// source-language text is not parsed or reverse-engineered here.
            ///
            /// Formal models:
            /// - `dovetail/formal/rocq/theories/Lowering/GeneratedReportCompiler.v`
            /// - `dovetail/formal/rocq/theories/Refinement/RustModelBridge.v`
            /// - `dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v`
            pub fn dovetail_report_for(
                term: &dyn mettail_runtime::Term,
                max_iters: usize,
                max_nodes: usize,
            ) -> Result<mettail_runtime::RuntimeDovetailRunReport, String> {
                #native_gate

                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("expected {}Term, got {:?}", #language_lit, term))?;

                #source_binding

                let mut eg = ::dovetail::egraph::EGraph::<String>::with_config(
                    ::dovetail::egraph::EGraphConfig { max_nodes },
                );
                #(#category_fns)*

                let mut __roots = Vec::new();
                #root_block
                __roots.sort_unstable();
                __roots.dedup();
                if __roots.is_empty() {
                    return Err(format!(
                        "generated Dovetail compiler for language {} produced no roots",
                        #language_lit,
                    ));
                }

                static __DOVETAIL_COMPILED_RULES: ::std::sync::OnceLock<
                    ::dovetail::rules::CompiledRuleSet<String>,
                > = ::std::sync::OnceLock::new();
                let __compiled_rules = __DOVETAIL_COMPILED_RULES
                    .get_or_init(|| ::dovetail::rules::CompiledRuleSet::from_rewrites(#rules));
                let sat = eg.saturate_compiled(__compiled_rules, max_iters);
                if sat.outcome != ::dovetail::rules::SaturationOutcome::Converged {
                    return Err(format!(
                        "generated Dovetail saturation for language {} stopped before convergence: {:?}",
                        #language_lit,
                        sat.outcome,
                    ));
                }

                let mut __derivations = Vec::new();
                let mut __completeness = ::dovetail::extract::ExtractionCompleteness::Complete;
                for __root in __roots {
                    let mut extractor =
                        ::dovetail::extract::Extractor::new(&eg, |_| ::rigail::TropicalWeight(0.0));
                    let __extracted = extractor.funded_best(eg.find(__root));
                    if __extracted.completeness
                        == ::dovetail::extract::ExtractionCompleteness::BoundedByCycleCut
                    {
                        __completeness =
                            ::dovetail::extract::ExtractionCompleteness::BoundedByCycleCut;
                    }
                    if let ::core::option::Option::Some(__derivation) = __extracted.value {
                        __derivations.push(__derivation);
                    }
                }

                #report_projection
            }

            /// Installable Dovetail compiler stage for this generated language.
            pub fn dovetail_compiler_stage(
            ) -> ::mettail_dovetail_runtime::DovetailCompilerStage<
                fn(&dyn mettail_runtime::Term) -> Result<mettail_runtime::RuntimeDovetailRunReport, String>,
            > {
                fn __runner(
                    term: &dyn mettail_runtime::Term,
                ) -> Result<mettail_runtime::RuntimeDovetailRunReport, String> {
                    #language_struct::dovetail_report_for(term, 64, 1_000_000)
                }

                ::mettail_dovetail_runtime::DovetailCompilerStage::new(
                    <#language_struct as mettail_runtime::Language>::metadata(&#language_struct)
                        .definition_fingerprint()
                        .unwrap_or_default(),
                    __runner as fn(&dyn mettail_runtime::Term) -> Result<mettail_runtime::RuntimeDovetailRunReport, String>,
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(fragment: &str) -> LanguageDef {
        syn::parse_str(fragment).expect("test language fragment must parse")
    }

    /// The constructs `rule_block` lowered NOWHERE.
    ///
    /// The pre-disposition assertions in this module read `assert!(unsupported.is_empty())`,
    /// which conflated "lowered here" with "lowered on another lane" — both produced an empty
    /// vector. The declination subset is the honest restatement of what those assertions meant.
    fn declined_dispositions(dispositions: &[LoweringDisposition]) -> Vec<&LoweringDisposition> {
        dispositions
            .iter()
            .filter(|disposition| disposition.is_declined())
            .collect()
    }

    #[test]
    fn generated_report_uses_structured_constructor_rules() {
        let language = parse(
            r#"
                name: DovetailSmoke,
                types { Expr }
                terms {
                    A . |- "a" : Expr ;
                    B . |- "b" : Expr ;
                    Wrap . x:Expr |- "wrap" "(" x ")" : Expr ;
                }
                equations {}
                rewrites {
                    AToB . |- A ~> B ;
                }
            "#,
        );

        let tokens = generate_dovetail_report(&language).to_string();
        // ★ UNIT-TEST CONSUMER. `rule_block` now answers with the disposition of every
        // construct, so "nothing was rejected" is the DECLINED subset being empty — the whole
        // vector is never empty, because `AToB` is `Delivered`.
        let (_, dispositions) = rule_block(&language, None);
        let declined = declined_dispositions(&dispositions);
        assert!(tokens.contains("dovetail_report_for"));
        assert!(tokens.contains("DovetailSmoke"));
        assert!(tokens.contains("AToB"));
        assert!(tokens.contains("funded_best"));
        assert!(declined.is_empty(), "unexpected declined rules: {declined:?}");
        // Positive control on that zero: the rewrite really was seen, and really was lowered
        // here — not merely absent from the declination list because nothing was inspected.
        assert!(
            dispositions.iter().any(|disposition| {
                disposition.construct == "AToB"
                    && matches!(
                        disposition.outcome,
                        LoweringOutcome::Delivered { ref label }
                            if label == "DovetailSmoke::rewrite::AToB"
                    )
            }),
            "AToB must be recorded as Delivered: {dispositions:?}",
        );
    }

    #[test]
    fn scalar_report_producer_stays_empty_of_rewrite_justifications() {
        // (R-4 guard) A scalar-only language has no base-rewrite σ-receiver, so its
        // generated report producer never resolves σ provenance — its report is
        // byte-identical to before R-4 (`rewrite_justifications` stays empty).
        let language = parse(
            r#"
                name: ScalarReportGuard,
                types { ![i32] as Int }
                terms { AddInt . a:Int, b:Int |- a "+" b : Int ; }
            "#,
        );
        let tokens = generate_dovetail_report(&language).to_string();
        assert!(tokens.contains("dovetail_report_for"));
        assert!(!tokens.contains("resolve_rewrite_justifications"));
        assert!(!tokens.contains("bareify_rewrite_justifications"));
    }

    #[test]
    fn base_rewrite_report_producer_populates_and_bareifies_sigma() {
        // (R-4) A base-rewrite σ-receiver language DOES resolve + bare-ify σ so a
        // runtime Rho σ-injection can read it.
        let language = parse(
            r#"
                name: SwapReportGuard,
                types { Proc }
                terms {
                    A . |- "A" : Proc ;
                    B . |- "B" : Proc ;
                    Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
                    Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
                }
                equations {}
                rewrites { SwapStep . |- (Swap x y) ~> (Pair y x) ; }
            "#,
        );
        let tokens = generate_dovetail_report(&language).to_string();
        assert!(tokens.contains("resolve_rewrite_justifications"));
        assert!(tokens.contains("__mettail_bareify_rewrite_justifications"));
    }

    #[test]
    fn generated_report_fails_closed_for_binder_metapatterns() {
        let language = parse(
            r#"
                name: DovetailBinder,
                types { Expr Name }
                terms {
                    A . |- "a" : Expr ;
                    B . |- "b" : Expr ;
                    Lam . ^x.p:[Name -> Expr] |- "lam" x "." p : Expr ;
                }
                equations {}
                rewrites {
                    BadBeta . |- (Lam ^x.A) ~> B ;
                }
            "#,
        );

        let tokens = generate_dovetail_report(&language).to_string();
        assert!(tokens.contains("dovetail_report_for"));
        assert!(tokens.contains("lambda patterns require binder lowering"));
    }

    #[test]
    fn generated_report_lowers_ac_bag_rewrite_to_pattern_ac() {
        // An Ambient-shaped fragment: a HashBag `PPar` and an OpenRule AC redex.
        // The rewrite must lower to `Pattern::ac` (NOT be rejected as
        // unsupported), with the constructor label as the AC operator.
        let language = parse(
            r#"
                name: AcSmoke,
                types { Proc Name }
                terms {
                    PZero . Proc ::= "0" ;
                    POpen . Proc ::= "open(" Name "," Proc ")" ;
                    PAmb . Proc ::= Name "[" Proc "]" ;
                    PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
                }
                equations {}
                rewrites {
                    OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
                        ~> (PPar {P, Q, ...rest}) ;
                }
            "#,
        );

        // ★ UNIT-TEST CONSUMER.
        let (_, dispositions) = rule_block(&language, None);
        let declined = declined_dispositions(&dispositions);
        assert!(declined.is_empty(), "AC bag rewrite must lower, not be rejected: {declined:?}");
        assert!(
            dispositions.iter().any(|disposition| {
                disposition.construct == "OpenRule"
                    && matches!(disposition.outcome, LoweringOutcome::Delivered { .. })
            }),
            "OpenRule must be recorded as Delivered on the String path: {dispositions:?}",
        );

        let tokens = generate_dovetail_report(&language).to_string();
        // The lowered rule uses the AC pattern constructor with the PPar label.
        // (`::` inside a string literal is not token-spaced; the surrounding
        // path `Pattern::ac` IS spaced by the token stringifier.)
        assert!(tokens.contains("Pattern :: ac"), "AC bag pattern emitted");
        assert!(
            tokens.contains("AcSmoke::Proc::PPar"),
            "PPar is the AC operator label: {tokens}"
        );
        // The fixed sub-patterns (POpen / PAmb apps) and the `rest` remainder
        // are present.
        assert!(tokens.contains("AcSmoke::Proc::POpen"));
        assert!(tokens.contains("AcSmoke::Proc::PAmb"));
        assert!(tokens.contains("\"rest\""), "rest remainder variable bound");
    }

    #[test]
    fn generated_report_lowers_ac_bag_rewrite_on_the_typed_path() {
        // (A-1 + Stage 3d) The SAME AC bag rewrite must lower on the TYPED fold path
        // (`enum_id = Some(L)`), NOT be rejected as "AC collection metapatterns are
        // not yet lowered on the typed fold path". As of Stage 3d the Ambient `OpenRule`
        // is a STRUCTURAL non-linear AC rewrite, so it lowers on the typed NATIVE lane
        // (`is_structural_ac_rewrite` → a `NativeRule`, skipped by `rule_block`), NOT as a
        // structural `RewriteRule`; the typed op variants (`L::Proc_PPar`, `L::Proc_POpen`,
        // …) still appear — now as the native rule's AcApp LHS + tag-routed element patterns.
        // `rule_block` therefore reports it as NEITHER unsupported (not rejected) NOR a
        // structural rule (it is native).
        let language = parse(
            r#"
                name: AcTypedSmoke,
                types { Proc Name }
                terms {
                    PZero . Proc ::= "0" ;
                    POpen . Proc ::= "open(" Name "," Proc ")" ;
                    PAmb . Proc ::= Name "[" Proc "]" ;
                    PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
                }
                equations {}
                rewrites {
                    OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
                        ~> (PPar {P, Q, ...rest}) ;
                }
            "#,
        );

        let enum_id = op_enum::op_enum_ident(&language);
        // ★ UNIT-TEST CONSUMER. This test's own comment already had to SAY IN PROSE what
        // the return value could not: "`rule_block` therefore reports it as NEITHER unsupported
        // (not rejected) NOR a structural rule (it is native)". That sentence exists only
        // because the old return type could express "not rejected" and "not lowered here" only
        // as the same empty vector. The disposition says it directly, and is asserted.
        let (_, dispositions) = rule_block(&language, Some(&enum_id));
        let declined = declined_dispositions(&dispositions);
        assert!(
            declined.is_empty(),
            "the typed AC bag rewrite must lower (native lane), not be rejected: {declined:?}"
        );
        assert!(
            dispositions.iter().any(|disposition| {
                disposition.construct == "OpenRule"
                    && matches!(
                        disposition.outcome,
                        LoweringOutcome::DeliveredElsewhere {
                            lane: LoweringLane::TypedNativeStructuralAc,
                            ..
                        }
                    )
            }),
            "OpenRule must be attributed to the typed structural-AC native lane, not merely \
             absent: {dispositions:?}",
        );

        // The whole typed report carries the structural-AC NATIVE rule, whose AcApp LHS uses the
        // TYPED op variant (`Proc_PPar`) with the tag-routed `Proc_POpen`/`Proc_PAmb` element
        // patterns + the `rest` remainder.
        let tokens = generate_dovetail_report(&language).to_string();
        assert!(tokens.contains("Pattern :: ac"), "typed AC bag pattern emitted");
        assert!(tokens.contains("Proc_PPar"), "PPar is the typed AC operator variant: {tokens}");
        assert!(tokens.contains("Proc_POpen"), "the fixed POpen element lowers typed");
        assert!(tokens.contains("Proc_PAmb"), "the fixed PAmb element lowers typed");
        assert!(
            !tokens.contains("not yet lowered on the typed fold path"),
            "the typed AC gate must be removed"
        );
        assert!(tokens.contains("\"rest\""), "rest remainder variable bound");
    }

    #[test]
    fn premise_supported_is_exhaustive_and_only_congruence() {
        use mettail_ast::language::{FreshnessCondition, FreshnessTarget};
        use proc_macro2::Span;
        use syn::Ident;
        let id = |s: &str| Ident::new(s, Span::call_site());
        // Congruence is the ONLY supported premise; every other variant fails
        // closed (exhaustive match — no catch-all).
        assert!(premise_supported(&Premise::Congruence { source: id("S"), target: id("T") }));
        assert!(!premise_supported(&Premise::Freshness(FreshnessCondition {
            var: id("x"),
            term: FreshnessTarget::Var(id("P")),
        })));
        assert!(!premise_supported(&Premise::RelationQuery {
            relation: id("rel"),
            args: vec![id("a")],
        }));
    }

    // ─── E2.2: `needs_normal_term` MF7 gating ───────────────────────────────────

    #[test]
    fn needs_normal_term_true_for_structural_rewrite() {
        // A language with a non-congruence structural rewrite (`A ~> B`) gets the method.
        let language = parse(
            r#"
                name: NntStructural,
                types { Expr }
                terms {
                    A . |- "a" : Expr ;
                    B . |- "b" : Expr ;
                }
                equations {}
                rewrites { AToB . |- A ~> B ; }
            "#,
        );
        assert!(needs_normal_term(&language));
    }

    #[test]
    fn needs_normal_term_true_for_equation() {
        // A language with a (structural) equation gets the method even with no rewrites.
        let language = parse(
            r#"
                name: NntEquation,
                types { Expr }
                terms {
                    A . |- "a" : Expr ;
                    B . |- "b" : Expr ;
                }
                equations { Swap . |- A = B ; }
                rewrites {}
            "#,
        );
        assert!(needs_normal_term(&language));
    }

    #[test]
    fn needs_normal_term_false_for_pure_scalar_fold() {
        // A pure scalar-fold language (a native-output `+`/`-` fold, no structural rewrites/
        // equations, no substitution, no channels) is NOT given `dovetail_normal_term`.
        let language = parse(
            r#"
                name: NntPureScalar,
                types { ![i32] as Int }
                terms {
                    AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
                    SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
                }
            "#,
        );
        assert!(!needs_normal_term(&language));
        // Stage 3f: it DOES now reach the typed-fold path. A native SCALAR fold (`AddInt`, whose
        // `+` lowers to an in-Rho scalar contract, so it is classified `NativeFold` and surfaces a
        // native-fold FIRING site) reduces to its host-computed value on the TYPED fold path, so
        // its fold can fire as a COMM (D2(f)/D3). Before Stage 3f it stayed on the untyped String
        // path — where the fold reduced but recorded NO rewrite justification for the native-fold
        // σ-injection to read. `needs_normal_term` and `needs_typed_fold_path` are independent
        // gates: the fold routes typed to fire, but still needs no `dovetail_normal_term`.
        assert!(needs_typed_fold_path(&language));
        assert!(
            !mettail_rholang_codegen::rho_net_native_fold_injection_sites(&language).is_empty(),
            "a `fold` scalar op must surface a native-fold firing site (the reason it routes typed)"
        );
    }

    #[test]
    fn needs_normal_term_true_for_substitution_rewrite() {
        // A β-style substitution in a rewrite RHS (`(eval fun arg)` parses to a `MultiSubst`)
        // triggers the gate. This is independent of E1's stricter `is_substitution_rewrite`
        // shape classifier — being permissive here is sound (it can only enable a fail-closed
        // method). Mirrors the Lambda `Beta` rule.
        let language = parse(
            r#"
                name: NntBeta,
                types { Term }
                terms {
                    Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
                    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term;
                }
                equations {}
                rewrites {
                    Beta . |- (App (Lam fun) arg) ~> (eval fun arg);
                    AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N);
                }
            "#,
        );
        assert!(
            needs_normal_term(&language),
            "a MultiSubst in the rewrite RHS must trigger needs_normal_term"
        );
    }

    // ─── E1.2: `is_substitution_rewrite` shape classifier (MF4) ─────────────────────────────

    /// Find a rewrite by name in a parsed language.
    fn rewrite<'a>(language: &'a LanguageDef, name: &str) -> &'a RewriteRule {
        language
            .rewrites
            .iter()
            .find(|r| r.name == name)
            .unwrap_or_else(|| panic!("rewrite `{name}` not found"))
    }

    /// The Lambda `Beta` rule — `(App (Lam fun) arg) ~> (eval fun arg)` — is detected, with all
    /// `SubstRewrite` fields derived from `LanguageDef` (single binder `[Term->Term]`).
    #[test]
    fn is_substitution_rewrite_detects_lambda_beta() {
        let language = parse(
            r#"
                name: Lam,
                types { Term }
                terms {
                    Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
                    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term;
                }
                equations {}
                rewrites {
                    Beta . |- (App (Lam fun) arg) ~> (eval fun arg);
                    AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N);
                }
            "#,
        );
        let sr = is_substitution_rewrite(&language, rewrite(&language, "Beta"))
            .expect("Beta must be detected as a substitution rewrite");
        assert_eq!(sr.scope_var.to_string(), "fun");
        assert_eq!(
            sr.repl_vars
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>(),
            vec!["arg"]
        );
        assert_eq!(sr.binder_label.to_string(), "Lam");
        assert_eq!(sr.binder_cat.to_string(), "Term");
        assert_eq!(sr.binder_var_cat.to_string(), "Term");
        assert_eq!(sr.body_cat.to_string(), "Term");
        assert!(!sr.multi, "Lam is a single binder");
        assert_eq!(sr.head_label.to_string(), "App");
        assert_eq!(sr.head_cat.to_string(), "Term");

        // The congruence rule is NOT a substitution rewrite.
        assert!(is_substitution_rewrite(&language, rewrite(&language, "AppCongL")).is_none());

        // And it routes the language to the typed path.
        assert!(needs_typed_dovetail_path(&language));
    }

    /// (MF4 — the crux negative) Rholang's `Comm` is NOT a substitution rewrite: its RHS nests
    /// the `MultiSubst` inside an AC `PPar` collection, AND the replacement is a `*map(..)`
    /// comprehension (a `Pattern::Map`), AND the LHS is AC-collection-nested. ANY of these must
    /// reject it; this exercises all three guards together on the real `Comm` shape.
    #[test]
    fn is_substitution_rewrite_rejects_rholang_comm() {
        let language = parse(
            r#"
                name: RholangSubset,
                types {
                    Name
                    Proc
                }
                terms {
                    PZero . Proc ::= "0" ;
                    NQuote . p:Proc |- "@" p : Name ;
                    POutput . n:Name, q:Proc |- n "!(" q ")" : Proc ;
                    PInputs . ^[xs].cont:[Name -> Proc] |- "for(" xs ")" "{" cont "}" : Proc ;
                    PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
                }
                equations {}
                rewrites {
                    Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
                        ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});
                }
            "#,
        );
        assert!(
            is_substitution_rewrite(&language, rewrite(&language, "Comm")).is_none(),
            "Rholang Comm (MultiSubst nested in AC PPar, Map replacement, AC-nested LHS) must NOT \
             be detected as a substitution rewrite"
        );
    }

    // ─── A-3: `is_comm_rewrite` shape classifier ────────────────────────────────────────────

    /// The canonical single-receive COMMUNICATION rule
    /// `(PPar {(PFor N cont), (POutput N Q), ...rest}) ~> (PPar {(eval cont Q), ...rest})` is
    /// detected, with every `CommRewrite` field derived from `LanguageDef`, and it routes the
    /// language to the typed native lane.
    #[test]
    fn is_comm_rewrite_detects_the_canonical_comm() {
        let language = parse(
            r#"
                name: CommClassify,
                types { Proc Name }
                terms {
                    PZero . |- "0" : Proc ;
                    Na . |- "na" : Name ;
                    Nb . |- "nb" : Name ;
                    Nc . |- "nc" : Name ;
                    PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
                    POutput . n:Name, q:Name |- n "!" "(" q ")" : Proc ;
                    PFor . n:Name, ^x.p:[Name -> Proc]
                        |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
                }
                equations {}
                rewrites {
                    Comm . |- (PPar {(PFor N cont), (POutput N Q), ...rest})
                        ~> (PPar {(eval cont Q), ...rest}) ;
                }
            "#,
        );
        let cr = is_comm_rewrite(&language, rewrite(&language, "Comm"))
            .expect("Comm must be detected as a Comm rewrite");
        assert_eq!(cr.op_label.to_string(), "PPar");
        assert_eq!(cr.op_cat.to_string(), "Proc");
        assert_eq!(cr.nonlinear_var.to_string(), "N");
        assert_eq!(cr.rest_var.to_string(), "rest");
        assert_eq!(cr.scope_var.to_string(), "cont");
        assert_eq!(cr.arg_var.to_string(), "Q");
        assert_eq!(cr.binder_var_cat.to_string(), "Name", "the bound variable is a Name");
        assert_eq!(cr.body_cat.to_string(), "Proc", "the continuation body is a Proc");
        assert_eq!(cr.elements.len(), 2);
        // The binder element is `PFor` (its scope is `cont`); `POutput` is the send.
        let binder = &cr.elements[cr.binder_element_index];
        assert_eq!(binder.constructor.to_string(), "PFor");
        assert!(binder.is_binder, "the receive element is a binder");
        let send = &cr.elements[1 - cr.binder_element_index];
        assert_eq!(send.constructor.to_string(), "POutput");
        assert!(!send.is_binder, "the send element is not a binder");
        // And it routes the language to the typed native lane.
        assert!(needs_typed_dovetail_path(&language));
    }

    /// β-reduction (`(App (Lam fun) arg) ~> (eval fun arg)`) is NOT a Comm rewrite — no AC bag, no
    /// non-linear channel — so `is_comm_rewrite` fail-closes (it stays on the `SubstRewrite` lane).
    #[test]
    fn is_comm_rewrite_rejects_lambda_beta() {
        let language = parse(
            r#"
                name: BetaClassify,
                types { Term }
                terms {
                    Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
                    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term;
                }
                equations {}
                rewrites { Beta . |- (App (Lam fun) arg) ~> (eval fun arg); }
            "#,
        );
        assert!(
            is_comm_rewrite(&language, rewrite(&language, "Beta")).is_none(),
            "β-reduction is not a Comm rewrite (no AC bag / non-linear channel)"
        );
    }

    /// A STRUCTURAL non-linear AC rewrite (Ambient's `OpenRule` — the RHS is structural, TWO
    /// elements, NOT a single substitution) is NOT a Comm rewrite: it stays on the AC lane, so
    /// `is_comm_rewrite` fail-closes.
    #[test]
    fn is_comm_rewrite_rejects_structural_ac() {
        let language = parse(
            r#"
                name: OpenClassify,
                types { Proc Name }
                terms {
                    POpen . Proc ::= "open(" Name "," Proc ")" ;
                    PAmb . Proc ::= Name "[" Proc "]" ;
                    PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
                }
                equations {}
                rewrites {
                    OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
                        ~> (PPar {P, Q, ...rest}) ;
                }
            "#,
        );
        assert!(
            is_comm_rewrite(&language, rewrite(&language, "OpenRule")).is_none(),
            "a structural non-linear AC rewrite (RHS is not a single substitution) is not a Comm rewrite"
        );
    }

    // ─── Stage 3d: `is_structural_ac_rewrite` shape classifier ───────────────────────────────────

    /// Ambient's `OpenRule` `(PPar {(POpen N P), (PAmb N Q), ...rest}) ~> (PPar {P, Q, ...rest})` is
    /// detected as a STRUCTURAL non-linear AC rewrite, with every field derived from `LanguageDef`,
    /// and it routes the language to the typed native lane. It is NOT a Comm rewrite (RHS is
    /// structural, not a substitution).
    #[test]
    fn is_structural_ac_rewrite_detects_open_rule() {
        let language = parse(
            r#"
                name: OpenClassify,
                types { Proc Name }
                terms {
                    POpen . Proc ::= "open(" Name "," Proc ")" ;
                    PAmb . Proc ::= Name "[" Proc "]" ;
                    PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
                }
                equations {}
                rewrites {
                    OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
                        ~> (PPar {P, Q, ...rest}) ;
                }
            "#,
        );
        let sr = is_structural_ac_rewrite(&language, rewrite(&language, "OpenRule"))
            .expect("OpenRule must be detected as a structural AC rewrite");
        assert_eq!(sr.op_label.to_string(), "PPar");
        assert_eq!(sr.op_cat.to_string(), "Proc");
        assert_eq!(sr.nonlinear_var.to_string(), "N");
        assert_eq!(sr.rest_var.to_string(), "rest");
        assert_eq!(
            sr.reduct_vars
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>(),
            vec!["P".to_string(), "Q".to_string()]
        );
        assert_eq!(
            sr.elements
                .iter()
                .map(|e| e.constructor.to_string())
                .collect::<Vec<_>>(),
            vec!["POpen".to_string(), "PAmb".to_string()]
        );
        // It is NOT a Comm rewrite (mutually exclusive by RHS shape).
        assert!(is_comm_rewrite(&language, rewrite(&language, "OpenRule")).is_none());
        // And it routes the language (no binder handler — no equations) to the typed native lane.
        assert!(needs_typed_dovetail_path(&language));
    }

    /// The canonical Comm rule (substitution-in-bag RHS) is NOT a structural AC rewrite — the two
    /// classifiers are mutually exclusive by RHS shape.
    #[test]
    fn is_structural_ac_rewrite_rejects_comm() {
        let language = parse(
            r#"
                name: CommNotStructural,
                types { Proc Name }
                terms {
                    PZero . |- "0" : Proc ;
                    Na . |- "na" : Name ;
                    Nb . |- "nb" : Name ;
                    PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
                    POutput . n:Name, q:Name |- n "!" "(" q ")" : Proc ;
                    PFor . n:Name, ^x.p:[Name -> Proc]
                        |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
                }
                equations {}
                rewrites {
                    Comm . |- (PPar {(PFor N cont), (POutput N Q), ...rest})
                        ~> (PPar {(eval cont Q), ...rest}) ;
                }
            "#,
        );
        assert!(
            is_structural_ac_rewrite(&language, rewrite(&language, "Comm")).is_none(),
            "a Comm (substitution-in-bag) RHS is not a structural AC rewrite"
        );
    }

    /// A structural AC rewrite whose RHS reintroduces a FRESH variable the σ cannot supply (not an
    /// LHS-element argument) is rejected.
    #[test]
    fn is_structural_ac_rewrite_rejects_fresh_rhs_var() {
        let language = parse(
            r#"
                name: FreshRhsVar,
                types { Proc Name }
                terms {
                    POpen . Proc ::= "open(" Name "," Proc ")" ;
                    PAmb . Proc ::= Name "[" Proc "]" ;
                    PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
                }
                equations {}
                rewrites {
                    BadOpen . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
                        ~> (PPar {P, Z, ...rest}) ;
                }
            "#,
        );
        assert!(
            is_structural_ac_rewrite(&language, rewrite(&language, "BadOpen")).is_none(),
            "an RHS reduct var `Z` that is not an LHS-element arg is rejected"
        );
    }

    /// A rewrite whose substitution is NESTED inside another `Apply` (not the whole RHS) is
    /// rejected — the substitution must be the entire RHS.
    #[test]
    fn is_substitution_rewrite_rejects_nested_subst_rhs() {
        let language = parse(
            r#"
                name: NestedSubst,
                types { Term }
                terms {
                    Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
                    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term;
                    Wrap . t:Term |- "wrap(" t ")" : Term;
                }
                equations {}
                rewrites {
                    BadBeta . |- (App (Lam fun) arg) ~> (Wrap (eval fun arg));
                }
            "#,
        );
        assert!(
            is_substitution_rewrite(&language, rewrite(&language, "BadBeta")).is_none(),
            "a MultiSubst nested under `Wrap` is not a whole-RHS substitution"
        );
    }

    /// A rewrite whose scope variable is NOT bound by a binder constructor in the LHS is
    /// rejected (no `Binder`/`MultiBinder` position binds `fun`).
    #[test]
    fn is_substitution_rewrite_rejects_non_binder_scope() {
        let language = parse(
            r#"
                name: NoBinderScope,
                types { Term }
                terms {
                    Pair . l:Term, r:Term |- "<" l "," r ">" : Term;
                    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term;
                }
                equations {}
                rewrites {
                    BadBeta . |- (App (Pair fun other) arg) ~> (eval fun arg);
                }
            "#,
        );
        assert!(
            is_substitution_rewrite(&language, rewrite(&language, "BadBeta")).is_none(),
            "`Pair` is not a binder, so `fun` is not bound by a binder position"
        );
    }

    /// (Generality) A CROSS-category binder `[Name -> Proc]` is detected with the bound-variable
    /// category (`Name`) tracked SEPARATELY from the body category (`Proc`). This is what makes
    /// the generated dispatcher select the cross-category `substitute_name` (not
    /// `substitute_proc`) — the substitution lowering is not limited to same-category binders.
    /// (End-to-end reduction of a synthetic language is covered by the Lambda gates; a test-local
    /// `language!` is infeasible here because the macro writes crate-coupled `simulate_<lang>.rs`
    /// + `gen_<lang>_*.rs` files referencing `mettail_languages::<lang>`.)
    #[test]
    fn is_substitution_rewrite_tracks_cross_category_binder() {
        let language = parse(
            r#"
                name: CrossCat,
                types {
                    Name
                    Proc
                }
                terms {
                    NVar . n:Name |- "@" n : Proc;
                    Bind . ^x.body:[Name -> Proc] |- "bind " x "." body : Proc;
                    Send . k:Proc, arg:Name |- "send(" k "," arg ")" : Proc;
                }
                equations {}
                rewrites {
                    Deliver . |- (Send (Bind k) a) ~> (eval k a);
                }
            "#,
        );
        let sr = is_substitution_rewrite(&language, rewrite(&language, "Deliver"))
            .expect("Deliver must be detected (cross-category binder)");
        assert_eq!(sr.scope_var.to_string(), "k");
        assert_eq!(sr.binder_label.to_string(), "Bind");
        assert_eq!(sr.binder_cat.to_string(), "Proc", "Bind constructs a Proc");
        assert_eq!(sr.binder_var_cat.to_string(), "Name", "the bound variable is a Name");
        assert_eq!(sr.body_cat.to_string(), "Proc", "the body is a Proc");
        assert_ne!(
            sr.binder_var_cat.to_string(),
            sr.body_cat.to_string(),
            "cross-category: bound-variable category differs from body category — the dispatcher \
             must select `substitute_name`, not `substitute_proc`"
        );
        assert_eq!(
            sr.repl_vars
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>(),
            vec!["a"]
        );
        assert_eq!(sr.head_label.to_string(), "Send");
    }

    // ─── D10: the SYNCHRONOUS π `Comm` — an arity-2 reduct + an explicit `^x.p` scope ────────────

    /// The GSLT omnibus's synchronous π communication (`omnibus.tex:1988-1989`)
    ///
    /// ```text
    /// Comm . |- (PPar {(PIn n ^x.p), (POut n m q), ...rest}) ~> (PPar {(eval ^x.p m), q, ...rest})
    /// ```
    ///
    /// is a Comm rewrite. It exercises BOTH halves of the D10 generalization at once: the receive
    /// element carries an EXPLICIT binder abstraction `^x.p` (not a bare scope variable), and the
    /// reduct has TWO elements — the host-computed substitution `p[m/x]` AND the output's
    /// continuation `q`, whose parallel composition is exactly `c!x.P | c?y.Q ⇒ P | Q{x/y}`.
    #[test]
    fn is_comm_rewrite_detects_the_synchronous_pi_comm() {
        let language = parse(
            r#"
                name: SyncCommClassify,
                types { Proc Name }
                terms {
                    PZero . |- "0" : Proc ;
                    Na . |- "na" : Name ;
                    Nb . |- "nb" : Name ;
                    PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
                    POut . n:Name, m:Name, p:Proc |- n "!" m "." p : Proc ;
                    PIn . n:Name, ^x.p:[Name -> Proc]
                        |- "in" "(" n "," x ")" "." p : Proc ;
                }
                equations {}
                rewrites {
                    Comm . |- (PPar {(PIn n ^x.p), (POut n m q), ...rest})
                        ~> (PPar {(eval ^x.p m), q, ...rest}) ;
                }
            "#,
        );
        let cr = is_comm_rewrite(&language, rewrite(&language, "Comm"))
            .expect("the synchronous π Comm must be detected as a Comm rewrite");
        assert_eq!(cr.op_label.to_string(), "PPar");
        assert_eq!(cr.nonlinear_var.to_string(), "n", "the shared channel is `n`");
        assert_eq!(cr.rest_var.to_string(), "rest");
        // The explicit `^x.p` scope contributes its BODY variable `p`.
        assert_eq!(cr.scope_var.to_string(), "p");
        assert_eq!(cr.arg_var.to_string(), "m");
        assert_eq!(cr.binder_var_cat.to_string(), "Name");
        assert_eq!(cr.body_cat.to_string(), "Proc");
        let binder = &cr.elements[cr.binder_element_index];
        assert_eq!(binder.constructor.to_string(), "PIn");
        assert!(binder.is_binder);
        assert!(binder.scope_is_explicit_lambda, "`^x.p` is the explicit binder spelling");
        assert_eq!(
            binder
                .args
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>(),
            vec!["n".to_string(), "p".to_string()],
            "the `^x.p` argument contributes the body variable `p`"
        );
        // ★ The D10 property: a TWO-element reduct — the substitution ∥ the output continuation.
        assert_eq!(
            cr.reduct_elements,
            vec![
                CommReductElement::Substitution,
                CommReductElement::Var(Ident::new("q", Span::call_site())),
            ],
            "the synchronous reduct is `(eval ^x.p m) | q`"
        );
        // It is NOT a structural AC rewrite (mutually exclusive: it carries a substitution).
        assert!(is_structural_ac_rewrite(&language, rewrite(&language, "Comm")).is_none());
        // And it routes the language to the typed native lane.
        assert!(needs_typed_dovetail_path(&language));
    }

    /// (D10, fail-closed) A reduct with TWO substitution elements is ambiguous — there is exactly
    /// one host-computed contractum slot (`__comm_reduct`) — so the classifier declines.
    #[test]
    fn is_comm_rewrite_rejects_two_substitution_reducts() {
        let language = parse(
            r#"
                name: TwoSubstReduct,
                types { Proc Name }
                terms {
                    PZero . |- "0" : Proc ;
                    Na . |- "na" : Name ;
                    PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
                    POut . n:Name, m:Name, p:Proc |- n "!" m "." p : Proc ;
                    PIn . n:Name, ^x.p:[Name -> Proc]
                        |- "in" "(" n "," x ")" "." p : Proc ;
                }
                equations {}
                rewrites {
                    Comm . |- (PPar {(PIn n ^x.p), (POut n m q), ...rest})
                        ~> (PPar {(eval ^x.p m), (eval ^x.p m), ...rest}) ;
                }
            "#,
        );
        assert!(
            is_comm_rewrite(&language, rewrite(&language, "Comm")).is_none(),
            "a reduct with two substitutions has no unambiguous host-computed contractum slot"
        );
    }

    /// (D10, fail-closed — the ONE semantic side condition the generalization adds) A σ-delivered
    /// reduct element may not be a binder SCOPE: splicing the raw body `p` of `^x.p` beside the
    /// substitution would let the bound variable `x` escape its binder.
    #[test]
    fn is_comm_rewrite_rejects_a_binder_scope_as_a_bare_reduct_element() {
        let language = parse(
            r#"
                name: EscapingScopeReduct,
                types { Proc Name }
                terms {
                    PZero . |- "0" : Proc ;
                    Na . |- "na" : Name ;
                    PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
                    POut . n:Name, m:Name, p:Proc |- n "!" m "." p : Proc ;
                    PIn . n:Name, ^x.c:[Name -> Proc]
                        |- "in" "(" n "," x ")" "." c : Proc ;
                }
                equations {}
                rewrites {
                    Comm . |- (PPar {(PIn n ^x.c), (POut n m q), ...rest})
                        ~> (PPar {(eval ^x.c m), c, ...rest}) ;
                }
            "#,
        );
        assert!(
            is_comm_rewrite(&language, rewrite(&language, "Comm")).is_none(),
            "a raw binder body may not be spliced into the reduct (the bound variable would escape)"
        );
    }

    /// (D10, fail-closed) A `^x.p` abstraction is admitted ONLY as the LAST argument of a single
    /// `Binder` constructor. Here `POut` is a plain (non-binder) constructor, so writing its last
    /// argument as an abstraction must fail closed rather than silently drop the binder.
    #[test]
    fn is_comm_rewrite_rejects_a_lambda_argument_of_a_non_binder_element() {
        let language = parse(
            r#"
                name: LambdaOnNonBinder,
                types { Proc Name }
                terms {
                    PZero . |- "0" : Proc ;
                    Na . |- "na" : Name ;
                    PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
                    POut . n:Name, m:Name, p:Proc |- n "!" m "." p : Proc ;
                    PIn . n:Name, ^x.p:[Name -> Proc]
                        |- "in" "(" n "," x ")" "." p : Proc ;
                }
                equations {}
                rewrites {
                    Comm . |- (PPar {(PIn n ^x.p), (POut n m ^z.q), ...rest})
                        ~> (PPar {(eval ^x.p m), q, ...rest}) ;
                }
            "#,
        );
        assert!(
            is_comm_rewrite(&language, rewrite(&language, "Comm")).is_none(),
            "an abstraction argument of a non-binder constructor must fail closed"
        );
    }

    /// (D10 regression) The ASYNCHRONOUS single-element reduct — the shape the lane was written for
    /// — still classifies EXACTLY as before, with `reduct_elements == [Substitution]`.
    #[test]
    fn is_comm_rewrite_keeps_the_asynchronous_single_element_reduct() {
        let language = parse(
            r#"
                name: AsyncCommClassify,
                types { Proc Name }
                terms {
                    PZero . |- "0" : Proc ;
                    Na . |- "na" : Name ;
                    Nb . |- "nb" : Name ;
                    PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
                    POutput . n:Name, q:Name |- n "!" "(" q ")" : Proc ;
                    PFor . n:Name, ^x.p:[Name -> Proc]
                        |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
                }
                equations {}
                rewrites {
                    Comm . |- (PPar {(PFor N cont), (POutput N Q), ...rest})
                        ~> (PPar {(eval cont Q), ...rest}) ;
                }
            "#,
        );
        let cr = is_comm_rewrite(&language, rewrite(&language, "Comm"))
            .expect("the asynchronous Comm must still be detected");
        assert_eq!(cr.reduct_elements, vec![CommReductElement::Substitution]);
        let binder = &cr.elements[cr.binder_element_index];
        assert!(
            !binder.scope_is_explicit_lambda,
            "the bare scope-variable spelling is unchanged"
        );
    }
}
