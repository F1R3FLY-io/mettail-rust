//! Auto-injection codegen — emit synthetic cross-cat injection rules
//! for lossless built-in promotion edges.
//!
//! **Stage 3.13 (2026-04-30):** generalizes per-grammar hand-written
//! injection rules like
//! ```text
//! IntToBigInt . i:Int |- i : BigInt ;
//! IntToBigRat . i:Int |- i : BigRat ;
//! ```
//! into automatic emission driven by `NativeKind::lossless_targets()`.
//!
//! **Relocated from `mettail-macros` into `mettail-ast` (2026-06-15)** so the
//! exact macro-time augmentation of a `LanguageDef` can be replayed at runtime
//! by [`reconstruct_language_def`]. The macro applies composition then this
//! auto-injection then computes the definition fingerprint over the augmented
//! def; hosting the augmentation here lets a generated language's
//! `definition_source()` be re-augmented to the same fingerprint without
//! depending on the proc-macro crate.
//!
//! ## Why
//!
//! Hand-writing `<Source>To<Target>` injection rules per grammar is
//! duplicative + error-prone + combinatorial. Rholang's `bigrat_display_parse_roundtrip`
//! failure (B9) was caused by missing such an injection that Calculator
//! had hand-written. With auto-injection, every grammar declaring both
//! `Int` (or any signed-int width) and `BigInt` automatically gets the
//! right cross-cat injection without grammar-author intervention.
//!
//! ## Invocation
//!
//! Called from `macros/src/lib.rs` AFTER composition (`apply_extends` /
//! `apply_includes` / `apply_mixins`) and BEFORE codegen. Synthetic
//! rules are appended to `language.terms`, where downstream passes
//! (classify_atomic, classify_judgement, prefix.rs::emit_cross_cat,
//! Display, lint, etc.) consume them byte-identically to user-written
//! rules.
//!
//! ## Demand-driven default (Option B from `plan-auto-injection-codegen.md`)
//!
//! Synthetic rules are emitted ONLY when:
//! 1. Both source and target categories are declared in the language.
//! 2. Source's `NativeKind` has target's `NativeKind` in its
//!    `lossless_targets()`.
//! 3. The user has NOT already defined an injection rule for this
//!    `(source_cat, target_cat)` pair (dedup via
//!    `classify_simple_projection_shape`).
//!
//! Lossy edges (`IntN → UIntM`, `Float → IntN`, etc.) require
//! per-edge user opt-in via grammar `options { auto_inject_allow: [...] }`
//! — emitted only on explicit allow-list match, gated behind
//! `auto_inject_lossy: true` (current default `false`).
//!
//! ## Future-proof
//!
//! Adding a new built-in type (`Decimal128`):
//! 1. Add `NativeKind::Decimal128` variant.
//! 2. Update `from_syn_type`, `standard_token_variant`.
//! 3. Add `Decimal128 → CanonicalBigRat` (etc.) to
//!    `NativeKind::lossless_targets`.
//!
//! Every grammar declaring `![Decimal128] as Money` gains the
//! `Decimal128 → BigRat` injection rule automatically. Zero code
//! change in this file or downstream codegen.

use crate::grammar::{GrammarRule, SyntaxExpr, TermParam};
use crate::language::{AttributeValue, LanguageDef, NativeKind, Premise, RewriteRule};
use crate::pattern::{Pattern, PatternTerm};
use crate::types::TypeExpr;
use proc_macro2::Span;
use std::collections::{HashMap, HashSet};
use syn::Ident;

use crate::grammar_shapes::classify_simple_projection_shape;

/// Stage 3.13e (2026-05-01): auto-injection emits both term constructors
/// (`<Source>To<Target>` `GrammarRule`s) AND matching congruence rewrites
/// (`<Source>To<Target>Cong` `RewriteRule`s) atomically per pair, so the
/// rewrite engine propagates inner `rw_<source>` reductions through the
/// cast wrapper into `rw_<target>`.
pub struct AutoInjectionOutput {
    pub terms: Vec<GrammarRule>,
    pub rewrites: Vec<RewriteRule>,
}

/// Check the `options { auto_inject: ... }` setting on the language.
///
/// Default: `true` (auto-injection enabled). Grammars that hit
/// regressions due to new synthetic rules can opt out by setting
/// `options { auto_inject: false }`.
fn is_auto_inject_enabled(language: &LanguageDef) -> bool {
    match language.options.get("auto_inject") {
        Some(AttributeValue::Bool(b)) => *b,
        _ => true, // default: enabled
    }
}

/// Reconstruct a generated language's exact macro-time augmented
/// [`LanguageDef`] from its raw `language!` body source.
///
/// This replays — byte-for-byte — the mutation pipeline that
/// `macros/src/lib.rs` performs on a parsed `LanguageDef` before it computes
/// the definition fingerprint (see `crate::identity::language_definition_fingerprint`):
///
/// 1. `syn::parse_str::<LanguageDef>(raw_source)` — parse the raw body.
/// 2. `apply_extends` / `apply_includes` / `apply_mixins` — composition.
/// 3. `emit_auto_injection_rules` — synthetic cross-cat injection terms +
///    congruence/normalization rewrites, appended to `terms`/`rewrites`.
///
/// Validation and stratification analysis are intentionally omitted: they are
/// read-only checks that never mutate the `LanguageDef`, so they cannot change
/// the fingerprint. The returned value therefore fingerprints identically to
/// the macro-expanded definition for any language whose composition clauses
/// resolve trivially.
///
/// ## Exactness scope
///
/// Composition (`apply_extends`/`apply_includes`/`apply_mixins`) resolves base
/// and fragment grammars against `crate::registry`, which is the *macro-time*
/// in-process registry. At runtime that registry is empty, so composition is a
/// no-op for any language that declares `extends`/`includes`/`mixins`. The
/// standalone generated languages (Calculator, Rholang, Ambient, GuardedRho)
/// declare none, so this reconstruction is **exact** for them. Reconstructing a
/// composed language exactly would require serializing the resolved base/fragment
/// sources into the registry at runtime — that is a separate, later task.
pub fn reconstruct_language_def(raw_source: &str) -> syn::Result<LanguageDef> {
    let mut def = syn::parse_str::<LanguageDef>(raw_source)?;

    // Mirror macros/src/lib.rs: apply composition clauses in order.
    // `apply_*` return `Result<(), String>`; map any error to a syn::Error so
    // callers get a uniform error type. For standalone languages these are
    // no-ops (empty extends/includes/mixins).
    let span = Span::call_site();
    crate::merge::apply_extends(&mut def)
        .map_err(|msg| syn::Error::new(span, format!("extends error:\n{msg}")))?;
    crate::merge::apply_includes(&mut def)
        .map_err(|msg| syn::Error::new(span, format!("includes error:\n{msg}")))?;
    crate::merge::apply_mixins(&mut def)
        .map_err(|msg| syn::Error::new(span, format!("mixins error:\n{msg}")))?;

    // Mirror macros/src/lib.rs: append synthetic auto-injection terms +
    // rewrites. This is the augmentation the fingerprint is computed over.
    let out = emit_auto_injection_rules(&def);
    def.terms.extend(out.terms);
    def.rewrites.extend(out.rewrites);

    // S2 — the reserved-reflect-namespace gate, at the SECOND entry point.
    //
    // `macros/src/lib.rs` calls `validate_language` after composition settles, so
    // a macro-authored language is gated. This function is the OTHER way a
    // `LanguageDef` reaches codegen — `planned_rho_backend_for` and the FLT demo
    // both build one here, with no proc-macro anywhere — and it did not validate
    // at all. A definition that never passed the macro gate could therefore reach
    // the lowering, which is exactly the hole the namespace check exists to close.
    //
    // Only the namespace check is applied, not full `validate_language`: this is a
    // RE-PARSE of a definition that already compiled, so re-running the whole
    // validator would be redundant work on the runtime path, and any disagreement
    // would be a defect in the round trip rather than in the language. The
    // namespace rule is the one property that must hold no matter which door the
    // definition came through, because the tags it protects are unforgeability
    // primitives.
    crate::validation::validate_reserved_reflect_names(&def)
        .map_err(|err| syn::Error::new(span, err.message()))?;

    Ok(def)
}

/// Emit synthetic auto-injection rules for the given language.
///
/// Returns the list of new `GrammarRule`s to append to
/// `language.terms`. Caller is responsible for the actual append.
///
/// Algorithm:
/// 1. Collect `(NativeKind, category_name)` pairs for every type
///    declaration in the language with a non-`Other` native kind.
/// 2. Collect user-defined injections via
///    `classify_simple_projection_shape` (skip-list).
/// 3. For each `(source_kind, target_kind)` lossless edge, find every
///    `(source_cat, target_cat)` pair and emit
///    `<Source>To<Target> . v:Source |- v : Target ;`
///    unless the pair is already in the user skip-list.
pub fn emit_auto_injection_rules(language: &LanguageDef) -> AutoInjectionOutput {
    if !is_auto_inject_enabled(language) {
        return AutoInjectionOutput { terms: Vec::new(), rewrites: Vec::new() };
    }

    // Step 1: kind → category name(s).
    let mut kind_to_cats: HashMap<NativeKind, Vec<String>> = HashMap::new();
    for ty in &language.types {
        let Some(native_ty) = ty.native_type.as_ref() else {
            continue;
        };
        let kind = NativeKind::from_syn_type(native_ty);
        if matches!(kind, NativeKind::Other) {
            continue;
        }
        kind_to_cats
            .entry(kind)
            .or_default()
            .push(ty.name.to_string());
    }

    // Step 2a: user-defined simple-projection skip-list (by source→target pair).
    let mut user_injections: HashSet<(String, String)> = HashSet::new();
    for rule in &language.terms {
        if let Some(shape) = classify_simple_projection_shape(rule) {
            user_injections.insert((shape.source_category, shape.target_category));
        }
    }

    // Step 2b: user-defined LABELS skip-list (catches function-call forms like
    // `BoolToInt . a:Bool |- "int" "(" a ")" : Int` which are NOT simple
    // projections but happen to share our synthesized label name). Without
    // this, auto-injection would emit a duplicate `BoolToInt` rule and
    // codegen would fail at G04 + E0428 duplicate-name.
    let user_labels: HashSet<String> = language.terms.iter().map(|r| r.label.to_string()).collect();

    // Stage 3.13e (2026-05-01): user-defined congruence-rule skip set.
    // Two layers:
    //   (a) `user_cong_constructors` — set of constructor labels for which
    //       the user has hand-written a congruence rewrite. If the user
    //       wrote `MyFloatToBigRatCong . | S ~> T |- (FloatToBigRat S) ~>
    //       (FloatToBigRat T) ;`, we skip emitting our synthetic
    //       `FloatToBigRatCong` to avoid duplicate-Ascent-rule emission.
    //   (b) `user_cong_labels` — set of cong-rule names. If the user
    //       wrote a cong with label `FloatToBigRatCong` (different shape,
    //       same name), still skip.
    // Both layers are populated from `language.rewrites`.
    let mut user_cong_constructors: HashSet<String> = HashSet::new();
    let user_cong_labels: HashSet<String> = language
        .rewrites
        .iter()
        .filter(|r| r.is_congruence_rule())
        .map(|r| r.name.to_string())
        .collect();
    for rule in &language.rewrites {
        if !rule.is_congruence_rule() {
            continue;
        }
        // Extract the LHS apply-constructor: pattern `(K x)` where K is
        // the constructor for which this rule is a congruence.
        if let Pattern::Term(PatternTerm::Apply { constructor, .. }) = &rule.left {
            user_cong_constructors.insert(constructor.to_string());
        }
    }

    // Fix B (F5 canonicalization, 2026-05-11): collect absorber-category
    // map for cast canonicalization. Map: result_cat → [source_native_cat]
    // where the user declared `Cast<source> . v:source |- v : result_cat`.
    // For each lossless edge (source_a → source_b) where both are sources
    // of casts into the SAME absorber result_cat, we'll emit a
    // canonicalization rewrite lifting Cast<source_a> to Cast<source_b>
    // (via the auto-injected source_a-to-source_b cast inside).
    let mut absorbers: std::collections::BTreeMap<String, Vec<String>> =
        std::collections::BTreeMap::new();
    for (src, tgt) in &user_injections {
        absorbers.entry(tgt.clone()).or_default().push(src.clone());
    }

    // Step 3: enumerate lossless edges, emit synthetic rules.
    let mut synth_terms: Vec<GrammarRule> = Vec::new();
    let mut synth_rewrites: Vec<RewriteRule> = Vec::new();
    let mut emitted_pairs: HashSet<(String, String)> = HashSet::new();
    let mut emitted_cast_canon: HashSet<(String, String, String)> = HashSet::new();

    // Sort kinds for deterministic emission order across runs.
    let mut sorted_kinds: Vec<NativeKind> = kind_to_cats.keys().copied().collect();
    sorted_kinds.sort_by_key(|k| native_kind_sort_key(*k));

    for source_kind in &sorted_kinds {
        let Some(source_cats) = kind_to_cats.get(source_kind) else {
            continue;
        };
        for &target_kind in source_kind.lossless_targets() {
            let Some(target_cats) = kind_to_cats.get(&target_kind) else {
                continue;
            };
            for source_cat in source_cats {
                for target_cat in target_cats {
                    if source_cat == target_cat {
                        continue;
                    }
                    let pair = (source_cat.clone(), target_cat.clone());
                    if user_injections.contains(&pair) || emitted_pairs.contains(&pair) {
                        continue;
                    }
                    let label = format!("{}To{}", source_cat, target_cat);
                    if user_labels.contains(&label) {
                        // User has a rule with this exact label (likely a
                        // function-call form like `BoolToInt . a:Bool |- "int" "(" a ")" : Int`).
                        // Skip auto-emission to avoid duplicate-label codegen errors.
                        continue;
                    }
                    synth_terms.push(make_injection_rule(source_cat, target_cat));
                    // Stage 3.13e (2026-05-01): emit matching cong rule unless
                    // user has covered the constructor or claimed the label.
                    let cong_label = format!("{}Cong", label);
                    let cong_already_covered = user_cong_constructors.contains(&label)
                        || user_cong_labels.contains(&cong_label);
                    if !cong_already_covered {
                        synth_rewrites.push(make_injection_cong_rule(source_cat, target_cat));
                    }
                    emitted_pairs.insert(pair);

                    // Fix B (F5 canonicalization, 2026-05-11): for each
                    // absorber category that has BOTH Cast<source_cat>
                    // AND Cast<target_cat>, emit a canonicalization
                    // rewrite lifting Cast<source_cat> wraps to
                    // Cast<target_cat>. This normalizes mixed cast
                    // operands of binary ops to a uniform variant so
                    // fold rules' same-variant arms can match.
                    for (result_cat, sources) in &absorbers {
                        if sources.iter().any(|s| s == source_cat)
                            && sources.iter().any(|s| s == target_cat)
                        {
                            let canon_key =
                                (result_cat.clone(), source_cat.clone(), target_cat.clone());
                            if emitted_cast_canon.contains(&canon_key) {
                                continue;
                            }
                            let canon_label =
                                format!("NormCast{}To{}In{}", source_cat, target_cat, result_cat);
                            // Skip if the user defined a rewrite with the
                            // same label name (defensive against future
                            // user-hand-written canonicalizations).
                            if user_cong_labels.contains(&canon_label) {
                                continue;
                            }
                            synth_rewrites.push(make_cast_canonicalization_rule(
                                result_cat, source_cat, target_cat,
                            ));
                            emitted_cast_canon.insert(canon_key);
                        }
                    }
                }
            }
        }
    }

    // Phase A.2+A.3 (2026-05-16): post-process NormCast rules to embed
    // a `Premise::SyntheticInjGuard` premise excluding all auto-injected
    // injection variants targeting the cascade's source_cat. This bounds
    // the cross-cat coercion cascade at depth 1 per source term — see
    // ~/.claude/plans/phase-a-cascade-option-c-refined.md (Option C.5).
    //
    // The exclusion list is derived AFTER all synth_terms are emitted
    // (so `<X>To<source_cat>` injections emitted in later loop iterations
    // are correctly captured). Empty exclusion list = no guard premise
    // emitted (zero-cost for grammars without cross-cat injection
    // targeting source_cat).
    //
    // Grammar-general: applies to any grammar whose `kind_to_cats x
    // lossless_targets()` enumeration yields multi-hop cascades.
    let injections_into: std::collections::BTreeMap<String, Vec<Ident>> = {
        let mut m: std::collections::BTreeMap<String, Vec<Ident>> = Default::default();
        for r in &synth_terms {
            // synth_terms entries are all auto-injected `<X>To<C>` rules
            // whose label has been emitted; r.category is the TARGET cat
            // (i.e., where the cast variant lives).
            m.entry(r.category.to_string())
                .or_default()
                .push(r.label.clone());
        }
        // Deterministic ordering for reproducible codegen output.
        for variants in m.values_mut() {
            variants.sort_by_key(|i| i.to_string());
        }
        m
    };
    for rw in synth_rewrites.iter_mut() {
        if !rw.is_auto_injected {
            continue;
        }
        let name = rw.name.to_string();
        if !name.starts_with("NormCast") {
            continue;
        }
        // Parse source_cat from "NormCast<Src>To<Tgt>In<Result>". The
        // boundary is the FIRST "To" after "NormCast". `Src` must be a
        // valid category name (no embedded "To" or "In" substrings in
        // category names is enforced grammar-wide).
        let after_prefix = &name["NormCast".len()..];
        let Some(to_idx) = after_prefix.find("To") else {
            continue;
        };
        let src_cat = &after_prefix[..to_idx];
        let Some(variants) = injections_into.get(src_cat) else {
            continue;
        };
        if variants.is_empty() {
            continue;
        }
        // The LHS pattern `Cast<Src>(v)` registers `v` in
        // `lhs_clauses.bindings`. At codegen time, the SyntheticInjGuard
        // lowering looks up `bindings[inner_var.to_string()]` to obtain
        // the actual Rust-side expression — honoring the Apply-pattern
        // lowering's positional rename (`v` → `s_f<i>` → `s_f<i>_deref`).
        let inner_var = Ident::new("v", Span::call_site());
        let source_category = Ident::new(src_cat, Span::call_site());
        // Phase A.5 (2026-05-17): codegen-time diagnostic log listing
        // the synthetic-injection exclusion set per NormCast rule. The
        // `eprintln!` runs DURING macro expansion (i.e., at cargo build
        // time), surfacing the cascade-bounding behavior to users who
        // want to audit which auto-injection variants are excluded
        // from each cast rule.
        //
        // Gated on the `WPDA_CODEGEN_DIAG` env var (set by `cargo build`
        // -E or via a build-time `--config env.WPDA_CODEGEN_DIAG=1`) so
        // it doesn't pollute the standard build log. Look for entries
        // like:
        //   [phase-a.5] NormCastIntToBigRatInProc: excluding from Int:
        //     [BoolToInt, UInt32ToInt]
        if std::env::var("WPDA_CODEGEN_DIAG").is_ok() {
            let variants_str: Vec<String> = variants.iter().map(|v| v.to_string()).collect();
            eprintln!(
                "[phase-a.5] {}: excluding from {}: [{}]",
                name,
                src_cat,
                variants_str.join(", "),
            );
        }
        rw.premises.push(Premise::SyntheticInjGuard {
            inner_var,
            source_category,
            excluded_variants: variants.clone(),
        });
    }

    AutoInjectionOutput {
        terms: synth_terms,
        rewrites: synth_rewrites,
    }
}

/// Stage 3.13e (2026-05-01): build the canonical congruence rewrite for
/// a synthetic `<Source>To<Target>` cast constructor.
///
/// Shape (matches user-written cast cong rules like `IntToFloatCong` at
/// `languages/src/calculator.rs:486-488`):
///
/// ```text
/// <Source>To<Target>Cong . | S ~> T |- (<Source>To<Target> S) ~> (<Source>To<Target> T) ;
/// ```
///
/// Reads at the rewrite engine: "if `S` rewrites to `T` (in `Source`'s
/// `rw_<source>`), then `<Source>To<Target>(S)` rewrites to
/// `<Source>To<Target>(T)` (in `Target`'s `rw_<target>`)." Without this
/// rule, inner-source reductions are absorbed by the cast wrapper and
/// never propagate to `rw_<target>`.
///
/// `is_auto_injected: true` mirrors `GrammarRule.is_auto_injected`
/// (Stage 3.13b precedent), letting future W05-rewrite-analog lints
/// distinguish synthetic vs user-authored cong rules.
/// Fix B (F5 canonicalization, 2026-05-11): emit a canonicalization
/// rewrite that lifts `Cast<Source>` wrappers in an absorber category
/// to `Cast<Target>` via the auto-injected `Source-To-Target` cast.
///
/// Shape:
///   `NormCast<Source>To<Target>In<ResultCat> . |- (Cast<Source> v) ~> (Cast<Target> (<Source>To<Target> v))`
///
/// Used to canonicalize mixed-cast operands of binary ops (e.g.,
/// `Add(CastBigInt(_), CastUInt32(_))`) to a uniform cast variant
/// (e.g., `Add(CastBigInt(_), CastBigInt(UInt32ToBigInt(_)))`), then
/// further to `Add(CastBigRat(...), CastBigRat(...))`. The transitive
/// closure of these rewrites reaches the terminal node of the lossless
/// lattice (BigRat for numeric types). The Add fold's
/// `(CastBigRat, CastBigRat)` arm then matches and folds.
///
/// `is_auto_injected: true` marks the rule synthetic for lint filtering.
fn make_cast_canonicalization_rule(
    result_cat: &str,
    source_cat: &str,
    target_cat: &str,
) -> RewriteRule {
    let label_str = format!("NormCast{}To{}In{}", source_cat, target_cat, result_cat);
    let name = Ident::new(&label_str, Span::call_site());
    let v = Ident::new("v", Span::call_site());
    let cast_source = Ident::new(&format!("Cast{}", source_cat), Span::call_site());
    let cast_target = Ident::new(&format!("Cast{}", target_cat), Span::call_site());
    let source_to_target =
        Ident::new(&format!("{}To{}", source_cat, target_cat), Span::call_site());

    // LHS: (CastSource v)
    let lhs = Pattern::Term(PatternTerm::Apply {
        constructor: cast_source,
        args: vec![Pattern::Term(PatternTerm::Var(v.clone()))],
    });
    // RHS: (CastTarget (SourceToTarget v))
    let inner = Pattern::Term(PatternTerm::Apply {
        constructor: source_to_target,
        args: vec![Pattern::Term(PatternTerm::Var(v))],
    });
    let rhs = Pattern::Term(PatternTerm::Apply {
        constructor: cast_target,
        args: vec![inner],
    });

    RewriteRule {
        name,
        type_context: Vec::new(),
        premises: Vec::new(),
        left: lhs,
        right: rhs,
        is_auto_injected: true,
    }
}

fn make_injection_cong_rule(source_cat: &str, target_cat: &str) -> RewriteRule {
    let label_str = format!("{}To{}Cong", source_cat, target_cat);
    let name = Ident::new(&label_str, Span::call_site());
    let s = Ident::new("S", Span::call_site());
    let t = Ident::new("T", Span::call_site());
    let ctor = Ident::new(&format!("{}To{}", source_cat, target_cat), Span::call_site());

    let lhs = Pattern::Term(PatternTerm::Apply {
        constructor: ctor.clone(),
        args: vec![Pattern::Term(PatternTerm::Var(s.clone()))],
    });
    let rhs = Pattern::Term(PatternTerm::Apply {
        constructor: ctor,
        args: vec![Pattern::Term(PatternTerm::Var(t.clone()))],
    });

    RewriteRule {
        name,
        type_context: Vec::new(),
        premises: vec![Premise::Congruence { source: s, target: t }],
        left: lhs,
        right: rhs,
        is_auto_injected: true,
    }
}

/// Construct a synthetic `<Source>To<Target> . v:Source |- v : Target ;`
/// `GrammarRule`, byte-identical at downstream passes to user-written
/// equivalents.
///
/// **Stage 3.13 root-cause fix (2026-05-01):** populates BOTH `term_context`
/// AND `items`/`bindings` via `crate::grammar::convert_term_context_to_items`,
/// matching the DSL parser's behavior at `ast/src/grammar.rs:589`. Without
/// this, downstream codegen (test-gen, lint, parser arms) reading `rule.items`
/// treats the synthetic rule as a nullary constructor and emits
/// type-mismatched code (E0308) referencing the AST variant without its
/// required `Box<Source>` payload.
fn make_injection_rule(source_cat: &str, target_cat: &str) -> GrammarRule {
    let label_str = format!("{}To{}", source_cat, target_cat);
    let label = Ident::new(&label_str, Span::call_site());
    let category = Ident::new(target_cat, Span::call_site());
    let param_name = Ident::new("v", Span::call_site());
    let source_ty = Ident::new(source_cat, Span::call_site());

    let term_context = vec![TermParam::Simple {
        name: param_name.clone(),
        ty: TypeExpr::Base(source_ty),
    }];

    // Populate `items` + `bindings` exactly as the language! macro DSL parser
    // does (single source of truth — `convert_term_context_to_items`). This
    // ensures synthetic rules are byte-identical to user-written rules of
    // the same shape at every downstream codegen pass.
    let (items, bindings) = crate::grammar::convert_term_context_to_items(&term_context);

    GrammarRule {
        label,
        category,
        items,
        bindings,
        term_context: Some(term_context),
        syntax_pattern: Some(vec![SyntaxExpr::Param(param_name)]),
        rust_code: None,
        eval_mode: None,
        is_right_assoc: false,
        // A cross-category injection is a unary promotion (`v : Source ⊢ v : Target`),
        // never an infix operator, so it never reaches a precedence level to share.
        shares_level_with_previous: false,
        prefix_bp: None,
        tier_directive: None,
        // Stage 3.13b (2026-05-01): provenance flag — synthetic rule
        // emitted by auto-injection. Stage 3.13c filter consumes this at
        // pipeline.rs:1316 to exclude from legacy unified-trampoline view.
        is_auto_injected: true,
        doc_comment: None,
        is_canonical_synonym: false,
    }
}

/// Stable sort key for `NativeKind`: ensures deterministic emission
/// order across runs. The order itself doesn't matter for correctness
/// (only for reproducibility).
fn native_kind_sort_key(kind: NativeKind) -> u8 {
    match kind {
        NativeKind::Bool => 0,
        NativeKind::Int8 => 1,
        NativeKind::Int16 => 2,
        NativeKind::Int32 => 3,
        NativeKind::Int64 => 4,
        NativeKind::Int128 => 5,
        NativeKind::Isize => 6,
        NativeKind::UInt8 => 7,
        NativeKind::UInt16 => 8,
        NativeKind::UInt32 => 9,
        NativeKind::UInt64 => 10,
        NativeKind::UInt128 => 11,
        NativeKind::Usize => 12,
        NativeKind::Float32 => 13,
        NativeKind::Float64 => 14,
        NativeKind::CanonicalBigInt => 15,
        NativeKind::CanonicalBigRat => 16,
        NativeKind::CanonicalFixedPoint => 17,
        NativeKind::Str => 18,
        NativeKind::Other => 19,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::LangType;
    use syn::parse_quote;

    fn ident(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    fn lang_type(name: &str, native_ty: syn::Type) -> LangType {
        LangType {
            name: ident(name),
            native_type: Some(native_ty),
            collection_kind: None,
        }
    }

    fn empty_language() -> LanguageDef {
        LanguageDef {
            name: ident("Test"),
            options: HashMap::new(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    #[test]
    fn emits_int_to_bigint_when_both_declared() {
        let mut lang = empty_language();
        lang.types.push(lang_type("Int", parse_quote!(i32)));
        lang.types
            .push(lang_type("BigInt", parse_quote!(CanonicalBigInt)));

        let output = emit_auto_injection_rules(&lang);
        let rules = &output.terms;

        // Should emit IntToBigInt + IntToBigRat? No, BigRat not declared, so just IntToBigInt.
        let labels: Vec<String> = rules.iter().map(|r| r.label.to_string()).collect();
        assert!(labels.contains(&"IntToBigInt".to_string()), "got: {:?}", labels);
    }

    #[test]
    fn emits_full_int_to_bigrat_chain_when_all_declared() {
        let mut lang = empty_language();
        lang.types.push(lang_type("Int", parse_quote!(i32)));
        lang.types
            .push(lang_type("BigInt", parse_quote!(CanonicalBigInt)));
        lang.types
            .push(lang_type("BigRat", parse_quote!(CanonicalBigRat)));

        let output = emit_auto_injection_rules(&lang);
        let rules = &output.terms;
        let labels: Vec<String> = rules.iter().map(|r| r.label.to_string()).collect();
        assert!(labels.contains(&"IntToBigInt".to_string()), "got: {:?}", labels);
        assert!(labels.contains(&"IntToBigRat".to_string()), "got: {:?}", labels);
        assert!(labels.contains(&"BigIntToBigRat".to_string()), "got: {:?}", labels);
    }

    #[test]
    fn skips_user_defined_injection() {
        let mut lang = empty_language();
        lang.types.push(lang_type("Int", parse_quote!(i32)));
        lang.types
            .push(lang_type("BigInt", parse_quote!(CanonicalBigInt)));

        // User-defined rule for the IntToBigInt pair.
        let user_rule = GrammarRule {
            label: ident("MyIntToBigInt"),
            category: ident("BigInt"),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(vec![TermParam::Simple {
                name: ident("v"),
                ty: TypeExpr::Base(ident("Int")),
            }]),
            syntax_pattern: Some(vec![SyntaxExpr::Param(ident("v"))]),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            shares_level_with_previous: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
            is_canonical_synonym: false,
        };
        lang.terms.push(user_rule);

        let output = emit_auto_injection_rules(&lang);
        let rules = &output.terms;
        let labels: Vec<String> = rules.iter().map(|r| r.label.to_string()).collect();
        assert!(
            !labels.contains(&"IntToBigInt".to_string()),
            "should skip user-defined Int→BigInt; got: {:?}",
            labels
        );
    }

    #[test]
    fn no_emission_when_only_one_kind_declared() {
        let mut lang = empty_language();
        lang.types.push(lang_type("Int", parse_quote!(i32)));
        // No BigInt or BigRat declared.

        let output = emit_auto_injection_rules(&lang);
        // Only Int declared → no lossless edges to emittable targets.
        assert!(
            output.terms.is_empty(),
            "got terms: {:?}",
            output
                .terms
                .iter()
                .map(|r| r.label.to_string())
                .collect::<Vec<_>>()
        );
        assert!(
            output.rewrites.is_empty(),
            "got rewrites: {:?}",
            output
                .rewrites
                .iter()
                .map(|r| r.name.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn synthetic_rule_shape_matches_user_form() {
        // The emitted rule must satisfy `classify_simple_projection_shape`
        // exactly so downstream passes treat it byte-identically.
        let mut lang = empty_language();
        lang.types.push(lang_type("Int", parse_quote!(i32)));
        lang.types
            .push(lang_type("BigInt", parse_quote!(CanonicalBigInt)));

        let output = emit_auto_injection_rules(&lang);
        let int_to_big = output
            .terms
            .iter()
            .find(|r| r.label == "IntToBigInt")
            .expect("IntToBigInt should be emitted");

        let shape = classify_simple_projection_shape(int_to_big)
            .expect("emitted rule should be classified as simple projection");
        assert_eq!(shape.source_category, "Int");
        assert_eq!(shape.target_category, "BigInt");
    }

    #[test]
    fn deterministic_emission_order() {
        let mut lang = empty_language();
        lang.types
            .push(lang_type("BigInt", parse_quote!(CanonicalBigInt)));
        lang.types.push(lang_type("Int", parse_quote!(i32)));

        let output1 = emit_auto_injection_rules(&lang);
        let output2 = emit_auto_injection_rules(&lang);

        let labels1: Vec<String> = output1.terms.iter().map(|r| r.label.to_string()).collect();
        let labels2: Vec<String> = output2.terms.iter().map(|r| r.label.to_string()).collect();
        assert_eq!(labels1, labels2, "term emission order must be deterministic");

        let cong1: Vec<String> = output1
            .rewrites
            .iter()
            .map(|r| r.name.to_string())
            .collect();
        let cong2: Vec<String> = output2
            .rewrites
            .iter()
            .map(|r| r.name.to_string())
            .collect();
        assert_eq!(cong1, cong2, "cong emission order must be deterministic");
    }

    #[test]
    fn float_to_bigrat_emitted() {
        let mut lang = empty_language();
        lang.types.push(lang_type("Float", parse_quote!(f64)));
        lang.types
            .push(lang_type("BigRat", parse_quote!(CanonicalBigRat)));

        let output = emit_auto_injection_rules(&lang);
        let rules = &output.terms;
        let labels: Vec<String> = rules.iter().map(|r| r.label.to_string()).collect();
        assert!(labels.contains(&"FloatToBigRat".to_string()), "got: {:?}", labels);
    }

    // ─── Stage 3.13e (2026-05-01): synthetic congruence rule tests ────────

    #[test]
    fn emits_cong_rule_alongside_term() {
        let mut lang = empty_language();
        lang.types.push(lang_type("Int", parse_quote!(i32)));
        lang.types
            .push(lang_type("BigInt", parse_quote!(CanonicalBigInt)));

        let output = emit_auto_injection_rules(&lang);

        // Must emit IntToBigInt term constructor.
        let term_labels: Vec<String> = output.terms.iter().map(|r| r.label.to_string()).collect();
        assert!(
            term_labels.contains(&"IntToBigInt".to_string()),
            "expected IntToBigInt term; got: {:?}",
            term_labels
        );

        // Must emit IntToBigIntCong rewrite alongside.
        let cong_labels: Vec<String> = output.rewrites.iter().map(|r| r.name.to_string()).collect();
        assert!(
            cong_labels.contains(&"IntToBigIntCong".to_string()),
            "expected IntToBigIntCong rewrite; got: {:?}",
            cong_labels
        );

        // The cong rule must satisfy `is_congruence_rule()`.
        let cong = output
            .rewrites
            .iter()
            .find(|r| r.name == "IntToBigIntCong")
            .expect("cong rule");
        assert!(cong.is_congruence_rule(), "synthetic cong must satisfy is_congruence_rule()",);
    }

    #[test]
    fn synthetic_cong_marked_auto_injected() {
        let mut lang = empty_language();
        lang.types.push(lang_type("Int", parse_quote!(i32)));
        lang.types
            .push(lang_type("BigInt", parse_quote!(CanonicalBigInt)));

        let output = emit_auto_injection_rules(&lang);
        let cong = output
            .rewrites
            .iter()
            .find(|r| r.name == "IntToBigIntCong")
            .expect("cong rule");
        assert!(cong.is_auto_injected, "synthetic cong must have is_auto_injected = true");
    }

    #[test]
    fn skips_cong_when_user_has_one_with_matching_constructor() {
        // User-written cong on the synthetic constructor — synthetic
        // skipped to avoid duplicate-Ascent-rule emission. The TERM
        // is still emitted (Stage 3.13's existing behavior).
        let mut lang = empty_language();
        lang.types.push(lang_type("Int", parse_quote!(i32)));
        lang.types
            .push(lang_type("BigInt", parse_quote!(CanonicalBigInt)));

        // Build a user cong rewrite: `MyIntToBigIntCong . | S ~> T |- (IntToBigInt S) ~> (IntToBigInt T)`.
        let s = ident("S");
        let t = ident("T");
        let ctor = ident("IntToBigInt");
        let user_cong = RewriteRule {
            name: ident("MyIntToBigIntCong"),
            type_context: Vec::new(),
            premises: vec![Premise::Congruence { source: s.clone(), target: t.clone() }],
            left: Pattern::Term(PatternTerm::Apply {
                constructor: ctor.clone(),
                args: vec![Pattern::Term(PatternTerm::Var(s))],
            }),
            right: Pattern::Term(PatternTerm::Apply {
                constructor: ctor,
                args: vec![Pattern::Term(PatternTerm::Var(t))],
            }),
            is_auto_injected: false,
        };
        lang.rewrites.push(user_cong);

        let output = emit_auto_injection_rules(&lang);
        let cong_labels: Vec<String> = output.rewrites.iter().map(|r| r.name.to_string()).collect();
        assert!(
            !cong_labels.contains(&"IntToBigIntCong".to_string()),
            "should skip synthetic cong when user has one for the constructor; got: {:?}",
            cong_labels
        );
    }

    #[test]
    fn skips_cong_on_label_collision() {
        // User-written rewrite with the SAME label as the synthetic cong
        // (different shape — not a cong on IntToBigInt). Synthetic
        // skipped to avoid duplicate-name codegen errors.
        let mut lang = empty_language();
        lang.types.push(lang_type("Int", parse_quote!(i32)));
        lang.types
            .push(lang_type("BigInt", parse_quote!(CanonicalBigInt)));

        // Build a degenerate cong on a different constructor but same label.
        let s = ident("S");
        let t = ident("T");
        let ctor = ident("Other");
        let user_cong = RewriteRule {
            name: ident("IntToBigIntCong"),
            type_context: Vec::new(),
            premises: vec![Premise::Congruence { source: s.clone(), target: t.clone() }],
            left: Pattern::Term(PatternTerm::Apply {
                constructor: ctor.clone(),
                args: vec![Pattern::Term(PatternTerm::Var(s))],
            }),
            right: Pattern::Term(PatternTerm::Apply {
                constructor: ctor,
                args: vec![Pattern::Term(PatternTerm::Var(t))],
            }),
            is_auto_injected: false,
        };
        lang.rewrites.push(user_cong);

        let output = emit_auto_injection_rules(&lang);
        // Only the user's cong should remain — synthetic was suppressed.
        let synthetic_count = output
            .rewrites
            .iter()
            .filter(|r| r.name == "IntToBigIntCong" && r.is_auto_injected)
            .count();
        assert_eq!(
            synthetic_count, 0,
            "should skip synthetic cong on label collision; got {} synthetic copies",
            synthetic_count
        );
    }

    // ─── Reconstruction identity (2026-06-15) ─────────────────────────────

    #[test]
    fn reconstruct_standalone_language_appends_auto_injection() {
        // A standalone language (no extends/includes/mixins) reconstructs to
        // the same augmented def the macro would produce: parse + auto-inject.
        let src = r#"
            name: ReconstructSmoke,
            types {
                Proc
                ![i32] as Int
                ![mettail_runtime::CanonicalBigInt] as BigInt
            }
            terms {
                AddInt . a:Int, b:Int |- a "+" b : Int ;
            }
        "#;
        let def = reconstruct_language_def(src).expect("standalone reconstruct must parse");
        let labels: Vec<String> = def.terms.iter().map(|r| r.label.to_string()).collect();
        assert!(
            labels.contains(&"AddInt".to_string()),
            "user rule must survive; got: {labels:?}"
        );
        assert!(
            labels.contains(&"IntToBigInt".to_string()),
            "auto-injection must append IntToBigInt; got: {labels:?}"
        );
        let cong: Vec<String> = def.rewrites.iter().map(|r| r.name.to_string()).collect();
        assert!(
            cong.contains(&"IntToBigIntCong".to_string()),
            "auto-injection must append the congruence rewrite; got: {cong:?}"
        );
    }

    #[test]
    fn reconstruct_matches_direct_parse_plus_emit() {
        // `reconstruct_language_def` must produce the exact same fingerprint as
        // a manual parse + apply_* (no-ops here) + emit_auto_injection_rules.
        let src = r#"
            name: ReconstructFingerprint,
            types {
                Proc
                ![i32] as Int
                ![mettail_runtime::CanonicalBigInt] as BigInt
                ![mettail_runtime::CanonicalBigRat] as BigRat
            }
            terms {
                AddInt . a:Int, b:Int |- a "+" b : Int ;
                Neg . a:Int |- "-" a : Int ;
            }
        "#;
        let reconstructed = reconstruct_language_def(src).expect("reconstruct must parse");

        let mut manual = syn::parse_str::<LanguageDef>(src).expect("manual parse");
        let out = emit_auto_injection_rules(&manual);
        manual.terms.extend(out.terms);
        manual.rewrites.extend(out.rewrites);

        assert_eq!(
            crate::identity::language_definition_fingerprint(&reconstructed),
            crate::identity::language_definition_fingerprint(&manual),
            "reconstruct must equal direct parse + auto-injection"
        );
    }
}
