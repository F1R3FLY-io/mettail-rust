//! Semantic-action table emission.
//!
//! Phase A.2: for each atomic rule, emit an `ActionEntry` whose `action_fn`
//! consumes a captured token and pushes the parsed term into the builder.
//! Phase A.3+ extends to composite rules (Pratt, binder, collection, …).

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use mettail_prattail::binding_power::InfixRuleInfo;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::binder::{classify_binder, emit_binder_action_entry};
use super::collection::{classify_collection, CollectionShape};
use super::infix;
use super::prefix::{classify_atomic, AtomicShape, LiteralFamily};
use super::refinement::lookup_refinement_type;
use crate::gen::native::NativeType;

/// Emit the body of `action_for` — a `match (src_idx, rule_idx)` with
/// one arm per rule that has a semantic action.
///
/// `per_cat` is the pre-built combined user + synthetic rule list built
/// by `synthetic::build_per_category_rules`, converted to
/// `Vec<Vec<(rule_idx, &rule)>>` in the caller.
pub fn emit_action_for_body(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<(u16, &GrammarRule)>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        // Look up the Rust ident for this category's AST enum — needed to
        // construct wrapper variants like `Int::NumLit(v)`.
        let cat_name = &categories[cat_i];
        let cat_ident = format_ident!("{}", cat_name);
        for (rule_idx, rule) in rules {
            // Phase 5: try classifying as a binder rule first; takes
            // precedence over collection / atomic / infix classification.
            if let Some(shape) = classify_binder(rule) {
                if let Some(entry) = emit_binder_action_entry(
                    cat_i as u16,
                    *rule_idx,
                    &shape,
                    &cat_ident,
                    categories,
                ) {
                    arms.push(entry);
                }
                continue;
            }
            // Phase 4: try classifying as a collection rule next.
            if let Some(shape) = classify_collection(rule, language) {
                if let Some(entry) = emit_collection_action_entry(
                    cat_i as u16,
                    *rule_idx,
                    &shape,
                    &cat_ident,
                    categories,
                ) {
                    arms.push(entry);
                }
                continue;
            }
            let shape = classify_atomic(rule, language);
            if !matches!(shape, AtomicShape::NonAtomic) {
                let refinement_name =
                    lookup_refinement_type(language, cat_name).map(|r| r.name.to_string());
                if let Some(entry) = emit_action_entry_arm(
                    cat_i as u16,
                    *rule_idx,
                    &shape,
                    &cat_ident,
                    refinement_name.as_deref(),
                    categories,
                    language,
                ) {
                    arms.push(entry);
                }
                continue;
            }
            // Phase 3: try classifying as an infix / postfix / mixfix rule.
            if let Some(info) = infix::classify_rule_public(rule) {
                if let Some(entry) =
                    emit_infix_action_entry(cat_i as u16, *rule_idx, &info, &cat_ident, categories)
                {
                    arms.push(entry);
                }
            }
        }
    }

    if arms.is_empty() {
        quote! { None }
    } else {
        quote! {
            match (src_idx, rule_idx) {
                #(#arms)*
                _ => None,
            }
        }
    }
}

/// Pass-2c token-soundness backstop (2026-05-30): emit the body of
/// `WpdaEngine::min_terminal_span` — a `match (src_idx, rule_idx)` returning,
/// per rule, the count of `SyntaxExpr::Literal` terminals that appear AFTER
/// the rule's FIRST parameter in its `syntax_pattern`. Those literals are
/// matched STRICTLY WITHIN the rule's result-Symbol span (leading literals
/// before the first param are consumed as out-of-span `TriggerTerminal`s), so
/// a sound derivation's Symbol span must exceed the operand spans by at least
/// this many input positions. See `WpdaEngine::min_terminal_span` for the full
/// soundness rationale and the realize-time filter that consumes this.
///
/// Only emitted for rules whose `syntax_pattern` is a plain literal/param
/// sequence (NO `SyntaxExpr::Op` meta-syntax — collection `#sep`/`#zip`/`#map`
/// etc. have variable-length structure whose span arithmetic is not a fixed
/// literal count; those return 0 = no constraint, which never rejects). Rules
/// with a zero count are omitted (default arm returns 0). This targets exactly
/// the trigger-bearing cast shape `"t" "(" a ")"` (count = 1, the trailing
/// `")"`) whose fabricating Pass-2c wrap is the falsified soundness bug.
pub fn emit_min_terminal_span_body(
    categories: &[String],
    per_cat: &[Vec<(u16, &GrammarRule)>],
) -> TokenStream {
    use mettail_ast::grammar::SyntaxExpr;
    let mut arms: Vec<TokenStream> = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let cat_u16 = cat_i as u16;
        for (rule_idx, rule) in rules {
            let Some(sp) = rule.syntax_pattern.as_ref() else {
                continue;
            };
            // Skip patterns containing meta-syntax Op (collections): their
            // span is not a fixed literal count.
            if sp.iter().any(|e| matches!(e, SyntaxExpr::Op(_))) {
                continue;
            }
            // Emit the constraint ONLY for rules whose `term_context` params
            // are ALL `Simple` (a plain typed operand `a:Y` that parses to a
            // Symbol child carrying a real input span). Any non-Simple param —
            // `^x.body` Abstraction / MultiAbstraction (the bound variable is a
            // BinderScope/Ident with NO span), GuardBody, or Optional — makes
            // the realize-time `slack = sym_span - Σ child spans` arithmetic
            // undercount the children (no span for the binder var) and would
            // wrongly reject sound derivations (observed: ambient PNew
            // `"new" "(" x "," p ")"` → `nested_new`). The Pass-2c fabrication
            // this backstop targets is a SIMPLE unary cast
            // (`<Y>To<X> . a:Y |- "t" "(" a ")"`) — all-Simple params — never a
            // binder; binders/guards parse soundly via their own machinery.
            let all_simple_params = rule
                .term_context
                .as_ref()
                .map(|tc| {
                    tc.iter()
                        .all(|p| matches!(p, mettail_ast::grammar::TermParam::Simple { .. }))
                })
                .unwrap_or(true);
            if !all_simple_params {
                continue;
            }
            // Count literals strictly after the first Param.
            let mut seen_param = false;
            let mut post_param_literals: u32 = 0;
            for e in sp.iter() {
                match e {
                    SyntaxExpr::Param(_) => seen_param = true,
                    SyntaxExpr::Literal(_) if seen_param => post_param_literals += 1,
                    _ => {},
                }
            }
            if post_param_literals > 0 {
                let r = *rule_idx;
                arms.push(quote! { (#cat_u16, #r) => #post_param_literals, });
            }
        }
    }
    let _ = categories;
    if arms.is_empty() {
        quote! { 0u32 }
    } else {
        quote! {
            match (src_idx, rule_idx) {
                #(#arms)*
                _ => 0u32,
            }
        }
    }
}

/// Sig-B Blocker-3 §2.3 (2026-06-01, pgmcp experiment #9): emit the body of
/// `WpdaEngine::single_hop_coercion(from_cat, to_cat) -> &[(u16, u16)]`.
///
/// Returns, for the cross-category pair `(from_cat → to_cat)`, the
/// grammar-declared SINGLE-hop coercion rules that bridge it, as
/// `(target_cat = to_cat, rule_index_in_to_cat)` pairs. EMPTY when no such
/// grammar rule exists (the §2.4a clause-4 category compatibility then
/// REJECTS the pair). Usually one entry; MULTIPLE entries are returned when
/// two rules share `(from, to)` (Ambiguous — §2.4c emits one splice job per
/// coercion).
///
/// **The rule set MIRRORS the live span-transparent synthesis EXACTLY**:
/// `prefix.rs` `classify_atomic`'s `CrossCatProjection` arm — sp.len()==1,
/// single Simple `Base(Y)` param, `Param(name)` matching, source≠result.
/// Terminal-bearing wrappers are excluded because they are not transparent
/// coercions; their literal evidence must be parsed by their own continuation.
/// This is the HARD-CONSTRAINT guarantee that the splice's interposed coercion
/// is never an invented terminal-bearing cast.
///
/// Emitted as a `match (from_cat, to_cat)` returning a `&'static [(u16,u16)]`
/// (interned per arm), default `&[]`. Sibling of `min_terminal_span`'s
/// emission. PURE static lookup — no runtime state, O(1).
pub fn emit_single_hop_coercion_body(
    categories: &[String],
    per_cat: &[Vec<(u16, &GrammarRule)>],
    language: &LanguageDef,
) -> TokenStream {
    use mettail_ast::grammar::{SyntaxExpr, TermParam};
    use mettail_ast::types::TypeExpr;
    let _ = language;
    // Collect `(from_cat, to_cat) -> Vec<rule_idx>` so co-bridging rules
    // accumulate into one arm (Ambiguous).
    let mut table: std::collections::BTreeMap<(u16, u16), Vec<u16>> =
        std::collections::BTreeMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let to_cat = cat_i as u16;
        for (rule_idx, rule) in rules {
            // Both shapes require a single Simple param of a foreign Base
            // category. Read the operand (`a:Y`) category name.
            let Some(tc) = rule.term_context.as_ref() else {
                continue;
            };
            if tc.len() != 1 {
                continue;
            }
            let TermParam::Simple { name: param_name, ty } = &tc[0] else {
                continue;
            };
            let TypeExpr::Base(source_ident) = ty else {
                continue;
            };
            let source_cat_name = source_ident.to_string();
            if source_cat_name == rule.category.to_string() {
                continue;
            }
            let Some(sp) = rule.syntax_pattern.as_ref() else {
                continue;
            };
            // Pass-2a CrossCatProjection: sp.len()==1, the lone element is
            // `Param(name)` matching the param (transparent projection
            // `ProcFloat . f:Float |- f : Proc`, span-0, min_terminal_span 0).
            let is_pass2a = sp.len() == 1
                && matches!(
                    sp.first(),
                    Some(SyntaxExpr::Param(syn_name)) if syn_name == param_name
                );
            if !is_pass2a {
                continue;
            }
            let from_cat = categories
                .iter()
                .position(|c| c == &source_cat_name)
                .map(|i| i as u16)
                .unwrap_or(0);
            table.entry((from_cat, to_cat)).or_default().push(*rule_idx);
        }
    }
    let _ = categories;
    if table.is_empty() {
        return quote! { &[] };
    }
    let mut arms: Vec<TokenStream> = Vec::with_capacity(table.len());
    for ((from_cat, to_cat), rule_idxs) in table {
        // Build the `&'static [(to_cat, rule_idx)]` slice literal for this
        // (from, to) pair. `to_cat` is the coercion rule's category
        // (category_src_idx); `rule_idx` is its index within that category.
        let pairs: Vec<TokenStream> = rule_idxs
            .iter()
            .map(|ri| quote! { (#to_cat, #ri) })
            .collect();
        arms.push(quote! {
            (#from_cat, #to_cat) => &[#(#pairs),*],
        });
    }
    quote! {
        match (from_cat, to_cat) {
            #(#arms)*
            _ => &[],
        }
    }
}

/// RC-B (2026-06-17): emit the body of
/// `WpdaEngine::prefix_cast_into(from_cat, to_cat) -> Option<u16>`.
///
/// Returns the local rule index in `to_cat` of the TRIGGER-BEARING
/// single-argument prefix cast `from_cat -> to_cat` — a `kw "(" a ")"` cast
/// such as `BoolToInt . a:Bool |- "int" "(" a ")" : Int`. This is the EXACT
/// COMPLEMENT of [`emit_single_hop_coercion_body`]: same "single Simple param
/// of a foreign Base category" shape, but the syntax pattern is the
/// terminal-bearing wrapper (it contains `Literal`s — the keyword + brackets)
/// rather than the span-0 lone-`Param` transparent projection. These casts are
/// invisible to `single_hop_coercion` (which deliberately excludes them), which
/// is precisely why the chain-folded cross-cat body cannot be re-wrapped by the
/// span-anchored coercion drain and needs the RC-B pop-site reconciliation.
///
/// One entry per `(from, to)` (the FIRST in source order if a grammar somehow
/// declares two `from -> to` bracketed casts via the same shape; the walker
/// re-validates the hit against `action_for` + `min_terminal_span`). Emitted as
/// a `match (from_cat, to_cat)` returning `Option<u16>`, default `None`. PURE
/// static lookup — O(1), no runtime state. Sibling of `single_hop_coercion`.
pub fn emit_prefix_cast_into_body(
    categories: &[String],
    per_cat: &[Vec<(u16, &GrammarRule)>],
) -> TokenStream {
    use mettail_ast::grammar::{SyntaxExpr, TermParam};
    use mettail_ast::types::TypeExpr;
    // `(from_cat, to_cat) -> rule_idx` (first match wins per pair).
    let mut table: std::collections::BTreeMap<(u16, u16), u16> = std::collections::BTreeMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let to_cat = cat_i as u16;
        for (rule_idx, rule) in rules {
            // Single Simple param of a foreign Base category (the cast operand).
            let Some(tc) = rule.term_context.as_ref() else {
                continue;
            };
            if tc.len() != 1 {
                continue;
            }
            let TermParam::Simple { name: param_name, ty } = &tc[0] else {
                continue;
            };
            let TypeExpr::Base(source_ident) = ty else {
                continue;
            };
            let source_cat_name = source_ident.to_string();
            if source_cat_name == rule.category.to_string() {
                continue;
            }
            let Some(sp) = rule.syntax_pattern.as_ref() else {
                continue;
            };
            // TRIGGER-BEARING wrapper: the syntax pattern references the single
            // param (so the cast forwards exactly one operand) AND contains at
            // least one Literal (the keyword / brackets) — i.e. it is NOT the
            // span-0 lone-`Param` transparent projection that
            // `single_hop_coercion` captures.
            let refs_param = sp
                .iter()
                .any(|e| matches!(e, SyntaxExpr::Param(syn_name) if syn_name == param_name));
            let has_literal = sp.iter().any(|e| matches!(e, SyntaxExpr::Literal(_)));
            let is_lone_param = sp.len() == 1
                && matches!(
                    sp.first(),
                    Some(SyntaxExpr::Param(syn_name)) if syn_name == param_name
                );
            if !(refs_param && has_literal && !is_lone_param) {
                continue;
            }
            let from_cat = categories
                .iter()
                .position(|c| c == &source_cat_name)
                .map(|i| i as u16)
                .unwrap_or(0);
            table.entry((from_cat, to_cat)).or_insert(*rule_idx);
        }
    }
    let _ = categories;
    if table.is_empty() {
        return quote! { None };
    }
    let mut arms: Vec<TokenStream> = Vec::with_capacity(table.len());
    for ((from_cat, to_cat), rule_idx) in table {
        arms.push(quote! {
            (#from_cat, #to_cat) => Some(#rule_idx),
        });
    }
    quote! {
        match (from_cat, to_cat) {
            #(#arms)*
            _ => None,
        }
    }
}

/// RC-B (2026-06-17): emit `WpdaEngine::prefix_cast_keyword(to_cat, rule_idx)
/// -> Option<&'static str>` — the LEADING keyword literal of each
/// trigger-bearing prefix-cast rule (the SAME rule set
/// `emit_prefix_cast_into_body` enumerates). The keyword is the first
/// `SyntaxExpr::Literal` in the rule's syntax pattern (e.g. `"int"` for
/// `BoolToInt`, `"|"` for `Len`, `"length"` for `LenList`). The pop-site wrap
/// synthesis uses this to reject a candidate cast whose keyword does not match
/// the enclosing `kw "(" .. ")"` frame's keyword — without which a length
/// operator (also a single-arg trigger-bearing Int producer) would be
/// synthesized under the frame's `int` keyword and fabricate a token-unsound
/// parse (`int(a)` -> `|a|`). Keyed by `(to_cat, rule_idx)` so it is unique per
/// rule. Emitted as a `match (to_cat, rule_idx)`, default `None`. PURE static
/// lookup. Sibling of `prefix_cast_into`.
pub fn emit_prefix_cast_keyword_body(
    categories: &[String],
    per_cat: &[Vec<(u16, &GrammarRule)>],
) -> TokenStream {
    use mettail_ast::grammar::{SyntaxExpr, TermParam};
    use mettail_ast::types::TypeExpr;
    // `(to_cat, rule_idx) -> keyword` for every trigger-bearing prefix cast.
    let mut table: std::collections::BTreeMap<(u16, u16), String> =
        std::collections::BTreeMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let to_cat = cat_i as u16;
        for (rule_idx, rule) in rules {
            // SAME filter as emit_prefix_cast_into_body: single Simple param of
            // a foreign Base category, trigger-bearing wrapper (refs param +
            // has a Literal + not a lone param).
            let Some(tc) = rule.term_context.as_ref() else {
                continue;
            };
            if tc.len() != 1 {
                continue;
            }
            let TermParam::Simple { name: param_name, ty } = &tc[0] else {
                continue;
            };
            let TypeExpr::Base(source_ident) = ty else {
                continue;
            };
            if source_ident.to_string() == rule.category.to_string() {
                continue;
            }
            let Some(sp) = rule.syntax_pattern.as_ref() else {
                continue;
            };
            let refs_param = sp
                .iter()
                .any(|e| matches!(e, SyntaxExpr::Param(syn_name) if syn_name == param_name));
            let has_literal = sp.iter().any(|e| matches!(e, SyntaxExpr::Literal(_)));
            let is_lone_param = sp.len() == 1
                && matches!(
                    sp.first(),
                    Some(SyntaxExpr::Param(syn_name)) if syn_name == param_name
                );
            if !(refs_param && has_literal && !is_lone_param) {
                continue;
            }
            // The leading keyword = the FIRST Literal in the syntax pattern.
            let Some(keyword) = sp.iter().find_map(|e| match e {
                SyntaxExpr::Literal(text) => Some(text.clone()),
                _ => None,
            }) else {
                continue;
            };
            table.entry((to_cat, *rule_idx)).or_insert(keyword);
        }
    }
    let _ = categories;
    if table.is_empty() {
        return quote! { None };
    }
    let mut arms: Vec<TokenStream> = Vec::with_capacity(table.len());
    for ((to_cat, rule_idx), keyword) in table {
        arms.push(quote! {
            (#to_cat, #rule_idx) => Some(#keyword),
        });
    }
    quote! {
        match (to_cat, rule_idx) {
            #(#arms)*
            _ => None,
        }
    }
}

/// D7 fix (2026-05-13): Look up a zero-arity terminal-keyword rule for
/// `cat_name` whose label can serve as an error-fallback variant for a
/// failing literal-eval action.
///
/// Matches shape `<Label> . |- "<terminal>" : <Cat>` where:
///   - `rule.category.to_string() == cat_name`
///   - `term_context` is `Some(empty)` (no params)
///   - `syntax_pattern` is `Some([SyntaxExpr::Literal(_)])` (single literal)
///
/// Returns the rule's label ident (e.g., `Err` for `Err . |- "error" : BigRat`).
/// Calculator has `Err . |- "error" : BigRat` and `Err . |- "error" : Int`;
/// rhocalc has `Err . |- "error" : Proc`. Pattern is grammar-determined.
///
/// Returns the FIRST matching rule (source order). If a grammar lacks such a
/// rule for a category, returns None and the literal action silent-fails as
/// before (W2 detector catches and drops the cursor).
fn lookup_err_fallback_variant(language: &LanguageDef, cat_name: &str) -> Option<Ident> {
    use mettail_ast::grammar::SyntaxExpr;
    language.terms.iter().find_map(|rule| {
        if rule.category.to_string() != cat_name {
            return None;
        }
        let tc = rule.term_context.as_ref()?;
        let sp = rule.syntax_pattern.as_ref()?;
        if !tc.is_empty() || sp.len() != 1 {
            return None;
        }
        if !matches!(sp.first(), Some(SyntaxExpr::Literal(_))) {
            return None;
        }
        Some(rule.label.clone())
    })
}

fn emit_action_entry_arm(
    src_idx: u16,
    rule_idx: u16,
    shape: &AtomicShape,
    cat_ident: &Ident,
    refinement_name: Option<&str>,
    categories: &[String],
    language: &LanguageDef,
) -> Option<TokenStream> {
    // B13c / Candidate H (2026-05-08): per-shape input/output category
    // metadata for cursor-side type-tag projection. Output cat is always
    // the home cat (`src_idx`). Input cats:
    //  - Token-typed shapes (LiteralInteger/Boolean/String/Float/Patterned,
    //    TerminalKeyword, VarRule): single ANY_CAT slot (the action accepts
    //    a Token / Ident, not a Term).
    //  - Cross-cat-projection / Cross-cat-prefix-unary: single Term slot
    //    of source_cat (the source category's index).
    let any_cat = quote! { mettail_prattail::wpda_runtime::ANY_CAT };
    let (action_fn, arity, expected_input_cats) = match shape {
        AtomicShape::LiteralInteger => (emit_integer_literal_action(), 1u8, quote! { &[#any_cat] }),
        AtomicShape::LiteralBoolean => (emit_boolean_literal_action(), 1u8, quote! { &[#any_cat] }),
        AtomicShape::LiteralString => (emit_string_literal_action(), 1u8, quote! { &[#any_cat] }),
        AtomicShape::LiteralFloat => (emit_float_literal_action(), 1u8, quote! { &[#any_cat] }),
        AtomicShape::LiteralPatterned {
            native_type,
            family,
            wrapper_variant,
            rust_code,
            cat_name: lit_cat_name,
            ..
        } => {
            // D7 fix (2026-05-13, refined): on eval failure, push the cat's
            // Err variant ONLY when `family == LiteralFamily::Rational`.
            // Other families fail post-regex only via parse-rejection (Integer
            // overflow/suffix-mismatch; FixedPoint mantissa precision; Float
            // f64 parse failure) which must silent-fail so alternate dispatch
            // (e.g., UInt32 wins for `0u32` after Int rejects) works.
            // Rational is the only family whose post-regex eval can produce a
            // true semantic runtime error (zero denominator → `1r/0r` becomes
            // BigRat::Err displayed as "error").
            //
            // Without this family gate, the unconditional Err fallback closes
            // test_bigrat_literal_division_by_zero_is_error BUT regresses 7
            // tests that depend on silent-fail-then-alternate-dispatch.
            let err_fallback = if matches!(*family, LiteralFamily::Rational) {
                lookup_err_fallback_variant(language, lit_cat_name)
            } else {
                None
            };
            (
                emit_literal_patterned_action(
                    cat_ident,
                    native_type,
                    *family,
                    wrapper_variant,
                    rust_code,
                    refinement_name,
                    err_fallback.as_ref(),
                ),
                1u8,
                quote! { &[#any_cat] },
            )
        },
        AtomicShape::TerminalKeyword { wrapper_variant, .. } => (
            emit_terminal_keyword_action(cat_ident, wrapper_variant),
            1u8,
            quote! { &[#any_cat] },
        ),
        AtomicShape::VarRule { wrapper_variant } => {
            (emit_var_rule_action(cat_ident, wrapper_variant), 1u8, quote! { &[#any_cat] })
        },
        // Stage 1.1: cross-cat wrap-action — pop 1 source-cat Term arg,
        // wrap as Cat::wrapper_variant(Box::new(arg)).
        AtomicShape::CrossCatProjection { source_cat_name, wrapper_variant }
        | AtomicShape::CrossCatPrefixUnary { source_cat_name, wrapper_variant, .. } => {
            let source_src_idx = categories
                .iter()
                .position(|c| c == source_cat_name)
                .map(|i| i as u16)
                .unwrap_or(0);
            (
                emit_cross_cat_wrap_action(cat_ident, source_cat_name, wrapper_variant),
                1u8,
                quote! { &[#source_src_idx] },
            )
        },
        // M6c.6.4.b (2026-05-14): same-cat unary prefix has no atomic-
        // literal semantic action — the rule's action body emits its
        // own AST term wrapping the operand's sub-parse result. Phase
        // 3 binder/prefix dispatch handles emission.
        AtomicShape::PrefixOperator { .. } => return None,
        AtomicShape::NonAtomic => return None, // Phase 3 dispatch handled separately.
    };
    Some(quote! {
        (#src_idx, #rule_idx) => {
            static ENTRY: mettail_prattail::wpda_runtime::ActionEntry =
                mettail_prattail::wpda_runtime::ActionEntry {
                    action_fn: #action_fn,
                    arity: #arity,
                    expected_input_cats: #expected_input_cats,
                    output_cat: #src_idx,
                };
            Some(&ENTRY)
        }
        ,
    })
}

/// Emit the action body for `AtomicShape::LiteralPatterned`.
///
/// The user's `rust_code` (from `literals { Cat { eval: ![ { ... } ] } }`)
/// returns `Result<Intermediate, ()>`. The intermediate type depends on the
/// family:
/// - `Integer` / `CanonicalBigInt`: `IntLit` (requires width-specific extraction)
/// - `Rational`: `CanonicalBigRat`
/// - `FixedPoint`: `CanonicalFixedPoint`
/// - `Float`: native `f32`/`f64` (or a wrapper)
/// - `Boolean`: `bool`
/// - `String`: `String`
///
/// The action: capture text → run rust_code → extract native type → wrap in
/// `Cat::<wrapper_variant>(native)` → push. On parse failure, don't push
/// (builder remains empty; facade surfaces as `ParseError::InvalidLiteral`).
/// This is simpler than pushing a `Cat::Err` variant because not every
/// category has an `Err` variant. Parity drift OK per
/// `feedback_parity_drift_ok_if_better.md`.
fn emit_literal_patterned_action(
    cat_ident: &Ident,
    native_type: &syn::Type,
    family: LiteralFamily,
    wrapper_variant: &Ident,
    rust_code: &TokenStream,
    refinement_name: Option<&str>,
    err_fallback_variant: Option<&Ident>,
) -> TokenStream {
    let conversion = emit_native_conversion(native_type, family);
    // The payload type for `push_term` — unsized `str` becomes `String`.
    let payload_type = normalize_payload_type(native_type);
    // B8 (2026-04-28): if `cat_ident` names a refinement type, gate the
    // push on `evaluate_refinement_predicate(name, &v)`. On false, no push
    // (refinement violation surfaces as `WpdaParseError::EmptyResult` —
    // RT01-equivalent diagnostic).
    let push_guard = match refinement_name {
        Some(name) => quote! {
            if mettail_runtime::evaluate_refinement_predicate(#name, &__v) {
                b.push_term::<#cat_ident>(#cat_ident::#wrapper_variant(__v));
            }
        },
        None => quote! {
            b.push_term::<#cat_ident>(#cat_ident::#wrapper_variant(__v));
        },
    };
    // D7 fix (2026-05-13): on eval failure, push the cat's zero-arity Err
    // variant if one exists. Closes test_bigrat_literal_division_by_zero_is_error
    // (input `1r/0r` — regex matches as one token; parse_rational_lit returns
    // Err for zero denom; previously silent-failed → W2 dropped cursor →
    // parse failed entirely; now pushes BigRat::Err → downstream rewrite
    // surfaces as "error" display).
    //
    // For categories WITHOUT an Err variant in their grammar, the legacy
    // silent-fail behavior is preserved (W2 detector catches and drops).
    let err_branch = match err_fallback_variant {
        Some(err_ident) => quote! {
            b.push_term::<#cat_ident>(#cat_ident::#err_ident);
        },
        None => quote! {
            // No Err variant for this category — preserve legacy silent-fail
            // (W2 detector at wpda_walker.rs:5281 catches the missing push
            // and transitions the cursor to Error).
        },
    };
    quote! {
        |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
         args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
            let arg = args.into_iter().next();
            let text: &str = arg
                .as_ref()
                .and_then(|a| a.as_token_text())
                .unwrap_or("");
            let __result: Result<#payload_type, ()> = (|| -> Result<#payload_type, ()> {
                let __intermediate = { #rust_code }?;
                #conversion
            })();
            if let Ok(__v) = __result {
                #push_guard
            } else {
                #err_branch
            }
        }
    }
}

/// Normalize a category's native type for `push_term::<T>()`, matching the
/// AST-variant payload selection in `macros/src/gen/types/enums.rs`:
/// - `str` → `std::string::String` (unsized can't be a generic param)
/// - `f32`/`f64` → `CanonicalFloat32`/`CanonicalFloat64` (derive Eq/Hash/Ord)
/// - everything else → `#native_type` as-is
fn normalize_payload_type(native_type: &syn::Type) -> TokenStream {
    let nt = NativeType::from_syn_type(native_type);
    match nt {
        NativeType::Str => quote! { std::string::String },
        NativeType::Float32 => quote! { mettail_runtime::CanonicalFloat32 },
        NativeType::Float64 => quote! { mettail_runtime::CanonicalFloat64 },
        _ => quote! { #native_type },
    }
}

/// Emit the intermediate-to-native conversion step. Runs inside a closure
/// where `__intermediate` holds the unwrapped `Ok(_)` result from the user
/// `rust_code` block. Returns `Result<#native_type, ()>`.
fn emit_native_conversion(native_type: &syn::Type, family: LiteralFamily) -> TokenStream {
    let nt = NativeType::from_syn_type(native_type);
    match family {
        LiteralFamily::Integer => match nt {
            NativeType::Int8 => quote! {
                __intermediate.as_i64()
                    .and_then(|v| i8::try_from(v).ok())
                    .ok_or(())
            },
            NativeType::Int16 => quote! {
                __intermediate.as_i64()
                    .and_then(|v| i16::try_from(v).ok())
                    .ok_or(())
            },
            NativeType::Int32 => quote! {
                __intermediate.as_i64()
                    .and_then(|v| i32::try_from(v).ok())
                    .ok_or(())
            },
            NativeType::Int64 => quote! {
                __intermediate.as_i64().ok_or(())
            },
            // Int128: lossless via `as_i128`. (B12 fix: was `as_i64.map(|v| v as i128)`,
            // which silently dropped any value > i64::MAX even though it fit in i128.)
            NativeType::Int128 => quote! {
                __intermediate.as_i128().ok_or(())
            },
            // Isize: bound by i64 on every platform (isize ≤ i64), so as_i64 is lossless;
            // the platform-narrowing happens at the final isize::try_from.
            NativeType::Isize => quote! {
                __intermediate.as_i64()
                    .and_then(|v| isize::try_from(v).ok())
                    .ok_or(())
            },
            NativeType::UInt8 => quote! {
                __intermediate.as_i64()
                    .and_then(|v| u8::try_from(v).ok())
                    .ok_or(())
            },
            NativeType::UInt16 => quote! {
                __intermediate.as_i64()
                    .and_then(|v| u16::try_from(v).ok())
                    .ok_or(())
            },
            NativeType::UInt32 => quote! {
                __intermediate.as_i64()
                    .and_then(|v| u32::try_from(v).ok())
                    .ok_or(())
            },
            // UInt64: lossless via `as_u64`. (B12 fix: was `as_i64.and_then(u64::try_from)`,
            // which silently rejected any value > i64::MAX even though it fit in u64,
            // including u64::MAX itself.)
            NativeType::UInt64 => quote! {
                __intermediate.as_u64().ok_or(())
            },
            // UInt128: lossless via `as_u128`.
            NativeType::UInt128 => quote! {
                __intermediate.as_u128().ok_or(())
            },
            // Usize: lossless via `as_u64` (since usize ≤ u64 on every platform);
            // the platform-narrowing happens at the final usize::try_from.
            NativeType::Usize => quote! {
                __intermediate.as_u64()
                    .and_then(|v| usize::try_from(v).ok())
                    .ok_or(())
            },
            NativeType::CanonicalBigInt => quote! {
                __intermediate
                    .to_bigint()
                    .map(mettail_runtime::CanonicalBigInt::new)
                    .ok_or(())
            },
            _ => quote! { Err(()) },
        },
        // Rational: user's `parse_rational_lit` returns `RationalLit(Ratio<BigInt>)`.
        // Wrap into `CanonicalBigRat` via its `From<Ratio<BigInt>>` impl.
        LiteralFamily::Rational => quote! {
            Ok(mettail_runtime::CanonicalBigRat::from(__intermediate.0))
        },
        // FixedPoint / Float / Boolean / String: the user's rust_code
        // already returns the payload type directly (CanonicalFixedPoint /
        // CanonicalFloat64 / bool / String).
        LiteralFamily::FixedPoint
        | LiteralFamily::Float
        | LiteralFamily::Boolean
        | LiteralFamily::String => quote! {
            Ok(__intermediate)
        },
    }
}

/// Emit the action body for `AtomicShape::TerminalKeyword` — nullary rules
/// like `Err . |- "error" : Int`. Pushes `Cat::<wrapper_variant>` with no
/// payload.
fn emit_terminal_keyword_action(cat_ident: &Ident, wrapper_variant: &Ident) -> TokenStream {
    quote! {
        |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
         _args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
            b.push_term::<#cat_ident>(#cat_ident::#wrapper_variant);
        }
    }
}

/// Stage 1.1: emit the wrap-action body for cross-cat projection /
/// cross-cat prefix unary. The action pops 1 source-cat Term arg and
/// wraps as `Cat::wrapper_variant(Box::new(arg))`.
fn emit_cross_cat_wrap_action(
    cat_ident: &Ident,
    source_cat_name: &str,
    wrapper_variant: &Ident,
) -> TokenStream {
    let source_cat_ident = format_ident!("{}", source_cat_name);
    quote! {
        |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
         args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
            let arg = match args.into_iter().next().and_then(|a| a.into_term_arc::<#source_cat_ident>()) {
                Some(t) => t,
                None => return,
            };
            b.push_term::<#cat_ident>(#cat_ident::#wrapper_variant(arg));
        }
    }
}

/// Phase 5a: emit the action body for `AtomicShape::VarRule`. The rule
/// captured an `Ident` token; the action wraps it as
/// `Cat::<TVar>(OrdVar(Var::Free(get_or_create_var(name))))`.
fn emit_var_rule_action(cat_ident: &Ident, wrapper_variant: &Ident) -> TokenStream {
    quote! {
        |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
         args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
            let arg = args.into_iter().next();
            let name = arg
                .as_ref()
                .and_then(|a| a.as_token_text())
                .unwrap_or("")
                .to_string();
            let var = mettail_runtime::OrdVar(
                mettail_runtime::Var::Free(mettail_runtime::get_or_create_var(name)),
            );
            b.push_term::<#cat_ident>(#cat_ident::#wrapper_variant(var));
        }
    }
}

/// Phase 4: Emit an action entry for a collection-finalize rule. The action
/// has arity 1: the auto-pushed `ActionArg::CollectionId` injected by the
/// walker when the `CollectionMarker` symbol was pushed. The action drains
/// the indexed accumulator from `SemanticBuilder.collection_stack`,
/// downcasts each `ActionArg::Term` to the element category's native type,
/// constructs the container per `coll_kind`, and pushes
/// `Cat::Label(container)` onto the builder stack.
fn emit_collection_action_entry(
    src_idx: u16,
    rule_idx: u16,
    shape: &CollectionShape,
    cat_ident: &Ident,
    _categories: &[String],
) -> Option<TokenStream> {
    let label_ident = format_ident!("{}", shape.label);
    let element_cat_ident = format_ident!("{}", shape.element_cat);
    // The action body diverges between non-Map (sequential element drain)
    // and Map (pair-walking key/value drain). Both produce the runtime
    // container type that matches the AST variant's payload:
    //   Vec → std::vec::Vec<E>
    //   HashBag → mettail_runtime::HashBag<E>
    //   HashSet → std::collections::HashSet<E>
    //   HashMap → mettail_runtime::HashMapLit<K, V>  (NOT std::HashMap;
    //     `Map::MapLit(HashMapLit)` per ast_enums.rs:750. The wrapper
    //     gives deterministic Hash/Ord required by Ascent relations.)
    let action_fn = match shape.coll_kind {
        CollectionType::Vec => quote! {
            |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
             args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
                let id = match args.into_iter().next().and_then(|a| a.as_collection_id()) {
                    Some(id) => id,
                    None => return,
                };
                let drained = b.drain_collection(id);
                let elems: std::vec::Vec<#element_cat_ident> = drained
                    .into_iter()
                    .filter_map(|a| a.into_term::<#element_cat_ident>())
                    .collect();
                b.push_term::<#cat_ident>(#cat_ident::#label_ident(elems));
            }
        },
        CollectionType::HashBag => quote! {
            |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
             args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
                let id = match args.into_iter().next().and_then(|a| a.as_collection_id()) {
                    Some(id) => id,
                    None => return,
                };
                let drained = b.drain_collection(id);
                let container = mettail_runtime::HashBag::<#element_cat_ident>::from_iter(
                    drained
                        .into_iter()
                        .filter_map(|a| a.into_term::<#element_cat_ident>())
                );
                b.push_term::<#cat_ident>(#cat_ident::#label_ident(container));
            }
        },
        CollectionType::HashSet => quote! {
            |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
             args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
                let id = match args.into_iter().next().and_then(|a| a.as_collection_id()) {
                    Some(id) => id,
                    None => return,
                };
                let drained = b.drain_collection(id);
                let container = std::collections::HashSet::<#element_cat_ident>::from_iter(
                    drained
                        .into_iter()
                        .filter_map(|a| a.into_term::<#element_cat_ident>())
                );
                b.push_term::<#cat_ident>(#cat_ident::#label_ident(container));
            }
        },
        CollectionType::HashMap => quote! {
            |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
             args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
                let id = match args.into_iter().next().and_then(|a| a.as_collection_id()) {
                    Some(id) => id,
                    None => return,
                };
                let drained = b.drain_collection(id);
                // Map elements are flattened key/value pairs in drain order:
                // [k0, v0, k1, v1, ...]. Walk two-at-a-time and insert into
                // a HashMapLit (the wrapper that `Map::MapLit(...)` accepts —
                // see runtime/src/hashmap_lit.rs:30 for the wrapper rationale,
                // and language.rs::map_defaults for the `:` key_val_sep that
                // the parser uses to split pairs).
                let mut iter = drained.into_iter();
                let mut container = mettail_runtime::HashMapLit::<
                    #element_cat_ident, #element_cat_ident,
                >::default();
                while let Some(k_arg) = iter.next() {
                    let v_arg = match iter.next() {
                        Some(v) => v,
                        None => break, // odd-length drain; codegen invariant violation
                    };
                    if let (Some(k), Some(v)) = (
                        k_arg.into_term::<#element_cat_ident>(),
                        v_arg.into_term::<#element_cat_ident>(),
                    ) {
                        container.insert(k, v);
                    }
                }
                b.push_term::<#cat_ident>(#cat_ident::#label_ident(container));
            }
        },
    };
    // B13c / Candidate H (2026-05-08): collection-finalize takes one
    // CollectionId (not a Term), so input is ANY_CAT. Output is the home
    // category.
    let any_cat = quote! { mettail_prattail::wpda_runtime::ANY_CAT };
    Some(quote! {
        (#src_idx, #rule_idx) => {
            static ENTRY: mettail_prattail::wpda_runtime::ActionEntry =
                mettail_prattail::wpda_runtime::ActionEntry {
                    action_fn: #action_fn,
                    arity: 1u8,
                    expected_input_cats: &[#any_cat],
                    output_cat: #src_idx,
                };
            Some(&ENTRY)
        }
        ,
    })
}

/// Phase 3: Emit an action entry for an infix / postfix / mixfix rule.
/// Arity = number of operands (2 for binary infix, 1 for postfix, N for
/// mixfix). Action body pops N args from the builder, downcasts each to
/// the operand category's term type, and constructs
/// `<Cat>::<Label>(Box::new(arg_0), ..., Box::new(arg_N))`.
fn emit_infix_action_entry(
    src_idx: u16,
    rule_idx: u16,
    info: &InfixRuleInfo,
    cat_ident: &Ident,
    categories: &[String],
) -> Option<TokenStream> {
    let arity: u8 = if info.is_postfix {
        1
    } else if info.is_mixfix {
        // Mixfix: 1 LHS + N parts (each part has one operand).
        1 + info.mixfix_parts.len() as u8
    } else {
        2 // binary infix
    };
    let label_ident = format_ident!("{}", info.label);
    let operand_cat_ident = format_ident!("{}", info.category);
    // B13c / Candidate H (2026-05-08): per-arg expected categories.
    // Postfix: 1 arg of info.category.
    // Binary infix: 2 args of info.category.
    // Mixfix: arg0=info.category, args 1..N=info.mixfix_parts[i-1].operand_category.
    let lookup_cat_idx = |name: &str| -> u16 {
        categories
            .iter()
            .position(|c| c == name)
            .map(|i| i as u16)
            .unwrap_or(0)
    };
    let operand_cat_idx = lookup_cat_idx(&info.category);
    let result_cat_idx = lookup_cat_idx(&info.result_category);
    let expected_input_cats: Vec<u16> = if info.is_postfix {
        vec![operand_cat_idx]
    } else if info.is_mixfix {
        let mut v = vec![operand_cat_idx];
        for part in &info.mixfix_parts {
            v.push(lookup_cat_idx(&part.operand_category));
        }
        v
    } else {
        vec![operand_cat_idx, operand_cat_idx]
    };
    let cats_lits: Vec<TokenStream> = expected_input_cats
        .iter()
        .map(|c| {
            let c = *c;
            quote! { #c }
        })
        .collect();
    let expected_input_cats_ts = quote! { &[#(#cats_lits),*] };
    let action_fn = if info.is_postfix {
        // Arity-1: pop one operand, construct unary variant.
        quote! {
            |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
             args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
                let mut iter = args.into_iter();
                let arg0 = match iter.next().and_then(|a| a.into_term_arc::<#operand_cat_ident>()) {
                    Some(v) => v,
                    None => return,
                };
                b.push_term::<#cat_ident>(#cat_ident::#label_ident(arg0));
            }
        }
    } else if info.is_mixfix {
        // Arity-N for mixfix. Per-position operand category: arg0 is the LHS
        // (info.category), args 1..N are the per-part operand categories
        // (info.mixfix_parts[i-1].operand_category). For Calculator's ternary
        // these all equal `Int`; for POutput-shape (Name "(" Proc ")") the
        // LHS and inner operand differ — required for B6 step 3 postfix-mixfix.
        let n = arity as usize;
        let pops: Vec<TokenStream> = (0..n)
            .map(|i| {
                let var = format_ident!("arg{}", i);
                let cat_str = if i == 0 {
                    info.category.clone()
                } else {
                    info.mixfix_parts[i - 1].operand_category.clone()
                };
                let cat = format_ident!("{}", cat_str);
                quote! {
                    let #var = match iter.next().and_then(|a| a.into_term_arc::<#cat>()) {
                        Some(v) => v,
                        None => return,
                    };
                }
            })
            .collect();
        let names: Vec<TokenStream> = (0..n)
            .map(|i| {
                let v = format_ident!("arg{}", i);
                quote! { #v }
            })
            .collect();
        quote! {
            |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
             args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
                let mut iter = args.into_iter();
                #(#pops)*
                b.push_term::<#cat_ident>(#cat_ident::#label_ident(#(#names),*));
            }
        }
    } else {
        // Arity-2 binary infix.
        quote! {
            |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
             args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
                let mut iter = args.into_iter();
                let arg0 = match iter.next().and_then(|a| a.into_term_arc::<#operand_cat_ident>()) {
                    Some(v) => v,
                    None => return,
                };
                let arg1 = match iter.next().and_then(|a| a.into_term_arc::<#operand_cat_ident>()) {
                    Some(v) => v,
                    None => return,
                };
                b.push_term::<#cat_ident>(
                    #cat_ident::#label_ident(arg0, arg1)
                );
            }
        }
    };
    Some(quote! {
        (#src_idx, #rule_idx) => {
            static ENTRY: mettail_prattail::wpda_runtime::ActionEntry =
                mettail_prattail::wpda_runtime::ActionEntry {
                    action_fn: #action_fn,
                    arity: #arity,
                    expected_input_cats: #expected_input_cats_ts,
                    output_cat: #result_cat_idx,
                };
            Some(&ENTRY)
        }
        ,
    })
}

// ── Legacy actions retained for the four builtin `NonTerminalKind::*`
// literal variants. No shipped grammar uses these today, but the
// classifier still recognizes them so keep the emitters correct.

fn emit_integer_literal_action() -> TokenStream {
    quote! {
        |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
         args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
            let arg = args.into_iter().next();
            let text = arg
                .as_ref()
                .and_then(|a| a.as_token_text())
                .unwrap_or("0");
            let parsed: i64 = text.parse().unwrap_or_else(|_| {
                if let Some(rest) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
                    i64::from_str_radix(&rest.replace('_', ""), 16).unwrap_or(0)
                } else if let Some(rest) = text.strip_prefix("0b").or_else(|| text.strip_prefix("0B")) {
                    i64::from_str_radix(&rest.replace('_', ""), 2).unwrap_or(0)
                } else if let Some(rest) = text.strip_prefix("0o").or_else(|| text.strip_prefix("0O")) {
                    i64::from_str_radix(&rest.replace('_', ""), 8).unwrap_or(0)
                } else {
                    0
                }
            });
            b.push_term::<i64>(parsed);
        }
    }
}

fn emit_boolean_literal_action() -> TokenStream {
    quote! {
        |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
         args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
            let arg = args.into_iter().next();
            let text = arg
                .as_ref()
                .and_then(|a| a.as_token_text())
                .unwrap_or("false");
            let parsed: bool = matches!(text, "true" | "yeap");
            b.push_term::<bool>(parsed);
        }
    }
}

fn emit_string_literal_action() -> TokenStream {
    quote! {
        |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
         args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
            let arg = args.into_iter().next();
            let text = arg
                .as_ref()
                .and_then(|a| a.as_token_text())
                .unwrap_or("");
            let stripped = text.trim_start_matches('"').trim_end_matches('"').to_string();
            b.push_term::<String>(stripped);
        }
    }
}

fn emit_float_literal_action() -> TokenStream {
    quote! {
        |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
         args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
            let arg = args.into_iter().next();
            let text = arg
                .as_ref()
                .and_then(|a| a.as_token_text())
                .unwrap_or("0.0");
            let parsed: f64 = text.parse().unwrap_or(0.0);
            b.push_term::<f64>(parsed);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::{GrammarItem, NonTerminalKind};
    use mettail_ast::language::{LangType, TokenDef};
    use proc_macro2::Span;
    use syn::{parse_quote, Ident};

    fn rule(label: &str, cat: &str, kind: NonTerminalKind) -> GrammarRule {
        GrammarRule {
            label: Ident::new(label, Span::call_site()),
            category: Ident::new(cat, Span::call_site()),
            items: vec![GrammarItem::NonTerminal {
                ident: Ident::new(&format!("{:?}", kind), Span::call_site()),
                kind,
            }],
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
        }
    }

    fn terminal_rule(label: &str, cat: &str, text: &str) -> GrammarRule {
        GrammarRule {
            label: Ident::new(label, Span::call_site()),
            category: Ident::new(cat, Span::call_site()),
            items: vec![GrammarItem::Terminal(text.into())],
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
        }
    }

    fn category_rule(label: &str, cat: &str, referenced_cat: &str) -> GrammarRule {
        GrammarRule {
            label: Ident::new(label, Span::call_site()),
            category: Ident::new(cat, Span::call_site()),
            items: vec![GrammarItem::NonTerminal {
                ident: Ident::new(referenced_cat, Span::call_site()),
                kind: NonTerminalKind::Category,
            }],
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
        }
    }

    fn lang_with_rules(rules: Vec<GrammarRule>) -> LanguageDef {
        LanguageDef {
            name: Ident::new("Toy", Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: rules,
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    fn lang_with_int_literal() -> LanguageDef {
        let mut lang = lang_with_rules(Vec::new());
        lang.types.push(LangType {
            name: Ident::new("Int", Span::call_site()),
            native_type: Some(parse_quote!(i32)),
            collection_kind: None,
        });
        lang.token_defs.push(TokenDef {
            name: Ident::new("Integer", Span::call_site()),
            pattern: r"[0-9]+".to_string(),
            category: Some(Ident::new("Int", Span::call_site())),
            rust_code: Some(
                quote! { mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::I32)).map_err(|_| ()) },
            ),
            priority: None,
            push_mode: None,
            is_pop: false,
            stream: None,
            from_literals: true,
        });
        lang
    }

    /// Convert `Vec<GrammarRule>` per-cat layout to the indexed view the
    /// emitter expects.
    fn indexed<'a>(per_cat: &'a [Vec<GrammarRule>]) -> Vec<Vec<(u16, &'a GrammarRule)>> {
        per_cat
            .iter()
            .map(|rules| {
                rules
                    .iter()
                    .enumerate()
                    .map(|(i, r)| (i as u16, r))
                    .collect()
            })
            .collect()
    }

    #[test]
    fn empty_language_emits_none() {
        let lang = lang_with_rules(Vec::new());
        let per_cat: Vec<Vec<GrammarRule>> = Vec::new();
        let idx = indexed(&per_cat);
        let ts = emit_action_for_body(&lang, &[], &idx);
        assert!(ts.to_string().trim() == "None");
    }

    #[test]
    fn integer_literal_emits_action_with_arity_1() {
        let rules = vec![rule("IntLit", "Int", NonTerminalKind::Integer)];
        let lang = lang_with_rules(rules.clone());
        let per_cat: Vec<Vec<GrammarRule>> = vec![rules];
        let idx = indexed(&per_cat);
        let ts = emit_action_for_body(&lang, &["Int".to_string()], &idx);
        let s = ts.to_string();
        assert!(s.contains("ActionEntry"));
        assert!(s.contains("arity : 1u8") || s.contains("arity: 1u8"));
    }

    #[test]
    fn mixed_rule_shapes_emits_only_atomic_arms() {
        let rules = vec![
            rule("IntLit", "Int", NonTerminalKind::Integer),
            rule("BoolLit", "Bool", NonTerminalKind::Boolean),
            {
                let mut r = rule("NotAtomic", "Int", NonTerminalKind::Integer);
                r.items.push(GrammarItem::Terminal("+".into()));
                r
            },
        ];
        let lang = lang_with_rules(rules.clone());
        let per_cat: Vec<Vec<GrammarRule>> =
            vec![vec![rules[0].clone(), rules[2].clone()], vec![rules[1].clone()]];
        let idx = indexed(&per_cat);
        let ts = emit_action_for_body(&lang, &["Int".to_string(), "Bool".to_string()], &idx);
        let s = ts.to_string();
        assert!(s.matches("ActionEntry").count() >= 2);
    }

    #[test]
    fn terminal_keyword_emits_action_pushing_nullary_variant() {
        let r = terminal_rule("Err", "Int", "error");
        let lang = lang_with_rules(vec![r.clone()]);
        let per_cat: Vec<Vec<GrammarRule>> = vec![vec![r]];
        let idx = indexed(&per_cat);
        let ts = emit_action_for_body(&lang, &["Int".to_string()], &idx);
        let s = ts.to_string();
        assert!(s.contains("ActionEntry"));
        assert!(s.contains("Int :: Err") || s.contains("Int::Err"));
    }

    #[test]
    fn literal_patterned_int_emits_action_with_numlit_wrapper() {
        // Category-referencing rule with rule.category == ident AND a
        // from_literals TokenDef for that category.
        let r = category_rule("IntLit", "Int", "Int");
        let mut lang = lang_with_int_literal();
        lang.terms.push(r.clone());
        let per_cat: Vec<Vec<GrammarRule>> = vec![vec![r]];
        let idx = indexed(&per_cat);
        let ts = emit_action_for_body(&lang, &["Int".to_string()], &idx);
        let s = ts.to_string();
        assert!(s.contains("ActionEntry"));
        assert!(s.contains("NumLit"));
        assert!(s.contains("as_i64") || s.contains("i32"));
    }

    /// Build a language with a single literal rule for `cat` whose native_type
    /// is `native`. Used by B12 conversion-emission tests below.
    fn lang_with_typed_literal(cat: &str, native: syn::Type) -> LanguageDef {
        let mut lang = lang_with_rules(Vec::new());
        lang.types.push(LangType {
            name: Ident::new(cat, Span::call_site()),
            native_type: Some(native),
            collection_kind: None,
        });
        lang.token_defs.push(TokenDef {
            name: Ident::new(cat, Span::call_site()),
            pattern: r"[0-9]+".to_string(),
            category: Some(Ident::new(cat, Span::call_site())),
            rust_code: Some(quote! { mettail_prattail::parse_int_lit(text, None).map_err(|_| ()) }),
            priority: None,
            push_mode: None,
            is_pop: false,
            stream: None,
            from_literals: true,
        });
        lang
    }

    /// B12: Int128-typed literal must emit `as_i128()` (not `as_i64`).
    /// Pre-fix it routed through `as_i64.map(|v| v as i128)`, silently
    /// dropping any value > i64::MAX even though it fit in i128.
    #[test]
    fn literal_patterned_int128_emits_as_i128_conversion() {
        let r = category_rule("IntLit", "Int128Cat", "Int128Cat");
        let mut lang = lang_with_typed_literal("Int128Cat", parse_quote!(i128));
        lang.terms.push(r.clone());
        let per_cat: Vec<Vec<GrammarRule>> = vec![vec![r]];
        let idx = indexed(&per_cat);
        let ts = emit_action_for_body(&lang, &["Int128Cat".to_string()], &idx);
        let s = ts.to_string();
        assert!(s.contains("as_i128"), "expected as_i128() call, got: {s}");
        assert!(!s.contains("as_i64"), "Int128 must not route through as_i64: {s}");
    }

    /// B12: UInt64-typed literal must emit `as_u64()` (not `as_i64`).
    /// Pre-fix it routed through `as_i64.and_then(u64::try_from)`, silently
    /// rejecting any value > i64::MAX (including u64::MAX itself).
    #[test]
    fn literal_patterned_uint64_emits_as_u64_conversion() {
        let r = category_rule("UInt64Lit", "UInt64Cat", "UInt64Cat");
        let mut lang = lang_with_typed_literal("UInt64Cat", parse_quote!(u64));
        lang.terms.push(r.clone());
        let per_cat: Vec<Vec<GrammarRule>> = vec![vec![r]];
        let idx = indexed(&per_cat);
        let ts = emit_action_for_body(&lang, &["UInt64Cat".to_string()], &idx);
        let s = ts.to_string();
        assert!(s.contains("as_u64"), "expected as_u64() call, got: {s}");
        assert!(!s.contains("as_i64"), "UInt64 must not route through as_i64: {s}");
    }

    /// B12: UInt128-typed literal must emit `as_u128()` (not `as_i64`).
    #[test]
    fn literal_patterned_uint128_emits_as_u128_conversion() {
        let r = category_rule("UInt128Lit", "UInt128Cat", "UInt128Cat");
        let mut lang = lang_with_typed_literal("UInt128Cat", parse_quote!(u128));
        lang.terms.push(r.clone());
        let per_cat: Vec<Vec<GrammarRule>> = vec![vec![r]];
        let idx = indexed(&per_cat);
        let ts = emit_action_for_body(&lang, &["UInt128Cat".to_string()], &idx);
        let s = ts.to_string();
        assert!(s.contains("as_u128"), "expected as_u128() call, got: {s}");
        assert!(!s.contains("as_i64"), "UInt128 must not route through as_i64: {s}");
    }

    /// B12: Usize-typed literal must route through `as_u64()` (lossless for
    /// usize), then down-narrow with `usize::try_from`. Pre-fix it routed
    /// through `as_i64.and_then(usize::try_from)`, dropping u64::MAX on 64-bit.
    #[test]
    fn literal_patterned_usize_emits_as_u64_with_usize_narrow() {
        let r = category_rule("UsizeLit", "UsizeCat", "UsizeCat");
        let mut lang = lang_with_typed_literal("UsizeCat", parse_quote!(usize));
        lang.terms.push(r.clone());
        let per_cat: Vec<Vec<GrammarRule>> = vec![vec![r]];
        let idx = indexed(&per_cat);
        let ts = emit_action_for_body(&lang, &["UsizeCat".to_string()], &idx);
        let s = ts.to_string();
        assert!(s.contains("as_u64"), "Usize must use as_u64 for the lossless prefix, got: {s}");
        assert!(s.contains("usize :: try_from") || s.contains("usize::try_from"));
    }
}
