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

use super::binder::{
    cat_idx_tokens, classify_binder_in, emit_binder_action_entry, field_order_disagreement,
};
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
            if let Some(shape) = classify_binder_in(rule, language) {
                // ★ #139 — THE POSITIONAL GATE. This is the one site that holds
                // BOTH derivations of the variant's field order: the rule (from
                // which `gen/types/enums.rs` will write the DEFINITION, via
                // `gen::capture::field_layout`) and the shape (from which
                // `emit_binder_action_entry` will write the CONSTRUCTION). A
                // disagreement is refused HERE, at the offending rule, because
                // downstream it is not reliably a compile error: two same-typed
                // fields transpose in silence.
                if let Some(message) = field_order_disagreement(rule, &shape) {
                    let span = rule.label.span();
                    let refusal = syn::Error::new(span, message).to_compile_error();
                    let src_idx = cat_i as u16;
                    let rule_idx = *rule_idx;
                    arms.push(quote! {
                        (#src_idx, #rule_idx) => { #refusal }
                        ,
                    });
                    continue;
                }
                if let Some(entry) = emit_binder_action_entry(
                    cat_i as u16,
                    *rule_idx,
                    &shape,
                    &cat_ident,
                    categories,
                    rule.label.span(),
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
                    &rule.label.to_string(),
                    rule.label.span(),
                ) {
                    arms.push(entry);
                }
                continue;
            }
            // Phase 3: try classifying as an infix / postfix / mixfix rule.
            if let Some(info) = infix::classify_rule_public(rule) {
                if let Some(entry) = emit_infix_action_entry(
                    cat_i as u16,
                    *rule_idx,
                    &info,
                    &cat_ident,
                    categories,
                    rule.label.span(),
                ) {
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

/// ROOT-C structural token-soundness backstop (2026-07-08): emit the body of
/// `WpdaEngine::rule_leads_with_literal(src_idx, rule_idx) -> bool` — a
/// `match (src_idx, rule_idx)` returning `true` for every rule whose FIRST
/// `syntax_pattern` element is a `SyntaxExpr::Literal`.
///
/// This is the STRUCTURAL companion to `min_terminal_span`. Where the (count-
/// based) span filter cannot soundly distinguish a rule's IN-span leading
/// literal (rholang `ToStr`'s `str`) from an OUT-OF-span leading trigger
/// (calculator `StrToInt`'s `int`, lambda `App`'s `(`) — because that split is
/// a runtime parse property, not a grammar property — this predicate captures
/// the ONE grammar fact both dispositions share: the rule LEADS WITH A LITERAL,
/// so a sound derivation must realize that literal as a terminal-kind FIRST
/// child. The realize filter (`packing_satisfies_min_terminal_span`) then
/// rejects any such packing whose `children[0]` is a `Symbol` (the demand-
/// driver's fabricated cast wrap, which consumed no leading literal). See
/// `WpdaEngine::rule_leads_with_literal` for the full rationale.
///
/// Grammar-derived and MAXIMALLY general: EVERY literal-led rule is included
/// (casts, groupings, sigil sends, keyword atoms) — the structural check on
/// `children[0]` is inert for a sound packing (its first child IS the terminal)
/// and fires only on the phantom, so over-inclusion here can never reject a
/// sound parse. Emitted unconditionally (no kill-switch): the trait default is
/// `false`, so the generated impl is byte-identical for grammars with no
/// literal-led rules.
pub fn emit_rule_leads_with_literal_body(per_cat: &[Vec<(u16, &GrammarRule)>]) -> TokenStream {
    use mettail_ast::grammar::SyntaxExpr;
    let mut arms: Vec<TokenStream> = Vec::new();
    for (ci, rules) in per_cat.iter().enumerate() {
        let cat_u16 = ci as u16;
        for (rule_idx, rule) in rules {
            let Some(sp) = rule.syntax_pattern.as_ref() else {
                continue;
            };
            if matches!(sp.first(), Some(SyntaxExpr::Literal(_))) {
                let r = *rule_idx;
                arms.push(quote! { (#cat_u16, #r) => true, });
            }
        }
    }
    if arms.is_empty() {
        quote! { false }
    } else {
        quote! {
            match (src_idx, rule_idx) {
                #(#arms)*
                _ => false,
            }
        }
    }
}

/// AT_QUOTED_BIND_GATE realize-backstop (option B, 2026-07-03). Emit the body
/// of `WpdaEngine::sigil_quoted_bind_overgen_rule(src_idx, rule_idx) -> bool`.
///
/// The DROP-SET: a rule `R` in category `C` is a generic whole-source bind rule
/// that a sigil-quoted sibling subsumes iff (a) `R.syntax_pattern[0]` is a
/// `Param` (the whole-`source` LHS — NOT a leading literal), (b) `R` carries at
/// least one interior bind-trigger literal `T`, and (c) `C` contains a
/// SIGIL-LED sibling `R'` (`R'.syntax_pattern[0]` a `Literal`) that ALSO carries
/// `T` as an interior literal. For rholang InputBind this selects rule 7
/// `InputBind (lhs "<-" n)`, rule 8 `InputBindPersistent (lhs "<=" n)`, and
/// rule 0 `InputBindQuery (lhs "<-" n "!" "?" …)` — each subsumed by
/// InputBindQuoted / …Persistent / …Query respectively. Polyadic rules
/// (`lhs "," …`) are EXCLUDED: their bind position follows a `,` that no
/// sigil-led sibling carries, so no `R'` matches. Grammar-derived; empty ⇒
/// default `false`.
pub fn emit_sigil_quoted_bind_overgen_rule_body(
    per_cat: &[Vec<(u16, &GrammarRule)>],
) -> TokenStream {
    use mettail_ast::grammar::SyntaxExpr;
    // Per category: the set of interior literals carried by SIGIL-LED rules
    // (sp[0] == Literal). These are the bind-trigger positions a quoted sibling
    // provides.
    let mut arms: Vec<TokenStream> = Vec::new();
    for (ci, rules) in per_cat.iter().enumerate() {
        let cat_u16 = ci as u16;
        // sigil-led interior literals for THIS category.
        let mut sigil_interior: std::collections::BTreeSet<String> =
            std::collections::BTreeSet::new();
        for (_ri, rule) in rules {
            let Some(sp) = rule.syntax_pattern.as_ref() else {
                continue;
            };
            if !matches!(sp.first(), Some(SyntaxExpr::Literal(_))) {
                continue;
            }
            for (i, e) in sp.iter().enumerate() {
                if i == 0 {
                    continue;
                }
                if let SyntaxExpr::Literal(t) = e {
                    sigil_interior.insert(t.clone());
                }
            }
        }
        if sigil_interior.is_empty() {
            continue;
        }
        for (rule_idx, rule) in rules {
            let Some(sp) = rule.syntax_pattern.as_ref() else {
                continue;
            };
            // (a) whole-source: first syntax element is a Param.
            if !matches!(sp.first(), Some(SyntaxExpr::Param(_))) {
                continue;
            }
            // (b)+(c): some interior literal of R is also carried by a
            // sigil-led sibling of the same category.
            let has_shared_bind_trigger = sp.iter().enumerate().any(|(i, e)| {
                i > 0 && matches!(e, SyntaxExpr::Literal(t) if sigil_interior.contains(t))
            });
            if has_shared_bind_trigger {
                let r = *rule_idx;
                arms.push(quote! { (#cat_u16, #r) => true, });
            }
        }
    }
    if arms.is_empty() {
        quote! { false }
    } else {
        quote! {
            match (src_idx, rule_idx) {
                #(#arms)*
                _ => false,
            }
        }
    }
}

/// AT_QUOTED_BIND_GATE realize-backstop companion (option B, 2026-07-03). Emit
/// the body of `WpdaEngine::sigil_quoted_source_atom_rule(src_idx, rule_idx) ->
/// bool`.
///
/// The SIGIL-ATOM set: a rule `R` in category `S` whose `syntax_pattern[0]` is
/// a Literal `σ` that ALSO leads a sibling rule in a DIFFERENT result category
/// `C ≠ S` (so `σ` both makes `σ…` an `S` atom and directly triggers a rule in
/// `C`). For rholang this selects `NQuoteShort . p:Proc |- "@" p : Name` and
/// `NQuote . p:Proc |- "@" "(" p ")" : Name` (both `@`-led in Name, and `@`
/// also leads InputBindQuoted in InputBind). The realize backstop uses this to
/// decide whether a whole-source packing's `children[0]` is `σ`-quoted.
/// Grammar-derived; empty ⇒ default `false`.
pub fn emit_sigil_quoted_source_atom_rule_body(
    categories: &[String],
    per_cat: &[Vec<(u16, &GrammarRule)>],
    language: &LanguageDef,
) -> TokenStream {
    use mettail_ast::grammar::SyntaxExpr;
    // For each category, the leading literals of its rules (grammar-wide).
    let mut leads_by_cat: Vec<std::collections::BTreeSet<String>> =
        vec![std::collections::BTreeSet::new(); categories.len()];
    for (ci, rules) in per_cat.iter().enumerate() {
        for (_ri, rule) in rules {
            if let Some(sp) = rule.syntax_pattern.as_ref() {
                if let Some(SyntaxExpr::Literal(t)) = sp.first() {
                    leads_by_cat[ci].insert(t.clone());
                }
            }
        }
    }
    let _ = language;
    let mut arms: Vec<TokenStream> = Vec::new();
    for (ci, rules) in per_cat.iter().enumerate() {
        for (rule_idx, rule) in rules {
            let Some(sp) = rule.syntax_pattern.as_ref() else {
                continue;
            };
            let Some(SyntaxExpr::Literal(sigil)) = sp.first() else {
                continue;
            };
            // σ must lead a sibling in a DIFFERENT category.
            let leads_elsewhere = leads_by_cat
                .iter()
                .enumerate()
                .any(|(cj, leads)| cj != ci && leads.contains(sigil));
            if leads_elsewhere {
                let cat_u16 = ci as u16;
                let r = *rule_idx;
                arms.push(quote! { (#cat_u16, #r) => true, });
            }
        }
    }
    if arms.is_empty() {
        quote! { false }
    } else {
        quote! {
            match (src_idx, rule_idx) {
                #(#arms)*
                _ => false,
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
/// Whether `name` denotes a BUILTIN TOKEN CLASS rather than a declared category.
///
/// # ★ #141 — the defect this predicate exists to remove, MEASURED
///
/// A single-argument wrapper's source "category" is read off the param's declared
/// type, and that type may be a builtin token class: `Tagged . m:Ident |- "tag" m
/// : Num` (`languages/tests/ident_param_capture.rs`) and `Named . m:Ident |- …`
/// (`languages/tests/definitions/token_text_leaf_demo.rs`) both declare one.
/// `Ident` is a TOKEN KIND, not a category — the param lowers to a
/// `std::string::String` field — so such a rule captures text and coerces
/// NOTHING, and belongs in none of the three coercion tables below.
///
/// Both grammars reached the tables anyway, and the `.position(..).unwrap_or(0)`
/// lookup resolved `Ident` to index 0, THE FIRST DECLARED CATEGORY. So
/// `TokenTextLeafDemo` published a `Proc → Proc` coercion and `IdentParamToy` a
/// `Num → Num` one, each attributed to a rule that performs no coercion at all,
/// with no diagnostic anywhere. ⚠ That is the fails-open shape this campaign is
/// about, FIRING on shipped grammars — the "no grammar reaches these paths"
/// negative held only because `cargo check -p languages` does not build
/// `languages/tests/`, where both live.
///
/// Refusing them would be wrong (the grammars are correct); resolving them would
/// be wrong (there is no category to resolve). The honest answer is that they are
/// NOT COERCIONS, so they are excluded here — the same treatment
/// `infix::emit_mixfix_parts_fn` gives a capture part, which "legitimately names
/// a non-category (`Ident`)" and takes the `MIXFIX_PART_NO_OPERAND` poison rather
/// than the lookup.
fn is_builtin_token_class(name: &str) -> bool {
    mettail_ast::grammar::NonTerminalKind::classify(name).is_builtin()
}

/// The refusal body for a coercion table that could not resolve a category, or
/// `None` when there is nothing to refuse.
///
/// # Why the three tables share this and why it is shaped as an early return
///
/// `emit_single_hop_coercion_body`, `emit_trigger_unary_wrappers_into_body` and
/// `emit_prefix_cast_into_body` each build a `BTreeMap` keyed on a resolved
/// SOURCE category and then render it as a `match` EXPRESSION. There is no slot
/// in a `match` expression to hang a diagnostic on, so the refusal replaces the
/// whole body — a block whose `compile_error!`s fire at expansion and whose
/// `fallback` keeps the emitted body parseable in the position it occupies.
///
/// ⚠ It is an EARLY RETURN, taken only when `refusals` is non-empty, precisely so
/// the successful body is emitted byte-for-byte as before. A helper that always
/// wrapped the body in a block would move every generated file for every
/// language, which is the opposite of what a refusal-path repair may do.
fn coercion_table_refusal(
    refusals: &[TokenStream],
    fallback: TokenStream,
) -> Option<TokenStream> {
    match refusals.is_empty() {
        true => None,
        false => Some(quote! {
            {
                #(#refusals;)*
                #fallback
            }
        }),
    }
}

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
    let mut refusals: Vec<TokenStream> = Vec::new();
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
            // ★ #141 — a builtin token class is not a coercion source at all; see
            // `is_builtin_token_class`.
            if is_builtin_token_class(&source_cat_name) {
                continue;
            }
            // ★ #141 — sibling 4 of 7. `.unwrap_or(0)` here made an undeclared
            // SOURCE category key the table at index 0, the first declared
            // category, so `single_hop_coercion(0, to)` reported a coercion the
            // grammar never declared — and, worse, could collide with a real
            // entry for category 0. See `coercion_table_refusal`.
            let from_cat = match super::binder::resolve_cat_idx(
                &source_cat_name,
                categories,
                "a single-hop coercion's source position",
                &rule.label.to_string(),
            ) {
                Ok(idx) => idx,
                Err(unresolved) => {
                    refusals.push(unresolved.compile_error(rule.label.span()));
                    continue;
                },
            };
            table.entry((from_cat, to_cat)).or_default().push(*rule_idx);
        }
    }
    if let Some(refusal) = coercion_table_refusal(&refusals, quote! { &[] }) {
        return refusal;
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

/// S1-FACTORING F0 (2026-07-11): `pub(crate)` so the A2 cast-machinery
/// eligibility exclusion (`numeric_cast_adapter::cast_machinery_participates`,
/// consumed by `wpda_codegen::factoring`) keys off the SAME source data that
/// feeds `emit_trigger_unary_wrappers_into_body` / `emit_prefix_cast_into_body`
/// / `emit_prefix_cast_keyword_body` — the tables the walker's
/// `trigger_unary_wrapper_rule_matches` parking gate consults. Visibility-only
/// change; emission is untouched.
pub(crate) fn trigger_unary_wrapper_source_cat(rule: &GrammarRule) -> Option<String> {
    use mettail_ast::grammar::{SyntaxExpr, TermParam};
    use mettail_ast::types::TypeExpr;

    let tc = rule.term_context.as_ref()?;
    if tc.len() != 1 {
        return None;
    }
    let TermParam::Simple { name: param_name, ty } = &tc[0] else {
        return None;
    };
    let TypeExpr::Base(source_ident) = ty else {
        return None;
    };
    let sp = rule.syntax_pattern.as_ref()?;
    if !matches!(sp.first(), Some(SyntaxExpr::Literal(_))) {
        return None;
    }
    let refs_param = sp
        .iter()
        .any(|e| matches!(e, SyntaxExpr::Param(syn_name) if syn_name == param_name));
    let is_lone_param = sp.len() == 1
        && matches!(
            sp.first(),
            Some(SyntaxExpr::Param(syn_name)) if syn_name == param_name
        );
    if refs_param && !is_lone_param {
        Some(source_ident.to_string())
    } else {
        None
    }
}

/// RC-B (2026-06-19): emit the body of
/// `WpdaEngine::trigger_unary_wrappers_into(from_cat, to_cat) -> &'static [u16]`.
///
/// This all-candidates table covers every single-argument leading-literal
/// wrapper, including same-category wrappers such as `float(<Float>)` and
/// `sin(<Float>)`. The walker filters by keyword and action evidence instead
/// of using source order as a disambiguator.
pub fn emit_trigger_unary_wrappers_into_body(
    categories: &[String],
    per_cat: &[Vec<(u16, &GrammarRule)>],
) -> TokenStream {
    let mut table: std::collections::BTreeMap<(u16, u16), Vec<u16>> =
        std::collections::BTreeMap::new();
    let mut refusals: Vec<TokenStream> = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let to_cat = cat_i as u16;
        for (rule_idx, rule) in rules {
            let Some(source_cat_name) = trigger_unary_wrapper_source_cat(rule) else {
                continue;
            };
            // ★ #141 — see `is_builtin_token_class`: `TokenTextLeafDemo::Named`
            // and `IdentParamToy::Tagged` both reach here with `Ident`, and both
            // were silently entering this table at category 0.
            if is_builtin_token_class(&source_cat_name) {
                continue;
            }
            // ★ #141 — sibling 5 of 7. See `coercion_table_refusal`.
            let from_cat = match super::binder::resolve_cat_idx(
                &source_cat_name,
                categories,
                "a trigger-unary wrapper's source position",
                &rule.label.to_string(),
            ) {
                Ok(idx) => idx,
                Err(unresolved) => {
                    refusals.push(unresolved.compile_error(rule.label.span()));
                    continue;
                },
            };
            table.entry((from_cat, to_cat)).or_default().push(*rule_idx);
        }
    }
    if let Some(refusal) = coercion_table_refusal(&refusals, quote! { &[] }) {
        return refusal;
    }
    if table.is_empty() {
        return quote! { &[] };
    }
    let mut arms: Vec<TokenStream> = Vec::with_capacity(table.len());
    for ((from_cat, to_cat), rule_idxs) in table {
        let rules: Vec<TokenStream> = rule_idxs.iter().map(|ri| quote! { #ri }).collect();
        arms.push(quote! {
            (#from_cat, #to_cat) => &[#(#rules),*],
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
    // `(from_cat, to_cat) -> rule_idx` (first match wins per pair).
    let mut table: std::collections::BTreeMap<(u16, u16), u16> = std::collections::BTreeMap::new();
    let mut refusals: Vec<TokenStream> = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let to_cat = cat_i as u16;
        for (rule_idx, rule) in rules {
            let Some(source_cat_name) = trigger_unary_wrapper_source_cat(rule) else {
                continue;
            };
            if source_cat_name == rule.category.to_string() {
                continue;
            }
            // ★ #141 — see `is_builtin_token_class`. This table's `or_insert` made
            // the same two grammars' `Ident` rows WORSE than spurious: first write
            // wins, so a `(0, to)` row invented for a token-text capture could
            // SUPPRESS a real cast out of category 0.
            if is_builtin_token_class(&source_cat_name) {
                continue;
            }
            // ★ #141 — sibling 6 of 7. See `coercion_table_refusal`. This table
            // uses `or_insert`, so a `.unwrap_or(0)` collision did not merely add
            // a spurious row: it could SUPPRESS the real `(0, to_cat)` cast,
            // because first-write-wins.
            let from_cat = match super::binder::resolve_cat_idx(
                &source_cat_name,
                categories,
                "a prefix cast's source position",
                &rule.label.to_string(),
            ) {
                Ok(idx) => idx,
                Err(unresolved) => {
                    refusals.push(unresolved.compile_error(rule.label.span()));
                    continue;
                },
            };
            table.entry((from_cat, to_cat)).or_insert(*rule_idx);
        }
    }
    if let Some(refusal) = coercion_table_refusal(&refusals, quote! { None }) {
        return refusal;
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
    use mettail_ast::grammar::SyntaxExpr;
    // `(to_cat, rule_idx) -> keyword` for every trigger-bearing prefix cast.
    let mut table: std::collections::BTreeMap<(u16, u16), String> =
        std::collections::BTreeMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let to_cat = cat_i as u16;
        for (rule_idx, rule) in rules {
            if trigger_unary_wrapper_source_cat(rule).is_none() {
                continue;
            }
            let Some(sp) = rule.syntax_pattern.as_ref() else {
                continue;
            };
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
/// rholang has `Err . |- "error" : Proc`. Pattern is grammar-determined.
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

/// `rule_label` / `rule_span` identify the rule whose action entry this is, and
/// exist for the same reason `emit_binder_action_entry`'s `rule_span` does: the
/// cross-category shapes below resolve a SOURCE category, and a category that
/// cannot be resolved must refuse AT THE RULE rather than at the whole
/// `language!` invocation.
#[allow(clippy::too_many_arguments)]
fn emit_action_entry_arm(
    src_idx: u16,
    rule_idx: u16,
    shape: &AtomicShape,
    cat_ident: &Ident,
    refinement_name: Option<&str>,
    categories: &[String],
    language: &LanguageDef,
    rule_label: &str,
    rule_span: proc_macro2::Span,
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
        // GAP-3 (2026-06-28): 0-operand multi-literal keyword-prefix rule
        // (`Map ()`, `Pathmap ()`, `@ Nil`). REUSE the TerminalKeyword action
        // body verbatim — it ignores its `_args` and builds the nullary VARIANT
        // `Cat::<wrapper_variant>` (e.g. `Proc::MapEmpty`, NOT the container;
        // the `fold`, if any, materializes the container at eval time). The
        // trigger reaches the SPPF as a `TriggerTerminal`, which the runtime
        // FILTERS before counting children, so the marker-pop fire sees
        // `action_children.len() == 0`. Arity MUST therefore be 0 (the walker's
        // `debug_assert_eq!(action_entry.arity, action_children.len())` fires
        // otherwise) and there are no input-category slots.
        AtomicShape::NullaryLiteralRun { wrapper_variant, .. } => {
            (emit_terminal_keyword_action(cat_ident, wrapper_variant), 0u8, quote! { &[] })
        },
        AtomicShape::VarRule { wrapper_variant } => {
            (emit_var_rule_action(cat_ident, wrapper_variant), 1u8, quote! { &[#any_cat] })
        },
        // Stage 1.1: cross-cat wrap-action — pop 1 source-cat Term arg,
        // wrap as Cat::wrapper_variant(Box::new(arg)).
        AtomicShape::CrossCatProjection { source_cat_name, wrapper_variant }
        | AtomicShape::CrossCatPrefixUnary { source_cat_name, wrapper_variant, .. } => {
            // ★ #141 — sibling 7 of 7, and the only one of the seven already in a
            // TOKEN position: the index is interpolated straight into
            // `expected_input_cats: &[…]`. `.unwrap_or(0)` here is the SAME defect
            // `binder::emit_binder_action_entry`'s `lookup_cat_idx` had (#141 G2) —
            // the action advertised a source category the rule never named, and the
            // arg-shape gate then rejected readings whose parse was correct. Takes
            // the shared resolver's token form.
            let source_src_idx = super::binder::cat_idx_tokens(
                source_cat_name,
                categories,
                "a cross-category projection's source position",
                rule_label,
                rule_span,
            );
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
                // `as Set` (Rholang 1.4 / main) carries a `HashSetLit` payload (see
                // rholang `![mettail_runtime::HashSetLit<Proc>] as Set`); build the
                // deterministic wrapper, not `std::collections::HashSet`.
                let container = mettail_runtime::HashSetLit::<#element_cat_ident>::from_iter(
                    drained
                        .into_iter()
                        .filter_map(|a| a.into_term::<#element_cat_ident>())
                );
                b.push_term::<#cat_ident>(#cat_ident::#label_ident(container));
            }
        },
        CollectionType::PathMap => quote! {
            |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
             args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
                let id = match args.into_iter().next().and_then(|a| a.as_collection_id()) {
                    Some(id) => id,
                    None => return,
                };
                let drained = b.drain_collection(id);
                // PathMap elements are flattened key/value pairs in drain order
                // [k0, v0, k1, v1, ...] (same as HashMap); insert into a PathMapLit
                // (the wrapper that `Pathmap::PathmapLit(...)` accepts — see
                // runtime/src/pathmap_lit.rs; it derefs to HashMapLit for `insert`).
                let mut iter = drained.into_iter();
                let mut container = mettail_runtime::PathMapLit::<
                    #element_cat_ident, #element_cat_ident,
                >::new();
                while let Some(k_arg) = iter.next() {
                    match iter.next() {
                        Some(v_arg) => {
                            if let (Some(k), Some(v)) = (
                                k_arg.into_term::<#element_cat_ident>(),
                                v_arg.into_term::<#element_cat_ident>(),
                            ) {
                                container.insert(k, v);
                            }
                        },
                        None => {
                            // Pathmap optional-value (2026-06-27): a trailing
                            // UNPAIRED key is a bare path `{| k |}` whose value
                            // is the key itself (set-form: value = key). The
                            // parser duplicates bare-path keys at parse time
                            // (DuplicateLastCollectionElement) so even-length
                            // pairs are the norm; this odd-tail arm is the
                            // defensive net that still materializes a correct
                            // `k → k` entry rather than dropping the key.
                            if let Some(k) = k_arg.into_term::<#element_cat_ident>() {
                                container.insert(k.clone(), k);
                            }
                        },
                    }
                }
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
///
/// `rule_span` is the offending rule's LABEL span, threaded from the single
/// caller ([`emit_action_for_body`], which holds the `GrammarRule`). `cat_ident`
/// cannot serve: it is a `format_ident!` of the category NAME, so its span is
/// the call site, and a `quote_spanned!` on it would be `quote!` wearing a
/// longer name.
fn emit_infix_action_entry(
    src_idx: u16,
    rule_idx: u16,
    info: &InfixRuleInfo,
    cat_ident: &Ident,
    categories: &[String],
    rule_span: proc_macro2::Span,
) -> Option<TokenStream> {
    // GEN-1 B-3 (Stage S3): a mixfix rule MAY carry a `*sep` repetition part
    // (POutput2Plus `… bs.*sep(",") …`, InputBind* polyadic/query binds). Its
    // field is a `Vec<elem>` built by DRAINING the `ActionArg::CollectionId` that
    // the walker left in the marker's args (the rep slot's CollectionMarker pop is
    // FireAction-suppressed via `is_binder_internal_collection`), NOT by
    // `into_term_arc`. The per-arg emission below special-cases the rep parts
    // (drain) vs ordinary parts (`into_term_arc`). Mirrors
    // `emit_collection_action_entry`'s Vec drain. (At Stage S2 this returned
    // `None` because the walker erred at the inert rep slot before the marker
    // popped; S3 wires both the walker handoff and this drain-aware action.)
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
    //
    // ★ #141 G2 — THIS CLOSURE USED TO END IN `.unwrap_or(0)`, and the incident
    // report is the `capture_kind` arm twenty lines below: `Ident` is not in
    // `categories`, so it resolved to index 0 — the FIRST declared category —
    // the language COMPILED, and the only thing the user saw was "no accepting
    // branch reached end of input" with nothing naming `Ident`. #131 closed ONE
    // door into that default (`capture_kind.is_some()`); the default itself
    // stayed open, here and in `binder::emit_binder_action_entry`, and the #133
    // sweep hardened two other siblings without reaching either. It now refuses
    // through the shared resolver, which substitutes a spanned `compile_error!`
    // exactly where the wrong index would have gone.
    let lookup_cat_idx = |name: &str| -> TokenStream {
        cat_idx_tokens(
            name,
            categories,
            "an infix/postfix/mixfix rule's action entry",
            &info.label,
            rule_span,
        )
    };
    let operand_cat_idx = lookup_cat_idx(&info.category);
    let result_cat_idx = lookup_cat_idx(&info.result_category);
    let any_cat_value: u16 = u16::MAX;
    let expected_input_cats: Vec<TokenStream> = if info.is_postfix {
        vec![operand_cat_idx]
    } else if info.is_mixfix {
        let mut v = vec![operand_cat_idx.clone()];
        for part in &info.mixfix_parts {
            // GEN-1 B-3 (Stage S3): a `*sep` repetition part's arg is an
            // `ActionArg::CollectionId` (not a Term), so its expected category is
            // ANY_CAT (u16::MAX) — mirroring the binder/collection drain args.
            if part.repetition.is_some() {
                v.push(quote! { #any_cat_value });
            } else if part.capture_kind.is_some() {
                // ★ A CAPTURE part's arg is token TEXT, not a Term, so — exactly like the
                // `*sep` repetition arg above — its expected category is ANY_CAT.
                //
                // #131: keyed on `capture_kind`, which is the ONE place a part is decided
                // to be a capture (`capture_kind_of` in `infix.rs`). It previously
                // re-derived that from `operand_category`, which meant the classifier and
                // the action entry could disagree about what a part IS while both
                // compiled — the arg-shape gate would then reject every reading of a rule
                // whose parse was otherwise correct.
                //
                // ⚠ WITHOUT THIS THE RULE CANNOT PARSE AT ALL, and the reason WAS a silent
                // default: `lookup_cat_idx` ended in `.unwrap_or(0)`, and `Ident` is not in
                // `categories`, so it resolved to index 0 — the FIRST declared category.
                // The action entry then advertised "slot 1 expects a `Num` term" while the
                // extractor at that slot read `as_ident()`. The arg-shape gate rejected
                // every reading, surfacing as "no accepting branch reached end of input"
                // with nothing naming `Ident` anywhere in the diagnostic.
                //
                // ★ #141 G2: the default is gone — `lookup_cat_idx` now REFUSES. This arm
                // stays exactly as #131 wrote it: a capture part's expected category is
                // genuinely ANY_CAT, so it must not consult the resolver at all. The arm is
                // a positive statement about capture parts, not a way around a bad lookup.
                v.push(quote! { #any_cat_value });
            } else {
                v.push(lookup_cat_idx(&part.operand_category));
            }
        }
        v
    } else {
        vec![operand_cat_idx.clone(), operand_cat_idx]
    };
    // #141 G2: `expected_input_cats` now holds the emitted tokens directly —
    // either a `u16` literal or the `compile_error!` that refuses in its place.
    let expected_input_cats_ts = quote! { &[#(#expected_input_cats),*] };
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
                // arg0 is the LHS (info.category); args 1..N correspond to
                // mixfix_parts[i-1] in term_context (= constructor) order.
                let part = if i == 0 {
                    None
                } else {
                    Some(&info.mixfix_parts[i - 1])
                };
                // GEN-1 B-3 (Stage S3): a repetition part's arg is an
                // `ActionArg::CollectionId`; drain it into `Vec<elem>` (the AST
                // field type for a `*sep` collection param — all shipped rep params
                // are `Vec`). Mirrors `emit_collection_action_entry`'s Vec drain.
                if let Some(p) = part {
                    if p.repetition.is_some() {
                        let elem = format_ident!("{}", p.operand_category);
                        return quote! {
                            let #var: std::vec::Vec<#elem> = {
                                let __id = match iter.next().and_then(|a| a.as_collection_id()) {
                                    Some(__id) => __id,
                                    None => return,
                                };
                                b.drain_collection(__id)
                                    .into_iter()
                                    .filter_map(|a| a.into_term::<#elem>())
                                    .collect()
                            };
                        };
                    }
                }
                // ★ #131: a CAPTURE part's arg is token TEXT, not a Term of some
                // category named `Ident`. `into_term_arc::<Ident>()` would name a type
                // that does not exist AND could never match this arg shape.
                //
                // ⚠ THE ACCESSOR ORDER IS LOAD-BEARING AND WAS MEASURED, NOT ASSUMED.
                // Which `ActionArg` variant arrives depends on the SPPF terminal's
                // `pushed_via_push_ident` discriminator, NOT on its `TokenKind`
                // (`wpda_walker.rs` realize: `emit_push_ident` ⇒ `ActionArg::Ident`,
                // `emit_push_token` ⇒ `ActionArg::Token` EVEN WHEN the kind is `Ident`).
                // The mixfix capture is driven by `GuardedConsumeTokenKindAndReplace`,
                // which interns with `pushed_via_push_ident = false` — so it delivers
                // `ActionArg::Token { kind: Ident, .. }` and `as_ident()` alone returns
                // `None`. Reading only `as_ident()` here would make every reading of the
                // rule unrealizable while every symbol involved still existed and
                // compiled: precisely the "a symbol exists, therefore the path works"
                // inference that cost this task two rounds.
                //
                // Both accessors are read because both origins are legitimate — the
                // binder path's `ConsumeIdentAndReplace` interns with the discriminator
                // TRUE and yields `ActionArg::Ident`. What is NOT done is defaulting:
                // when neither accessor yields text the action `return`s, killing the
                // reading, because a blank name once built a well-formed term with an
                // empty field and survived a full build, a green type-check and eight
                // walkers before a fixture caught it.
                if let Some(p) = part {
                    if p.capture_kind.is_some() {
                        return quote! {
                            let #var: std::string::String = {
                                let __arg = match iter.next() {
                                    Some(__a) => __a,
                                    None => return,
                                };
                                match __arg.as_ident() {
                                    Some(__s) => __s.to_string(),
                                    None => match __arg.as_token_text() {
                                        Some(__s) => __s.to_string(),
                                        None => return,
                                    },
                                }
                            };
                        };
                    }
                }
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


// ═══════════════════════════════════════════════════════════════════════════
// #141 Part B RED — the SEVEN `.unwrap_or(0)` siblings, at the three coercion
// tables that carry four of them
// ═══════════════════════════════════════════════════════════════════════════
//
// All three tables keyed a `BTreeMap` on a SOURCE category resolved with
// `.position(..).unwrap_or(0)`. An undeclared source silently became index 0 —
// the FIRST declared category — and the language COMPILED, advertising a coercion
// the grammar never declared. `emit_prefix_cast_into_body` is worse still: it
// keys with `or_insert`, so the spurious `(0, to)` row could SUPPRESS the real
// cast out of category 0 by winning the first write.
//
// ⚠ No cell here expects a panic: each reads the tokens the emitter returns.
#[cfg(test)]
mod sibling_refusal_red {
    use super::*;
    use mettail_ast::grammar::{rule_fixture, GrammarRule, SyntaxExpr, TermParam};
    use mettail_ast::types::TypeExpr;
    use proc_macro2::Span;
    use syn::Ident;

    fn id(name: &str) -> Ident {
        Ident::new(name, Span::call_site())
    }

    /// A trigger-bearing unary cast `Cast<Source> . v:<source> |- "cast" v : Wrapped`.
    ///
    /// `source` is the ONLY thing the two fixtures below differ in, and it is what
    /// `trigger_unary_wrapper_source_cat` reads, so it is exactly the input the
    /// three tables resolve.
    fn cast_rule(source: &str) -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![TermParam::Simple {
                name: id("v"),
                ty: TypeExpr::Base(id(source)),
            }]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("cast".to_string()),
                SyntaxExpr::Param(id("v")),
            ]),
            ..rule_fixture(id("CastFromSource"), id("Wrapped"))
        }
    }

    /// A SPAN-TRANSPARENT projection `CastFromSource . v:<source> |- v : Wrapped`.
    ///
    /// `emit_single_hop_coercion_body` admits only this shape (`sp.len() == 1`,
    /// the lone element the param) — the trigger-bearing twin above is its exact
    /// COMPLEMENT and is what the other two tables read. Both are needed, or one
    /// of the three cells below would range over an empty table.
    fn projection_rule(source: &str) -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![TermParam::Simple {
                name: id("v"),
                ty: TypeExpr::Base(id(source)),
            }]),
            syntax_pattern: Some(vec![SyntaxExpr::Param(id("v"))]),
            ..rule_fixture(id("CastFromSource"), id("Wrapped"))
        }
    }

    fn declared_categories() -> Vec<String> {
        vec!["Wrapped".to_string(), "Real".to_string()]
    }

    /// The three emitters, by name, each over the rule SHAPE it admits.
    fn render(source: &str) -> Vec<(&'static str, String)> {
        let categories = declared_categories();
        let projection = vec![vec![(0u16, projection_rule(source))]];
        let cast = vec![vec![(0u16, cast_rule(source))]];
        let borrow = |owned: &Vec<Vec<(u16, GrammarRule)>>| -> Vec<Vec<(u16, GrammarRule)>> {
            owned.clone()
        };
        let projection = borrow(&projection);
        let cast = borrow(&cast);
        let projection_ref: Vec<Vec<(u16, &GrammarRule)>> = projection
            .iter()
            .map(|rules| rules.iter().map(|(i, r)| (*i, r)).collect())
            .collect();
        let cast_ref: Vec<Vec<(u16, &GrammarRule)>> = cast
            .iter()
            .map(|rules| rules.iter().map(|(i, r)| (*i, r)).collect())
            .collect();
        let language = crate::gen::empty_language_for_tests();
        vec![
            (
                "single_hop_coercion",
                emit_single_hop_coercion_body(&categories, &projection_ref, &language).to_string(),
            ),
            (
                "trigger_unary_wrappers_into",
                emit_trigger_unary_wrappers_into_body(&categories, &cast_ref).to_string(),
            ),
            (
                "prefix_cast_into",
                emit_prefix_cast_into_body(&categories, &cast_ref).to_string(),
            ),
        ]
    }

    /// ★ THE MUTATION CELL. An UNDECLARED source category refuses, in every table
    /// that reads one, and the diagnostic names the category and the rule.
    #[test]
    fn an_undeclared_source_category_refuses_in_every_coercion_table() {
        // The mutation really is applied, and is the only difference: the two
        // fixtures agree on everything but the source category's spelling.
        let mutated = cast_rule("Ghost");
        let control = cast_rule("Real");
        assert_eq!(mutated.label, control.label, "same rule, one token apart");
        assert_ne!(
            format!("{:?}", mutated.term_context),
            format!("{:?}", control.term_context),
            "and the token they differ in is the SOURCE CATEGORY, which is what \
             these tables resolve",
        );

        for (table, rendered) in render("Ghost") {
            assert!(
                rendered.contains("compile_error"),
                "`{table}` must REFUSE an undeclared source category, not resolve it to \
                 index 0 — the first declared category — and emit a table row for a \
                 coercion the grammar never declared. Got: {rendered}",
            );
            assert!(
                rendered.contains("Ghost"),
                "`{table}`'s diagnostic must name the CATEGORY it could not resolve. \
                 Got: {rendered}",
            );
            assert!(
                rendered.contains("CastFromSource"),
                "`{table}`'s diagnostic must name the RULE the category appears on — an \
                 index names nothing an author can act on. Got: {rendered}",
            );
            assert!(
                rendered.contains("Wrapped , Real") || rendered.contains("Wrapped, Real"),
                "`{table}`'s diagnostic must list the DECLARED categories, because the \
                 single most common cause is a typo. Got: {rendered}",
            );
        }
    }

    /// ★ THE CONTROL that must NOT discriminate: a DECLARED source still builds
    /// its row, and emits no diagnostic at all.
    #[test]
    fn a_declared_source_category_still_builds_its_row() {
        for (table, rendered) in render("Real") {
            assert!(
                !rendered.contains("compile_error"),
                "`{table}` must not refuse a source category the language declares — \
                 otherwise the cell above proves only that these emitters refuse \
                 everything. Got: {rendered}",
            );
            assert!(
                rendered.contains("match"),
                "`{table}` must still emit its lookup `match` for a resolvable cast. \
                 Got: {rendered}",
            );
        }
    }

    /// ★ THE MEASURED FINDING (2026-07-29). A source that is a BUILTIN TOKEN
    /// CLASS is not a coercion at all — it neither refuses nor enters the table.
    ///
    /// This is not a hypothetical: `Tagged . m:Ident |- "tag" m : Num`
    /// (`languages/tests/ident_param_capture.rs`) and `Named . m:Ident |- …`
    /// (`languages/tests/definitions/token_text_leaf_demo.rs`) are shipped
    /// grammars that reach these tables, and `.unwrap_or(0)` was silently
    /// publishing a `Num → Num` / `Proc → Proc` coercion for each. The cell below
    /// is a fixture of exactly that shape.
    #[test]
    fn an_ident_source_is_not_a_coercion_and_neither_refuses_nor_enters_the_table() {
        for (table, rendered) in render("Ident") {
            assert!(
                !rendered.contains("compile_error"),
                "`{table}` must not REFUSE `m:Ident`: the grammars that write it are \
                 correct — `Ident` is a token kind whose param lowers to a `String`, so \
                 the rule captures text and coerces nothing. Got: {rendered}",
            );
            assert!(
                !rendered.contains("0u16 , 0u16") && !rendered.contains("(0u16, 0u16)"),
                "…and it must not resolve `Ident` to category 0 either, which is what \
                 `.unwrap_or(0)` did — publishing a coercion out of THE FIRST DECLARED \
                 CATEGORY for a rule that performs none. Got: {rendered}",
            );
        }
    }

    /// ANTI-VACUITY for the cell above: `Ident` really is classified as a builtin,
    /// and `Real` really is not. Without this, the exclusion could be matching
    /// nothing (or everything) and both halves would pass.
    #[test]
    fn the_builtin_token_class_predicate_separates_ident_from_a_real_category() {
        assert!(
            is_builtin_token_class("Ident"),
            "`Ident` is a builtin token kind, which is what excludes it",
        );
        assert!(
            !is_builtin_token_class("Real"),
            "…and a declared category is not, which is what keeps the exclusion from \
             swallowing every coercion in the corpus",
        );
    }

    /// ANTI-VACUITY: the fixture really does reach the resolving code. If
    /// `trigger_unary_wrapper_source_cat` stopped recognising this shape, every
    /// assertion above would range over an empty table and pass for the wrong
    /// reason.
    #[test]
    fn the_fixture_reaches_the_source_category_lookup() {
        assert_eq!(
            trigger_unary_wrapper_source_cat(&cast_rule("Real")).as_deref(),
            Some("Real"),
            "the fixture must be classified as a trigger-bearing unary wrapper, or the \
             cells above never reach the lookup they are about",
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::{rule_fixture, GrammarItem, NonTerminalKind};
    use mettail_ast::language::{LangType, TokenDef};
    use proc_macro2::Span;
    use syn::{parse_quote, Ident};

    fn rule(label: &str, cat: &str, kind: NonTerminalKind) -> GrammarRule {
        GrammarRule {
            items: vec![GrammarItem::NonTerminal {
                ident: Ident::new(&format!("{:?}", kind), Span::call_site()),
                kind,
            }],
            ..rule_fixture(Ident::new(label, Span::call_site()), Ident::new(cat, Span::call_site()))
        }
    }

    fn terminal_rule(label: &str, cat: &str, text: &str) -> GrammarRule {
        GrammarRule {
            items: vec![GrammarItem::Terminal(text.into())],
            ..rule_fixture(Ident::new(label, Span::call_site()), Ident::new(cat, Span::call_site()))
        }
    }

    fn category_rule(label: &str, cat: &str, referenced_cat: &str) -> GrammarRule {
        GrammarRule {
            items: vec![GrammarItem::NonTerminal {
                ident: Ident::new(referenced_cat, Span::call_site()),
                kind: NonTerminalKind::Category,
            }],
            ..rule_fixture(Ident::new(label, Span::call_site()), Ident::new(cat, Span::call_site()))
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

    // ═══════════════════════════════════════════════════════════════════════
    // Task #141 G2 / RED-2 — the fails-open category lookup
    // ═══════════════════════════════════════════════════════════════════════
    //
    // ## What the mutation is, and why it is applied HERE and not to a grammar
    //
    // The defect: `emit_infix_action_entry`'s `lookup_cat_idx` ended in
    // `.unwrap_or(0)`, so a category name absent from `categories` became index
    // 0 — THE FIRST DECLARED CATEGORY — and the language COMPILED, shipping a
    // parser whose `expected_input_cats` and `output_cat` named the wrong
    // category. That is the one shape in this campaign whose "before" state is a
    // SUCCESSFUL BUILD producing a wrong parser.
    //
    // ⚠ The mutation cannot be written as a grammar. Measured 2026-07-29, both
    // by construction and by build:
    //
    // * `collect_category_names_with_literals`'s **Pass 5** (`wpda_codegen/mod.rs`)
    //   adds "any remaining user-declared `LangType` not covered above", so
    //   `categories` is TOTAL over `language.types`. A declared category is
    //   therefore always resolvable. (Measured: a fixture declaring a rule-less
    //   `Ghost` still emitted `WPDA_CATEGORIES = ["Term", "Ghost"]`.)
    // * An UNdeclared category is rejected earlier, by `validate_language`:
    //   `Rule 'Sel' references category 'Ghost' which is not exported`. (Measured
    //   on the same fixture with `Ghost` removed from `types { }`.)
    //
    // So the only inputs that reach the default are category names a CLASSIFIER
    // synthesises that are not declared types — `Ident` being the measured one
    // (task #131, whose incident report is the `capture_kind` arm of
    // `emit_infix_action_entry`). #131 closed that ONE door; the default behind it
    // stayed open, which is precisely why it must become a refusal: the next
    // classifier change re-opens a door, and a backstop that answers "category 0"
    // converts a diagnosable macro bug into an undiagnosable parser bug.
    //
    // The mutation is therefore applied at the emitter — the only layer at which
    // it IS applicable — and every cell decides on EMITTED TEXT. No cell expects a
    // panic; none exists to expect.
    //
    // ## Anti-vacuity
    //
    // Four cells: the mutation-applied check (the two category lists differ in
    // exactly the referenced name), the mutation (refuses, naming category AND
    // rule), the control (same call, category present ⇒ index emitted, NO
    // refusal), and the twin at `binder::emit_binder_action_entry`
    // (`binder.rs`'s own `mod tests`), so a repair to one site cannot pass for
    // both.

    /// The category the fixture rule's operands are declared in. Absent from
    /// [`RED2_CATEGORIES_MUTATION`], present in [`RED2_CATEGORIES_CONTROL`] —
    /// that difference IS the mutation.
    const RED2_REFERENCED_CATEGORY: &str = "Ghost";
    /// The fixture rule's label. The refusal must name it: a message that names
    /// `rule 7` names nothing a grammar author can act on.
    const RED2_RULE_LABEL: &str = "SelectGhost";
    const RED2_CATEGORIES_MUTATION: &[&str] = &["Term"];
    const RED2_CATEGORIES_CONTROL: &[&str] = &["Term", "Ghost"];

    fn red2_categories(names: &[&str]) -> Vec<String> {
        names.iter().map(|n| (*n).to_string()).collect()
    }

    /// A binary infix rule whose OPERAND category is `RED2_REFERENCED_CATEGORY`
    /// and whose result category is declared — so exactly one lookup can fail,
    /// and the cells below can attribute the refusal to it.
    fn red2_infix_info() -> InfixRuleInfo {
        InfixRuleInfo {
            label: RED2_RULE_LABEL.to_string(),
            terminal: "?".to_string(),
            category: RED2_REFERENCED_CATEGORY.to_string(),
            result_category: "Term".to_string(),
            associativity: mettail_prattail::binding_power::Associativity::Left,
            shares_level_with_previous: false,
            is_cross_category: true,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: Vec::new(),
            nullary_literals: Vec::new(),
        }
    }

    fn red2_emit(categories: &[&str]) -> String {
        emit_infix_action_entry(
            0u16,
            0u16,
            &red2_infix_info(),
            &Ident::new("Term", Span::call_site()),
            &red2_categories(categories),
            Span::call_site(),
        )
        .expect("the fixture rule must yield an action entry in BOTH arms; a `None` here \
                 would make the mutation and the control agree vacuously")
        .to_string()
    }

    /// The mutation is REALLY applied: the two category lists differ in exactly
    /// the name the fixture rule references, and in nothing else. Without this a
    /// fixture that quietly stopped exercising the lookup would pass forever.
    #[test]
    fn the_red2_mutation_is_applied() {
        let missing: Vec<&&str> = RED2_CATEGORIES_CONTROL
            .iter()
            .filter(|c| !RED2_CATEGORIES_MUTATION.contains(c))
            .collect();
        assert_eq!(
            missing,
            vec![&RED2_REFERENCED_CATEGORY],
            "control minus mutation must be exactly the referenced category",
        );
        assert!(
            RED2_CATEGORIES_MUTATION
                .iter()
                .all(|c| RED2_CATEGORIES_CONTROL.contains(c)),
            "the mutation must REMOVE a category, never add or rename one",
        );
        assert_eq!(
            red2_infix_info().category,
            RED2_REFERENCED_CATEGORY,
            "the fixture rule must actually reference the removed category",
        );
    }

    /// MUTATION. The category is unresolvable ⇒ the emitter refuses, and the
    /// refusal NAMES the category and the rule. A refusal that said only
    /// "unresolvable category" would be the vacuous form this cell exists to
    /// reject.
    #[test]
    fn unresolved_operand_category_refuses_naming_the_category_and_the_rule() {
        let emitted = red2_emit(RED2_CATEGORIES_MUTATION);
        assert!(
            emitted.contains("compile_error"),
            "an unresolvable category must emit `compile_error!`, not an index. Got: {emitted}",
        );
        assert!(
            emitted.contains(RED2_REFERENCED_CATEGORY),
            "the refusal must NAME the unresolvable category `{RED2_REFERENCED_CATEGORY}`. \
             Got: {emitted}",
        );
        assert!(
            emitted.contains(RED2_RULE_LABEL),
            "the refusal must NAME the rule `{RED2_RULE_LABEL}` — not its index. Got: {emitted}",
        );
    }

    /// CONTROL. The same call with the category present emits the index and does
    /// NOT refuse — so the mutation's refusal is attributable to the missing
    /// category and not to the fixture being malformed.
    #[test]
    fn resolved_operand_category_emits_the_index_and_does_not_refuse() {
        let emitted = red2_emit(RED2_CATEGORIES_CONTROL);
        assert!(
            !emitted.contains("compile_error"),
            "a resolvable category must NOT refuse. Got: {emitted}",
        );
        assert!(
            emitted.contains("1u16"),
            "`Ghost` is index 1 of {RED2_CATEGORIES_CONTROL:?}, so the entry must carry `1u16`. \
             Got: {emitted}",
        );
    }
}
