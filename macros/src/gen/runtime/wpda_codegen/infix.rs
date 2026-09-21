//! Phase A.3 (merged with A.4): Pratt rule shapes + cross-cat dispatch.
//!
//! Classifies rules from `language.terms` into infix / prefix / postfix /
//! mixfix shapes by inspecting the judgement-style `term_context` and
//! `syntax_pattern`. Builds `InfixRuleInfo` records, feeds them to
//! `prattail::binding_power::analyze_binding_powers`, and emits the
//! resulting `InfixOperator` entries into per-category static tables
//! consumed by the engine's `InfixLoop` state.
//!
//! Cross-category operators (e.g., Calculator's `EqInt: Int × Int → Bool`)
//! are handled in the same classification pass — the `is_cross_category`
//! flag on `InfixRuleInfo` drives Fork-based selection at runtime when a
//! token has multiple candidate result categories.

use mettail_ast::grammar::{GrammarRule, PatternOp, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;
use mettail_prattail::binding_power::{
    analyze_binding_powers, BindingPowerTable, InfixOperator, InfixRuleInfo,
};
use mettail_prattail::wpda_rule_analysis::{
    InfixParamShape, InfixRuleShape, InfixSyntaxShape, InfixTypeShape, IDENT_CAPTURE_KIND_NAME,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// #131: the `operand_src_idx` a CAPTURE `MixfixPart` carries in the emitted
/// `mixfix_part` table.
///
/// A capture part consumes ONE token and yields no operand, so no category index
/// is honest for it. The alternative — resolving `"Ident"` through the category
/// list — silently produced `0`, the FIRST declared category, and the walker then
/// sub-parsed the wrong category with no diagnostic anywhere. This value is the
/// backstop that makes such a read detectable; the driver reads `capture_kind`
/// first and never reaches it.
///
/// Emitted verbatim as the generated `MIXFIX_PART_NO_OPERAND` so the codegen-time
/// and runtime notions cannot drift.
const MIXFIX_PART_NO_OPERAND: u16 = u16::MAX;

/// Build the BindingPowerTable for a language from its `terms` block.
pub(crate) fn build_bp_table(language: &LanguageDef) -> BindingPowerTable {
    let infix_rules = extract_infix_rules(language);
    analyze_binding_powers(&infix_rules)
}

/// Extract `InfixRuleInfo` entries from the language's rules. Covers
/// binary infix (old + judgement-style), unary-postfix, and mixfix.
/// Unary prefix rules are classified separately in `prefix.rs`.
///
/// Plan 3 (ambient cluster, 2026-05-10): clones each rule and runs
/// `convert_items_to_term_context` on the clone before classification
/// so BNF-style rules (e.g., ambient.rs's `PAmb . Proc ::= Name "[" Proc "]"`)
/// get classified as judgement-style. The conversion is a no-op for rules
/// that already have `term_context` + `syntax_pattern` set.
pub(crate) fn extract_infix_rules(language: &LanguageDef) -> Vec<InfixRuleInfo> {
    let mut rules = Vec::new();
    for rule in &language.terms {
        let mut normalized = rule.clone();
        mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
        if let Some(info) = classify_rule(&normalized) {
            rules.push(info);
        }
    }
    rules
}

/// Classify a single `GrammarRule` as infix / postfix / mixfix or None
/// (everything else: atomics, binders, cross-cat projections, etc.).
fn classify_rule(rule: &GrammarRule) -> Option<InfixRuleInfo> {
    mettail_prattail::wpda_rule_analysis::classify_rule(&project_infix_rule(rule))
}

/// Project only observations consumed by the shared original classifier.
/// Keeping every position (including unsupported markers) preserves its
/// length and name checks. This projection performs no normalization/search.
fn project_infix_rule(rule: &GrammarRule) -> InfixRuleShape {
    debug_assert_eq!(
        mettail_ast::grammar::NonTerminalKind::classify(IDENT_CAPTURE_KIND_NAME),
        mettail_ast::grammar::NonTerminalKind::Ident,
        "the shared capture kind must retain the AST's builtin Ident meaning",
    );
    InfixRuleShape {
        label: rule.label.to_string(),
        category: rule.category.to_string(),
        is_right_assoc: rule.is_right_assoc,
        shares_level_with_previous: rule.shares_level_with_previous,
        term_context: rule.term_context.as_ref().map(|params| {
            params
                .iter()
                .map(|param| match param {
                    TermParam::Simple { name, ty } => InfixParamShape::Simple {
                        name: name.to_string(),
                        ty: project_infix_type(ty),
                    },
                    _ => InfixParamShape::Other,
                })
                .collect()
        }),
        syntax_pattern: rule.syntax_pattern.as_ref().map(|pattern| {
            pattern
                .iter()
                .map(|item| match item {
                    SyntaxExpr::Literal(text) => InfixSyntaxShape::Literal(text.clone()),
                    SyntaxExpr::Param(name) => InfixSyntaxShape::Param(name.to_string()),
                    SyntaxExpr::Op(PatternOp::Sep { collection, separator, .. }) => {
                        InfixSyntaxShape::Sep {
                            collection: collection.to_string(),
                            separator: separator.clone(),
                        }
                    },
                    _ => InfixSyntaxShape::Other,
                })
                .collect()
        }),
    }
}

fn project_infix_type(ty: &TypeExpr) -> InfixTypeShape {
    match ty {
        TypeExpr::Base(name) => InfixTypeShape::Base(name.to_string()),
        TypeExpr::Collection { element, .. } => InfixTypeShape::Collection {
            element_base: match element.as_ref() {
                TypeExpr::Base(name) => Some(name.to_string()),
                _ => None,
            },
        },
        _ => InfixTypeShape::Other,
    }
}

/// Public re-export of `classify_rule` for use in `semantic_actions.rs`.
///
/// Plan 3 (ambient cluster, 2026-05-10): clones the rule and runs
/// `convert_items_to_term_context` so BNF-style rules are normalized
/// before classification. No-op for judgement-style rules.
pub(crate) fn classify_rule_public(rule: &GrammarRule) -> Option<InfixRuleInfo> {
    let mut normalized = rule.clone();
    mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
    classify_rule(&normalized)
}

/// Emit per-category static BP tables consumed by the `InfixLoop` engine
/// state. Tables are indexed by terminal text at runtime via the emitted
/// lookup helpers.
///
/// The lookup returns `(left_bp, right_bp, result_src_idx, rule_idx)` so
/// the engine can emit the correct InfixContinuation Return symbol with
/// the rule_idx pointing at the operator's arity-2 action.
pub(crate) fn emit_bp_tables(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
) -> TokenStream {
    let bp_table = build_bp_table(language);
    // Lookup: rule label → (cat_src_idx, rule_idx) for resolving result
    // categories and rule indices in the BP-table emission.
    let label_to_indices = build_label_index(categories, per_cat);
    // C1 S0: per-category literal-injection rule index (`NumLit` for Int).
    // The synth_atom_symbol primitive needs each operand category's literal
    // rule to build atom leaves. `generate_literal_label(native_type)` names
    // the synthetic rule; resolve its local rule_idx via the label index.
    let cat_lit_rule_idx: std::collections::HashMap<String, u16> = language
        .types
        .iter()
        .filter_map(|td| {
            let cat_name = td.name.to_string();
            let nt = td.native_type.as_ref()?;
            let lit_label = crate::gen::generate_literal_label(nt).to_string();
            let (_, ri) = label_to_indices.get(&(cat_name.clone(), lit_label))?;
            Some((cat_name, *ri))
        })
        .collect();
    // C1 D1: per-category value-home rank source — `true` if the category
    // parses its literal operand via a tier-0.0 polymorphic home prefix arm
    // (integer kinds incl. `CanonicalBigInt`), else `false`. This is the
    // lex-min PRIMARY key the canonical-op winner selection mirrors: a
    // bare-integer chain converges on the integer-home category (Int) even
    // when a non-integer-home category (e.g. BigRat) has a lower
    // `category_src_idx` but reaches a bare integer only via a cross-cat
    // projection (tier >= BP_TIER_CROSSCAT_PROJECTION = 0.025).
    let cat_is_value_home: std::collections::HashMap<String, bool> = language
        .types
        .iter()
        .map(|td| {
            let is_home = td
                .native_type
                .as_ref()
                .map(|nt| crate::gen::native::NativeType::from_syn_type(nt).is_integer())
                .unwrap_or(false);
            (td.name.to_string(), is_home)
        })
        .collect();
    // GEN-1 B-2 (Stage S0): one shared (cat,terminal) grouping consumed by all
    // three per-tier slice emitters below AND by `emit_infix_lex_alt_rule_arms`
    // (kind_dispatch.rs) ⇒ the slice and lex-alt rule multisets are identical per
    // (cat,terminal) by construction (NO-LOSS).
    let grouped = group_ops_by_cat_terminal(&bp_table, categories, &label_to_indices);
    let mut per_cat_tables = Vec::new();
    for (cat_i, cat) in categories.iter().enumerate() {
        let cat_src_idx = cat_i as u16;
        let cat_lower = cat.to_lowercase();
        let infix_ident = format_ident!("infix_bp_{}", cat_lower);
        let postfix_ident = format_ident!("postfix_bp_{}", cat_lower);
        let mixfix_ident = format_ident!("mixfix_bp_{}", cat_lower);
        // Phase F.13 chain_10000 Exp 6 Substage 6b (2026-05-26): per-cat
        // iter-eligible lookup. Returns `Some((left_bp, right_bp))` when
        // the (rs, ri) tuple refers to an iterative-eligible operator
        // AND no other operator in the same category shares the same
        // (terminal, left_bp) pair (Plan A invariant I1 — singleton
        // InfixLoop dispatch).
        let iter_ident = format_ident!("iter_eligible_{}", cat_lower);
        per_cat_tables.push(emit_infix_bp_fn(&grouped, cat_src_idx, &infix_ident));
        per_cat_tables.push(emit_postfix_bp_fn(&grouped, cat_src_idx, &postfix_ident));
        per_cat_tables.push(emit_mixfix_bp_fn(&grouped, cat_src_idx, &mixfix_ident));
        per_cat_tables.push(emit_iter_eligible_fn(
            &bp_table,
            cat,
            &iter_ident,
            &label_to_indices,
            categories,
            &cat_lit_rule_idx,
            &cat_is_value_home,
        ));
    }
    // B7 Pattern 1: per-rule mixfix-parts metadata. Used by the engine's
    // Unwinding-MixfixMarker / MixfixContinuation arms to look up each
    // inner operand's category and the separator that follows it. Keyed
    // on (result_src_idx, rule_idx, part_idx).
    per_cat_tables.push(emit_mixfix_parts_fn(
        &bp_table,
        categories,
        &label_to_indices,
        per_cat,
        language,
    ));
    quote! { #(#per_cat_tables)* }
}

/// Build a map from rule.label → (cat_src_idx, rule_idx). Used to look up
/// the pair for an operator's `result_category` + `label`.
/// F5-2 (2026-07-13): `pub(crate)` so `factoring::discover_mixfix_cohorts`
/// reads the SAME (cat,terminal) grouping the slice emitters consume.
pub(crate) fn build_label_index(
    categories: &[String],
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
) -> std::collections::HashMap<(String, String), (u16, u16)> {
    let mut idx = std::collections::HashMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let cat_name = &categories[cat_i];
        for (rule_i, rule) in rules.iter().enumerate() {
            idx.insert((cat_name.clone(), rule.label.to_string()), (cat_i as u16, rule_i as u16));
        }
    }
    idx
}

/// GEN-1 compile-time kill-switch (B-2 slice migration, Stage S0).
///
/// Each per-tier binding-power lookup (`infix_bp_<cat>` / `postfix_bp_<cat>` /
/// `mixfix_bp_<cat>`) returns a `&'static [..]` slice of EVERY rule that shares a
/// `(category, terminal)` trigger, in canonical `rule_idx` order.
/// `GEN1_MAX_SLICE` truncates every emitted slice to its first `GEN1_MAX_SLICE`
/// element(s) at macro-expansion time.
///
/// At `cap = 1` the slice holds only the canonical-order-first (rule_idx-min)
/// element — exactly the operator the pre-S0 `Option`-returning lookups returned
/// via Rust's first-arm-wins `match` — so the slice dispatch is BYTE-IDENTICAL to
/// the legacy single-winner dispatch. Raising the cap (S1+) admits the remaining
/// trigger-sharing rules as fork candidates with NO further plumbing change;
/// reverting GEN-1 is a one-line flip back to `1`.
///
/// Stage S1 (2026-06-28): UNCAPPED to `usize::MAX` so multi-element slices FORK.
/// The only pre-C3 multi-element slices are the 24 `.`-method mixfix rules (they
/// share the `.` trigger in `mixfix_bp_proc`); they now fork 24-way and each
/// non-matching branch dies in ONE step at its method-name literal-run
/// (`__checked_literal_consume!` → 0-edge `Error`), so methods still roundtrip.
/// Revert = flip back to `1`.
pub(crate) const GEN1_MAX_SLICE: usize = usize::MAX;

/// One operator resolved to its global packing coordinates, retaining a borrow of
/// the source [`InfixOperator`] for its tier flags and binding powers. Produced by
/// [`group_ops_by_cat_terminal`].
pub(crate) struct GroupedOp<'a> {
    /// The source operator (tier flags `is_postfix` / `is_mixfix`, `left_bp`,
    /// `right_bp`, `terminal`, ...).
    pub(crate) op: &'a InfixOperator,
    /// Result-category source index (the packing's category).
    pub(crate) result_src_idx: u16,
    /// Local rule index within the result category.
    pub(crate) rule_idx: u16,
}

/// B-2 (Stage S0) NO-LOSS foundation: group EVERY operator by
/// `(operand cat_src_idx, terminal)`, preserving the canonical
/// `bp_table.operators` order within each group (category-alphabetical ×
/// infix/mixfix-then-postfix, each in declaration order — see
/// `analyze_binding_powers`).
///
/// This single grouping feeds BOTH the per-tier slice emitters
/// (`emit_{infix,postfix,mixfix}_bp_fn`) AND the lattice lex-alt emitter
/// (`emit_infix_lex_alt_rule_arms`, `kind_dispatch.rs`), so the per-(cat,terminal)
/// rule multiset is IDENTICAL across the two dispatch surfaces by construction —
/// the GEN-1 NO-LOSS invariant. Operators whose operand category or
/// `(result_category, label)` packing coordinates cannot be resolved are skipped
/// (matching the legacy emitters' defensive `filter_map` / `continue`).
pub(crate) fn group_ops_by_cat_terminal<'a>(
    bp_table: &'a BindingPowerTable,
    categories: &[String],
    label_index: &std::collections::HashMap<(String, String), (u16, u16)>,
) -> std::collections::BTreeMap<(u16, String), Vec<GroupedOp<'a>>> {
    let mut grouped: std::collections::BTreeMap<(u16, String), Vec<GroupedOp<'a>>> =
        std::collections::BTreeMap::new();
    for op in &bp_table.operators {
        let Some(cat_src_idx) = categories
            .iter()
            .position(|cat| cat == &op.category)
            .map(|idx| idx as u16)
        else {
            continue;
        };
        let Some(&(result_src_idx, rule_idx)) =
            label_index.get(&(op.result_category.clone(), op.label.clone()))
        else {
            continue;
        };
        grouped
            .entry((cat_src_idx, op.terminal.clone()))
            .or_default()
            .push(GroupedOp { op, result_src_idx, rule_idx });
    }
    grouped
}

/// Emit `infix_bp_<cat>(terminal) -> &'static [(l_bp, r_bp, result_src, rule_idx)]`.
///
/// GEN-1 B-2 (Stage S0): returns a slice of every infix rule sharing the terminal
/// in this category, truncated to [`GEN1_MAX_SLICE`] (1 at S0 ⇒ the legacy
/// single-winner / first-arm-wins element). The four-tuple KEEPS `r_bp` — the
/// cross-cat / right-assoc sub-parse floor — unlike the postfix/mixfix tiers.
fn emit_infix_bp_fn(
    grouped: &std::collections::BTreeMap<(u16, String), Vec<GroupedOp>>,
    cat_src_idx: u16,
    fn_ident: &proc_macro2::Ident,
) -> TokenStream {
    let arms = grouped
        .iter()
        .filter(|((c, _t), _ops)| *c == cat_src_idx)
        .filter_map(|((_c, terminal), ops)| {
            let tuples: Vec<TokenStream> = ops
                .iter()
                .filter(|g| !g.op.is_postfix && !g.op.is_mixfix)
                .take(GEN1_MAX_SLICE)
                .map(|g| {
                    let l = g.op.left_bp;
                    let r = g.op.right_bp;
                    let result_src_idx = g.result_src_idx;
                    let rule_idx = g.rule_idx;
                    quote! { (#l, #r, #result_src_idx, #rule_idx) }
                })
                .collect();
            if tuples.is_empty() {
                return None;
            }
            Some(quote! {
                #terminal => &[ #(#tuples),* ],
            })
        });
    quote! {
        /// Binding-power lookup for infix operators in this category. Returns a
        /// slice of `(left_bp, right_bp, result_src_idx, rule_idx)` for every
        /// infix rule sharing the terminal (GEN-1 B-2; capped to `GEN1_MAX_SLICE`
        /// at codegen — 1 at Stage S0 ⇒ legacy single-winner).
        #[allow(non_snake_case, dead_code)]
        fn #fn_ident(terminal: &str) -> &'static [(u8, u8, u16, u16)] {
            match terminal {
                #(#arms)*
                _ => &[],
            }
        }
    }
}

/// Phase F.13 chain_10000 Exp 6 Substage 6b (2026-05-26): emit
/// `iter_eligible_<cat>(rs, ri) -> Option<(u8, u8)>` returning
/// `Some((left_bp, right_bp))` when (rs, ri) refers to an
/// iterative-eligible operator AND no other operator in the same
/// category shares the same `(terminal, left_bp)` pair (Plan A
/// invariant I1 — singleton InfixLoop dispatch). The codegen-time
/// uniqueness check is required because `InfixOperator::is_iterative_candidate`
/// can only inspect a single operator at a time; the I1 invariant
/// requires a per-category scan.
///
/// At codegen time, the eligibility stays category-local: every same-category
/// iterative operator that is unique within its category may be summarized in
/// that category. Cross-category ambiguity is preserved as distinct WPDA
/// alternatives; the absorber only changes the representation of an
/// individual category-local derivation.
fn emit_iter_eligible_fn(
    bp_table: &BindingPowerTable,
    category: &str,
    fn_ident: &proc_macro2::Ident,
    label_index: &std::collections::HashMap<(String, String), (u16, u16)>,
    categories: &[String],
    cat_lit_rule_idx: &std::collections::HashMap<String, u16>,
    cat_is_value_home: &std::collections::HashMap<String, bool>,
) -> TokenStream {
    let _ = (categories, cat_is_value_home);
    let cat_ops: Vec<&InfixOperator> = bp_table
        .operators
        .iter()
        .filter(|op| op.category == category)
        .collect();
    // GEN-1 B-2 (Stage S0) §2.4 — codegen DISJOINTNESS ASSERT.
    //
    // The InfixLoop pre-fork absorption blocks (engine_impl.rs) read the
    // iterative-eligible op via `#dispatch.first()` over the per-tier BP slice.
    // For that `.first()` to remain SOUND once `GEN1_MAX_SLICE` is uncapped
    // (S1+) — i.e. for the iter-eligible op to be the UNIQUE candidate at its
    // terminal so truncation can never drop it in favor of a competing rule —
    // every iter-eligible op in this category MUST be the only op in the
    // category bearing its terminal. This STRENGTHENS the (terminal, left_bp)
    // uniqueness (I1, below) to plain terminal uniqueness. A breach is a
    // grammar-level GEN-1 precondition violation ⇒ hard `compile_error!`.
    // Vacuous when no op in the category is iterative-eligible (e.g. rholang).
    let disjointness_errors: Vec<TokenStream> = cat_ops
        .iter()
        .enumerate()
        .filter(|(_, op)| op.is_iterative_candidate())
        .filter_map(|(i, op)| {
            let clash = cat_ops
                .iter()
                .enumerate()
                .find(|(j, other)| *j != i && other.terminal == op.terminal)
                .map(|(_, other)| other)?;
            let msg = format!(
                "GEN-1 B-2 disjointness violation: iterative-eligible operator \
                 `{}` (terminal `{}`) in category `{}` shares its terminal with \
                 operator `{}`. The InfixLoop pre-fork `.first()` absorption \
                 requires each iter-eligible op to own its terminal uniquely \
                 within its category.",
                op.label, op.terminal, category, clash.label,
            );
            Some(quote! { compile_error!(#msg); })
        })
        .collect();
    let arms: Vec<TokenStream> = cat_ops
        .iter()
        .filter(|op| op.is_iterative_candidate())
        .filter_map(|op| {
            // I1 (within-category): no other operator in this category shares
            // the same (terminal, left_bp) pair, so the singleton InfixLoop
            // dispatch is unambiguous.
            let conflict = cat_ops.iter().any(|other| {
                !std::ptr::eq(*other as *const _, *op as *const _)
                    && other.terminal == op.terminal
                    && other.left_bp == op.left_bp
            });
            if conflict {
                return None;
            }
            let (rs, ri) = *label_index.get(&(op.result_category.clone(), op.label.clone()))?;
            let l = op.left_bp;
            let r = op.right_bp;
            let assoc_right = op.left_bp > op.right_bp;
            let is_mixfix = op.is_mixfix;
            // For an iter-candidate (`!is_cross_category`) the operand
            // category equals the result category, so atom_cat_src_idx == rs.
            let atom_cat_src_idx = rs;
            let atom_lit_rule_idx = *cat_lit_rule_idx.get(&op.result_category)?;
            // Mixfix trigger + inner separator terminals (empty for binary).
            let (trigger, sep): (String, String) = if op.is_mixfix {
                let sep = op
                    .mixfix_parts
                    .first()
                    .and_then(|p| p.following_terminals.first().cloned())
                    .unwrap_or_default();
                (op.terminal.clone(), sep)
            } else {
                (String::new(), String::new())
            };
            let trigger_lit = proc_macro2::Literal::string(&trigger);
            let sep_lit = proc_macro2::Literal::string(&sep);
            Some(quote! {
                (#rs, #ri) => Some(mettail_prattail::binding_power::IterAbsorbSpec {
                    left_bp: #l,
                    right_bp: #r,
                    assoc_right: #assoc_right,
                    is_mixfix: #is_mixfix,
                    op_cat_src_idx: #rs,
                    op_rule_idx: #ri,
                    atom_cat_src_idx: #atom_cat_src_idx,
                    atom_lit_rule_idx: #atom_lit_rule_idx,
                    trigger: #trigger_lit,
                    sep: #sep_lit,
                }),
            })
        })
        .collect();
    quote! {
        // GEN-1 B-2 (Stage S0) §2.4: terminal-disjointness breaches (if any)
        // surface here as `compile_error!`. Empty ⇒ no tokens ⇒ byte-identical.
        #(#disjointness_errors)*
        /// C1: iterative-eligible operator lookup. Returns the canonical
        /// `IterAbsorbSpec` for `(rs, ri)` — present iff this op is THE
        /// canonical absorber for its terminal (cross-category D1 filter) and
        /// has no within-category (terminal, l_bp) conflict (I1). The walker's
        /// H3 absorption + the InfixLoop pre-fork trigger consume the spec.
        #[allow(non_snake_case, dead_code)]
        fn #fn_ident(rs: u16, ri: u16) -> Option<mettail_prattail::binding_power::IterAbsorbSpec> {
            match (rs, ri) {
                #(#arms)*
                _ => None,
            }
        }
    }
}

/// Emit `postfix_bp_<cat>(terminal) -> &'static [(l_bp, result_src, rule_idx)]`.
/// GEN-1 B-2 (Stage S0): slice of every postfix rule sharing the terminal,
/// truncated to [`GEN1_MAX_SLICE`] (1 at S0 ⇒ legacy single-winner).
fn emit_postfix_bp_fn(
    grouped: &std::collections::BTreeMap<(u16, String), Vec<GroupedOp>>,
    cat_src_idx: u16,
    fn_ident: &proc_macro2::Ident,
) -> TokenStream {
    let arms = grouped
        .iter()
        .filter(|((c, _t), _ops)| *c == cat_src_idx)
        .filter_map(|((_c, terminal), ops)| {
            let tuples: Vec<TokenStream> = ops
                .iter()
                .filter(|g| g.op.is_postfix)
                .take(GEN1_MAX_SLICE)
                .map(|g| {
                    let l = g.op.left_bp;
                    let result_src_idx = g.result_src_idx;
                    let rule_idx = g.rule_idx;
                    quote! { (#l, #result_src_idx, #rule_idx) }
                })
                .collect();
            if tuples.is_empty() {
                return None;
            }
            Some(quote! {
                #terminal => &[ #(#tuples),* ],
            })
        });
    quote! {
        /// Binding-power lookup for postfix operators in this category. Returns a
        /// slice of `(left_bp, result_src_idx, rule_idx)` (GEN-1 B-2; capped to
        /// `GEN1_MAX_SLICE` at codegen — 1 at Stage S0 ⇒ legacy single-winner).
        #[allow(non_snake_case, dead_code)]
        fn #fn_ident(terminal: &str) -> &'static [(u8, u16, u16)] {
            match terminal {
                #(#arms)*
                _ => &[],
            }
        }
    }
}

/// B7 Pattern 1: emit a per-category mixfix BP lookup, returning
/// `(left_bp, result_src_idx, rule_idx)` for any mixfix trigger keyword
/// whose left operand is in this category. The InfixLoop dispatch
/// queries this AFTER infix and postfix lookups; on hit, it consumes the
/// trigger token and pushes a MixfixMarker with `bp=0` (zero operands
/// completed so far).
fn emit_mixfix_bp_fn(
    grouped: &std::collections::BTreeMap<(u16, String), Vec<GroupedOp>>,
    cat_src_idx: u16,
    fn_ident: &proc_macro2::Ident,
) -> TokenStream {
    let arms = grouped
        .iter()
        .filter(|((c, _t), _ops)| *c == cat_src_idx)
        .filter_map(|((_c, terminal), ops)| {
            let tuples: Vec<TokenStream> = ops
                .iter()
                .filter(|g| g.op.is_mixfix)
                .take(GEN1_MAX_SLICE)
                .map(|g| {
                    let l = g.op.left_bp;
                    let result_src_idx = g.result_src_idx;
                    let rule_idx = g.rule_idx;
                    quote! { (#l, #result_src_idx, #rule_idx) }
                })
                .collect();
            if tuples.is_empty() {
                return None;
            }
            Some(quote! {
                #terminal => &[ #(#tuples),* ],
            })
        });
    quote! {
        /// Binding-power lookup for mixfix operators in this category. Returns a
        /// slice of `(left_bp, result_src_idx, rule_idx)` (GEN-1 B-2; capped to
        /// `GEN1_MAX_SLICE` at codegen — 1 at Stage S0 ⇒ legacy single-winner).
        #[allow(non_snake_case, dead_code)]
        fn #fn_ident(terminal: &str) -> &'static [(u8, u16, u16)] {
            match terminal {
                #(#arms)*
                _ => &[],
            }
        }
    }
}

/// B7 Pattern 1 + L12 follow-up B6 (2026-05-07): emit per-rule
/// mixfix-parts metadata. Returns
/// `mixfix_part(result_src_idx, rule_idx, part_idx) ->
///   Option<(operand_src_idx, preceding: &'static [&'static str],
///           following: &'static [&'static str])>`.
///
/// `preceding` is the literal sequence consumed BEFORE the operand
/// sub-parse (used for postfix-mixfix shapes like POutput's `(`
/// between trigger and inner operand). `following` is the literal
/// sequence consumed AFTER the operand sub-parse (used for trailing
/// brackets and per-part separators). Pre-B6 this was a single
/// `Option<&'static str>` for `following_terminal` only — widened to
/// vectors so postfix-mixfix patterns with consecutive literals are
/// expressible.
///
/// `mixfix_parts_len(result_src_idx, rule_idx) -> Option<u8>` returns
/// the number of inner operands so the engine knows when to stop.
fn emit_mixfix_parts_fn(
    bp_table: &BindingPowerTable,
    categories: &[String],
    label_index: &std::collections::HashMap<(String, String), (u16, u16)>,
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
    language: &LanguageDef,
) -> TokenStream {
    let mut part_arms = Vec::new();
    let mut len_arms = Vec::new();
    let mut nullary_arms = Vec::new();
    // GEN-1 B-3 (Stage S3): per-rep-part metadata arms (one per `*sep` part).
    let mut rep_arms = Vec::new();
    for op in bp_table.operators.iter().filter(|op| op.is_mixfix) {
        let Some(&(result_src_idx, rule_idx)) =
            label_index.get(&(op.result_category.clone(), op.label.clone()))
        else {
            continue;
        };
        // ★ #141 G3 — the refusals below name the rule by its LABEL and point at
        // it. `label_index` is built by `build_label_index` from the very
        // `per_cat` this function is handed, and its value is exactly the
        // `(cat_i, rule_i)` pair that indexes it, so this cannot miss.
        let rule_label = op.label.clone();
        let rule_span = per_cat
            .get(result_src_idx as usize)
            .and_then(|rules| rules.get(rule_idx as usize))
            .map(|rule| rule.label.span())
            .unwrap_or_else(proc_macro2::Span::call_site);
        // `mixfix_parts_len` counts EVERY part, including a `*sep` repetition
        // part. The repetition part's per-part `mixfix_part(..)` arm is SKIPPED
        // below (Stage S2 ⇒ it returns None ⇒ the walker errors cleanly at the
        // rep slot until the Stage S3 repetition handling lands). Counting it
        // keeps `completed_idx + 1 == parts_len` accurate for the surrounding
        // mixfix literal-run accounting.
        let parts_len = op.mixfix_parts.len() as u8;
        len_arms.push(quote! {
            (#result_src_idx, #rule_idx) => Some(#parts_len),
        });
        // GEN-1 B-1 (Stage S2): nullary (0-operand) mixfix literal run.
        if !op.nullary_literals.is_empty() {
            let lits: Vec<TokenStream> =
                op.nullary_literals.iter().map(|t| quote! { #t }).collect();
            nullary_arms.push(quote! {
                (#result_src_idx, #rule_idx) => Some(&[ #( #lits ),* ][..]),
            });
        }
        for (part_idx, part) in op.mixfix_parts.iter().enumerate() {
            // GEN-1 B-3 (Stage S3): a `*sep` repetition part emits NO `mixfix_part`
            // arm (so `mixfix_part(..)` returns None for it) but DOES emit a
            // `mixfix_rep` arm carrying its
            // `(element_src, preceding, separator, close, min)`.
            // The walker's MixfixLiteralRun arms detect the rep slot via
            // `mixfix_rep(..).is_some()` and hand it off to the CollectionLoop;
            // `mixfix_parts_len` still counts it (accounting stays accurate).
            if let Some(rep) = &part.repetition {
                let rep_part_idx = part_idx as u8;
                // ★ #141 G3, AN EIGHTH SIBLING — not on the brief's list of seven,
                // found by reading the enclosing function rather than the list. This
                // `.unwrap_or(0)` is the SAME fails-open shape as the operand lookup
                // twenty lines below, in the same emitter, on the same
                // `part.operand_category` field: an unresolvable element category
                // became index 0, the FIRST declared category, and the emitted
                // `mixfix_rep` row told the CollectionLoop to sub-parse it. Token
                // position, so it takes the shared resolver.
                let elem_src_idx = super::binder::cat_idx_tokens(
                    &part.operand_category,
                    categories,
                    "a mixfix `*sep` repetition's element position",
                    &rule_label,
                    rule_span,
                );
                let separator = &rep.separator;
                let preceding_lits: Vec<TokenStream> = part
                    .preceding_terminals
                    .iter()
                    .map(|t| quote! { #t })
                    .collect();
                let close_lits: Vec<TokenStream> =
                    rep.close.iter().map(|t| quote! { #t }).collect();
                let min = rep.min;
                rep_arms.push(quote! {
                    (#result_src_idx, #rule_idx, #rep_part_idx) => Some((
                        #elem_src_idx,
                        &[ #( #preceding_lits ),* ][..],
                        #separator,
                        &[ #( #close_lits ),* ][..],
                        #min,
                    )),
                });
                continue;
            }
            let part_idx = part_idx as u8;
            // #131: a CAPTURE part consumes one token and yields NO operand, so it must
            // not occupy an operand slot. `MIXFIX_PART_NO_OPERAND` is emitted in the
            // `operand_src_idx` position precisely so a consumer that ignores
            // `capture_kind` and reads the index anyway cannot silently sub-parse
            // category 0 — the failure it would otherwise produce is the one this whole
            // task root-caused. The driver matches on the capture kind BEFORE the index
            // is ever read; the poison is the backstop, not the mechanism.
            let capture_kind_ts: TokenStream = match &part.capture_kind {
                Some(k) => quote! { Some(#k) },
                None => quote! { None },
            };
            // ⚠ SIBLING OF THE #131 ROOT, HARDENED. This is the same fails-open shape as
            // `semantic_actions.rs`'s `lookup_cat_idx(..).unwrap_or(0)`, which resolved
            // the unknown category `Ident` to index 0 — the FIRST declared category — and
            // made an action advertise "slot N expects a `Num` term" while its extractor
            // read identifier text. Here the consequence would be a mixfix part that
            // SUB-PARSES THE WRONG CATEGORY: silently wrong, never a diagnostic.
            //
            // A CAPTURE part legitimately names a non-category (`Ident`), so it takes the
            // poison instead of the lookup. Every OTHER part must resolve.
            //
            // ★ #141 G3 — TWO FIXES AT ONE SITE.
            //
            // (1) The refusal was a `panic!`. Under this workspace's cranelift dev
            //     backend a `panic!` inside a proc macro prints NOTHING: rustc dies with
            //     `fatal runtime error: Rust cannot catch foreign exceptions` and the
            //     payload never appears (#141 RED-0, 2026-07-29). So the message below
            //     could not be read even when it fired. It is now a spanned
            //     `compile_error!` — a TOKEN, rendered by rustc, which the backend
            //     cannot swallow.
            //
            // (2) The message said "mixfix part `{}` of rule `{}`" and passed
            //     `rule_idx`, AN INTEGER. Even had it printed, `rule 7` names nothing a
            //     grammar author can act on: `rule_idx` is a position within
            //     `per_cat[result_src_idx]`, an artefact of codegen ordering. It now
            //     names the rule by LABEL and points the diagnostic at that label's
            //     span, which is what `UnresolvedCategory` exists to make uniform.
            //
            // A capture row is emitted with the poison spelled by NAME rather than as
            // the bare literal `65535u16`, so the generated table says what it means at
            // the one place a reader would otherwise have to guess:
            //   `(0u16, 1u16, 0u8) => Some((MIXFIX_PART_NO_OPERAND, &[][..], &["("][..],
            //                              Some("Ident")))`
            let operand_src_idx: TokenStream = match part.capture_kind.is_some() {
                true => quote! { MIXFIX_PART_NO_OPERAND },
                false => super::binder::cat_idx_tokens(
                    &part.operand_category,
                    categories,
                    "a mixfix operand position",
                    &rule_label,
                    rule_span,
                ),
            };
            let preceding_lits: Vec<TokenStream> = part
                .preceding_terminals
                .iter()
                .map(|t| quote! { #t })
                .collect();
            let following_lits: Vec<TokenStream> = part
                .following_terminals
                .iter()
                .map(|t| quote! { #t })
                .collect();
            part_arms.push(quote! {
                (#result_src_idx, #rule_idx, #part_idx) => Some((
                    #operand_src_idx,
                    &[ #( #preceding_lits ),* ][..],
                    &[ #( #following_lits ),* ][..],
                    #capture_kind_ts,
                )),
            });
        }
    }
    // GAP-3 (2026-06-28): 0-operand MULTI-literal keyword-PREFIX rules
    // (`Map ()`, `Pathmap ()`, `@ Nil`) are NOT in `bp_table.operators` (they
    // have no binding power and are never `is_mixfix`), so the loop above never
    // sees them. They REUSE the same `MixfixLiteralRun { kind: 2, parts_len ==
    // 0 }` runtime arm as B-1, entered from the PREFIX site (prefix.rs) instead
    // of the InfixLoop. Emit their metadata here:
    //   - `mixfix_parts_len(cat, rule) == Some(0)` selects the nullary arm
    //     (distinct from a suppressed `*sep` rep slot, which has parts_len >= 1);
    //   - `mixfix_nullary_literals(cat, rule)` carries the POST-trigger literals
    //     the arm consumes (membership-checked) before popping the marker.
    // The (cat_i, rule_i) coordinates from `per_cat` enumeration MATCH the
    // prefix dispatch's (category_src_idx, rule_idx) exactly (both derive from
    // the same `build_per_category_rules` result — see engine_impl per_cat_indexed
    // and mod.rs). No dup-arm risk: these rules are never `is_mixfix`, so their
    // (result, rule) keys cannot collide with the loop above.
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let result_src_idx = cat_i as u16;
        for (rule_i, rule) in rules.iter().enumerate() {
            if let super::prefix::AtomicShape::NullaryLiteralRun { trailing_literals, .. } =
                super::prefix::classify_atomic(rule, language)
            {
                let rule_idx = rule_i as u16;
                len_arms.push(quote! {
                    (#result_src_idx, #rule_idx) => Some(0u8),
                });
                let lits: Vec<TokenStream> =
                    trailing_literals.iter().map(|t| quote! { #t }).collect();
                nullary_arms.push(quote! {
                    (#result_src_idx, #rule_idx) => Some(&[ #( #lits ),* ][..]),
                });
            }
        }
    }
    // S1-FACTORING F5-2 (2026-07-13): mixfix SPINE `parts_len` PRESENCE rows,
    // `Some(u8::MAX)` poison. The Unwinding-MixfixMarker arm validates
    // `Some(..)` then DISCARDS the value (engine_impl `let _ = parts_len`),
    // so a spine-marked operand return re-enters
    // `MixfixLiteralRun { kind: 0 }` — which the spliced spine prelude
    // intercepts BEFORE the generic reads. An escaped spine id at any OTHER
    // `parts_len` consumer dies loudly on the poison. Rows come from the
    // const-gated partition (`mixfix_emission_partition` — deterministic, so
    // this agrees with the `build_spine_emission` bundle without threading);
    // EMPTY while `S1_FACTORING && S1F5_MIXFIX_COHORTS` is off
    // (byte-identity).
    for (spine_result_src, spine_id) in
        super::factoring::mixfix_spine_parts_len_rows(language, categories, per_cat)
    {
        len_arms.push(quote! {
            (#spine_result_src, #spine_id) => Some(u8::MAX),
        });
    }
    let no_operand_lit = MIXFIX_PART_NO_OPERAND;
    quote! {
        /// Mixfix per-part metadata: returns
        /// `(operand_src_idx, preceding_terminals, following_terminals, capture_kind)`.
        /// L12 follow-up B6 (2026-05-07): widened to vector terminals
        /// for postfix-mixfix support.
        ///
        /// #131 (2026-07-28): the 4th element is the TOKEN CAPTURE kind. `Some(k)`
        /// means "consume ONE token of kind `k`", NOT "sub-parse the category `k`";
        /// `None` is an ordinary category operand. A capture part yields no operand,
        /// so its `operand_src_idx` is the poison `MIXFIX_PART_NO_OPERAND` — reading
        /// it as a category index is a bug, and the poison makes that bug loud
        /// instead of letting it sub-parse category 0.
        #[allow(non_snake_case, dead_code)]
        fn mixfix_part(
            result_src_idx: u16,
            rule_idx: u16,
            part_idx: u8,
        ) -> Option<(
            u16,
            &'static [&'static str],
            &'static [&'static str],
            Option<&'static str>,
        )> {
            match (result_src_idx, rule_idx, part_idx) {
                #(#part_arms)*
                _ => None,
            }
        }

        /// #131: the `operand_src_idx` a CAPTURE part carries. A capture consumes a
        /// token and produces no operand, so there is no honest category index to
        /// put here; this value exists so that reading one is detectable rather than
        /// silently equal to the first declared category.
        #[allow(dead_code)]
        const MIXFIX_PART_NO_OPERAND: u16 = #no_operand_lit;

        /// Mixfix parts count: returns the number of inner operands for
        /// the (result_src, rule_idx) mixfix rule. Counts a `*sep` repetition
        /// part even though its per-part metadata is suppressed (B-3 S2).
        #[allow(non_snake_case, dead_code)]
        fn mixfix_parts_len(result_src_idx: u16, rule_idx: u16) -> Option<u8> {
            match (result_src_idx, rule_idx) {
                #(#len_arms)*
                _ => None,
            }
        }

        /// GEN-1 B-1 (Stage S2): post-trigger literal run for a 0-operand
        /// (nullary) mixfix rule (POutputEmpty `n "!" "(" ")"` ⇒ `["(", ")"]`,
        /// zero-arg methods `.size()` ⇒ `["size", "(", ")"]`). The walker's
        /// `(2, None) if parts_len == 0` arm consumes these literals then pops
        /// the marker and fires the arity-1 (LHS-only) action. `None` for every
        /// operand-bearing mixfix rule (`mixfix_parts_len(..) != Some(0)`).
        #[allow(non_snake_case, dead_code)]
        fn mixfix_nullary_literals(
            result_src_idx: u16,
            rule_idx: u16,
        ) -> Option<&'static [&'static str]> {
            match (result_src_idx, rule_idx) {
                #(#nullary_arms)*
                _ => None,
            }
        }

        /// GEN-1 B-3 (Stage S3): repetition-part metadata. For a `*sep`
        /// repetition `MixfixPart` (e.g. POutput2Plus's `bs.*sep(",")`), returns
        /// `(element_src_idx, preceding_terminals, separator, close_terminals,
        /// min)`; `None` for an ordinary single-operand part and for every
        /// non-rep rule. The walker's
        /// `MixfixLiteralRun` arms use `mixfix_rep(rs, ri, part_idx).is_some()` to
        /// detect a repetition slot and hand it off to the `CollectionLoop`
        /// (replace the marker → push a `CollectionMarker` for `part_idx` →
        /// `PrefixDispatch`). The close/sep/element_src are ALSO carried by the
        /// per-slot `collection_spec(rs, ri, part_idx)` record (the CollectionLoop
        /// reads those); `mixfix_rep` is the codegen-time presence signal + the
        /// documented descriptor.
        #[allow(non_snake_case, dead_code)]
        fn mixfix_rep(
            result_src_idx: u16,
            rule_idx: u16,
            part_idx: u8,
        ) -> Option<(
            u16,
            &'static [&'static str],
            &'static str,
            &'static [&'static str],
            u8,
        )> {
            match (result_src_idx, rule_idx, part_idx) {
                #(#rep_arms)*
                _ => None,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::{rule_fixture, GrammarRule, PatternOp, SyntaxExpr, TermParam};
    use mettail_ast::types::TypeExpr;
    use mettail_prattail::binding_power::{Associativity, InfixRuleInfo, MixfixPart, MixfixRep};
    use proc_macro2::Span;
    use syn::Ident;

    fn simple(name: &str, ty: &str) -> TermParam {
        TermParam::Simple {
            name: Ident::new(name, Span::call_site()),
            ty: TypeExpr::Base(Ident::new(ty, Span::call_site())),
        }
    }

    fn param(name: &str) -> SyntaxExpr {
        SyntaxExpr::Param(Ident::new(name, Span::call_site()))
    }

    fn lit(s: &str) -> SyntaxExpr {
        SyntaxExpr::Literal(s.to_string())
    }

    fn infix_rule(label: &str, cat: &str, operand: &str, op: &str) -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![simple("a", operand), simple("b", operand)]),
            syntax_pattern: Some(vec![param("a"), lit(op), param("b")]),
            ..rule_fixture(Ident::new(label, Span::call_site()), Ident::new(cat, Span::call_site()))
        }
    }

    fn postfix_rule(label: &str, cat: &str, operand: &str, op: &str) -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![simple("a", operand)]),
            syntax_pattern: Some(vec![param("a"), lit(op)]),
            ..rule_fixture(Ident::new(label, Span::call_site()), Ident::new(cat, Span::call_site()))
        }
    }

    // These are fixed expected descriptors, not another rule classifier. Debug
    // equality covers every nested field without changing production derives.
    fn projection_baseline_descriptor(label: &str, terminal: &str) -> InfixRuleInfo {
        InfixRuleInfo {
            label: label.into(),
            terminal: terminal.into(),
            category: "Int".into(),
            result_category: "Int".into(),
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: Vec::new(),
            nullary_literals: Vec::new(),
        }
    }

    fn assert_projection_baseline(rule: &GrammarRule, expected: InfixRuleInfo) {
        let actual = classify_rule(rule).expect("original classifier must accept this fixture");
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn projected_infix_views_preserve_absence_and_unsupported_positions() {
        let mut rule = postfix_rule("View", "Int", "Int", "!");
        rule.term_context.as_mut().expect("fixture context").insert(
            0,
            TermParam::GuardBody {
                name: Ident::new("guard", Span::call_site()),
            },
        );
        rule.syntax_pattern
            .as_mut()
            .expect("fixture syntax")
            .insert(1, SyntaxExpr::Op(PatternOp::Opt { inner: vec![lit("ignored")] }));
        let projected = project_infix_rule(&rule);
        assert_eq!(
            projected.term_context,
            Some(vec![
                InfixParamShape::Other,
                InfixParamShape::Simple {
                    name: "a".into(),
                    ty: InfixTypeShape::Base("Int".into()),
                },
            ])
        );
        assert_eq!(
            projected.syntax_pattern,
            Some(vec![
                InfixSyntaxShape::Param("a".into()),
                InfixSyntaxShape::Other,
                InfixSyntaxShape::Literal("!".into()),
            ])
        );
        rule.term_context = None;
        rule.syntax_pattern = None;
        let absent = project_infix_rule(&rule);
        assert_eq!(absent.term_context, None);
        assert_eq!(absent.syntax_pattern, None);
        rule.term_context = Some(Vec::new());
        rule.syntax_pattern = Some(Vec::new());
        let empty = project_infix_rule(&rule);
        assert_eq!(empty.term_context, Some(Vec::new()));
        assert_eq!(empty.syntax_pattern, Some(Vec::new()));
    }

    #[test]
    fn projection_baseline_preserves_parameter_declaration_order() {
        let mut rule = infix_rule("Order", "Int", "Int", "+");
        rule.term_context
            .as_mut()
            .expect("test fixture contains its declared context or syntax")
            .swap(0, 1);
        assert!(classify_rule(&rule).is_none());
        rule.syntax_pattern = Some(vec![param("b"), lit("+"), param("a")]);
        assert_projection_baseline(&rule, projection_baseline_descriptor("Order", "+"));
    }

    #[test]
    fn projection_baseline_matches_raw_and_unicode_identifiers() {
        for name in [Ident::new_raw("type", Span::call_site()), Ident::new("δ", Span::call_site())]
        {
            let mut rule = postfix_rule("Names", "Int", "Int", "!");
            let mut syntax_name = name.clone();
            syntax_name.set_span(Span::mixed_site());
            rule.term_context = Some(vec![TermParam::Simple {
                name,
                ty: TypeExpr::Base(Ident::new("Int", Span::call_site())),
            }]);
            rule.syntax_pattern = Some(vec![SyntaxExpr::Param(syntax_name), lit("!")]);
            let mut expected = projection_baseline_descriptor("Names", "!");
            expected.is_postfix = true;
            assert_projection_baseline(&rule, expected);
            rule.syntax_pattern = Some(vec![param("different"), lit("!")]);
            assert!(classify_rule(&rule).is_none());
        }
    }

    #[test]
    fn projection_baseline_never_filters_unsupported_positions() {
        let original = infix_rule("Unsupported", "Int", "Int", "+");
        for position in 0..=2 {
            let mut rule = original.clone();
            rule.term_context
                .as_mut()
                .expect("test fixture contains its declared context or syntax")
                .insert(
                    position,
                    TermParam::GuardBody {
                        name: Ident::new("guard", Span::call_site()),
                    },
                );
            assert!(classify_rule(&rule).is_none(), "parameter position {position}");
        }
        for position in 0..=3 {
            let mut rule = original.clone();
            rule.syntax_pattern
                .as_mut()
                .expect("test fixture contains its declared context or syntax")
                .insert(
                    position,
                    SyntaxExpr::TokenKind {
                        name: Ident::new("Custom", Span::call_site()),
                        bind: None,
                    },
                );
            assert!(classify_rule(&rule).is_none(), "syntax position {position}");
        }
        let mut rule = original;
        rule.syntax_pattern
            .as_mut()
            .expect("test fixture contains its declared context or syntax")[1] =
            SyntaxExpr::Op(PatternOp::Opt { inner: vec![lit("+")] });
        assert!(classify_rule(&rule).is_none());
    }

    #[test]
    fn projection_baseline_rejects_missing_and_empty_observations() {
        for term_context in [None, Some(Vec::new())] {
            let mut rule = infix_rule("Absent", "Int", "Int", "+");
            rule.term_context = term_context;
            assert!(classify_rule(&rule).is_none());
        }
        for syntax_pattern in [None, Some(Vec::new())] {
            let mut rule = infix_rule("Absent", "Int", "Int", "+");
            rule.syntax_pattern = syntax_pattern;
            assert!(classify_rule(&rule).is_none());
        }
        let mut rule = infix_rule("Absent", "Int", "Int", "+");
        rule.term_context = Some(Vec::new());
        rule.syntax_pattern = Some(Vec::new());
        assert!(classify_rule(&rule).is_none());
    }

    #[test]
    fn projection_baseline_ident_capture_in_both_mixfix_branches() {
        let mut rule = infix_rule("Capture", "Int", "Int", ".");
        rule.term_context = Some(vec![simple("a", "Int"), simple("name", "Ident")]);
        rule.syntax_pattern = Some(vec![param("a"), lit("."), param("name"), lit("!")]);
        let mut expected = projection_baseline_descriptor("Capture", ".");
        expected.is_mixfix = true;
        expected.mixfix_parts = vec![MixfixPart {
            operand_category: "Ident".into(),
            param_name: "name".into(),
            preceding_terminals: Vec::new(),
            following_terminals: vec!["!".into()],
            repetition: None,
            capture_kind: Some("Ident".into()),
        }];
        assert_projection_baseline(&rule, expected.clone());

        rule.term_context
            .as_mut()
            .expect("test fixture contains its declared context or syntax")
            .push(simple("tail", "Int"));
        rule.syntax_pattern
            .as_mut()
            .expect("test fixture contains its declared context or syntax")
            .push(param("tail"));
        expected.mixfix_parts.push(MixfixPart {
            operand_category: "Int".into(),
            param_name: "tail".into(),
            preceding_terminals: Vec::new(),
            following_terminals: Vec::new(),
            repetition: None,
            capture_kind: None,
        });
        assert_projection_baseline(&rule, expected);
    }

    #[test]
    fn projection_baseline_repetition_preserves_separator_and_close_run() {
        use mettail_ast::types::CollectionType;

        for source in
            [None, Some(Box::new(PatternOp::Var(Ident::new("ignored", Span::call_site()))))]
        {
            let mut rule = infix_rule("Call", "Int", "Int", "!");
            rule.term_context = Some(vec![
                simple("a", "Int"),
                TermParam::Simple {
                    name: Ident::new("args", Span::call_site()),
                    ty: TypeExpr::Collection {
                        coll_type: CollectionType::Vec,
                        element: Box::new(TypeExpr::Base(Ident::new("Int", Span::call_site()))),
                    },
                },
            ]);
            rule.syntax_pattern = Some(vec![
                param("a"),
                lit("!"),
                lit("("),
                SyntaxExpr::Op(PatternOp::Sep {
                    collection: Ident::new("args", Span::call_site()),
                    separator: ",;".into(),
                    source,
                }),
                lit(")"),
                lit("end"),
            ]);
            let mut expected = projection_baseline_descriptor("Call", "!");
            expected.is_mixfix = true;
            expected.mixfix_parts = vec![MixfixPart {
                operand_category: "Int".into(),
                param_name: "args".into(),
                preceding_terminals: vec!["(".into()],
                following_terminals: Vec::new(),
                repetition: Some(MixfixRep {
                    separator: ",;".into(),
                    min: 0,
                    close: vec![")".into(), "end".into()],
                }),
                capture_kind: None,
            }];
            assert_projection_baseline(&rule, expected);
            // A nested collection is not a category operand for this classifier.
            if let TermParam::Simple {
                ty: TypeExpr::Collection { element, .. }, ..
            } = &mut rule
                .term_context
                .as_mut()
                .expect("test fixture contains its declared context or syntax")[1]
            {
                *element = Box::new(TypeExpr::Collection {
                    coll_type: CollectionType::Vec,
                    element: Box::new(TypeExpr::Base(Ident::new("Int", Span::call_site()))),
                });
            } else {
                panic!("fixture must contain a collection parameter");
            }
            assert!(classify_rule(&rule).is_none());
        }
    }

    #[test]
    fn projection_baseline_nullary_literals_and_postfix_flags() {
        let mut rule = postfix_rule("EmptyCall", "Int", "Int", "!");
        rule.is_right_assoc = true;
        rule.shares_level_with_previous = true;
        rule.syntax_pattern = Some(vec![param("a"), lit("!"), lit("("), lit(")")]);
        let mut expected = projection_baseline_descriptor("EmptyCall", "!");
        expected.is_mixfix = true;
        expected.shares_level_with_previous = true;
        expected.nullary_literals = vec!["(".into(), ")".into()];
        assert_projection_baseline(&rule, expected);

        rule.syntax_pattern = Some(vec![param("a"), lit("!")]);
        let mut expected = projection_baseline_descriptor("EmptyCall", "!");
        expected.is_postfix = true;
        // Original unary-postfix classification deliberately ignores right/same.
        assert_projection_baseline(&rule, expected);
    }

    #[test]
    fn projection_baseline_open_right_edge_and_same_precedence() {
        let mut rule = infix_rule("Tern", "Int", "Int", "?");
        rule.term_context = Some(vec![simple("a", "Int"), simple("b", "Int"), simple("c", "Int")]);
        rule.syntax_pattern = Some(vec![param("a"), lit("?"), param("b"), lit(":"), param("c")]);
        rule.is_right_assoc = true;
        rule.shares_level_with_previous = true;
        let mut expected = projection_baseline_descriptor("Tern", "?");
        expected.associativity = Associativity::Right;
        expected.shares_level_with_previous = true;
        expected.is_mixfix = true;
        expected.mixfix_parts = vec![
            MixfixPart {
                operand_category: "Int".into(),
                param_name: "b".into(),
                preceding_terminals: Vec::new(),
                following_terminals: vec![":".into()],
                repetition: None,
                capture_kind: None,
            },
            MixfixPart {
                operand_category: "Int".into(),
                param_name: "c".into(),
                preceding_terminals: Vec::new(),
                following_terminals: Vec::new(),
                repetition: None,
                capture_kind: None,
            },
        ];
        assert_projection_baseline(&rule, expected.clone());
        rule.syntax_pattern
            .as_mut()
            .expect("test fixture contains its declared context or syntax")
            .push(lit("end"));
        expected.associativity = Associativity::Left;
        expected.mixfix_parts[1]
            .following_terminals
            .push("end".into());
        assert_projection_baseline(&rule, expected);

        let mut binary = infix_rule("RightSame", "Int", "Int", "^");
        binary.is_right_assoc = true;
        binary.shares_level_with_previous = true;
        let mut expected = projection_baseline_descriptor("RightSame", "^");
        expected.associativity = Associativity::Right;
        expected.shares_level_with_previous = true;
        assert_projection_baseline(&binary, expected);
    }

    #[test]
    fn classifies_binary_infix_same_cat() {
        let rule = infix_rule("AddInt", "Int", "Int", "+");
        let info = classify_rule(&rule).expect("infix");
        assert_eq!(info.label, "AddInt");
        assert_eq!(info.terminal, "+");
        assert_eq!(info.category, "Int");
        assert_eq!(info.result_category, "Int");
        assert!(!info.is_cross_category);
        assert!(!info.is_postfix);
    }

    #[test]
    fn classifies_cross_cat_infix() {
        let rule = infix_rule("EqInt", "Bool", "Int", "==");
        let info = classify_rule(&rule).expect("cross-cat infix");
        assert_eq!(info.category, "Int");
        assert_eq!(info.result_category, "Bool");
        assert!(info.is_cross_category);
    }

    #[test]
    fn classifies_postfix() {
        let rule = postfix_rule("Fact", "Int", "Int", "!");
        let info = classify_rule(&rule).expect("postfix");
        assert!(info.is_postfix);
        assert_eq!(info.terminal, "!");
    }

    /// GEN-1 GAP-1 (2026-06-28): a HETEROGENEOUS-operand binary
    /// (`a:Int "+" b:Float`) is no longer DROPPED. It falls through from the
    /// binary-infix arm to `classify_postfix_mixfix` and is emitted as a mixfix
    /// whose LHS category is the FIRST operand (`Int`, the cross-cat source)
    /// with the second operand (`Float`) as a goal-bounded inner mixfix part.
    /// Previously `classify_rule` returned `None`, silently losing the rule's BP
    /// table entry, its lex-alt arm, AND its `cat_can_reach` edge — making the
    /// goal-gate non-conservative for heterogeneous casts (`e:Expr "as" t:Type`,
    /// `x satisfies T`). Audit §GAP-1; replaces the prior
    /// `rejects_mixed_operand_types` test that asserted the dropped behavior.
    #[test]
    fn heterogeneous_operand_binary_classifies_as_mixfix() {
        let mut rule = infix_rule("Mix", "Int", "Int", "+");
        rule.term_context = Some(vec![simple("a", "Int"), simple("b", "Float")]);
        let info = classify_rule(&rule).expect("heterogeneous binary now classifies (GAP-1)");
        assert_eq!(info.category, "Int", "LHS (first operand) is the cross-cat source category");
        assert_eq!(info.result_category, "Int");
        assert!(info.is_mixfix, "heterogeneous binary is emitted as a mixfix");
        assert!(
            info.mixfix_parts
                .iter()
                .any(|p| p.operand_category == "Float"),
            "the second (heterogeneous) operand becomes a goal-bounded inner mixfix part",
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // #141 G3 RED — the mixfix operand refusal SPEAKS, and names the RULE
    // ═══════════════════════════════════════════════════════════════════════
    //
    // Two defects at one site. (1) The refusal was a `panic!`, which prints
    // NOTHING inside a proc macro under this workspace's cranelift dev backend
    // (#141 RED-0) — so the message could not be read even when it fired. (2) The
    // message read "mixfix part `{}` of rule `{}`" and passed `rule_idx`, AN
    // INTEGER: even had it printed, `rule 0` names nothing a grammar author can
    // act on.
    //
    // ⚠ Neither cell expects a panic; both read the emitted tokens.

    /// A one-rule language whose heterogeneous binary `a:Int "+" b:<operand>`
    /// classifies as a mixfix, so the emitter resolves `<operand>`.
    fn mixfix_language(operand: &str) -> (LanguageDef, Vec<String>, Vec<Vec<GrammarRule>>) {
        let mut rule = infix_rule("Mix", "Int", "Int", "+");
        rule.term_context = Some(vec![simple("a", "Int"), simple("b", operand)]);
        let mut language = crate::gen::empty_language_for_tests();
        language.types.push(mettail_ast::language::LangType {
            name: Ident::new("Int", Span::call_site()),
            role: Default::default(),
            native_type: None,
            collection_kind: None,
        });
        language.terms.push(rule.clone());
        (language, vec!["Int".to_string()], vec![vec![rule]])
    }

    /// ★ THE MUTATION CELL. A mixfix operand naming an UNDECLARED category emits a
    /// `compile_error!` that names the category AND the rule's LABEL.
    #[test]
    fn an_undeclared_mixfix_operand_refuses_and_names_the_rule_label() {
        let (language, categories, per_cat) = mixfix_language("Ghost");
        let (control_language, _, _) = mixfix_language("Int");

        // The mutation is applied, and is the only difference.
        assert_ne!(
            format!("{:?}", language.terms[0].term_context),
            format!("{:?}", control_language.terms[0].term_context),
            "the two fixtures differ in exactly the OPERAND CATEGORY, which is what \
             this emitter resolves",
        );

        let rendered = emit_bp_tables(&language, &categories, &per_cat).to_string();

        assert!(
            rendered.contains("compile_error"),
            "an undeclared mixfix operand must REFUSE as a token rustc renders, not as \
             a panic the backend swallows. Got: {rendered}",
        );
        assert!(
            rendered.contains("Ghost"),
            "the diagnostic must name the CATEGORY it could not resolve. Got: {rendered}",
        );
        assert!(
            rendered.contains("`Mix`"),
            "★ and it must name the RULE BY LABEL. The message it replaces claimed to \
             name the rule and passed `rule_idx`, an integer — a position within \
             `per_cat[cat]`, which is an artefact of codegen ordering and names nothing \
             a grammar author can act on. Got: {rendered}",
        );
        assert!(
            rendered.contains("mixfix operand position"),
            "…and it must say WHERE, since one rule can name a category in several \
             positions. Got: {rendered}",
        );
    }

    /// ★ THE CONTROL that must NOT discriminate: a DECLARED operand still emits
    /// its table, with no diagnostic at all.
    #[test]
    fn a_declared_mixfix_operand_still_emits_its_table() {
        let (language, categories, per_cat) = mixfix_language("Int");
        let rendered = emit_bp_tables(&language, &categories, &per_cat).to_string();
        assert!(
            !rendered.contains("compile_error"),
            "an operand category the language declares must not be refused — otherwise \
             the cell above proves only that this emitter refuses everything. Got: \
             {rendered}",
        );
        assert!(
            rendered.contains("mixfix_part"),
            "and the mixfix part table must still be emitted. Got: {rendered}",
        );
    }
}
