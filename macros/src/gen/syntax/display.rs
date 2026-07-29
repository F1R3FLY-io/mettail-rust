// Pretty-printing generation for MeTTaIL languages
//
// This module generates trampolined (iterative, work-stack-based) Display trait
// implementations for AST types.  Instead of recursively calling
// `write!(f, "{}", child)` — which causes stack overflow for deeply nested
// terms — the generated code pushes `DisplayTask` variants onto an explicit
// work stack and processes them iteratively.
//
// Architecture mirrors `match_pattern.rs`: a heterogeneous `DisplayTask` enum
// with one variant per category, a thread-local `Cell<Vec<DisplayTask>>` pool,
// and a single `display_iterative` driver loop.

#![allow(clippy::cmp_owned)]

use crate::gen::capture::{capture_layout, CaptureFieldKind};
use crate::gen::native::has_native_type;
use crate::gen::syntax::parser::prattail_bridge::language_def_to_spec;
use crate::gen::{generate_literal_label, generate_var_label, is_literal_rule, is_var_rule};
use mettail_ast::{
    grammar::{GrammarItem, GrammarRule, NonTerminalKind, PatternOp, SyntaxExpr, TermParam},
    grammar_shapes::{classify_simple_projection_shape, classify_unary_prefix_shape},
    language::LanguageDef,
    types::TypeExpr,
};
use mettail_prattail::binding_power::{
    analyze_binding_powers, compute_prefix_bp, InfixRuleInfo, MixfixPart as BpMixfixPart,
};
use mettail_prattail::SyntaxItemSpec;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
// `VecDeque` was imported solely for `display_projection_reaches`'s BFS queue; that
// function is disabled with the rest of the projection-surface wrapper election
// (DEFECT 1, 2026-07-26 — see the block comment before its retained body). Dropped
// from the import list so the disabled block does not leave an unused import behind;
// restore it if that block is ever revived.
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

// =============================================================================
// FENCE CAPTURE — the delimiter analogue of precedence parenthesization
// =============================================================================
//
// A rule's surface template is a sequence of LITERAL tokens and CHILD slots.
// When the parser reaches a slot that is not an outermost Pratt operand it
// locates the slot's right edge LEXICALLY: it scans for the literal that
// follows the slot in the template — the slot's RIGHT FENCE. If the child's
// rendered text carries that fence at bracket depth 0, the parser stops inside
// the child and every token after that point is mis-assigned.
//
// `Display` therefore wraps such a child in PraTTaIL's TRANSPARENT `( … )`
// grouping. The full statement of the invariant, the proof that `(…)` is
// term-preserving and that the wrapped form is a canonical fixed point, and the
// two Rholang failures that motivated it live in
// `runtime/src/display_grouping.rs`.
//
// The helpers below derive each slot's fence set from the template alone — no
// per-rule or per-language special cases — and encode the two exclusions:
//
//   * PRECEDENCE-GOVERNED OPERANDS. In a rule that PraTTaIL registers as an
//     infix / prefix / postfix / mixfix operator, the LEADING slot's left edge
//     is owned by the Pratt loop, not by a lexical scan; Display already
//     parenthesizes it with `own_left_bp < min_bp`. Adding fence parentheses
//     there would be precedence-redundant, the next parse would drop them, and
//     the canonical form would oscillate — breaking one-cycle Display
//     idempotence. A slot with no literal immediately to its RIGHT has no fence
//     at all, which covers the trailing operand.
//
//     ⚠ The exclusion keys on BP REGISTRATION, not on template position alone.
//     A rule may start with a slot and still be fence-delimited: Rholang's
//     `InputBindPolyadic` is `lhs "," lhss.*sep(",") "<-" n` with no binding
//     power at all, and an `@`-quoted two-binder `new` in `lhs` rendered
//     `@new a0 , a1 in{…},a , a<-@Nil`, which does not parse. Excluding every
//     template-leading slot missed exactly that family
//     (`gen_rholang_prop::inputbind_display_parse_roundtrip`, 2026-07-25).
//
//   * VACUOUS BRACKET FENCES. The depth scan consumes `(`, `[`, `{` as depth
//     increments and `)`, `]`, `}` as decrements, so a bracket character is
//     never TESTED as a fence; on the balanced text Display always emits, a
//     bracket-initial fence can never match at depth 0. Skipping it statically
//     avoids materializing the child to a `String` for a guard that is a
//     constant `false`.

/// True when a depth-0 occurrence of `lit` is impossible in any balanced
/// rendered surface, so the fence guard would be a constant `false`.
fn fence_is_vacuous(lit: &str) -> bool {
    matches!(lit.chars().next(), None | Some('(' | ')' | '[' | ']' | '{' | '}'))
}

/// The right fence of the new-style syntax-pattern slot at index `i`, or `None`
/// when the slot needs no guard.
///
/// `rule_is_pratt` is `infix_info.is_some() || prefix_info.is_some()` for the
/// enclosing rule — the signal that its leading slot is an operand whose left
/// edge binding power owns (see the FENCE CAPTURE header).
fn syntax_fence_after(
    syntax_pattern: &[SyntaxExpr],
    i: usize,
    rule_is_pratt: bool,
) -> Option<String> {
    let template_leading = !syntax_pattern[..i]
        .iter()
        .any(|e| matches!(e, SyntaxExpr::Literal(_)));
    if rule_is_pratt && template_leading {
        return None;
    }
    match syntax_pattern.get(i + 1) {
        // Trailing-operand exclusion is implicit: no following element, or a
        // following non-literal, yields no fence.
        Some(SyntaxExpr::Literal(lit)) if !fence_is_vacuous(lit) => Some(lit.clone()),
        _ => None,
    }
}

/// The right fence of the old-style `GrammarItem` slot at index `i`. Same rule
/// as [`syntax_fence_after`], over `rule.items` instead of a syntax pattern.
fn item_fence_after(items: &[GrammarItem], i: usize, rule_is_pratt: bool) -> Option<String> {
    let template_leading = !items[..i]
        .iter()
        .any(|it| matches!(it, GrammarItem::Terminal(_)));
    if rule_is_pratt && template_leading {
        return None;
    }
    match items.get(i + 1) {
        Some(GrammarItem::Terminal(term)) if !fence_is_vacuous(term) => Some(term.clone()),
        _ => None,
    }
}

/// The `&[…]` slice literal of fence strings a generated `group_if_bare_delims`
/// call takes, or `None` when the fence set is empty (emit no guard).
///
/// `separator` is the `.*sep(S)` continuation fence — present only for
/// repetition elements, whose loop either CONTINUES on `S` or TERMINATES on the
/// following literal.
fn fence_slice_expr(separator: Option<&str>, fence: Option<&str>) -> Option<TokenStream> {
    let mut delims: Vec<String> = Vec::with_capacity(2);
    if let Some(sep) = separator {
        delims.push(sep.to_string());
    }
    match fence {
        Some(f) if !delims.iter().any(|d| d == f) => delims.push(f.to_string()),
        _ => {},
    }
    match delims.is_empty() {
        true => None,
        false => Some(quote! { &[#(#delims),*] }),
    }
}

// =============================================================================
// Main Entry Point
// =============================================================================

/// Binding power information for a single constructor in the Display context.
///
/// ★ #97: `pub(crate)` because the REFLECTION renderer
/// (`gen/runtime/metadata.rs`) parenthesizes from this same table. Two
/// precedence models — one for `Display`, one for the reflected equational
/// theory — could disagree about the very brackets an associativity law is
/// about, so there is one.
#[derive(Debug, Clone)]
pub(crate) struct DisplayBpInfo {
    /// Left binding power of this operator.
    pub(crate) left_bp: u8,
    /// Right binding power of this operator.
    pub(crate) right_bp: u8,
    /// Whether this is a postfix operator.
    pub(crate) is_postfix: bool,
    /// Whether this is a mixfix operator.
    pub(crate) is_mixfix: bool,
}

/// Binding power information for a unary prefix operator.
#[derive(Debug, Clone)]
pub(crate) struct DisplayPrefixBpInfo {
    /// Prefix binding power (child gets this as min_bp).
    pub(crate) prefix_bp: u8,
}

/// Lookup table for binding power information, keyed by constructor label.
#[derive(Debug, Clone)]
pub(crate) struct BpLookup {
    /// Infix/postfix/mixfix operators: label -> BP info.
    pub(crate) infix: HashMap<String, DisplayBpInfo>,
    /// Unary prefix operators: label -> prefix BP.
    pub(crate) prefix: HashMap<String, DisplayPrefixBpInfo>,
    /// Maximum Display binding power of constructors that produce each category.
    pub(crate) max_bp_by_category: HashMap<String, u8>,
}

impl BpLookup {
    pub(crate) fn empty() -> Self {
        BpLookup {
            infix: HashMap::new(),
            prefix: HashMap::new(),
            max_bp_by_category: HashMap::new(),
        }
    }

    pub(crate) fn atomic_child_bp(&self, category: &str) -> u8 {
        self.max_bp_by_category
            .get(category)
            .copied()
            .unwrap_or(0)
            .saturating_add(1)
    }
}

/// Build a `BpLookup` from a `LanguageDef`.
///
/// Converts the language definition to a spec, classifies rules, computes
/// binding powers, and builds a label-indexed lookup table for display codegen.
///
/// # Errors
///
/// Propagates the `LanguageDef → LanguageSpec` bridge's refusal (an `options`
/// value it cannot decode). Display shares that bridge with the parser generator,
/// so it shares the refusal rather than substituting an empty lookup: a
/// `BpLookup::empty()` fallback would silently emit a `Display` impl that
/// parenthesizes nothing correctly.
pub(crate) fn build_bp_lookup(language: &LanguageDef) -> Result<BpLookup, String> {
    let spec = language_def_to_spec(language)?;

    // Extract infix rules exactly as the pipeline does
    let infix_rules: Vec<InfixRuleInfo> = spec
        .rules
        .iter()
        .filter(|r| r.is_infix)
        .filter_map(|r| {
            let operand_category = r
                .cross_source_category
                .clone()
                .or_else(|| first_nonterminal_category_for_display(&r.syntax))
                .unwrap_or_else(|| r.category.clone());
            let (is_mixfix, mixfix_parts) = extract_mixfix_parts_for_display(&r.syntax);
            Some(InfixRuleInfo {
                label: r.label.clone(),
                terminal: r
                    .syntax
                    .iter()
                    .find_map(|item| {
                        if let SyntaxItemSpec::Terminal(t) = item {
                            Some(t.clone())
                        } else {
                            None
                        }
                    })
                    .unwrap_or_default(),
                category: operand_category.clone(),
                result_category: r.category.clone(),
                associativity: r.associativity,
                shares_level_with_previous: r.shares_level_with_previous,
                is_cross_category: r.is_cross_category || operand_category != r.category,
                is_postfix: r.is_postfix,
                is_mixfix,
                mixfix_parts,
                nullary_literals: Vec::new(),
            })
        })
        .collect();

    let bp_table = analyze_binding_powers(&infix_rules);

    // Stage 3.27d-pre (2026-04-30): prefix_bp now derives from
    // `compute_prefix_bp()` (single source of truth, queries bp_table directly).
    // The local max_infix_bp HashMap was removed.

    let mut lookup = BpLookup::empty();

    // Build a terminal→same-operand-category BP map so cross-category operators
    // can share a threshold with a same-category operator on the same operand
    // category when such a rule exists. The source category is the Pratt
    // competition domain for the operands; the result category is not.
    let mut same_cat_bp: HashMap<(String, String), (u8, u8)> = HashMap::new();
    for op in &bp_table.operators {
        if !op.is_cross_category {
            same_cat_bp
                .insert((op.terminal.clone(), op.category.clone()), (op.left_bp, op.right_bp));
        }
    }

    // Add infix/postfix/mixfix operators
    for op in &bp_table.operators {
        // For cross-category operators, use the same operand-category
        // operator's BP for parenthesization when available. If no same-token
        // source-category operator exists, keep the binding power assigned in
        // the source category by analyze_binding_powers().
        let (display_left_bp, display_right_bp) = if op.is_cross_category {
            same_cat_bp
                .get(&(op.terminal.clone(), op.category.clone()))
                .copied()
                .unwrap_or((op.left_bp, op.right_bp))
        } else {
            (op.left_bp, op.right_bp)
        };
        lookup.infix.insert(
            op.label.clone(),
            DisplayBpInfo {
                left_bp: display_left_bp,
                right_bp: display_right_bp,
                is_postfix: op.is_postfix,
                is_mixfix: op.is_mixfix,
            },
        );
        let own_bp = display_left_bp.max(display_right_bp);
        lookup
            .max_bp_by_category
            .entry(op.result_category.clone())
            .and_modify(|max_bp| *max_bp = (*max_bp).max(own_bp))
            .or_insert(own_bp);
    }

    // Add unary prefix operators (Stage 3.27d-pre standardized helper)
    for rule in &spec.rules {
        if rule.is_unary_prefix {
            let prefix_bp = compute_prefix_bp(&rule.category, rule.prefix_precedence, &bp_table);
            lookup
                .prefix
                .insert(rule.label.clone(), DisplayPrefixBpInfo { prefix_bp });
            lookup
                .max_bp_by_category
                .entry(rule.category.clone())
                .and_modify(|max_bp| *max_bp = (*max_bp).max(prefix_bp))
                .or_insert(prefix_bp);
        }
    }

    Ok(lookup)
}

fn first_nonterminal_category_for_display(syntax: &[SyntaxItemSpec]) -> Option<String> {
    syntax.iter().find_map(|item| {
        if let SyntaxItemSpec::NonTerminal { category, .. } = item {
            Some(category.clone())
        } else {
            None
        }
    })
}

/// Extract mixfix parts from syntax items (same logic as pipeline.rs).
fn extract_mixfix_parts_for_display(syntax: &[SyntaxItemSpec]) -> (bool, Vec<BpMixfixPart>) {
    let operand_count = syntax
        .iter()
        .filter(|item| matches!(item, SyntaxItemSpec::NonTerminal { .. }))
        .count();
    let terminal_count = syntax
        .iter()
        .filter(|item| matches!(item, SyntaxItemSpec::Terminal(_)))
        .count();

    if operand_count < 3 || terminal_count < 2 {
        return (false, Vec::new());
    }

    let mut parts = Vec::with_capacity(operand_count - 1);
    let mut after_trigger = false;
    let mut skip_count = 0;

    for item in syntax {
        match item {
            SyntaxItemSpec::NonTerminal { .. } if skip_count == 0 => {
                skip_count += 1;
            },
            SyntaxItemSpec::Terminal(_) if !after_trigger => {
                after_trigger = true;
            },
            SyntaxItemSpec::NonTerminal { category, param_name } if after_trigger => {
                parts.push(BpMixfixPart {
                    operand_category: category.clone(),
                    param_name: param_name.clone(),
                    preceding_terminals: Vec::new(),
                    following_terminals: Vec::new(),
                    repetition: None,
                    // #131: Display's parts feed `build_bp_lookup`, which uses them
                    // ONLY to decide precedence-aware parenthesization. A capture part
                    // renders one token and can never need parentheses, so the bp view
                    // is unchanged by the distinction.
                    capture_kind: None,
                });
            },
            SyntaxItemSpec::Terminal(t) if after_trigger => {
                // L12 follow-up B6 (2026-05-07): append literal to the
                // last part's following_terminals vec for postfix-mixfix
                // support (consecutive literals between operands).
                if let Some(last_part) = parts.last_mut() {
                    last_part.following_terminals.push(t.clone());
                }
            },
            _ => {},
        }
    }

    (true, parts)
}

/// Generate trampolined Display implementations for all exported categories.
///
/// Produces:
/// 1. `DisplayTask` enum with one variant per category + literal/string helpers
/// 2. `DISPLAY_TASK_POOL` thread-local for zero-allocation steady-state
/// 3. `display_iterative()` driver loop
/// 4. `impl Display for Cat` delegating to the iterative engine
///
/// # Errors
///
/// Propagates [`build_bp_lookup`]'s refusal — an `options` value the shared
/// `LanguageDef → LanguageSpec` bridge cannot decode.
pub fn generate_display(language: &LanguageDef) -> Result<TokenStream, String> {
    // Compute binding power lookup for precedence-aware parenthesization
    let bp_lookup = build_bp_lookup(language)?;

    // ★ SURFACE SYNONYMY (2026-07-26). Derived from the grammar's own fold bodies and grouping
    // shapes; see `synonymy.rs` for the defect, the two refuted inference rules, and why the
    // canonical member has to be DECLARED. `compile_errors` is the loud build gate: a new
    // interchangeable surface stops the build until the grammar names its canonical member.
    let synonymy = crate::gen::syntax::synonymy::derive(language);
    let synonymy_errors = crate::gen::syntax::synonymy::compile_errors(language, &synonymy);
    let synonymy_table = crate::gen::syntax::synonymy::gate_table(language, &synonymy);

    let task_enum = generate_display_task_enum(language);
    let iterative_engine = generate_iterative_engine(language, &bp_lookup, &synonymy);
    let display_impls = generate_display_impls(language);
    let at_sigil_wrap_predicate = generate_at_sigil_wrap_predicate(language);

    Ok(quote! {
        #synonymy_errors
        #synonymy_table
        #task_enum
        #iterative_engine
        #display_impls
        #at_sigil_wrap_predicate
    })
}

// =============================================================================
// DisplayTask Enum + TLS Pool
// =============================================================================

/// Generate the `DisplayTask` enum and thread-local pool.
fn generate_display_task_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Display{}", cat);
            quote! {
                #variant_name(*const #cat, u8)
            }
        })
        .collect();

    quote! {
        /// Work item for the iterative Display engine.
        ///
        /// Each category variant wraps a raw pointer to a term to be displayed,
        /// plus a `min_bp` (minimum binding power) for precedence-aware
        /// parenthesization.  When an infix operator's own `left_bp` is less
        /// than the inherited `min_bp`, the operator wraps its output in `(…)`.
        /// `WriteLiteral` and `WriteString` variants handle static and dynamic
        /// text fragments (separators, delimiters, variable names, etc.) that do
        /// not require recursive descent into child terms.
        #[allow(dead_code)]
        enum DisplayTask {
            #(#variants,)*
            /// Write a compile-time-known string (separator, delimiter, keyword).
            WriteLiteral(&'static str),
            /// Write a dynamically computed string (variable name, formatted value).
            WriteString(String),
        }

        thread_local! {
            /// Pool for reusing `DisplayTask` work stacks across Display calls.
            ///
            /// The `Cell<Vec<DisplayTask>>` pattern allows zero-allocation
            /// steady-state operation: the first call allocates, subsequent
            /// calls reuse the same buffer. Re-entrant calls (e.g. from
            /// collection element formatting) get fresh vectors; the outermost
            /// call retains capacity.
            static DISPLAY_TASK_POOL: std::cell::Cell<Vec<DisplayTask>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

// =============================================================================
// Iterative Engine
// =============================================================================

/// Generate the `display_iterative` function that processes the work stack.
/// **Frame-size fix (residual #11-2, 2026-07-14):** each category's variant
/// match is peeled into a `#[inline(never)] display_visit_<cat>` helper (the
/// Tier-1 idiom `normalize_iterative` uses). Without it, `display_iterative`'s
/// -O0 frame is the alloca SUM of every category's variant locals (measured
/// 385,544 B for rholang). Helpers return `std::fmt::Result`, so the `?` writes
/// inside the arms propagate through them and the dispatch arm re-propagates
/// with `?` — control-flow-equivalent (the only generated escapes are `?` and
/// arm-local `break value` loops; no `return`/`continue` cross an arm).
fn generate_iterative_engine(
    language: &LanguageDef,
    bp_lookup: &BpLookup,
    synonymy: &crate::gen::syntax::synonymy::SynonymyModel,
) -> TokenStream {
    let visit_helper_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            generate_display_visit_helper(&lang_type.name, language, bp_lookup, synonymy)
        })
        .collect();
    let category_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_engine_category_dispatch(&lang_type.name))
        .collect();

    quote! {
        #(#visit_helper_fns)*

        /// Iterative Display engine.
        ///
        /// Pops tasks from the work stack and either writes text directly to
        /// the formatter or pushes sub-tasks for child terms.  Stack-safe for
        /// arbitrarily deep terms.
        #[allow(dead_code)]
        fn display_iterative(
            stack: &mut Vec<DisplayTask>,
            f: &mut std::fmt::Formatter,
        ) -> std::fmt::Result {
            while let Some(task) = stack.pop() {
                match task {
                    DisplayTask::WriteLiteral(s) => {
                        f.write_str(s)?;
                    }
                    DisplayTask::WriteString(s) => {
                        f.write_str(&s)?;
                    }
                    #(#category_arms)*
                }
            }
            Ok(())
        }
    }
}

/// Emit the thin dispatch arm that delegates to the per-category
/// `#[inline(never)] display_visit_<cat>` helper (residual #11-2).
fn generate_engine_category_dispatch(category: &syn::Ident) -> TokenStream {
    let task_variant = format_ident!("Display{}", category);
    let helper_fn = format_ident!("display_visit_{}", category.to_string().to_lowercase());
    quote! {
        DisplayTask::#task_variant(ptr, min_bp) => {
            #helper_fn(stack, f, ptr, min_bp)?;
        }
    }
}

/// Emit the per-category `#[inline(never)] display_visit_<cat>` helper (residual
/// #11-2). Builds every variant arm (grammar rules + auto var/literal + the
/// synthetic HOL lam/apply variants) and wraps them in the helper fn so their
/// -O0 locals live in the helper frame, not in `display_iterative`.
///
/// For each variant of the category, we generate code that either:
/// - Writes text directly (literals, vars, nullary constructors)
/// - Pushes sub-tasks in REVERSE order for child terms (stack is LIFO)
fn generate_display_visit_helper(
    category: &syn::Ident,
    language: &LanguageDef,
    bp_lookup: &BpLookup,
    synonymy: &crate::gen::syntax::synonymy::SynonymyModel,
) -> TokenStream {
    let helper_fn = format_ident!("display_visit_{}", category.to_string().to_lowercase());

    // Group rules by category for lookup
    let mut rules_by_cat: HashMap<String, Vec<&GrammarRule>> = HashMap::new();
    for rule in &language.terms {
        let cat_name = rule.category.to_string();
        rules_by_cat.entry(cat_name).or_default().push(rule);
    }

    let rules = rules_by_cat
        .get(&category.to_string())
        .map(|v| v.as_slice())
        .unwrap_or(&[]);

    // ★ SURFACE SYNONYMY (2026-07-26) — route each member of a synonymy class through the
    // class's DECLARED canonical member, and render an INERT GROUPING transparently. Both are
    // no-ops for a grammar that declares neither, so an unaffected language's arms are
    // byte-identical. See `synonymy.rs`.
    let by_label: HashMap<String, &GrammarRule> = language
        .terms
        .iter()
        .map(|r| (r.label.to_string(), r))
        .collect();

    // Generate match arms for grammar-defined rules
    let mut variant_arms: Vec<TokenStream> = rules
        .iter()
        .map(|rule| {
            let label = rule.label.to_string();
            // ★ MEASURED REFUTATION (2026-07-26) — an INERT GROUPING IS NOT DISPLAY-COLLAPSED.
            //
            // The first cut of surface synonymy also rendered inert groupings transparently
            // (`NParen(x)` ⇒ `Display(x)` at the inherited threshold), on the reasoning that
            // `Grouping(x) ≡ x` makes the brackets redundant. Two independent standing contracts
            // REFUTED it, and both are about AMBIGUITY PRESERVATION rather than about brackets:
            //
            //   languages/tests/rd_a1_budget.rs::genuinely_ambiguous_witness_strict_boundary
            //       `@((a)!(0))!()` has |R|_distinct = 2, and the two readings differ ONLY by
            //       the kept `NParen`. Transparency displayed both as `@(a!(0))!()`, so the
            //       distinct-reading count collapsed 2 → 1 and the budget boundary moved.
            //   languages/tests/rholang_tests.rs::realize_mode_contract_pins
            //       ::prefix_bounded_alternatives_enumerate_display_distinct_family (2026-07-14,
            //       USER-APPROVED) requires `@Nil!(@(@Nil)!())` and `@Nil!(@@Nil!())` to remain
            //       a display-DISTINCT 2-reading family. Transparency made both `@Nil!(@@Nil!())`.
            //
            // So a grouping's brackets are the ONLY observable separating the kept-grouping
            // reading from its transparent twin; deleting them from the surface DISAMBIGUATES AT
            // THE DISPLAY LAYER, which this project forbids. The property surface synonymy needs
            // — `Display(Parse(Display(t))) == Display(t)` — is measured to hold for the grouping
            // ALREADY (`(@Nil)` ⇒ `(@Nil)`), because the parser re-elects the grouping from its
            // own brackets. There is therefore nothing to repair here and a reading to lose, so
            // the grouping keeps its own arm. It is still REPORTED in the gate table
            // (`__SURFACE_INERT_GROUPINGS`) and the shared harness asserts its stability.
            let _ = &synonymy.inert_groupings;
            if let Some(plan) = synonymy.reroutes.get(&label) {
                if let Some(canonical_rule) = by_label.get(&plan.canonical) {
                    let synthetic =
                        crate::gen::syntax::synonymy::rerouted_rule(canonical_rule, plan);
                    return generate_engine_rule_arm_as(
                        &synthetic,
                        &rule.label,
                        language,
                        bp_lookup,
                    );
                }
            }
            generate_engine_rule_arm(rule, language, bp_lookup)
        })
        .collect();

    // Auto-generated Var variant
    let has_var_rule = rules.iter().any(|rule| is_var_rule(rule));
    if !has_var_rule {
        variant_arms.push(generate_engine_auto_var_arm(category));
    }

    // Auto-generated Literal variant
    let has_literal_rule = rules.iter().any(|rule| is_literal_rule(rule));
    if let Some(native_type) = has_native_type(category, language) {
        if !has_literal_rule {
            // For collection-kind categories (![Vec<T>] / ![HashBag<T>] /
            // ![HashMap<K,V>] as Cat), thread the collection delimiters so
            // Display matches the parser-expected surface syntax
            // (`list(...)`, `bag(...)`, `map(k:v, ...)`) — merge plan B.1.
            let collection_kind = language
                .types
                .iter()
                .find(|t| &t.name == category)
                .and_then(|t| t.collection_kind.as_ref());
            // Divergence I / Stage C: the mandatory literal tail declared by this
            // category's own `literals { }` pattern (`BigInt`'s `…n`), derived from
            // the grammar rather than hardcoded per language.
            let payload_is_signed = !matches!(
                crate::gen::native::NativeType::from_syn_type(native_type),
                crate::gen::native::NativeType::UInt8
                    | crate::gen::native::NativeType::UInt16
                    | crate::gen::native::NativeType::UInt32
                    | crate::gen::native::NativeType::UInt64
                    | crate::gen::native::NativeType::UInt128
                    | crate::gen::native::NativeType::Usize
            );
            let category_has_unary_minus = category_has_unary_minus_rule(language, category);
            let mandatory_literal_tail = language
                .token_defs
                .iter()
                .find(|td| td.from_literals && td.category.as_ref().is_some_and(|c| c == category))
                .and_then(|td| {
                    mandatory_literal_tail_of_pattern(
                        &td.pattern,
                        payload_is_signed,
                        category_has_unary_minus,
                    )
                });
            variant_arms.push(generate_engine_auto_literal_arm(
                category,
                native_type,
                collection_kind,
                mandatory_literal_tail,
            ));
        }
    }

    // Auto-generated lambda/apply variants — post-HOL-B: only for
    // (category, domain) pairs flagged by `compute_hol_domain_pairs`.
    let hol_pairs = crate::logic::common::compute_hol_domain_pairs(language);
    let category_str_disp = category.to_string();
    for domain_lang_type in &language.types {
        let domain_name = &domain_lang_type.name;

        if !hol_pairs.contains(&(category_str_disp.clone(), domain_name.to_string())) {
            continue;
        }

        // LamDomain
        let lam_variant = format_ident!("Lam{}", domain_name);
        let body_task_variant = format_ident!("Display{}", category);
        variant_arms.push(quote! {
            #category::#lam_variant(scope) => {
                let inner = scope.inner();
                let var_name = inner.unsafe_pattern.0.pretty_name.as_deref().unwrap_or("?").to_string();
                // Push in reverse: "^" name ".{" body "}"
                stack.push(DisplayTask::WriteLiteral("}"));
                stack.push(DisplayTask::#body_task_variant(&*inner.unsafe_body as *const _, 0));
                stack.push(DisplayTask::WriteLiteral(".{"));
                stack.push(DisplayTask::WriteString(var_name));
                stack.push(DisplayTask::WriteLiteral("^"));
            }
        });

        // MLamDomain
        let mlam_variant = format_ident!("MLam{}", domain_name);
        variant_arms.push(quote! {
            #category::#mlam_variant(scope) => {
                let inner = scope.inner();
                let names: Vec<_> = inner.unsafe_pattern.iter()
                    .map(|b| b.0.pretty_name.as_deref().unwrap_or("?").to_string())
                    .collect();
                // Push in reverse: "^[" names "].{" body "}"
                stack.push(DisplayTask::WriteLiteral("}"));
                stack.push(DisplayTask::#body_task_variant(&*inner.unsafe_body as *const _, 0));
                stack.push(DisplayTask::WriteLiteral("].{"));
                stack.push(DisplayTask::WriteString(names.join(",")));
                stack.push(DisplayTask::WriteLiteral("^["));
            }
        });

        // ApplyDomain
        let apply_variant = format_ident!("Apply{}", domain_name);
        let domain_lower = domain_name.to_string().to_lowercase();
        let arg_task_variant = format_ident!("Display{}", domain_name);
        let apply_prefix: String = format!("${}(", domain_lower);
        variant_arms.push(quote! {
            #category::#apply_variant(lam, arg) => {
                // Push in reverse: "$domain(" lam ", " arg ")"
                stack.push(DisplayTask::WriteLiteral(")"));
                stack.push(DisplayTask::#arg_task_variant(&**arg as *const _, 0));
                stack.push(DisplayTask::WriteLiteral(", "));
                stack.push(DisplayTask::#body_task_variant(&**lam as *const _, 0));
                stack.push(DisplayTask::WriteString(#apply_prefix.to_string()));
            }
        });

        // MApplyDomain
        let mapply_variant = format_ident!("MApply{}", domain_name);
        let mapply_prefix: String = format!("$${}", domain_lower);
        variant_arms.push(quote! {
            #category::#mapply_variant(lam, args) => {
                // Each arg is pushed as a separate Display task so the
                // iterative driver traverses them without recursion — the
                // previous inline `.to_string()` call on each arg re-entered
                // Display at an arbitrary depth determined by the arg's
                // subtree, which was a stack-overflow hazard for deep args.
                // Layout: "$$domain" "(" lam [", " arg_0 ... ", " arg_{n-1}] ")"
                stack.push(DisplayTask::WriteLiteral(")"));
                // Push args in reverse order so arg_0 is processed first (LIFO).
                // `args` is `Vec<ArgCat>` (not boxed); iter() yields `&ArgCat`
                // which can be cast directly to `*const _`.
                for (i, arg) in args.iter().enumerate().rev() {
                    stack.push(DisplayTask::#arg_task_variant(arg as *const _, 0));
                    // Comma comes BEFORE each arg (after `lam` for arg_0, after
                    // previous arg for arg_i). With reverse iteration, push the
                    // comma AFTER the arg in stack order so it prints BEFORE.
                    stack.push(DisplayTask::WriteLiteral(", "));
                    let _ = i;
                }
                stack.push(DisplayTask::#body_task_variant(&**lam as *const _, 0));
                stack.push(DisplayTask::WriteLiteral("("));
                stack.push(DisplayTask::WriteString(#mapply_prefix.to_string()));
            }
        });
    }

    // PRE-PEEL body (residual #11-2, 2026-07-14): the variant match inlined the
    // whole category into `display_iterative`. Commented-out-never-deleted; the
    // match now lives in the `#[inline(never)] display_visit_<cat>` helper below
    // and `generate_engine_category_dispatch` emits the thin call arm.
    /*
    quote! {
        DisplayTask::#task_variant(ptr, min_bp) => {
            // SAFETY: ptr was derived from a &Cat reference within the same
            // fmt() call; the referent is alive for the entire duration.
            let term = unsafe { &*ptr };
            // Suppress unused warning for non-operator variants.
            let _ = min_bp;
            match term {
                #(#variant_arms,)*
            }
        }
    }
    */
    // Frame-bound constraint: peel the category's variant match into a local-free
    // `#[inline(never)]` helper returning `std::fmt::Result` (the `?` writes
    // propagate through it; the dispatch arm re-propagates with `?`).
    quote! {
        #[inline(never)]
        #[allow(dead_code, unused_variables, non_snake_case)]
        fn #helper_fn(
            stack: &mut Vec<DisplayTask>,
            f: &mut std::fmt::Formatter,
            ptr: *const #category,
            min_bp: u8,
        ) -> std::fmt::Result {
            // SAFETY: ptr was derived from a &Cat reference within the same
            // fmt() call; the referent is alive for the entire duration.
            let term = unsafe { &*ptr };
            // Suppress unused warning for non-operator variants.
            let _ = min_bp;
            match term {
                #(#variant_arms,)*
            }
            Ok(())
        }
    }
}

// =============================================================================
// Per-Rule Arm Generation (for the iterative engine)
// =============================================================================

// ★ COMMENTED OUT, NOT DELETED (2026-07-26) — the INERT-GROUPING transparency arm, refuted by
// measurement. See the two contracts named at the call site in `generate_display_visit_helper`:
// a grouping's brackets are the ONLY observable separating the kept-grouping reading from its
// transparent twin, so collapsing them disambiguates at the display layer. The code is retained
// verbatim so a future design that wants transparency (behind a per-rule declaration, say) does
// not have to re-derive it, and so the refutation is legible next to what it refuted.
//
// /// ★ SURFACE SYNONYMY (2026-07-26) — the INERT-GROUPING arm.
// ///
// /// A grouping rule (`NParen . n:Name |- "(" n ")" : Name ![{ n.clone() }] fold;`) evaluates to
// /// its child unchanged, so `Grouping(x)` and `x` are the same term with two surfaces. There is
// /// no second RULE to nominate as canonical — the canonical member is the WRAPPED TERM — so the
// /// arm forwards the child at the INHERITED threshold `min_bp` and writes no brackets of its own.
// ///
// /// Forwarding `min_bp` rather than `0` is the whole point: the child is now standing exactly
// /// where the grouping stood, so it inherits the grouping's precedence obligation, and the child's
// /// own `own_bp < min_bp` test re-inserts brackets whenever the surrounding context needs them.
// /// The fence machinery (see this file's header) does the same for lexical fences. A grouping can
// /// therefore never be dropped in a position where its absence would change the parse.
// fn generate_inert_grouping_arm(rule: &GrammarRule) -> TokenStream {
//     let category = &rule.category;
//     let label = &rule.label;
//     let child_category = rule
//         .term_context
//         .as_ref()
//         .and_then(|tc| tc.first())
//         .and_then(|p| match p {
//             TermParam::Simple { ty: TypeExpr::Base(c), .. } => Some(c.clone()),
//             _ => None,
//         })
//         .unwrap_or_else(|| category.clone());
//     let task_variant = format_ident!("Display{}", child_category);
//     quote! {
//         #category::#label(__inner) => {
//             // Transparent: the child inherits this position's binding-power obligation.
//             stack.push(DisplayTask::#task_variant(&**__inner as *const _, min_bp));
//         }
//     }
// }

/// Generate the match arm for `rule`, but matching on the variant `match_label` instead of the
/// rule's own label.
///
/// ★ SURFACE SYNONYMY (2026-07-26). This is how a synonymy class renders through its DECLARED
/// canonical member: `rule` is the canonical rule (with its `term_context` already permuted into
/// the member's field order by `synonymy::rerouted_rule`), and `match_label` is the member being
/// rendered. The emitted arm therefore binds `Member(f₀ … fₙ)` and prints the CANONICAL surface.
///
/// The canonical rule's binding-power registration travels with it — `bp_lookup` is consulted
/// with the CANONICAL label, which is correct precisely because the surface being printed is the
/// canonical one, so the parenthesization obligation is the canonical one too. (`NQuoteShort`
/// carries `prefix(220)`, so `Name::NQuote(Add(1, 2))` prints `@(1 + 2)` and
/// `Name::NQuote(PZero)` prints `@Nil` — the bracket appears exactly when the operand binds
/// looser than the sigil, which is the same condition the parser applies.)
fn generate_engine_rule_arm_as(
    rule: &GrammarRule,
    match_label: &syn::Ident,
    language: &LanguageDef,
    bp_lookup: &BpLookup,
) -> TokenStream {
    if let (Some(syntax_pattern), Some(term_context)) = (&rule.syntax_pattern, &rule.term_context) {
        return generate_engine_syntax_pattern_arm_inner(
            rule,
            syntax_pattern,
            term_context,
            language,
            bp_lookup,
            Some(match_label),
        );
    }
    // A canonical member with no `syntax_pattern` has no surface to route through; fall back to
    // the member's own arm rather than emit an ill-typed one.
    generate_engine_rule_arm(rule, language, bp_lookup)
}

/// Generate the match arm for a single grammar rule inside the iterative engine.
fn generate_engine_rule_arm(
    rule: &GrammarRule,
    language: &LanguageDef,
    bp_lookup: &BpLookup,
) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    // New syntax_pattern rules
    if let (Some(syntax_pattern), Some(term_context)) = (&rule.syntax_pattern, &rule.term_context) {
        return generate_engine_syntax_pattern_arm(
            rule,
            syntax_pattern,
            term_context,
            language,
            bp_lookup,
        );
    }

    // Old-style binder rules
    if !rule.bindings.is_empty() {
        return generate_engine_binder_arm(rule, language);
    }

    // Collect field names and their types
    let fields: Vec<(String, Option<&syn::Ident>)> = rule
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| match item {
            GrammarItem::NonTerminal { ident, .. } => Some((format!("f{}", i), Some(ident))),
            GrammarItem::Collection { .. } => Some((format!("f{}", i), None)),
            _ => None,
        })
        .collect();

    if fields.is_empty() {
        // Nullary: write terminals directly
        let output = format_terminals(rule);
        quote! {
            #category::#label => {
                f.write_str(#output)?;
            }
        }
    } else {
        let field_names: Vec<syn::Ident> = fields
            .iter()
            .map(|(name, _)| syn::Ident::new(name, proc_macro2::Span::call_site()))
            .collect();

        // Check if any field is Var
        let has_var = fields.iter().any(|(_, nt_opt)| {
            nt_opt.as_ref().is_some_and(|nt| {
                NonTerminalKind::classify(&nt.to_string()) == NonTerminalKind::Var
            })
        });

        if has_var {
            generate_engine_var_fields_arm(rule, &fields, &field_names, bp_lookup)
        } else {
            generate_engine_regular_arm(rule, &fields, &field_names, language, bp_lookup)
        }
    }
}

/// Generate arm for rules with Var fields (old syntax).
/// Var fields write their name directly, non-Var fields push DisplayTask.
fn generate_engine_var_fields_arm(
    rule: &GrammarRule,
    fields: &[(String, Option<&syn::Ident>)],
    field_names: &[syn::Ident],
    _bp_lookup: &BpLookup,
) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    // Build list of push operations in reverse order.
    // We construct a forward list first, then reverse.
    let mut forward_ops: Vec<TokenStream> = Vec::new();
    let mut field_iter = fields.iter().zip(field_names.iter());

    for item in &rule.items {
        match item {
            GrammarItem::Terminal(term) => {
                let escaped = term.clone();
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(#escaped.to_string()));
                });
            },
            GrammarItem::NonTerminal { kind: NonTerminalKind::Var, .. } => {
                if let Some((_, field_name)) = field_iter.next() {
                    forward_ops.push(quote! {
                        stack.push(DisplayTask::WriteString(
                            match &(#field_name).0 {
                                mettail_runtime::Var::Free(fv) => fv.pretty_name.as_ref().map(|s| s.to_string()).unwrap_or_else(|| "_".to_string()),
                                mettail_runtime::Var::Bound(bv) => bv.pretty_name.as_ref().map(|s| s.to_string()).unwrap_or_else(|| "_".to_string()),
                            }
                        ));
                    });
                }
            },
            GrammarItem::NonTerminal { ident: nt, .. } => {
                if let Some((_, field_name)) = field_iter.next() {
                    let nt_str = nt.to_string();
                    // Find which category this nonterminal belongs to
                    let task_variant = format_ident!("Display{}", nt_str);
                    forward_ops.push(quote! {
                        stack.push(DisplayTask::#task_variant(&**#field_name as *const _, 0));
                    });
                }
            },
            _ => {},
        }
    }

    // Reverse the ops so stack processes them left-to-right
    forward_ops.reverse();

    quote! {
        #category::#label(#(#field_names),*) => {
            #(#forward_ops)*
        }
    }
}

/// True for a rule whose printed surface is exactly one child term.
///
/// Such rules are display-transparent: the wrapper itself contributes no
/// delimiter, keyword, or operator that could isolate the child from the
/// surrounding parse context.  They must therefore forward the inherited
/// binding-power threshold instead of resetting it to zero.
fn is_syntaxless_single_child_projection(rule: &GrammarRule) -> bool {
    if simple_projection_shape_for_display(rule).is_some() {
        return true;
    }
    // DEFECT 1 (2026-07-26): `simple_projection_shape_for_display` excludes
    // AUTO-INJECTED rules, because the projection-SURFACE arm (now disabled — see
    // the block comment above `find_projection_surface_wrapper`) used to claim them
    // before this path was ever consulted. With that arm gone an auto-injected
    // cross-category projection must take the SAME `atomic_child_bp` route as an
    // explicit one, or it would render its source bare at every threshold and lose
    // its bracketing in operand position.
    //
    // Every auto-injected projection `auto_inject.rs` emits carries a
    // `syntax_pattern`, so it is routed to `generate_engine_syntax_pattern_arm`
    // (whose own `forwards_projection_param` path already covers it) rather than
    // here. This arm closes the corresponding hole on the OLD-STYLE, items-only
    // path so the two generators agree by construction instead of by coincidence.
    rule.is_auto_injected
        && classify_simple_projection_shape(rule)
            .is_some_and(|shape| shape.source_category != shape.target_category)
}

fn simple_projection_shape_for_display(rule: &GrammarRule) -> Option<(String, String)> {
    if rule.is_auto_injected {
        return None;
    }
    if let Some(shape) = classify_simple_projection_shape(rule) {
        return Some((shape.source_category, shape.target_category));
    }
    if rule.items.len() == 1 && rule.bindings.is_empty() && rule.syntax_pattern.is_none() {
        if let Some(GrammarItem::NonTerminal { ident, .. }) = rule.items.first() {
            let source = ident.to_string();
            let target = rule.category.to_string();
            if source != target {
                return Some((source, target));
            }
        }
    }
    None
}

// DISABLED 2026-07-26 (DEFECT 1) — `single_base_param` had exactly one caller,
// `find_projection_surface_wrapper`, where it read the borrowed rule's sole base
// parameter. With that election disabled it has no remaining use. Retained verbatim,
// not deleted, so the disabled block below reads as written.
//
// fn single_base_param(rule: &GrammarRule) -> Option<(String, String)> {
//     let tc = rule.term_context.as_ref()?;
//     if tc.len() != 1 {
//         return None;
//     }
//     let TermParam::Simple { name, ty } = &tc[0] else {
//         return None;
//     };
//     let TypeExpr::Base(cat) = ty else {
//         return None;
//     };
//     Some((name.to_string(), cat.to_string()))
// }

// ════════════════════════════════════════════════════════════════════════════
// DISABLED 2026-07-26 — THE PROJECTION-SURFACE WRAPPER ELECTION (DEFECT 1)
// ════════════════════════════════════════════════════════════════════════════
//
// The block below (`display_projection_reaches`, `find_projection_surface_wrapper`,
// `is_delimited_projection_surface_pattern`, `simple_literal_param_pattern_ops`, and
// the three arm builders that consumed them) rendered a CROSS-CATEGORY PROJECTION
// operand at `min_bp > 0` by BORROWING the first delimited single-base-param rule of
// the target category and re-emitting that rule's own surface around the source term.
//
// The intent was legitimate and is recorded in the commit that introduced it
// (`641caeb5`, "projection-shadowed operands parenthesize"): a projection is
// display-transparent, so an operator-rooted source term placed bare in an operand
// slot fuses with the surrounding operator and the bracketing is lost.
//
// THE DEFECT: the borrowed rule is a REAL CONSTRUCTOR, so the rendered text does not
// denote the term. Measured on rholang, where the election lands on
// `POutputNil . q:Proc |- "@" "Nil" "!" "(" q ")"` — a SEND:
//
//     Add(CastInt 1, CastInt 2)  ─display→  "@Nil!(1) + @Nil!(2)"
//                                ─parse──→  Add(POutputNil 1, POutputNil 2)
//
// Two integers went in; two sends on the null-process channel came out. The same
// election on calculator lands on `BigratCast . a:Proc |- "bigrat" "(" a ")"`, so
// `IntToBigRat(AddInt(1,2))` rendered `bigrat(1 + 2)` and reparsed as a `BigratCast`
// over `Proc`. Neither language's display was term-preserving in operand position.
//
// It also could not be repaired in place: no rule of the target category can serve as
// a pure bracket, because every rule of the target category MEANS something.
//
// THE REPLACEMENT is the mechanism this file already had, one layer down — the
// `forwards_projection_min_bp` / `forwards_projection_param` path, which renders the
// source at `BpLookup::atomic_child_bp(source_cat) = max_bp(source_cat) + 1`. That
// threshold is above every operator of the source category, so the SOURCE's own
// precedence logic emits `WriteLiteral("(")` / `WriteLiteral(")")` — the language's
// pure, inert grouping form, which carries no rule of its own and therefore denotes
// nothing (`languages/tests/calculator_grouping_is_inert.rs` pins
// `C::parse(E).is_ok() ⟺ C::parse("(" ++ E ++ ")").is_ok()` for every category, and
// `emit_paren_dispatch_arms` in `macros/src/gen/runtime/wpda_codegen/prefix.rs` emits
// the `(`-grouping dispatch for every category, so no category lacks the form).
//
// Because the threshold is consulted per-term rather than applied blanketly, a
// SELF-DELIMITING source (an atom, a variable, a bracketed collection literal, a
// keyword-led call such as `Set( … )` or `int(a, 32)`) emits no parentheses at all —
// so `Add(CastInt 1, CastInt 2)` now displays as `1 + 2`, while
// `AddBigRat(IntToBigRat(AddInt(1,2)), Err)` displays as `(1 + 2) + error`. The
// existing comment above `generate_engine_regular_arm`'s infix branch already named
// this path as the one responsible for "the genuinely necessary disambiguation
// parentheses for a syntaxless-projection node used AS an operand"; the wrapper
// election was a second, competing mechanism layered over it. Removing it leaves one.
//
// Retained verbatim below rather than deleted, so the borrowed-surface approach is
// recoverable and its failure mode stays on the record.
//
// fn display_projection_reaches(language: &LanguageDef, source_cat: &str, target_cat: &str) -> bool {
//     if source_cat == target_cat {
//         return true;
//     }
//
//     let mut seen: HashSet<String> = HashSet::new();
//     let mut queue: VecDeque<String> = VecDeque::new();
//     seen.insert(source_cat.to_string());
//     queue.push_back(source_cat.to_string());
//
//     while let Some(cat) = queue.pop_front() {
//         for rule in &language.terms {
//             let Some((next_source, next_target)) = simple_projection_shape_for_display(rule) else {
//                 continue;
//             };
//             if next_source != cat || !seen.insert(next_target.clone()) {
//                 continue;
//             }
//             if next_target == target_cat {
//                 return true;
//             }
//             queue.push_back(next_target);
//         }
//     }
//
//     false
// }
//
// fn find_projection_surface_wrapper<'a>(
//     language: &'a LanguageDef,
//     source_cat: &str,
//     target_cat: &str,
// ) -> Option<(&'a GrammarRule, String)> {
//     language.terms.iter().find_map(|rule| {
//         if rule.is_auto_injected || rule.category.to_string() != target_cat {
//             return None;
//         }
//         let syntax_pattern = rule.syntax_pattern.as_ref()?;
//         let (param_name, param_cat) = single_base_param(rule)?;
//         let param_occurrences = syntax_pattern
//             .iter()
//             .filter(|expr| matches!(expr, SyntaxExpr::Param(id) if id.to_string() == param_name))
//             .count();
//         let has_literal = syntax_pattern
//             .iter()
//             .any(|expr| matches!(expr, SyntaxExpr::Literal(_)));
//         if param_occurrences != 1 || !has_literal {
//             return None;
//         }
//         if !is_delimited_projection_surface_pattern(syntax_pattern, &param_name) {
//             return None;
//         }
//         if !display_projection_reaches(language, source_cat, &param_cat) {
//             return None;
//         }
//         Some((rule, param_name))
//     })
// }
//
// fn is_delimited_projection_surface_pattern(
//     syntax_pattern: &[SyntaxExpr],
//     param_name: &str,
// ) -> bool {
//     let Some(param_idx) = syntax_pattern
//         .iter()
//         .position(|expr| matches!(expr, SyntaxExpr::Param(id) if id.to_string() == param_name))
//     else {
//         return false;
//     };
//
//     let has_left_literal = syntax_pattern[..param_idx]
//         .iter()
//         .any(|expr| matches!(expr, SyntaxExpr::Literal(s) if !s.is_empty()));
//     let has_right_literal = syntax_pattern[param_idx + 1..]
//         .iter()
//         .any(|expr| matches!(expr, SyntaxExpr::Literal(s) if !s.is_empty()));
//
//     has_left_literal && has_right_literal
// }

/// Element category of a collection-typed `Simple` param `param` on `rule`
/// (e.g. `Proc` for `ps:HashBag(Proc)`), read from the rule's term context.
fn collection_param_element_category(rule: &GrammarRule, param: &str) -> Option<String> {
    let term_context = rule.term_context.as_ref()?;
    term_context.iter().find_map(|p| match p {
        TermParam::Simple {
            name,
            ty: TypeExpr::Collection { element, .. },
        } if name.to_string() == param => match element.as_ref() {
            TypeExpr::Base(cat) => Some(cat.to_string()),
            _ => None,
        },
        _ => None,
    })
}

/// True when `rule` is the bare-infix twin of an associative collection: a
/// same-category binary infix operator `a OP b : C` whose operator token `OP`
/// is also the element separator of a collection rule producing `C` over
/// elements of category `C`.
///
/// Example (rholang): `PParInfix . a:Proc, b:Proc |- a "|" b : Proc` mirrors
/// the parallel-composition collection
/// `PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc`.
///
/// Such an operator is the loosest-binding combinator for its category — the
/// collection is flat and associative, so nothing ever needs parenthesizing
/// beneath it. Its operands must therefore be displayed exactly like the
/// collection twin renders its elements: at `min_bp == 0` (bare). Otherwise a
/// cross-category projection operand (e.g. `CastBigInt`) borrows a
/// projection-surface wrapper in operand position and `1 | 2` mis-renders as
/// `@Nil!(1) | @Nil!(2)` (the projection-surface arm only renders the bare
/// source when `min_bp == 0`). Arithmetic/relational operators (`+`, `==`, …)
/// are NOT collection mirrors, so they keep their operand binding powers and
/// their disambiguating projection-surface wrapping.
///
/// Operator token and operand/element categories are read from
/// `syntax_pattern` + `term_context` — NOT `rule.items`, whose terminal tokens
/// are dropped and whose collection separator is a hard-coded `"|"` default
/// (see `convert_term_context_to_items`).
/// Compile-time gate for the `@`-prefix display disambiguation (the Rholang
/// `@`-quote round-trip fix). Flip to `false` to restore the prior bare emission.
const AT_QUOTE_DISAMBIGUATION: bool = true;

/// Whether `param` is the **operand directly following a leading sigil terminal**
/// of a sigil-prefix rule whose operand is parsed under a prefix binding-power cap
/// (the Rholang `prefix(220)` on `NQuoteShort`, `POutputShort`,
/// `PPersistOutputShort`).
///
/// Grammar shape (structural, per-rule):
///   1. the rule's FIRST syntax item is a `Literal` sigil (`@`) and `param` is the
///      immediately following `Param` operand (a base-category nonterminal), and
///   2. the rule is NOT a `classify_unary_prefix_shape` rule.
///
/// The unary-prefix exclusion separates the SUGAR sigils that need this rescue
/// from ordinary same-category unary prefixes:
///   • `NQuoteShort . p:Proc |- "@" p : Name` (operand cat ≠ rule cat → not a
///     unary prefix), `POutputShort . p:Proc, q:Proc |- "@" p "!" "(" q ")" : Proc`
///     and its `!!` twin (four syntax items → not a unary prefix): the unary-prefix
///     classifier rejects all three, so they render their operand at `child_bp = 0`
///     with no precedence protection → INCLUDED (need the structural wrap).
///   • `NegProc . a:Proc |- "-" a : Proc`, `BitNot`, `Not`, `PDrop`'s `"*" n`:
///     these ARE `classify_unary_prefix_shape` rules that already receive a real
///     `child_bp = prefix_bp` → EXCLUDED (a bare `@-a` / `@bitnot a` already
///     round-trips; wrapping would only cost byte-identity).
///
/// When true, the operand is rendered bare (`min_bp == 0`, so a cast stays bare as
/// `{|1:2|}` — the projection-surface arm renders the bare source only at
/// `min_bp == 0`) and then conditionally wrapped `@(…)` by the STRUCTURAL runtime
/// predicate `<Cat>::__at_sigil_operand_needs_wrap` (see
/// [`generate_at_sigil_wrap_predicate`]) — never by a fragile string scan.
/// Returns `false` for every non-sigil rule, so languages without these shapes
/// (calculator / ambient / class2*) are unaffected.
fn is_sigil_prefix_operand(rule: &GrammarRule, param: &str) -> bool {
    let Some(sp) = rule.syntax_pattern.as_ref() else {
        return false;
    };
    // Ordinary same-category unary prefixes (`-`, `bitnot`, `not`, `*`) already
    // carry a real `child_bp = prefix_bp` and parenthesize through the ordinary
    // prefix path — a bare `@-a` / `@bitnot a` already round-trips, so excluding
    // them keeps their emission byte-identical.
    if classify_unary_prefix_shape(rule).is_some() {
        return false;
    }
    // The sigil operand must itself be a base-category nonterminal (`p:Proc`).
    let is_base_operand = rule.term_context.as_ref().map_or(false, |tc| {
        tc.iter().any(|p| {
            matches!(p,
                TermParam::Simple { name, ty: TypeExpr::Base(_) } if name.to_string() == param)
        })
    });
    if !is_base_operand {
        return false;
    }
    // Leading sigil terminal immediately followed by this operand param.
    matches!(
        (sp.first(), sp.get(1)),
        (Some(SyntaxExpr::Literal(_)), Some(SyntaxExpr::Param(p))) if p.to_string() == param
    )
}

/// Whether a term whose top constructor is `rule` must be wrapped `(…)` when it
/// appears as the operand of a cross-category sigil prefix (the `@`-operand). This
/// is the GRAMMAR-DERIVED, per-rule structural core of
/// [`generate_at_sigil_wrap_predicate`].
///
/// A sigil prefix parses its operand under a very high binding-power cap (Rholang
/// `prefix(220)`), so the operand parser accepts ONLY a self-delimiting primary:
/// an atom / variable, a cast rendered bare, a bracket-delimited literal
/// (`{ … }`, `{| … |}`), a keyword-prefixed call (`int( … )`, `str( … )`), or a
/// terminal-leading prefix (`@ …`-send sugar, `- …`, `bitnot …`, `* …`).  It does
/// NOT re-consume a top-level operator, so an **operand-leading** rule — one whose
/// surface begins with a nonterminal operand and then continues with a terminal —
/// loses its tail unless wrapped.  That single structural test
///
/// > first syntax item is a `Param` (nonterminal operand) AND the rule carries at
/// > least one `Literal` terminal
///
/// captures exactly the wrap set, verified against parser-truth for every Rholang
/// `Proc` rule:
///   • binary infix     `a "|" b`, `a "+" b`, `a "==" b`, …  → WRAP
///   • postfix method   `m "." "size" "(" ")"`, …            → WRAP
///   • plain-channel send `n "!" "(" q ")"`, `n "!!" …`       → WRAP
/// and excludes (first item is a `Literal`, or param-only):
///   • casts / projections `m : Proc` (param-only, no terminal)  → bare
///   • vars / nullary atoms (`Nil`, `error`)                     → bare
///   • keyword / sigil-leading rules (`int( … )`, `@ p "!" …`,
///     `- a`, `bitnot a`, `* n`, `{ … }`)                        → bare
///
/// The predicate is independent of the concrete sigil, operator token set, and
/// category, so it generalizes to any language with a cross-category sigil prefix.
fn rule_is_sigil_operand_wrap_shape(rule: &GrammarRule) -> bool {
    let Some(sp) = rule.syntax_pattern.as_ref() else {
        return false;
    };
    // Param-only rules (casts / projections / bare identity) never need a wrap.
    if classify_simple_projection_shape(rule).is_some() {
        return false;
    }
    let first_is_operand = matches!(sp.first(), Some(SyntaxExpr::Param(_)));
    let has_terminal = sp.iter().any(|e| matches!(e, SyntaxExpr::Literal(_)));
    first_is_operand && has_terminal
}

/// Whether `rule` is a param-only projection `CastX . x:X |- x : Cat` whose SOURCE
/// category `X` is a native collection whose declared literal opener is a
/// KEYWORD-CALL (`Set(`, `list(`, …) rather than a self-delimiting BRACKET
/// (`{`, `[`, `{|`, `#{`).  Such a projection renders its bare surface as
/// `Set( … )` — a keyword-prefixed call.  Placed BARE as the operand of a
/// cross-category sigil prefix `@` (which parses its operand under the very high
/// `prefix(220)` bp cap), that `Set( … )` surface is NOT reachable (the cross-cat
/// projection is not in the sigil operand's dispatch set at that cap), so `@Set()`
/// fails to re-parse while `@(Set())` succeeds — hence it must be wrapped `@(…)`.
///
/// This is the missing companion to [`rule_is_sigil_operand_wrap_shape`]: that one
/// wraps OPERAND-LEADING rules (infix/postfix/send); this one wraps the ONE class
/// of param-only PROJECTION that also fails bare — a keyword-led collection cast.
/// Bracket-opened collection casts (rholang `CastMap`→`{…}`, `CastList`→`[…]`,
/// `CastBag`→`#{…}#`, `CastPathmap`→`{|…|}`) are self-delimiting primaries reachable
/// at the cap, and their EMPTY forms additionally have direct `Proc` rules
/// (`MapEmpty`/`PathmapEmpty`), so they do NOT need wrapping — the opener's leading
/// character (alphanumeric ⟹ keyword-call; punctuation ⟹ bracket) is the exact,
/// grammar-derived discriminator.  Generalises to any language with a keyword-call
/// collection projection under a cross-category sigil prefix.
fn rule_projection_source_is_keyword_led_collection(
    rule: &GrammarRule,
    language: &LanguageDef,
) -> bool {
    let Some(shape) = classify_simple_projection_shape(rule) else {
        return false;
    };
    language.types.iter().any(|t| {
        t.name.to_string() == shape.source_category
            && t.collection_kind.as_ref().is_some_and(|ck| {
                ck.delimiters()
                    .open
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_alphanumeric())
            })
    })
}

/// Generate, for every base category, a structural runtime predicate
/// `impl Cat { fn __at_sigil_operand_needs_wrap(&self) -> bool }` that returns
/// `true` iff `self`'s top constructor is an operand-leading rule
/// ([`rule_is_sigil_operand_wrap_shape`]) — i.e. a term that, placed bare after a
/// cross-category sigil prefix (`@`), would lose its tail to the prefix
/// binding-power cap and so must be wrapped `@(…)`.
///
/// One arm per operand-leading variant returns `true`; a `_ => false` catch-all
/// covers atoms, casts, keyword/sigil-leading forms, and every other category's
/// variants.  The predicate is emitted for a category only when it actually
/// appears as a cross-category sigil operand in the grammar, so languages without
/// such a shape gain no code.
fn generate_at_sigil_wrap_predicate(language: &LanguageDef) -> TokenStream {
    // Categories that appear as a sigil-prefix operand anywhere.
    let mut sigil_operand_cats: HashSet<String> = HashSet::new();
    for rule in &language.terms {
        if let Some(tc) = rule.term_context.as_ref() {
            for p in tc {
                if let TermParam::Simple { name, ty: TypeExpr::Base(cat) } = p {
                    if is_sigil_prefix_operand(rule, &name.to_string()) {
                        sigil_operand_cats.insert(cat.to_string());
                    }
                }
            }
        }
    }
    if sigil_operand_cats.is_empty() {
        return quote! {};
    }

    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .filter(|t| sigil_operand_cats.contains(&t.name.to_string()))
        .map(|lang_type| {
            let cat = &lang_type.name;
            let wrap_arms: Vec<TokenStream> = language
                .terms
                .iter()
                .filter(|rule| rule.category.to_string() == cat.to_string())
                .filter(|rule| {
                    // Wrap operand-leading rules (infix/postfix/send) AND the one
                    // class of param-only projection that also fails bare under the
                    // `@` sigil cap: a keyword-led collection cast (`CastSet`→`Set(…)`).
                    rule_is_sigil_operand_wrap_shape(rule)
                        || rule_projection_source_is_keyword_led_collection(rule, language)
                })
                .map(|rule| {
                    let label = &rule.label;
                    // ★ 2026-07-27: the wrap is conditioned on the RENDERED surface, not on the
                    // template position. An operand-leading rule whose LEADING OPERAND itself
                    // renders terminal-leading composes to a terminal-leading surface, and then
                    // the wrap is not only unnecessary but ACTIVELY WRONG — see the block comment
                    // above `terminal_leading_arms_for`.
                    // ★ ONLY A BRACKET-CLOSED FRAME MAY RECURSE (2026-07-27, measured).
                    // The recursion asks "does the surface OPEN with a sigil?", which is only
                    // enough when nothing after the leading operand can dangle. A BINARY INFIX
                    // ends with a `Param` (`a "*" b`), so its tail is an OPERATOR at a binding
                    // power BELOW the sigil's cap and is lost however the left operand opens:
                    // `@@Nil!(0) * Nil` parses `@@Nil!(0)` and strands `* Nil`. A send / postfix
                    // method ends with a closing-bracket `Literal`, so its tail belongs to the
                    // same primary and rides along. This is the same shape test
                    // `facade.rs::is_receiver_led_postfix_frame` uses, for the same reason.
                    let bracket_closed = matches!(
                        rule.syntax_pattern.as_ref().and_then(|sp| sp.last()),
                        Some(SyntaxExpr::Literal(_))
                    );
                    match leading_operand_field_index(rule).filter(|_| bracket_closed) {
                        Some(idx) => {
                            let binds: Vec<TokenStream> = (0..constructor_field_count(rule))
                                .map(|i| {
                                    if i == idx {
                                        quote! { __lead }
                                    } else {
                                        quote! { _ }
                                    }
                                })
                                .collect();
                            quote! {
                                #cat::#label(#(#binds),*) => {
                                    !__lead.__renders_sigil_led_primary()
                                },
                            }
                        },
                        None => quote! { #cat::#label(..) => true, },
                    }
                })
                .collect();
            quote! {
                impl #cat {
                    /// Grammar-derived: `true` iff this term, placed BARE as the
                    /// operand of a cross-category sigil prefix (`@`), would fail
                    /// to round-trip (its top rule is operand-leading — a
                    /// top-level infix, a postfix method, or a plain-channel send)
                    /// and so must be wrapped `@(…)`.  Generated by
                    /// `generate_at_sigil_wrap_predicate`.
                    ///
                    /// ★ CONDITIONED ON THE RENDERED SURFACE (2026-07-27). An operand-leading
                    /// rule whose leading operand renders as a sigil-led PRIMARY is not
                    /// operand-leading on the page, so it takes the bare spelling. See
                    /// [`Self::__renders_sigil_led_primary`].
                    #[allow(dead_code)]
                    pub fn __at_sigil_operand_needs_wrap(&self) -> bool {
                        match self {
                            #(#wrap_arms)*
                            _ => false,
                        }
                    }
                }
            }
        })
        .collect();

    // ★ The companion predicate is emitted for EVERY category, not only for the sigil-operand
    // ones: the recursion follows the LEADING OPERAND, which crosses categories freely
    // (`Proc::CastReadZipper(z)` descends into `ReadZipper`), so a category that never appears
    // as a sigil operand can still be asked the question. `#[allow(dead_code)]` covers the
    // categories nothing ever asks.
    let terminal_leading_impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            let cat = &lang_type.name;
            let arms = self_delimiting_sigil_arms_for(cat, language);
            quote! {
                impl #cat {
                    /// Grammar-derived: `true` iff this term's RENDERED surface begins with a
                    /// SIGIL that opens a SELF-DELIMITING PRIMARY — a surface the sigil-prefix
                    /// operand parser consumes ENTIRE at its binding-power cap, so a frame built
                    /// around it keeps its own tail.
                    ///
                    /// Three conditions, each grammar-derived and each REFUTED-then-added:
                    ///
                    /// 1. the opener is a NON-ident-shaped literal (`@`, `*`, `{`, `[`) — spelled
                    ///    by the rule itself, or, for an operand-leading rule, by its leading
                    ///    operand transitively. An IDENT-shaped opener (`error`, `Nil`, `Map(`)
                    ///    is a keyword primary that the operand parser takes and stops at, so a
                    ///    tail after it is lost (`@error.union(X)` does not parse);
                    /// 2. the rule is NOT a SAME-CATEGORY unary prefix. `- a : Proc` over
                    ///    `a : Proc` puts its operand in its own category's precedence ladder, so
                    ///    under the cap the `-` closes at its own prefix binding power and the
                    ///    frame's tail is stranded — `@-a.get(Nil)` does not parse, while the
                    ///    CROSS-category `* n : Proc` over `n : Name` does not join that ladder
                    ///    and `@*a.get(Nil)` does;
                    /// 3. (for the recursive arm) the descent follows the leading operand, which
                    ///    crosses categories freely.
                    ///
                    /// Well-founded: every recursive arm descends strictly into a child.
                    /// Generated by `generate_at_sigil_wrap_predicate`.
                    #[allow(dead_code)]
                    pub fn __renders_sigil_led_primary(&self) -> bool {
                        match self {
                            #(#arms)*
                            _ => false,
                        }
                    }
                }
            }
        })
        .collect();

    let wrap_gate = generate_sigil_operand_wrap_gate(language, &sigil_operand_cats);
    quote! { #(#impls)* #(#terminal_leading_impls)* #wrap_gate }
}

/// ★ THE SIGIL-OPERAND WRAP GATE — the constructor-surface counterpart of
/// `languages/tests/literal_domain_agreement.rs`.
///
/// # The invariant, and why it needs a gate at the GRAMMAR rather than in a proptest
///
/// > A `Display` arm may not emit a surface its own grammar cannot parse back.
///
/// `__at_sigil_operand_needs_wrap` decides, per constructor, whether a term placed after a
/// cross-category sigil prefix keeps its `( … )`. Both directions of getting it wrong are silent:
///
/// * too EAGER — the bracket is kept where it is not needed, two constructors that render the
///   same surface disagree about it, and `Display ∘ Parse` sheds one surface per nesting layer
///   (`gen_rholang_prop::inputbind_display_parse_roundtrip`, 2026-07-27);
/// * too LAX — the bracket is dropped where the re-parse needs it, and `Display` emits a surface
///   the grammar rejects outright (`@@a!(a,) * Nil`).
///
/// Both were reached during this repair, each by a single proptest draw, and a draw is a poor
/// detector: it finds an instance only when the generator happens to build one. This gate asks
/// the question of EVERY RULE of every sigil-operand category, from a sample surface the macro
/// builds out of that rule's own syntax pattern — so a new constructor is covered the moment it
/// is declared.
///
/// It emits `__sigil_operand_wrap_surface(category, surface)`, which parses `surface` at
/// `category`, applies the SAME predicate `Display` applies, and returns the composed `@…`
/// spelling. `languages/tests/sigil_operand_wrap_agreement.rs` then requires that spelling to
/// parse and to be a `Display` fixpoint.
fn generate_sigil_operand_wrap_gate(
    language: &LanguageDef,
    sigil_operand_cats: &HashSet<String>,
) -> TokenStream {
    use crate::gen::syntax::synonymy::{
        nonground_filler_surfaces, nullary_filler_surfaces, sample_surface_for,
        sample_surface_with_lead,
    };
    if sigil_operand_cats.is_empty() {
        return quote! {};
    }
    // ★ TWO FILLER REGIMES, because ONE of them cannot express a shape.
    //
    // `nullary_filler_surfaces` is GROUND, and a ground argument is what a `fold` rule consumes:
    // `- Nil . get ( Nil )` parses to `MGet(error, Nil)`, not to the `MGet(NegProc(…), …)` the
    // sample was written for, so a row built that way reports on `error`. The VARIABLE regime is
    // opaque to evaluation (folds are demand-gated on ground operands) and preserves the shape.
    // Both are kept: the ground rows exercise the folded VALUES a program really writes, the
    // variable rows exercise the CONSTRUCTORS. Neither subsumes the other.
    let ground_filler = nullary_filler_surfaces(language);
    let filler = nonground_filler_surfaces(language);

    // ★ THE FRAME IS COMPOSED WHOLE, not as `sigil + operand`.
    //
    // `is_sigil_prefix_operand` — the predicate's own gate — admits any rule whose pattern starts
    // `Literal, Param`, which includes MULTI-SLOT frames: `POutputShort . p:Proc, q:Proc |- "@" p
    // "!" "(" q ")"`. The first cut of this gate composed only `@` + operand and then parsed the
    // result at the frame's category, so it asked whether `@Nil` is a `Proc` — it is not, and 87
    // rows "failed" for a reason that was the GATE's, not the predicate's. A gate that reports a
    // defect it invented is worse than no gate, so the row carries the frame's own PREFIX and
    // SUFFIX (its pattern either side of the operand slot, other params filled) and the composed
    // string is the frame's real surface.
    let mut rows: Vec<TokenStream> = Vec::new();
    // `(frame_label, prefix, suffix, operand_rule_label, sample)` already emitted.
    let mut seen_rows: BTreeSet<(String, String, String, String, String)> = BTreeSet::new();
    let mut gate_cats: BTreeSet<String> = BTreeSet::new();
    // The categories the FRAMES produce — the gate parses its composed surfaces at these, and
    // they need not be synonymy categories (Rholang's `InputBind` is a frame result and has no
    // synonymy class), so the gate carries its own entry rather than borrowing one.
    let mut frame_cats: BTreeSet<String> = BTreeSet::new();
    // ★ THE NARROWEST FRAME PER OPERAND CATEGORY, for the DEPTH-2 leg below.
    //
    // `__at_sigil_operand_needs_wrap` reads only the OPERAND — the frame supplies surrounding
    // text and never enters the decision — so a wrong verdict breaks every frame that hosts that
    // operand alike, and crossing the depth-2 rows with all of them multiplies the table without
    // adding detection power. The depth-2 leg therefore holds the frame fixed and varies the
    // dimension the verdict actually depends on. The frame chosen is the one with the least
    // surrounding text (ties by declaration order), so a failure is attributable to the operand
    // slot rather than to the frame's own fillers.
    //
    // Key: operand category. Value: `(result_cat, frame_label, frame rule index, operand field
    // index within that rule's term context)`. `width` (below) picks the minimum.
    let mut narrowest_frame_terms: BTreeMap<String, (String, String, usize, usize)> =
        BTreeMap::new();
    let mut narrowest_width: BTreeMap<String, usize> = BTreeMap::new();
    // The narrowest frame's surface BEFORE the operand slot, carried into the term rows so a test
    // can distinguish a wrapped operand from a bare one without knowing the language's sigil.
    let mut narrowest_prefix: BTreeMap<String, String> = BTreeMap::new();
    for (frame_rule_idx, rule) in language.terms.iter().enumerate() {
        let (Some(sp), Some(tc)) = (rule.syntax_pattern.as_ref(), rule.term_context.as_ref())
        else {
            continue;
        };
        // The operand slot: pattern position 1, immediately after the leading literal.
        let Some(SyntaxExpr::Param(op_param)) = sp.get(1) else {
            continue;
        };
        let op_param = op_param.to_string();
        if !is_sigil_prefix_operand(rule, &op_param) {
            continue;
        }
        let Some(op_idx) = tc
            .iter()
            .position(|p| matches!(p, TermParam::Simple { name, .. } if *name == op_param))
        else {
            continue;
        };
        let Some(TermParam::Simple { ty: opcat_ty @ TypeExpr::Base(opcat), .. }) = tc.get(op_idx)
        else {
            continue;
        };
        // An `Ident` operand is identifier TEXT, not a category, so it is not a gate
        // operand: there is no `Ident` enum to `parse(surface)` back into, and the whole
        // notion of "does this operand need wrapping at this precedence?" is vacuous for a
        // bare identifier, which is atomic and can never need parenthesising.
        if opcat_ty.is_ident_text() {
            continue;
        }
        let opcat = opcat.to_string();
        // Render the frame either side of the operand slot, filling the other params from the
        // requested regime.
        let render_with = |items: &[SyntaxExpr], f: &BTreeMap<String, String>| -> Option<String> {
            let mut parts: Vec<String> = Vec::new();
            for e in items {
                match e {
                    SyntaxExpr::Literal(l) => parts.push(l.clone()),
                    SyntaxExpr::Param(p) => {
                        let pname = p.to_string();
                        let pcat = tc.iter().find_map(|tp| match tp {
                            TermParam::Simple { name, ty: TypeExpr::Base(c) }
                                if name.to_string() == pname =>
                            {
                                Some(c.to_string())
                            },
                            _ => None,
                        })?;
                        parts.push(f.get(&pcat)?.clone());
                    },
                    _ => return None,
                }
            }
            Some(parts.join(" "))
        };
        let render_side = |items: &[SyntaxExpr]| render_with(items, &filler);
        let render_ground = |items: &[SyntaxExpr]| render_with(items, &ground_filler);
        let (Some(prefix), Some(suffix)) = (render_side(&sp[..1]), render_side(&sp[2..])) else {
            continue;
        };
        let result_cat = rule.category.to_string();
        let frame = rule.label.to_string();
        for op_rule in language
            .terms
            .iter()
            .filter(|r| r.category.to_string() == opcat)
        {
            let Some(sample) = sample_surface_for(op_rule, &filler) else {
                continue;
            };
            let op_label = op_rule.label.to_string();
            if seen_rows.insert((
                frame.clone(),
                prefix.clone(),
                suffix.clone(),
                op_label.clone(),
                sample.clone(),
            )) {
                rows.push(quote! {
                    (#opcat, #result_cat, #frame, #prefix, #suffix, #op_label, #sample)
                });
            }
        }
        // The same frame under the GROUND regime: its prefix/suffix fillers and its operand
        // samples are the folded VALUES, which is a different — and equally real — population of
        // surfaces. Rows identical to the variable regime's (a nullary operand renders the same
        // either way) are dropped rather than duplicated.
        if let (Some(g_prefix), Some(g_suffix)) = (render_ground(&sp[..1]), render_ground(&sp[2..]))
        {
            for op_rule in language
                .terms
                .iter()
                .filter(|r| r.category.to_string() == opcat)
            {
                let Some(g_sample) = sample_surface_for(op_rule, &ground_filler) else {
                    continue;
                };
                let op_label = op_rule.label.to_string();
                if seen_rows.insert((
                    frame.clone(),
                    g_prefix.clone(),
                    g_suffix.clone(),
                    op_label.clone(),
                    g_sample.clone(),
                )) {
                    rows.push(quote! {
                        (#opcat, #result_cat, #frame, #g_prefix, #g_suffix, #op_label, #g_sample)
                    });
                }
            }
        }
        let width = prefix.len() + suffix.len();
        if narrowest_width.get(&opcat).is_none_or(|w| width < *w) {
            narrowest_width.insert(opcat.clone(), width);
            narrowest_frame_terms
                .insert(opcat.clone(), (result_cat.clone(), frame.clone(), frame_rule_idx, op_idx));
            narrowest_prefix.insert(opcat.clone(), prefix.clone());
        }
        gate_cats.insert(opcat);
        frame_cats.insert(result_cat);
    }

    // ══════════════════════════════════════════════════════════════════════════════════════
    //  ★ THE TERM-FIRST LEG — the only shape of gate that can reject this class.
    // ══════════════════════════════════════════════════════════════════════════════════════
    //
    // Everything above is SURFACE-FIRST: the row is a string the macro composes, and the term it
    // is really about is recovered by PARSING that string. Two measured consequences make that
    // shape structurally unable to reject the defect it exists for:
    //
    //  1. A surface-first row can only ever test a term the parser ELECTS. The defect class is
    //     precisely "terms whose `Display` surface the parser does not elect back", so the terms
    //     at issue are unreachable from a composed string by construction.
    //  2. Concretely, `sample_surface_for` joins pattern items with a SPACE, and the spacing
    //     changes the election:
    //
    //     ```text
    //       Proc::parse("- a . get ( a )")  ─▶  NegProc(MGet(a, a))     ← what the row measured
    //       Proc::parse("-a.get(a)")        ─▶  MGet(NegProc(a), a)     ← the shape at issue
    //     ```
    //
    //  A controlled A/B proved it rather than argued it: with the `classify_unary_prefix_shape`
    //  guard in `self_delimiting_sigil_arms_for` disabled — i.e. with the defect re-armed — every
    //  surface-first row stayed GREEN, at depth 1 and at depth 2, under both filler regimes.
    //
    // The rows below CONSTRUCT the term and ask `Display` for its surface, which is the property
    // itself: `Display(t)` must parse and must be a fixpoint. Nothing is recovered by parsing
    // except the leaves, and a leaf is a single identifier with one reading.
    //
    // Coverage is the pair space the predicate's recursion actually ranges over: every operand
    // rule (with the leading slot at a leaf — depth 1) and every (operand rule with a recursion
    // arm x rule of its leading operand's category) pair — depth 2.
    let leaf_cats: BTreeMap<String, String> = language
        .types
        .iter()
        .filter_map(|t| {
            let name = t.name.to_string();
            filler.get(&name).map(|surface| (name, surface.clone()))
        })
        .collect();

    // `Cat::Label(Arc::new(f0), …)` with each field a leaf, except `lead` when supplied.
    // `None` for any rule whose fields are not all plain `Simple { Base }` with a leafable
    // category — a collection, binder, capture or optional slot has no single child to construct.
    let ctor_expr =
        |rule: &GrammarRule, lead: Option<(usize, TokenStream)>| -> Option<TokenStream> {
            let cat = quote::format_ident!("{}", rule.category.to_string());
            let label = &rule.label;
            // A UNIT variant is a rule whose whole surface is literals — the same test
            // `nullary_filler_surfaces` uses. An absent `term_context` is NOT sufficient: an FLT rule
            // (`PFlt`) carries a capture instead of a term context and still has fields, and naming it
            // as a unit variant does not compile.
            let is_nullary_surface = rule.syntax_pattern.as_ref().is_some_and(|sp| {
                !sp.is_empty() && sp.iter().all(|e| matches!(e, SyntaxExpr::Literal(_)))
            });
            let Some(tc) = rule.term_context.as_ref().filter(|tc| !tc.is_empty()) else {
                return is_nullary_surface.then(|| quote! { #cat::#label });
            };
            let mut fields: Vec<TokenStream> = Vec::with_capacity(tc.len());
            for (i, param) in tc.iter().enumerate() {
                let TermParam::Simple { ty: TypeExpr::Base(field_cat), .. } = param else {
                    return None;
                };
                if let Some((_, expr)) = lead.as_ref().filter(|(j, _)| *j == i) {
                    fields.push(quote! { std::sync::Arc::new(#expr) });
                    continue;
                }
                let field_cat = field_cat.to_string();
                if !leaf_cats.contains_key(&field_cat) {
                    return None;
                }
                let leaf_fn = quote::format_ident!("__sigil_leaf_{}", field_cat);
                fields.push(quote! { std::sync::Arc::new(#leaf_fn()) });
            }
            Some(quote! { #cat::#label(#(#fields),*) })
        };

    // One leaf constructor per leafable category. A leaf is the ONE place a surface is parsed,
    // and its surface is a single identifier (or, for a literal-typed category, that category's
    // nullary spelling) — one token, one reading, so the election cannot move underneath it.
    let leaf_fns: Vec<TokenStream> = leaf_cats
        .iter()
        .map(|(cat, surface)| {
            let cat_ident = quote::format_ident!("{}", cat);
            let fn_ident = quote::format_ident!("__sigil_leaf_{}", cat);
            let msg = format!("the `{cat}` leaf surface `{surface}` must parse at `{cat}`");
            quote! {
                #[allow(dead_code, non_snake_case)]
                fn #fn_ident() -> #cat_ident {
                    #cat_ident::parse(#surface).expect(#msg)
                }
            }
        })
        .collect();

    // `__sigil_term_at_<Cat>(label)`: the DEPTH-1 term of `Cat` whose top constructor is `label`,
    // every field a leaf. `""` names the leaf itself, so a caller can ask for "no wrapping rule".
    let term_at_fns: Vec<TokenStream> = leaf_cats
        .keys()
        .map(|cat| {
            let cat_ident = quote::format_ident!("{}", cat);
            let fn_ident = quote::format_ident!("__sigil_term_at_{}", cat);
            let leaf_fn = quote::format_ident!("__sigil_leaf_{}", cat);
            let arms: Vec<TokenStream> = language
                .terms
                .iter()
                .filter(|r| r.category.to_string() == *cat)
                .filter_map(|r| {
                    let expr = ctor_expr(r, None)?;
                    let label = r.label.to_string();
                    Some(quote! { #label => #expr, })
                })
                .collect();
            quote! {
                #[allow(dead_code, non_snake_case)]
                fn #fn_ident(label: &str) -> Option<#cat_ident> {
                    if label.is_empty() {
                        return Some(#leaf_fn());
                    }
                    Some(match label {
                        #(#arms)*
                        _ => return None,
                    })
                }
            }
        })
        .collect();

    // `__sigil_term_operand_<Cat>(op_label, lead_label)`: the term the gate puts in the sigil's
    // operand slot. With an empty `lead_label` it is the depth-1 term; otherwise the leading
    // operand carries the depth-1 term of `lead_label` — the slot the wrap recursion reads.
    let operand_fns: Vec<TokenStream> = gate_cats
        .iter()
        .filter(|c| leaf_cats.contains_key(*c))
        .map(|cat| {
            let cat_ident = quote::format_ident!("{}", cat);
            let fn_ident = quote::format_ident!("__sigil_term_operand_{}", cat);
            let at_fn = quote::format_ident!("__sigil_term_at_{}", cat);
            let arms: Vec<TokenStream> = language
                .terms
                .iter()
                .filter(|r| r.category.to_string() == *cat)
                .filter_map(|r| {
                    let lead_idx = leading_operand_field_index(r)?;
                    let TermParam::Simple { ty: TypeExpr::Base(lead_cat), .. } =
                        r.term_context.as_ref()?.get(lead_idx)?
                    else {
                        return None;
                    };
                    let lead_cat = lead_cat.to_string();
                    if !leaf_cats.contains_key(&lead_cat) {
                        return None;
                    }
                    let lead_at = quote::format_ident!("__sigil_term_at_{}", lead_cat);
                    let expr = ctor_expr(r, Some((lead_idx, quote! { #lead_at(lead_label)? })))?;
                    let label = r.label.to_string();
                    Some(quote! { #label => #expr, })
                })
                .collect();
            quote! {
                #[allow(dead_code, non_snake_case)]
                fn #fn_ident(op_label: &str, lead_label: &str) -> Option<#cat_ident> {
                    if lead_label.is_empty() {
                        return #at_fn(op_label);
                    }
                    Some(match op_label {
                        #(#arms)*
                        _ => return None,
                    })
                }
            }
        })
        .collect();

    // One frame arm per operand category, at that category's NARROWEST frame. The frame never
    // enters `__at_sigil_operand_needs_wrap`, so a wrong verdict breaks every frame that hosts
    // the operand alike; the narrowest one surrounds the slot with the least text, so a failure
    // is attributable to the operand rather than to the frame's own fillers.
    let mut frame_surface_arms: Vec<TokenStream> = Vec::new();
    let mut term_rows: Vec<TokenStream> = Vec::new();
    for (opcat, (result_cat, frame_label, frame_rule_idx, op_idx)) in &narrowest_frame_terms {
        if !leaf_cats.contains_key(opcat) {
            continue;
        }
        let frame_rule = &language.terms[*frame_rule_idx];
        let Some(frame_expr) = ctor_expr(frame_rule, Some((*op_idx, quote! { __op }))) else {
            continue;
        };
        let operand_fn = quote::format_ident!("__sigil_term_operand_{}", opcat);
        let frame_prefix = narrowest_prefix.get(opcat).cloned().unwrap_or_default();
        frame_surface_arms.push(quote! {
            #opcat => {
                let __op = #operand_fn(op_label, lead_label)?;
                Some(format!("{}", #frame_expr))
            },
        });
        for op_rule in language
            .terms
            .iter()
            .filter(|r| r.category.to_string() == *opcat)
        {
            let op_label = op_rule.label.to_string();
            // DEPTH 1: the operand rule with a leaf in every slot.
            term_rows.push(quote! {
                (#opcat, #result_cat, #frame_label, #frame_prefix, #op_label, "")
            });
            // DEPTH 2: the same rule with each rule of its leading operand's category in the slot
            // the wrap recursion descends into. Only rules that HAVE a recursion arm — an
            // operand-leading wrap shape with a bracket-closed frame — have a verdict that can
            // change with the child, so only those get the second dimension.
            if !rule_is_sigil_operand_wrap_shape(op_rule) {
                continue;
            }
            if !matches!(
                op_rule.syntax_pattern.as_ref().and_then(|sp| sp.last()),
                Some(SyntaxExpr::Literal(_))
            ) {
                continue;
            }
            let Some(lead_idx) = leading_operand_field_index(op_rule) else {
                continue;
            };
            let Some(TermParam::Simple { ty: TypeExpr::Base(lead_cat), .. }) = op_rule
                .term_context
                .as_ref()
                .and_then(|tc| tc.get(lead_idx))
            else {
                continue;
            };
            let lead_cat = lead_cat.to_string();
            for lead_rule in language
                .terms
                .iter()
                .filter(|r| r.category.to_string() == lead_cat)
            {
                let lead_label = lead_rule.label.to_string();
                term_rows.push(quote! {
                    (#opcat, #result_cat, #frame_label, #frame_prefix, #op_label, #lead_label)
                });
            }
        }
    }

    let arms: Vec<TokenStream> = gate_cats
        .iter()
        .map(|c| {
            let cat_ident = quote::format_ident!("{}", c);
            quote! {
                #c => #cat_ident::parse(surface)
                    .map(|__t| {
                        let __body = format!("{}", __t);
                        if __t.__at_sigil_operand_needs_wrap() {
                            format!("({__body})")
                        } else {
                            __body
                        }
                    })
                    .map_err(|__e| format!("{__e:?}")),
            }
        })
        .collect();

    let frame_arms: Vec<TokenStream> = frame_cats
        .iter()
        .map(|c| {
            let cat_ident = quote::format_ident!("{}", c);
            quote! {
                #c => #cat_ident::parse(surface)
                    .map(|__t| format!("{}", __t))
                    .map_err(|__e| format!("{__e:?}")),
            }
        })
        .collect();

    quote! {
        /// ★ SIGIL-OPERAND WRAP GATE — one row per (sigil FRAME x rule of the operand category).
        /// `(operand_category, frame_result_category, frame_label, frame_prefix, frame_suffix,
        ///   operand_rule_label, operand_sample_surface)`.
        ///
        /// The composed surface is `prefix + <operand as Display renders it> + suffix`, i.e. the
        /// frame's REAL surface — see `languages/tests/sigil_operand_wrap_agreement.rs`.
        #[allow(dead_code)]
        pub const __SIGIL_OPERAND_WRAP_SAMPLES:
            &[(&str, &str, &str, &str, &str, &str, &str)] = &[#(#rows),*];

        #(#leaf_fns)*
        #(#term_at_fns)*
        #(#operand_fns)*

        /// ★ THE TERM-FIRST LEG of the wrap gate.
        /// `(operand_category, frame_result_category, frame_label, frame_prefix,
        ///   operand_rule_label, leading_operand_rule_label)`; an empty leading label means the
        /// operand rule's own depth-1 term (every slot a leaf). `frame_prefix` is the frame's
        /// surface BEFORE the operand slot, so a test can tell a wrapped operand from a bare one
        /// without knowing the language's sigil.
        ///
        /// `__SIGIL_OPERAND_WRAP_SAMPLES` is SURFACE-first: its row is a string, and the term it
        /// is about is recovered by parsing that string — so it can only ever test terms the
        /// parser ELECTS, which is exactly the complement of the defect class. These rows name a
        /// term by its constructors instead; `__sigil_term_frame_surface` builds it and returns
        /// `Display` of the frame around it. See `languages/tests/sigil_operand_wrap_agreement.rs`.
        #[allow(dead_code)]
        pub const __SIGIL_OPERAND_WRAP_TERM_ROWS: &[(&str, &str, &str, &str, &str, &str)] =
            &[#(#term_rows),*];

        /// `Display` of the sigil frame built around the term named by
        /// `(operand_rule_label, leading_operand_rule_label)` at `operand_category`.
        ///
        /// `None` when the pair names no constructible term — a rule with a collection, binder,
        /// capture or optional slot has no single child to build, and is REPORTED as uncovered
        /// rather than given a guessed one.
        #[allow(dead_code, non_snake_case)]
        pub fn __sigil_term_frame_surface(
            operand_category: &str,
            op_label: &str,
            lead_label: &str,
        ) -> Option<String> {
            match operand_category {
                #(#frame_surface_arms)*
                _ => None,
            }
        }

        /// Parse a composed FRAME surface at its result category and render it back, so the gate
        /// can require the surface `Display` emits to parse and to be a fixpoint. Separate from
        /// `__surface_synonymy_normalise` because a frame's result category need not carry a
        /// synonymy class (`InputBind` does not).
        #[allow(dead_code, non_snake_case)]
        pub fn __sigil_frame_normalise(category: &str, surface: &str) -> Result<String, String> {
            let _ = surface;
            match category {
                #(#frame_arms)*
                other => Err(format!("no frame entry generated for category `{other}`")),
            }
        }

        /// Parse `surface` at `category`, then render it EXACTLY as a sigil frame's operand slot
        /// would be rendered — with the `( … )` iff `__at_sigil_operand_needs_wrap` says so.
        #[allow(dead_code, non_snake_case)]
        pub fn __sigil_operand_wrap_surface(
            category: &str,
            surface: &str,
        ) -> Result<String, String> {
            let _ = surface;
            match category {
                #(#arms)*
                other => Err(format!("no string entry generated for category `{other}`")),
            }
        }
    }
}

/// The CONSTRUCTOR FIELD INDEX of `rule`'s leading operand, when its syntax pattern begins with a
/// `Param` — i.e. when the rule is operand-leading and the surface's first characters therefore
/// come from that operand rather than from this rule.
///
/// `None` for a rule whose surface begins with one of its own literals, for a param-only
/// projection, and for any rule whose leading `Param` is not a plain `Simple { Base }` constructor
/// field (a collection or binder slot has no single child to recurse into).
fn leading_operand_field_index(rule: &GrammarRule) -> Option<usize> {
    let sp = rule.syntax_pattern.as_ref()?;
    let tc = rule.term_context.as_ref()?;
    let SyntaxExpr::Param(lead) = sp.first()? else {
        return None;
    };
    let lead = lead.to_string();
    // Constructor fields are the term-context params in declaration order; find the leading one
    // and require it to be a plain boxed category field.
    let idx = tc
        .iter()
        .position(|p| matches!(p, TermParam::Simple { name, .. } if *name == lead))?;
    match tc.get(idx) {
        Some(TermParam::Simple { ty: TypeExpr::Base(_), .. }) => Some(idx),
        _ => None,
    }
}

/// The number of constructor fields `rule` declares (its term-context arity).
fn constructor_field_count(rule: &GrammarRule) -> usize {
    rule.term_context.as_ref().map(|tc| tc.len()).unwrap_or(0)
}

/// ★ THE `__renders_sigil_led_primary` ARMS, and why this predicate has to exist.
///
/// `rule_is_sigil_operand_wrap_shape`'s own documentation states the criterion over the SURFACE —
/// *"an operand-leading rule — one whose surface begins with a nonterminal operand and then
/// continues with a terminal — loses its tail unless wrapped"* — and the implementation tested the
/// TEMPLATE instead. Those differ exactly when the leading operand's own surface begins with a
/// terminal, and Rholang reaches that case constantly, because a send's channel is usually an
/// `@`-name:
///
/// ```text
///   POutput2Plus(NQuoteShort(PZero), a, [])  renders  @Nil!(Nil,)   ← begins with `@`
///   POutputNil2Plus(a, [])                   renders  @Nil!(Nil,)   ← the SAME surface
/// ```
///
/// Two terms, one surface — the language's own `fold` bodies declare them equal — and the
/// template-based predicate gave them OPPOSITE wrap obligations (`POutput2Plus` is `Param`-leading
/// ⇒ wrap; `POutputNil2Plus` is `"@"`-leading ⇒ bare). An enclosing `@ pat` therefore rendered
/// `@(@Nil!(Nil,))` from one and `@@Nil!(Nil,)` from the other, and re-parsing moved between them,
/// so `Display ∘ Parse` shed one surface per layer. That is what
/// `gen_rholang_prop::inputbind_display_parse_roundtrip` measured on
/// `InputBindQuotedPersistent(POutput2Plus(NParen(NQuoteNil), …), NQuoteNil)`.
///
/// ★ THE WRAP IS NOT LOAD-BEARING WHERE IT IS DROPPED — measured, not argued. For each candidate
/// operand the enclosing frame was rendered BOTH ways and re-parsed:
///
/// ```text
///   pat                                Display(pat)     bare `@<pat>`   wrapped `@(<pat>)`
///   POutput2Plus(NQuoteShort(PZero))   @Nil!(Nil,)      POutputNil2Plus  POutputNil2Plus
///   POutput2Plus(NQuoteNil)            @Nil!(Nil,)      POutputNil2Plus  POutputNil2Plus
///   POutput2Plus(NParen(NQuoteNil))    (@Nil)!(Nil,)    keeps NParen     DROPS NParen
///   POutput2Plus(NVar x)               x!(Nil,)         (unchanged)      (unchanged)
///   Add(1, 2)                          1 + 2            round-trips      round-trips
/// ```
///
/// The two rows that change answer identically with and without the wrap, so removing it loses
/// nothing; the `NParen` row is strictly BETTER bare (the wrapped spelling is the one that drops
/// the grouping). The rows that keep the wrap — a variable channel, a top-level infix — are
/// exactly the rows whose leading operand does NOT render as a sigil-led primary.
///
/// ★ SIGIL-LED IS NOT ENOUGH — IT MUST BE A *PRIMARY* (2026-07-28, measured).
///
/// The first cut of this predicate asked only *"does the surface open with a sigil?"*, and that
/// admitted one shape it should not have: a SAME-CATEGORY unary prefix. `NegProc . a:Proc |- "-"
/// a : Proc` opens with the sigil `-`, but its operand is parsed in its OWN category's precedence
/// ladder, so under the sigil's binding-power cap the `-` closes at its own prefix binding power
/// and whatever the enclosing frame appends is stranded:
///
/// ```text
///   Display(NQuote(MGet(NegProc(a), PZero)))   emitted  @-a.get(Nil)
///   Name::parse("@-a.get(Nil)")                1:13 no accepting branch reached end of input
/// ```
///
/// The CROSS-category prefix `PDrop . n:Name |- "*" n : Proc` does not join that ladder — its
/// operand is a `Name`, bounded by its own category — and `@*a.get(Nil)` parses.
/// `classify_unary_prefix_shape` IS the "same-category unary prefix" test, and it is already the
/// test [`is_sigil_prefix_operand`] uses to exclude these very rules from the structural-wrap
/// path, so the two cannot drift.
///
/// Measured over the WHOLE sigil-led cohort rather than over an example: each of the sixteen
/// Rholang `Proc` rules whose own surface renders sigil-led was placed in the leading-operand slot
/// of a postfix frame and composed bare after `@`. Fifteen parse; exactly one does not, and it is
/// the only `classify_unary_prefix_shape` rule among them:
///
/// ```text
///   @*@Nil.get(Nil)        PARSES     PDrop         "*" n      cross-category prefix
///   @@Nil!(Nil).get(Nil)   PARSES     POutput …     n "!" …    operand-leading, bracket-closed
///   @-Nil.get(Nil)         REJECTS    NegProc       "-" a      SAME-category unary prefix  ✗
/// ```
fn self_delimiting_sigil_arms_for(cat: &syn::Ident, language: &LanguageDef) -> Vec<TokenStream> {
    language
        .terms
        .iter()
        .filter(|rule| rule.category.to_string() == cat.to_string())
        .filter_map(|rule| {
            let sp = rule.syntax_pattern.as_ref()?;
            let label = &rule.label;
            // ★ THE LEADING LITERAL MUST BE A SIGIL, NOT A KEYWORD — measured, see the block
            // comment above. `is_ident_shaped` is the SAME test `facade.rs` uses to decide
            // `ProjVariant::sigil_led`, so the two cannot drift.
            let is_ident_shaped = |t: &str| t.chars().all(|c| c.is_alphanumeric() || c == '_');
            match sp.first()? {
                // An IDENT-shaped opener (`error`, `Nil`, `Map(`) is a keyword primary: the
                // sigil's operand parser takes IT and stops, so any tail is lost and the wrap
                // stays. Only a punctuation opener (`@`, `(`, `{`, `[`) keeps the whole surface
                // reachable at the cap.
                SyntaxExpr::Literal(t) if is_ident_shaped(t) => None,
                // ★ A SAME-CATEGORY UNARY PREFIX IS NOT A PRIMARY. Its operand is parsed at the
                // rule's OWN prefix binding power inside its OWN category, so the surface it opens
                // is open-ended to the right: under the sigil's cap it closes early and the
                // enclosing frame's tail has nowhere to attach. See the block comment above.
                SyntaxExpr::Literal(_) if classify_unary_prefix_shape(rule).is_some() => None,
                // The rule spells its own opening sigil: the surface begins with it.
                // A NULLARY constructor is a unit variant, so it takes no `(..)` pattern.
                SyntaxExpr::Literal(_) if constructor_field_count(rule) == 0 => {
                    Some(quote! { #cat::#label => true, })
                },
                SyntaxExpr::Literal(_) => Some(quote! { #cat::#label(..) => true, }),
                // Operand-leading: the surface begins wherever the leading operand's does.
                SyntaxExpr::Param(_) => {
                    let idx = leading_operand_field_index(rule)?;
                    let binds: Vec<TokenStream> = (0..constructor_field_count(rule))
                        .map(|i| {
                            if i == idx {
                                quote! { __lead }
                            } else {
                                quote! { _ }
                            }
                        })
                        .collect();
                    Some(quote! {
                        #cat::#label(#(#binds),*) => __lead.__renders_sigil_led_primary(),
                    })
                },
                _ => None,
            }
        })
        .collect()
}

fn is_collection_mirror_infix(rule: &GrammarRule, language: &LanguageDef) -> bool {
    let Some(syntax_pattern) = rule.syntax_pattern.as_ref() else {
        return false;
    };
    // Exactly one operator literal and exactly two operand params.
    let mut operator: Option<&str> = None;
    let mut param_count = 0usize;
    for expr in syntax_pattern {
        match expr {
            SyntaxExpr::Literal(token) => {
                if operator.is_some() {
                    return false; // more than one terminal: not a simple binary infix
                }
                operator = Some(token.as_str());
            },
            SyntaxExpr::Param(_) => param_count += 1,
            // Sep/Zip/Map/Opt/Var: this rule is itself a collection/complex
            // form, not a bare binary infix.
            SyntaxExpr::Op(_) => return false,
            // L9-3: a token-kind consumption is not a bare binary infix operator.
            SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. } => return false,
        }
    }
    let Some(operator) = operator else {
        return false;
    };
    if param_count != 2 {
        return false;
    }
    let result_cat = rule.category.to_string();
    // Both operands must be Simple base params of the result category.
    let operand_categories: Vec<String> = rule
        .term_context
        .as_ref()
        .map(|tc| {
            tc.iter()
                .filter_map(|p| match p {
                    TermParam::Simple { ty: TypeExpr::Base(cat), .. } => Some(cat.to_string()),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default();
    if operand_categories.len() != 2 || operand_categories.iter().any(|cat| *cat != result_cat) {
        return false;
    }
    // A same-category collection rule whose element separator is this operator
    // and whose elements are themselves of the result category.
    language.terms.iter().any(|collection_rule| {
        if collection_rule.category.to_string() != result_cat {
            return false;
        }
        let Some(collection_syntax) = collection_rule.syntax_pattern.as_ref() else {
            return false;
        };
        collection_syntax.iter().any(|expr| match expr {
            SyntaxExpr::Op(PatternOp::Sep { collection, separator, .. }) => {
                separator == operator
                    && collection_param_element_category(collection_rule, &collection.to_string())
                        .as_deref()
                        == Some(result_cat.as_str())
            },
            _ => false,
        })
    })
}

// ════════════════════════════════════════════════════════════════════════════
// DISABLED 2026-07-26 — the four arm builders that consumed the borrowed wrapper.
// See the DEFECT 1 block comment above the (also disabled)
// `find_projection_surface_wrapper`. Retained verbatim; not deleted.
//
// Each arm rendered the source BARE at `min_bp == 0` and, at `min_bp > 0`, emitted
// the BORROWED rule's literal surface around it. The `min_bp == 0` half survives —
// it is exactly what `forwards_projection_{min_bp,param}` emits via
// `if min_bp == 0 { 0 } else { atomic_bp }` — so disabling these arms changes the
// `min_bp == 0` rendering NOT AT ALL and replaces only the `min_bp > 0` half:
// a borrowed constructor's surface becomes the source category's own
// precedence-driven `(` … `)`.
//
// fn simple_literal_param_pattern_ops(
//     syntax_pattern: &[SyntaxExpr],
//     param_name: &str,
//     task_variant: &syn::Ident,
//     field_ident: &syn::Ident,
// ) -> Option<Vec<TokenStream>> {
//     let mut forward_ops: Vec<TokenStream> = Vec::new();
//     for (i, expr) in syntax_pattern.iter().enumerate() {
//         match expr {
//             SyntaxExpr::Literal(s) => {
//                 let next_param = syntax_pattern
//                     .get(i + 1)
//                     .map(|e| matches!(e, SyntaxExpr::Param(_)));
//                 let prev_param =
//                     i > 0 && matches!(syntax_pattern.get(i - 1), Some(SyntaxExpr::Param(_)));
//                 let is_word = !s.is_empty()
//                     && s.chars().all(|c| c.is_alphanumeric() || c == '_')
//                     && !s.chars().next().unwrap().is_numeric();
//                 let (prefix, suffix) = if prev_param && next_param.unwrap_or(false) {
//                     (" ", " ")
//                 } else if next_param == Some(true) && is_word {
//                     ("", " ")
//                 } else {
//                     ("", "")
//                 };
//                 let raw = format!("{}{}{}", prefix, s, suffix);
//                 forward_ops.push(quote! {
//                     stack.push(DisplayTask::WriteString(#raw.to_string()));
//                 });
//             },
//             SyntaxExpr::Param(id) if id.to_string() == param_name => {
//                 forward_ops.push(quote! {
//                     stack.push(DisplayTask::#task_variant(&**#field_ident as *const _, 0u8));
//                 });
//             },
//             _ => return None,
//         }
//     }
//     forward_ops.reverse();
//     Some(forward_ops)
// }
//
// fn generate_projection_surface_display_arm_for_field(
//     rule: &GrammarRule,
//     field_name: &syn::Ident,
//     language: &LanguageDef,
// ) -> Option<TokenStream> {
//     if !rule.is_auto_injected {
//         return None;
//     }
//     let shape = classify_simple_projection_shape(rule)?;
//     if shape.source_category == shape.target_category {
//         return None;
//     }
//     let source_task_variant = format_ident!("Display{}", shape.source_category);
//     let (wrapper, param_name) =
//         find_projection_surface_wrapper(language, &shape.source_category, &shape.target_category)?;
//     let syntax_pattern = wrapper.syntax_pattern.as_ref()?;
//     let forward_ops = simple_literal_param_pattern_ops(
//         syntax_pattern,
//         &param_name,
//         &source_task_variant,
//         field_name,
//     )?;
//     let category = &rule.category;
//     let label = &rule.label;
//     Some(quote! {
//         #category::#label(#field_name) => {
//             if min_bp == 0 {
//                 stack.push(DisplayTask::#source_task_variant(&**#field_name as *const _, 0u8));
//             } else {
//                 #(#forward_ops)*
//             }
//         }
//     })
// }
//
// fn contextual_projection_surface_ops_for_field(
//     rule: &GrammarRule,
//     field_name: &syn::Ident,
//     language: &LanguageDef,
// ) -> Option<Vec<TokenStream>> {
//     let shape = classify_simple_projection_shape(rule)?;
//     if shape.source_category == shape.target_category {
//         return None;
//     }
//     let source_task_variant = format_ident!("Display{}", shape.source_category);
//     let (wrapper, param_name) =
//         find_projection_surface_wrapper(language, &shape.source_category, &shape.target_category)?;
//     let syntax_pattern = wrapper.syntax_pattern.as_ref()?;
//     simple_literal_param_pattern_ops(syntax_pattern, &param_name, &source_task_variant, field_name)
// }
//
// fn generate_contextual_projection_surface_display_arm_for_field(
//     rule: &GrammarRule,
//     field_name: &syn::Ident,
//     language: &LanguageDef,
// ) -> Option<TokenStream> {
//     let shape = classify_simple_projection_shape(rule)?;
//     if shape.source_category == shape.target_category {
//         return None;
//     }
//     let category = &rule.category;
//     let label = &rule.label;
//     let source_task_variant = format_ident!("Display{}", shape.source_category);
//     let wrapper_ops = contextual_projection_surface_ops_for_field(rule, field_name, language)?;
//     Some(quote! {
//         #category::#label(#field_name) => {
//             if min_bp == 0 {
//                 stack.push(DisplayTask::#source_task_variant(&**#field_name as *const _, 0u8));
//             } else {
//                 #(#wrapper_ops)*
//             }
//         }
//     })
// }
//
// fn generate_projection_surface_display_arm(
//     rule: &GrammarRule,
//     field_names: &[syn::Ident],
//     language: &LanguageDef,
// ) -> Option<TokenStream> {
//     generate_projection_surface_display_arm_for_field(rule, field_names.first()?, language)
// }

/// Generate arm for regular rules (no Var fields, no binders, no syntax_pattern).
///
/// Precedence-aware: for infix/postfix/prefix operators, wraps the output in
/// parentheses when the inherited `min_bp` exceeds the operator's own binding power.
/// Non-operator rules push children with `min_bp = 0`, except syntaxless
/// single-child projections, which preserve the surrounding boundary because
/// the wrapper has no surface syntax of its own. Same-category projections
/// forward the inherited threshold directly; cross-category projections render
/// a foreign-category child atomically whenever the wrapper appears as an
/// operand.
fn generate_engine_regular_arm(
    rule: &GrammarRule,
    fields: &[(String, Option<&syn::Ident>)],
    field_names: &[syn::Ident],
    _language: &LanguageDef,
    bp_lookup: &BpLookup,
) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;
    let label_str = label.to_string();
    let category_str = category.to_string();
    // DISABLED 2026-07-26 (DEFECT 1) — the projection-surface wrapper election.
    // Falling through to `forwards_projection_min_bp` below routes a cross-category
    // projection's source through `atomic_child_bp`, so the SOURCE's own precedence
    // logic emits the language's pure `(` … `)` grouping instead of a borrowed
    // constructor's surface. See the block comment above the disabled
    // `find_projection_surface_wrapper`.
    //
    // if let Some(auto_projection_arm) =
    //     generate_projection_surface_display_arm(rule, field_names, _language)
    // {
    //     return auto_projection_arm;
    // }
    // if field_names.len() == 1 {
    //     if let Some(contextual_projection_arm) =
    //         generate_contextual_projection_surface_display_arm_for_field(
    //             rule,
    //             &field_names[0],
    //             _language,
    //         )
    //     {
    //         return contextual_projection_arm;
    //     }
    // }
    let forwards_projection_min_bp = is_syntaxless_single_child_projection(rule);

    // Check if this rule is an infix/postfix/mixfix operator
    let infix_info = bp_lookup.infix.get(&label_str);
    // Check if this rule is a unary prefix operator
    let prefix_info = bp_lookup.prefix.get(&label_str);
    // FENCE CAPTURE: a Pratt-registered rule's LEADING slot is an operand whose
    // left edge binding power owns — see the header of this file.
    let rule_is_pratt = infix_info.is_some() || prefix_info.is_some();

    // Determine child min_bp values for each NonTerminal field
    // For infix: first NT gets left_bp, last NT gets right_bp
    // For prefix: single NT gets prefix_bp
    // For postfix: single NT gets left_bp
    // For mixfix: first NT gets left_bp, middle NTs get 0, last NT gets right_bp
    // For non-operator: all NTs get 0
    let nt_count = rule
        .items
        .iter()
        .filter(|i| matches!(i, GrammarItem::NonTerminal { .. }))
        .count();

    let mut forward_ops: Vec<TokenStream> = Vec::new();
    let mut field_iter = fields.iter().zip(field_names.iter());
    let mut nt_idx: usize = 0;

    for (item_idx, item) in rule.items.iter().enumerate() {
        match item {
            GrammarItem::Terminal(term) => {
                let escaped = term.clone();
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(#escaped.to_string()));
                });
            },
            GrammarItem::NonTerminal { ident: nt, .. } => {
                if let Some(((_, _), field_name)) = field_iter.next() {
                    let nt_str = nt.to_string();
                    let task_variant = format_ident!("Display{}", nt_str);

                    let child_min_bp: u8 = if let Some(info) = infix_info {
                        if info.is_postfix {
                            // Postfix: single operand gets left_bp
                            info.left_bp
                        } else if info.is_mixfix {
                            // Mixfix: first operand = left_bp, middle = 0, last = right_bp
                            if nt_idx == 0 {
                                info.left_bp
                            } else if nt_idx == nt_count - 1 {
                                info.right_bp
                            } else {
                                0
                            }
                        } else {
                            // Regular infix: left child = left_bp, right child = right_bp
                            if nt_idx == 0 {
                                info.left_bp
                            } else {
                                info.right_bp
                            }
                        }
                    } else if let Some(pinfo) = prefix_info {
                        // Unary prefix: child gets prefix_bp
                        pinfo.prefix_bp
                    } else {
                        0
                    };

                    // FENCE CAPTURE (2026-07-25): the guard materializes the
                    // child at `min_bp == 0`, which is faithful ONLY when the
                    // slot's inherited threshold is statically zero — i.e. when
                    // the slot is not precedence-governed. Both disqualifiers
                    // (a non-zero operand bp, a projection that forwards the
                    // parent's `min_bp`) are checked here rather than assumed
                    // from the leading/trailing exclusion in `item_fence_after`.
                    let fence_slot_is_bare = child_min_bp == 0 && !forwards_projection_min_bp;

                    let child_min_bp = if forwards_projection_min_bp {
                        if nt_str == category_str {
                            quote! { min_bp }
                        } else {
                            let atomic_bp = bp_lookup.atomic_child_bp(&nt_str);
                            quote! { if min_bp == 0 { 0 } else { #atomic_bp } }
                        }
                    } else {
                        quote! { #child_min_bp }
                    };

                    let fence_delims = match fence_slot_is_bare {
                        true => item_fence_after(&rule.items, item_idx, rule_is_pratt)
                            .and_then(|f| fence_slice_expr(None, Some(&f))),
                        false => None,
                    };
                    match fence_delims {
                        Some(delims) => forward_ops.push(quote! {
                            stack.push(DisplayTask::WriteString(
                                mettail_runtime::group_if_bare_delims(
                                    &#field_name.to_string(), #delims,
                                ),
                            ));
                        }),
                        None => forward_ops.push(quote! {
                            stack.push(DisplayTask::#task_variant(&**#field_name as *const _, #child_min_bp));
                        }),
                    }
                    nt_idx += 1;
                }
            },
            GrammarItem::Collection { coll_type, separator, delimiters, .. } => {
                if let Some(((_, _), field_name)) = field_iter.next() {
                    // A repetition element's fence set is `{ S }` plus the
                    // literal that TERMINATES the loop. When the collection
                    // carries its OWN delimiters the terminator is `close`
                    // (normally a bracket, hence vacuous) and the enclosing
                    // template literal is unreachable from inside them.
                    let loop_terminator: Option<String> = match delimiters {
                        Some((_, close)) => Some(close.clone()),
                        None => item_fence_after(&rule.items, item_idx, rule_is_pratt),
                    };
                    let elem_delims = fence_slice_expr(
                        Some(separator),
                        loop_terminator.as_deref().filter(|t| !fence_is_vacuous(t)),
                    )
                    .unwrap_or_else(|| quote! { &[] });
                    // Collection fields write inline (elements may not be deeply nested)
                    let sep = separator.clone();
                    // B9 / Class 2 (2026-05-08): branch on coll_type. Vec
                    // yields bare elements; HashBag yields (elem, count)
                    // tuples; HashSet yields bare elements with order
                    // preservation via sort. The previous unconditional
                    // (elem, count) pattern only matched HashBag and
                    // failed to compile when Vec collections appeared
                    // (e.g. Class-2 binder rule with Vec<Proc> slot or a
                    // Class-5 collection rule with Vec element type).
                    let items_expr = match coll_type {
                        // FENCE-CAPTURE grouping (separator half 2026-07-24,
                        // loop-terminator half 2026-07-25) — see the
                        // `PatternOp::Sep` arm below and
                        // `runtime/src/display_grouping.rs`. No-op unless an
                        // element's own text carries a fence at bracket depth 0.
                        mettail_ast::types::CollectionType::Vec => quote! {
                            let items: Vec<String> = #field_name.iter()
                                .map(|elem| mettail_runtime::group_if_bare_delims(&elem.to_string(), #elem_delims))
                                .collect();
                        },
                        mettail_ast::types::CollectionType::HashSet => quote! {
                            let mut items: Vec<String> = #field_name.iter()
                                .map(|elem| mettail_runtime::group_if_bare_delims(&elem.to_string(), #elem_delims))
                                .collect();
                            items.sort();
                        },
                        mettail_ast::types::CollectionType::HashBag => quote! {
                            let mut items: Vec<String> = #field_name.iter().map(|(elem, count)| {
                                (0..count)
                                    .map(|_| mettail_runtime::group_if_bare_delims(&elem.to_string(), #elem_delims))
                                    .collect::<Vec<_>>()
                                    .join(&format!(" {} ", #sep))
                            }).collect();
                            items.sort();
                        },
                        mettail_ast::types::CollectionType::HashMap => quote! {
                            // HashMap display path is handled separately;
                            // defensive fallback that yields each entry's
                            // Display form. Pilot grammars do not exercise
                            // HashMap-in-binder Class 2.
                            let mut items: Vec<String> = #field_name.iter()
                                .map(|(k, v)| format!("{} : {}", k, v))
                                .collect();
                            items.sort();
                        },
                        // #74: a `PathMap` value is a `PathValue`; an `Unset`
                        // entry renders as the BARE KEY, with no separator.
                        // (`PathMap` is not admissible as an INLINE binder
                        // collection type — `binder.rs` rejects it at its
                        // `_ => return None` collection arm — so this arm is
                        // unreachable today; it is written correctly rather than
                        // merely compilably so it stays right if that changes.)
                        mettail_ast::types::CollectionType::PathMap => quote! {
                            let mut items: Vec<String> = #field_name.iter()
                                .map(|(k, v)| match v {
                                    mettail_runtime::PathValue::Unset => format!("{}", k),
                                    mettail_runtime::PathValue::Set(inner) => {
                                        format!("{} : {}", k, inner)
                                    },
                                })
                                .collect();
                            items.sort();
                        },
                    };
                    if let Some((open, close)) = delimiters {
                        forward_ops.push(quote! {
                            {
                                let mut s = String::from(#open);
                                #items_expr
                                if !items.is_empty() {
                                    s.push_str(&items.join(&format!(" {} ", #sep)));
                                }
                                s.push_str(#close);
                                stack.push(DisplayTask::WriteString(s));
                            }
                        });
                    } else {
                        forward_ops.push(quote! {
                            {
                                #items_expr
                                stack.push(DisplayTask::WriteString(items.join(&format!(" {} ", #sep))));
                            }
                        });
                    }
                    nt_idx += 1;
                }
            },
            GrammarItem::Binder { .. } => {
                // Handled in binder path
            },
        }
    }

    // Reverse so stack processes left-to-right
    forward_ops.reverse();

    // Wrap in parenthesization logic for infix/prefix/postfix operators.
    //
    // Parenthesization is decided PURELY by precedence (`own_left_bp <
    // min_bp`): an operator wraps itself in `(…)` exactly when the inherited
    // threshold from its parent context exceeds its own left binding power.
    // This is the standard Pratt-symmetric rule and it makes Display a
    // one-cycle fixed point: the parser's binding-power table (the same
    // `analyze_binding_powers` output) re-derives the identical grouping
    // from the parenthesis-minimal surface, so `display(parse(display(t)))`
    // == `display(parse(t))` for every well-formed `t`.
    //
    // (2026-06-22) The earlier `|| (shadowed_by_syntaxless_projection &&
    // min_bp != 0)` disjunct was REMOVED. It force-parenthesized every
    // non-root occurrence of any operator whose result category is the
    // target of a syntaxless projection (e.g. every `BigInt` `+`/`-`/`bitand`
    // because `Int` projects syntaxlessly into `BigInt` and shares those
    // terminals). Those parentheses are precedence-REDUNDANT — a syntaxless
    // projection contributes no surface token, so it cannot change the
    // grouping the parser recovers — and they BREAK one-cycle idempotence:
    // the redundant parens are dropped on the second display, so the
    // canonical form oscillates between the parenthesized and bare forms.
    // (At the ambiguity-budget boundary the two surface forms even elect
    // different parse winners — `IntToBigInt(AddInt(…))` vs
    // `AddBigInt(…)` — which displayed to each other forever; see
    // `gen_calculator_prop::bigint_display_parse_roundtrip`.) The genuinely
    // necessary disambiguation parentheses for a syntaxless-projection node
    // used AS an operand (e.g. `(816675508 <= cast_error_int) bitand …` for a
    // `BoolToUInt32`-wrapped comparison) are emitted by the projection node's
    // own `forwards_projection_min_bp` path below, NOT by this flag.
    if let Some(info) = infix_info {
        let own_left_bp = info.left_bp;
        quote! {
            #category::#label(#(#field_names),*) => {
                let needs_parens = #own_left_bp < min_bp;
                if needs_parens {
                    stack.push(DisplayTask::WriteLiteral(")"));
                }
                #(#forward_ops)*
                if needs_parens {
                    stack.push(DisplayTask::WriteLiteral("("));
                }
            }
        }
    } else if let Some(pinfo) = prefix_info {
        let own_bp = pinfo.prefix_bp;
        quote! {
            #category::#label(#(#field_names),*) => {
                let needs_parens = #own_bp < min_bp;
                if needs_parens {
                    stack.push(DisplayTask::WriteLiteral(")"));
                }
                #(#forward_ops)*
                if needs_parens {
                    stack.push(DisplayTask::WriteLiteral("("));
                }
            }
        }
    } else {
        quote! {
            #category::#label(#(#field_names),*) => {
                #(#forward_ops)*
            }
        }
    }
}

/// Generate arm for old-style binder rules.
fn generate_engine_binder_arm(rule: &GrammarRule, _language: &LanguageDef) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Collect regular fields (not binder, not body)
    let mut regular_fields = Vec::new();
    let mut has_scope = false;
    let mut field_idx = 0;

    for (i, item) in rule.items.iter().enumerate() {
        match item {
            GrammarItem::NonTerminal { .. } if i == body_idx => {
                has_scope = true;
            },
            GrammarItem::NonTerminal { .. } => {
                regular_fields.push(format!("f{}", field_idx));
                field_idx += 1;
            },
            GrammarItem::Binder { .. } if i == *binder_idx => {
                // Skip - it's in the scope
            },
            _ => {},
        }
    }

    let mut all_fields = regular_fields.clone();
    if has_scope {
        all_fields.push("scope".to_string());
    }

    let field_idents: Vec<syn::Ident> = all_fields
        .iter()
        .map(|name| syn::Ident::new(name, proc_macro2::Span::call_site()))
        .collect();

    // Build forward push operations from items.
    // The binder name and body come from scope.inner().
    let mut forward_ops: Vec<TokenStream> = Vec::new();
    let mut regular_field_iter = regular_fields.iter();

    // Get the body category from the rule
    // ★ #141 G5 — see `crate::gen::shape_refusal`.
    let GrammarItem::NonTerminal { ident: body_cat, .. } = &rule.items[body_idx] else {
        return crate::gen::shape_refusal(
            &rule.label,
            "declares a binding whose body index does not point at a non-terminal item",
        );
    };
    let body_cat = body_cat.clone();
    let body_task_variant = format_ident!("Display{}", body_cat);

    for (i, item) in rule.items.iter().enumerate() {
        match item {
            GrammarItem::Terminal(term) => {
                let escaped = term.clone();
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(#escaped.to_string()));
                });
            },
            GrammarItem::NonTerminal { .. } if i == body_idx => {
                // Body from scope — binder body resets precedence context
                forward_ops.push(quote! {
                    stack.push(DisplayTask::#body_task_variant(&*inner.unsafe_body as *const _, 0));
                });
            },
            GrammarItem::NonTerminal { ident: nt, .. } => {
                // Regular field — non-binder context resets precedence
                if let Some(field_name_str) = regular_field_iter.next() {
                    let field_name =
                        syn::Ident::new(field_name_str, proc_macro2::Span::call_site());
                    let nt_str = nt.to_string();
                    let task_variant = format_ident!("Display{}", nt_str);
                    // FENCE CAPTURE — the slot renders at min_bp 0 here by
                    // construction ("non-binder context resets precedence"), so
                    // the materialized text is faithful.
                    // Binder rules are never Pratt operators (see the
                    // `has_abstraction` arms: "Abstraction rules are never
                    // infix, no parenthesization needed").
                    match item_fence_after(&rule.items, i, false)
                        .and_then(|f| fence_slice_expr(None, Some(&f)))
                    {
                        Some(delims) => forward_ops.push(quote! {
                            stack.push(DisplayTask::WriteString(
                                mettail_runtime::group_if_bare_delims(
                                    &#field_name.to_string(), #delims,
                                ),
                            ));
                        }),
                        None => forward_ops.push(quote! {
                            stack.push(DisplayTask::#task_variant(&**#field_name as *const _, 0));
                        }),
                    }
                }
            },
            GrammarItem::Binder { .. } if i == *binder_idx => {
                // Binder name from scope
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(binder_name.to_string()));
                });
            },
            GrammarItem::Binder { .. } => {},
            GrammarItem::Collection { .. } => {
                // Unlikely in binder rules, but handle gracefully
            },
        }
    }

    forward_ops.reverse();

    quote! {
        #category::#label(#(#field_idents),*) => {
            let inner = scope.inner();
            let binder_name = inner.unsafe_pattern.0.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
            #(#forward_ops)*
        }
    }
}

/// Generate arm for new-style syntax_pattern rules.
///
/// Precedence-aware: for infix/postfix/prefix operators, wraps the output in
/// parentheses when the inherited `min_bp` exceeds the operator's own binding power.
/// L9-4: the opener/closer DELIMITER strings for a guest-body's `open`/`close`
/// token KIND names, so `Display` can reconstruct `<tag><open><body><close>`.
/// Derived from the FLT naming convention (`FltOpen{Backtick,Brace,Fence}` /
/// `FltClose*`): a `Backtick`-suffixed kind uses `` ` ``, `Brace` uses `{`/`}`,
/// `Fence` uses ```` ``` ````. A kind that matches none prints no delimiter
/// (the tag+body still round-trips when the body itself is self-delimiting).
pub(crate) fn flt_delimiters_for(
    open_name: &str,
    close_name: &str,
) -> (&'static str, &'static str) {
    let open = if open_name.contains("Backtick") {
        "`"
    } else if open_name.contains("Brace") {
        "{"
    } else if open_name.contains("Fence") {
        "```"
    } else {
        ""
    };
    let close = if close_name.contains("Backtick") {
        "`"
    } else if close_name.contains("Brace") {
        "}"
    } else if close_name.contains("Fence") {
        "```"
    } else {
        ""
    };
    (open, close)
}

/// L9-3: linear Display arm for a capture-bearing rule. Fields are bound in
/// `capture_layout` order (identical to the enum definition and the walker
/// constructor), and each syntax position prints in encounter order separated
/// by a single space — a token's captured text prints verbatim, so re-lexing
/// the printed form yields the same tokens (`parse(display(t)) == t`).
fn generate_capture_display_arm(
    rule: &GrammarRule,
    syntax_pattern: &[SyntaxExpr],
    term_context: &[TermParam],
) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;
    let layout = capture_layout(term_context, syntax_pattern)
        .expect("generate_capture_display_arm requires a capture-bearing rule");

    // Pattern bindings in variant-field order (non-scope fields, then Scope).
    let mut pats: Vec<TokenStream> = Vec::new();
    for f in &layout.non_scope {
        let name = format_ident!("{}", f.name);
        pats.push(quote! { #name });
    }
    if layout.scope.is_some() {
        pats.push(quote! { _scope });
    }

    // Resolve a simple param's base category (for a Display recursion task).
    let simple_cat = |name: &str| -> Option<syn::Ident> {
        term_context.iter().find_map(|p| match p {
            TermParam::Simple { name: n, ty: TypeExpr::Base(cat) } if n.to_string() == name => {
                Some(cat.clone())
            },
            _ => None,
        })
    };

    let mut forward_ops: Vec<TokenStream> = Vec::new();
    let mut emitted = false;
    for expr in syntax_pattern {
        // A single separating space between adjacent printed positions.
        let space = if emitted {
            quote! { stack.push(DisplayTask::WriteString(" ".to_string())); }
        } else {
            quote! {}
        };
        match expr {
            SyntaxExpr::Literal(s) => {
                forward_ops.push(space);
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(#s.to_string()));
                });
                emitted = true;
            },
            SyntaxExpr::TokenKind { name, bind } => {
                forward_ops.push(space);
                let ident = bind
                    .as_ref()
                    .map(|b| format_ident!("{}", b.to_string()))
                    .unwrap_or_else(|| format_ident!("__tok_{}", name));
                // The captured token's text prints verbatim (bound `&String`).
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(#ident.clone()));
                });
                emitted = true;
            },
            SyntaxExpr::GuestBody { open, close, bind } => {
                forward_ops.push(space);
                let field = format_ident!("{}", bind.to_string());
                // Reconstruct the guest region: `<tag><open_delim><body_src>
                // <close_delim>`. `body_src` already carries the `${…}` holes
                // verbatim; the delimiters (derived from the FLT opener/closer
                // kind names) re-lex to the same opener/closer kinds, so the
                // printed form round-trips.
                let (open_delim, close_delim) =
                    flt_delimiters_for(&open.to_string(), &close.to_string());
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(format!(
                        "{}{}{}{}",
                        #field.tag, #open_delim, #field.body_src, #close_delim,
                    )));
                });
                emitted = true;
            },
            SyntaxExpr::Param(id) => {
                if let Some(cat) = simple_cat(&id.to_string()) {
                    forward_ops.push(space);
                    let task = format_ident!("Display{}", cat);
                    let field = format_ident!("{}", id.to_string());
                    forward_ops.push(quote! {
                        stack.push(DisplayTask::#task(&**#field as *const _, 0));
                    });
                    emitted = true;
                }
                // Abstraction binder/body params fold into the trailing Scope
                // (bound `_scope`); a capture+binder rule is not exercised by
                // any grammar, and its Scope body render is deferred.
            },
            SyntaxExpr::Op(_) => {
                // Sep/Zip/Map/Opt never co-occur with a capture in one rule.
            },
        }
    }

    forward_ops.reverse();
    quote! {
        #category::#label(#(#pats),*) => {
            #(#forward_ops)*
        }
    }
}

fn generate_engine_syntax_pattern_arm(
    rule: &GrammarRule,
    syntax_pattern: &[SyntaxExpr],
    term_context: &[TermParam],
    language: &LanguageDef,
    bp_lookup: &BpLookup,
) -> TokenStream {
    generate_engine_syntax_pattern_arm_inner(
        rule,
        syntax_pattern,
        term_context,
        language,
        bp_lookup,
        None,
    )
}

/// The body of [`generate_engine_syntax_pattern_arm`], with the MATCH-PATTERN variant name
/// optionally overridden.
///
/// `match_label_override` is `Some` only on the surface-synonymy re-route path
/// (`generate_engine_rule_arm_as`): every use of `label` below that selects a BINDING POWER, a
/// syntax position, or a chain-walk of the rule's own variant keeps the rule's own label, and
/// only the five arm-head emissions use the override. `None` reproduces the pre-2026-07-26
/// generator exactly.
fn generate_engine_syntax_pattern_arm_inner(
    rule: &GrammarRule,
    syntax_pattern: &[SyntaxExpr],
    term_context: &[TermParam],
    _language: &LanguageDef,
    bp_lookup: &BpLookup,
    match_label_override: Option<&syn::Ident>,
) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;
    let label_str = label.to_string();
    // The variant the emitted arm MATCHES on. Identical to `label` unless this arm is a
    // surface-synonymy re-route.
    let match_label: &syn::Ident = match_label_override.unwrap_or(label);

    // L9-3 (ROUND-TRIP-CRITICAL): a rule with a `v@Tok` capture is never an
    // infix Pratt operator — it renders LINEARLY. Bind fields in
    // `capture_layout` order (matching the enum) and print each syntax
    // position (literal / captured token text / param) left-to-right, space
    // separated, so `parse(display(t)) == t`.
    if capture_layout(term_context, syntax_pattern).is_some() {
        return generate_capture_display_arm(rule, syntax_pattern, term_context);
    }

    // Check if this rule is an infix/postfix/mixfix operator
    let infix_info = bp_lookup.infix.get(&label_str);
    // Check if this rule is a unary prefix operator
    let prefix_info = bp_lookup.prefix.get(&label_str);
    // FENCE CAPTURE: a Pratt-registered rule's LEADING slot is an operand whose
    // left edge binding power owns — see the header of this file.
    let rule_is_pratt = infix_info.is_some() || prefix_info.is_some();

    // W3 (Neg-zero display canonicalization): if this rule is a unary-prefix
    // `"-" a` operator over a numeric native-type category, we emit a runtime
    // pre-scan so that `Neg(…Neg(Zero)…)` renders the `a` portion without
    // the leading `-`. AST and evaluation are unchanged — Float specifically
    // retains its `-0.0` bit pattern; we just normalize the printed form.
    // Activated later in the `needs_bp_check` emission branch; here we only
    // build the pre-scan expression so the arm can reference it.
    let neg_zero_prescan: Option<TokenStream> = (|| {
        prefix_info?; // only unary-prefix rules
        if syntax_pattern.len() != 2 {
            return None;
        }
        let is_minus = matches!(
            syntax_pattern.first(),
            Some(SyntaxExpr::Literal(s)) if s == "-"
        );
        if !is_minus {
            return None;
        }
        let param_name = match syntax_pattern.get(1) {
            Some(SyntaxExpr::Param(id)) => id.to_string(),
            _ => return None,
        };
        // The unary param must be of this rule's own category (same-cat
        // negation), so the inner-variant pattern `#category::#label(inner)`
        // is well-typed for chain walking.
        let param_ty = term_context.iter().find_map(|p| match p {
            TermParam::Simple { name, ty } if name.to_string() == param_name => Some(ty),
            _ => None,
        })?;
        let TypeExpr::Base(param_cat) = param_ty else {
            return None;
        };
        if param_cat != category {
            return None;
        }
        let lang_type = _language.types.iter().find(|t| &t.name == param_cat)?;
        let native_type = lang_type.native_type.as_ref()?;
        use crate::gen::native::NativeType;
        let nt = NativeType::from_syn_type(native_type);
        let lit_label = generate_literal_label(native_type);
        let param_ident = syn::Ident::new(&param_name, proc_macro2::Span::call_site());

        // Per-type literal-zero test, applied inside the match arm that binds
        // `v` to the literal payload.
        // Use the canonical wrappers' inner accessors + `num_traits::Zero` on
        // the underlying value (the canonical types themselves don't impl Zero
        // — see `runtime/src/canonical_*.rs`). Float comes through as a value,
        // not a reference, so `==` against `0.0` covers both `+0.0` and `-0.0`
        // (which is exactly what we want — display canonicalization, not
        // bit-pattern preservation).
        let zero_check: TokenStream = match &nt {
            NativeType::Float32 | NativeType::Float64 => quote! { v.get() == 0.0 },
            NativeType::CanonicalBigRat => quote! {
                <num_rational::Ratio<num_bigint::BigInt> as num_traits::Zero>::is_zero(v.get())
            },
            NativeType::CanonicalFixedPoint => quote! {
                <num_bigint::BigInt as num_traits::Zero>::is_zero(v.unscaled())
            },
            NativeType::CanonicalBigInt => quote! {
                <num_bigint::BigInt as num_traits::Zero>::is_zero(v.get())
            },
            _ if nt.is_integer() => quote! { *v == 0 },
            _ => return None,
        };

        Some(quote! {
            {
                let mut cur: &#category = #param_ident.as_ref();
                loop {
                    match cur {
                        #category::#label(__neg_inner) => {
                            cur = __neg_inner.as_ref();
                        }
                        #category::#lit_label(v) => break #zero_check,
                        _ => break false,
                    }
                }
            }
        })
    })();

    // Analyze term_context to understand the structure
    let mut param_names: Vec<String> = Vec::new();
    let mut has_abstraction = false;
    let mut is_multi_binder = false;
    let mut abstraction_binder: Option<String> = None;
    let mut abstraction_body: Option<String> = None;
    // Map from param name -> TypeExpr for looking up category
    let mut param_types: HashMap<String, &TypeExpr> = HashMap::new();
    // Task #14 (Option<Guard>): guard slot names. Guards register into
    // `param_names` but are ABSENT from `param_types` (they have no
    // TypeExpr) — the same is true of Abstraction binders, so "absent from
    // param_types" is NOT a usable discriminator; an explicit set is.
    // Threaded into `generate_engine_pattern_op` so the `#opt(...)` inner
    // bindings can skip the Arc-deref map for `Option<BehavioralPred>`.
    let mut guard_params: HashSet<String> = HashSet::new();

    // Opt-Group: flatten the term context so inner params of `#opt(...)`
    // are visible to the display generator with the same name resolution
    // as top-level params. The display impl handles Option<T> wrapping
    // by emitting inner literals/params only when the Option is Some.
    fn flatten_params<'a>(params: &'a [TermParam], out: &mut Vec<&'a TermParam>) {
        for p in params {
            match p {
                TermParam::Optional { params: inner } => flatten_params(inner, out),
                _ => out.push(p),
            }
        }
    }
    let mut flat: Vec<&TermParam> = Vec::new();
    flatten_params(term_context, &mut flat);

    for param in flat {
        match param {
            TermParam::Simple { name, ty } => {
                param_names.push(name.to_string());
                param_types.insert(name.to_string(), ty);
            },
            TermParam::Abstraction { binder, body, ty: _ } => {
                has_abstraction = true;
                abstraction_binder = Some(binder.to_string());
                abstraction_body = Some(body.to_string());
                let _ = body;
            },
            TermParam::MultiAbstraction { binder, body, ty: _ } => {
                has_abstraction = true;
                is_multi_binder = true;
                abstraction_binder = Some(binder.to_string());
                abstraction_body = Some(body.to_string());
                let _ = body;
            },
            TermParam::GuardBody { name } => {
                // Phase 2E: register the guard slot's name so the
                // syntax pattern's reference resolves and the
                // per-instance BehavioralPred field is rendered.
                param_names.push(name.to_string());
                guard_params.insert(name.to_string());
            },
            TermParam::Optional { .. } => {
                // Already flattened — unreachable.
                unreachable!("Optional should have been flattened");
            },
        }
    }

    // DISABLED 2026-07-26 (DEFECT 1) — the projection-surface wrapper election.
    // This is the LIVE site for every shipped grammar: `auto_inject.rs` always emits
    // a `syntax_pattern` for the projections it synthesizes, and every hand-written
    // cast (`CastInt . k:Int |- k : Proc`) has one too, so `generate_engine_rule_arm`
    // routes them all here rather than to `generate_engine_regular_arm`. Falling
    // through leaves them to `forwards_projection_param` below, which renders the
    // source at `atomic_child_bp` and so gets the source category's own
    // `WriteLiteral("(")` / `WriteLiteral(")")` — nothing borrowed, nothing denoted.
    // See the block comment above the disabled `find_projection_surface_wrapper`.
    //
    // if !has_abstraction && param_names.len() == 1 {
    //     let field_ident = syn::Ident::new(&param_names[0], proc_macro2::Span::call_site());
    //     if let Some(surface_projection_arm) =
    //         generate_projection_surface_display_arm_for_field(rule, &field_ident, _language)
    //     {
    //         return surface_projection_arm;
    //     }
    //     if let Some(contextual_projection_arm) =
    //         generate_contextual_projection_surface_display_arm_for_field(
    //             rule,
    //             &field_ident,
    //             _language,
    //         )
    //     {
    //         return contextual_projection_arm;
    //     }
    // }

    let forwards_projection_param = if !has_abstraction && syntax_pattern.len() == 1 {
        if let SyntaxExpr::Param(id) = &syntax_pattern[0] {
            let name = id.to_string();
            if param_names.len() == 1
                && param_names[0] == name
                && matches!(param_types.get(name.as_str()), Some(TypeExpr::Base(_)))
            {
                Some(name)
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };

    // Count non-terminal parameters for infix position tracking
    // For new-style syntax, params appearing in the syntax_pattern as base-category
    // types are the "operand" nonterminals.
    let base_cat_params: Vec<String> = param_names
        .iter()
        .filter(|name| {
            if let Some(ty) = param_types.get(name.as_str()) {
                matches!(ty, TypeExpr::Base(_))
            } else {
                false
            }
        })
        .cloned()
        .collect();
    let nt_count = base_cat_params.len();

    // Determine body category from the abstraction type for pushing tasks
    let body_cat_ident = if has_abstraction {
        // Find the abstraction's type and get the codomain
        let abs_type = term_context.iter().find_map(|p| match p {
            TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => Some(ty),
            _ => None,
        });
        if let Some(TypeExpr::Arrow { codomain, .. }) = abs_type {
            Some(extract_base_category_ident(codomain))
        } else {
            None
        }
    } else {
        None
    };

    // Compute a map from param name -> child min_bp for infix/prefix rules
    let child_bp_map: HashMap<String, u8> = if let Some(info) = infix_info {
        let mut map = HashMap::new();
        if is_collection_mirror_infix(rule, _language) {
            // Collection-mirror infix (e.g. `PParInfix` `|` mirrors the `PPar`
            // bag): the loosest-binding associative combinator. Render its
            // operands bare (min_bp 0) exactly like the collection twin's
            // elements — otherwise a cross-category projection operand (e.g.
            // `CastBigInt`) borrows a projection-surface wrapper in operand
            // position and `1 | 2` mis-renders as `@Nil!(1) | @Nil!(2)`.
            for name in &base_cat_params {
                map.insert(name.clone(), 0u8);
            }
        } else if info.is_postfix {
            // Postfix: single operand gets left_bp
            if let Some(name) = base_cat_params.first() {
                map.insert(name.clone(), info.left_bp);
            }
        } else if info.is_mixfix {
            // Mixfix: first operand = left_bp, middle = 0, last = right_bp
            for (idx, name) in base_cat_params.iter().enumerate() {
                if idx == 0 {
                    map.insert(name.clone(), info.left_bp);
                } else if idx == nt_count - 1 {
                    map.insert(name.clone(), info.right_bp);
                } else {
                    map.insert(name.clone(), 0u8);
                }
            }
        } else {
            // Regular infix: first param = left_bp, second param = right_bp
            if let Some(name) = base_cat_params.first() {
                map.insert(name.clone(), info.left_bp);
            }
            if base_cat_params.len() >= 2 {
                map.insert(base_cat_params[1].clone(), info.right_bp);
            }
        }
        map
    } else if let Some(pinfo) = prefix_info {
        // Unary prefix: single operand gets prefix_bp
        let mut map = HashMap::new();
        if let Some(name) = base_cat_params.first() {
            map.insert(name.clone(), pinfo.prefix_bp);
        }
        map
    } else {
        HashMap::new()
    };

    // Build forward push operations from syntax_pattern
    let mut forward_ops: Vec<TokenStream> = Vec::new();

    for (i, expr) in syntax_pattern.iter().enumerate() {
        match expr {
            SyntaxExpr::Literal(s) => {
                let next_param = syntax_pattern
                    .get(i + 1)
                    .map(|e| matches!(e, SyntaxExpr::Param(_)));
                let prev_param =
                    i > 0 && matches!(syntax_pattern.get(i - 1), Some(SyntaxExpr::Param(_)));
                // Roundtrip fix (2026-07-01): a pattern-op element
                // (`SyntaxExpr::Op` — a repeated-with-separator `bs.*sep("&")`,
                // or a `#map`/`#zip` chain) emits PARAM VALUES as its leading /
                // trailing tokens, and those values can be identifiers. For the
                // WORD-adjacency spacing decision below (does a keyword-literal
                // risk glomming with an adjacent emitted identifier?), an `Op`
                // neighbour is therefore exactly as word-adjacent as a bare
                // `Param`. Treat them uniformly.
                //
                // Bug fixed: `ForRowWhere = b "&" bs.*sep("&") "where" cond`
                // displayed `<a>where <cond>` — no space BEFORE the `where`
                // keyword — because the element preceding `"where"` is an `Op`
                // (`bs.*sep("&")`), not a `Param`, so the old `prev_param` guard
                // was false and the leading space was dropped. The result
                // `@Nil <= @Nil&awhere error` then re-lexes `awhere` as ONE
                // identifier (the lexer's `is_alphanumeric()||'_'` keyword rule)
                // and fails to parse — a Display/parse roundtrip break surfaced
                // nondeterministically by `arb_*` (a persistent/plain `where`
                // row with a var immediately before `where`). Only ADDS a space
                // where a word-literal abuts a param-value-emitting neighbour, so
                // it can never introduce a glom; it never removes a space.
                //
                // NOTE: the `next_word_adjacent` (SUFFIX) half only concerns a
                // word-literal FOLLOWED by an `Op` whose first emitted token is
                // an identifier. That case is rare and, when the Op's first token
                // is a delimiter (`(`,`{`,`[`) rather than an identifier, adding a
                // trailing space is unnecessary (harmless but perturbs canonical
                // display). We restrict the ADDED behavior to the PREFIX side (a
                // word-literal PRECEDED by an Op) which is the exact `where`-glom
                // bug; the suffix side stays as the pre-existing behavior.
                let prev_op_adjacent =
                    i > 0 && matches!(syntax_pattern.get(i - 1), Some(SyntaxExpr::Op(_)));
                // 2026-07-24: the SUFFIX twin of `prev_op_adjacent` — a
                // word-literal immediately FOLLOWED by an `Op` (see the
                // `is_word && (prev_op_adjacent || next_op_adjacent)` arm below).
                let next_op_adjacent = matches!(syntax_pattern.get(i + 1), Some(SyntaxExpr::Op(_)));
                // Stage 3.3 (2026-04-30): broaden `is_word` to mirror the
                // lexer's keyword-recognition rule
                // (`prattail/src/lexer.rs:523`): `is_alphanumeric() || '_'`,
                // not just `is_alphabetic()`. A literal like `"r2d2"` IS an
                // identifier-like keyword to the lexer; failing to space it
                // from adjacent ident-char text would re-lex into a single
                // glommed Ident. Guard against empty literals (vacuously
                // true) and digit-leading literals (those parse as Integer,
                // not as keywords).
                let is_word = !s.is_empty()
                    && s.chars().all(|c| c.is_alphanumeric() || c == '_')
                    && !s.chars().next().unwrap().is_numeric();
                let (prefix, suffix) = if prev_param && next_param.unwrap_or(false) {
                    (" ", " ")
                } else if next_param == Some(true) && is_word {
                    // Word-literal FOLLOWED by a param (existing behavior: space
                    // after). PLUS: when the PRECEDING element is an `Op`
                    // (repeated-param that emits identifier values), also add a
                    // LEADING space — the exact `where`-glom fix (`bs.*sep("&")
                    // "where" cond`). This is the ONLY added case; it strictly
                    // adds a space (never removes one) between an identifier-
                    // emitting Op and a following keyword.
                    if prev_op_adjacent {
                        (" ", " ")
                    } else {
                        ("", " ")
                    }
                } else if is_word && (prev_op_adjacent || next_op_adjacent) {
                    // Word-literal keyword ABUTTING an `Op` on either side. An
                    // `Op` emits PARAM VALUES, which can be identifiers, so a
                    // word-literal touching one gloms exactly as it would touch
                    // a bare `Param`.
                    //
                    // - PREFIX half (`prev_op_adjacent`, 2026-07-01): a trailing
                    //   keyword after a list, e.g. ForRow's
                    //   `bs.*sep("&") "where" cond` → `…&a where …`, not
                    //   `…&awhere …`.
                    // - SUFFIX half (`next_op_adjacent`, 2026-07-24): a LEADING
                    //   keyword before a list, e.g. PNew's
                    //   `"new" xs.*sep(",") "in" p` → `new x in …`, not
                    //   `newx in …` (which re-lexes as the single Ident `newx`
                    //   and breaks the Display→parse roundtrip). This completes
                    //   the symmetry the 2026-07-01 fix deliberately deferred as
                    //   "rare"; `PNew` is the only word-literal-before-`Op`
                    //   production in the repo, so no other rule's canonical
                    //   display moves.
                    //
                    // Byte-identical to the previous `(" ", "")` whenever
                    // `next_op_adjacent` is false; it only ever ADDS a space.
                    (
                        if prev_op_adjacent { " " } else { "" },
                        if next_op_adjacent { " " } else { "" },
                    )
                } else {
                    ("", "")
                };
                let raw = format!("{}{}{}", prefix, s, suffix);
                // Roundtrip fix (2026-07-01): a MANDATORY separator literal that
                // immediately precedes a matching `.*sep(S)` rest-list which is the
                // LAST element of the production (the trailing one-or-more idiom
                // `… X S bs.*sep(S)` with NOTHING after it — e.g. ForRow's
                // `b "&" bs.*sep("&")` and `lhs "<=" n "&" bs.*sep("&")`) is
                // UNPARSEABLE when the rest-list is empty: `b "&" <empty>` displays
                // `b&`, but with nothing following the `&` the grammar requires `bs`
                // non-empty (the parser has no way to know the list ended). Such an
                // empty-rest-list AST (`ForRowNoWhere(b, [])`) is degenerate — the
                // parser never produces it (it produces the `Single*` variant with
                // NO separator) — but the term generator can, and the roundtrip
                // contract (`Proc::parse(display(t))` must succeed for ANY generated
                // `t`) then breaks. FIX: emit the trailing mandatory separator only
                // when the rest-list is NON-EMPTY, so the degenerate AST displays as
                // its parseable equivalent (`b` alone, which re-parses to the
                // `Single*` variant).
                //
                // CRUCIAL SCOPE (verified empirically, control C1): this applies
                // ONLY when the `.*sep` op is the LAST syntax element. When a
                // mandatory token FOLLOWS the rest-list (`"where" cond`, `")"`,
                // `"<-" n`, …), the empty-rest-list form is SELF-CONSISTENT — it
                // displays with a "dangling" separator (`@Nil,<-@Nil`, `@Nil!(Nil,)`,
                // `@Nil <- @Nil& where Nil`) that PARSES BACK to the same empty-list
                // variant (the following token delimits the empty list), so dropping
                // the separator there would BREAK the roundtrip (regressed
                // `unit_rholang_inputbind_inputbindpolyadic` etc.). So we gate on the
                // op being the final element. Spec-derived from the syntax pattern
                // (no per-rule hardcoding); preserves Display for every non-degenerate
                // AST and for every self-consistent trailing-token rule.
                let sep_op_is_last = matches!(
                    syntax_pattern.get(i + 1),
                    Some(SyntaxExpr::Op(PatternOp::Sep { .. }))
                ) && syntax_pattern.get(i + 2).is_none();
                let mandatory_sep_before_trailing_restlist = if sep_op_is_last {
                    syntax_pattern.get(i + 1).and_then(|nxt| match nxt {
                        SyntaxExpr::Op(PatternOp::Sep { collection, separator, source: None })
                            if separator == s =>
                        {
                            Some(collection.clone())
                        },
                        _ => None,
                    })
                } else {
                    None
                };
                match mandatory_sep_before_trailing_restlist {
                    Some(coll_ident) => {
                        // Guard the trailing separator on the rest-list being
                        // non-empty. `.iter().next().is_some()` works for every
                        // collection wrapper (Vec / HashBag / HashSet / HashMapLit).
                        forward_ops.push(quote! {
                            if #coll_ident.iter().next().is_some() {
                                stack.push(DisplayTask::WriteString(#raw.to_string()));
                            }
                        });
                    },
                    None => {
                        forward_ops.push(quote! {
                            stack.push(DisplayTask::WriteString(#raw.to_string()));
                        });
                    },
                }
            },
            SyntaxExpr::Param(id) => {
                let name = id.to_string();

                if Some(&name) == abstraction_binder.as_ref() {
                    // Binder name from scope.unbind()
                    forward_ops.push(quote! {
                        stack.push(DisplayTask::WriteString(binder_name.to_string()));
                    });
                } else if Some(&name) == abstraction_body.as_ref() {
                    // Body from scope.inner() — binder body resets precedence
                    if let Some(ref body_cat) = body_cat_ident {
                        let task_variant = format_ident!("Display{}", body_cat);
                        forward_ops.push(quote! {
                            stack.push(DisplayTask::#task_variant(&*inner.unsafe_body as *const _, 0));
                        });
                    } else {
                        // Fallback: format to string
                        forward_ops.push(quote! {
                            stack.push(DisplayTask::WriteString(format!("{}", body)));
                        });
                    }
                } else {
                    // Simple parameter - determine its category and push task
                    let field_ident = syn::Ident::new(&name, proc_macro2::Span::call_site());
                    let child_bp = child_bp_map.get(&name).copied().unwrap_or(0u8);
                    if let Some(ty) = param_types.get(&name) {
                        match ty {
                            // An `m:Ident` param is an OPAQUE STRING LEAF: write its text
                            // verbatim through the engine's existing `WriteString` task.
                            // It has no `Display<Cat>` task because there is no `Ident`
                            // category to visit, and it carries NO binding-power argument
                            // because a bare identifier is atomic — no precedence context
                            // can ever require it to be parenthesised.
                            //
                            // ⚠ Deliberately NOT the `StringLiteral` rendering, which
                            // quotes and escapes. A method name must round-trip as the
                            // bare token the lexer produced (`l.nth(0)`, never
                            // `l."nth"(0)`), or `parse ∘ display` stops being stable —
                            // pinned by `ident_param_capture::ident_param_display_round_trips`.
                            TypeExpr::Base(cat_ident)
                                if mettail_ast::grammar::NonTerminalKind::classify(
                                    &cat_ident.to_string(),
                                ) == mettail_ast::grammar::NonTerminalKind::Ident =>
                            {
                                forward_ops.push(quote! {
                                    stack.push(DisplayTask::WriteString(#field_ident.clone()));
                                });
                            },
                            TypeExpr::Base(cat_ident) => {
                                let task_variant = format_ident!("Display{}", cat_ident);
                                let child_bp = if forwards_projection_param.as_deref()
                                    == Some(name.as_str())
                                {
                                    let cat_name = cat_ident.to_string();
                                    if cat_name == category.to_string() {
                                        quote! { min_bp }
                                    } else {
                                        let atomic_bp = bp_lookup.atomic_child_bp(&cat_name);
                                        quote! { if min_bp == 0 { 0 } else { #atomic_bp } }
                                    }
                                } else {
                                    quote! { #child_bp }
                                };
                                // FENCE CAPTURE (2026-07-25) — see the header of
                                // this file and `runtime/src/display_grouping.rs`.
                                //
                                // THE BUG THIS FIXES: `POutput2Plus`'s surface is
                                // `"@" n "!" "(" a "," bs.*sep(",") ")"`. The
                                // 2026-07-24 pass guarded the `bs` ELEMENTS but
                                // not `a`, whose right fence is the LITERAL `","`
                                // one position later. A two-binder `new` in `a`
                                // then rendered `@@Nil!(new a0 , a1 in{Nil},)`,
                                // which does not parse. Pinned by
                                // `languages/tests/rholang_new_official_syntax.rs`.
                                //
                                // Emitted only where the child's inherited
                                // threshold is statically 0 — the guard renders
                                // it via `to_string()` (min_bp 0), so a
                                // precedence-governed slot would be materialized
                                // at the wrong threshold. `child_bp_map` holds a
                                // non-zero entry exactly for the outermost
                                // operands of infix/prefix/postfix rules, which
                                // `syntax_fence_after` already excludes
                                // structurally; the check makes that agreement
                                // explicit rather than assumed.
                                //
                                // A sigil-prefix operand keeps its own
                                // grammar-derived `__at_sigil_operand_needs_wrap`
                                // wrapper; the two COMPOSE rather than compete.
                                // When that predicate fires, the operand's text
                                // is already inside `( … )` so every fence sits
                                // at depth ≥ 1 and the fence guard is a proven
                                // no-op — hence the guard goes in the ELSE arm,
                                // where it catches fences the sigil predicate
                                // (which asks a different question: does the
                                // operand lose its TAIL to the prefix bp cap?)
                                // does not cover. Never double-wraps.
                                let fence_slot_is_bare =
                                    child_bp_map.get(&name).copied().unwrap_or(0u8) == 0
                                        && forwards_projection_param.as_deref()
                                            != Some(name.as_str());
                                let fence_delims = match fence_slot_is_bare {
                                    true => syntax_fence_after(syntax_pattern, i, rule_is_pratt)
                                        .and_then(|f| fence_slice_expr(None, Some(&f))),
                                    false => None,
                                };
                                // The emission for this slot when no `@`-wrap is
                                // in play. `sigil_fallback` is the same guard at
                                // the sigil path's own threshold (`0u8`, NOT
                                // `child_bp` — a sigil operand of a `prefix(n)`
                                // rule carries `n` in `child_bp_map`, and the
                                // 2026-06 `@`-disambiguation deliberately renders
                                // it bare).
                                let fence_guarded = fence_delims.as_ref().map(|delims| {
                                    quote! {
                                        stack.push(DisplayTask::WriteString(
                                            mettail_runtime::group_if_bare_delims(
                                                &#field_ident.to_string(), #delims,
                                            ),
                                        ));
                                    }
                                });
                                let bare_push = fence_guarded.clone().unwrap_or_else(|| {
                                    quote! {
                                        stack.push(DisplayTask::#task_variant(&**#field_ident as *const _, #child_bp));
                                    }
                                });
                                let sigil_fallback = fence_guarded.unwrap_or_else(|| {
                                    quote! {
                                        stack.push(DisplayTask::#task_variant(&**#field_ident as *const _, 0u8));
                                    }
                                });
                                if AT_QUOTE_DISAMBIGUATION && is_sigil_prefix_operand(rule, &name) {
                                    // Cross-category sigil-prefix operand (the `@`-operand of
                                    // NQuoteShort / POutputShort / PPersistOutputShort). The
                                    // operand is rendered BARE (min_bp == 0, so a cast stays bare
                                    // as `{|1:2|}` — the projection-surface arm only renders the
                                    // bare source at min_bp == 0), then conditionally wrapped
                                    // `@(…)` by the GRAMMAR-DERIVED structural predicate when its
                                    // top rule is operand-leading (a top-level infix, a postfix
                                    // method, or a plain-channel send) and would otherwise lose
                                    // its tail to the prefix binding-power cap. This is the
                                    // trampolined (stack-based) analogue of the projection-
                                    // surface wrap: `)` is pushed first so it pops LAST.
                                    forward_ops.push(quote! {
                                        if #field_ident.__at_sigil_operand_needs_wrap() {
                                            stack.push(DisplayTask::WriteString(")".to_string()));
                                            stack.push(DisplayTask::#task_variant(&**#field_ident as *const _, 0u8));
                                            stack.push(DisplayTask::WriteString("(".to_string()));
                                        } else {
                                            #sigil_fallback
                                        }
                                    });
                                } else {
                                    forward_ops.push(bare_push);
                                }
                            },
                            TypeExpr::Collection { .. } => {
                                // Collection param without #sep - format inline
                                forward_ops.push(quote! {
                                    stack.push(DisplayTask::WriteString(format!("{}", #field_ident)));
                                });
                            },
                            _ => {
                                forward_ops.push(quote! {
                                    stack.push(DisplayTask::WriteString(format!("{}", #field_ident)));
                                });
                            },
                        }
                    } else {
                        forward_ops.push(quote! {
                            stack.push(DisplayTask::WriteString(format!("{}", #field_ident)));
                        });
                    }
                }
            },
            SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. } => {
                // L9-3/L9-4: capture positions render via the dedicated
                // `generate_capture_display_arm` (a capture-bearing rule is
                // routed there before this general renderer), so this arm is
                // never reached for them.
            },
            SyntaxExpr::Op(op) => {
                // Stage 3.3 (2026-04-30): pass outer-adjacent Param flags so
                // PatternOp::Opt can apply the same word-literal spacing rules
                // the outer SyntaxExpr::Literal arm uses. Without this, an
                // optional group like `*opt("else" e)` placed after a Param
                // emits `<param><else>` with no separator → re-lex glomming
                // into Ident("<value>else").
                let prev_outer_is_param =
                    i > 0 && matches!(syntax_pattern.get(i - 1), Some(SyntaxExpr::Param(_)));
                let next_outer_is_param =
                    matches!(syntax_pattern.get(i + 1), Some(SyntaxExpr::Param(_)));
                // FENCE CAPTURE: the literal that TERMINATES this op's loop.
                // For a `.*sep(S)` repetition an element must be grouped when it
                // carries `S` (loop continues) OR this terminator (loop ends) at
                // depth 0. `syntax_fence_after` applies the same leading-operand
                // and vacuous-bracket exclusions used for plain params.
                let outer_fence = syntax_fence_after(syntax_pattern, i, rule_is_pratt);
                let op_code = generate_engine_pattern_op(
                    op,
                    &abstraction_binder,
                    &abstraction_body,
                    &body_cat_ident,
                    &param_types,
                    &guard_params,
                    prev_outer_is_param,
                    next_outer_is_param,
                    outer_fence.as_deref(),
                );
                forward_ops.push(op_code);
            },
        }
    }

    // Reverse so stack processes left-to-right
    forward_ops.reverse();

    // Build field pattern
    let mut field_idents: Vec<syn::Ident> = param_names
        .iter()
        .map(|name| syn::Ident::new(name, proc_macro2::Span::call_site()))
        .collect();

    // Determine if we need parenthesization wrapping
    let needs_bp_check = infix_info.is_some() || prefix_info.is_some();
    let own_bp: u8 = if let Some(info) = infix_info {
        info.left_bp
    } else if let Some(pinfo) = prefix_info {
        pinfo.prefix_bp
    } else {
        0
    };
    if has_abstraction {
        field_idents.push(syn::Ident::new("scope", proc_macro2::Span::call_site()));

        if is_multi_binder {
            // Abstraction rules are never infix, no parenthesization needed
            quote! {
                #category::#match_label(#(#field_idents),*) => {
                    let inner = scope.inner();
                    let binder_names: Vec<String> = inner.unsafe_pattern.iter()
                        .map(|b| b.0.pretty_name.as_ref().map(|s| s.to_string()).unwrap_or_else(|| "_".to_string()))
                        .collect();
                    // For multi-binder, binder_name is the joined list (used by some ops)
                    let binder_name = binder_names.join(",");
                    let _ = &binder_name;
                    #(#forward_ops)*
                }
            }
        } else {
            // Abstraction rules are never infix, no parenthesization needed
            quote! {
                #category::#match_label(#(#field_idents),*) => {
                    let inner = scope.inner();
                    let binder_name = inner.unsafe_pattern.0.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
                    let _ = binder_name;
                    #(#forward_ops)*
                }
            }
        }
    } else if field_idents.is_empty() {
        quote! {
            #category::#match_label => {
                #(#forward_ops)*
            }
        }
    } else if needs_bp_check {
        // Phase F.12.B+C (2026-05-20): W3 `neg_zero_prescan` DELETED.
        //
        // W3 used to suppress the leading `-` when `Neg(...Neg(NumLit(0)))`
        // chains terminated in literal zero, so `Display(Neg(NumLit(0)))`
        // rendered as `"0"`. This was a printing-layer "lie" introduced in
        // commit 29d2b0d0 (2026-04-23) as a workaround for the round-trip
        // problem `Display(parse(s)) != s`.
        //
        // The principled resolution (per user direction 2026-05-20):
        // Display is honest about the AST. `Display(Neg(NumLit(0)))` =
        // `"-0"`. The simulation runner's Phase F.12.A multi-source BFS
        // explores all alts of an Ambiguous wrapper and picks the
        // canonically-shortest NF — so the lex-min interpretation's NF
        // (`NumLit(0)` for "- 0" after the `(-a)` fold rule applies)
        // wins on display length and the test
        // `sim_calculator_roundtrip_under_rewrite` returns "0" without
        // needing to suppress the `-`.
        //
        // The `neg_zero_prescan` variable above is still computed for
        // forward compatibility (it may become useful if a future phase
        // wants opt-in canonicalization on cross-cat absorber paths) —
        // but it is NOT consumed here. See the comment at lines 936-1016
        // for the prescan body; it is now effectively dead code that
        // will be removed in a follow-up cleanup once we are confident
        // no future phase needs it.
        let _ = &neg_zero_prescan;
        {
            quote! {
                #category::#match_label(#(#field_idents),*) => {
                    // Precedence-only parenthesization — see the rationale at
                    // `generate_engine_regular_arm` (the projection-shadow
                    // disjunct was removed 2026-06-22 because it injected
                    // precedence-redundant parens that broke one-cycle Display
                    // idempotence).
                    let needs_parens = #own_bp < min_bp;
                    if needs_parens {
                        stack.push(DisplayTask::WriteLiteral(")"));
                    }
                    #(#forward_ops)*
                    if needs_parens {
                        stack.push(DisplayTask::WriteLiteral("("));
                    }
                }
            }
        }
    } else {
        quote! {
            #category::#match_label(#(#field_idents),*) => {
                #(#forward_ops)*
            }
        }
    }
}

/// Generate push operations for a pattern operation (Sep, Var, Opt, etc.)
/// These produce inline write-to-formatter code (since they involve loops/conditionals
/// that don't recurse deeply) and push the result as a WriteString.
///
/// `prev_outer_is_param` / `next_outer_is_param` (Stage 3.3, 2026-04-30):
/// whether the immediately-adjacent OUTER syntax-pattern position is a
/// `SyntaxExpr::Param`. Used by `PatternOp::Opt` to embed leading/trailing
/// spaces in its emitted `result` string when its first/last inner element
/// is a word-literal abutting an outer Param. The space MUST be embedded
/// (not pushed as a separate `WriteLiteral` task) so it's atomically gated
/// on the optional-group's Some/None discriminant — emitting outer-side
/// would produce trailing whitespace when the group is absent.
///
/// `outer_fence` (2026-07-25): the literal that terminates this op in the
/// enclosing template, if any — the second half of a repetition element's fence
/// set. See the FENCE CAPTURE header of this file.
fn generate_engine_pattern_op(
    op: &PatternOp,
    abstraction_binder: &Option<String>,
    _abstraction_body: &Option<String>,
    _body_cat_ident: &Option<syn::Ident>,
    param_types: &HashMap<String, &TypeExpr>,
    guard_params: &HashSet<String>,
    prev_outer_is_param: bool,
    next_outer_is_param: bool,
    outer_fence: Option<&str>,
) -> TokenStream {
    // Sep / Var ignore the outer flags; their emission already produces
    // self-contained spacing or atomic ident formatting.
    let _ = (prev_outer_is_param, next_outer_is_param);
    match op {
        PatternOp::Sep { collection, separator, source } => {
            if let Some(chain_source) = source {
                return generate_engine_chained_sep(chain_source, separator);
            }
            let coll_name = collection.to_string();
            let sep_with_spaces = format!(" {} ", separator);

            if abstraction_binder.as_ref().map(|s| s.as_str()) == Some(&coll_name) {
                // Iterate binder_names
                quote! {
                    {
                        let mut parts = Vec::new();
                        for name in &binder_names {
                            parts.push(name.clone());
                        }
                        stack.push(DisplayTask::WriteString(parts.join(#sep_with_spaces)));
                    }
                }
            } else {
                // B9 / Class 2 (2026-05-08): branch on the collection
                // param's coll_type. Vec yields bare elements; HashBag/
                // HashSet yield (elem, count) tuples (HashBag has count >= 1,
                // HashSet count == 1 by construction). Pre-B9 the
                // unconditional (item, count) iteration assumed HashBag,
                // breaking Class-5 Vec collections AND Class-2 binder-rule
                // Vec collection slots (the smoke test's `qs:Vec(Proc)`).
                // Phase 4 #5b (2026-05-12): also recognize `TypeExpr::Map`
                // (`HashMap(K, V)` form) — `parse_type_atom` lowers
                // `HashMap(K, V)` to `TypeExpr::Map` rather than
                // `TypeExpr::Collection { coll_type: HashMap, ... }`.
                let coll_kind = param_types.get(&coll_name).and_then(|ty| {
                    if let TypeExpr::Collection { coll_type, .. } = ty {
                        Some(coll_type.clone())
                    } else if let TypeExpr::Map { .. } = ty {
                        Some(mettail_ast::types::CollectionType::HashMap)
                    } else {
                        None
                    }
                });
                let coll_ident = syn::Ident::new(&coll_name, proc_macro2::Span::call_site());
                // Roundtrip fix — FENCE CAPTURE (separator half 2026-07-24,
                // loop-terminator half 2026-07-25). The joined text only
                // re-parses if no ELEMENT carries, at bracket depth 0, either
                // `separator` (the parser would CONTINUE the list inside the
                // element) or the literal that terminates the list (it would END
                // the list inside the element). `group_if_bare_delims` wraps such
                // an element in PraTTaIL's transparent `( … )` grouping
                // (term-preserving: `(P)` parses to `P`, no wrapper node).
                //
                // Reachable since the official-Rholang `new` alignment made
                // `new x, y in { P }` the first `Proc` whose surface carries a
                // depth-0 comma: `@Nil!(0 , new a , b in{Nil})` re-parsed as FOUR
                // operands. It is a no-op for every element without a depth-0
                // fence — i.e. for every pre-2026-07-24 display — so it can
                // only repair a broken roundtrip, never break a working one.
                // See `runtime/src/display_grouping.rs`.
                let elem_delims = fence_slice_expr(Some(separator), outer_fence)
                    .unwrap_or_else(|| quote! { &[] });
                let iter_body = match coll_kind {
                    Some(mettail_ast::types::CollectionType::Vec) => quote! {
                        for item in #coll_ident.iter() {
                            parts.push(mettail_runtime::group_if_bare_delims(&item.to_string(), #elem_delims));
                        }
                        // Vec preserves insertion order — no sort.
                    },
                    Some(mettail_ast::types::CollectionType::HashSet) => quote! {
                        for item in #coll_ident.iter() {
                            parts.push(mettail_runtime::group_if_bare_delims(&item.to_string(), #elem_delims));
                        }
                        parts.sort();
                    },
                    Some(mettail_ast::types::CollectionType::HashMap) => quote! {
                        // HashMap: pair-wise iteration with `:` between
                        // K and V — matches the parse-side `:` consumption
                        // in walker phase 1 (`emit_collection_loop_arm`).
                        for (k, v) in #coll_ident.iter() {
                            parts.push(format!(
                                "{} : {}",
                                mettail_runtime::group_if_bare_delims(&k.to_string(), #elem_delims),
                                mettail_runtime::group_if_bare_delims(&v.to_string(), #elem_delims),
                            ));
                        }
                        parts.sort();
                    },
                    // #74: an `Unset` PathMap entry renders as the bare key.
                    // (Unreachable for an INLINE binder collection — `PathMap`
                    // is not an admissible inline collection type.)
                    Some(mettail_ast::types::CollectionType::PathMap) => quote! {
                        for (k, v) in #coll_ident.iter() {
                            let k_s = mettail_runtime::group_if_bare_delims(
                                &k.to_string(), #elem_delims,
                            );
                            parts.push(match v {
                                mettail_runtime::PathValue::Unset => k_s,
                                mettail_runtime::PathValue::Set(inner) => format!(
                                    "{} : {}",
                                    k_s,
                                    mettail_runtime::group_if_bare_delims(
                                        &inner.to_string(), #elem_delims,
                                    ),
                                ),
                            });
                        }
                        parts.sort();
                    },
                    // Default (HashBag or unknown): preserve pre-B9 behavior.
                    Some(mettail_ast::types::CollectionType::HashBag) | None => quote! {
                        for (item, count) in #coll_ident.iter() {
                            for _ in 0..count {
                                parts.push(mettail_runtime::group_if_bare_delims(&item.to_string(), #elem_delims));
                            }
                        }
                        parts.sort();
                    },
                };
                quote! {
                    {
                        let mut parts = Vec::new();
                        #iter_body
                        stack.push(DisplayTask::WriteString(parts.join(#sep_with_spaces)));
                    }
                }
            }
        },
        PatternOp::Var(id) => {
            let ident = syn::Ident::new(&id.to_string(), proc_macro2::Span::call_site());
            quote! {
                stack.push(DisplayTask::WriteString(format!("{}", #ident)));
            }
        },
        PatternOp::Opt { inner } => {
            // Opt-Group: emit the inner segment GATED on the first
            // Param's `is_some()`. By WPDS Opt-Group invariant, all
            // inner Param fields share the same Some/None fate (the
            // walker's optional-scope finalize/skip is atomic). Gating
            // on the first Param's discriminant suffices.
            //
            // Inside the gated block, each inner Param's variant field
            // is `Option<Box<Cat>>`; rebind to `&Cat` via
            // `unwrap_or_unchecked`-style on `as_ref().unwrap()` (safe
            // because the gating ensures Some).
            // Phase 4 #3 (2026-05-12): gating_ident now also considers
            // Op(Sep) — its `collection` param is the gating signal
            // (Option<Vec<T>> / Option<HashBag<T>> / etc.). The first
            // inner Param OR Sep-collection-param wins.
            let gating_ident: Option<syn::Ident> = inner.iter().find_map(|expr| match expr {
                SyntaxExpr::Param(id) => {
                    Some(syn::Ident::new(&id.to_string(), proc_macro2::Span::call_site()))
                },
                SyntaxExpr::Op(PatternOp::Sep { collection, source: None, .. }) => {
                    Some(syn::Ident::new(&collection.to_string(), proc_macro2::Span::call_site()))
                },
                _ => None,
            });
            let inner_bindings: Vec<TokenStream> = inner
                .iter()
                .filter_map(|expr| {
                    match expr {
                        SyntaxExpr::Param(id) => {
                            let id_ident =
                                syn::Ident::new(&id.to_string(), proc_macro2::Span::call_site());
                            let inner_var = quote::format_ident!("__opt_{}", id);
                            // Task #14 (Option<Guard>): a guard slot's field
                            // is `Option<BehavioralPred>` — no Arc layer to
                            // strip, so the `.map(|__b| __b.as_ref())` of the
                            // term arm is E0599 (`BehavioralPred: !AsRef`).
                            // Bind `&BehavioralPred` directly; rendering goes
                            // through BehavioralPred's Display (`Top` renders
                            // `true()`, display-stable under re-parse).
                            if guard_params.contains(&id.to_string()) {
                                Some(quote! {
                                    let #inner_var: &_ = #id_ident.as_ref()
                                        .expect("Opt-Group: inner display ran with None");
                                })
                            } else {
                                Some(quote! {
                                    let #inner_var: &_ = #id_ident.as_ref()
                                        .map(|__b| __b.as_ref())
                                        .expect("Opt-Group: inner display ran with None");
                                })
                            }
                        },
                        // Phase 4 #3 (2026-05-12): bind the Sep collection param
                        // to a reference of the inner Vec/HashBag/etc. The field
                        // type is `Option<Container<T>>` (no Box), so as_ref()
                        // gives &Container<T> directly.
                        SyntaxExpr::Op(PatternOp::Sep { collection, source: None, .. }) => {
                            let id_ident = syn::Ident::new(
                                &collection.to_string(),
                                proc_macro2::Span::call_site(),
                            );
                            let inner_var = quote::format_ident!("__opt_{}", collection);
                            Some(quote! {
                                let #inner_var = #id_ident.as_ref()
                                    .expect("Opt-Group: inner display ran with None");
                            })
                        },
                        _ => None,
                    }
                })
                .collect();
            // Stage 3.3 (2026-04-30): mirror the outer SyntaxExpr::Literal
            // spacing heuristic for inner positions, plus inject leading /
            // trailing spaces at inner edges when the OUTER neighbour is a
            // Param. This guarantees the Display→Parse roundtrip for any
            // optional-group position whose word-literals would otherwise
            // glom together with adjacent Param-formatted text under the
            // lexer's maximal-munch keyword recognition.
            //
            // Rules (per inner index `j`):
            //  * `is_word`: same lexer-aligned predicate as the outer arm —
            //    non-empty, ident-class chars only, non-numeric leading.
            //  * `inner_3case_force`: when the inner position is between two
            //    Params, force `(" ", " ")` — matches outer behaviour for
            //    `["a", "+", "b"]` shapes.
            //  * Leading-space sources: (a) inner-prev is a Param + is_word;
            //    (b) is_first AND outer-prev is a Param + is_word;
            //    (c) inner_3case_force.
            //  * Trailing-space sources: (a) is_word AND any inner-next exists
            //    (covers Lit→Lit-word AND Lit→Param);
            //    (b) is_last AND outer-next is a Param + is_word;
            //    (c) inner_3case_force.
            //  * Param at inner-edge with outer-adjacent Param: emit an
            //    explicit `result.push_str(" ");` because Param widths are
            //    unbounded and adjacency would re-lex into a single token.
            //  * Nested Op inside Opt: emit `compile_error!` — the parser side
            //    rejects this construction at `binder.rs:347`, so the Display
            //    side must as well, surfaced at language! macro expansion.
            let inner_parts: Vec<TokenStream> = inner
                .iter()
                .enumerate()
                .map(|(j, expr)| {
                    let inner_prev_is_param =
                        j > 0 && matches!(inner.get(j - 1), Some(SyntaxExpr::Param(_)));
                    let inner_next_is_param =
                        inner.get(j + 1).map(|e| matches!(e, SyntaxExpr::Param(_)));
                    let is_first = j == 0;
                    let is_last = j + 1 == inner.len();
                    // FENCE CAPTURE inside an optional group: the terminator is
                    // the next INNER literal, or — at the group's last position
                    // — the literal that follows the group in the outer
                    // template. Only interior inner positions qualify (a literal
                    // must precede them inside the group), which is the same
                    // leading-operand exclusion `syntax_fence_after` applies.
                    let inner_fence: Option<String> = match inner[..j]
                        .iter()
                        .any(|e| matches!(e, SyntaxExpr::Literal(_)))
                    {
                        false => None,
                        true => match inner.get(j + 1) {
                            Some(SyntaxExpr::Literal(lit)) if !fence_is_vacuous(lit) => {
                                Some(lit.clone())
                            },
                            None => outer_fence.map(|f| f.to_string()),
                            _ => None,
                        },
                    };
                    match expr {
                        SyntaxExpr::Literal(s) => {
                            let is_word = !s.is_empty()
                                && s.chars().all(|c| c.is_alphanumeric() || c == '_')
                                && !s.chars().next().unwrap().is_numeric();
                            let inner_3case_force =
                                inner_prev_is_param && inner_next_is_param.unwrap_or(false);
                            let need_prefix = (inner_prev_is_param && is_word)
                                || (is_first && prev_outer_is_param && is_word)
                                || inner_3case_force;
                            let need_suffix = (is_word && !is_last)
                                || (is_last && next_outer_is_param && is_word)
                                || inner_3case_force;
                            let prefix = if need_prefix { " " } else { "" };
                            let suffix = if need_suffix { " " } else { "" };
                            let raw = format!("{}{}{}", prefix, s, suffix);
                            quote! { result.push_str(#raw); }
                        },
                        SyntaxExpr::Param(id) => {
                            let inner_var = quote::format_ident!("__opt_{}", id);
                            let leading = if is_first && prev_outer_is_param {
                                quote! { result.push_str(" "); }
                            } else {
                                quote! {}
                            };
                            let trailing = if is_last && next_outer_is_param {
                                quote! { result.push_str(" "); }
                            } else {
                                quote! {}
                            };
                            let body = match inner_fence
                                .as_deref()
                                .and_then(|f| fence_slice_expr(None, Some(f)))
                            {
                                Some(delims) => quote! {
                                    result.push_str(&mettail_runtime::group_if_bare_delims(
                                        &format!("{}", #inner_var), #delims,
                                    ));
                                },
                                None => quote! {
                                    result.push_str(&format!("{}", #inner_var));
                                },
                            };
                            quote! {
                                #leading
                                #body
                                #trailing
                            }
                        },
                        // L9-3: STAGE 3 renders a captured token's text inside an
                        // optional group. INERT in STAGE 1 (unconstructable).
                        SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. } => quote! {},
                        SyntaxExpr::Op(PatternOp::Sep { collection, separator, source: None }) => {
                            // Phase 4 #3 (2026-05-12): Sep inside *opt.
                            // Iterate `__opt_<coll_name>` joining elements
                            // with the separator. The container's coll_kind
                            // determines iteration shape: Vec yields bare
                            // elements; HashBag yields (item, count);
                            // HashSet yields bare elements (and sorts);
                            // HashMap yields (k, v) pair-wise.
                            let inner_var = quote::format_ident!("__opt_{}", collection);
                            let coll_name = collection.to_string();
                            let sep_with_spaces = format!(" {} ", separator);
                            // Phase 4 #5b (2026-05-12): also recognize
                            // `TypeExpr::Map` (HashMap(K, V) form).
                            let coll_kind = param_types.get(&coll_name).and_then(|ty| {
                                if let TypeExpr::Collection { coll_type, .. } = ty {
                                    Some(coll_type.clone())
                                } else if let TypeExpr::Map { .. } = ty {
                                    Some(mettail_ast::types::CollectionType::HashMap)
                                } else {
                                    None
                                }
                            });
                            // FENCE CAPTURE — same fence set as a top-level
                            // repetition: the separator plus the loop's
                            // terminating literal (inner, or the outer one when
                            // the list closes the optional group).
                            let elem_delims =
                                fence_slice_expr(Some(separator), inner_fence.as_deref())
                                    .unwrap_or_else(|| quote! { &[] });
                            let iter_body = match coll_kind {
                                Some(mettail_ast::types::CollectionType::Vec) => quote! {
                                    for item in #inner_var.iter() {
                                        parts.push(mettail_runtime::group_if_bare_delims(&item.to_string(), #elem_delims));
                                    }
                                },
                                Some(mettail_ast::types::CollectionType::HashSet) => quote! {
                                    for item in #inner_var.iter() {
                                        parts.push(mettail_runtime::group_if_bare_delims(&item.to_string(), #elem_delims));
                                    }
                                    parts.sort();
                                },
                                Some(mettail_ast::types::CollectionType::HashMap) => quote! {
                                    for (k, v) in #inner_var.iter() {
                                        parts.push(format!("{} : {}", k, v));
                                    }
                                    parts.sort();
                                },
                                // #74: an `Unset` PathMap entry renders as the
                                // bare key. (Unreachable for an INLINE binder
                                // collection — see the sibling arms.)
                                Some(mettail_ast::types::CollectionType::PathMap) => quote! {
                                    for (k, v) in #inner_var.iter() {
                                        parts.push(match v {
                                            mettail_runtime::PathValue::Unset => {
                                                format!("{}", k)
                                            },
                                            mettail_runtime::PathValue::Set(inner) => {
                                                format!("{} : {}", k, inner)
                                            },
                                        });
                                    }
                                    parts.sort();
                                },
                                Some(mettail_ast::types::CollectionType::HashBag) | None => {
                                    quote! {
                                        for (item, count) in #inner_var.iter() {
                                            for _ in 0..count {
                                                parts.push(mettail_runtime::group_if_bare_delims(&item.to_string(), #elem_delims));
                                            }
                                        }
                                        parts.sort();
                                    }
                                },
                            };
                            quote! {
                                {
                                    let mut parts: Vec<String> = Vec::new();
                                    #iter_body
                                    result.push_str(&parts.join(#sep_with_spaces));
                                }
                            }
                        },
                        SyntaxExpr::Op(_inner_op) => {
                            // Other nested PatternOps (Zip, Map, Var, Opt) inside
                            // *opt are out of pilot scope. The WPDS binder
                            // classifier returns None for these.
                            quote! {
                                compile_error!(
                                    "nested non-Sep PatternOp inside #opt(...) is \
                                     not supported. Rewrite the grammar to \
                                     flatten the inner ops, or open an issue if \
                                     your grammar genuinely needs nested \
                                     optionality with Zip/Map/Var/Opt."
                                );
                            }
                        },
                    }
                })
                .collect();
            if let Some(gating) = gating_ident {
                quote! {
                    {
                        if #gating.is_some() {
                            let mut result = String::new();
                            #(#inner_bindings)*
                            #(#inner_parts)*
                            stack.push(DisplayTask::WriteString(result));
                        }
                    }
                }
            } else {
                // No Param inside the optional — emit unconditional
                // (literal-only optional groups are unusual but valid).
                quote! {
                    {
                        let mut result = String::new();
                        #(#inner_parts)*
                        stack.push(DisplayTask::WriteString(result));
                    }
                }
            }
        },
        PatternOp::Zip { .. } | PatternOp::Map { .. } => {
            quote! { /* zip/map should be chained with #sep */ }
        },
    }
}

/// Generate engine code for chained #zip().#map().#sep() pattern
fn generate_engine_chained_sep(source: &PatternOp, separator: &str) -> TokenStream {
    if let PatternOp::Map { source: map_source, params, body } = source {
        if let PatternOp::Zip { left, .. } = map_source.as_ref() {
            let left_name = left.to_string();
            let left_ident = syn::Ident::new(&left_name, proc_macro2::Span::call_site());

            let format_code = generate_engine_map_body_format(params, body);
            let sep_str = format!("{} ", separator);

            return quote! {
                {
                    let mut parts = Vec::new();
                    for (i, item) in #left_ident.iter().enumerate() {
                        let binder_name = binder_names.get(i).map(|s| s.as_str()).unwrap_or("_");
                        let mut part = String::new();
                        #format_code
                        parts.push(part);
                    }
                    parts.sort();
                    stack.push(DisplayTask::WriteString(parts.join(#sep_str)));
                }
            };
        }
    }
    quote! { /* unhandled chained pattern */ }
}

/// Generate format code from map body for the engine (builds into `part` String)
fn generate_engine_map_body_format(params: &[syn::Ident], body: &[SyntaxExpr]) -> TokenStream {
    let mut format_parts: Vec<TokenStream> = Vec::new();

    for expr in body {
        match expr {
            SyntaxExpr::Literal(s) => {
                format_parts.push(quote! { part.push_str(#s); });
            },
            SyntaxExpr::Param(id) => {
                let id_str = id.to_string();
                if params.len() >= 2 {
                    let first_param = params[0].to_string();
                    let second_param = params[1].to_string();

                    if id_str == first_param {
                        format_parts.push(quote! { part.push_str(&format!("{}", item)); });
                    } else if id_str == second_param {
                        format_parts.push(quote! { part.push_str(binder_name); });
                    } else {
                        let ident = syn::Ident::new(&id_str, proc_macro2::Span::call_site());
                        format_parts.push(quote! { part.push_str(&format!("{}", #ident)); });
                    }
                } else if params.len() == 1 && id.to_string() == params[0].to_string() {
                    format_parts.push(quote! { part.push_str(&format!("{}", item)); });
                } else {
                    let ident = syn::Ident::new(&id_str, proc_macro2::Span::call_site());
                    format_parts.push(quote! { part.push_str(&format!("{}", #ident)); });
                }
            },
            SyntaxExpr::Op(_) => {},
            // L9-3: STAGE 3 implements the token-text render; INERT here
            // (unconstructable from source, so this map body never sees one).
            SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. } => {},
        }
    }

    quote! { #(#format_parts)* }
}

// =============================================================================
// Auto-generated Variant Arms
// =============================================================================

/// Generate engine arm for auto-generated Var variant.
fn generate_engine_auto_var_arm(category: &syn::Ident) -> TokenStream {
    let var_label = generate_var_label(category);

    quote! {
        #category::#var_label(var) => {
            let name = match &var.0 {
                mettail_runtime::Var::Free(fv) => {
                    fv.pretty_name.as_ref().map(|s| s.to_string()).unwrap_or_else(|| "_".to_string())
                }
                mettail_runtime::Var::Bound(bv) => {
                    bv.pretty_name.as_ref().map(|s| s.to_string()).unwrap_or_else(|| "_".to_string())
                }
            };
            stack.push(DisplayTask::WriteString(name));
        }
    }
}

/// Extract the VALUE type Ident from a two-arg collection native type
/// (e.g. `HashMap<K, V>` → `Some(V)`, `HashMapLit<K, V>` → `Some(V)`).
/// Returns None for one-arg collections (Vec, HashBag, HashSet).
fn extract_map_value_ident(native_type: &syn::Type) -> Option<syn::Ident> {
    use syn::GenericArgument;
    let path = match native_type {
        syn::Type::Path(t) => &t.path,
        _ => return None,
    };
    let segment = path.segments.last()?;
    let args = match &segment.arguments {
        syn::PathArguments::AngleBracketed(a) => &a.args,
        _ => return None,
    };
    // Need at least 2 args for a key-value map.
    if args.len() < 2 {
        return None;
    }
    let second = args.iter().nth(1)?;
    match second {
        GenericArgument::Type(syn::Type::Path(t)) => t
            .path
            .get_ident()
            .cloned()
            .or_else(|| t.path.segments.last().map(|s| s.ident.clone())),
        _ => None,
    }
}

/// Generate engine arm for auto-generated literal variant (NumLit, FloatLit, etc.)
///
/// `mandatory_literal_tail` (divergence I / Stage C) is the literal suffix the
/// category's declared `literals { }` pattern forces onto every word it accepts,
/// if any — see [`mandatory_literal_tail_of_pattern`]. Its `composite_separator`
/// carries the declared COMPOSITE form's separator when the pattern has one.
fn generate_engine_auto_literal_arm(
    category: &syn::Ident,
    native_type: &syn::Type,
    collection_kind: Option<&mettail_ast::language::CollectionCategory>,
    mandatory_literal_tail: Option<MandatoryTail>,
) -> TokenStream {
    let literal_label = generate_literal_label(native_type);
    let nt = crate::gen::native::NativeType::from_syn_type(native_type);

    if nt.is_string() {
        quote! {
            #category::#literal_label(v) => {
                stack.push(DisplayTask::WriteString(
                    format!("\"{}\"", v.replace('\"', "\\\""))
                ));
            }
        }
    } else if collection_kind.is_some() || nt.is_collection() {
        // Collection payloads. Wrap with the keyword prefix from
        // `CollectionDelimiters` (default: `list(`, `bag(`, `map(`) so
        // Display → parse roundtrip holds. Without this wrapping the
        // generated parser's auto-synthesized `ListLit`/`BagLit`/`MapLit`
        // rules would reject the Display output.
        //
        // Gate fix (2026-06-30): enter the collection block whenever the
        // language DECLARED this category as a collection (`collection_kind`),
        // not only when the native wrapper's NAME is in `NativeType`'s
        // hardcoded allowlist (Vec/HashBag/HashSet/HashMap[Lit]). Native
        // wrappers like `PathMapLit`/`HashSetLit` map to `NativeType::Other`
        // (`is_collection()==false`) and previously fell through to the scalar
        // `format!("{}", v)` arm, which delegates to the wrapper's own Display
        // (e.g. `PathMapLit` → `HashMapLit` → hardcoded `{}`) and ignores the
        // declared `{| |}` / `Set(` `)` delimiters, breaking Display→parse.
        let (open, close, sep, kv_sep): (String, String, String, Option<String>) =
            match collection_kind {
                Some(mettail_ast::language::CollectionCategory::List(d))
                | Some(mettail_ast::language::CollectionCategory::Bag(d))
                | Some(mettail_ast::language::CollectionCategory::Map(d))
                | Some(mettail_ast::language::CollectionCategory::Set(d))
                | Some(mettail_ast::language::CollectionCategory::Pathmap(d)) => {
                    (d.open.clone(), d.close.clone(), d.sep.clone(), d.key_val_sep.clone())
                },
                None => ("".to_string(), "".to_string(), ", ".to_string(), None),
            };
        // Extract the element category (e.g. Vec<Proc> → Proc). Every
        // element gets pushed as a DisplayTask::Display<ElemCat> onto the
        // OUTER display stack — we STAY inside the single iterative Display
        // context instead of calling `write!(s, "{}", item)` which re-enters
        // `display_iterative` (CPU-stack-deep on nested collections). Stack-
        // safety invariant.
        let elem_ident = crate::gen::native::native_type_element_ident(native_type);
        // HashMap<K,V> / HashMapLit<K,V> take TWO generic args; extract V
        // separately. For K we still use the first generic arg (same as
        // element extraction), since HashMap's "element" concept is
        // key+value pair.
        let value_ident = extract_map_value_ident(native_type);
        let elem_display_task = elem_ident.as_ref().map(|c| format_ident!("Display{}", c));
        let value_display_task = value_ident.as_ref().map(|c| format_ident!("Display{}", c));

        // Re-key the per-shape emitter on the DECLARED collection category
        // (general) rather than the `NativeType` name allowlist. Each declared
        // category maps to the existing emitter body whose iteration shape it
        // shares — so List/Bag/Map produce BYTE-IDENTICAL output to before, Set
        // routes through the sorted-seq (HashSet) body, and Map/Pathmap through
        // the key-value (HashMap) body. The delimiters/sep/kv_sep already come
        // from the declared `d` above, so Pathmap emits its `{| |}` correctly.
        // When no category was declared (a bare `![Vec<_>]` with no `as List`),
        // fall back to the `NativeType` heuristic (`nt`) for back-compat.
        let effective_nt = match collection_kind {
            Some(mettail_ast::language::CollectionCategory::List(_)) => {
                crate::gen::native::NativeType::VecCollection
            },
            Some(mettail_ast::language::CollectionCategory::Bag(_)) => {
                crate::gen::native::NativeType::HashBagCollection
            },
            Some(mettail_ast::language::CollectionCategory::Map(_))
            | Some(mettail_ast::language::CollectionCategory::Pathmap(_)) => {
                crate::gen::native::NativeType::HashMapLitCollection
            },
            Some(mettail_ast::language::CollectionCategory::Set(_)) => {
                crate::gen::native::NativeType::HashSetCollection
            },
            None => nt,
        };

        // ★ #74 (2026-07-29): a `Pathmap`'s entries are `(K, PathValue<V>)`, and
        // a `PathValue::Unset` entry prints as the BARE KEY — `{| k |}`, with no
        // `:` and no value. This arm is emitted BEFORE the shared kv body,
        // because it is the one place where the presence of the separator is a
        // RUNTIME question rather than a static property of the container.
        //
        // ★ This is the self-check for Ruling B. `{| k |}` must be a fixpoint of
        // `parse ∘ display`: encoding the unset value as `Nil` would print
        // `{|k:Nil|}` for an input the user wrote as `{|k|}`, so the surface
        // would not round-trip. That is why "unset ≠ Nil" is a soundness
        // property here and not a preference.
        if matches!(
            collection_kind,
            Some(mettail_ast::language::CollectionCategory::Pathmap(_))
        ) {
            let kv = kv_sep.clone().unwrap_or_else(|| ":".to_string());
            let sep_with_space = format!("{} ", sep);
            if let (Some(key_task), Some(val_task)) =
                (elem_display_task.clone(), value_display_task.clone())
            {
                return quote! {
                    #category::#literal_label(v) => {
                        // ⚠ NEVER SORTED (2026-07-29, Ruling E). A pathmap is a
                        // PATH-KEYED container whose order is the source's
                        // insertion order; `PathMapLit` preserves it, and Display
                        // must not reorder what the author wrote.
                        //
                        // This arm used to run
                        // `entries.sort_by(|a, b| format!("{}", a.0).cmp(…))` —
                        // a sort by the FORMATTED KEY, which is
                        // (a) lexicographic on rendered text, so `[10]` sorted
                        // before `[9]`, and (b) O(n·|render|) allocation per
                        // comparison. It also put `Display` and the container's
                        // own `iter()` into permanent disagreement about order,
                        // which is why the #151/#74 test rows had to read the
                        // PAYLOAD rather than the rendering.
                        //
                        // The sibling asymmetry that shows it was a defect and
                        // not a policy: `lower_map` (the map→`EMap` lowering)
                        // does NOT sort, and neither does the `Map` Display path
                        // for insertion-ordered content. Only pathmaps were
                        // sorted, in two places, for no reason their siblings
                        // shared.
                        let entries: Vec<_> = v.iter().collect();
                        stack.push(DisplayTask::WriteString(#close.to_string()));
                        for (i, (k, val)) in entries.iter().enumerate().rev() {
                            // Tasks are pushed in REVERSE display order, so the
                            // value and its separator go on first.
                            if let mettail_runtime::PathValue::Set(__inner) = *val {
                                stack.push(DisplayTask::#val_task(__inner as *const _, 0u8));
                                stack.push(DisplayTask::WriteLiteral(#kv));
                            }
                            stack.push(DisplayTask::#key_task(*k as *const _, 0u8));
                            if i > 0 {
                                stack.push(DisplayTask::WriteString(#sep_with_space.to_string()));
                            }
                        }
                        stack.push(DisplayTask::WriteString(#open.to_string()));
                    }
                };
            }
            // Fallback for an unknown element category (no DisplayTask to push):
            // format inline. Same unset discipline.
            return quote! {
                #category::#literal_label(v) => {
                    use std::fmt::Write as _;
                    let mut s = String::from(#open);
                    // ⚠ NEVER SORTED — see the sibling arm above.
                    let entries: Vec<_> = v.iter().collect();
                    for (i, (k, val)) in entries.iter().enumerate() {
                        if i > 0 { s.push_str(#sep); s.push(' '); }
                        match val {
                            mettail_runtime::PathValue::Unset => {
                                let _ = write!(s, "{}", k);
                            },
                            mettail_runtime::PathValue::Set(__inner) => {
                                let _ = write!(s, "{}{}{}", k, #kv, __inner);
                            },
                        }
                    }
                    s.push_str(#close);
                    stack.push(DisplayTask::WriteString(s));
                }
            };
        }

        match effective_nt {
            crate::gen::native::NativeType::VecCollection => {
                let Some(elem_task) = elem_display_task.clone() else {
                    // Fallback for unknown element category — keep old
                    // behavior (stack-unsafe, but at least compiles).
                    return quote! {
                        #category::#literal_label(v) => {
                            use std::fmt::Write as _;
                            let mut s = String::from(#open);
                            for (i, item) in v.iter().enumerate() {
                                if i > 0 { s.push_str(#sep); s.push(' '); }
                                let _ = write!(s, "{}", item);
                            }
                            s.push_str(#close);
                            stack.push(DisplayTask::WriteString(s));
                        }
                    };
                };
                let sep_with_space = format!("{} ", sep);
                quote! {
                    #category::#literal_label(v) => {
                        // Push in reverse order so the first element is
                        // popped (and displayed) first: open, elem0, sep,
                        // elem1, sep, ..., elemN, close.
                        stack.push(DisplayTask::WriteString(#close.to_string()));
                        for (i, item) in v.iter().enumerate().rev() {
                            stack.push(DisplayTask::#elem_task(item as *const _, 0u8));
                            if i > 0 {
                                stack.push(DisplayTask::WriteString(#sep_with_space.to_string()));
                            }
                        }
                        stack.push(DisplayTask::WriteString(#open.to_string()));
                    }
                }
            },
            crate::gen::native::NativeType::HashMapCollection
            | crate::gen::native::NativeType::HashMapLitCollection => {
                let kv = kv_sep.unwrap_or_else(|| ":".to_string());
                let (Some(key_task), Some(val_task)) =
                    (elem_display_task.clone(), value_display_task.clone())
                else {
                    return quote! {
                        #category::#literal_label(v) => {
                            use std::fmt::Write as _;
                            let mut s = String::from(#open);
                            let mut entries: Vec<_> = v.iter().collect();
                            entries.sort_by(|a, b| format!("{}", a.0).cmp(&format!("{}", b.0)));
                            for (i, (k, val)) in entries.iter().enumerate() {
                                if i > 0 { s.push_str(#sep); s.push(' '); }
                                let _ = write!(s, "{}{}{}", k, #kv, val);
                            }
                            s.push_str(#close);
                            stack.push(DisplayTask::WriteString(s));
                        }
                    };
                };
                let sep_with_space = format!("{} ", sep);
                // Box the keys/vals so sorting doesn't move addresses we
                // reference via pointers. Sort by formatted key (stable
                // display order), then push Display tasks in reverse.
                quote! {
                    #category::#literal_label(v) => {
                        let mut entries: Vec<_> = v.iter().collect();
                        entries.sort_by(|a, b| format!("{}", a.0).cmp(&format!("{}", b.0)));
                        // The entries Vec holds REFERENCES into v's storage,
                        // so addresses inside v are stable across sort.
                        stack.push(DisplayTask::WriteString(#close.to_string()));
                        for (i, (k, val)) in entries.iter().enumerate().rev() {
                            stack.push(DisplayTask::#val_task(*val as *const _, 0u8));
                            stack.push(DisplayTask::WriteLiteral(#kv));
                            stack.push(DisplayTask::#key_task(*k as *const _, 0u8));
                            if i > 0 {
                                stack.push(DisplayTask::WriteString(#sep_with_space.to_string()));
                            }
                        }
                        stack.push(DisplayTask::WriteString(#open.to_string()));
                    }
                }
            },
            crate::gen::native::NativeType::HashBagCollection => {
                let Some(elem_task) = elem_display_task.clone() else {
                    return quote! {
                        #category::#literal_label(v) => {
                            use std::fmt::Write as _;
                            let mut s = String::from(#open);
                            let mut entries: Vec<_> = v.iter().collect();
                            entries.sort_by(|a, b| format!("{}", a.0).cmp(&format!("{}", b.0)));
                            let mut first = true;
                            for (item, count) in entries {
                                for _ in 0..count {
                                    if !first { s.push_str(#sep); s.push(' '); }
                                    first = false;
                                    let _ = write!(s, "{}", item);
                                }
                            }
                            s.push_str(#close);
                            stack.push(DisplayTask::WriteString(s));
                        }
                    };
                };
                let sep_with_space = format!("{} ", sep);
                quote! {
                    #category::#literal_label(v) => {
                        let mut entries: Vec<_> = v.iter().collect();
                        entries.sort_by(|a, b| format!("{}", a.0).cmp(&format!("{}", b.0)));
                        // Materialize (item_ptr, count) tuples, then flatten
                        // to a Vec of item_ptrs for uniform display. The
                        // `entries` Vec holds refs into v's storage; we
                        // convert to raw pointers before flattening.
                        let mut flat: Vec<*const _> = Vec::new();
                        for (item, count) in entries {
                            for _ in 0..count {
                                flat.push(item as *const _);
                            }
                        }
                        stack.push(DisplayTask::WriteString(#close.to_string()));
                        for (i, ptr) in flat.iter().enumerate().rev() {
                            stack.push(DisplayTask::#elem_task(*ptr, 0u8));
                            if i > 0 {
                                stack.push(DisplayTask::WriteString(#sep_with_space.to_string()));
                            }
                        }
                        stack.push(DisplayTask::WriteString(#open.to_string()));
                    }
                }
            },
            crate::gen::native::NativeType::HashSetCollection => {
                let Some(elem_task) = elem_display_task.clone() else {
                    return quote! {
                        #category::#literal_label(v) => {
                            use std::fmt::Write as _;
                            let mut s = String::from(#open);
                            let mut entries: Vec<_> = v.iter().collect();
                            entries.sort_by(|a, b| format!("{}", a).cmp(&format!("{}", b)));
                            for (i, item) in entries.iter().enumerate() {
                                if i > 0 { s.push_str(#sep); s.push(' '); }
                                let _ = write!(s, "{}", item);
                            }
                            s.push_str(#close);
                            stack.push(DisplayTask::WriteString(s));
                        }
                    };
                };
                let sep_with_space = format!("{} ", sep);
                quote! {
                    #category::#literal_label(v) => {
                        let mut entries: Vec<_> = v.iter().collect();
                        entries.sort_by(|a, b| format!("{}", a).cmp(&format!("{}", b)));
                        stack.push(DisplayTask::WriteString(#close.to_string()));
                        for (i, item) in entries.iter().enumerate().rev() {
                            stack.push(DisplayTask::#elem_task(*item as *const _, 0u8));
                            if i > 0 {
                                stack.push(DisplayTask::WriteString(#sep_with_space.to_string()));
                            }
                        }
                        stack.push(DisplayTask::WriteString(#open.to_string()));
                    }
                }
            },
            _ => quote! {
                // Fallback for any other collection native type — use Display impl.
                #category::#literal_label(v) => {
                    stack.push(DisplayTask::WriteString(format!("{}", v)));
                }
            },
        }
    } else if let Some(MandatoryTail { tail, composite_separator }) = mandatory_literal_tail {
        // ── Divergence I / Stage C (2026-07-25): MANDATORY LITERAL TAIL ──────────
        //
        // A `literals { }` pattern whose language forces every accepted word to end
        // with a fixed literal — Rholang/Calculator's `BigInt` (`…n`) is the case in
        // point — must have that tail in its Display, or Display emits a word its own
        // category cannot read back.
        //
        // It used to be harmless: while `BigInt`'s eval was a universal acceptor,
        // the tail-less `3` was re-read as a `BigInt` anyway. Closing that acceptor
        // (so a numeral's carrier is a function of its text — divergence I) makes
        // `3` an `Int`, and the omission becomes a real display→parse fixpoint break:
        // `Display(BigInt::NumLit(3)) = "3"`, `Parse("3") = Int`. `parse_structured`
        // feels it first — it prefers the raw derivation whose Display equals the
        // input, so without the tail NO derivation of `3n` is surface-exact.
        //
        // The tail is DERIVED from the declared pattern (see
        // [`mandatory_literal_tail_of_pattern`]), never hardcoded per language, so any
        // grammar that declares a suffix-terminated literal category gets it.
        //
        // ── The COMPOSITE form (2026-07-27) ──────────────────────────────────────
        //
        // Appending the tail to the payload's WHOLE rendering is right only while that
        // rendering is a single numeral. `CanonicalBigRat` renders `3/4` for a
        // non-unit denominator, and `format!("{}r", v)` then yields `3/4r` — which is
        // not a word of `(…)r(/(…)r)?` in either language that declares one:
        //
        //   Calculator  `3/4`   ⇒ IntToBigRat(DivInt 3 4)   ← INTEGER division, value 0
        //   Rholang     `3/4r`  ⇒ parse error at BigRat
        //
        // The tail belongs to each COMPONENT of the composite, not to the rendering:
        // `3r/4r`. The separator is the one the pattern's own optional group declares,
        // so this is grammar-derived exactly as the tail is. When no composite is
        // declared, `composite_separator` is `None` and the emitted arm is
        // byte-identical to the append-once form above — `BigInt`'s `-7` ⇒ `-7n` and
        // `UInt32`'s `4294967295` ⇒ `4294967295u32` do not move.
        match composite_separator {
            None => quote! {
                #category::#literal_label(v) => {
                    stack.push(DisplayTask::WriteString(format!(concat!("{}", #tail), v)));
                }
            },
            Some(separator) => quote! {
                #category::#literal_label(v) => {
                    // The payload's own rendering, re-tailed component-wise. A rendering
                    // with no separator has exactly one component, so the whole-value and
                    // composite cases share this one path.
                    let __rendered = format!("{}", v);
                    let mut __out = std::string::String::with_capacity(
                        __rendered.len() + #tail.len() * 2,
                    );
                    let mut __first = true;
                    for __component in __rendered.split(#separator) {
                        if !__first {
                            __out.push_str(#separator);
                        }
                        __first = false;
                        __out.push_str(__component);
                        __out.push_str(#tail);
                    }
                    stack.push(DisplayTask::WriteString(__out));
                }
            },
        }
    } else {
        // Bare value display for all numeric types (matches main). Suffixes
        // like `u32` / `i32` are accepted at parse via OPTIONAL regex fragments,
        // so they are not required in display; a MANDATORY tail is handled above.
        quote! {
            #category::#literal_label(v) => {
                stack.push(DisplayTask::WriteString(format!("{}", v)));
            }
        }
    }
}

/// The literal suffix that EVERY word of `pattern`'s language must end with, or
/// `None` when the pattern forces no such suffix.
///
/// Grammar-derived Stage-C input (divergence I): a `literals { }` category whose
/// declared pattern ends in unquantified literal characters — `BigInt`'s
/// `-?(…)n`, `BigRat`'s `(…)r` — can only ever be *written* with that tail, so
/// Display must *emit* it.
///
/// The scan walks the pattern backwards over characters that are plain literals
/// (ASCII alphanumeric, never a regex metacharacter) and stops at the first
/// character that is not. Two stop conditions are conservative refusals:
///
/// - stopping on `|` means the accumulated run is only ONE branch of an
///   alternation (`yeap|nope|true|false` would otherwise "prove" every boolean
///   ends in `false`), and
/// - stopping on `\` means the run's first character was escaped, so it is not a
///   literal at all.
///
/// Stopping on `)`, `]`, `?`, `*`, `+` or `}` is SAFE: those close a group, class
/// or quantifier that precedes the run, and a quantifier binds only what is to
/// its left — the run itself remains mandatory. Consuming the ENTIRE pattern is
/// also a refusal: a wholly-literal pattern has no value part for the tail to
/// follow.
///
/// ## Display must stay TOTAL — the sign-coverage side condition
///
/// A tail is only usable if the pattern's language covers EVERY value the native
/// type can render. A signed payload renders a leading `-`, so a pattern that does
/// not admit one (Rholang/Calculator `BigRat`: `(…)r`, versus `BigInt`: `-?(…)r`)
/// covers only the non-negative half. Appending its tail anyway would emit
/// `-823154820r` — a MINUS followed by a rational literal, which those grammars
/// have no unary-minus rule to read at the `BigRat` category. Refusing the tail in
/// that case keeps Display total and byte-identical to its pre-Stage-C output for
/// such categories; giving them a tail is a separate grammar change (their pattern
/// would have to gain `-?`, as `BigInt`'s already has).
fn mandatory_literal_tail_of_pattern(
    pattern: &str,
    payload_is_signed: bool,
    category_has_unary_minus: bool,
) -> Option<MandatoryTail> {
    // ── The OPTIONAL-REPEAT form (2026-07-27) ───────────────────────────────────
    //
    // A pattern may end in a `?`-quantified group — Calculator's `BigRat`,
    // `(…)r(/(…)r)?`, whose optional half is the composite rational `3r/4r`. The
    // backward scan below sees the `?` first and refuses, which is how that category
    // ended up with NO tail at all and a `Display` that wrote `3/4` — a surface its
    // own acceptor rejects and that `Int`'s acceptor takes instead, as INTEGER
    // division (`3/4 ⇒ 0`). See [`composite_repeat_of_optional_group`].
    if let Some(mandatory) =
        composite_repeat_of_optional_group(pattern, payload_is_signed, category_has_unary_minus)
    {
        return Some(mandatory);
    }
    let tail = mandatory_literal_tail_run(pattern)?;
    if payload_is_signed && !pattern.starts_with('-') && !category_has_unary_minus {
        // The pattern cannot spell a negative value as one token, and the category has
        // no unary-minus rule to read a detached sign either; see above.
        return None;
    }
    Some(MandatoryTail { tail, composite_separator: None })
}

/// A category's mandatory literal tail, plus the separator of its declared COMPOSITE
/// form when it has one.
///
/// `composite_separator` is `Some(sep)` exactly when the declared pattern ends in an
/// optional group that repeats the same tail after `sep` — i.e. the payload's own
/// `Display` may render as `A<sep>B`, and the tail then belongs to **each** component
/// rather than to the rendering as a whole. `None` restores the historical
/// append-once behaviour byte-for-byte.
#[derive(Debug, Clone)]
struct MandatoryTail {
    tail: String,
    composite_separator: Option<String>,
}

/// The trailing run of unquantified literal characters of `pattern`, or `None`.
///
/// Extracted from [`mandatory_literal_tail_of_pattern`] so the optional-repeat case can
/// re-use it on a pattern PREFIX. The stop conditions are unchanged and are documented
/// on the caller.
fn mandatory_literal_tail_run(pattern: &str) -> Option<String> {
    let bytes = pattern.as_bytes();
    let mut i = bytes.len();
    while i > 0 && bytes[i - 1].is_ascii_alphanumeric() {
        i -= 1;
    }
    if i == bytes.len() || i == 0 {
        // No trailing literal run, or the pattern is nothing but one.
        return None;
    }
    match bytes[i - 1] {
        // One branch of an alternation, or an escape sequence: not mandatory.
        b'|' | b'\\' => return None,
        _ => {},
    }
    Some(pattern[i..].to_string())
}

/// Recognise `…<prefix><tail>(<sep>…<tail>)?` — a pattern whose last element is an
/// OPTIONAL group repeating the prefix's own tail after a fixed literal separator.
///
/// The recognition is deliberately conservative and each condition is a proof
/// obligation, not a convenience:
///
/// 1. the pattern ends in `)?`, and its `(` is found by a BALANCED backward scan
///    (so a `?` inside the group cannot be mistaken for the quantifier);
/// 2. the PREFIX before the group has a mandatory tail `T` — this is what every word
///    ends with when the optional group is ABSENT;
/// 3. the group's body ALSO ends with `T` — without this, a word WITH the group would
///    not end in `T` and `T` would not be mandatory at all;
/// 4. the group's body begins with a run of plain literal characters, which is the
///    separator between the two components.
///
/// The sign side condition of the caller applies here too, with the same relaxation:
/// a pattern that cannot spell a leading `-` is still usable when the CATEGORY has a
/// unary-minus rule to read the detached sign (Calculator's
/// `NegBigRat . a:BigRat |- "-" a : BigRat`), because then `-1r/2r` is read as
/// `NegBigRat(RatLit 1/2)` — a term of the same denotation whose own Display is that
/// same string, so `Display` stays total AND lands inside the language.
fn composite_repeat_of_optional_group(
    pattern: &str,
    payload_is_signed: bool,
    category_has_unary_minus: bool,
) -> Option<MandatoryTail> {
    let without_quantifier = pattern.strip_suffix(")?")?;
    // Balanced backward scan for the `(` that opens the final group. `depth` counts
    // the closers seen but not yet matched, starting at 1 for the `)` just stripped.
    let bytes = without_quantifier.as_bytes();
    let mut depth = 1usize;
    let mut open = None;
    for i in (0..bytes.len()).rev() {
        match bytes[i] {
            b')' if i == 0 || bytes[i - 1] != b'\\' => depth += 1,
            b'(' if i == 0 || bytes[i - 1] != b'\\' => {
                depth -= 1;
                if depth == 0 {
                    open = Some(i);
                    break;
                }
            },
            _ => {},
        }
    }
    let open = open?;
    let prefix = &without_quantifier[..open];
    let body = &without_quantifier[open + 1..];

    let tail = mandatory_literal_tail_run(prefix)?;
    if !body.ends_with(&tail) {
        // A word carrying the optional group would not end in `tail`.
        return None;
    }
    let separator: String = body
        .chars()
        .take_while(|c| !is_regex_metacharacter(*c))
        .collect();
    if separator.is_empty() {
        return None;
    }
    if payload_is_signed && !pattern.starts_with('-') && !category_has_unary_minus {
        return None;
    }
    Some(MandatoryTail {
        tail,
        composite_separator: Some(separator),
    })
}

/// Whether `c` carries regex meaning rather than standing for itself. Used only to
/// bound the separator run of a composite group, so it errs toward stopping early.
fn is_regex_metacharacter(c: char) -> bool {
    matches!(
        c,
        '(' | ')' | '[' | ']' | '{' | '}' | '|' | '?' | '*' | '+' | '.' | '\\' | '^' | '$'
    )
}

/// Whether `category` has a unary-minus rule over ITSELF — `"-" a : Cat` for a single
/// parameter `a : Cat`.
///
/// This is the predicate the sign side condition of
/// [`mandatory_literal_tail_of_pattern`] always MEANT: its comment refused a tail
/// because those grammars had "no unary-minus rule to read at the category", but it
/// tested the PATTERN for a `-?` instead of testing the grammar for the rule. Where the
/// rule exists, a detached sign is readable and the tail is safe.
fn category_has_unary_minus_rule(language: &LanguageDef, category: &syn::Ident) -> bool {
    language.terms.iter().any(|rule| {
        if &rule.category != category {
            return false;
        }
        let Some(pattern) = rule.syntax_pattern.as_ref() else {
            return false;
        };
        let [SyntaxExpr::Literal(sign), SyntaxExpr::Param(param)] = pattern.as_slice() else {
            return false;
        };
        if sign != "-" {
            return false;
        }
        rule.term_context.as_ref().is_some_and(|params| {
            matches!(
                params.as_slice(),
                [TermParam::Simple { name, ty: TypeExpr::Base(base) }]
                    if name == param && base == category
            )
        })
    })
}

// =============================================================================
// Display Impl Generation (delegates to iterative engine)
// =============================================================================

/// Generate `impl Display for Cat` blocks that delegate to the iterative engine.
fn generate_display_impls(language: &LanguageDef) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            let cat = &lang_type.name;
            let task_variant = format_ident!("Display{}", cat);

            quote! {
                impl std::fmt::Display for #cat {
                    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                        // Use try_with to avoid double-panic when Display is called
                        // during panic unwinding (e.g., proptest error formatting).
                        // Falls back to a fresh local stack if TLS is unavailable.
                        let result = DISPLAY_TASK_POOL.try_with(|cell| {
                            let mut stack = cell.take();
                            stack.clear();
                            stack.push(DisplayTask::#task_variant(self as *const #cat, 0));
                            let result = display_iterative(&mut stack, f);
                            cell.set(stack);
                            result
                        });
                        match result {
                            Ok(fmt_result) => fmt_result,
                            Err(_) => {
                                // TLS unavailable (thread shutdown or panic unwinding).
                                let mut stack = Vec::new();
                                stack.push(DisplayTask::#task_variant(self as *const #cat, 0));
                                display_iterative(&mut stack, f)
                            }
                        }
                    }
                }
            }
        })
        .collect();

    quote! {
        #(#impls)*
    }
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Format just the terminals for a unit variant
fn format_terminals(rule: &GrammarRule) -> String {
    rule.items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::Terminal(term) => Some(term.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("")
}

/// Extract base category identifier from a TypeExpr
fn extract_base_category_ident(ty: &TypeExpr) -> syn::Ident {
    match ty {
        TypeExpr::Base(ident) => ident.clone(),
        TypeExpr::Collection { element, .. } => extract_base_category_ident(element),
        TypeExpr::Arrow { codomain, .. } => extract_base_category_ident(codomain),
        TypeExpr::MultiBinder(inner) => extract_base_category_ident(inner),
        TypeExpr::Refined { base, .. } => extract_base_category_ident(base),
        TypeExpr::Map { value, .. } => extract_base_category_ident(value),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::rule_fixture;
    use mettail_ast::language::LanguageDef;
    use proc_macro2::Span;
    use std::collections::HashMap;

    fn ident(name: &str) -> syn::Ident {
        syn::Ident::new(name, Span::call_site())
    }

    fn simple_param(name: &str, cat: &str) -> TermParam {
        TermParam::Simple {
            name: ident(name),
            ty: TypeExpr::Base(ident(cat)),
        }
    }

    fn syntaxless_projection(label: &str, source: &str, target: &str, auto: bool) -> GrammarRule {
        let param = "v";
        rule(
            label,
            target,
            vec![simple_param(param, source)],
            vec![SyntaxExpr::Param(ident(param))],
            auto,
        )
    }

    fn rule(
        label: &str,
        target: &str,
        term_context: Vec<TermParam>,
        syntax_pattern: Vec<SyntaxExpr>,
        auto: bool,
    ) -> GrammarRule {
        GrammarRule {
            term_context: Some(term_context),
            syntax_pattern: Some(syntax_pattern),
            is_auto_injected: auto,
            ..rule_fixture(ident(label), ident(target))
        }
    }

    /// Retained for the disabled projection-surface tests below (DEFECT 1,
    /// 2026-07-26). Their successors work on single `GrammarRule`s and on a
    /// hand-built `BpLookup`, so nothing live needs a whole `LanguageDef` — but
    /// deleting the builder would make the retained tests unreadable.
    #[allow(dead_code)]
    fn language(terms: Vec<GrammarRule>) -> LanguageDef {
        LanguageDef {
            name: ident("DisplayProjectionTest"),
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
            terms,
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // DISABLED 2026-07-26 (DEFECT 1) — the four unit tests that pinned the
    // borrowed-wrapper election. Each asserted a PROPERTY OF THE DEFECT, not of the
    // intent: `projection_wrapper_search_rejects_unary_operators` asserted the
    // election lands on `BigintCast` (a real `Proc → BigInt` constructor), and
    // `auto_syntaxless_projection_is_contextual_not_always_wrapped` asserted the
    // emitted arm literally contains the token `bigint`. With the election disabled
    // those properties are gone by design; their successors are the four
    // `projection_operand_*` tests directly below, which pin the REPLACEMENT
    // (`atomic_child_bp` routing → the source category's own `(` … `)`).
    // Retained verbatim; not deleted.
    //
    // #[test]
    // fn projection_wrapper_search_rejects_unary_operators() {
    //     let projection = syntaxless_projection("BoolToBigInt", "Bool", "BigInt", true);
    //     let proc_bool = syntaxless_projection("ProcBool", "Bool", "Proc", false);
    //     let neg_bigint = rule(
    //         "NegBigInt",
    //         "BigInt",
    //         vec![simple_param("a", "BigInt")],
    //         vec![SyntaxExpr::Literal("-".to_string()), SyntaxExpr::Param(ident("a"))],
    //         false,
    //     );
    //     let bigint_cast = rule(
    //         "BigintCast",
    //         "BigInt",
    //         vec![simple_param("a", "Proc")],
    //         vec![
    //             SyntaxExpr::Literal("bigint".to_string()),
    //             SyntaxExpr::Literal("(".to_string()),
    //             SyntaxExpr::Param(ident("a")),
    //             SyntaxExpr::Literal(")".to_string()),
    //         ],
    //         false,
    //     );
    //     let lang = language(vec![projection, proc_bool, neg_bigint, bigint_cast]);
    //
    //     let (wrapper, param_name) =
    //         find_projection_surface_wrapper(&lang, "Bool", "BigInt").unwrap();
    //
    //     assert_eq!(wrapper.label.to_string(), "BigintCast");
    //     assert_eq!(param_name, "a");
    // }
    //
    // #[test]
    // fn explicit_syntaxless_projection_stays_transparent() {
    //     let projection = syntaxless_projection("IntToBigInt", "Int", "BigInt", false);
    //     let bigint_cast = rule(
    //         "BigintCast",
    //         "BigInt",
    //         vec![simple_param("a", "Proc")],
    //         vec![
    //             SyntaxExpr::Literal("bigint".to_string()),
    //             SyntaxExpr::Literal("(".to_string()),
    //             SyntaxExpr::Param(ident("a")),
    //             SyntaxExpr::Literal(")".to_string()),
    //         ],
    //         false,
    //     );
    //     let lang = language(vec![projection.clone(), bigint_cast]);
    //
    //     assert!(
    //         generate_projection_surface_display_arm_for_field(&projection, &ident("v"), &lang)
    //             .is_none()
    //     );
    // }
    //
    // #[test]
    // fn auto_syntaxless_projection_is_contextual_not_always_wrapped() {
    //     let projection = syntaxless_projection("BoolToBigInt", "Bool", "BigInt", true);
    //     let proc_bool = syntaxless_projection("ProcBool", "Bool", "Proc", false);
    //     let bigint_cast = rule(
    //         "BigintCast",
    //         "BigInt",
    //         vec![simple_param("a", "Proc")],
    //         vec![
    //             SyntaxExpr::Literal("bigint".to_string()),
    //             SyntaxExpr::Literal("(".to_string()),
    //             SyntaxExpr::Param(ident("a")),
    //             SyntaxExpr::Literal(")".to_string()),
    //         ],
    //         false,
    //     );
    //     let lang = language(vec![projection.clone(), proc_bool, bigint_cast]);
    //
    //     let arm =
    //         generate_projection_surface_display_arm_for_field(&projection, &ident("v"), &lang)
    //             .expect("auto projection should borrow a wrapper in operand context");
    //     let rendered = arm.to_string();
    //
    //     assert!(rendered.contains("if min_bp == 0"));
    //     assert!(rendered.contains("DisplayBool"));
    //     assert!(rendered.contains("bigint"));
    // }
    //
    // #[test]
    // fn explicit_syntaxless_projection_can_use_wrapper_in_operand_context() {
    //     let projection = syntaxless_projection("IntToBigInt", "Int", "BigInt", false);
    //     let proc_int = syntaxless_projection("ProcInt", "Int", "Proc", false);
    //     let bigint_cast = rule(
    //         "BigintCast",
    //         "BigInt",
    //         vec![simple_param("a", "Proc")],
    //         vec![
    //             SyntaxExpr::Literal("bigint".to_string()),
    //             SyntaxExpr::Literal("(".to_string()),
    //             SyntaxExpr::Param(ident("a")),
    //             SyntaxExpr::Literal(")".to_string()),
    //         ],
    //         false,
    //     );
    //     let lang = language(vec![projection.clone(), proc_int, bigint_cast]);
    //
    //     assert!(generate_contextual_projection_surface_display_arm_for_field(
    //         &projection,
    //         &ident("v"),
    //         &lang
    //     )
    //     .is_some());
    // }

    // ════════════════════════════════════════════════════════════════════════
    // SUCCESSORS — the replacement mechanism (DEFECT 1 fix, 2026-07-26)
    // ════════════════════════════════════════════════════════════════════════

    /// An EXPLICIT cross-category projection routes through the transparent-wrapper
    /// path, whose child threshold is `atomic_child_bp` — so the source's own
    /// precedence logic supplies the bracket.
    #[test]
    fn projection_operand_explicit_projection_forwards_min_bp() {
        let projection = syntaxless_projection("IntToBigInt", "Int", "BigInt", false);
        assert!(
            is_syntaxless_single_child_projection(&projection),
            "an explicit cross-category projection must take the atomic_child_bp route"
        );
    }

    /// An AUTO-INJECTED cross-category projection must take the SAME route. Before
    /// the fix `simple_projection_shape_for_display` returned `None` for
    /// `is_auto_injected` rules, because the (now disabled) surface arm claimed them
    /// first; leaving that exclusion in place would have rendered an auto-injected
    /// projection's source bare at every threshold and lost its bracketing.
    #[test]
    fn projection_operand_auto_injected_projection_also_forwards_min_bp() {
        let projection = syntaxless_projection("BoolToBigInt", "Bool", "BigInt", true);
        assert!(
            is_syntaxless_single_child_projection(&projection),
            "an auto-injected cross-category projection must take the atomic_child_bp route"
        );
    }

    /// A SAME-category rule is not a projection and must keep its own thresholds.
    #[test]
    fn projection_operand_same_category_rule_is_not_a_projection() {
        let neg_bigint = rule(
            "NegBigInt",
            "BigInt",
            vec![simple_param("a", "BigInt")],
            vec![SyntaxExpr::Literal("-".to_string()), SyntaxExpr::Param(ident("a"))],
            false,
        );
        assert!(
            !is_syntaxless_single_child_projection(&neg_bigint),
            "a unary operator is not a transparent projection"
        );
    }

    /// The threshold the projection forwards is strictly ABOVE every binding power
    /// of the source category, which is what makes an operator-rooted source
    /// parenthesize while an atom stays bare. Pins the arithmetic of
    /// `BpLookup::atomic_child_bp` rather than trusting it.
    #[test]
    fn projection_operand_atomic_child_bp_exceeds_every_source_bp() {
        let mut lookup = BpLookup::empty();
        lookup.max_bp_by_category.insert("Int".to_string(), 40);
        assert_eq!(
            lookup.atomic_child_bp("Int"),
            41,
            "the projection child threshold must exceed the source category's max bp"
        );
        assert_eq!(
            lookup.atomic_child_bp("CategoryWithNoOperators"),
            1,
            "a source category with no operators still gets a non-zero threshold"
        );
    }
}
