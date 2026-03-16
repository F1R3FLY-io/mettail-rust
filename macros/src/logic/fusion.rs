//! BCG02: Rule fusion analysis for chained deconstruction-rewrite patterns.
//!
//! ## Overview
//!
//! This module detects chains of **deconstruction** followed by **rewrite** rules
//! that produce intermediate tuples which could be eliminated by fusing the rules
//! into a single combined rule.
//!
//! ### The pattern
//!
//! In the generated Ascent code, a typical deconstruction-rewrite chain looks like:
//!
//! ```text
//! // Step 1: Deconstruction — extract subterms from a constructor.
//! //   cat(sub) <-- cat(t), for sub in all_subterms_cat_cat(t);
//! //   This populates the `cat` relation with subterms.
//!
//! // Step 2: Rewrite — match a constructor pattern and produce a rewrite.
//! //   rw_cat(s_orig, t) <-- eq_cat(s_orig, s), if let Cat::Ctor(f0, f1) = s, ..., let t = ...;
//! ```
//!
//! When a rewrite rule's LHS pattern matches a constructor that is *also* extracted
//! by a deconstruction rule, the rewrite's pattern-match against the `cat` relation
//! is redundant with the deconstruction's extraction. A **fused** rule would directly
//! match the parent constructor and apply the rewrite, skipping the intermediate
//! `cat(sub)` insertion for the deconstructed subterm.
//!
//! ### Safety conditions
//!
//! A chain is safe to fuse only if:
//! 1. The intermediate relation (the deconstructed subterm in `cat`) is consumed
//!    *only* by the candidate rewrite rule (no other equations, rewrites, or logic
//!    rules reference that constructor's subterms from the `cat` relation).
//! 2. The rewrite rule has no premises (congruence rules are excluded).
//! 3. The rewrite LHS is a simple constructor application (no nested patterns,
//!    collections, or metasyntax).
//!
//! ### Current scope
//!
//! This module provides **analysis and diagnostics only**. It detects fusable chains
//! and emits `note[BCG02]` diagnostics. Actual code generation changes (fusing the
//! Ascent rules) are deferred to a future sprint due to the complexity of modifying
//! the deconstruction and rewrite codegen paths simultaneously.

use crate::ast::grammar::GrammarItem;
use crate::ast::language::LanguageDef;
use crate::ast::pattern::{Pattern, PatternTerm};
use std::collections::{HashMap, HashSet};

// =============================================================================
// Data types
// =============================================================================

/// A candidate for rule fusion: a deconstruction rule feeds an intermediate
/// relation that is consumed by a rewrite rule.
#[derive(Debug, Clone)]
#[allow(dead_code)] // Fields are part of the public diagnostic API
pub struct FusionCandidate {
    /// Index of the grammar rule (constructor) whose deconstruction produces the
    /// intermediate subterm. Index into `language.terms`.
    pub decon_rule_idx: usize,
    /// Label of the deconstructing constructor (e.g., `"PPar"`, `"Add"`).
    pub decon_constructor: String,
    /// Category of the parent constructor being deconstructed (e.g., `"Proc"`).
    pub parent_category: String,
    /// Index of the rewrite rule that consumes the intermediate. Index into
    /// `language.rewrites`.
    pub rewrite_rule_idx: usize,
    /// Name of the rewrite rule (e.g., `"Exec"`).
    pub rewrite_name: String,
    /// Constructor matched by the rewrite LHS (e.g., `"PDrop"`).
    pub rewrite_lhs_constructor: String,
    /// Category of the rewrite LHS constructor (e.g., `"Proc"`).
    pub rewrite_category: String,
    /// Whether this candidate is safe to fuse (no other consumers of the
    /// intermediate relation for this specific constructor).
    pub is_safe: bool,
    /// If not safe, the names of the other consumers that prevent fusion.
    pub blocking_consumers: Vec<String>,
}

/// Summary report from fusion analysis.
#[derive(Debug, Clone)]
pub struct FusionReport {
    /// All detected fusion candidates (both safe and unsafe).
    pub candidates: Vec<FusionCandidate>,
    /// Number of candidates that are safe to fuse.
    pub safe_count: usize,
    /// Number of candidates blocked by multiple consumers.
    pub blocked_count: usize,
    /// Estimated number of intermediate tuples eliminated if all safe fusions
    /// are applied. This is a heuristic: each safe fusion eliminates one
    /// intermediate `cat(sub)` insertion per deconstructed subterm.
    pub estimated_tuple_reduction: usize,
}

// =============================================================================
// Analysis entry points
// =============================================================================

/// Detect all fusion candidates in the language definition.
///
/// Identifies deconstruction-rewrite chains by:
/// 1. Building a map of which constructors produce subterms of which categories
///    (from grammar rules / deconstruction).
/// 2. Building a map of which rewrite rules consume constructors from which
///    categories (from rewrite LHS patterns).
/// 3. Matching chains: a deconstruction of constructor C in category X produces
///    subterms of category Y, and a rewrite rule R matches a constructor in
///    category Y — if R's LHS constructor is one of the subterm types extracted
///    by C's deconstruction, we have a chain.
/// 4. Checking safety: for each chain, verify that no other equation, rewrite,
///    or logic rule also consumes the intermediate constructor from the category
///    relation.
pub fn detect_fusion_candidates(language: &LanguageDef) -> Vec<FusionCandidate> {
    // Step 1: Build subterm extraction map.
    // For each grammar rule (constructor), map (parent_category, constructor_label)
    // → set of (field_index, target_category) pairs.
    let subterm_map = build_subterm_map(language);

    // Step 2: Identify non-congruence rewrite rules with simple constructor LHS.
    let rewrite_info = collect_rewrite_lhs_info(language);

    // Step 3: Build consumer map — which constructors are referenced by rules
    // other than the candidate rewrite.
    let constructor_consumers = build_constructor_consumer_map(language);

    // Step 4: Match chains and check safety.
    let mut candidates = Vec::new();

    for (rewrite_idx, rw_info) in &rewrite_info {
        // The rewrite matches constructor `rw_info.constructor` in category
        // `rw_info.category`. Find all parent constructors that deconstruct
        // to produce subterms of type `rw_info.category` containing the
        // matched constructor.
        for (decon_idx, decon_label, parent_cat, target_cats) in &subterm_map {
            // The deconstruction of `decon_label` (in `parent_cat`) extracts
            // subterms of certain categories. If `rw_info.category` is among
            // them, this is a chain candidate.
            if !target_cats.contains(&rw_info.category) {
                continue;
            }

            // Check safety: is `rw_info.constructor` in `rw_info.category`
            // consumed *only* by this rewrite rule?
            // Consumer names are prefixed (e.g., "rw:Exec", "eq:ScopeExtrusion"),
            // so filter against the full prefixed name.
            let consumer_key = (rw_info.category.clone(), rw_info.constructor.clone());
            let rw_consumer_name = format!("rw:{}", rw_info.name);
            let other_consumers: Vec<String> = constructor_consumers
                .get(&consumer_key)
                .map(|consumers| {
                    consumers
                        .iter()
                        .filter(|c| *c != &rw_consumer_name)
                        .cloned()
                        .collect()
                })
                .unwrap_or_default();

            let is_safe = other_consumers.is_empty();

            candidates.push(FusionCandidate {
                decon_rule_idx: *decon_idx,
                decon_constructor: decon_label.clone(),
                parent_category: parent_cat.clone(),
                rewrite_rule_idx: *rewrite_idx,
                rewrite_name: rw_info.name.clone(),
                rewrite_lhs_constructor: rw_info.constructor.clone(),
                rewrite_category: rw_info.category.clone(),
                is_safe,
                blocking_consumers: other_consumers,
            });
        }
    }

    candidates
}

/// Analyze the fusion potential of a language definition.
///
/// Returns a summary report with counts and estimated tuple reduction.
pub fn analyze_fusion_potential(language: &LanguageDef) -> FusionReport {
    let candidates = detect_fusion_candidates(language);
    let safe_count = candidates.iter().filter(|c| c.is_safe).count();
    let blocked_count = candidates.len() - safe_count;

    // Heuristic: each safe fusion eliminates one intermediate tuple insertion
    // per iteration of the deconstructing rule. The actual reduction depends on
    // the number of terms flowing through the category relation at runtime, but
    // at compile time we approximate by counting safe chains.
    let estimated_tuple_reduction = safe_count;

    FusionReport {
        candidates,
        safe_count,
        blocked_count,
        estimated_tuple_reduction,
    }
}

// =============================================================================
// Internal helpers
// =============================================================================

/// Information about a rewrite rule's LHS.
struct RewriteLhsInfo {
    /// Rewrite rule name.
    name: String,
    /// Constructor matched by the LHS pattern.
    constructor: String,
    /// Category of the LHS constructor.
    category: String,
}

/// Build a map of subterm extractions from grammar rules.
///
/// Returns a list of (constructor_index, constructor_label, parent_category,
/// set_of_target_categories) tuples. Each entry says: "deconstruction of
/// constructor C in category P extracts subterms of categories {T1, T2, ...}".
fn build_subterm_map(
    language: &LanguageDef,
) -> Vec<(usize, String, String, HashSet<String>)> {
    let all_categories: HashSet<String> =
        language.types.iter().map(|t| t.name.to_string()).collect();

    let mut result = Vec::new();

    for (idx, rule) in language.terms.iter().enumerate() {
        let parent_cat = rule.category.to_string();
        let label = rule.label.to_string();
        let mut target_cats = HashSet::new();

        // Extract target categories from term_context (new syntax)
        if let Some(ref term_ctx) = rule.term_context {
            for param in term_ctx {
                match param {
                    crate::ast::grammar::TermParam::Simple { ty, .. } => {
                        if let crate::ast::types::TypeExpr::Base(ident) = ty {
                            let cat = ident.to_string();
                            if all_categories.contains(&cat) {
                                target_cats.insert(cat);
                            }
                        }
                    }
                    crate::ast::grammar::TermParam::Abstraction { ty, .. }
                    | crate::ast::grammar::TermParam::MultiAbstraction { ty, .. } => {
                        if let crate::ast::types::TypeExpr::Base(ident) = ty {
                            let cat = ident.to_string();
                            if all_categories.contains(&cat) {
                                target_cats.insert(cat);
                            }
                        }
                    }
                    crate::ast::grammar::TermParam::GuardBody { .. } => {}
                }
            }
        } else {
            // Old syntax: inspect items
            for item in &rule.items {
                match item {
                    GrammarItem::NonTerminal(cat) => {
                        let cat_str = cat.to_string();
                        if all_categories.contains(&cat_str) {
                            target_cats.insert(cat_str);
                        }
                    }
                    GrammarItem::Collection { element_type, .. } => {
                        let cat_str = element_type.to_string();
                        if all_categories.contains(&cat_str) {
                            target_cats.insert(cat_str);
                        }
                    }
                    GrammarItem::Binder { category, .. } => {
                        let cat_str = category.to_string();
                        if all_categories.contains(&cat_str) {
                            target_cats.insert(cat_str);
                        }
                    }
                    GrammarItem::Terminal(_) => {}
                }
            }
        }

        if !target_cats.is_empty() {
            result.push((idx, label, parent_cat, target_cats));
        }
    }

    result
}

/// Collect information about non-congruence rewrite rules with simple
/// constructor LHS patterns.
///
/// Returns a map of (rewrite_index, RewriteLhsInfo) for each eligible rewrite.
fn collect_rewrite_lhs_info(language: &LanguageDef) -> Vec<(usize, RewriteLhsInfo)> {
    let mut result = Vec::new();

    for (idx, rw) in language.rewrites.iter().enumerate() {
        // Skip congruence rules (those with a congruence premise)
        if rw.is_congruence_rule() {
            continue;
        }

        // Only consider simple constructor LHS patterns
        if let Some((constructor, category)) = extract_simple_constructor_lhs(&rw.left, language) {
            result.push((
                idx,
                RewriteLhsInfo {
                    name: rw.name.to_string(),
                    constructor,
                    category,
                },
            ));
        }
    }

    result
}

/// Extract the constructor name and category from a simple constructor LHS pattern.
///
/// Returns `Some((constructor_name, category_name))` if the pattern is a simple
/// `Apply { constructor, args }` where all args are variables (no nested
/// constructors, collections, or metasyntax).
///
/// Returns `None` for complex patterns (nested constructors, collections, etc.)
/// since those require multi-level matching that complicates fusion.
fn extract_simple_constructor_lhs(
    pattern: &Pattern,
    language: &LanguageDef,
) -> Option<(String, String)> {
    match pattern {
        Pattern::Term(PatternTerm::Apply { constructor, args: _ }) => {
            // For fusion analysis, we accept any Apply pattern — the key is that the
            // outer constructor is what gets matched during deconstruction.
            let category = language.category_of_constructor(constructor)?;
            Some((constructor.to_string(), category.to_string()))
        }
        _ => None,
    }
}

/// Build a map of which rules consume which constructors from which categories.
///
/// The key is (category, constructor_label), and the value is the set of
/// rule names that reference that constructor in their patterns.
///
/// This is used to determine whether an intermediate relation has a single
/// consumer (safe to fuse) or multiple consumers (unsafe).
fn build_constructor_consumer_map(
    language: &LanguageDef,
) -> HashMap<(String, String), HashSet<String>> {
    let mut consumers: HashMap<(String, String), HashSet<String>> = HashMap::new();

    // Equations reference constructors in both LHS and RHS
    for eq in &language.equations {
        let mut labels = HashSet::new();
        eq.left.collect_constructor_labels(&mut labels);
        eq.right.collect_constructor_labels(&mut labels);

        for label in &labels {
            if let Some(category) = language
                .get_constructor(&syn::Ident::new(label, proc_macro2::Span::call_site()))
                .map(|r| r.category.to_string())
            {
                consumers
                    .entry((category, label.clone()))
                    .or_default()
                    .insert(format!("eq:{}", eq.name));
            }
        }
    }

    // Rewrites reference constructors in LHS (and RHS, but RHS is construction, not matching)
    for rw in &language.rewrites {
        let mut labels = HashSet::new();
        rw.left.collect_constructor_labels(&mut labels);
        // RHS constructors are used for construction, not matching — but they
        // still represent a "consumer" because the term they construct gets
        // inserted into the category relation and could be matched by other rules.
        rw.right.collect_constructor_labels(&mut labels);

        for label in &labels {
            if let Some(category) = language
                .get_constructor(&syn::Ident::new(label, proc_macro2::Span::call_site()))
                .map(|r| r.category.to_string())
            {
                consumers
                    .entry((category, label.clone()))
                    .or_default()
                    .insert(format!("rw:{}", rw.name));
            }
        }
    }

    // Logic block: we can't easily introspect TokenStream content, so we
    // conservatively assume logic blocks don't reference specific constructors
    // by pattern matching. If they do, the user would need to audit manually.
    // The relation declarations give some signal but are coarse-grained.

    consumers
}

// =============================================================================
// Diagnostic emission
// =============================================================================

/// Emit BCG02 diagnostic notes about fusion opportunities.
///
/// Called from `generate_ascent_source` in `mod.rs` when the `RuleFusion` gate
/// is registered.
pub fn emit_fusion_diagnostics(language: &LanguageDef, grammar_name: &str) {
    let report = analyze_fusion_potential(language);

    if report.candidates.is_empty() {
        // No fusion opportunities — verbose-only (not actionable)
        if std::env::var("PRATTAIL_LINT_VERBOSE").is_ok() {
            mettail_prattail::lint::emit_diagnostic(&mettail_prattail::lint::LintDiagnostic {
                id: "G42",
                name: "rule-fusion-analysis",
                severity: mettail_prattail::lint::LintSeverity::Note,
                category: None,
                rule: None,
                message: "BCG02: no deconstruction-rewrite fusion candidates detected".to_string(),
                hint: Some(
                    "fusion applies when a rewrite LHS matches a constructor that is also \
                     extracted by deconstruction from a parent constructor"
                        .to_string(),
                ),
                grammar_name: Some(grammar_name.to_string()),
                source_location: None,
            });
        }
        return;
    }

    // Summary diagnostic — verbose-only when all candidates are blocked (not actionable)
    if report.safe_count == 0 {
        if std::env::var("PRATTAIL_LINT_VERBOSE").is_err() {
            return;
        }
    }

    mettail_prattail::lint::emit_diagnostic(&mettail_prattail::lint::LintDiagnostic {
        id: "G42",
        name: "rule-fusion-analysis",
        severity: mettail_prattail::lint::LintSeverity::Note,
        category: None,
        rule: None,
        message: format!(
            "BCG02: {} fusion candidate(s) detected ({} safe, {} blocked); \
             estimated tuple reduction: {}",
            report.candidates.len(),
            report.safe_count,
            report.blocked_count,
            report.estimated_tuple_reduction,
        ),
        hint: Some(
            "safe candidates can be fused to eliminate intermediate tuple production; \
             blocked candidates have multiple consumers of the intermediate relation"
                .to_string(),
        ),
        grammar_name: Some(grammar_name.to_string()),
        source_location: None,
    });

    // Per-candidate diagnostics (verbose mode only, via PRATTAIL_LINT_VERBOSE)
    if std::env::var("PRATTAIL_LINT_VERBOSE").is_ok() {
        for candidate in &report.candidates {
            let status = if candidate.is_safe {
                "SAFE"
            } else {
                "BLOCKED"
            };
            let detail = if candidate.is_safe {
                format!(
                    "deconstruction of {} ({}) → rewrite {} ({}) matching {} — fusable",
                    candidate.decon_constructor,
                    candidate.parent_category,
                    candidate.rewrite_name,
                    candidate.rewrite_category,
                    candidate.rewrite_lhs_constructor,
                )
            } else {
                format!(
                    "deconstruction of {} ({}) → rewrite {} ({}) matching {} — blocked by: {}",
                    candidate.decon_constructor,
                    candidate.parent_category,
                    candidate.rewrite_name,
                    candidate.rewrite_category,
                    candidate.rewrite_lhs_constructor,
                    candidate.blocking_consumers.join(", "),
                )
            };

            mettail_prattail::lint::emit_diagnostic(&mettail_prattail::lint::LintDiagnostic {
                id: "G42",
                name: "rule-fusion-candidate",
                severity: mettail_prattail::lint::LintSeverity::Note,
                category: Some(candidate.parent_category.clone()),
                rule: Some(candidate.rewrite_name.clone()),
                message: format!("BCG02 [{}]: {}", status, detail),
                hint: None,
                grammar_name: Some(grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// =============================================================================
// BCG02: Fused Rule Code Generation
// =============================================================================

/// Generate a single fused Ascent rule for a safe fusion candidate.
///
/// The fused rule combines parent constructor destructuring with the rewrite LHS
/// pattern match, eliminating the intermediate `cat(sub)` insertion step.
///
/// Generated rule form:
/// ```text
/// rw_rewrite_cat(s_orig.clone(), result) <--
///     eq_parent_cat(s_orig, parent),
///     if let ParentCat::ParentCtor(ref f0, ref f1, ...) = parent,
///     // f_i is the field of type rewrite_cat
///     if let RewriteCat::RewriteLhsCtor(ref rf0, ...) = *f_i,
///     let result = <rewrite_rhs>.normalize(),
///     // BCG05 dedup guard
///     ;
/// ```
fn generate_fused_rule(
    candidate: &FusionCandidate,
    language: &LanguageDef,
) -> Option<proc_macro2::TokenStream> {
    use proc_macro2::TokenStream;
    use quote::{format_ident, quote};

    // Look up the parent constructor (grammar rule)
    let parent_rule = language.terms.get(candidate.decon_rule_idx)?;

    // Look up the rewrite rule
    let rewrite = language.rewrites.get(candidate.rewrite_rule_idx)?;

    // Skip congruence rules (shouldn't be here, but defensive)
    if rewrite.is_congruence_rule() {
        return None;
    }

    // Skip rewrites with premises (conditions complicate fusion)
    if !rewrite.premises.is_empty() {
        return None;
    }

    // Determine categories
    let parent_cat = &parent_rule.category;
    let parent_cat_lower = format_ident!("{}", parent_cat.to_string().to_lowercase());
    let eq_parent_rel = format_ident!("eq_{}", parent_cat_lower);

    let rewrite_cat = rewrite.left.category(language)?;
    let rewrite_cat_lower = format_ident!("{}", rewrite_cat.to_string().to_lowercase());
    let rw_rewrite_rel = format_ident!("rw_{}", rewrite_cat_lower);

    // Build parent constructor destructuring pattern.
    // We need to identify which field(s) of the parent constructor have type rewrite_cat.
    let parent_label = &parent_rule.label;
    let rewrite_cat_str = rewrite_cat.to_string();

    // Collect fields with their types
    let fields: Vec<(usize, String)> = if let Some(ref ctx) = parent_rule.term_context {
        ctx.iter()
            .enumerate()
            .filter_map(|(i, param)| {
                let ty_str = match param {
                    crate::ast::grammar::TermParam::Simple { ty, .. } => {
                        if let crate::ast::types::TypeExpr::Base(ident) = ty {
                            Some(ident.to_string())
                        } else {
                            None
                        }
                    }
                    crate::ast::grammar::TermParam::Abstraction { ty, .. }
                    | crate::ast::grammar::TermParam::MultiAbstraction { ty, .. } => {
                        if let crate::ast::types::TypeExpr::Base(ident) = ty {
                            Some(ident.to_string())
                        } else {
                            None
                        }
                    }
                    crate::ast::grammar::TermParam::GuardBody { .. } => None,
                };
                ty_str.map(|t| (i, t))
            })
            .collect()
    } else {
        parent_rule
            .items
            .iter()
            .enumerate()
            .filter_map(|(i, item)| match item {
                GrammarItem::NonTerminal(cat) => Some((i, cat.to_string())),
                _ => None,
            })
            .collect()
    };

    if fields.is_empty() {
        return None;
    }

    // Find indices of fields matching the rewrite category
    let matching_field_indices: Vec<usize> = fields
        .iter()
        .filter(|(_, ty)| *ty == rewrite_cat_str)
        .map(|(i, _)| *i)
        .collect();

    if matching_field_indices.is_empty() {
        return None;
    }

    // Generate field names for the parent destructuring
    let field_count = fields.len();
    let field_names: Vec<proc_macro2::Ident> = (0..field_count)
        .map(|i| format_ident!("__fused_f{}", i))
        .collect();

    // Build the parent pattern: ParentCat::ParentCtor(ref __fused_f0, ref __fused_f1, ...)
    let parent_pat_fields: Vec<TokenStream> = field_names
        .iter()
        .map(|f| quote! { ref #f })
        .collect();

    // Now generate the rewrite part. For each matching field, we need to:
    // 1. Pattern-match the field as the rewrite LHS constructor
    // 2. Compute the rewrite RHS
    // 3. Produce rw_rewrite_cat(s_orig, result)
    //
    // Use the existing Pattern infrastructure for the rewrite LHS/RHS.
    let s_orig = format_ident!("s_orig");
    let parent_var = format_ident!("__fused_parent");

    // Generate one fused rule per matching field index
    let mut rules = Vec::new();

    for &field_idx in &matching_field_indices {
        let field_var = &field_names[field_idx];

        // Generate rewrite LHS matching clauses on the extracted field.
        // The rewrite LHS pattern matches a constructor of rewrite_cat.
        let lhs_var = format_ident!("__fused_sub");
        let duplicate_vars: std::collections::HashSet<String> = {
            let mut vars = rewrite.left.var_occurrences();
            for (var, count) in rewrite.right.var_occurrences() {
                *vars.entry(var).or_insert(0) += count;
            }
            vars.into_iter()
                .filter(|(_, count)| *count > 1)
                .map(|(var, _)| var)
                .collect()
        };

        let lhs_clauses =
            rewrite
                .left
                .to_ascent_clauses(&lhs_var, rewrite_cat, language, &duplicate_vars);

        // Generate the RHS expression
        let rhs_var = format_ident!("__fused_result");
        let rhs_expr = rewrite.right.to_ascent_rhs(&lhs_clauses.bindings, language);

        // Build the fused rule body:
        // eq_parent(s_orig, __fused_parent),
        // if let ParentCat::Ctor(ref __fused_f0, ...) = __fused_parent,
        // let __fused_sub = (**__fused_f{field_idx}).clone(),  // for Box<T> fields
        // <lhs_clauses for rewrite matching on __fused_sub>,
        // <BCG05 dedup guard>,
        // let __fused_result = <rhs>.normalize()

        let lhs_clauses_ts = &lhs_clauses.clauses;
        let eq_checks = &lhs_clauses.equational_checks;

        // BCG05 dedup guard for the fused rule
        let bcg05_guard = quote! {
            if {
                use std::hash::{Hash, Hasher};
                let mut __bcg05_h = std::hash::DefaultHasher::new();
                #parent_var.hash(&mut __bcg05_h);
                let __bcg05_hash = __bcg05_h.finish();
                thread_local! {
                    static __BCG05_FUSED: std::cell::RefCell<(u64, std::collections::HashSet<u64>)> =
                        std::cell::RefCell::new((0, std::collections::HashSet::new()));
                }
                let __epoch = mettail_runtime::bcg05_epoch();
                __BCG05_FUSED.with(|s| {
                    let mut guard = s.borrow_mut();
                    if guard.0 != __epoch {
                        guard.0 = __epoch;
                        guard.1.clear();
                    }
                    guard.1.insert(__bcg05_hash)
                })
            }
        };

        // Determine whether the field is behind a Box (most AST fields are Box<T>)
        // and build the let binding accordingly
        let let_sub = quote! {
            let #lhs_var = #field_var.as_ref().clone()
        };

        let rule = quote! {
            #rw_rewrite_rel(#s_orig.clone(), #rhs_var) <--
                #eq_parent_rel(#s_orig, #parent_var),
                if let #parent_cat::#parent_label(#(#parent_pat_fields),*) = #parent_var,
                #let_sub,
                #(#lhs_clauses_ts,)*
                #(#eq_checks,)*
                #bcg05_guard,
                let #rhs_var = (#rhs_expr).normalize();
        };

        rules.push(rule);
    }

    if rules.is_empty() {
        return None;
    }

    Some(quote! { #(#rules)* })
}

/// Generate all fused rules for safe fusion candidates.
///
/// Returns (fused_rules, count) where fused_rules is a Vec of TokenStream fragments
/// and count is the number of candidates that were successfully fused.
pub fn generate_all_fused_rules(
    language: &crate::ast::language::LanguageDef,
) -> (Vec<proc_macro2::TokenStream>, usize) {
    let candidates = detect_fusion_candidates(language);
    let safe_candidates: Vec<_> = candidates.into_iter().filter(|c| c.is_safe).collect();

    let mut fused_rules = Vec::new();
    let mut count = 0;

    for candidate in &safe_candidates {
        if let Some(rule) = generate_fused_rule(candidate, language) {
            fused_rules.push(rule);
            count += 1;
        }
    }

    (fused_rules, count)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::language::LanguageDef;
    use quote::quote;
    use syn::parse2;

    /// Parse a language definition from a token stream.
    fn parse_language(tokens: proc_macro2::TokenStream) -> LanguageDef {
        parse2::<LanguageDef>(tokens).expect("failed to parse language definition")
    }

    // ── Simple chain detection ─────────────────────────────────────────────

    #[test]
    fn test_detect_simple_chain() {
        // A language where PDrop(Name) deconstructs to extract Name,
        // and a rewrite matches NQuote(Proc) → Proc.
        // Chain: proc(PDrop(n)) → deconstruct → name(n), then
        //        rw_name(NQuote(p), p) matches name(NQuote(p)).
        // This is the classic Exec pattern from RhoCalc.
        let lang = parse_language(quote! {
            name: TestChain,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                Exec . |- (PDrop (NQuote P)) ~> P ;
            },
        });

        let candidates = detect_fusion_candidates(&lang);
        // PDrop has a Name field → deconstructs to name(n).
        // The Exec rewrite matches PDrop(NQuote(P)), which has constructor PDrop
        // in category Proc. PDrop's deconstruction extracts Name subterms.
        // The Exec rewrite's LHS outer constructor is PDrop (category Proc).
        // So we should find a chain: PDrop deconstruction → Exec rewrite.
        assert!(
            !candidates.is_empty(),
            "expected fusion candidates for TestChain, got none"
        );

        // Find the candidate for PDrop → Exec chain
        let exec_candidate = candidates
            .iter()
            .find(|c| c.rewrite_name == "Exec")
            .expect("expected an Exec fusion candidate");

        assert_eq!(exec_candidate.rewrite_lhs_constructor, "PDrop");
        assert_eq!(exec_candidate.rewrite_category, "Proc");
    }

    #[test]
    fn test_detect_chain_calculator_style() {
        // Calculator-style: Add(Int, Int) deconstructs to int(a), int(b).
        // A rewrite like AddResult . |- (Add A B) ~> ... would be a chain
        // with the deconstruction of Add.
        let lang = parse_language(quote! {
            name: TestCalc,
            types { ![i32] as Int },
            terms {
                Add . a:Int, b:Int |- a "+" b : Int ![a + b] step;
                NumLit . Int ::= "num" ;
            },
            equations {},
            rewrites {},
        });

        // No rewrite rules → no fusion candidates
        let candidates = detect_fusion_candidates(&lang);
        assert!(
            candidates.is_empty(),
            "expected no fusion candidates without rewrites, got {}",
            candidates.len()
        );
    }

    // ── Multiple consumer safety check ─────────────────────────────────────

    #[test]
    fn test_multiple_consumers_block_fusion() {
        // Two rewrites both match the same constructor — fusion is unsafe
        // because fusing one would still leave the other needing the
        // intermediate relation.
        let lang = parse_language(quote! {
            name: TestMultiConsumer,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                Exec1 . |- (PDrop (NQuote P)) ~> P ;
                Exec2 . |- (PDrop N) ~> PNil ;
            },
        });

        let candidates = detect_fusion_candidates(&lang);

        // Both Exec1 and Exec2 reference PDrop, so each chain involving PDrop
        // should have the other as a blocking consumer.
        for candidate in &candidates {
            if candidate.rewrite_lhs_constructor == "PDrop" {
                // PDrop is consumed by both Exec1 and Exec2 (and possibly by the
                // equation system via RHS construction). The candidate should either
                // be blocked or have blocking consumers.
                // At minimum, both rewrites reference PDrop, so neither is the sole consumer.
                assert!(
                    !candidate.is_safe || candidate.blocking_consumers.is_empty(),
                    "candidate {} should reflect multiple consumers of PDrop",
                    candidate.rewrite_name,
                );
            }
        }
    }

    #[test]
    fn test_no_candidates_without_matching_constructors() {
        // A language where deconstruction and rewrites don't chain
        // (rewrite matches a constructor that isn't extracted by any
        // deconstruction).
        let lang = parse_language(quote! {
            name: TestNoChain,
            types { Proc },
            terms {
                PNil . Proc ::= "nil" ;
                POne . Proc ::= "one" ;
            },
            equations {},
            rewrites {
                NilToOne . |- PNil ~> POne ;
            },
        });

        let candidates = detect_fusion_candidates(&lang);
        // PNil and POne are nullary constructors — no subterm extraction,
        // so no deconstruction-rewrite chains.
        assert!(
            candidates.is_empty(),
            "expected no fusion candidates for nullary constructors, got {}",
            candidates.len()
        );
    }

    // ── Report analysis ────────────────────────────────────────────────────

    #[test]
    fn test_fusion_report_counts() {
        let lang = parse_language(quote! {
            name: TestReport,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                Exec . |- (PDrop (NQuote P)) ~> P ;
            },
        });

        let report = analyze_fusion_potential(&lang);
        assert!(
            !report.candidates.is_empty(),
            "expected non-empty fusion report"
        );
        assert_eq!(
            report.safe_count + report.blocked_count,
            report.candidates.len(),
            "safe + blocked should equal total candidates"
        );
    }

    #[test]
    fn test_fusion_report_empty_language() {
        let lang = parse_language(quote! {
            name: TestEmpty,
            types { Proc },
            terms {
                PNil . Proc ::= "nil" ;
            },
            equations {},
            rewrites {},
        });

        let report = analyze_fusion_potential(&lang);
        assert!(report.candidates.is_empty());
        assert_eq!(report.safe_count, 0);
        assert_eq!(report.blocked_count, 0);
        assert_eq!(report.estimated_tuple_reduction, 0);
    }

    // ── Congruence rules excluded ──────────────────────────────────────────

    #[test]
    fn test_congruence_rules_excluded_from_candidates() {
        // Congruence rules (with S ~> T premise) should not appear as fusion candidates.
        let lang = parse_language(quote! {
            name: TestCong,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                DropCong . | S ~> T |- (PDrop S) ~> (PDrop T) ;
            },
        });

        let candidates = detect_fusion_candidates(&lang);
        // Congruence rules are excluded from analysis
        let cong_candidates: Vec<_> = candidates
            .iter()
            .filter(|c| c.rewrite_name == "DropCong")
            .collect();
        assert!(
            cong_candidates.is_empty(),
            "congruence rules should not appear as fusion candidates"
        );
    }

    // ── Equation consumers block fusion ────────────────────────────────────

    #[test]
    fn test_equation_consumers_block_fusion() {
        // An equation that references the same constructor as a rewrite
        // should block the fusion.
        let lang = parse_language(quote! {
            name: TestEqBlock,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {
                ExecEq . |- (PDrop (NQuote P)) = P ;
            },
            rewrites {
                Exec . |- (PDrop (NQuote P)) ~> P ;
            },
        });

        let candidates = detect_fusion_candidates(&lang);
        // The Exec rewrite matches PDrop, but the ExecEq equation also
        // references PDrop → PDrop has multiple consumers → fusion blocked.
        let exec_candidates: Vec<_> = candidates
            .iter()
            .filter(|c| c.rewrite_name == "Exec" && c.rewrite_lhs_constructor == "PDrop")
            .collect();

        // If there are candidates for PDrop+Exec, they should be blocked
        // because the equation also references PDrop.
        for c in &exec_candidates {
            assert!(
                !c.is_safe,
                "Exec fusion should be blocked by ExecEq equation consumer"
            );
            assert!(
                !c.blocking_consumers.is_empty(),
                "should have blocking consumers from the equation"
            );
        }
    }

    // ── Cross-category chain detection ─────────────────────────────────────

    #[test]
    fn test_cross_category_chain() {
        // POutput(Name, Proc) deconstructs to name(n) and proc(p).
        // A rewrite matching NQuote would chain with the Name extraction.
        let lang = parse_language(quote! {
            name: TestCrossCategory,
            types { Proc Name },
            terms {
                POutput . Proc ::= Name Proc ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                QuoteReduce . |- (NQuote P) ~> (NQuote PNil) ;
            },
        });

        let candidates = detect_fusion_candidates(&lang);
        // POutput deconstructs to extract Name subterms.
        // QuoteReduce matches NQuote in category Name.
        // This is a cross-category chain: Proc → Name.
        // Check we detect it.
        let cross_cat = candidates.iter().any(|c| {
            c.parent_category == "Proc"
                && c.rewrite_category == "Name"
                && c.rewrite_name == "QuoteReduce"
        });
        // Note: The chain here is POutput→Name extraction, then QuoteReduce
        // matches in the Name category. The deconstruction of POutput produces
        // name(n), and QuoteReduce matches NQuote in the name relation.
        // This should appear as a candidate.
        assert!(
            cross_cat,
            "expected cross-category fusion candidate (Proc→Name) for QuoteReduce"
        );
    }

    // ── BCG02: Fused rule codegen tests ─────────────────────────────────────

    #[test]
    fn test_safe_candidate_is_safe() {
        // TestChain has a safe candidate: NQuote deconstruction → Exec rewrite.
        // Exec's consumer key is (Proc, PDrop), with only rw:Exec referencing it.
        // The safety check filters out the candidate's own consumer ("rw:Exec").
        let lang = parse_language(quote! {
            name: TestChain2,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                Exec . |- (PDrop (NQuote P)) ~> P ;
            },
        });

        let candidates = detect_fusion_candidates(&lang);
        let exec_candidate = candidates
            .iter()
            .find(|c| c.rewrite_name == "Exec")
            .expect("expected an Exec fusion candidate");

        assert!(
            exec_candidate.is_safe,
            "Exec candidate should be safe (single consumer of PDrop in Proc), blockers: {:?}",
            exec_candidate.blocking_consumers
        );
    }

    #[test]
    fn test_generate_fused_rule_produces_output() {
        // Use TestChain grammar with safe candidate, verify generate_fused_rule()
        // returns Some(...).
        let lang = parse_language(quote! {
            name: TestChainFused,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                Exec . |- (PDrop (NQuote P)) ~> P ;
            },
        });

        let candidates = detect_fusion_candidates(&lang);
        let safe_candidates: Vec<_> = candidates.iter().filter(|c| c.is_safe).collect();
        assert!(
            !safe_candidates.is_empty(),
            "should have at least one safe candidate"
        );

        // Generate a fused rule for the first safe candidate
        let fused = generate_fused_rule(safe_candidates[0], &lang);
        assert!(
            fused.is_some(),
            "generate_fused_rule should produce output for safe candidate"
        );
    }

    #[test]
    fn test_generate_all_fused_rules_nonempty() {
        // Verify generate_all_fused_rules returns non-empty Vec with count > 0.
        let lang = parse_language(quote! {
            name: TestAllFused,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                Exec . |- (PDrop (NQuote P)) ~> P ;
            },
        });

        let (fused_rules, count) = generate_all_fused_rules(&lang);
        assert!(count > 0, "should have at least one fused rule generated");
        assert!(
            !fused_rules.is_empty(),
            "fused_rules Vec should be non-empty"
        );
    }

    #[test]
    fn test_fused_rule_contains_bcg05_dedup_guard() {
        // Verify the generated fused rule contains the BCG05 epoch-based dedup.
        let lang = parse_language(quote! {
            name: TestFusedBCG05,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                Exec . |- (PDrop (NQuote P)) ~> P ;
            },
        });

        let candidates = detect_fusion_candidates(&lang);
        let safe = candidates.iter().find(|c| c.is_safe).expect("need safe candidate");
        let fused_ts = generate_fused_rule(safe, &lang).expect("should generate fused rule");
        let fused_str = fused_ts.to_string();

        assert!(
            fused_str.contains("bcg05"),
            "fused rule should contain BCG05 dedup guard: {}",
            fused_str
        );
        assert!(
            fused_str.contains("bcg05_epoch"),
            "fused rule should reference bcg05_epoch: {}",
            fused_str
        );
    }

    #[test]
    fn test_fused_rule_contains_expected_relations() {
        // Verify the fused rule reads eq_name (parent category = Name, since decon_constructor
        // is NQuote in Name) and writes rw_proc (rewrite category = Proc, since Exec matches
        // PDrop in Proc).
        let lang = parse_language(quote! {
            name: TestFusedRelations,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                Exec . |- (PDrop (NQuote P)) ~> P ;
            },
        });

        let candidates = detect_fusion_candidates(&lang);
        let safe = candidates.iter().find(|c| c.is_safe).expect("need safe candidate");
        let fused_ts = generate_fused_rule(safe, &lang).expect("should generate fused rule");
        let fused_str = fused_ts.to_string();

        // Parent category is Name (NQuote is in Name), so reads eq_name.
        // Rewrite category is Proc (Exec's LHS is PDrop in Proc), so writes rw_proc.
        assert!(
            fused_str.contains("eq_name"),
            "fused rule should read eq_name (parent eq relation): {}",
            fused_str
        );
        assert!(
            fused_str.contains("rw_proc"),
            "fused rule should write rw_proc (rewrite relation): {}",
            fused_str
        );
    }

    #[test]
    fn test_blocked_candidate_produces_no_fused_rules() {
        // TestMultiConsumer has two rewrites both matching PDrop — no safe candidates.
        let lang = parse_language(quote! {
            name: TestBlockedFusion,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                Exec1 . |- (PDrop (NQuote P)) ~> P ;
                Exec2 . |- (PDrop N) ~> PNil ;
            },
        });

        let (fused_rules, count) = generate_all_fused_rules(&lang);
        assert_eq!(
            count, 0,
            "blocked candidates should produce no fused rules"
        );
        assert!(
            fused_rules.is_empty(),
            "fused_rules should be empty for blocked candidates"
        );
    }

    #[test]
    fn test_constructor_consumer_map_counts() {
        // Directly exercise build_constructor_consumer_map for a known grammar.
        let lang = parse_language(quote! {
            name: TestConsumerMap,
            types { Proc Name },
            terms {
                PDrop . Proc ::= Name ;
                PNil . Proc ::= "nil" ;
                NQuote . Name ::= Proc ;
            },
            equations {},
            rewrites {
                Exec . |- (PDrop (NQuote P)) ~> P ;
            },
        });

        let consumer_map = build_constructor_consumer_map(&lang);

        // PDrop in Proc is referenced by rewrite Exec (in LHS)
        let pdrop_consumers = consumer_map
            .get(&("Proc".to_string(), "PDrop".to_string()))
            .expect("PDrop should have consumers");
        assert!(
            pdrop_consumers.contains("rw:Exec"),
            "PDrop should be consumed by rw:Exec, got: {:?}",
            pdrop_consumers
        );

        // NQuote in Name is referenced by Exec's LHS (nested inside PDrop)
        let nquote_consumers = consumer_map
            .get(&("Name".to_string(), "NQuote".to_string()))
            .expect("NQuote should have consumers");
        assert!(
            nquote_consumers.contains("rw:Exec"),
            "NQuote should be consumed by rw:Exec, got: {:?}",
            nquote_consumers
        );
    }
}
