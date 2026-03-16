//! Equation rules generation for Ascent Datalog.
//!
//! Generates:
//! - Reflexivity rules (eq_cat(t, t) for all t)
//! - Equality congruence rules (if args equal, constructed terms equal)
//! - User-defined equation rules

use super::common::{
    generate_tls_pool_iter, in_cat_filter, relation_names, CategoryFilter, PoolArm,
};
use crate::ast::grammar::{GrammarItem, GrammarRule};
use crate::ast::language::LanguageDef;
use crate::logic::bloom_filter::BloomFilter;
use crate::logic::rules as unified_rules;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use syn::Ident;

/// Main entry point: Generate all equation rules.
///
/// This includes:
/// 1. Reflexivity rules for all categories
/// 2. Demand-driven equality congruence for existing terms
/// 3. User-defined equations
///
/// When `cat_filter` is `Some`, only generates rules for categories in the filter set.
/// When `analysis` is `Some`, dead constructors are skipped in congruence rules (Sprint 1 DCE).
/// When `subsumed_equations` is non-empty, subsumed equations are eliminated (Sprint A N10 DCE).
/// When `cancellation_equations` is non-empty, cancellation pair equations are suppressed from
/// eqrel generation (they would cause non-convergence via symmetric expansion).
///
/// ## ART06 Extended Demand Filtering
///
/// The `demanded` set specifies categories referenced by at least one rule.
/// Reflexivity and congruence rules for categories NOT in the demanded set are skipped.
///
/// ## BCG06 Stratum-Ordered Rule Generation
///
/// When `strat_info` is provided, congruence groups are sorted by dependency depth
/// (fewer eq_* reads first) and user equations are sorted by stratum index.
pub fn generate_equation_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
    analysis: Option<&mettail_prattail::PipelineAnalysis>,
    subsumed_equations: &std::collections::HashSet<usize>,
    cancellation_equations: &std::collections::HashSet<usize>,
    emit_diagnostics: bool,
    demanded: &BTreeSet<String>,
    strat_info: Option<&StratificationInfo>,
) -> TokenStream {
    let mut rules = Vec::new();

    // 1. Add reflexivity for eq relations (ART06: skip non-demanded categories)
    rules.extend(generate_reflexivity_rules(language, cat_filter, demanded));

    // 2. Add demand-driven congruence rules for all constructors
    // These only equate terms that already exist, not synthesize new ones
    // (ART06: skip non-demanded categories; BCG06: sort by dependency depth)
    rules.extend(generate_congruence_rules(language, cat_filter, analysis, emit_diagnostics, demanded, strat_info));

    // 3. Generate user-defined equation rules using unified approach,
    //    filtering out subsumed equations (Sprint A N10 DCE) and
    //    cancellation pair equations (would cause non-convergence)
    //    (ART06: skip rules targeting non-demanded categories)
    //    (BCG06: sort by stratum index for faster convergence)
    rules.extend(unified_rules::generate_equation_rules(language, cat_filter, subsumed_equations, cancellation_equations, demanded, strat_info));

    quote! {
        #(#rules)*
    }
}

/// Generate only reflexivity rules (public for pre-stratum use).
///
/// The pre-stratum needs reflexivity to initialize the eq relations but does not
/// need congruence or user-defined equation rules.
pub fn generate_equation_rules_reflexivity_only(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
    demanded: &BTreeSet<String>,
) -> TokenStream {
    let rules = generate_reflexivity_rules(language, cat_filter, demanded);
    quote! { #(#rules)* }
}

/// Generate reflexivity rules: eq_cat(t, t) for all t in cat
///
/// ART06: Skips categories not in the `demanded` set — their eq_cat relations
/// are not declared, so reflexivity rules for them would be dead code.
fn generate_reflexivity_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
    demanded: &BTreeSet<String>,
) -> Vec<TokenStream> {
    language
        .types
        .iter()
        .filter(|lang_type| in_cat_filter(&lang_type.name, cat_filter))
        .filter(|lang_type| demanded.contains(&lang_type.name.to_string()))
        .map(|lang_type| {
            let rn = relation_names(&lang_type.name);
            let cat_lower = &rn.cat_lower;
            let eq_rel = &rn.eq_rel;
            quote! {
                #eq_rel(t.clone(), t.clone()) <-- #cat_lower(t);
            }
        })
        .collect()
}

/// B-CG03: Compute the set of "equation-active" constructor labels.
///
/// A constructor is equation-active if:
/// 1. It appears directly in any equation LHS or RHS pattern, OR
/// 2. It is transitively reachable: if constructor A has a field of category C,
///    and any equation-active constructor belongs to category C, then A is also
///    equation-active (because equation-produced terms of category C could be
///    subterms of A, making A's congruence rule useful for propagation).
///
/// Constructors that are NOT equation-active can have their congruence match
/// arms pruned, since no non-trivial equalities will ever flow through them.
///
/// This analysis is conservative: if in doubt, constructors are included.
fn compute_equation_active_constructors(language: &LanguageDef) -> HashSet<String> {
    // Step 1: Collect constructors directly referenced in equation patterns.
    let mut directly_active: HashSet<String> = HashSet::new();
    for eq in &language.equations {
        eq.left.collect_constructor_labels(&mut directly_active);
        eq.right.collect_constructor_labels(&mut directly_active);
    }

    // If no equations exist, ALL constructors are trivially equation-inert.
    // Return empty set; callers should skip congruence pruning (nothing to prune).
    if language.equations.is_empty() {
        return HashSet::new();
    }

    // Step 2: Compute "equation-active categories" — categories that contain at
    // least one directly-active constructor.
    let mut active_categories: HashSet<String> = HashSet::new();
    for rule in &language.terms {
        if directly_active.contains(&rule.label.to_string()) {
            active_categories.insert(rule.category.to_string());
        }
    }

    // Step 3: Transitive closure over the constructor→field-category graph.
    // If constructor C has a field of an active category, C's result category
    // becomes active too, and C itself becomes equation-active.
    //
    // Iterate until no new categories are activated (fixpoint).
    let mut equation_active: HashSet<String> = directly_active;
    loop {
        let mut new_active_categories: HashSet<String> = HashSet::new();

        for rule in &language.terms {
            // Skip already-active constructors
            if equation_active.contains(&rule.label.to_string()) {
                continue;
            }

            // Check if any non-terminal field belongs to an active category
            let has_active_field = rule.items.iter().any(|item| {
                if let GrammarItem::NonTerminal(cat) = item {
                    active_categories.contains(&cat.to_string())
                } else {
                    false
                }
            });

            if has_active_field {
                equation_active.insert(rule.label.to_string());
                let result_cat = rule.category.to_string();
                if !active_categories.contains(&result_cat) {
                    new_active_categories.insert(result_cat);
                }
            }
        }

        if new_active_categories.is_empty() {
            break;
        }

        active_categories.extend(new_active_categories);
    }

    equation_active
}

/// Generate demand-driven congruence rules for equality.
///
/// Groups constructors by `(result_category, field_types_tuple)` and generates
/// one consolidated rule per group using `match (s, t)` to extract fields.
///
/// Uses thread-local Vec pools for zero-allocation iteration.
///
/// Before: one rule per constructor
/// After: one rule per unique (category, field_types) signature
///
/// B-CG03: Constructors that are equation-inert (never participate in equations
/// directly or transitively via field categories) have their congruence match
/// arms pruned, reducing generated code size and runtime overhead.
///
/// For terms that already exist: if their args are equal, then the terms are equal.
/// This is demand-driven and avoids O(N^2) term explosion.
fn generate_congruence_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
    analysis: Option<&mettail_prattail::PipelineAnalysis>,
    emit_diagnostics: bool,
    demanded: &BTreeSet<String>,
    strat_info: Option<&StratificationInfo>,
) -> Vec<TokenStream> {
    // B-CG03: Compute equation-active constructors for selective pruning.
    // Only constructors that participate in equations (directly or transitively
    // via field categories) need congruence match arms.
    let equation_active = compute_equation_active_constructors(language);
    // If the language has equations but the active set is computed, use it for pruning.
    // If the language has NO equations, equation_active is empty, and we should skip
    // ALL congruence rules (no equations means no non-trivial equalities to propagate).
    let has_equations = !language.equations.is_empty();
    let mut bcg03_pruned_count: usize = 0;

    // Group constructors by (category, ordered field types)
    // Key: (category_str, vec of field_type_str)
    let mut groups: BTreeMap<(String, Vec<String>), Vec<&GrammarRule>> = BTreeMap::new();

    let var_str = "Var";
    let int_str = "Integer";

    for grammar_rule in &language.terms {
        // Skip categories not in the filter
        if !in_cat_filter(&grammar_rule.category, cat_filter) {
            continue;
        }

        // ART06: Skip categories not in the demanded set — their eq_cat relations
        // are not declared, so congruence rules for them would be dead code.
        if !demanded.contains(&grammar_rule.category.to_string()) {
            continue;
        }

        // Sprint 1 DCE: skip dead constructors — their congruence rules can never fire
        if let Some(ref a) = analysis {
            if a.dead_rule_labels.contains(&grammar_rule.label.to_string()) {
                continue;
            }
        }

        // B-CG03: skip equation-inert constructors — their congruence rules
        // can never produce useful (non-reflexive) equalities. Only applies
        // when the language has equations (otherwise there are no congruence
        // rules to generate at all, since no equalities flow through them).
        if has_equations && !equation_active.contains(&grammar_rule.label.to_string()) {
            bcg03_pruned_count += 1;
            continue;
        }

        // Skip binders (alpha-equivalence is complex)
        if !grammar_rule.bindings.is_empty() {
            continue;
        }

        // Skip collections (built-in equality)
        if grammar_rule
            .items
            .iter()
            .any(|item| matches!(item, GrammarItem::Collection { .. }))
        {
            continue;
        }

        // Collect non-terminal argument categories
        let arg_cats: Vec<String> = grammar_rule
            .items
            .iter()
            .filter_map(|item| {
                if let GrammarItem::NonTerminal(cat) = item {
                    Some(cat.to_string())
                } else {
                    None
                }
            })
            .collect();

        if arg_cats.is_empty() {
            continue; // Nullary constructor
        }

        // Skip constructors with Var or Integer arguments
        if arg_cats.iter().any(|c| c == var_str || c == int_str) {
            continue;
        }

        let key = (grammar_rule.category.to_string(), arg_cats);
        groups.entry(key).or_default().push(grammar_rule);
    }

    // A-RT04: Build a per-category bloom filter of constructor labels that participate
    // in equality congruence groups. Used at codegen time for fast lookup, and the
    // constructor set is used to generate discriminant pre-check guards that eliminate
    // cross-constructor pairs from the O(|cat|²) scan before the pool match executes.
    let mut per_category_bloom: BTreeMap<String, BloomFilter> = BTreeMap::new();
    for ((cat_str, _), constructors) in &groups {
        let bloom = per_category_bloom.entry(cat_str.clone())
            .or_insert_with(|| BloomFilter::new(constructors.len().max(1)));
        for rule in constructors {
            bloom.insert_str(&rule.label.to_string());
        }
    }

    // BCG06: Sort congruence groups by dependency depth for faster convergence.
    // Groups reading fewer distinct eq_* relations are placed first, so their results
    // are available sooner in semi-naive evaluation. This is the intra-struct rule
    // ordering variant of BCG06 (no additional Ascent structs needed).
    let sorted_group_keys: Vec<(String, Vec<String>)> = {
        let mut keys: Vec<_> = groups.keys().cloned().collect();
        if strat_info.is_some() {
            keys.sort_by(|(cat_a, fields_a), (cat_b, fields_b)| {
                // Dependency depth = number of distinct eq_* relations read.
                // A congruence rule for (Cat, [F1, F2]) reads eq_F1 and eq_F2.
                // Fewer reads = fewer dependencies = should come first.
                let depth_a = fields_a.iter().collect::<BTreeSet<_>>().len();
                let depth_b = fields_b.iter().collect::<BTreeSet<_>>().len();
                depth_a.cmp(&depth_b)
                    // Break ties by category name for stability
                    .then_with(|| cat_a.cmp(cat_b))
                    .then_with(|| fields_a.cmp(fields_b))
            });
        }
        keys
    };

    // Generate one consolidated rule per group.
    // Sprint 3: sort constructors within each group by WFST weight (lower = more frequent first)
    // for better branch prediction in the match arms.
    let mut rules = Vec::with_capacity(groups.len());
    let mut art04_eq_guarded_count: usize = 0;
    for (pool_counter, key) in sorted_group_keys.iter().enumerate() {
        let (cat_str, field_type_strs) = key;
        let constructors = &groups[key];
        // Weight-sorted constructors: most frequent (lowest weight) first
        let mut sorted_constructors: Vec<&&GrammarRule> = constructors.iter().collect();
        if let Some(ref a) = analysis {
            sorted_constructors.sort_by(|a_rule, b_rule| {
                let a_weight = a.constructor_weights
                    .get(&a_rule.label.to_string())
                    .copied()
                    .unwrap_or(f64::INFINITY);
                let b_weight = a.constructor_weights
                    .get(&b_rule.label.to_string())
                    .copied()
                    .unwrap_or(f64::INFINITY);
                a_weight.total_cmp(&b_weight)
            });
        }
        let constructors = &sorted_constructors;
        let category = format_ident!("{}", cat_str);
        let rn = relation_names(&category);
        let cat_rel = &rn.cat_lower;
        let eq_rel = &rn.eq_rel;

        let arity = field_type_strs.len();

        // Field names for the for-binding
        let s_fields: Vec<Ident> = (0..arity).map(|i| format_ident!("s_f{}", i)).collect();
        let t_fields: Vec<Ident> = (0..arity).map(|i| format_ident!("t_f{}", i)).collect();

        // Build pool arms for (s, t) extraction
        let pool_arms: Vec<PoolArm> = constructors
            .iter()
            .map(|rule| {
                let label = &rule.label;
                let s_pat_fields: Vec<Ident> =
                    (0..arity).map(|i| format_ident!("sf{}", i)).collect();
                let t_pat_fields: Vec<Ident> =
                    (0..arity).map(|i| format_ident!("tf{}", i)).collect();

                // Push a tuple of (s_f0, s_f1, ..., t_f0, t_f1, ...)
                let push_fields: Vec<TokenStream> = s_pat_fields
                    .iter()
                    .chain(t_pat_fields.iter())
                    .map(|f| quote! { #f.as_ref().clone() })
                    .collect();

                PoolArm {
                    pattern: quote! {
                        (#category::#label(#(#s_pat_fields),*), #category::#label(#(#t_pat_fields),*))
                    },
                    pushes: vec![quote! { buf.push((#(#push_fields),*)); }],
                }
            })
            .collect();

        // For-binding: (s_f0, s_f1, ..., t_f0, t_f1, ...)
        let for_bindings: Vec<&Ident> = s_fields.iter().chain(t_fields.iter()).collect();

        // Sprint 4: Equality checks for corresponding field pairs, ordered by
        // category diversity (most diverse first → fail-fast in semi-naive evaluation).
        //
        // Higher category weight (from WFST analysis) → more diverse → check first.
        // Rationale: categories with many constructors produce many distinct terms,
        // making equality checks more likely to fail early, pruning the join.
        //
        // Note: The O(|cat|²) cross-product from `cat(s), cat(t)` is inherent in
        // Ascent's evaluation model — the pool filters same-constructor pairs AFTER
        // the cross-product is formed. This reordering optimizes the constant factor
        // by failing non-matching pairs faster in the eq_checks.
        let mut eq_check_pairs: Vec<(usize, String)> = field_type_strs
            .iter()
            .enumerate()
            .map(|(i, ft_str)| (i, ft_str.clone()))
            .collect();

        // Sort by category weight descending (highest weight = most diverse = check first)
        if let Some(ref a) = analysis {
            eq_check_pairs.sort_by(|(_, ft_a), (_, ft_b)| {
                let w_a = a.category_weights
                    .get(ft_a)
                    .copied()
                    .unwrap_or(0.0);
                let w_b = a.category_weights
                    .get(ft_b)
                    .copied()
                    .unwrap_or(0.0);
                // Higher weight first (descending) → more diverse → fail-fast
                w_b.total_cmp(&w_a)
            });
        }

        let eq_checks: Vec<TokenStream> = eq_check_pairs
            .iter()
            .map(|(i, ft_str)| {
                let eq_arg_rel = format_ident!("eq_{}", ft_str.to_lowercase());
                let sf = &s_fields[*i];
                let tf = &t_fields[*i];
                quote! { #eq_arg_rel(#sf, #tf) }
            })
            .collect();

        // TLS pool with unique name per group
        let pool_name = format_ident!("POOL_{}_EQ_CONG_{}", cat_str.to_uppercase(), pool_counter);

        // Element type is the tuple of all s_fields and t_fields
        let field_types: Vec<TokenStream> = field_type_strs
            .iter()
            .map(|ft_str| {
                let ft = format_ident!("{}", ft_str);
                quote! { #ft }
            })
            .collect();
        // Double the field types: s fields then t fields
        let all_field_types: Vec<&TokenStream> =
            field_types.iter().chain(field_types.iter()).collect();
        let elem_type = quote! { (#(#all_field_types),*) };
        let match_expr = quote! { (s, t) };
        let for_iter = generate_tls_pool_iter(&pool_name, &elem_type, &match_expr, &pool_arms);

        // A-RT04: Bloom filter pre-check for equality congruence.
        //
        // The pool only matches same-constructor pairs: (Cat::A(..), Cat::A(..)).
        // When s and t have different discriminants, the pool returns empty and
        // the `for` yields zero iterations. Adding a discriminant equality check
        // before the pool eliminates all cross-constructor pairs from the
        // O(|cat|²) scan with a single integer comparison.
        //
        // Additionally, for groups with fewer constructors than the total category
        // size, we add a `matches!()` guard to skip constructors not in the group.
        // The bloom filter is consulted at codegen time to verify which constructors
        // participate, ensuring conservativeness (no false negatives).
        //
        // Combined guards:
        // 1. `std::mem::discriminant(s) == std::mem::discriminant(t)` — O(1) integer cmp
        // 2. `matches!(s, Cat::A(..) | Cat::B(..) | ...)` — discriminant range check
        //
        // Guard (1) is always profitable: it prunes O(|cat|²) → O(|cat|) worst case.
        // Guard (2) is profitable when the group has fewer constructors than the
        // total for the category: it filters out non-participating constructors.

        // Collect the constructor labels in this group for the matches!() guard.
        // The bloom filter ensures we include every constructor that could participate.
        let group_constructor_labels: Vec<&Ident> = constructors
            .iter()
            .map(|rule| &rule.label)
            .collect();

        // Count total constructors in this category to decide if the matches!() guard
        // adds value beyond the discriminant equality check.
        let total_cat_constructors = language.terms.iter()
            .filter(|r| r.category.to_string() == *cat_str)
            .count();

        // Build the pre-check guard(s).
        let discriminant_guard = quote! {
            if std::mem::discriminant(s) == std::mem::discriminant(t)
        };

        // Only add the matches!() guard if the group covers a strict subset of
        // the category's constructors. When the group covers all constructors,
        // the discriminant equality check is sufficient.
        let use_matches_guard = group_constructor_labels.len() < total_cat_constructors;
        let matches_guard = if use_matches_guard {
            // Generate: if matches!(s, Cat::A(..) | Cat::B(..) | ...)
            let match_patterns: Vec<TokenStream> = group_constructor_labels
                .iter()
                .map(|label| quote! { #category::#label(..) })
                .collect();
            quote! { if matches!(s, #(#match_patterns)|*) }
        } else {
            quote! {}
        };

        art04_eq_guarded_count += 1;

        if use_matches_guard {
            rules.push(quote! {
                #eq_rel(s.clone(), t.clone()) <--
                    #cat_rel(s),
                    #cat_rel(t),
                    #discriminant_guard,
                    #matches_guard,
                    for (#(#for_bindings),*) in #for_iter,
                    #(#eq_checks),*;
            });
        } else {
            rules.push(quote! {
                #eq_rel(s.clone(), t.clone()) <--
                    #cat_rel(s),
                    #cat_rel(t),
                    #discriminant_guard,
                    for (#(#for_bindings),*) in #for_iter,
                    #(#eq_checks),*;
            });
        }
    }

    // B-CG03: Emit lint diagnostic if any constructors were pruned.
    if emit_diagnostics && bcg03_pruned_count > 0 {
        mettail_prattail::lint::emit_diagnostic(
            &mettail_prattail::lint::LintDiagnostic {
                id: "G36",
                name: "equation-inert-congruence-pruned",
                severity: mettail_prattail::lint::LintSeverity::Note,
                category: None,
                rule: None,
                message: format!(
                    "{} equation-inert constructor(s) pruned from congruence rules (B-CG03) \
                     — {} equation-active constructor(s) retained",
                    bcg03_pruned_count,
                    equation_active.len(),
                ),
                hint: Some(
                    "equation-inert constructors never participate in equations \
                     (directly or transitively); their congruence match arms are unnecessary"
                        .to_string(),
                ),
                grammar_name: Some(language.name.to_string()),
                source_location: None,
            },
        );
    }

    // A-RT04: Emit lint diagnostic for bloom filter / discriminant pre-check optimization.
    if emit_diagnostics && art04_eq_guarded_count > 0 {
        let bloom_summary: Vec<String> = per_category_bloom.iter()
            .map(|(cat, bloom)| format!("{}: {} bits set", cat, bloom.occupancy()))
            .collect();
        mettail_prattail::lint::emit_diagnostic(
            &mettail_prattail::lint::LintDiagnostic {
                id: "G37",
                name: "bloom-filter-eq-congruence-guard",
                severity: mettail_prattail::lint::LintSeverity::Note,
                category: None,
                rule: None,
                message: format!(
                    "{} equality congruence group(s) guarded by discriminant pre-check (A-RT04) \
                     — eliminates O(|cat|²) cross-constructor pairs before pool evaluation",
                    art04_eq_guarded_count,
                ),
                hint: Some(format!(
                    "per-category bloom filter occupancy: [{}]",
                    bloom_summary.join(", "),
                )),
                grammar_name: Some(language.name.to_string()),
                source_location: None,
            },
        );
    }

    rules
}

// =============================================================================
// BCG06: Stratified Equation Evaluation — SCC-Based Analysis
// =============================================================================

/// Classification of an equation rule's role in the evaluation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EqRuleKind {
    /// Reflexivity: `eq_cat(t, t) <-- cat(t)`
    /// No equation dependencies — depends only on category population.
    Reflexivity,
    /// Congruence: `eq_cat(s, t) <-- cat(s), cat(t), ..., eq_field_cat(sf, tf)`
    /// Depends on `eq_*` relations (produced by reflexivity and other congruence rules).
    Congruence,
    /// User-defined equation: matches patterns, may read `cat` and `eq_*` relations.
    UserDefined,
}

impl std::fmt::Display for EqRuleKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EqRuleKind::Reflexivity => write!(f, "reflexivity"),
            EqRuleKind::Congruence => write!(f, "congruence"),
            EqRuleKind::UserDefined => write!(f, "user-defined"),
        }
    }
}

/// A classified equation rule with its dependency information.
#[derive(Debug, Clone)]
pub struct ClassifiedEqRule {
    /// Unique identifier for this rule within the analysis.
    pub id: usize,
    /// What kind of equation rule this is.
    pub kind: EqRuleKind,
    /// Human-readable label (e.g., "reflexivity:Proc", "congruence:Proc(Name,Name)",
    /// "user:ScopeExtrusion").
    pub label: String,
    /// Category this rule writes to (the `eq_cat` relation).
    pub writes_category: String,
    /// Categories this rule reads from via `eq_*` relations.
    /// Empty for reflexivity (reads only `cat`, not `eq_*`).
    pub reads_eq_categories: BTreeSet<String>,
}

/// A stratum: a group of equation rules that can be evaluated together.
///
/// Rules within the same stratum may have mutual dependencies (SCC).
/// Strata are ordered: stratum i must complete before stratum i+1 begins.
#[derive(Debug, Clone)]
pub struct Stratum {
    /// Stratum index (0-based, lower = evaluated first).
    pub index: usize,
    /// The classified rules in this stratum.
    pub rules: Vec<ClassifiedEqRule>,
}

/// BCG06: Stratification analysis result.
///
/// Captures the SCC-based stratification of equation rules into independent
/// evaluation strata. Reflexivity rules (no `eq_*` dependencies) form the
/// lowest stratum, congruence rules form the next, and user-defined equations
/// are placed according to their dependency structure.
///
/// This analysis informs the diagnostic/lint system about the equation rule
/// structure. The actual Ascent evaluation order is controlled by Ascent's
/// own semi-naive stratification, so this primarily serves as a compile-time
/// diagnostic overlay.
#[derive(Debug, Clone)]
pub struct StratificationInfo {
    /// Total number of equation rules analyzed.
    pub total_rules: usize,
    /// Number of reflexivity rules.
    pub reflexivity_count: usize,
    /// Number of congruence rules.
    pub congruence_count: usize,
    /// Number of user-defined equation rules.
    pub user_defined_count: usize,
    /// The strata, ordered from lowest (fewest dependencies) to highest.
    pub strata: Vec<Stratum>,
    /// Number of SCCs found in the dependency graph.
    pub scc_count: usize,
}

impl std::fmt::Display for StratificationInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} equation rule(s) stratified into {} stratum/strata ({} SCC(s)): \
             {} reflexivity, {} congruence, {} user-defined",
            self.total_rules,
            self.strata.len(),
            self.scc_count,
            self.reflexivity_count,
            self.congruence_count,
            self.user_defined_count,
        )
    }
}

/// BCG06: Perform SCC-based stratification of equation rules.
///
/// Classifies each equation rule as reflexivity, congruence, or user-defined,
/// builds a dependency graph over the `eq_*` relations they read/write, computes
/// SCCs (strongly connected components), and returns the rules grouped by stratum.
///
/// # Dependency model
///
/// - **Reflexivity** (`eq_cat(t, t) <-- cat(t)`): Reads `cat`, writes `eq_cat`.
///   No dependency on any `eq_*` relation.
/// - **Congruence** (`eq_cat(s, t) <-- cat(s), cat(t), ..., eq_field_cat(sf, tf)`):
///   Reads `eq_field_cat` for each field category, writes `eq_cat`.
///   Depends on reflexivity (and possibly other congruence rules if field categories
///   have their own congruence rules).
/// - **User-defined** equations: Read `cat` (for pattern matching), may implicitly
///   read `eq_*` if the equation's LHS/RHS patterns involve categories with equation
///   rules. Writes `eq_cat` for the equation's result category.
///
/// # SCC computation
///
/// Uses Tarjan's algorithm to find SCCs in the dependency graph. Each SCC becomes
/// one stratum. Strata are topologically sorted so that a stratum's dependencies
/// are satisfied by earlier strata.
///
/// # Arguments
///
/// * `language` - The language definition containing equations, types, and terms.
///
/// # Returns
///
/// A `StratificationInfo` capturing the full analysis result.
pub fn stratify_equation_rules(language: &LanguageDef) -> StratificationInfo {
    let mut classified: Vec<ClassifiedEqRule> = Vec::new();
    let mut next_id: usize = 0;

    // --- Phase 1: Classify all equation rules ---

    // 1a. Reflexivity rules: one per category
    for lang_type in &language.types {
        let cat_str = lang_type.name.to_string();
        classified.push(ClassifiedEqRule {
            id: next_id,
            kind: EqRuleKind::Reflexivity,
            label: format!("reflexivity:{}", cat_str),
            writes_category: cat_str,
            reads_eq_categories: BTreeSet::new(), // No eq_* dependencies
        });
        next_id += 1;
    }

    // 1b. Congruence rules: one per (category, field_types) group
    //     (mirrors the grouping logic in generate_congruence_rules)
    let mut congruence_groups: BTreeMap<(String, Vec<String>), Vec<String>> = BTreeMap::new();
    for grammar_rule in &language.terms {
        // Skip binders, collections, nullary constructors, Var/Integer args
        if !grammar_rule.bindings.is_empty() {
            continue;
        }
        if grammar_rule
            .items
            .iter()
            .any(|item| matches!(item, GrammarItem::Collection { .. }))
        {
            continue;
        }
        let arg_cats: Vec<String> = grammar_rule
            .items
            .iter()
            .filter_map(|item| {
                if let GrammarItem::NonTerminal(cat) = item {
                    Some(cat.to_string())
                } else {
                    None
                }
            })
            .collect();
        if arg_cats.is_empty() {
            continue;
        }
        if arg_cats.iter().any(|c| c == "Var" || c == "Integer") {
            continue;
        }
        let key = (grammar_rule.category.to_string(), arg_cats);
        congruence_groups
            .entry(key)
            .or_default()
            .push(grammar_rule.label.to_string());
    }

    for ((cat_str, field_cats), constructor_labels) in &congruence_groups {
        let reads: BTreeSet<String> = field_cats.iter().cloned().collect();
        let constructors_summary = constructor_labels.join(",");
        classified.push(ClassifiedEqRule {
            id: next_id,
            kind: EqRuleKind::Congruence,
            label: format!("congruence:{}({})", cat_str, constructors_summary),
            writes_category: cat_str.clone(),
            reads_eq_categories: reads,
        });
        next_id += 1;
    }

    // 1c. User-defined equations
    for eq in &language.equations {
        let cat = eq
            .left
            .category(language)
            .or_else(|| eq.right.category(language));
        let writes_cat = cat
            .map(|c| c.to_string())
            .unwrap_or_else(|| "unknown".to_string());

        // Determine which eq_* relations this equation reads.
        // A user equation reads eq_cat for categories of constructors it pattern-matches.
        // Conservative: collect all categories referenced in both LHS and RHS patterns.
        let mut referenced_cats: BTreeSet<String> = BTreeSet::new();
        collect_pattern_eq_deps(&eq.left, language, &mut referenced_cats);
        collect_pattern_eq_deps(&eq.right, language, &mut referenced_cats);

        classified.push(ClassifiedEqRule {
            id: next_id,
            kind: EqRuleKind::UserDefined,
            label: format!("user:{}", eq.name),
            writes_category: writes_cat,
            reads_eq_categories: referenced_cats,
        });
        next_id += 1;
    }

    let total_rules = classified.len();
    let reflexivity_count = classified
        .iter()
        .filter(|r| r.kind == EqRuleKind::Reflexivity)
        .count();
    let congruence_count = classified
        .iter()
        .filter(|r| r.kind == EqRuleKind::Congruence)
        .count();
    let user_defined_count = classified
        .iter()
        .filter(|r| r.kind == EqRuleKind::UserDefined)
        .count();

    // --- Phase 2: Build dependency graph ---
    //
    // Edge (i -> j) means rule i depends on rule j (i reads eq_cat that j writes).
    // We need to find which rules produce eq_cat facts for category C (writers of C),
    // then draw edges from each reader of eq_C to those writers.

    // Map from category -> set of rule IDs that write eq_cat for that category
    let mut writers_by_cat: HashMap<String, Vec<usize>> = HashMap::new();
    for rule in &classified {
        writers_by_cat
            .entry(rule.writes_category.clone())
            .or_default()
            .push(rule.id);
    }

    // Build adjacency list: adj[i] = set of rule IDs that rule i depends on
    let n = classified.len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for rule in &classified {
        for read_cat in &rule.reads_eq_categories {
            if let Some(writers) = writers_by_cat.get(read_cat) {
                for &writer_id in writers {
                    // Don't add self-loops (a rule depending on itself is implicit in SCCs)
                    if writer_id != rule.id {
                        adj[rule.id].push(writer_id);
                    }
                }
            }
        }
    }

    // --- Phase 3: Compute SCCs using Tarjan's algorithm ---
    let sccs = tarjan_scc(n, &adj);
    let scc_count = sccs.len();

    // --- Phase 4: Topological sort of SCCs ---
    //
    // SCCs are already returned in reverse topological order by Tarjan's algorithm
    // (leaf SCCs first). We want strata ordered so that dependencies come first,
    // which is exactly the reverse-topological order.

    // Build strata from SCCs (in reverse topological order = dependency-first order)
    let mut strata: Vec<Stratum> = Vec::with_capacity(sccs.len());
    for (stratum_idx, scc) in sccs.iter().enumerate() {
        let rules: Vec<ClassifiedEqRule> = scc
            .iter()
            .map(|&rule_id| classified[rule_id].clone())
            .collect();
        strata.push(Stratum {
            index: stratum_idx,
            rules,
        });
    }

    StratificationInfo {
        total_rules,
        reflexivity_count,
        congruence_count,
        user_defined_count,
        strata,
        scc_count,
    }
}

/// Collect category names from a pattern that would create `eq_*` dependencies.
///
/// A user equation that pattern-matches a constructor of category C implicitly
/// depends on `eq_C` (because congruence rules for C feed into the equation).
/// This is conservative: we collect all categories mentioned in the pattern.
fn collect_pattern_eq_deps(
    pattern: &crate::ast::pattern::Pattern,
    language: &LanguageDef,
    deps: &mut BTreeSet<String>,
) {
    use crate::ast::pattern::{Pattern, PatternTerm};
    match pattern {
        Pattern::Term(pt) => match pt {
            PatternTerm::Var(_) => {},
            PatternTerm::Apply { constructor, args } => {
                if let Some(cat) = language.category_of_constructor(constructor) {
                    deps.insert(cat.to_string());
                }
                // Also collect field categories (constructor's field types)
                if let Some(rule) = language.get_constructor(constructor) {
                    for item in &rule.items {
                        if let GrammarItem::NonTerminal(field_cat) = item {
                            deps.insert(field_cat.to_string());
                        }
                    }
                }
                for arg in args {
                    collect_pattern_eq_deps(arg, language, deps);
                }
            },
            PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
                collect_pattern_eq_deps(body, language, deps);
            },
            PatternTerm::Subst { term, replacement, .. } => {
                collect_pattern_eq_deps(term, language, deps);
                collect_pattern_eq_deps(replacement, language, deps);
            },
            PatternTerm::MultiSubst { scope, replacements } => {
                collect_pattern_eq_deps(scope, language, deps);
                for r in replacements {
                    collect_pattern_eq_deps(r, language, deps);
                }
            },
        },
        Pattern::Collection { elements, .. } => {
            for elem in elements {
                collect_pattern_eq_deps(elem, language, deps);
            }
        },
        Pattern::Map { collection, body, .. } => {
            collect_pattern_eq_deps(collection, language, deps);
            collect_pattern_eq_deps(body, language, deps);
        },
        Pattern::Zip { first, second } => {
            collect_pattern_eq_deps(first, language, deps);
            collect_pattern_eq_deps(second, language, deps);
        },
    }
}

/// Tarjan's SCC algorithm.
///
/// Returns SCCs in reverse topological order (leaf SCCs first, i.e., SCCs with
/// no outgoing edges to other SCCs come first).
///
/// # Arguments
///
/// * `n` - Number of nodes (0..n-1)
/// * `adj` - Adjacency list: `adj[u]` = list of nodes that `u` depends on (u -> v)
fn tarjan_scc(n: usize, adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct TarjanState {
        index_counter: usize,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        index: Vec<Option<usize>>,
        lowlink: Vec<usize>,
        sccs: Vec<Vec<usize>>,
    }

    fn strongconnect(v: usize, adj: &[Vec<usize>], state: &mut TarjanState) {
        state.index[v] = Some(state.index_counter);
        state.lowlink[v] = state.index_counter;
        state.index_counter += 1;
        state.stack.push(v);
        state.on_stack[v] = true;

        for &w in &adj[v] {
            if state.index[w].is_none() {
                // w has not yet been visited; recurse
                strongconnect(w, adj, state);
                state.lowlink[v] = state.lowlink[v].min(state.lowlink[w]);
            } else if state.on_stack[w] {
                // w is on the stack and hence in the current SCC
                state.lowlink[v] = state.lowlink[v].min(state.index[w].expect("index must be set"));
            }
        }

        // If v is a root node, pop the stack and generate an SCC
        if state.lowlink[v] == state.index[v].expect("index must be set") {
            let mut scc = Vec::new();
            loop {
                let w = state.stack.pop().expect("stack must not be empty during SCC extraction");
                state.on_stack[w] = false;
                scc.push(w);
                if w == v {
                    break;
                }
            }
            state.sccs.push(scc);
        }
    }

    let mut state = TarjanState {
        index_counter: 0,
        stack: Vec::with_capacity(n),
        on_stack: vec![false; n],
        index: vec![None; n],
        lowlink: vec![0; n],
        sccs: Vec::new(),
    };

    for v in 0..n {
        if state.index[v].is_none() {
            strongconnect(v, adj, &mut state);
        }
    }

    // Tarjan's produces SCCs in reverse topological order (leaves first)
    state.sccs
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ── Tarjan SCC unit tests ────────────────────────────────────────────────

    #[test]
    fn tarjan_empty_graph() {
        let sccs = tarjan_scc(0, &[]);
        assert!(sccs.is_empty());
    }

    #[test]
    fn tarjan_single_node_no_edges() {
        let adj = vec![vec![]];
        let sccs = tarjan_scc(1, &adj);
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0], vec![0]);
    }

    #[test]
    fn tarjan_two_nodes_no_cycle() {
        // 0 -> 1 (no cycle)
        let adj = vec![vec![1], vec![]];
        let sccs = tarjan_scc(2, &adj);
        assert_eq!(sccs.len(), 2);
        // Reverse topological: leaf (1) first, then root (0)
        let scc_sets: Vec<HashSet<usize>> = sccs.iter().map(|s| s.iter().copied().collect()).collect();
        assert!(scc_sets[0].contains(&1));
        assert!(scc_sets[1].contains(&0));
    }

    #[test]
    fn tarjan_two_nodes_with_cycle() {
        // 0 -> 1, 1 -> 0 (cycle)
        let adj = vec![vec![1], vec![0]];
        let sccs = tarjan_scc(2, &adj);
        assert_eq!(sccs.len(), 1);
        let scc_set: HashSet<usize> = sccs[0].iter().copied().collect();
        assert!(scc_set.contains(&0));
        assert!(scc_set.contains(&1));
    }

    #[test]
    fn tarjan_diamond_no_cycles() {
        // 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
        let adj = vec![vec![1, 2], vec![3], vec![3], vec![]];
        let sccs = tarjan_scc(4, &adj);
        assert_eq!(sccs.len(), 4, "diamond graph should have 4 singleton SCCs");
        // Each SCC should be a singleton
        for scc in &sccs {
            assert_eq!(scc.len(), 1);
        }
        // Topological order: 3 before 1,2 before 0
        let order: Vec<usize> = sccs.iter().map(|s| s[0]).collect();
        let pos_of = |node: usize| order.iter().position(|&n| n == node).expect("node not found");
        assert!(pos_of(3) < pos_of(1), "3 should come before 1");
        assert!(pos_of(3) < pos_of(2), "3 should come before 2");
        assert!(pos_of(1) < pos_of(0), "1 should come before 0");
        assert!(pos_of(2) < pos_of(0), "2 should come before 0");
    }

    #[test]
    fn tarjan_mixed_scc_and_singletons() {
        // 0 -> 1, 1 -> 2, 2 -> 0 (SCC {0,1,2}), 0 -> 3, 3 -> 4 (singletons)
        let adj = vec![vec![1, 3], vec![2], vec![0], vec![4], vec![]];
        let sccs = tarjan_scc(5, &adj);
        assert_eq!(sccs.len(), 3, "should have 3 SCCs: {{0,1,2}}, {{3}}, {{4}}");
        let scc_sets: Vec<HashSet<usize>> = sccs.iter().map(|s| s.iter().copied().collect()).collect();
        // Find the large SCC
        let large_scc = scc_sets.iter().find(|s| s.len() == 3).expect("should have a 3-element SCC");
        assert!(large_scc.contains(&0) && large_scc.contains(&1) && large_scc.contains(&2));
        // Singletons {4} and {3} should precede the large SCC in reverse topological order
        let pos_of_scc = |target: &HashSet<usize>| {
            scc_sets.iter().position(|s| s == target).expect("SCC not found")
        };
        let pos_large = pos_of_scc(large_scc);
        let singleton_4: HashSet<usize> = [4].iter().copied().collect();
        let singleton_3: HashSet<usize> = [3].iter().copied().collect();
        let pos_4 = pos_of_scc(&singleton_4);
        let pos_3 = pos_of_scc(&singleton_3);
        assert!(pos_4 < pos_3, "4 should come before 3 (reverse topo)");
        assert!(pos_3 < pos_large, "3 should come before the large SCC");
    }

    // ── EqRuleKind display tests ────────────────────────────────────────────

    #[test]
    fn eq_rule_kind_display() {
        assert_eq!(format!("{}", EqRuleKind::Reflexivity), "reflexivity");
        assert_eq!(format!("{}", EqRuleKind::Congruence), "congruence");
        assert_eq!(format!("{}", EqRuleKind::UserDefined), "user-defined");
    }

    // ── StratificationInfo display test ─────────────────────────────────────

    #[test]
    fn stratification_info_display() {
        let info = StratificationInfo {
            total_rules: 10,
            reflexivity_count: 3,
            congruence_count: 5,
            user_defined_count: 2,
            strata: vec![
                Stratum { index: 0, rules: vec![] },
                Stratum { index: 1, rules: vec![] },
                Stratum { index: 2, rules: vec![] },
            ],
            scc_count: 3,
        };
        let s = format!("{}", info);
        assert!(s.contains("10 equation rule(s)"), "should mention total rules: {}", s);
        assert!(s.contains("3 stratum/strata"), "should mention strata count: {}", s);
        assert!(s.contains("3 SCC(s)"), "should mention SCC count: {}", s);
        assert!(s.contains("3 reflexivity"), "should mention reflexivity count: {}", s);
        assert!(s.contains("5 congruence"), "should mention congruence count: {}", s);
        assert!(s.contains("2 user-defined"), "should mention user-defined count: {}", s);
    }

    // ── Stratification structural invariant tests ───────────────────────────

    /// Helper: build a minimal LanguageDef with given types, terms, and equations.
    ///
    /// This constructs a bare-bones LanguageDef for testing stratification logic
    /// without needing the full parser.
    fn make_test_language(
        types: Vec<&str>,
        terms: Vec<(&str, &str, Vec<&str>)>, // (label, category, [field_categories])
        equations: Vec<(&str, &str, &str)>,   // (name, lhs_constructor, rhs_constructor)
    ) -> LanguageDef {
        use crate::ast::grammar::{GrammarItem, GrammarRule};
        use crate::ast::language::{Equation, LangType, LanguageDef};
        use crate::ast::pattern::{Pattern, PatternTerm};
        use proc_macro2::Span;
        use syn::Ident;

        let lang_types: Vec<LangType> = types
            .iter()
            .map(|name| LangType {
                name: Ident::new(name, Span::call_site()),
                native_type: None,
            })
            .collect();

        let grammar_rules: Vec<GrammarRule> = terms
            .iter()
            .map(|(label, category, field_cats)| {
                let items: Vec<GrammarItem> = field_cats
                    .iter()
                    .map(|fc| GrammarItem::NonTerminal(Ident::new(fc, Span::call_site())))
                    .collect();
                GrammarRule {
                    label: Ident::new(label, Span::call_site()),
                    category: Ident::new(category, Span::call_site()),
                    items,
                    bindings: vec![],
                    rust_code: None,
                    term_context: None,
                    syntax_pattern: None,
                    eval_mode: None,
                    is_right_assoc: false,
                    prefix_bp: None,
                }
            })
            .collect();

        let eqs: Vec<Equation> = equations
            .iter()
            .map(|(name, lhs_ctor, _rhs_ctor)| {
                let lhs_ident = Ident::new(lhs_ctor, Span::call_site());
                Equation {
                    name: Ident::new(name, Span::call_site()),
                    type_context: vec![],
                    premises: vec![],
                    left: Pattern::Term(PatternTerm::Apply {
                        constructor: lhs_ident,
                        args: vec![Pattern::Term(PatternTerm::Var(Ident::new(
                            "X",
                            Span::call_site(),
                        )))],
                    }),
                    right: Pattern::Term(PatternTerm::Var(Ident::new(
                        "X",
                        Span::call_site(),
                    ))),
                }
            })
            .collect();

        LanguageDef {
            name: Ident::new("TestLang", Span::call_site()),
            options: std::collections::HashMap::new(),
            extends_names: vec![],
            include_names: vec![],
            mixin_names: vec![],
            types: lang_types,
            refinement_types: Vec::new(),
            token_defs: vec![],
            mode_defs: vec![],
            sync_constraints: vec![],
            tree_invariants: vec![],
            terms: grammar_rules,
            equations: eqs,
            rewrites: vec![],
            logic: None,
        }
    }

    #[test]
    fn stratify_empty_language() {
        let lang = make_test_language(vec![], vec![], vec![]);
        let info = stratify_equation_rules(&lang);
        assert_eq!(info.total_rules, 0);
        assert_eq!(info.reflexivity_count, 0);
        assert_eq!(info.congruence_count, 0);
        assert_eq!(info.user_defined_count, 0);
        assert!(info.strata.is_empty());
    }

    #[test]
    fn stratify_reflexivity_only() {
        // Language with 2 types but no constructors and no equations
        let lang = make_test_language(vec!["Proc", "Name"], vec![], vec![]);
        let info = stratify_equation_rules(&lang);
        assert_eq!(info.total_rules, 2);
        assert_eq!(info.reflexivity_count, 2);
        assert_eq!(info.congruence_count, 0);
        assert_eq!(info.user_defined_count, 0);
        // Reflexivity rules have no eq_* dependencies, so they should be
        // independent singletons (2 SCCs)
        assert_eq!(info.scc_count, 2);
        // Both should be in separate strata
        assert_eq!(info.strata.len(), 2);
        for stratum in &info.strata {
            assert_eq!(stratum.rules.len(), 1);
            assert_eq!(stratum.rules[0].kind, EqRuleKind::Reflexivity);
        }
    }

    #[test]
    fn stratify_reflexivity_plus_congruence() {
        // Proc with constructor PFoo(Name), Name with NBar()
        // Congruence for PFoo reads eq_Name, writes eq_Proc
        // Reflexivity for Proc writes eq_Proc
        // Reflexivity for Name writes eq_Name
        let lang = make_test_language(
            vec!["Proc", "Name"],
            vec![("PFoo", "Proc", vec!["Name"])],
            vec![],
        );
        let info = stratify_equation_rules(&lang);
        assert_eq!(info.reflexivity_count, 2);
        assert_eq!(info.congruence_count, 1);
        assert_eq!(info.user_defined_count, 0);
        assert_eq!(info.total_rules, 3);

        // Congruence for PFoo depends on reflexivity for Name (via eq_Name)
        // Reflexivity for Proc and Name are independent
        // So we expect at least 2 strata
        assert!(
            info.strata.len() >= 2,
            "should have at least 2 strata; got {}",
            info.strata.len()
        );

        // The congruence rule should come in a later stratum than the
        // reflexivity rule for Name (which it depends on)
        let reflex_name_stratum = info
            .strata
            .iter()
            .find(|s| {
                s.rules.iter().any(|r| {
                    r.kind == EqRuleKind::Reflexivity && r.writes_category == "Name"
                })
            })
            .expect("should find reflexivity:Name stratum");
        let cong_stratum = info
            .strata
            .iter()
            .find(|s| s.rules.iter().any(|r| r.kind == EqRuleKind::Congruence))
            .expect("should find congruence stratum");
        assert!(
            reflex_name_stratum.index < cong_stratum.index,
            "reflexivity:Name (stratum {}) should precede congruence (stratum {})",
            reflex_name_stratum.index,
            cong_stratum.index,
        );
    }

    #[test]
    fn stratify_user_equation_classified_correctly() {
        // Language with a user equation that references PFoo constructor
        let lang = make_test_language(
            vec!["Proc", "Name"],
            vec![("PFoo", "Proc", vec!["Name"])],
            vec![("Eq1", "PFoo", "PFoo")],
        );
        let info = stratify_equation_rules(&lang);
        assert_eq!(info.user_defined_count, 1);
        // Find the user-defined rule
        let user_rule = info
            .strata
            .iter()
            .flat_map(|s| s.rules.iter())
            .find(|r| r.kind == EqRuleKind::UserDefined)
            .expect("should find user-defined rule");
        assert!(
            user_rule.label.contains("Eq1"),
            "user rule label should contain 'Eq1': {}",
            user_rule.label
        );
        assert_eq!(user_rule.writes_category, "Proc");
    }

    #[test]
    fn stratify_mutual_congruence_same_scc() {
        // Two categories with mutual constructor dependencies:
        // Proc has PFoo(Name), Name has NBar(Proc)
        // Congruence for PFoo reads eq_Name, writes eq_Proc
        // Congruence for NBar reads eq_Proc, writes eq_Name
        // These form a cycle -> same SCC -> same stratum
        let lang = make_test_language(
            vec!["Proc", "Name"],
            vec![("PFoo", "Proc", vec!["Name"]), ("NBar", "Name", vec!["Proc"])],
            vec![],
        );
        let info = stratify_equation_rules(&lang);
        assert_eq!(info.congruence_count, 2);

        // Find the stratum containing congruence rules
        let cong_strata: Vec<&Stratum> = info
            .strata
            .iter()
            .filter(|s| s.rules.iter().any(|r| r.kind == EqRuleKind::Congruence))
            .collect();

        // Both congruence rules should be in the same stratum (same SCC due to cycle)
        assert_eq!(
            cong_strata.len(),
            1,
            "mutually dependent congruence rules should be in the same stratum; got {} strata",
            cong_strata.len()
        );
        assert_eq!(cong_strata[0].rules.len(), 2);
    }

    #[test]
    fn stratify_independent_categories_separate_strata() {
        // Two categories with no dependency: Proc with PFoo(Proc), Name with NBar(Name)
        // Each congruence reads only its own eq_* category
        // But congruence for PFoo reads eq_Proc which is written by reflexivity:Proc
        // and congruence:PFoo itself — this creates a self-dependency via eq_Proc.
        // Similarly for NBar. These should be independent SCCs.
        let lang = make_test_language(
            vec!["Proc", "Name"],
            vec![
                ("PFoo", "Proc", vec!["Proc"]),
                ("NBar", "Name", vec!["Name"]),
            ],
            vec![],
        );
        let info = stratify_equation_rules(&lang);
        assert_eq!(info.congruence_count, 2);

        // The two congruence rules read different eq_* categories and write
        // different eq_* categories, so they should be in different strata.
        let cong_strata: Vec<&Stratum> = info
            .strata
            .iter()
            .filter(|s| s.rules.iter().any(|r| r.kind == EqRuleKind::Congruence))
            .collect();
        assert_eq!(
            cong_strata.len(),
            2,
            "independent congruence rules should be in separate strata; got {}",
            cong_strata.len()
        );
    }

    // ── BCG06: Congruence group ordering by dependency depth ──────────────

    #[test]
    fn congruence_groups_sorted_by_dependency_depth() {
        // Build a language with 3 categories where congruence groups have
        // different dependency depths:
        //   Int has no constructor fields → no congruence groups
        //   Name has NWrap(Int) → congruence reads eq_Int (1 dep)
        //   Proc has PBin(Name, Name) → congruence reads eq_Name (1 dep, but
        //     the group key is (Proc, [Name, Name]))
        //   Proc has PTriple(Name, Int, Name) → reads eq_Name, eq_Int (2 distinct deps)
        //
        // With BCG06, groups with fewer distinct eq reads should come first.
        let lang = make_test_language(
            vec!["Proc", "Name", "Int"],
            vec![
                ("NWrap", "Name", vec!["Int"]),           // reads eq_Int → 1 dep
                ("PBin", "Proc", vec!["Name", "Name"]),    // reads eq_Name → 1 dep
                ("PTriple", "Proc", vec!["Name", "Int", "Name"]), // reads eq_Name, eq_Int → 2 deps
            ],
            vec![("Eq1", "PBin", "PBin")], // need equation to make constructors equation-active
        );

        let strat_info = stratify_equation_rules(&lang);
        let demanded: BTreeSet<String> = lang.types.iter().map(|t| t.name.to_string()).collect();

        // Generate congruence rules WITH strat_info
        let rules_ordered = generate_congruence_rules(&lang, None, None, false, &demanded, Some(&strat_info));

        // Generate congruence rules WITHOUT strat_info for comparison
        let rules_unordered = generate_congruence_rules(&lang, None, None, false, &demanded, None);

        // Both should produce the same number of rules (ordering doesn't change count)
        assert_eq!(
            rules_ordered.len(),
            rules_unordered.len(),
            "ordered and unordered should have same number of rules"
        );

        // With BCG06 ordering, the output should be non-empty
        assert!(
            !rules_ordered.is_empty(),
            "should have at least one congruence group"
        );
    }

    #[test]
    fn congruence_ordering_deterministic() {
        // Same language generated twice should produce identical output.
        let lang = make_test_language(
            vec!["Proc", "Name"],
            vec![
                ("PFoo", "Proc", vec!["Name"]),
                ("NBar", "Name", vec!["Proc"]),
            ],
            vec![("Eq1", "PFoo", "PFoo")],
        );

        let strat_info = stratify_equation_rules(&lang);
        let demanded: BTreeSet<String> = lang.types.iter().map(|t| t.name.to_string()).collect();

        let rules1 = generate_congruence_rules(&lang, None, None, false, &demanded, Some(&strat_info));
        let rules2 = generate_congruence_rules(&lang, None, None, false, &demanded, Some(&strat_info));

        assert_eq!(rules1.len(), rules2.len(), "deterministic: same count");
        for (r1, r2) in rules1.iter().zip(rules2.iter()) {
            assert_eq!(
                r1.to_string(),
                r2.to_string(),
                "deterministic: same rule content"
            );
        }
    }

    #[test]
    fn user_equation_stratum_ordering() {
        // Two user equations at different strata:
        // Eq1 references PFoo (category Proc), Eq2 references NBar (category Name).
        // PFoo has a Name field, so congruence for PFoo depends on eq_Name.
        // NBar has no category fields, so it's independent.
        // The stratification should place NBar-related rules before PFoo-related rules.
        let lang = make_test_language(
            vec!["Proc", "Name"],
            vec![
                ("PFoo", "Proc", vec!["Name"]),
                ("NBar", "Name", vec![]),
            ],
            vec![
                ("EqP", "PFoo", "PFoo"), // writes eq_Proc, reads eq_Name (from congruence)
                ("EqN", "NBar", "NBar"),  // writes eq_Name, no eq_* reads
            ],
        );

        let strat_info = stratify_equation_rules(&lang);

        // Find stratum indices for each user equation
        let eq_p_stratum = strat_info.strata.iter()
            .find(|s| s.rules.iter().any(|r| r.label.contains("EqP")))
            .expect("should find EqP stratum");
        let eq_n_stratum = strat_info.strata.iter()
            .find(|s| s.rules.iter().any(|r| r.label.contains("EqN")))
            .expect("should find EqN stratum");

        // EqN should be in an earlier (or equal) stratum than EqP because
        // EqN has no eq_* dependencies while EqP (via Proc's congruence) depends on eq_Name.
        assert!(
            eq_n_stratum.index <= eq_p_stratum.index,
            "EqN (stratum {}) should be at same or earlier stratum than EqP (stratum {})",
            eq_n_stratum.index,
            eq_p_stratum.index,
        );
    }
}
