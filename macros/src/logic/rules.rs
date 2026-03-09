//! Unified rule generation for equations and rewrites.
//!
//! This module provides `generate_rule_clause`, the core abstraction that
//! generates Ascent Datalog clauses from Pattern-based rules.
//!
//! Key insight: Equations and rewrites differ only in:
//! 1. The relation they write to (`eq_cat` vs `rw_cat`)
//! 2. Whether they're bidirectional (equations) or directional (rewrites)

use super::common::{in_cat_filter, CategoryFilter};
use crate::ast::language::{Condition, FreshnessCondition, FreshnessTarget, LanguageDef};
use crate::ast::pattern::{AscentClauses, Pattern, VariableBinding};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;

/// Unified rule generator for both equations and rewrites.
///
/// # Arguments
/// * `left` - LHS pattern to match
/// * `right` - RHS pattern to construct
/// * `conditions` - Freshness/env conditions
/// * `relation_name` - Target relation (`eq_proc` or `rw_proc`)
/// * `theory` - Theory definition
/// * `use_equation_matching` - If true, match via `eq_cat(s_orig, s)` instead of `cat(s)`
///
/// # Example
/// For equation `(PDrop (NQuote P)) == P`:
/// ```text
/// eq_proc(s.clone(), t) <--
///     proc(s),
///     if let Proc::PDrop(f0) = s,
///     let f0_deref = &**f0,
///     if let Name::NQuote(f0_f0) = f0_deref,
///     let p = f0_f0.clone(),
///     let t = p.clone();
/// ```
///
/// For rewrites with equation matching:
/// ```text
/// rw_proc(s_orig.clone(), t) <--
///     eq_proc(s_orig, s),  // match via equation
///     if let Proc::Pattern(...) = s,
///     let t = ...;
/// ```
pub fn generate_rule_clause(
    left: &Pattern,
    right: &Pattern,
    conditions: &[Condition],
    relation_name: &syn::Ident,
    language: &LanguageDef,
    use_equation_matching: bool,
) -> TokenStream {
    // 1. Determine category from LHS
    let category = left
        .category(language)
        .expect("Cannot determine category from LHS pattern");
    generate_rule_clause_with_category(
        left,
        right,
        conditions,
        relation_name,
        category,
        language,
        use_equation_matching,
    )
}

/// Generate a rule clause with an explicitly provided category.
/// Useful when the LHS is a variable and category must come from context.
///
/// When `use_equation_matching` is true, the rule matches via `eq_cat(s_orig, s)`
/// instead of `cat(s)`, enabling rewrites to apply to equation-equivalent terms
/// without needing expensive closure rules.
pub fn generate_rule_clause_with_category(
    left: &Pattern,
    right: &Pattern,
    conditions: &[Condition],
    relation_name: &syn::Ident,
    category: &syn::Ident,
    language: &LanguageDef,
    use_equation_matching: bool,
) -> TokenStream {
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());

    // 2. Find duplicate variables for equational matching
    let mut all_vars = left.var_occurrences();
    for (var, count) in right.var_occurrences() {
        *all_vars.entry(var).or_insert(0) += count;
    }
    let duplicate_vars: HashSet<_> = all_vars
        .into_iter()
        .filter(|(_, count)| *count > 1)
        .map(|(var, _)| var)
        .collect();

    // 3. Generate LHS matching clauses
    let lhs_var = format_ident!("s");
    let lhs_clauses = left.to_ascent_clauses(&lhs_var, category, language, &duplicate_vars);

    // 4. Sort conditions by estimated cost (cheapest first) for fail-fast evaluation.
    // Respects data dependencies: if condition B references a variable bound by
    // condition A's EnvQuery, A must precede B.
    let sorted_conditions = sort_conditions_by_cost(conditions);

    // 5. BCG01: Generate condition checks with earliest-valid-position metadata.
    // Each condition clause is paired with the earliest LHS clause index after
    // which all its required variables are available.
    let (positioned_condition_clauses, env_bindings) =
        generate_positioned_condition_clauses(&sorted_conditions, &lhs_clauses);

    // 6. Merge LHS bindings with env query bindings for RHS generation
    let mut all_bindings = lhs_clauses.bindings.clone();
    all_bindings.extend(env_bindings);

    // 7. Generate RHS construction
    let rhs_var = format_ident!("t");
    let rhs_expr = right.to_ascent_rhs(&all_bindings, language);

    // 8. Assemble the rule
    let clauses = &lhs_clauses.clauses;
    let eq_checks = &lhs_clauses.equational_checks;

    // For equation matching, use eq_cat(s_orig, s) instead of cat(s)
    // This allows rewrites to apply to equation-equivalent terms directly,
    // avoiding the need for expensive closure rules like:
    //   rw_proc(s1, t) <-- rw_proc(s0, t), eq_proc(s0, s1)
    let source_var = format_ident!("s_orig");

    // Build rule head and first body clause based on matching mode
    let (head, first_clause) = if use_equation_matching {
        // Rewrite rules: match via equation relation
        (
            quote! { #relation_name(#source_var.clone(), #rhs_var) },
            quote! { #eq_rel(#source_var, #lhs_var) },
        )
    } else {
        // Equation rules: match directly on category relation
        // Also add the produced term to proc, enabling:
        // 1. Deconstruction of equation-produced terms
        // 2. Reflexivity for equation-produced terms (so rewrites can match via eq_proc)
        (
            quote! { #relation_name(#lhs_var.clone(), #rhs_var.clone()), #cat_lower(#rhs_var.clone()) },
            quote! { #cat_lower(#lhs_var) },
        )
    };

    // 9. BCG01: Interleave condition clauses with LHS clauses at their earliest
    // valid positions for fail-fast evaluation.
    //
    // The idea: if a condition only requires variables bound by the first 2 LHS
    // clauses, it can be inserted right after clause 2 instead of after all LHS
    // clauses. This lets Ascent fail fast — rejecting non-matching tuples before
    // spending time on deeper pattern destructuring.
    //
    // Sprint 7: Equational checks are already interleaved into `clauses` at their
    // earliest valid position (in pattern.rs), so `eq_checks` is typically empty.
    // We still extend from it for backward compatibility.
    //
    // BCG05: Normalize-on-insert deduplication.
    // Wrap the RHS normalize call with a hash-based dedup guard. Before
    // constructing and normalizing the RHS, hash the LHS match variable. If
    // the hash was already seen in this Ascent fixpoint, skip the entire rule
    // firing — the normalized RHS for this input was already produced. This
    // avoids redundant normalize() calls when the same LHS term participates
    // in multiple equation-equivalent groups.
    let rhs_binding = quote! { let #rhs_var = (#rhs_expr).normalize() };
    let bcg05_guard = quote! {
        if {
            use std::hash::{Hash, Hasher};
            let mut __bcg05_h = std::hash::DefaultHasher::new();
            #lhs_var.hash(&mut __bcg05_h);
            let __bcg05_hash = __bcg05_h.finish();
            thread_local! {
                static __BCG05_RULE: std::cell::RefCell<(u64, std::collections::HashSet<u64>)> =
                    std::cell::RefCell::new((0, std::collections::HashSet::new()));
            }
            let __epoch = mettail_runtime::bcg05_epoch();
            __BCG05_RULE.with(|s| {
                let mut guard = s.borrow_mut();
                if guard.0 != __epoch {
                    guard.0 = __epoch;
                    guard.1.clear();
                }
                guard.1.insert(__bcg05_hash)
            })
        }
    };
    let mut body = interleave_body_clauses(
        first_clause,
        clauses,
        eq_checks,
        &positioned_condition_clauses,
        rhs_binding,
    );
    // Insert the BCG05 guard just before the final rhs_binding clause.
    // This ensures all LHS variables are bound before the hash is computed.
    let rhs_pos = body.len().saturating_sub(1);
    body.insert(rhs_pos, bcg05_guard);

    quote! { #head <-- #(#body),*; }
}

// ══════════════════════════════════════════════════════════════════════════════
// Sprint 2: Premise cost ordering
// ══════════════════════════════════════════════════════════════════════════════

/// Estimate relative cost of evaluating a condition clause.
///
/// Lower cost = cheaper = should be evaluated first in the rule body.
/// Since Ascent evaluates body clauses left-to-right (3+ clause rules have
/// fixed order), putting cheap fail-fast checks first reduces the intermediate
/// tuple count during semi-naive evaluation.
///
/// BCG01 cost model (refined):
/// - Freshness: cost 2 — O(1) `free_vars().contains()` check, but involves
///   set membership test on the term's free variable set
/// - EnvQuery: cost 5 — O(|relation|) scan, but Ascent indexes help;
///   also requires OrdVar name extraction (pattern match + Option check)
/// - ForAll: cost 10 + body_cost — O(|collection| × body_cost), iterates
///   entire collection and checks body predicate per element
///
/// For reference, other clause types (not conditions) have implicit costs:
/// - Pattern-match guard (if let): cost 1 (single pattern match, cheapest)
/// - Let binding: cost 0 (free, deterministic)
/// - Relation lookup (cat(s)): cost |relation| (scans full relation)
fn condition_cost(condition: &Condition) -> u32 {
    match condition {
        Condition::Freshness(_) => 2,
        Condition::EnvQuery { .. } => 5,
        Condition::ForAll { body, .. } => 10 + condition_cost(body),
    }
}

/// Collect the set of variable names that a condition **binds** (produces).
///
/// EnvQuery binds its result arguments (2nd+ args).
/// Freshness and ForAll do not bind new variables.
fn condition_binds(condition: &Condition) -> HashSet<String> {
    match condition {
        Condition::EnvQuery { args, .. } => {
            // First arg is the lookup key (already bound by LHS),
            // subsequent args are result bindings.
            args.iter().skip(1).map(|a| a.to_string()).collect()
        }
        _ => HashSet::new(),
    }
}

/// Collect the set of variable names that a condition **requires** (consumes).
///
/// A condition requires a variable if it references it but doesn't bind it.
/// EnvQuery requires its first arg (lookup key).
/// ForAll requires its collection variable and body's requirements.
/// Freshness requires its variable and term.
fn condition_requires(condition: &Condition) -> HashSet<String> {
    match condition {
        Condition::Freshness(fc) => {
            let mut required = HashSet::new();
            required.insert(fc.var.to_string());
            match &fc.term {
                FreshnessTarget::Var(v) => { required.insert(v.to_string()); }
                FreshnessTarget::CollectionRest(v) => { required.insert(v.to_string()); }
            }
            required
        }
        Condition::EnvQuery { args, .. } => {
            // First arg is the lookup key (required from LHS or prior condition)
            let mut required = HashSet::new();
            if let Some(first) = args.first() {
                required.insert(first.to_string());
            }
            required
        }
        Condition::ForAll { collection, body, .. } => {
            let mut required = HashSet::new();
            required.insert(collection.to_string());
            required.extend(condition_requires(body));
            required
        }
    }
}

/// Sort conditions by cost, respecting data dependencies.
///
/// If condition B requires a variable that condition A binds,
/// A must precede B. Within dependency-compatible groups, sort by
/// ascending cost for fail-fast evaluation.
///
/// Uses a stable topological sort with cost-based tie-breaking:
/// repeatedly select the cheapest condition whose requirements are
/// satisfied by LHS bindings + previously emitted conditions.
fn sort_conditions_by_cost(conditions: &[Condition]) -> Vec<Condition> {
    if conditions.len() <= 1 {
        return conditions.to_vec();
    }

    // Pre-compute costs, bindings, and requirements for each condition
    let costs: Vec<u32> = conditions.iter().map(condition_cost).collect();
    let binds: Vec<HashSet<String>> = conditions.iter().map(condition_binds).collect();
    let requires: Vec<HashSet<String>> = conditions.iter().map(condition_requires).collect();

    // Track which variables are available (initially: all LHS bindings are available,
    // but we don't have access to them here — we only track variables that other
    // conditions produce. LHS-bound variables are always available.)
    let mut available_from_conditions: HashSet<String> = HashSet::new();
    let mut emitted = vec![false; conditions.len()];
    let mut result = Vec::with_capacity(conditions.len());

    for _ in 0..conditions.len() {
        // Find cheapest unemitted condition whose requirements from OTHER conditions
        // are satisfied. Requirements from LHS bindings are always satisfied.
        let best = (0..conditions.len())
            .filter(|&i| !emitted[i])
            .filter(|&i| {
                // Check that all requirements that come from other conditions are met.
                // A requirement is "from another condition" if some condition j (j != i)
                // binds it. If no condition binds it, it's from the LHS and always available.
                requires[i].iter().all(|req| {
                    let bound_by_condition = binds.iter().enumerate().any(|(j, b)| j != i && b.contains(req));
                    !bound_by_condition || available_from_conditions.contains(req)
                })
            })
            .min_by_key(|&i| costs[i]);

        match best {
            Some(idx) => {
                emitted[idx] = true;
                available_from_conditions.extend(binds[idx].iter().cloned());
                result.push(conditions[idx].clone());
            }
            None => {
                // Cycle detected or all remaining have unsatisfied deps.
                // Emit remaining in declaration order (safe fallback).
                for (i, cond) in conditions.iter().enumerate() {
                    if !emitted[i] {
                        result.push(cond.clone());
                    }
                }
                break;
            }
        }
    }

    result
}

// BCG01: `generate_condition_clauses` superseded by `generate_positioned_condition_clauses`
// which pairs each condition clause with its earliest valid LHS position.
// The old function is retained (commented out) for reference:
//
// fn generate_condition_clauses(
//     conditions: &[Condition],
//     lhs_clauses: &AscentClauses,
// ) -> (Vec<TokenStream>, std::collections::HashMap<String, VariableBinding>) { ... }

// ══════════════════════════════════════════════════════════════════════════════
// BCG01: Join Ordering Optimization — positioned condition generation
// ══════════════════════════════════════════════════════════════════════════════

/// A condition clause paired with its earliest valid position in the LHS
/// clause sequence. Used by `interleave_body_clauses` to place conditions
/// as early as possible for fail-fast evaluation.
struct PositionedClause {
    /// The generated TokenStream for this condition clause.
    clause: TokenStream,
    /// The earliest LHS clause index after which this condition can be placed.
    /// A value of 0 means the condition can go right after the first_clause
    /// (before any LHS pattern clauses). A value of `lhs_clauses.len()` means
    /// it must go after all LHS clauses (the pre-BCG01 behavior).
    earliest_position: usize,
}

/// Compute the earliest LHS clause index at which a condition's required
/// variables are all available.
///
/// Uses `binding_clause_index` from `AscentClauses` to look up when each
/// required variable was bound. Returns the maximum clause index among all
/// required variables. If a required variable is not found in the binding
/// index (e.g., it comes from the initial relation lookup), returns 0.
fn condition_earliest_position(
    condition: &Condition,
    lhs_clauses: &AscentClauses,
) -> usize {
    let required = condition_requires(condition);
    required
        .iter()
        .filter_map(|var| lhs_clauses.binding_clause_index.get(var))
        .copied()
        .max()
        .unwrap_or(0)
}

/// Generate condition clauses with earliest-valid-position metadata.
///
/// Like `generate_condition_clauses`, but each generated clause is paired
/// with the earliest LHS clause index at which it can be placed, enabling
/// BCG01 join ordering to interleave conditions for fail-fast evaluation.
///
/// Returns: (positioned_clauses, env_bindings)
fn generate_positioned_condition_clauses(
    conditions: &[Condition],
    lhs_clauses: &AscentClauses,
) -> (Vec<PositionedClause>, std::collections::HashMap<String, VariableBinding>) {
    let mut positioned = Vec::new();
    let mut env_bindings = std::collections::HashMap::new();

    // Get a default lang_type from existing bindings
    let default_lang_type = lhs_clauses
        .bindings
        .values()
        .next()
        .map(|b| b.lang_type.clone())
        .unwrap_or_else(|| format_ident!("Unknown"));

    for cond in conditions {
        let earliest = condition_earliest_position(cond, lhs_clauses);

        match cond {
            Condition::Freshness(freshness) => {
                if let Some(clause) = generate_freshness_clause(freshness, lhs_clauses) {
                    positioned.push(PositionedClause {
                        clause,
                        earliest_position: earliest,
                    });
                }
            },
            Condition::ForAll { collection, param, body } => {
                if let Some(clause) = generate_forall_clause(collection, param, body, lhs_clauses) {
                    positioned.push(PositionedClause {
                        clause,
                        earliest_position: earliest,
                    });
                }
            },
            Condition::EnvQuery { relation, args } => {
                if args.len() < 2 {
                    panic!("EnvQuery condition requires at least 2 arguments (variable name and value)");
                }

                let var_arg = &args[0]; // The OrdVar to extract name from
                let val_arg = &args[1]; // The result to bind

                // Get binding for var_arg from LHS
                let var_arg_name = var_arg.to_string();
                let var_binding_expr = lhs_clauses
                    .bindings
                    .get(&var_arg_name)
                    .map(|b| b.expression.clone())
                    .unwrap_or_else(|| quote! { #var_arg });

                // Generate code to extract variable name from OrdVar
                let var_name_extraction = quote! {
                    {
                        let var_name_opt = match #var_binding_expr {
                            mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)) => {
                                fv.pretty_name.clone()
                            }
                            _ => None
                        };
                        var_name_opt
                    }
                };

                // val_arg will be bound from the relation query (as a reference)
                let val_binding_name = format_ident!("{}", val_arg.to_string());
                positioned.push(PositionedClause {
                    clause: quote! {
                        if let Some(var_name) = #var_name_extraction,
                        #relation(var_name, #val_binding_name)
                    },
                    earliest_position: earliest,
                });

                // Add to env_bindings - Ascent binds relation values by reference.
                // Use .clone() so we don't move out of a shared reference (E0507 for String etc).
                env_bindings.insert(
                    val_arg.to_string(),
                    VariableBinding {
                        expression: quote! { (#val_binding_name).clone() },
                        lang_type: default_lang_type.clone(),
                        scope_kind: None,
                    },
                );
            },
        }
    }

    (positioned, env_bindings)
}

/// BCG01: Interleave condition clauses with LHS clauses at their earliest
/// valid positions for fail-fast evaluation.
///
/// Instead of appending all conditions after all LHS clauses (the pre-BCG01
/// behavior), this function inserts each condition right after the LHS clause
/// that makes its last required variable available.
///
/// This reduces intermediate tuple counts during Ascent's semi-naive evaluation:
/// if a cheap freshness check can reject a tuple after only 2 LHS clauses,
/// the remaining 5 LHS clauses are never evaluated for that tuple.
///
/// # Arguments
/// * `first_clause` - The initial relation lookup (always first)
/// * `lhs_clauses` - LHS pattern matching clauses (internal order preserved)
/// * `eq_checks` - Equational checks for duplicate variables (typically empty
///   since Sprint 7 interleaves them into `lhs_clauses`)
/// * `positioned_conditions` - Condition clauses with their earliest valid positions
/// * `rhs_binding` - The final RHS let binding (always last)
fn interleave_body_clauses(
    first_clause: TokenStream,
    lhs_clauses: &[TokenStream],
    eq_checks: &[TokenStream],
    positioned_conditions: &[PositionedClause],
    rhs_binding: TokenStream,
) -> Vec<TokenStream> {
    let total_cap = 1 + lhs_clauses.len() + eq_checks.len() + positioned_conditions.len() + 1;
    let mut body = Vec::with_capacity(total_cap);

    // Always start with the relation lookup
    body.push(first_clause);

    // Group conditions by their target slot in the LHS clause sequence.
    //
    // `binding_clause_index` records the clause count at binding time: if a
    // variable was bound when `clauses.len() == k`, it means the binding was
    // recorded when there were already k clauses in the vec. The variable is
    // therefore available after all k clauses have been emitted.
    //
    // `earliest_position` = max clause_index among a condition's required vars.
    // We map this to a "slot":
    //   Slot 0: condition can go before any LHS clause (earliest_position == 0)
    //   Slot i (1..=lhs_len): condition goes after LHS clause i-1
    //
    // Conditions within the same slot preserve their cost-sorted order from
    // `sort_conditions_by_cost`, which already handles inter-condition deps.
    let lhs_len = lhs_clauses.len();
    let num_slots = lhs_len + 1;
    let mut condition_slots: Vec<Vec<usize>> = vec![Vec::new(); num_slots];

    for (cond_idx, pc) in positioned_conditions.iter().enumerate() {
        let slot = pc.earliest_position.min(lhs_len);
        condition_slots[slot].push(cond_idx);
    }

    // Slot 0: conditions whose requirements are satisfied before any LHS clause
    for &cond_idx in &condition_slots[0] {
        body.push(positioned_conditions[cond_idx].clause.clone());
    }

    // Interleave: emit each LHS clause, then any conditions at that slot
    for (i, lhs_clause) in lhs_clauses.iter().enumerate() {
        body.push(lhs_clause.clone());
        // Slot i+1: conditions satisfied after LHS clause i
        for &cond_idx in &condition_slots[i + 1] {
            body.push(positioned_conditions[cond_idx].clause.clone());
        }
    }

    // Backward compat: append any remaining eq_checks (typically empty since Sprint 7)
    body.extend(eq_checks.iter().cloned());

    // Always end with the RHS binding
    body.push(rhs_binding);

    body
}

/// Generate a ForAll condition clause: for all `param` in `collection`, `body` holds.
fn generate_forall_clause(
    collection: &syn::Ident,
    param: &syn::Ident,
    body: &Condition,
    lhs_clauses: &AscentClauses,
) -> Option<TokenStream> {
    let coll_name = collection.to_string();
    let coll_binding = &lhs_clauses.bindings.get(&coll_name)?.expression;

    match body {
        Condition::Freshness(freshness) => match &freshness.term {
            FreshnessTarget::Var(term_var) => {
                let term_name = term_var.to_string();
                let term_binding = &lhs_clauses.bindings.get(&term_name)?.expression;
                Some(quote! {
                    if #coll_binding.iter().all(|#param|
                        !mettail_runtime::BoundTerm::free_vars(&#term_binding).contains(&#param.0)
                    )
                })
            },
            FreshnessTarget::CollectionRest(rest_var) => {
                let rest_name = rest_var.to_string();
                let rest_binding = &lhs_clauses.bindings.get(&rest_name)?.expression;
                Some(quote! {
                    if #coll_binding.iter().all(|#param|
                        #rest_binding.clone().iter().all(|(elem, _)|
                            !mettail_runtime::BoundTerm::free_vars(elem).contains(&#param.0)
                        )
                    )
                })
            },
        },
        _ => {
            panic!("ForAll body currently only supports Freshness conditions");
        },
    }
}

/// Generate a freshness condition clause.
fn generate_freshness_clause(
    freshness: &FreshnessCondition,
    lhs_clauses: &AscentClauses,
) -> Option<TokenStream> {
    let var_name = freshness.var.to_string();
    let var_binding = &lhs_clauses.bindings.get(&var_name)?.expression;

    match &freshness.term {
        FreshnessTarget::Var(term_var) => {
            let term_name = term_var.to_string();
            let term_binding = &lhs_clauses.bindings.get(&term_name)?.expression;

            // Generate: if !term_binding.free_vars().contains(&var_binding)
            // var_binding is a FreeVar<String> from a binder
            // free_vars() returns HashSet<FreeVar<String>>
            Some(quote! {
                if !mettail_runtime::BoundTerm::free_vars(&#term_binding).contains(&#var_binding)
            })
        },
        FreshnessTarget::CollectionRest(rest_var) => {
            let rest_name = rest_var.to_string();
            let rest_binding = &lhs_clauses.bindings.get(&rest_name)?.expression;

            // Check freshness in all elements of the rest collection
            // var_binding is a FreeVar<String> from a binder
            Some(quote! {
                if #rest_binding.clone().iter().all(|(elem, _)| !mettail_runtime::BoundTerm::free_vars(elem).contains(&#var_binding))
            })
        },
    }
}

/// Convert Premise to Condition for backward compatibility with generate_rule_clause
fn premise_to_condition(premise: &crate::ast::language::Premise) -> Option<Condition> {
    match premise {
        crate::ast::language::Premise::Freshness(f) => Some(Condition::Freshness(f.clone())),
        crate::ast::language::Premise::RelationQuery { relation, args } => {
            Some(Condition::EnvQuery {
                relation: relation.clone(),
                args: args.clone(),
            })
        },
        crate::ast::language::Premise::Congruence { .. } => None, // Handled separately
        crate::ast::language::Premise::ForAll { collection, param, body } => {
            Some(Condition::ForAll {
                collection: collection.clone(),
                param: param.clone(),
                body: Box::new(premise_to_condition(body)?),
            })
        },
    }
}

/// Generate all equation rules for a theory.
/// Equation rules use direct category matching (not equation matching)
/// because they define the base equations that feed into the eq_* relations.
///
/// When `cat_filter` is `Some`, only generates rules for categories in the filter set.
/// When `subsumed_equations` is non-empty, subsumed equations are skipped (Sprint A N10 DCE).
/// When `cancellation_equations` is non-empty, cancellation pair equations are suppressed
/// from eqrel generation (they would cause non-convergence via symmetric expansion).
/// ## ART06 Extended Demand Filtering
///
/// Skips user equations targeting categories not in the `demanded` set.
///
/// ## BCG06 Stratum-Ordered Rule Generation
///
/// When `strat_info` is provided, equations are sorted by stratum index so that
/// equations with fewer dependencies are emitted first, enabling faster convergence.
pub fn generate_equation_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
    subsumed_equations: &std::collections::HashSet<usize>,
    cancellation_equations: &std::collections::HashSet<usize>,
    demanded: &std::collections::BTreeSet<String>,
    strat_info: Option<&crate::logic::equations::StratificationInfo>,
) -> Vec<TokenStream> {
    // BCG06: Build a map from equation name to stratum index for sorting.
    let eq_stratum_order: std::collections::HashMap<String, usize> = strat_info
        .map(|si| {
            let mut order = std::collections::HashMap::new();
            for stratum in &si.strata {
                for rule in &stratum.rules {
                    if rule.kind == crate::logic::equations::EqRuleKind::UserDefined {
                        // Extract the equation name from the label "user:<name>"
                        if let Some(name) = rule.label.strip_prefix("user:") {
                            order.insert(name.to_string(), stratum.index);
                        }
                    }
                }
            }
            order
        })
        .unwrap_or_default();

    // Collect eligible equations with their indices
    let mut eligible: Vec<(usize, &crate::ast::language::Equation)> = Vec::new();

    for (eq_idx, eq) in language.equations.iter().enumerate() {
        // Sprint A (N10): Skip subsumed equations.
        if subsumed_equations.contains(&eq_idx) {
            continue;
        }
        // Skip cancellation pair equations
        if cancellation_equations.contains(&eq_idx) {
            continue;
        }
        // Determine category - try LHS first, then RHS
        let category = eq
            .left
            .category(language)
            .or_else(|| eq.right.category(language));

        if let Some(category) = category {
            // Skip categories not in the filter
            if !in_cat_filter(category, cat_filter) {
                continue;
            }
            // ART06: Skip categories not in the demanded set
            if !demanded.contains(&category.to_string()) {
                continue;
            }
            eligible.push((eq_idx, eq));
        }
    }

    // BCG06: Sort eligible equations by stratum index (lower = fewer dependencies = first)
    if !eq_stratum_order.is_empty() {
        eligible.sort_by_key(|(_, eq)| {
            eq_stratum_order
                .get(&eq.name.to_string())
                .copied()
                .unwrap_or(usize::MAX)
        });
    }

    let mut rules = Vec::new();

    for (_eq_idx, eq) in &eligible {
        let category = eq
            .left
            .category(language)
            .or_else(|| eq.right.category(language))
            .expect("Category already verified above");

        let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());

        // Convert premises to Conditions (filter out any congruence - invalid for equations)
        let conditions: Vec<Condition> = eq
            .premises
            .iter()
            .filter_map(premise_to_condition)
            .collect();

        // Forward direction: left => right
        // Skip if LHS is just a variable (would match everything)
        if !eq.left.is_just_variable() {
            rules.push(generate_rule_clause_with_category(
                &eq.left,
                &eq.right,
                &conditions,
                &eq_rel,
                category,
                language,
                false, // equations don't use equation matching
            ));
        }

        // Backward direction: right => left (equations are symmetric)
        // Skip if RHS is just a variable (would match everything and create infinite terms)
        if !eq.right.is_just_variable() {
            rules.push(generate_rule_clause_with_category(
                &eq.right,
                &eq.left,
                &conditions,
                &eq_rel,
                category,
                language,
                false, // equations don't use equation matching
            ));
        }
    }

    rules
}

/// Generate all base rewrite rules for a theory.
/// (Congruence rules are handled separately.)
///
/// Rewrite rules use equation matching: they iterate over `eq_cat(s_orig, s)`
/// instead of `cat(s)`, allowing rewrites to apply to equation-equivalent terms
/// without needing expensive closure rules like:
///   rw_proc(s1, t) <-- rw_proc(s0, t), eq_proc(s0, s1)
///
/// When `cat_filter` is `Some`, only generates rules for categories in the filter set.
pub fn generate_base_rewrites(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    for rw in &language.rewrites {
        // Skip congruence rules (those with a congruence premise)
        if rw.is_congruence_rule() {
            continue;
        }

        // Determine category from LHS
        if let Some(category) = rw.left.category(language) {
            // Skip categories not in the filter
            if !in_cat_filter(category, cat_filter) {
                continue;
            }

            let rw_rel = format_ident!("rw_{}", category.to_string().to_lowercase());

            // Convert premises to Conditions
            let conditions: Vec<Condition> = rw
                .premises
                .iter()
                .filter_map(premise_to_condition)
                .collect();

            // use_equation_matching: true - rewrites match via equation relation
            rules.push(generate_rule_clause(
                &rw.left,
                &rw.right,
                &conditions,
                &rw_rel,
                language,
                true, // rewrites use equation matching
            ));
        }
    }

    rules
}

// ══════════════════════════════════════════════════════════════════════════════
// A-RT05: Compile-time depth delta analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Result of analyzing depth delta for a single equation or rewrite rule.
#[derive(Debug, Clone)]
pub struct DepthDeltaResult {
    /// Rule name (for diagnostics).
    pub rule_name: String,
    /// Whether this is an equation (true) or rewrite (false).
    pub is_equation: bool,
    /// Maximum constructor nesting depth on the LHS.
    pub lhs_depth: u32,
    /// Maximum constructor nesting depth on the RHS.
    pub rhs_depth: u32,
    /// Delta = rhs_depth - lhs_depth (positive means depth-increasing).
    pub delta: i32,
}

/// Compute the constructor nesting depth of a pattern.
///
/// - Variables: depth 0
/// - Constructor applications: 1 + max(arg depths)
/// - Lambdas/binders: 1 + body depth
/// - Collections: 1 + max(element depths)
/// - Map/Zip: 1 + max(component depths)
fn pattern_depth(pattern: &crate::ast::pattern::Pattern) -> u32 {
    use crate::ast::pattern::Pattern;

    match pattern {
        Pattern::Term(pt) => pattern_term_depth(pt),
        Pattern::Collection { elements, .. } => {
            let max_elem = elements.iter().map(pattern_depth).max().unwrap_or(0);
            1 + max_elem
        }
        Pattern::Map { body, .. } => 1 + pattern_depth(body),
        Pattern::Zip { first, second } => {
            1 + pattern_depth(first).max(pattern_depth(second))
        }
    }
}

/// Compute the constructor nesting depth of a pattern term.
fn pattern_term_depth(pt: &crate::ast::pattern::PatternTerm) -> u32 {
    use crate::ast::pattern::PatternTerm;

    match pt {
        PatternTerm::Var(_) => 0,
        PatternTerm::Apply { args, .. } => {
            let max_arg = args.iter().map(pattern_depth).max().unwrap_or(0);
            1 + max_arg
        }
        PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
            1 + pattern_depth(body)
        }
        PatternTerm::Subst { term, replacement, .. } => {
            1 + pattern_depth(term).max(pattern_depth(replacement))
        }
        PatternTerm::MultiSubst { scope, replacements } => {
            let max_rep = replacements.iter().map(pattern_depth).max().unwrap_or(0);
            1 + pattern_depth(scope).max(max_rep)
        }
    }
}

/// Analyze the depth delta of all equations and rewrites in a language definition.
///
/// For each rule, computes the maximum constructor nesting depth on both LHS and
/// RHS, and the delta (RHS - LHS). A positive delta means the rule is
/// depth-increasing: it produces terms deeper than those it consumes.
///
/// Returns a list of `DepthDeltaResult` for all rules.
pub fn analyze_depth_delta(language: &LanguageDef) -> Vec<DepthDeltaResult> {
    let mut results = Vec::with_capacity(language.equations.len() + language.rewrites.len());

    for eq in &language.equations {
        let lhs_depth = pattern_depth(&eq.left);
        let rhs_depth = pattern_depth(&eq.right);
        results.push(DepthDeltaResult {
            rule_name: eq.name.to_string(),
            is_equation: true,
            lhs_depth,
            rhs_depth,
            delta: rhs_depth as i32 - lhs_depth as i32,
        });
    }

    for rw in &language.rewrites {
        let lhs_depth = pattern_depth(&rw.left);
        let rhs_depth = pattern_depth(&rw.right);
        results.push(DepthDeltaResult {
            rule_name: rw.name.to_string(),
            is_equation: false,
            lhs_depth,
            rhs_depth,
            delta: rhs_depth as i32 - lhs_depth as i32,
        });
    }

    results
}

/// Check whether the grammar has any depth-increasing rules without
/// complementary depth-decreasing rules.
///
/// Returns `true` if all rules are depth-non-increasing (delta <= 0), meaning
/// the fixpoint is guaranteed to converge (no unbounded term growth).
///
/// When `false`, there exist depth-increasing rules, and the caller should
/// consider emitting an A-RT05 warning or enabling the runtime depth bound.
pub fn is_depth_bounded(results: &[DepthDeltaResult]) -> bool {
    // Check if any rule has positive delta
    let has_increasing = results.iter().any(|r| r.delta > 0);
    if !has_increasing {
        return true;
    }

    // For equations, both directions matter: an equation with positive delta
    // in one direction has negative delta in the reverse direction.
    // But the equation generates *both* directions, so the net effect includes
    // the depth-increasing direction. For safety, we consider equations with
    // positive delta as potentially non-converging.
    false
}

// ══════════════════════════════════════════════════════════════════════════════
// B-CG04: Ground-term short-circuit in rewrite rules
// ══════════════════════════════════════════════════════════════════════════════

/// B-CG04: Detect ground-LHS rewrite rules and generate direct seed tuples.
///
/// A "ground-LHS" rewrite has a LHS pattern composed entirely of concrete
/// constructors and literals (no variables, no lambdas, no substitutions).
/// Such a rule can match at most one specific term shape, so its result is
/// statically known at compile time.
///
/// For each ground-LHS rewrite, this function generates a `TokenStream` of the form:
///   `prog.rw_cat.push((lhs_term.normalize(), rhs_term.normalize()));`
/// that seeds the rewrite relation at Ascent initialization (iteration 0),
/// bypassing per-iteration equation scanning and pattern matching.
///
/// The original Ascent rule is **preserved** for soundness: equation-equivalent
/// terms may still need to fire the rule via `eq_cat(s_orig, s)`, and the
/// equation-rewrite closure rule `rw_cat(a,c) <-- eq_cat(a,b), rw_cat(b,c)`
/// propagates the seed to equation-equivalent sources.
///
/// Also seeds `cat(lhs_term)` and `cat(rhs_term)` so that deconstruction rules
/// fire on both sides, enabling downstream rules that depend on subterms.
///
/// Returns a vec of seed `TokenStream` fragments and a count of detected ground rewrites.
pub fn generate_ground_rewrite_seeds(
    language: &LanguageDef,
) -> (Vec<TokenStream>, usize) {
    use std::collections::HashMap;
    use crate::ast::pattern::VariableBinding;

    let mut seeds = Vec::new();
    let empty_bindings: HashMap<String, VariableBinding> = HashMap::new();

    for rw in &language.rewrites {
        // Skip congruence rules
        if rw.is_congruence_rule() {
            continue;
        }

        // Skip rules with premises (freshness, env queries, etc.)
        // Ground LHS with premises is not fully ground in a semantic sense.
        if !rw.premises.is_empty() {
            continue;
        }

        // Check if LHS is ground
        if !rw.left.is_ground_pattern(language) {
            continue;
        }

        // Check if RHS is also ground (if RHS references variables from LHS,
        // those variables don't exist in ground patterns, so RHS must also be ground)
        if !rw.right.is_ground_pattern(language) {
            continue;
        }

        // Determine category from LHS
        let category = match rw.left.category(language) {
            Some(cat) => cat,
            None => continue,
        };

        let rw_rel = format_ident!("rw_{}", category.to_string().to_lowercase());
        let cat_rel = format_ident!("{}", category.to_string().to_lowercase());

        // Generate LHS and RHS term construction expressions.
        // For ground patterns, `to_ascent_rhs` with empty bindings produces
        // the correct constructor expression (no variable lookups needed).
        let lhs_expr = rw.left.to_ascent_rhs(&empty_bindings, language);
        let rhs_expr = rw.right.to_ascent_rhs(&empty_bindings, language);

        // Emit seed: push (lhs, rhs) into rw_cat, and both terms into cat
        // Normalize both sides to eagerly collapse any cancellation pairs.
        seeds.push(quote! {
            {
                let __ground_lhs = (#lhs_expr).normalize();
                let __ground_rhs = (#rhs_expr).normalize();
                prog.#rw_rel.push((__ground_lhs.clone(), __ground_rhs.clone()));
                prog.#cat_rel.push((__ground_lhs,));
                prog.#cat_rel.push((__ground_rhs,));
            }
        });
    }

    let count = seeds.len();
    (seeds, count)
}

pub fn generate_freshness_functions(_language: &LanguageDef) -> TokenStream {
    quote! {
        pub fn is_fresh<T>(binder: &mettail_runtime::Binder<String>, term: &T) -> bool
        where
            T: mettail_runtime::BoundTerm<String>
        {
            use mettail_runtime::BoundTerm;

            let mut is_fresh = true;
            term.visit_vars(&mut |v| {
                if let mettail_runtime::Var::Free(fv) = v {
                    if fv == &binder.0 {
                        is_fresh = false;
                    }
                }
            });

            is_fresh
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// BCG01: Unit tests for join ordering optimization
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::language::{Condition, FreshnessCondition, FreshnessTarget};
    use crate::ast::pattern::{AscentClauses, VariableBinding};
    use proc_macro2::Span;
    use quote::quote;

    fn make_ident(s: &str) -> syn::Ident {
        syn::Ident::new(s, Span::call_site())
    }

    fn make_freshness(var: &str, term: &str) -> Condition {
        Condition::Freshness(FreshnessCondition {
            var: make_ident(var),
            term: FreshnessTarget::Var(make_ident(term)),
        })
    }

    fn make_env_query(relation: &str, key: &str, val: &str) -> Condition {
        Condition::EnvQuery {
            relation: make_ident(relation),
            args: vec![make_ident(key), make_ident(val)],
        }
    }

    fn make_forall(collection: &str, param: &str, body: Condition) -> Condition {
        Condition::ForAll {
            collection: make_ident(collection),
            param: make_ident(param),
            body: Box::new(body),
        }
    }

    // ── Cost model tests ──────────────────────────────────────────────────

    #[test]
    fn test_condition_cost_freshness() {
        let cond = make_freshness("x", "P");
        assert_eq!(condition_cost(&cond), 2);
    }

    #[test]
    fn test_condition_cost_env_query() {
        let cond = make_env_query("env_var", "x", "v");
        assert_eq!(condition_cost(&cond), 5);
    }

    #[test]
    fn test_condition_cost_forall() {
        let body = make_freshness("x", "P");
        let cond = make_forall("ns", "n", body);
        // ForAll cost = 10 + body_cost(2) = 12
        assert_eq!(condition_cost(&cond), 12);
    }

    #[test]
    fn test_condition_cost_nested_forall() {
        let inner = make_freshness("x", "Q");
        let outer = make_forall("ns", "n", inner);
        let double = make_forall("ms", "m", outer);
        // outer = 10 + 2 = 12, double = 10 + 12 = 22
        assert_eq!(condition_cost(&double), 22);
    }

    // ── sort_conditions_by_cost tests ─────────────────────────────────────

    #[test]
    fn test_sort_conditions_by_cost_orders_cheapest_first() {
        // ForAll (cost 12) > EnvQuery (cost 5) > Freshness (cost 2)
        let conditions = vec![
            make_forall("ns", "n", make_freshness("x", "P")),
            make_env_query("env_var", "x", "v"),
            make_freshness("y", "Q"),
        ];

        let sorted = sort_conditions_by_cost(&conditions);
        assert_eq!(sorted.len(), 3);

        // Freshness (2) should come first, then EnvQuery (5), then ForAll (12)
        assert!(matches!(&sorted[0], Condition::Freshness(_)));
        assert!(matches!(&sorted[1], Condition::EnvQuery { .. }));
        assert!(matches!(&sorted[2], Condition::ForAll { .. }));
    }

    #[test]
    fn test_sort_conditions_respects_data_dependencies() {
        // EnvQuery binds "v", Freshness requires "v"
        // Even though Freshness is cheaper, EnvQuery must come first
        let conditions = vec![
            make_freshness("v", "P"),  // cost 2, requires "v" (bound by EnvQuery)
            make_env_query("env_var", "x", "v"),  // cost 5, binds "v"
        ];

        let sorted = sort_conditions_by_cost(&conditions);
        assert_eq!(sorted.len(), 2);

        // EnvQuery must come first because it binds "v" which Freshness needs
        assert!(matches!(&sorted[0], Condition::EnvQuery { .. }));
        assert!(matches!(&sorted[1], Condition::Freshness(_)));
    }

    #[test]
    fn test_sort_conditions_single_element() {
        let conditions = vec![make_freshness("x", "P")];
        let sorted = sort_conditions_by_cost(&conditions);
        assert_eq!(sorted.len(), 1);
        assert!(matches!(&sorted[0], Condition::Freshness(_)));
    }

    #[test]
    fn test_sort_conditions_empty() {
        let conditions: Vec<Condition> = vec![];
        let sorted = sort_conditions_by_cost(&conditions);
        assert!(sorted.is_empty());
    }

    // ── condition_earliest_position tests ─────────────────────────────────

    #[test]
    fn test_earliest_position_no_requirements() {
        // A freshness condition where the required vars aren't in binding_clause_index
        // (they come from the initial relation lookup) => position 0
        let cond = make_freshness("x", "P");

        let lhs = AscentClauses::default();
        let pos = condition_earliest_position(&cond, &lhs);
        assert_eq!(pos, 0);
    }

    #[test]
    fn test_earliest_position_with_late_binding() {
        // Variable "x" is bound at clause index 3
        let cond = make_freshness("x", "P");

        let mut lhs = AscentClauses::default();
        // Simulate 5 clauses being pushed, with "x" bound at index 3
        for _ in 0..5 {
            lhs.clauses.push(quote! { dummy });
        }
        lhs.binding_clause_index.insert("x".to_string(), 3);
        // "P" is bound at clause index 1
        lhs.binding_clause_index.insert("P".to_string(), 1);

        let pos = condition_earliest_position(&cond, &lhs);
        // max(3, 1) = 3
        assert_eq!(pos, 3);
    }

    #[test]
    fn test_earliest_position_env_query() {
        // EnvQuery requires its first arg
        let cond = make_env_query("env_var", "x", "v");

        let mut lhs = AscentClauses::default();
        for _ in 0..4 {
            lhs.clauses.push(quote! { dummy });
        }
        lhs.binding_clause_index.insert("x".to_string(), 2);

        let pos = condition_earliest_position(&cond, &lhs);
        assert_eq!(pos, 2);
    }

    // ── interleave_body_clauses tests ─────────────────────────────────────

    #[test]
    fn test_interleave_no_conditions() {
        let first = quote! { cat(s) };
        let lhs = vec![
            quote! { if let Proc::PNew(f0) = s },
            quote! { let f0_deref = &**f0 },
        ];
        let eq_checks: Vec<TokenStream> = vec![];
        let conditions: Vec<PositionedClause> = vec![];
        let rhs = quote! { let t = P.clone() };

        let body = interleave_body_clauses(first, &lhs, &eq_checks, &conditions, rhs);
        assert_eq!(body.len(), 4); // first + 2 lhs + rhs
    }

    #[test]
    fn test_interleave_condition_at_position_0() {
        // Condition can go before any LHS clause
        let first = quote! { cat(s) };
        let lhs = vec![
            quote! { if let Proc::PNew(f0) = s },
            quote! { let f0_deref = &**f0 },
        ];
        let eq_checks: Vec<TokenStream> = vec![];
        let conditions = vec![PositionedClause {
            clause: quote! { if !free_vars_check },
            earliest_position: 0,
        }];
        let rhs = quote! { let t = P.clone() };

        let body = interleave_body_clauses(first, &lhs, &eq_checks, &conditions, rhs);
        // first, condition_at_0, lhs[0], lhs[1], rhs
        assert_eq!(body.len(), 5);
        // The condition should be at index 1 (after first, before first LHS)
        assert_eq!(body[1].to_string(), quote! { if !free_vars_check }.to_string());
    }

    #[test]
    fn test_interleave_condition_after_lhs_clause_1() {
        // Condition has earliest_position = 1, meaning after first LHS clause
        let first = quote! { cat(s) };
        let lhs = vec![
            quote! { if let Proc::PNew(f0) = s },
            quote! { let f0_deref = &**f0 },
            quote! { if let Name::NQuote(g0) = f0_deref },
        ];
        let eq_checks: Vec<TokenStream> = vec![];
        let conditions = vec![PositionedClause {
            clause: quote! { if freshness_check },
            earliest_position: 1,
        }];
        let rhs = quote! { let t = P.clone() };

        let body = interleave_body_clauses(first, &lhs, &eq_checks, &conditions, rhs);
        // first, lhs[0], condition, lhs[1], lhs[2], rhs
        assert_eq!(body.len(), 6);
        assert_eq!(body[2].to_string(), quote! { if freshness_check }.to_string());
    }

    #[test]
    fn test_interleave_multiple_conditions_different_positions() {
        // Two conditions at different positions
        let first = quote! { cat(s) };
        let lhs = vec![
            quote! { clause_0 },
            quote! { clause_1 },
            quote! { clause_2 },
        ];
        let eq_checks: Vec<TokenStream> = vec![];
        let conditions = vec![
            PositionedClause {
                clause: quote! { early_check },
                earliest_position: 1,
            },
            PositionedClause {
                clause: quote! { late_check },
                earliest_position: 3,
            },
        ];
        let rhs = quote! { rhs_binding };

        let body = interleave_body_clauses(first, &lhs, &eq_checks, &conditions, rhs);
        // first, clause_0, early_check, clause_1, clause_2, late_check, rhs
        assert_eq!(body.len(), 7);
        assert_eq!(body[0].to_string(), quote! { cat(s) }.to_string());
        assert_eq!(body[1].to_string(), quote! { clause_0 }.to_string());
        assert_eq!(body[2].to_string(), quote! { early_check }.to_string());
        assert_eq!(body[3].to_string(), quote! { clause_1 }.to_string());
        assert_eq!(body[4].to_string(), quote! { clause_2 }.to_string());
        assert_eq!(body[5].to_string(), quote! { late_check }.to_string());
        assert_eq!(body[6].to_string(), quote! { rhs_binding }.to_string());
    }

    #[test]
    fn test_interleave_condition_clamped_to_lhs_len() {
        // Condition with earliest_position > lhs.len() is clamped
        let first = quote! { cat(s) };
        let lhs = vec![quote! { clause_0 }];
        let eq_checks: Vec<TokenStream> = vec![];
        let conditions = vec![PositionedClause {
            clause: quote! { late_check },
            earliest_position: 99, // Much larger than lhs.len()
        }];
        let rhs = quote! { rhs_binding };

        let body = interleave_body_clauses(first, &lhs, &eq_checks, &conditions, rhs);
        // first, clause_0, late_check (clamped to after last LHS), rhs
        assert_eq!(body.len(), 4);
        assert_eq!(body[2].to_string(), quote! { late_check }.to_string());
    }

    #[test]
    fn test_interleave_eq_checks_after_conditions() {
        // eq_checks go after all LHS clauses and conditions
        let first = quote! { cat(s) };
        let lhs = vec![quote! { clause_0 }];
        let eq_checks = vec![quote! { eq_check }];
        let conditions = vec![PositionedClause {
            clause: quote! { cond_check },
            earliest_position: 1,
        }];
        let rhs = quote! { rhs_binding };

        let body = interleave_body_clauses(first, &lhs, &eq_checks, &conditions, rhs);
        // first, clause_0, cond_check, eq_check, rhs
        assert_eq!(body.len(), 5);
        assert_eq!(body[2].to_string(), quote! { cond_check }.to_string());
        assert_eq!(body[3].to_string(), quote! { eq_check }.to_string());
        assert_eq!(body[4].to_string(), quote! { rhs_binding }.to_string());
    }

    // ── AscentClauses::record_binding tests ───────────────────────────────

    #[test]
    fn test_record_binding_tracks_clause_index() {
        let mut clauses = AscentClauses::default();

        // Record binding before any clauses
        clauses.record_binding(
            "x".to_string(),
            VariableBinding {
                expression: quote! { x.clone() },
                lang_type: make_ident("Proc"),
                scope_kind: None,
            },
        );
        assert_eq!(clauses.binding_clause_index["x"], 0);

        // Push 2 clauses
        clauses.clauses.push(quote! { clause_0 });
        clauses.clauses.push(quote! { clause_1 });

        // Record binding after 2 clauses
        clauses.record_binding(
            "y".to_string(),
            VariableBinding {
                expression: quote! { y.clone() },
                lang_type: make_ident("Name"),
                scope_kind: None,
            },
        );
        assert_eq!(clauses.binding_clause_index["y"], 2);

        // Push 1 more clause
        clauses.clauses.push(quote! { clause_2 });

        // Record binding after 3 clauses
        clauses.record_binding(
            "z".to_string(),
            VariableBinding {
                expression: quote! { z.clone() },
                lang_type: make_ident("Proc"),
                scope_kind: None,
            },
        );
        assert_eq!(clauses.binding_clause_index["z"], 3);

        // Re-recording doesn't update the index (uses or_insert)
        clauses.clauses.push(quote! { clause_3 });
        clauses.record_binding(
            "x".to_string(),
            VariableBinding {
                expression: quote! { x_new.clone() },
                lang_type: make_ident("Proc"),
                scope_kind: None,
            },
        );
        assert_eq!(clauses.binding_clause_index["x"], 0); // Still 0, not 4
    }
}
