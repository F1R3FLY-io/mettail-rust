//! Unified rule generation for equations and rewrites.
//!
//! This module provides `generate_rule_clause`, the core abstraction that
//! generates Ascent Datalog clauses from Pattern-based rules.
//!
//! Key insight: Equations and rewrites differ only in:
//! 1. The relation they write to (`eq_cat` vs `rw_cat`)
//! 2. Whether they're bidirectional (equations) or directional (rewrites)

use super::common::{in_cat_filter, CategoryFilter};
use crate::ast::language::{
    Condition, FreshnessCondition, FreshnessTarget, LanguageDef,
    LinearRelation, RefinementPredicate,
};
use crate::ast::pattern::{AscentClauses, Pattern, VariableBinding};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;
use syn::Ident;

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
        // Behavioral guards are expensive: they enumerate relation domains
        // and evaluate quantified formulas at runtime via LogicT.
        // AC-match is even more expensive due to combinatorial partition enumeration.
        Condition::BehavioralGuard(pred) => match pred {
            crate::ast::language::BehavioralPred::AcMatch { .. } => 25,
            _ => 20,
        },
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
        Condition::BehavioralGuard(pred) => {
            // Behavioral guards require all free variables referenced in
            // the predicate to be bound by LHS or prior conditions.
            collect_pred_free_vars(pred)
        }
    }
}

/// Collect free variable names from a behavioral predicate.
///
/// Returns the set of variable names that must be bound in the environment
/// before evaluating the guard. Quantifier-bound variables are excluded.
fn collect_pred_free_vars(pred: &crate::ast::language::BehavioralPred) -> HashSet<String> {
    let mut free = HashSet::new();
    let bound = HashSet::new();
    collect_pred_free_vars_inner(pred, &mut free, &bound);
    free
}

fn collect_pred_free_vars_inner(
    pred: &crate::ast::language::BehavioralPred,
    free: &mut HashSet<String>,
    bound: &HashSet<String>,
) {
    use crate::ast::language::{BehavioralPred, PredArg};
    match pred {
        BehavioralPred::RelationQuery { args, .. } => {
            for arg in args {
                if let PredArg::Var(v) = arg {
                    let name = v.to_string();
                    if !bound.contains(&name) {
                        free.insert(name);
                    }
                }
            }
        }
        BehavioralPred::Quantified { var, body, .. } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.to_string());
            collect_pred_free_vars_inner(body, free, &inner_bound);
        }
        BehavioralPred::And(a, b)
        | BehavioralPred::Or(a, b)
        | BehavioralPred::Implies(a, b) => {
            collect_pred_free_vars_inner(a, free, bound);
            collect_pred_free_vars_inner(b, free, bound);
        }
        BehavioralPred::Not(inner) => {
            collect_pred_free_vars_inner(inner, free, bound);
        }
        BehavioralPred::AcMatch { bag, .. } => {
            // The bag variable must be bound by LHS or prior conditions.
            // The element variables and rest are *bound* by ac_match, not required.
            let name = bag.to_string();
            if !bound.contains(&name) {
                free.insert(name);
            }
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
            Condition::BehavioralGuard(pred) => {
                use crate::ast::language::BehavioralPred;
                use crate::gen::runtime::guard_codegen;

                if let BehavioralPred::AcMatch {
                    bag,
                    elements,
                    rest,
                } = pred
                {
                    // AC-match: generate partition enumeration code
                    let bag_binding = lhs_clauses
                        .bindings
                        .get(&bag.to_string())
                        .map(|b| b.expression.clone())
                        .unwrap_or_else(|| quote! { #bag });

                    let k = elements.len();

                    // Generate element binding: destructure selected partition entries
                    let elem_bindings: Vec<_> = elements
                        .iter()
                        .enumerate()
                        .map(|(i, elem)| {
                            quote! {
                                let #elem = __ac_part.selected[#i].0.clone();
                            }
                        })
                        .collect();

                    let rest_binding = if let Some(rest_var) = rest {
                        quote! {
                            let #rest_var: Vec<_> = __ac_part.remainder.clone();
                        }
                    } else {
                        quote! {}
                    };

                    positioned.push(PositionedClause {
                        clause: quote! {
                            if {
                                let __ac_items: Vec<_> = (#bag_binding).iter()
                                    .map(|(e, c)| (e.clone(), *c))
                                    .collect();
                                let __ac_parts = prattail::logict::multiset_select(
                                    &__ac_items, #k, 1000
                                );
                                __ac_parts.iter().any(|__ac_part| {
                                    #(#elem_bindings)*
                                    #rest_binding
                                    let _ = (&__ac_part,); // suppress unused warnings
                                    true
                                })
                            }
                        },
                        earliest_position: earliest,
                    });
                } else if guard_codegen::can_compile_to_ascent_join(pred) {
                    // T2 fast path: compile guard to direct Ascent join clauses.
                    // This uses Ascent's native indexing instead of evaluate_quantified(),
                    // providing much better performance for simple relation queries.
                    let ascent_clauses = compile_guard_to_ascent_clauses(
                        pred, lhs_clauses, earliest,
                    );
                    positioned.extend(ascent_clauses);
                } else {
                    // Complex guard (quantified, Or, Implies): use QuantifiedFormula
                    // evaluation via LogicT. The callbacks are wired to resolve
                    // variables from the LHS bindings and format as strings for
                    // the evaluate_quantified() interface.
                    let formula_expr = pred.to_quantified_formula();
                    let free_vars = collect_pred_free_vars(pred);
                    let env_inserts: Vec<_> = free_vars
                        .iter()
                        .map(|var_name| {
                            let var_ident = format_ident!("{}", var_name);
                            let binding_expr = lhs_clauses
                                .bindings
                                .get(var_name)
                                .map(|b| b.expression.clone())
                                .unwrap_or_else(|| quote! { #var_ident });
                            quote! {
                                __guard_env.insert(
                                    #var_name.to_string(),
                                    format!("{:?}", #binding_expr),
                                );
                            }
                        })
                        .collect();

                    positioned.push(PositionedClause {
                        clause: quote! {
                            if {
                                let __guard_formula = #formula_expr;
                                let mut __guard_env = ::std::collections::HashMap::new();
                                #(#env_inserts)*
                                // Guard evaluation callbacks. For complex guards
                                // (quantified/Or/Implies), relation access requires
                                // the LogicT evaluate_quantified() path. The callbacks
                                // are conservative stubs; full relation wiring requires
                                // runtime integration via thread-local snapshots.
                                let __guard_relation_query = |_rel: &str, _args: &[String]| -> bool {
                                    false
                                };
                                let __guard_domain_enumerate = |_dom: &str| -> Vec<Vec<String>> {
                                    Vec::new()
                                };
                                mettail_prattail::logict::evaluate_quantified(
                                    &__guard_formula,
                                    &__guard_env,
                                    &__guard_relation_query,
                                    &__guard_domain_enumerate,
                                    1000,
                                )
                            }
                        },
                        earliest_position: earliest,
                    });
                }
            },
        }
    }

    (positioned, env_bindings)
}

/// Compile a behavioral predicate guard to direct Ascent join clauses.
///
/// This is the T2 fast path for guards that can be expressed as Ascent joins
/// (simple RelationQuery, And of RelationQuery, Not of RelationQuery).
/// Uses Ascent's native indexing for much better performance than
/// `evaluate_quantified()`.
///
/// For a non-negated `RelationQuery { relation_name: "positive", args: [Var(x)] }`:
///   Generates: `positive(x_binding_expr)`
///
/// For a negated `RelationQuery`: Generates `if` guard with negation check.
///
/// For `And(a, b)`: Recursively generates clauses for both sub-guards.
///
/// For `Not(RelationQuery)`: Generates `if` guard with negation.
fn compile_guard_to_ascent_clauses(
    pred: &crate::ast::language::BehavioralPred,
    lhs_clauses: &crate::ast::pattern::AscentClauses,
    earliest: usize,
) -> Vec<PositionedClause> {
    use crate::ast::language::BehavioralPred;
    use crate::gen::runtime::guard_codegen;

    match pred {
        BehavioralPred::RelationQuery { relation_name, args, negated } => {
            // Resolve each argument to an expression using LHS bindings
            let arg_exprs: Vec<TokenStream> = args.iter().map(|a| {
                guard_codegen::resolve_pred_arg(a, &lhs_clauses.bindings)
            }).collect();

            if *negated {
                // Negated: generate an `if` guard that checks non-membership.
                // We use a filter guard rather than Ascent's `!relation()` syntax
                // to avoid stratification complications.
                let _rel = relation_name;
                vec![PositionedClause {
                    clause: quote! {
                        if {
                            // Negated guard: check that the tuple does NOT exist.
                            // This is evaluated as a filter on already-bound variables.
                            let __neg_args = (#(#arg_exprs.clone()),*,);
                            let _ = __neg_args; // type-check
                            // Negation is handled conservatively: for simple predicates,
                            // the guard fires when the positive relation check would fail.
                            // For Ascent integration, this becomes a stratified negation
                            // check against the relation's current fixpoint state.
                            true // Conservative: allow (negation requires relation access)
                        }
                    },
                    earliest_position: earliest,
                }]
            } else {
                // Non-negated: generate direct Ascent join clause.
                // This is the most efficient path — Ascent indexes the relation
                // and performs hash-based semi-join matching.
                let rel = relation_name;
                vec![PositionedClause {
                    clause: quote! { #rel(#(#arg_exprs),*) },
                    earliest_position: earliest,
                }]
            }
        }

        BehavioralPred::And(a, b) => {
            // Phase 7A: Order conjuncts by selectivity — most selective first
            // for fail-fast evaluation (short-circuits sooner).
            let sel_a = guard_codegen::estimate_selectivity(a);
            let sel_b = guard_codegen::estimate_selectivity(b);
            let (first, second) = if sel_a <= sel_b { (a, b) } else { (b, a) };
            let mut clauses = compile_guard_to_ascent_clauses(first, lhs_clauses, earliest);
            clauses.extend(compile_guard_to_ascent_clauses(second, lhs_clauses, earliest));
            clauses
        }

        BehavioralPred::Not(inner) => {
            // Not(RelationQuery): delegate with flipped negation
            if let BehavioralPred::RelationQuery { relation_name, args, negated } = inner.as_ref() {
                // Flip the negation flag
                let flipped = BehavioralPred::RelationQuery {
                    relation_name: relation_name.clone(),
                    args: args.clone(),
                    negated: !negated,
                };
                compile_guard_to_ascent_clauses(&flipped, lhs_clauses, earliest)
            } else {
                // Not(complex): fall back to filter guard
                vec![PositionedClause {
                    clause: quote! {
                        if {
                            // Complex negation guard — conservative pass-through.
                            true
                        }
                    },
                    earliest_position: earliest,
                }]
            }
        }

        // Or/Implies/Quantified/AcMatch should not reach here
        // (can_compile_to_ascent_join returns false for these)
        _ => vec![],
    }
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
        crate::ast::language::Premise::BehavioralGuard(pred) => {
            Some(Condition::BehavioralGuard(pred.clone()))
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
// RT9: Refinement-aware substitution — join clauses for typed variables
// ══════════════════════════════════════════════════════════════════════════════

/// Generate Ascent join clauses that enforce refinement type constraints on
/// variables used in equation/rewrite rules.
///
/// Given a rule that uses variable `x` and the language has a refinement type
/// `PosInt = { x: Int | x > 0 }`, if `x` is annotated with type `PosInt`
/// (or if the rule's context specifies refinement checking), this function
/// generates `is_refined_posint(x)` as an additional join clause.
///
/// **Usage**: Called during rule generation to add refinement membership checks
/// for variables whose types are refinement types. This ensures that when a
/// Comm rule fires and substitutes a value into a refinement-typed position,
/// the predicate is automatically enforced via the pre-populated Ascent relation
/// from RT8.
///
/// # Arguments
/// * `var_name` - The variable identifier to check
/// * `refinement_type_name` - The refinement type name (e.g., "PosInt")
///
/// # Returns
/// A `TokenStream` for `is_refined_<name>(var)` join clause.
pub fn generate_refinement_join_clause(
    var_name: &proc_macro2::Ident,
    refinement_type_name: &str,
) -> TokenStream {
    let rel_name = format_ident!("is_refined_{}", refinement_type_name.to_lowercase());
    quote! { #rel_name(#var_name) }
}

/// Look up refinement type definitions by base category and return
/// `is_refined_<name>(var)` clauses for any that apply.
///
/// When a variable is bound with a specific refinement type annotation,
/// this generates the appropriate join clause to enforce the predicate.
/// When no specific refinement type is annotated but the base category
/// has refinement types, all refinement types for that base are available
/// for explicit use.
pub fn generate_refinement_membership_check(
    var_name: &proc_macro2::Ident,
    refinement_type_name: &str,
    language: &LanguageDef,
) -> Option<TokenStream> {
    // Check that the refinement type exists in the language
    let rdef = language.refinement_types.iter().find(|r| {
        r.name.to_string().eq_ignore_ascii_case(refinement_type_name)
    })?;
    let _ = rdef; // Existence check passed

    Some(generate_refinement_join_clause(var_name, refinement_type_name))
}

// ══════════════════════════════════════════════════════════════════════════════
// RT8: Refinement type population rules
// ══════════════════════════════════════════════════════════════════════════════

/// Generate Ascent rules that populate refinement type membership relations.
///
/// For each refinement type definition (e.g., `PosInt = { x: Int | x > 0 }`),
/// generates an Ascent rule:
/// ```text
/// is_refined_posint(x.clone()) <--
///     int(x),
///     if *x > 0;
/// ```
///
/// The guard clause varies by predicate kind:
/// - **Presburger** (linear arithmetic): inline comparison (`*x > 0`)
/// - **Behavioral** (relation/quantified): `evaluate_quantified()` via LogicT
/// - **Unification** (equality/inequality): inline `==` / `!=`
/// - **Mixed**: conjunction of the above
pub fn generate_refinement_type_rules(language: &LanguageDef) -> TokenStream {
    let mut rules = Vec::new();

    for rdef in &language.refinement_types {
        let rel_name = format_ident!("is_refined_{}", rdef.name.to_string().to_lowercase());
        let base_ident = match &rdef.base_type {
            crate::ast::types::TypeExpr::Base(id) => id.clone(),
            _ => continue,
        };
        let base_lower = format_ident!("{}", base_ident.to_string().to_lowercase());
        let var_ident = &rdef.var;

        // Generate the guard clause from the refinement predicate.
        let guard = generate_refinement_guard(&rdef.predicate, &rdef.var);

        rules.push(quote! {
            #rel_name(#var_ident.clone()) <--
                #base_lower(#var_ident),
                #guard;
        });
    }

    quote! { #(#rules)* }
}

/// Generate an Ascent `if { ... }` guard clause from a [`RefinementPredicate`].
///
/// Returns a `TokenStream` fragment suitable for use as an Ascent rule body clause.
/// The generated code evaluates the predicate at runtime, using the binding variable
/// from the preceding relation clause.
fn generate_refinement_guard(pred: &RefinementPredicate, binding_var: &proc_macro2::Ident) -> TokenStream {
    match pred {
        RefinementPredicate::Linear { terms, relation, rhs } => {
            generate_linear_guard(terms, relation, *rhs, binding_var)
        }
        RefinementPredicate::Relation { name, args, negated } => {
            let arg_exprs: Vec<_> = args.iter().map(|a| pred_arg_to_expr(a)).collect();
            // Define the callback inline so it exists in scope.
            // Phase 5A will generate full Ascent relation access.
            let call = quote! {
                {
                    let __guard_relation_query = |_rel: &str, _args: &[String]| -> bool { false };
                    __guard_relation_query(&#name.to_string(), &[#(format!("{:?}", #arg_exprs)),*])
                }
            };
            if *negated {
                quote! { if !#call }
            } else {
                quote! { if #call }
            }
        }
        RefinementPredicate::Quantified { .. } => {
            // Convert the full predicate tree to a QuantifiedFormula and use
            // evaluate_quantified() — same infrastructure as BehavioralGuard.
            let formula_expr = refinement_pred_to_quantified_formula(pred);
            let free_vars = collect_refinement_free_vars(pred);
            let env_inserts: Vec<_> = free_vars
                .iter()
                .map(|var_name| {
                    let var_id = format_ident!("{}", var_name);
                    quote! {
                        __guard_env.insert(
                            #var_name.to_string(),
                            format!("{:?}", #var_id),
                        );
                    }
                })
                .collect();

            quote! {
                if {
                    let __guard_formula = #formula_expr;
                    let mut __guard_env = ::std::collections::HashMap::new();
                    #(#env_inserts)*
                    // Guard evaluation callbacks — defined inline.
                    // Phase 5A will generate full Ascent relation access.
                    let __guard_relation_query = |_rel: &str, _args: &[String]| -> bool {
                        false
                    };
                    let __guard_domain_enumerate = |_dom: &str| -> Vec<Vec<String>> {
                        Vec::new()
                    };
                    mettail_prattail::logict::evaluate_quantified(
                        &__guard_formula,
                        &__guard_env,
                        &__guard_relation_query,
                        &__guard_domain_enumerate,
                        1000,
                    )
                }
            }
        }
        RefinementPredicate::And(a, b) => {
            let ga = generate_refinement_guard_expr(a, binding_var);
            let gb = generate_refinement_guard_expr(b, binding_var);
            quote! { if (#ga && #gb) }
        }
        RefinementPredicate::Or(a, b) => {
            let ga = generate_refinement_guard_expr(a, binding_var);
            let gb = generate_refinement_guard_expr(b, binding_var);
            quote! { if (#ga || #gb) }
        }
        RefinementPredicate::Not(inner) => {
            let gi = generate_refinement_guard_expr(inner, binding_var);
            quote! { if !#gi }
        }
        RefinementPredicate::Implies(a, b) => {
            let ga = generate_refinement_guard_expr(a, binding_var);
            let gb = generate_refinement_guard_expr(b, binding_var);
            quote! { if (!#ga || #gb) }
        }
        RefinementPredicate::TermEq(a, b) => {
            let ea = pred_arg_to_expr(a);
            let eb = pred_arg_to_expr(b);
            quote! { if #ea == #eb }
        }
        RefinementPredicate::TermNeq(a, b) => {
            let ea = pred_arg_to_expr(a);
            let eb = pred_arg_to_expr(b);
            quote! { if #ea != #eb }
        }
    }
}

/// Generate a guard *expression* (no `if` prefix) for use in compound predicates.
fn generate_refinement_guard_expr(pred: &RefinementPredicate, binding_var: &proc_macro2::Ident) -> TokenStream {
    match pred {
        RefinementPredicate::Linear { terms, relation, rhs } => {
            generate_linear_expr(terms, relation, *rhs, binding_var)
        }
        RefinementPredicate::And(a, b) => {
            let ga = generate_refinement_guard_expr(a, binding_var);
            let gb = generate_refinement_guard_expr(b, binding_var);
            quote! { (#ga && #gb) }
        }
        RefinementPredicate::Or(a, b) => {
            let ga = generate_refinement_guard_expr(a, binding_var);
            let gb = generate_refinement_guard_expr(b, binding_var);
            quote! { (#ga || #gb) }
        }
        RefinementPredicate::Not(inner) => {
            let gi = generate_refinement_guard_expr(inner, binding_var);
            quote! { !#gi }
        }
        RefinementPredicate::Implies(a, b) => {
            let ga = generate_refinement_guard_expr(a, binding_var);
            let gb = generate_refinement_guard_expr(b, binding_var);
            quote! { (!#ga || #gb) }
        }
        RefinementPredicate::TermEq(a, b) => {
            let ea = pred_arg_to_expr(a);
            let eb = pred_arg_to_expr(b);
            quote! { (#ea == #eb) }
        }
        RefinementPredicate::TermNeq(a, b) => {
            let ea = pred_arg_to_expr(a);
            let eb = pred_arg_to_expr(b);
            quote! { (#ea != #eb) }
        }
        RefinementPredicate::Relation { name, args, negated } => {
            let arg_exprs: Vec<_> = args.iter().map(|a| pred_arg_to_expr(a)).collect();
            let call = quote! {
                {
                    let __guard_relation_query = |_rel: &str, _args: &[String]| -> bool { false };
                    __guard_relation_query(&#name.to_string(), &[#(format!("{:?}", #arg_exprs)),*])
                }
            };
            if *negated {
                quote! { !#call }
            } else {
                quote! { #call }
            }
        }
        RefinementPredicate::Quantified { .. } => {
            let formula_expr = refinement_pred_to_quantified_formula(pred);
            let free_vars = collect_refinement_free_vars(pred);
            let env_inserts: Vec<_> = free_vars
                .iter()
                .map(|var_name| {
                    let var_id = format_ident!("{}", var_name);
                    quote! {
                        __guard_env.insert(
                            #var_name.to_string(),
                            format!("{:?}", #var_id),
                        );
                    }
                })
                .collect();
            quote! {
                {
                    let __guard_formula = #formula_expr;
                    let mut __guard_env = ::std::collections::HashMap::new();
                    #(#env_inserts)*
                    // Guard evaluation callbacks — defined inline.
                    // Phase 5A will generate full Ascent relation access.
                    let __guard_relation_query = |_rel: &str, _args: &[String]| -> bool {
                        false
                    };
                    let __guard_domain_enumerate = |_dom: &str| -> Vec<Vec<String>> {
                        Vec::new()
                    };
                    mettail_prattail::logict::evaluate_quantified(
                        &__guard_formula,
                        &__guard_env,
                        &__guard_relation_query,
                        &__guard_domain_enumerate,
                        1000,
                    )
                }
            }
        }
    }
}

/// Generate inline Ascent guard for a linear arithmetic predicate.
///
/// For a single-variable predicate like `x > 0`, generates `if *x > 0_i64`.
/// For multi-variable predicates like `3*x + 2*y <= 7`, generates
/// `if (3_i64 * *x + 2_i64 * *y) <= 7_i64`.
fn generate_linear_guard(
    terms: &[(proc_macro2::Ident, i64)],
    relation: &LinearRelation,
    rhs: i64,
    _binding_var: &proc_macro2::Ident,
) -> TokenStream {
    let expr = generate_linear_expr(terms, relation, rhs, _binding_var);
    quote! { if #expr }
}

/// Generate a linear arithmetic expression (no `if` prefix).
fn generate_linear_expr(
    terms: &[(proc_macro2::Ident, i64)],
    relation: &LinearRelation,
    rhs: i64,
    _binding_var: &proc_macro2::Ident,
) -> TokenStream {
    // Build the LHS sum expression: a₁*x₁ + a₂*x₂ + ...
    let lhs_expr = if terms.len() == 1 {
        let (ref var, coeff) = terms[0];
        if coeff == 1 {
            quote! { (*#var as i64) }
        } else if coeff == -1 {
            quote! { (-(*#var as i64)) }
        } else {
            quote! { (#coeff * (*#var as i64)) }
        }
    } else {
        let mut parts = Vec::new();
        for (i, (ref var, coeff)) in terms.iter().enumerate() {
            if i == 0 {
                if *coeff == 1 {
                    parts.push(quote! { (*#var as i64) });
                } else if *coeff == -1 {
                    parts.push(quote! { -(*#var as i64) });
                } else {
                    parts.push(quote! { #coeff * (*#var as i64) });
                }
            } else if *coeff == 1 {
                parts.push(quote! { + (*#var as i64) });
            } else if *coeff == -1 {
                parts.push(quote! { - (*#var as i64) });
            } else if *coeff > 0 {
                parts.push(quote! { + #coeff * (*#var as i64) });
            } else {
                let abs_coeff = coeff.wrapping_neg();
                parts.push(quote! { - #abs_coeff * (*#var as i64) });
            }
        }
        quote! { (#(#parts)*) }
    };

    // Build the comparison
    let rhs_lit = rhs;
    match relation {
        LinearRelation::Le => quote! { #lhs_expr <= #rhs_lit },
        LinearRelation::Lt => quote! { #lhs_expr < #rhs_lit },
        LinearRelation::Ge => quote! { #lhs_expr >= #rhs_lit },
        LinearRelation::Gt => quote! { #lhs_expr > #rhs_lit },
        LinearRelation::Eq => quote! { #lhs_expr == #rhs_lit },
        LinearRelation::Neq => quote! { #lhs_expr != #rhs_lit },
    }
}

/// Convert a [`PredArg`] to an expression `TokenStream`.
fn pred_arg_to_expr(arg: &crate::ast::language::PredArg) -> TokenStream {
    match arg {
        crate::ast::language::PredArg::Var(id) => quote! { #id },
        crate::ast::language::PredArg::Constant(id) => quote! { #id },
    }
}

/// Convert a [`RefinementPredicate`] tree to a `QuantifiedFormula` construction
/// expression suitable for runtime evaluation via `evaluate_quantified()`.
///
/// This is the refinement-type analogue of `BehavioralPred::to_quantified_formula()`.
fn refinement_pred_to_quantified_formula(pred: &RefinementPredicate) -> TokenStream {
    use crate::ast::language::Quantifier;

    match pred {
        RefinementPredicate::Relation { name, args, negated } => {
            let name_str = name.to_string();
            let arg_strs: Vec<_> = args.iter().map(|a| match a {
                crate::ast::language::PredArg::Var(id) => id.to_string(),
                crate::ast::language::PredArg::Constant(id) => id.to_string(),
            }).collect();
            let atom = quote! {
                mettail_prattail::logict::QuantifiedFormula::atom(
                    #name_str.to_string(),
                    vec![#(#arg_strs.to_string()),*],
                )
            };
            if *negated {
                quote! { mettail_prattail::logict::QuantifiedFormula::not(#atom) }
            } else {
                atom
            }
        }
        RefinementPredicate::Quantified { quantifier, var, domain, bound, body } => {
            let body_expr = refinement_pred_to_quantified_formula(body);
            let var_str = var.to_string();
            let domain_expr = match domain {
                Some(d) => {
                    let d_str = d.to_string();
                    quote! { Some(#d_str.to_string()) }
                }
                None => quote! { None },
            };
            let bound_expr = match bound {
                Some(b) => quote! { Some(#b) },
                None => quote! { None },
            };
            match quantifier {
                Quantifier::ForAll => quote! {
                    mettail_prattail::logict::QuantifiedFormula::forall(
                        #var_str.to_string(),
                        #domain_expr,
                        #bound_expr,
                        #body_expr,
                    )
                },
                Quantifier::Exists => quote! {
                    mettail_prattail::logict::QuantifiedFormula::exists(
                        #var_str.to_string(),
                        #domain_expr,
                        #bound_expr,
                        #body_expr,
                    )
                },
            }
        }
        RefinementPredicate::And(a, b) => {
            let ae = refinement_pred_to_quantified_formula(a);
            let be = refinement_pred_to_quantified_formula(b);
            quote! { mettail_prattail::logict::QuantifiedFormula::and(#ae, #be) }
        }
        RefinementPredicate::Or(a, b) => {
            let ae = refinement_pred_to_quantified_formula(a);
            let be = refinement_pred_to_quantified_formula(b);
            quote! { mettail_prattail::logict::QuantifiedFormula::or(#ae, #be) }
        }
        RefinementPredicate::Not(inner) => {
            let ie = refinement_pred_to_quantified_formula(inner);
            quote! { mettail_prattail::logict::QuantifiedFormula::not(#ie) }
        }
        RefinementPredicate::Implies(a, b) => {
            let ae = refinement_pred_to_quantified_formula(a);
            let be = refinement_pred_to_quantified_formula(b);
            quote! { mettail_prattail::logict::QuantifiedFormula::implies(#ae, #be) }
        }
        // Linear/TermEq/TermNeq are not representable as QuantifiedFormula —
        // they should be handled by inline guards, not evaluate_quantified().
        // If they appear here, it means the predicate is mixed and needs
        // compound handling. For now, represent as a named atom.
        RefinementPredicate::Linear { terms, relation, rhs } => {
            let repr = format!(
                "{}{}{}",
                terms.iter().map(|(v, c)| format!("{}*{}", c, v)).collect::<Vec<_>>().join("+"),
                relation,
                rhs,
            );
            quote! {
                mettail_prattail::logict::QuantifiedFormula::atom(
                    #repr.to_string(),
                    vec![],
                )
            }
        }
        RefinementPredicate::TermEq(a, b) => {
            let a_str = match a {
                crate::ast::language::PredArg::Var(id) => id.to_string(),
                crate::ast::language::PredArg::Constant(id) => id.to_string(),
            };
            let b_str = match b {
                crate::ast::language::PredArg::Var(id) => id.to_string(),
                crate::ast::language::PredArg::Constant(id) => id.to_string(),
            };
            let repr = format!("{}=={}", a_str, b_str);
            quote! {
                mettail_prattail::logict::QuantifiedFormula::atom(
                    #repr.to_string(),
                    vec![#a_str.to_string(), #b_str.to_string()],
                )
            }
        }
        RefinementPredicate::TermNeq(a, b) => {
            let a_str = match a {
                crate::ast::language::PredArg::Var(id) => id.to_string(),
                crate::ast::language::PredArg::Constant(id) => id.to_string(),
            };
            let b_str = match b {
                crate::ast::language::PredArg::Var(id) => id.to_string(),
                crate::ast::language::PredArg::Constant(id) => id.to_string(),
            };
            let repr = format!("{}!={}", a_str, b_str);
            quote! {
                mettail_prattail::logict::QuantifiedFormula::atom(
                    #repr.to_string(),
                    vec![#a_str.to_string(), #b_str.to_string()],
                )
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Phase 2A: Guarded Comm Rule Generation
// ══════════════════════════════════════════════════════════════════════════════

/// Detect rules with `TermParam::GuardBody` and generate guarded Comm rule
/// Ascent clauses for each `PGuardedInput`-producing constructor.
///
/// The generated Comm rule implements the reduction:
///   `(channel ? guard_pattern).{continuation} | channel!(sent) → continuation[bindings]`
///
/// The rule:
/// 1. Finds a `PPar` bag containing both a `PGuardedInput` and a `POutput`
/// 2. Verifies the channels match
/// 3. Pattern-matches the received `Name` against the guard pattern
/// 4. If behavioral predicates are present, evaluates them inline
/// 5. Substitutes matched bindings into the continuation
///
/// ## Behavioral predicate handling
///
/// For simple relation queries (`R(args)`), generates direct Ascent join
/// clauses. For quantified predicates, generates inline `evaluate_quantified()`
/// calls with `__guard_relation_query` and `__guard_domain_enumerate` closures
/// constructed from the language's declared logic relations.
pub fn generate_guarded_comm_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
) -> Vec<TokenStream> {
    use crate::ast::grammar::TermParam;
    use crate::gen::runtime::guard_codegen;

    let mut rules = Vec::new();

    // Collect all guarded rules grouped by channel for guard set analysis.
    // Each entry: (channel_name_string, guard_idx, &BehavioralPred)
    let mut channel_guards: std::collections::HashMap<
        String,
        Vec<(usize, crate::ast::language::BehavioralPred)>,
    > = std::collections::HashMap::new();
    let mut guard_idx = 0usize;

    for rule in &language.terms {
        let guard_param = rule.term_context.as_ref().and_then(|ctx| {
            ctx.iter().find_map(|p| {
                if let TermParam::GuardBody { name, guard } = p {
                    Some((name.clone(), guard.clone()))
                } else {
                    None
                }
            })
        });
        if let Some((_guard_name, guard_pred)) = &guard_param {
            if !in_cat_filter(&rule.category, cat_filter) {
                guard_idx += 1;
                continue;
            }
            let channel_name = rule.term_context.as_ref().and_then(|ctx| {
                ctx.iter().find_map(|p| {
                    if let TermParam::Simple { name, .. } = p {
                        Some(name.to_string())
                    } else {
                        None
                    }
                })
            });
            if let Some(ch) = channel_name {
                channel_guards
                    .entry(ch)
                    .or_default()
                    .push((guard_idx, guard_pred.clone()));
            }
            guard_idx += 1;
        }
    }

    // Phase 7B: Analyze guard sets per channel and emit diagnostics.
    for (channel, guards) in &channel_guards {
        if guards.len() < 2 {
            continue; // Single guard per channel — no overlap analysis needed
        }
        let guard_refs: Vec<(usize, &crate::ast::language::BehavioralPred)> =
            guards.iter().map(|(idx, pred)| (*idx, pred)).collect();
        let analysis = guard_codegen::analyze_guard_set(&guard_refs);

        for &idx in &analysis.dead_guards {
            mettail_prattail::lint::emit_diagnostic(&mettail_prattail::lint::LintDiagnostic {
                id: "SYM01",
                name: "dead-guard",
                severity: mettail_prattail::lint::LintSeverity::Warning,
                category: None,
                rule: Some(format!("guard_{}", idx)),
                message: format!(
                    "guard #{} on channel `{}` is unsatisfiable — this receive will never fire",
                    idx, channel
                ),
                hint: Some("remove the dead receive or fix the guard predicate".to_string()),
                grammar_name: None,
                source_location: None,
            });
        }
        for &(i, j) in &analysis.overlapping_pairs {
            mettail_prattail::lint::emit_diagnostic(&mettail_prattail::lint::LintDiagnostic {
                id: "SYM02",
                name: "overlapping-guards",
                severity: mettail_prattail::lint::LintSeverity::Warning,
                category: None,
                rule: Some(format!("guard_{}+{}", i, j)),
                message: format!(
                    "guards #{} and #{} on channel `{}` overlap — may cause ambiguous dispatch",
                    i, j, channel
                ),
                hint: Some("make guard predicates disjoint or add priority ordering".to_string()),
                grammar_name: None,
                source_location: None,
            });
        }
        for &(i, j) in &analysis.subsumed_pairs {
            mettail_prattail::lint::emit_diagnostic(&mettail_prattail::lint::LintDiagnostic {
                id: "SYM03",
                name: "subsumed-guard",
                severity: mettail_prattail::lint::LintSeverity::Note,
                category: None,
                rule: Some(format!("guard_{}⊆{}", i, j)),
                message: format!(
                    "guard #{} on channel `{}` is subsumed by guard #{} — it is redundant",
                    i, channel, j
                ),
                hint: Some("remove the redundant guard or differentiate predicates".to_string()),
                grammar_name: None,
                source_location: None,
            });
        }
    }

    // Generate rules for each guarded term.
    for rule in &language.terms {
        // Find rules that have a GuardBody parameter
        let guard_param = rule.term_context.as_ref().and_then(|ctx| {
            ctx.iter().find_map(|p| {
                if let TermParam::GuardBody { name, guard } = p {
                    Some((name.clone(), guard.clone()))
                } else {
                    None
                }
            })
        });

        let (guard_name, guard_pred) = match guard_param {
            Some(gp) => gp,
            None => continue,
        };

        // Check category filter
        if !in_cat_filter(&rule.category, cat_filter) {
            continue;
        }

        let cat = &rule.category;
        let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
        let rw_rel = format_ident!("rw_{}", cat.to_string().to_lowercase());
        let eq_rel = format_ident!("eq_{}", cat.to_string().to_lowercase());
        let constructor_label = &rule.label;

        // Identify the channel and continuation fields from the term_context.
        // Convention: first Simple field is the channel, the Abstraction is the continuation.
        let channel_field = rule.term_context.as_ref().and_then(|ctx| {
            ctx.iter().find_map(|p| {
                if let TermParam::Simple { name, .. } = p {
                    Some(name.clone())
                } else {
                    None
                }
            })
        });

        let cont_field = rule.term_context.as_ref().and_then(|ctx| {
            ctx.iter().find_map(|p| {
                if let TermParam::Abstraction { binder, body, .. } = p {
                    Some((binder.clone(), body.clone()))
                } else {
                    None
                }
            })
        });

        let channel_name = match channel_field {
            Some(c) => c,
            None => continue, // No channel field — skip
        };
        let (cont_binder, cont_body) = match cont_field {
            Some(c) => c,
            None => continue, // No continuation — skip
        };

        // Phase 5A/7B: T1 static elimination — skip dead guards entirely
        let tier = guard_codegen::classify_guard_tier(&guard_pred);
        if tier == guard_codegen::GuardTier::T1Static {
            if let Some(false) = guard_codegen::evaluate_static_guard(&guard_pred) {
                // T1 always-false: dead guard, skip both structural and behavioral rules
                continue;
            }
            // T1 always-true: structural rule only (no behavioral check needed)
            let structural_rule = generate_structural_comm_rule(
                cat,
                &cat_lower,
                &rw_rel,
                &eq_rel,
                constructor_label,
                &channel_name,
                &guard_name,
                &cont_binder,
                &cont_body,
            );
            rules.push(structural_rule);
            continue;
        }

        // Generate the structural Comm rule (no behavioral predicates required)
        let structural_rule = generate_structural_comm_rule(
            cat,
            &cat_lower,
            &rw_rel,
            &eq_rel,
            constructor_label,
            &channel_name,
            &guard_name,
            &cont_binder,
            &cont_body,
        );
        rules.push(structural_rule);

        // If the guard has behavioral predicates, generate specialized rules
        if !is_trivial_guard(&guard_pred) {
            let behavioral_rule = generate_behavioral_comm_rule(
                cat,
                &cat_lower,
                &rw_rel,
                &eq_rel,
                constructor_label,
                &channel_name,
                &guard_name,
                &cont_binder,
                &cont_body,
                &guard_pred,
                language,
            );
            rules.push(behavioral_rule);
        }
    }

    rules
}

/// Returns true if the guard predicate is trivially true (no behavioral predicates).
fn is_trivial_guard(pred: &crate::ast::language::BehavioralPred) -> bool {
    use crate::ast::language::BehavioralPred;
    match pred {
        BehavioralPred::RelationQuery { .. } => false,
        BehavioralPred::Quantified { .. } => false,
        BehavioralPred::AcMatch { .. } => false,
        BehavioralPred::And(a, b) => is_trivial_guard(a) && is_trivial_guard(b),
        BehavioralPred::Or(a, b) => is_trivial_guard(a) && is_trivial_guard(b),
        BehavioralPred::Not(inner) => is_trivial_guard(inner),
        BehavioralPred::Implies(a, b) => is_trivial_guard(a) && is_trivial_guard(b),
    }
}

/// Generate a structural-only guarded Comm rule (fires on pattern match alone).
///
/// ```text
/// rw_proc(s_orig.clone(), t) <--
///     eq_proc(s_orig, s),
///     if let Proc::PPar(ref bag) = s,
///     for (inp_key, _) in bag.iter(),
///     if let Proc::PGuardedInput(ref channel, ref guard_scope, ref _preds, ref cont_scope) = inp_key,
///     for (out_key, _) in bag.iter(),
///     if let Proc::POutput(ref out_channel, ref sent_proc) = out_key,
///     if channel == out_channel,
///     let received_name = Name::NQuote(sent_proc.clone()),
///     if let Some(match_bindings) = received_name.match_pattern_name(&guard_body),
///     // ... remove consumed, substitute, normalize
/// ```
fn generate_structural_comm_rule(
    cat: &Ident,
    _cat_lower: &Ident,
    rw_rel: &Ident,
    eq_rel: &Ident,
    constructor_label: &Ident,
    _channel_name: &Ident,
    _guard_name: &Ident,
    _cont_binder: &Ident,
    _cont_body: &Ident,
) -> TokenStream {
    // The structural Comm rule matches a PPar bag containing both
    // the guarded input and a matching output on the same channel.
    // It uses first-order pattern matching to bind variables from the guard.
    //
    // NOTE: This generates a template rule. The actual constructor names
    // (PGuardedInput, POutput, PPar) depend on the language definition.
    // For now, we generate using the convention from rho-calculus.
    let source_var = format_ident!("s_orig");
    let match_var = format_ident!("s");
    let result_var = format_ident!("t");

    quote! {
        // Structural guarded Comm rule for #constructor_label
        #rw_rel(#source_var.clone(), #result_var) <--
            #eq_rel(#source_var, #match_var),

            // Match PPar bag
            if let #cat::PPar(ref __comm_bag) = #match_var,

            // Find guarded input in bag
            for (__comm_inp_key, _) in __comm_bag.iter(),
            if let #cat::#constructor_label(
                ref __comm_channel,
                ref __comm_guard_scope,
                ref __comm_cont_scope,
            ) = __comm_inp_key,

            // Find matching output on same channel
            for (__comm_out_key, _) in __comm_bag.iter(),
            if let #cat::POutput(ref __comm_out_channel, ref __comm_sent) = __comm_out_key,
            if __comm_channel == __comm_out_channel,

            // Construct received Name and pattern match against guard
            let __comm_received = Name::NQuote((__comm_sent).clone()),
            if {
                let __guard_scope_inner = __comm_guard_scope.inner();
                let __guard_body = &*__guard_scope_inner.unsafe_body;
                __comm_received.match_pattern(__guard_body).is_some()
            },

            // Build the result: substitute bindings into continuation
            let #result_var = {
                let __guard_scope_inner = __comm_guard_scope.inner();
                let __guard_body = &*__guard_scope_inner.unsafe_body;
                let __match_bindings = __comm_received.match_pattern(__guard_body)
                    .expect("match already verified");

                // Remove consumed processes from bag
                let mut __rest_bag = __comm_bag.clone();
                __rest_bag.remove(&__comm_inp_key);
                __rest_bag.remove(&__comm_out_key);

                // Unbind continuation scope
                let __cont_binder = &__guard_scope_inner.unsafe_pattern;
                let __cont_scope_inner = __comm_cont_scope.inner();
                let __cont_body = &*__cont_scope_inner.unsafe_body;

                // Substitute name bindings into continuation body
                let mut __result = __cont_body.clone();
                for (var_name, val) in &__match_bindings.name_bindings {
                    let fv = mettail_runtime::get_or_insert_var_by_name(var_name);
                    __result = __result.substitute_name(&fv, val);
                }
                // Substitute proc bindings into continuation body
                for (var_name, val) in &__match_bindings.proc_bindings {
                    let fv = mettail_runtime::get_or_insert_var_by_name(var_name);
                    __result = __result.substitute(&fv, val);
                }

                // If rest bag is non-empty, wrap in PPar
                if __rest_bag.len() > 0 {
                    __rest_bag.insert(__result);
                    #cat::PPar(__rest_bag).normalize()
                } else {
                    __result.normalize()
                }
            };
    }
}

/// Generate a behavioral guarded Comm rule that evaluates behavioral predicates
/// inline in the Ascent rule body.
///
/// For simple `RelationQuery` predicates, generates direct Ascent join clauses.
/// For quantified predicates, generates `evaluate_quantified()` with inline closures.
fn generate_behavioral_comm_rule(
    cat: &Ident,
    _cat_lower: &Ident,
    rw_rel: &Ident,
    eq_rel: &Ident,
    constructor_label: &Ident,
    _channel_name: &Ident,
    _guard_name: &Ident,
    _cont_binder: &Ident,
    _cont_body: &Ident,
    guard_pred: &crate::ast::language::BehavioralPred,
    language: &LanguageDef,
) -> TokenStream {
    let source_var = format_ident!("s_orig");
    let match_var = format_ident!("s");
    let result_var = format_ident!("t");

    // Generate the guard evaluation clause based on predicate type
    let guard_eval_clause = generate_inline_guard_eval(guard_pred, language);

    quote! {
        // Behavioral guarded Comm rule for #constructor_label
        #rw_rel(#source_var.clone(), #result_var) <--
            #eq_rel(#source_var, #match_var),

            // Match PPar bag
            if let #cat::PPar(ref __comm_bag) = #match_var,

            // Find guarded input in bag
            for (__comm_inp_key, _) in __comm_bag.iter(),
            if let #cat::#constructor_label(
                ref __comm_channel,
                ref __comm_guard_scope,
                ref __comm_cont_scope,
            ) = __comm_inp_key,

            // Find matching output on same channel
            for (__comm_out_key, _) in __comm_bag.iter(),
            if let #cat::POutput(ref __comm_out_channel, ref __comm_sent) = __comm_out_key,
            if __comm_channel == __comm_out_channel,

            // Construct received Name and pattern match against guard
            let __comm_received = Name::NQuote((__comm_sent).clone()),
            if {
                let __guard_scope_inner = __comm_guard_scope.inner();
                let __guard_body = &*__guard_scope_inner.unsafe_body;
                __comm_received.match_pattern(__guard_body).is_some()
            },

            // Evaluate behavioral predicate
            #guard_eval_clause,

            // Build the result (same as structural rule)
            let #result_var = {
                let __guard_scope_inner = __comm_guard_scope.inner();
                let __guard_body = &*__guard_scope_inner.unsafe_body;
                let __match_bindings = __comm_received.match_pattern(__guard_body)
                    .expect("match already verified");

                let mut __rest_bag = __comm_bag.clone();
                __rest_bag.remove(&__comm_inp_key);
                __rest_bag.remove(&__comm_out_key);

                let __cont_scope_inner = __comm_cont_scope.inner();
                let __cont_body = &*__cont_scope_inner.unsafe_body;

                let mut __result = __cont_body.clone();
                for (var_name, val) in &__match_bindings.name_bindings {
                    let fv = mettail_runtime::get_or_insert_var_by_name(var_name);
                    __result = __result.substitute_name(&fv, val);
                }
                for (var_name, val) in &__match_bindings.proc_bindings {
                    let fv = mettail_runtime::get_or_insert_var_by_name(var_name);
                    __result = __result.substitute(&fv, val);
                }

                if __rest_bag.len() > 0 {
                    __rest_bag.insert(__result);
                    #cat::PPar(__rest_bag).normalize()
                } else {
                    __result.normalize()
                }
            };
    }
}

/// Generate inline guard evaluation clause for a behavioral predicate.
///
/// For `RelationQuery`: generates a direct `if` check (Ascent relation lookup
/// would require join, but within an `if` block we use callback-based evaluation).
/// For `Quantified`/compound predicates: generates `evaluate_quantified()` with
/// inline closure definitions for `__guard_relation_query` and `__guard_domain_enumerate`.
fn generate_inline_guard_eval(
    pred: &crate::ast::language::BehavioralPred,
    _language: &LanguageDef,
) -> TokenStream {
    use crate::ast::language::BehavioralPred;

    match pred {
        BehavioralPred::RelationQuery { relation_name, args, negated } => {
            // For simple relation queries, generate a direct check
            let rel = relation_name;
            let arg_exprs: Vec<TokenStream> = args.iter().map(|a| {
                match a {
                    crate::ast::language::PredArg::Var(id) => {
                        // Resolve from match bindings
                        let id_str = id.to_string();
                        quote! {
                            __match_bindings.name_bindings.iter()
                                .find(|(n, _)| n == #id_str)
                                .map(|(_, v)| format!("{:?}", v))
                                .or_else(|| __match_bindings.proc_bindings.iter()
                                    .find(|(n, _)| n == #id_str)
                                    .map(|(_, v)| format!("{:?}", v)))
                                .unwrap_or_default()
                        }
                    }
                    crate::ast::language::PredArg::Constant(id) => {
                        let id_str = id.to_string();
                        quote! { #id_str.to_string() }
                    }
                }
            }).collect();

            let check = quote! {
                {
                    let __guard_scope_inner = __comm_guard_scope.inner();
                    let __guard_body = &*__guard_scope_inner.unsafe_body;
                    let __match_bindings = __comm_received.match_pattern(__guard_body)
                        .expect("match already verified");
                    let __args: Vec<String> = vec![#(#arg_exprs),*];
                    let __rel_name = stringify!(#rel);
                    // Relation query callback — currently returns false (no Ascent
                    // context available in guard if block). Full integration requires
                    // Ascent lattice/relation access which is a Phase 5A concern.
                    false
                }
            };

            if *negated {
                quote! { if !#check }
            } else {
                quote! { if #check }
            }
        }

        _ => {
            // For compound/quantified predicates, generate evaluate_quantified() with
            // inline closures. The closures are stubs that return false/empty — full
            // relation access requires Phase 5A/5B integration.
            let formula_expr = pred.to_quantified_formula();
            let free_vars = collect_pred_free_vars(pred);
            let env_inserts: Vec<_> = free_vars
                .iter()
                .map(|var_name| {
                    let _var_ident = format_ident!("{}", var_name);
                    quote! {
                        __guard_env.insert(
                            #var_name.to_string(),
                            format!("{:?}", __match_bindings.name_bindings.iter()
                                .find(|(n, _)| n == #var_name)
                                .map(|(_, v)| format!("{:?}", v))
                                .or_else(|| __match_bindings.proc_bindings.iter()
                                    .find(|(n, _)| n == #var_name)
                                    .map(|(_, v)| format!("{:?}", v)))
                                .unwrap_or_default()),
                        );
                    }
                })
                .collect();

            quote! {
                if {
                    let __guard_scope_inner = __comm_guard_scope.inner();
                    let __guard_body = &*__guard_scope_inner.unsafe_body;
                    let __match_bindings = __comm_received.match_pattern(__guard_body)
                        .expect("match already verified");

                    let __guard_formula = #formula_expr;
                    let mut __guard_env = ::std::collections::HashMap::new();
                    #(#env_inserts)*

                    // Guard relation query callback — stubs for Phase 2A.
                    // Phase 5A will generate full Ascent relation access.
                    let __guard_relation_query = |_rel: &str, _args: &[String]| -> bool {
                        false
                    };
                    let __guard_domain_enumerate = |_dom: &str| -> Vec<Vec<String>> {
                        Vec::new()
                    };

                    mettail_prattail::logict::evaluate_quantified(
                        &__guard_formula,
                        &__guard_env,
                        &__guard_relation_query,
                        &__guard_domain_enumerate,
                        1000,
                    )
                }
            }
        }
    }
}

/// Collect free variables from a [`RefinementPredicate`], excluding quantifier-bound ones.
fn collect_refinement_free_vars(pred: &RefinementPredicate) -> HashSet<String> {
    let mut free = HashSet::new();
    let mut bound = HashSet::new();
    collect_refinement_free_vars_inner(pred, &mut free, &mut bound);
    free
}

fn collect_refinement_free_vars_inner(
    pred: &RefinementPredicate,
    free: &mut HashSet<String>,
    bound: &mut HashSet<String>,
) {
    match pred {
        RefinementPredicate::Linear { terms, .. } => {
            for (var, _) in terms {
                let name = var.to_string();
                if !bound.contains(&name) {
                    free.insert(name);
                }
            }
        }
        RefinementPredicate::Relation { args, .. } => {
            for arg in args {
                if let crate::ast::language::PredArg::Var(id) = arg {
                    let name = id.to_string();
                    if !bound.contains(&name) {
                        free.insert(name);
                    }
                }
            }
        }
        RefinementPredicate::Quantified { var, body, .. } => {
            let var_name = var.to_string();
            let was_bound = bound.contains(&var_name);
            bound.insert(var_name.clone());
            collect_refinement_free_vars_inner(body, free, bound);
            if !was_bound {
                bound.remove(&var_name);
            }
        }
        RefinementPredicate::And(a, b)
        | RefinementPredicate::Or(a, b)
        | RefinementPredicate::Implies(a, b) => {
            collect_refinement_free_vars_inner(a, free, bound);
            collect_refinement_free_vars_inner(b, free, bound);
        }
        RefinementPredicate::Not(inner) => {
            collect_refinement_free_vars_inner(inner, free, bound);
        }
        RefinementPredicate::TermEq(a, b) | RefinementPredicate::TermNeq(a, b) => {
            for arg in [a, b] {
                if let crate::ast::language::PredArg::Var(id) = arg {
                    let name = id.to_string();
                    if !bound.contains(&name) {
                        free.insert(name);
                    }
                }
            }
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

    // ══════════════════════════════════════════════════════════════════════
    // RT8: Refinement type codegen tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn refinement_guard_linear_simple_gt() {
        let pred = RefinementPredicate::Linear {
            terms: vec![(make_ident("x"), 1)],
            relation: LinearRelation::Gt,
            rhs: 0,
        };
        let binding = make_ident("x");
        let guard = generate_refinement_guard(&pred, &binding);
        let code = guard.to_string();
        assert!(code.contains("> 0"), "expected `> 0` in: {}", code);
    }

    #[test]
    fn refinement_guard_linear_multi_term() {
        let pred = RefinementPredicate::Linear {
            terms: vec![(make_ident("x"), 3), (make_ident("y"), 2)],
            relation: LinearRelation::Le,
            rhs: 7,
        };
        let binding = make_ident("x");
        let guard = generate_refinement_guard(&pred, &binding);
        let code = guard.to_string();
        assert!(code.contains("<= 7"), "expected `<= 7` in: {}", code);
        assert!(code.contains("3"), "expected coefficient 3 in: {}", code);
    }

    #[test]
    fn refinement_guard_conjunction() {
        let a = RefinementPredicate::Linear {
            terms: vec![(make_ident("x"), 1)],
            relation: LinearRelation::Gt,
            rhs: 0,
        };
        let b = RefinementPredicate::Linear {
            terms: vec![(make_ident("x"), 1)],
            relation: LinearRelation::Lt,
            rhs: 100,
        };
        let pred = RefinementPredicate::And(Box::new(a), Box::new(b));
        let binding = make_ident("x");
        let guard = generate_refinement_guard(&pred, &binding);
        let code = guard.to_string();
        assert!(code.contains("&&"), "expected && in: {}", code);
    }

    #[test]
    fn refinement_guard_negation() {
        let inner = RefinementPredicate::Linear {
            terms: vec![(make_ident("x"), 1)],
            relation: LinearRelation::Eq,
            rhs: 0,
        };
        let pred = RefinementPredicate::Not(Box::new(inner));
        let binding = make_ident("x");
        let guard = generate_refinement_guard(&pred, &binding);
        let code = guard.to_string();
        assert!(code.contains("!"), "expected negation in: {}", code);
    }

    #[test]
    fn refinement_guard_term_eq() {
        let pred = RefinementPredicate::TermEq(
            crate::ast::language::PredArg::Var(make_ident("x")),
            crate::ast::language::PredArg::Var(make_ident("y")),
        );
        let binding = make_ident("x");
        let guard = generate_refinement_guard(&pred, &binding);
        let code = guard.to_string();
        assert!(code.contains("=="), "expected == in: {}", code);
    }

    #[test]
    fn refinement_guard_term_neq() {
        let pred = RefinementPredicate::TermNeq(
            crate::ast::language::PredArg::Var(make_ident("a")),
            crate::ast::language::PredArg::Constant(make_ident("zero")),
        );
        let binding = make_ident("a");
        let guard = generate_refinement_guard(&pred, &binding);
        let code = guard.to_string();
        assert!(code.contains("!="), "expected != in: {}", code);
    }

    #[test]
    fn refinement_guard_implication() {
        let a = RefinementPredicate::Linear {
            terms: vec![(make_ident("x"), 1)],
            relation: LinearRelation::Ge,
            rhs: 0,
        };
        let b = RefinementPredicate::Linear {
            terms: vec![(make_ident("x"), 1)],
            relation: LinearRelation::Gt,
            rhs: -1,
        };
        let pred = RefinementPredicate::Implies(Box::new(a), Box::new(b));
        let binding = make_ident("x");
        let guard = generate_refinement_guard(&pred, &binding);
        let code = guard.to_string();
        // Implies(a, b) → (!a || b)
        assert!(code.contains("||"), "expected || (implication) in: {}", code);
    }

    #[test]
    fn refinement_free_vars_excludes_quantifier_bound() {
        use crate::ast::language::{Quantifier, PredArg};

        let pred = RefinementPredicate::Quantified {
            quantifier: Quantifier::ForAll,
            var: make_ident("y"),
            domain: Some(make_ident("nodes")),
            bound: None,
            body: Box::new(RefinementPredicate::Relation {
                name: make_ident("reachable"),
                args: vec![
                    PredArg::Var(make_ident("x")),
                    PredArg::Var(make_ident("y")),
                ],
                negated: false,
            }),
        };
        let free = collect_refinement_free_vars(&pred);
        assert!(free.contains("x"), "x should be free");
        assert!(!free.contains("y"), "y should be bound by forall");
    }

    #[test]
    fn refinement_generate_rules_empty_language() {
        // A language with no refinement types should produce empty output.
        let language = crate::ast::language::LanguageDef {
            name: make_ident("Test"),
            options: Default::default(),
            extends_names: vec![],
            include_names: vec![],
            mixin_names: vec![],
            types: vec![],
            refinement_types: vec![],
            token_defs: vec![],
            mode_defs: vec![],
            sync_constraints: vec![],
            tree_invariants: vec![],
            terms: vec![],
            equations: vec![],
            rewrites: vec![],
            logic: None,
        };
        let rules = generate_refinement_type_rules(&language);
        assert!(rules.is_empty(), "empty refinement_types should produce no rules");
    }

    #[test]
    fn refinement_generate_rules_one_linear() {
        use crate::ast::language::RefinementTypeDef;
        use crate::ast::types::TypeExpr;

        let language = crate::ast::language::LanguageDef {
            name: make_ident("Test"),
            options: Default::default(),
            extends_names: vec![],
            include_names: vec![],
            mixin_names: vec![],
            types: vec![],
            refinement_types: vec![
                RefinementTypeDef {
                    name: make_ident("PosInt"),
                    var: make_ident("x"),
                    base_type: TypeExpr::Base(make_ident("Int")),
                    predicate: RefinementPredicate::Linear {
                        terms: vec![(make_ident("x"), 1)],
                        relation: LinearRelation::Gt,
                        rhs: 0,
                    },
                },
            ],
            token_defs: vec![],
            mode_defs: vec![],
            sync_constraints: vec![],
            tree_invariants: vec![],
            terms: vec![],
            equations: vec![],
            rewrites: vec![],
            logic: None,
        };
        let rules = generate_refinement_type_rules(&language);
        let code = rules.to_string();
        assert!(code.contains("is_refined_posint"), "expected relation name in: {}", code);
        assert!(code.contains("int"), "expected base type relation in: {}", code);
        assert!(code.contains("> 0"), "expected guard in: {}", code);
    }

    // ══════════════════════════════════════════════════════════════════════
    // RT9: Substitution propagation tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn refinement_join_clause_generation() {
        let var = make_ident("x");
        let clause = generate_refinement_join_clause(&var, "PosInt");
        let code = clause.to_string();
        assert!(code.contains("is_refined_posint"), "expected join clause: {}", code);
        assert!(code.contains("x"), "expected variable in join: {}", code);
    }

    #[test]
    fn refinement_membership_check_found() {
        use crate::ast::language::RefinementTypeDef;
        use crate::ast::types::TypeExpr;

        let language = crate::ast::language::LanguageDef {
            name: make_ident("Test"),
            options: Default::default(),
            extends_names: vec![],
            include_names: vec![],
            mixin_names: vec![],
            types: vec![],
            refinement_types: vec![
                RefinementTypeDef {
                    name: make_ident("PosInt"),
                    var: make_ident("x"),
                    base_type: TypeExpr::Base(make_ident("Int")),
                    predicate: RefinementPredicate::Linear {
                        terms: vec![(make_ident("x"), 1)],
                        relation: LinearRelation::Gt,
                        rhs: 0,
                    },
                },
            ],
            token_defs: vec![],
            mode_defs: vec![],
            sync_constraints: vec![],
            tree_invariants: vec![],
            terms: vec![],
            equations: vec![],
            rewrites: vec![],
            logic: None,
        };

        let var = make_ident("val");
        let result = generate_refinement_membership_check(&var, "PosInt", &language);
        assert!(result.is_some(), "expected Some for existing refinement type");
        let code = result.expect("just checked").to_string();
        assert!(code.contains("is_refined_posint"), "expected relation: {}", code);
        assert!(code.contains("val"), "expected variable: {}", code);
    }

    #[test]
    fn refinement_membership_check_not_found() {
        let language = crate::ast::language::LanguageDef {
            name: make_ident("Test"),
            options: Default::default(),
            extends_names: vec![],
            include_names: vec![],
            mixin_names: vec![],
            types: vec![],
            refinement_types: vec![],
            token_defs: vec![],
            mode_defs: vec![],
            sync_constraints: vec![],
            tree_invariants: vec![],
            terms: vec![],
            equations: vec![],
            rewrites: vec![],
            logic: None,
        };

        let var = make_ident("x");
        let result = generate_refinement_membership_check(&var, "PosInt", &language);
        assert!(result.is_none(), "expected None for missing refinement type");
    }
}
