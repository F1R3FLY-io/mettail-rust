use super::*;

// ═══════════════════════════════════════════════════════════════════════════════
// §11 PredicateCompiler trait — per-predicate compilation interface
// ═══════════════════════════════════════════════════════════════════════════════

/// Trait for modules that can compile individual predicates.
///
/// Each advanced automata module (M1–M11) implements this trait to provide
/// targeted per-predicate compilation, as opposed to the existing
/// `analyze_from_bundle()` which processes entire grammars.
///
/// Default implementation delegates to the existing `analyze_from_bundle()`
/// for backward compatibility.
pub trait PredicateCompiler {
    /// The analysis output type.
    type Output;

    /// Compile a single predicate formula into this module's analysis.
    ///
    /// The `profile` provides pre-computed variety features to guide compilation.
    fn compile_predicate(
        &self,
        pred: &PredicateExpr,
        profile: &PredicateProfile,
        all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
        categories: &[CategoryInfo],
    ) -> Self::Output;
}

/// Run the per-predicate compilation pipeline.
///
/// For each predicate in the dispatch plan, invokes only the modules whose
/// bits are set in the predicate's signature. Collects results per-module.
pub fn compile_predicate_pipeline(
    plan: &GrammarDispatchPlan,
    _all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    _categories: &[CategoryInfo],
) -> DispatchDiagnostics {
    // For now, return diagnostics only (compilation delegates to existing
    // analyze_from_bundle() in Phase 7). Per-predicate compilation will be
    // wired in when modules implement PredicateCompiler.
    DispatchDiagnostics::from_plan(plan)
}

// ═══════════════════════════════════════════════════════════════════════════════
// §11b  Sprint C4 — Symbolic Subsumption → Predicate Dispatch Ordering
// ═══════════════════════════════════════════════════════════════════════════════

/// Reorder predicates by guard specificity using subsumption data.
///
/// When `subsumed_guards` data is available from symbolic analysis, more specific
/// guards (those subsumed by more general ones) are tried first. This implements
/// most-specific-first dispatch semantics (Ernst et al. 1998).
///
/// Each entry `(a, b)` in `subsumed_guards` means guard `a` is subsumed by
/// (more specific than) guard `b` — i.e. the language of `a` is a subset of the
/// language of `b`. A predicate's *specificity score* equals the number of
/// subsumption pairs where it appears as the subsumed element: higher score
/// means more guards are strictly more general, so the predicate is more specific.
///
/// Returns the input predicates sorted by specificity (most specific first).
/// Ties are broken by grammar order (index in the original list).
pub fn order_by_specificity(
    predicate_labels: &[String],
    subsumed_guards: &[(String, String)],
) -> Vec<String> {
    if subsumed_guards.is_empty() {
        return predicate_labels.to_vec();
    }

    // Build specificity scores: count how many other predicates subsume each one.
    // Higher count = more specific (more guards are more general than this one).
    let mut specificity: HashMap<&str, usize> = HashMap::with_capacity(predicate_labels.len());
    for label in predicate_labels {
        specificity.insert(label.as_str(), 0);
    }

    for (subsumed, _subsumer) in subsumed_guards {
        // subsumed is MORE specific (its guard is contained in subsumer's)
        if let Some(count) = specificity.get_mut(subsumed.as_str()) {
            *count += 1;
        }
    }

    // Sort: higher specificity first, then by original order for ties
    let mut indexed: Vec<(usize, &String)> = predicate_labels.iter().enumerate().collect();
    indexed.sort_by(|(idx_a, label_a), (idx_b, label_b)| {
        let spec_a = specificity.get(label_a.as_str()).copied().unwrap_or(0);
        let spec_b = specificity.get(label_b.as_str()).copied().unwrap_or(0);
        spec_b
            .cmp(&spec_a) // descending specificity
            .then(idx_a.cmp(idx_b)) // ascending grammar order for ties
    });

    indexed
        .into_iter()
        .map(|(_, label)| label.clone())
        .collect()
}

// ═══════════════════════════════════════════════════════════════════════════════
// §12 Guard Selectivity Estimation
// ═══════════════════════════════════════════════════════════════════════════════

/// Resolve the selectivity of a predicate, consulting the optional
/// `GuardConfigSpec` for per-predicate `@[selectivity(...)]` overrides
/// before falling back to heuristic estimation.
///
/// Override precedence (design doc §2A "Override precedence"):
/// 1. Explicit annotation (`selectivity_overrides[name]`)
/// 2. Heuristic default (`estimate_predicate_selectivity`)
///
/// Compound predicates (And, Or, Not, etc.) recursively use this resolver
/// to apply per-leaf overrides while maintaining the standard selectivity
/// algebra (independence assumption for conjunction, etc.).
pub fn resolve_selectivity(
    expr: &PredicateExpr,
    guard_config: Option<&crate::GuardConfigSpec>,
) -> f64 {
    match expr {
        PredicateExpr::Relation { name, .. } => {
            if let Some(gc) = guard_config {
                if let Some(&override_val) = gc.selectivity_overrides.get(name.as_str()) {
                    return override_val;
                }
            }
            estimate_predicate_selectivity(expr)
        },
        PredicateExpr::Not(inner) => 1.0 - resolve_selectivity(inner, guard_config),
        PredicateExpr::And(a, b) => {
            resolve_selectivity(a, guard_config) * resolve_selectivity(b, guard_config)
        },
        PredicateExpr::Or(a, b) => {
            let sa = resolve_selectivity(a, guard_config);
            let sb = resolve_selectivity(b, guard_config);
            1.0 - (1.0 - sa) * (1.0 - sb)
        },
        // For all other variants, fall back to the unconfigured estimate.
        _ => estimate_predicate_selectivity(expr),
    }
}

/// Resolve the cost of a predicate, consulting the optional `GuardConfigSpec`
/// for per-predicate `@[cost(...)]` overrides before falling back to
/// heuristic estimation.
///
/// Override precedence:
/// 1. Explicit annotation (`cost_overrides[name]`)
/// 2. Heuristic default (`estimate_predicate_cost`)
pub fn resolve_cost(expr: &PredicateExpr, guard_config: Option<&crate::GuardConfigSpec>) -> u32 {
    match expr {
        PredicateExpr::Relation { name, .. } => {
            if let Some(gc) = guard_config {
                if let Some(&override_val) = gc.cost_overrides.get(name.as_str()) {
                    return override_val;
                }
            }
            estimate_predicate_cost(expr)
        },
        PredicateExpr::Not(inner) => resolve_cost(inner, guard_config) + 1,
        PredicateExpr::And(a, b) | PredicateExpr::Or(a, b) => {
            resolve_cost(a, guard_config) + resolve_cost(b, guard_config)
        },
        _ => estimate_predicate_cost(expr),
    }
}

/// Selectivity estimation for predicate expressions.
///
/// Returns an estimate in [0.0, 1.0] of the fraction of inputs satisfying the
/// predicate. Used by guard ordering (Phase 7A) to sort guards on the same
/// channel so the most selective guard is evaluated first.
///
/// These are heuristic estimates — they do not require access to runtime data.
/// The selectivity model uses the independence assumption: conjunction selectivity
/// is the product, disjunction follows inclusion-exclusion.
pub fn estimate_predicate_selectivity(expr: &PredicateExpr) -> f64 {
    match expr {
        PredicateExpr::True => 1.0,
        PredicateExpr::False => 0.0,
        PredicateExpr::Atom(_) => 0.5, // unknown atom: assume 50%
        PredicateExpr::Relation { name, args, .. } => {
            // Estimate based on relation name and arity
            let arity_factor = 1.0 / (args.len() as f64 + 1.0).sqrt();
            if is_equality_relation(name) {
                // Equality is very selective
                0.1 * arity_factor
            } else if is_cardinality_relation(name) {
                0.3 * arity_factor
            } else {
                0.5 * arity_factor
            }
        },
        PredicateExpr::Not(inner) => 1.0 - estimate_predicate_selectivity(inner),
        PredicateExpr::And(a, b) => {
            estimate_predicate_selectivity(a) * estimate_predicate_selectivity(b)
        },
        PredicateExpr::Or(a, b) => {
            let sa = estimate_predicate_selectivity(a);
            let sb = estimate_predicate_selectivity(b);
            1.0 - (1.0 - sa) * (1.0 - sb)
        },
        PredicateExpr::ForallFinite { body, domain, .. } => {
            // Universal over finite domain: selectivity = body_sel ^ |domain|
            let body_sel = estimate_predicate_selectivity(body);
            let n = domain.len().max(1) as i32;
            body_sel.powi(n)
        },
        PredicateExpr::ExistsFinite { body, domain, .. } => {
            // Existential over finite domain: selectivity = 1 - (1 - body_sel)^|domain|
            let body_sel = estimate_predicate_selectivity(body);
            let n = domain.len().max(1) as i32;
            1.0 - (1.0 - body_sel).powi(n)
        },
        PredicateExpr::ForallInfinite { body, .. } => {
            // Universal over infinite domain: very selective
            let body_sel = estimate_predicate_selectivity(body);
            body_sel * 0.05
        },
        PredicateExpr::ExistsInfinite { body, .. } => {
            // Existential over infinite domain: moderate
            let body_sel = estimate_predicate_selectivity(body);
            1.0 - (1.0 - body_sel).powi(10)
        },
        PredicateExpr::Bounded { body, .. } => {
            // Bounded wrapper: same selectivity as body
            estimate_predicate_selectivity(body)
        },
    }
}

/// Estimated evaluation cost of a predicate expression.
///
/// Lower cost = cheaper. Used as a tiebreaker when guards have equal selectivity.
pub fn estimate_predicate_cost(expr: &PredicateExpr) -> u32 {
    match expr {
        PredicateExpr::True | PredicateExpr::False => 0,
        PredicateExpr::Atom(_) => 1,
        PredicateExpr::Relation { args, .. } => 2 + args.len() as u32,
        PredicateExpr::Not(inner) => estimate_predicate_cost(inner) + 1,
        PredicateExpr::And(a, b) | PredicateExpr::Or(a, b) => {
            estimate_predicate_cost(a) + estimate_predicate_cost(b)
        },
        PredicateExpr::ForallFinite { body, domain, .. } => {
            let n = domain.len().max(1) as u32;
            n * estimate_predicate_cost(body)
        },
        PredicateExpr::ExistsFinite { body, domain, .. } => {
            let n = domain.len().max(1) as u32;
            (n / 2).max(1) * estimate_predicate_cost(body)
        },
        PredicateExpr::ForallInfinite { body, .. } => 100 + estimate_predicate_cost(body) * 10,
        PredicateExpr::ExistsInfinite { body, .. } => 50 + estimate_predicate_cost(body) * 10,
        PredicateExpr::Bounded { body, bound } => {
            (*bound as u32).min(100) * estimate_predicate_cost(body)
        },
    }
}
