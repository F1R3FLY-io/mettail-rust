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

/// Whether a fold evaluates configured boolean compounds or the pure heuristic.
#[derive(Clone, Copy)]
enum PredicateFoldMode {
    Configured,
    Heuristic,
}

/// Post-order predicate fold driven by an explicit continuation stack.
///
/// Configured resolution deliberately propagates overrides only through
/// `Not`, `And`, and `Or`, matching the historical public contract. Other
/// roots switch their entire subtree to heuristic mode.
fn fold_predicate<T>(
    root: &PredicateExpr,
    root_mode: PredicateFoldMode,
    mut reduce: impl FnMut(&PredicateExpr, PredicateFoldMode, &mut Vec<T>) -> T,
) -> T {
    enum Task<'expr> {
        Visit(&'expr PredicateExpr, PredicateFoldMode),
        Reduce(&'expr PredicateExpr, PredicateFoldMode),
    }

    let mut tasks = vec![Task::Visit(root, root_mode)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(expr, PredicateFoldMode::Configured)
                if !matches!(
                    expr,
                    PredicateExpr::Relation { .. }
                        | PredicateExpr::Not(_)
                        | PredicateExpr::And(_, _)
                        | PredicateExpr::Or(_, _)
                ) =>
            {
                tasks.push(Task::Visit(expr, PredicateFoldMode::Heuristic));
            },
            Task::Visit(expr, mode) => {
                tasks.push(Task::Reduce(expr, mode));
                match expr {
                    PredicateExpr::Not(body)
                    | PredicateExpr::ForallFinite { body, .. }
                    | PredicateExpr::ExistsFinite { body, .. }
                    | PredicateExpr::ForallInfinite { body, .. }
                    | PredicateExpr::ExistsInfinite { body, .. }
                    | PredicateExpr::Bounded { body, .. } => {
                        tasks.push(Task::Visit(body, mode));
                    },
                    PredicateExpr::And(left, right) | PredicateExpr::Or(left, right) => {
                        tasks.push(Task::Visit(right, mode));
                        tasks.push(Task::Visit(left, mode));
                    },
                    PredicateExpr::True
                    | PredicateExpr::False
                    | PredicateExpr::Atom(_)
                    | PredicateExpr::Relation { .. } => {},
                }
            },
            Task::Reduce(expr, mode) => {
                let value = reduce(expr, mode, &mut values);
                values.push(value);
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    values.pop().expect("predicate fold produced no result")
}

fn fold_selectivity(
    expr: &PredicateExpr,
    guard_config: Option<&crate::GuardConfigSpec>,
    mode: PredicateFoldMode,
) -> f64 {
    fold_predicate(expr, mode, |expr, mode, values| match expr {
        PredicateExpr::True => 1.0,
        PredicateExpr::False => 0.0,
        PredicateExpr::Atom(_) => 0.5,
        PredicateExpr::Relation { name, args } => {
            if matches!(mode, PredicateFoldMode::Configured) {
                if let Some(value) =
                    guard_config.and_then(|config| config.selectivity_overrides.get(name.as_str()))
                {
                    return *value;
                }
            }
            let arity_factor = 1.0 / (args.len() as f64 + 1.0).sqrt();
            if is_equality_relation(name) {
                0.1 * arity_factor
            } else if is_cardinality_relation(name) {
                0.3 * arity_factor
            } else {
                0.5 * arity_factor
            }
        },
        PredicateExpr::Not(_) => 1.0 - values.pop().expect("selectivity fold lost not body"),
        PredicateExpr::And(_, _) => {
            let right = values
                .pop()
                .expect("selectivity fold lost right conjunction");
            let left = values
                .pop()
                .expect("selectivity fold lost left conjunction");
            left * right
        },
        PredicateExpr::Or(_, _) => {
            let right = values
                .pop()
                .expect("selectivity fold lost right disjunction");
            let left = values
                .pop()
                .expect("selectivity fold lost left disjunction");
            1.0 - (1.0 - left) * (1.0 - right)
        },
        PredicateExpr::ForallFinite { domain, .. } => {
            let body = values
                .pop()
                .expect("selectivity fold lost finite universal body");
            body.powi(domain.len().max(1) as i32)
        },
        PredicateExpr::ExistsFinite { domain, .. } => {
            let body = values
                .pop()
                .expect("selectivity fold lost finite existential body");
            1.0 - (1.0 - body).powi(domain.len().max(1) as i32)
        },
        PredicateExpr::ForallInfinite { .. } => {
            values
                .pop()
                .expect("selectivity fold lost infinite universal body")
                * 0.05
        },
        PredicateExpr::ExistsInfinite { .. } => {
            let body = values
                .pop()
                .expect("selectivity fold lost infinite existential body");
            1.0 - (1.0 - body).powi(10)
        },
        PredicateExpr::Bounded { .. } => values.pop().expect("selectivity fold lost bounded body"),
    })
}

fn fold_cost(
    expr: &PredicateExpr,
    guard_config: Option<&crate::GuardConfigSpec>,
    mode: PredicateFoldMode,
) -> u32 {
    fold_predicate(expr, mode, |expr, mode, values| match expr {
        PredicateExpr::True | PredicateExpr::False => 0,
        PredicateExpr::Atom(_) => 1,
        PredicateExpr::Relation { name, args } => {
            if matches!(mode, PredicateFoldMode::Configured) {
                if let Some(value) =
                    guard_config.and_then(|config| config.cost_overrides.get(name.as_str()))
                {
                    return *value;
                }
            }
            2 + args.len() as u32
        },
        PredicateExpr::Not(_) => values.pop().expect("cost fold lost not body") + 1,
        PredicateExpr::And(_, _) | PredicateExpr::Or(_, _) => {
            let right = values.pop().expect("cost fold lost right boolean operand");
            let left = values.pop().expect("cost fold lost left boolean operand");
            left + right
        },
        PredicateExpr::ForallFinite { domain, .. } => {
            domain.len().max(1) as u32 * values.pop().expect("cost fold lost finite universal body")
        },
        PredicateExpr::ExistsFinite { domain, .. } => {
            ((domain.len().max(1) as u32 / 2).max(1))
                * values
                    .pop()
                    .expect("cost fold lost finite existential body")
        },
        PredicateExpr::ForallInfinite { .. } => {
            100 + values
                .pop()
                .expect("cost fold lost infinite universal body")
                * 10
        },
        PredicateExpr::ExistsInfinite { .. } => {
            50 + values
                .pop()
                .expect("cost fold lost infinite existential body")
                * 10
        },
        PredicateExpr::Bounded { bound, .. } => {
            (*bound as u32).min(100) * values.pop().expect("cost fold lost bounded body")
        },
    })
}

/// Resolve selectivity with per-relation overrides through boolean compounds.
pub fn resolve_selectivity(
    expr: &PredicateExpr,
    guard_config: Option<&crate::GuardConfigSpec>,
) -> f64 {
    fold_selectivity(expr, guard_config, PredicateFoldMode::Configured)
}

/// Resolve cost with per-relation overrides through boolean compounds.
pub fn resolve_cost(expr: &PredicateExpr, guard_config: Option<&crate::GuardConfigSpec>) -> u32 {
    fold_cost(expr, guard_config, PredicateFoldMode::Configured)
}

/// Estimate the fraction of inputs satisfying a predicate.
pub fn estimate_predicate_selectivity(expr: &PredicateExpr) -> f64 {
    fold_selectivity(expr, None, PredicateFoldMode::Heuristic)
}

/// Estimate predicate evaluation cost; lower values are cheaper.
pub fn estimate_predicate_cost(expr: &PredicateExpr) -> u32 {
    fold_cost(expr, None, PredicateFoldMode::Heuristic)
}
