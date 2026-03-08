//! Termination analysis via dependency pairs and SCC decomposition.
//!
//! Determines whether a term rewriting system (TRS) is terminating — i.e.,
//! whether all reduction sequences are finite. This is a prerequisite for
//! Newman's Lemma (local confluence + termination → confluence), making
//! this module a companion to the `confluence` module.
//!
//! ## Theoretical Foundations
//!
//! - **Arts & Giesl (2000)** — "Termination of term rewriting using dependency
//!   pairs." Introduces the dependency pair framework, which decomposes the
//!   termination problem into subproblems via the dependency graph.
//! - **Hirokawa & Middeldorp (2005)** — "Automating the dependency pair method."
//!   Refines the framework with usable rules, argument filterings, and SCC
//!   decomposition for efficient automation.
//! - **Giesl et al. (2006)** — "Mechanizing and improving dependency pairs."
//!   The AProVE system and modern dependency pair extensions.
//!
//! ## Architecture
//!
//! ```text
//! RewriteRule set
//!       │
//!       ▼
//! extract_dependency_pairs()
//!       │
//!       ▼
//! Vec<DependencyPair>
//!       │
//!       ▼
//! build_dependency_graph()
//!       │
//!       ▼
//! SCC decomposition (Tarjan)
//!       │
//!       ▼
//! check_termination() ──→ TerminationResult
//! ```
//!
//! ## Key Insight
//!
//! A TRS is non-terminating iff there exists an infinite chain of dependency
//! pairs. By decomposing the dependency graph into strongly connected components
//! (SCCs), each SCC can be analyzed independently. An SCC with no decreasing
//! ordering witness is a potential source of non-termination.

use std::collections::{HashMap, HashSet};
use std::fmt;

// NOTE: Semiring import will be used when weighted termination analysis is implemented.
#[allow(unused_imports)]
use crate::automata::semiring::Semiring;

// Re-use Term and RewriteRule from the confluence module.
use crate::confluence::{RewriteRule, Term};

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A dependency pair `⟨l#, t#⟩` derived from a rewrite rule `l → r`.
///
/// For each defined symbol `f` occurring in the LHS of a rule `l → r`, and
/// each subterm `g(s₁, ..., sₙ)` of `r` where `g` is also a defined symbol,
/// the dependency pair `⟨f#(args_of_l), g#(s₁, ..., sₙ)⟩` is generated.
/// The `#` marks (called "tuple symbols") distinguish DP heads from ordinary
/// function symbols.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DependencyPair {
    /// The marked LHS of the originating rule (with `#` symbol).
    pub source: Term,
    /// The marked subterm from the RHS (with `#` symbol).
    pub target: Term,
    /// Index of the originating rewrite rule.
    pub rule_index: usize,
}

impl fmt::Display for DependencyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "⟨{}, {}⟩ (from rule {})", self.source, self.target, self.rule_index)
    }
}

/// A strongly connected component in the dependency graph.
///
/// Each SCC is a set of dependency pair indices that form a cycle. Non-trivial
/// SCCs (size > 1, or size 1 with a self-loop) require a decreasing ordering
/// witness to prove termination.
#[derive(Debug, Clone)]
pub struct DependencyScc {
    /// Indices into the dependency pair vector.
    pub pair_indices: Vec<usize>,
    /// Whether this SCC contains a self-loop (relevant for singleton SCCs).
    pub has_self_loop: bool,
}

impl fmt::Display for DependencyScc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "SCC({} pairs, self_loop: {})",
            self.pair_indices.len(),
            self.has_self_loop,
        )
    }
}

/// Result of termination analysis for a TRS.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TerminationResult {
    /// The TRS is terminating. All SCCs have decreasing ordering witnesses.
    Terminating,
    /// The TRS is potentially non-terminating. At least one SCC could not be
    /// shown to be terminating within the analysis bounds.
    PotentiallyNonTerminating {
        /// Human-readable reason (e.g., "SCC {2,5} has no decreasing ordering").
        reason: String,
        /// Indices of the problematic SCCs in the SCC list.
        problematic_sccs: Vec<usize>,
    },
    /// Termination analysis was inconclusive (e.g., analysis timed out or
    /// the ordering method is insufficient).
    Unknown {
        /// Reason the analysis was inconclusive.
        reason: String,
    },
}

impl fmt::Display for TerminationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TerminationResult::Terminating => write!(f, "Terminating"),
            TerminationResult::PotentiallyNonTerminating { reason, .. } => {
                write!(f, "Potentially non-terminating: {}", reason)
            }
            TerminationResult::Unknown { reason } => {
                write!(f, "Unknown: {}", reason)
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

/// Extract dependency pairs from a set of rewrite rules.
///
/// For each rule `l → r` where `l = f(t₁, ..., tₙ)`, and each subterm
/// `g(s₁, ..., sₘ)` of `r` where `g` is a defined symbol (i.e., appears
/// as the root of some rule's LHS), a dependency pair `⟨f#(t₁, ..., tₙ),
/// g#(s₁, ..., sₘ)⟩` is generated.
///
/// # Arguments
///
/// * `rules` - The rewrite rules of the TRS.
///
/// # Returns
///
/// A vector of all dependency pairs extracted from the rules.
pub fn extract_dependency_pairs(rules: &[RewriteRule]) -> Vec<DependencyPair> {
    // Step 1: Collect the set of defined symbols — root symbols of all LHS terms.
    let defined_symbols: HashSet<&str> = rules
        .iter()
        .filter_map(|rule| match &rule.lhs {
            Term::App { symbol, .. } => Some(symbol.as_str()),
            Term::Var(_) => None,
        })
        .collect();

    let mut pairs = Vec::new();

    // Step 2: For each rule l → r where l = f(t₁,...,tₙ), collect subterms of r
    // whose root is a defined symbol.
    for (rule_index, rule) in rules.iter().enumerate() {
        // Only consider rules whose LHS is a function application (not a bare variable).
        let source_marked = match &rule.lhs {
            Term::App { symbol, args } => Term::App {
                symbol: format!("{}#", symbol),
                args: args.clone(),
            },
            Term::Var(_) => continue,
        };

        // Collect all subterms of the RHS rooted at a defined symbol.
        let mut rhs_subterms = Vec::new();
        collect_defined_subterms(&rule.rhs, &defined_symbols, &mut rhs_subterms);

        for subterm in rhs_subterms {
            // Mark the subterm's root with #.
            let target_marked = match subterm {
                Term::App { symbol, args } => Term::App {
                    symbol: format!("{}#", symbol),
                    args,
                },
                // collect_defined_subterms only yields App terms.
                Term::Var(_) => unreachable!(),
            };

            pairs.push(DependencyPair {
                source: source_marked.clone(),
                target: target_marked,
                rule_index,
            });
        }
    }

    pairs
}

/// Collect all subterms of `term` whose root symbol is in `defined_symbols`.
///
/// The term itself is checked, and then recursion descends into each argument.
fn collect_defined_subterms<'a>(
    term: &'a Term,
    defined_symbols: &HashSet<&str>,
    acc: &mut Vec<Term>,
) {
    match term {
        Term::App { symbol, args } => {
            if defined_symbols.contains(symbol.as_str()) {
                acc.push(term.clone());
            }
            for arg in args {
                collect_defined_subterms(arg, defined_symbols, acc);
            }
        }
        Term::Var(_) => {}
    }
}

/// Build the dependency graph and decompose it into SCCs.
///
/// Two dependency pairs `⟨s, t⟩` and `⟨u, v⟩` have an edge from the first
/// to the second if `t` and `u` are unifiable (i.e., the target of one pair
/// can chain into the source of another). The SCCs of this graph are computed
/// via Tarjan's algorithm.
///
/// # Arguments
///
/// * `pairs` - The dependency pairs to analyze.
///
/// # Returns
///
/// A vector of SCCs, each containing the indices of its constituent pairs.
pub fn build_dependency_graph(pairs: &[DependencyPair]) -> Vec<DependencyScc> {
    let n = pairs.len();
    if n == 0 {
        return Vec::new();
    }

    // Build adjacency list: edge from DP_i to DP_j if target of i unifies with
    // source of j (after variable renaming to avoid capture).
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for i in 0..n {
        for j in 0..n {
            // Rename variables in pair j's source to avoid collision with pair i's target.
            let renamed_source = rename_variables(&pairs[j].source, "_R");
            if unify(&pairs[i].target, &renamed_source).is_some() {
                adj[i].push(j);
            }
        }
    }

    // Tarjan SCC decomposition.
    let scc_indices = tarjan_scc_indices(n, &adj);

    // Convert index-based SCCs into DependencyScc structs with self-loop detection.
    scc_indices
        .into_iter()
        .map(|pair_indices| {
            let has_self_loop = pair_indices.iter().any(|&i| adj[i].contains(&i));
            DependencyScc {
                pair_indices,
                has_self_loop,
            }
        })
        .collect()
}

/// Rename all variables in a term by appending `suffix` to each variable name.
///
/// This prevents accidental variable capture when unifying terms from different
/// dependency pairs.
fn rename_variables(term: &Term, suffix: &str) -> Term {
    match term {
        Term::Var(name) => Term::Var(format!("{}{}", name, suffix)),
        Term::App { symbol, args } => Term::App {
            symbol: symbol.clone(),
            args: args.iter().map(|a| rename_variables(a, suffix)).collect(),
        },
    }
}

/// First-order unification with occurs check.
///
/// Returns `Some(substitution)` if the two terms are unifiable, `None` otherwise.
/// The substitution maps variable names to terms.
fn unify(t1: &Term, t2: &Term) -> Option<HashMap<String, Term>> {
    let mut subst: HashMap<String, Term> = HashMap::new();
    let mut worklist: Vec<(Term, Term)> = vec![(t1.clone(), t2.clone())];

    while let Some((lhs, rhs)) = worklist.pop() {
        // Apply current substitution to both sides.
        let lhs = apply_subst(&lhs, &subst);
        let rhs = apply_subst(&rhs, &subst);

        if lhs == rhs {
            continue;
        }

        match (lhs, rhs) {
            (Term::Var(x), t) | (t, Term::Var(x)) => {
                // Occurs check: x must not appear in t.
                if occurs(&x, &t) {
                    return None;
                }
                subst.insert(x, t);
            }
            (
                Term::App {
                    symbol: s1,
                    args: a1,
                },
                Term::App {
                    symbol: s2,
                    args: a2,
                },
            ) => {
                if s1 != s2 || a1.len() != a2.len() {
                    return None;
                }
                for (arg1, arg2) in a1.into_iter().zip(a2.into_iter()) {
                    worklist.push((arg1, arg2));
                }
            }
        }
    }

    Some(subst)
}

/// Apply a substitution to a term, chasing variable bindings to fixpoint.
fn apply_subst(term: &Term, subst: &HashMap<String, Term>) -> Term {
    match term {
        Term::Var(name) => {
            if let Some(bound) = subst.get(name) {
                apply_subst(bound, subst)
            } else {
                term.clone()
            }
        }
        Term::App { symbol, args } => Term::App {
            symbol: symbol.clone(),
            args: args.iter().map(|a| apply_subst(a, subst)).collect(),
        },
    }
}

/// Occurs check: does variable `var` appear anywhere in `term`?
fn occurs(var: &str, term: &Term) -> bool {
    match term {
        Term::Var(name) => name == var,
        Term::App { args, .. } => args.iter().any(|a| occurs(var, a)),
    }
}

/// Tarjan's SCC algorithm on a graph of `n` nodes with adjacency list `adj`.
///
/// Returns a vector of SCCs, each represented as a vector of node indices.
fn tarjan_scc_indices(n: usize, adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut index_counter: usize = 0;
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack = vec![false; n];
    let mut indices = vec![usize::MAX; n]; // usize::MAX = undefined
    let mut lowlinks = vec![0usize; n];
    let mut result: Vec<Vec<usize>> = Vec::new();

    fn strongconnect(
        v: usize,
        adj: &[Vec<usize>],
        index_counter: &mut usize,
        stack: &mut Vec<usize>,
        on_stack: &mut [bool],
        indices: &mut [usize],
        lowlinks: &mut [usize],
        result: &mut Vec<Vec<usize>>,
    ) {
        indices[v] = *index_counter;
        lowlinks[v] = *index_counter;
        *index_counter += 1;
        stack.push(v);
        on_stack[v] = true;

        for &w in &adj[v] {
            if indices[w] == usize::MAX {
                strongconnect(w, adj, index_counter, stack, on_stack, indices, lowlinks, result);
                lowlinks[v] = lowlinks[v].min(lowlinks[w]);
            } else if on_stack[w] {
                lowlinks[v] = lowlinks[v].min(indices[w]);
            }
        }

        if lowlinks[v] == indices[v] {
            let mut component = Vec::new();
            loop {
                let w = stack.pop().expect("tarjan stack underflow");
                on_stack[w] = false;
                component.push(w);
                if w == v {
                    break;
                }
            }
            result.push(component);
        }
    }

    for v in 0..n {
        if indices[v] == usize::MAX {
            strongconnect(
                v,
                adj,
                &mut index_counter,
                &mut stack,
                &mut on_stack,
                &mut indices,
                &mut lowlinks,
                &mut result,
            );
        }
    }

    result
}

/// Check termination of a TRS via the dependency pair method.
///
/// Extracts dependency pairs, builds the dependency graph, decomposes into
/// SCCs, and attempts to find decreasing ordering witnesses for each
/// non-trivial SCC.
///
/// # Arguments
///
/// * `rules` - The rewrite rules of the TRS.
///
/// # Returns
///
/// A `TerminationResult` indicating whether the TRS is terminating.
pub fn check_termination(rules: &[RewriteRule]) -> TerminationResult {
    if rules.is_empty() {
        return TerminationResult::Terminating;
    }

    let pairs = extract_dependency_pairs(rules);
    if pairs.is_empty() {
        // No dependency pairs means no recursive calls — trivially terminating.
        return TerminationResult::Terminating;
    }

    let sccs = build_dependency_graph(&pairs);

    let mut problematic_scc_indices = Vec::new();
    let mut reasons = Vec::new();

    for (scc_idx, scc) in sccs.iter().enumerate() {
        // A singleton SCC without a self-loop is trivially terminating
        // (no cycle through this DP).
        if scc.pair_indices.len() == 1 && !scc.has_self_loop {
            continue;
        }

        // Non-trivial SCC: attempt to find a structural decrease.
        if !has_structural_decrease(&scc.pair_indices, &pairs) {
            problematic_scc_indices.push(scc_idx);
            let dp_indices_str: Vec<String> =
                scc.pair_indices.iter().map(|i| i.to_string()).collect();
            reasons.push(format!(
                "SCC {{{}}} has no decreasing ordering",
                dp_indices_str.join(", ")
            ));
        }
    }

    if problematic_scc_indices.is_empty() {
        TerminationResult::Terminating
    } else {
        TerminationResult::PotentiallyNonTerminating {
            reason: reasons.join("; "),
            problematic_sccs: problematic_scc_indices,
        }
    }
}

/// Check whether a non-trivial SCC admits a structural decrease.
///
/// For each dependency pair `⟨f#(t₁,...,tₙ), g#(s₁,...,sₘ)⟩` in the SCC, we
/// check if there exists an argument position `i` (of the source) such that for
/// every pair in the SCC, the target's corresponding argument at position `i`
/// is a proper subterm of the source's argument at position `i` (structural
/// decrease), or the arguments are equal (weak decrease) — with at least one
/// strict decrease in the SCC.
///
/// This is a simple subterm criterion: it checks whether the argument at some
/// shared position strictly decreases in at least one DP of the SCC and weakly
/// decreases (is a subterm or equal) in all others.
fn has_structural_decrease(scc_pair_indices: &[usize], pairs: &[DependencyPair]) -> bool {
    if scc_pair_indices.is_empty() {
        return true;
    }

    // Determine the minimum arity among source terms in this SCC.
    let min_arity = scc_pair_indices
        .iter()
        .filter_map(|&idx| match &pairs[idx].source {
            Term::App { args, .. } => Some(args.len()),
            Term::Var(_) => None,
        })
        .min()
        .unwrap_or(0);

    if min_arity == 0 {
        return false;
    }

    // For each argument position, check if it provides a valid decrease.
    for pos in 0..min_arity {
        let mut all_weakly_decrease = true;
        let mut at_least_one_strict = false;

        for &idx in scc_pair_indices {
            let (source_arg, target_arg) = match (&pairs[idx].source, &pairs[idx].target) {
                (
                    Term::App { args: src_args, .. },
                    Term::App {
                        args: tgt_args, ..
                    },
                ) => {
                    if pos >= src_args.len() || pos >= tgt_args.len() {
                        // This position doesn't exist in both — cannot use it.
                        all_weakly_decrease = false;
                        break;
                    }
                    (&src_args[pos], &tgt_args[pos])
                }
                _ => {
                    all_weakly_decrease = false;
                    break;
                }
            };

            if source_arg == target_arg {
                // Equal: weak decrease (OK).
                continue;
            } else if is_proper_subterm(target_arg, source_arg) {
                // target_arg is a proper subterm of source_arg: strict decrease.
                at_least_one_strict = true;
            } else {
                // Not a subterm relationship: this position fails.
                all_weakly_decrease = false;
                break;
            }
        }

        if all_weakly_decrease && at_least_one_strict {
            return true;
        }
    }

    false
}

/// Check whether `needle` is a proper subterm of `haystack`.
///
/// A term `s` is a proper subterm of `t` if `s` appears as a strict subterm
/// (not equal to `t` itself) within `t`.
fn is_proper_subterm(needle: &Term, haystack: &Term) -> bool {
    match haystack {
        Term::App { args, .. } => {
            for arg in args {
                if arg == needle || is_proper_subterm(needle, arg) {
                    return true;
                }
            }
            false
        }
        Term::Var(_) => false,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline bridge: run termination analysis on grammar syntax.
///
/// Reuses [`crate::confluence::syntax_to_rewrite_rules`] to convert `all_syntax`
/// into rewrite rules, then runs [`check_termination`].
///
/// Returns `None` if no rewrite rules are generated (trivially terminating).
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> Option<TerminationResult> {
    let rules = crate::confluence::syntax_to_rewrite_rules(all_syntax);
    if rules.is_empty() {
        return None;
    }
    Some(check_termination(&rules))
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dependency_pair_display() {
        let dp = DependencyPair {
            source: Term::app("f#", vec![Term::var("x")]),
            target: Term::app("g#", vec![Term::var("x")]),
            rule_index: 0,
        };
        assert_eq!(dp.to_string(), "⟨f#(x), g#(x)⟩ (from rule 0)");
    }

    #[test]
    fn termination_result_display() {
        assert_eq!(TerminationResult::Terminating.to_string(), "Terminating");

        let non_term = TerminationResult::PotentiallyNonTerminating {
            reason: "SCC {0, 1} has no decreasing ordering".to_string(),
            problematic_sccs: vec![0],
        };
        assert!(non_term.to_string().contains("Potentially non-terminating"));
    }

    #[test]
    fn dependency_scc_display() {
        let scc = DependencyScc {
            pair_indices: vec![0, 1, 2],
            has_self_loop: true,
        };
        assert_eq!(scc.to_string(), "SCC(3 pairs, self_loop: true)");
    }

    // ── extract_dependency_pairs tests ──────────────────────────────────────

    #[test]
    fn extract_dp_simple_recursive() {
        // f(s(x)) → f(x)
        // Defined symbols: {f}
        // RHS f(x) is rooted at defined symbol f → DP ⟨f#(s(x)), f#(x)⟩
        let rules = vec![RewriteRule::new(
            Term::app("f", vec![Term::app("s", vec![Term::var("x")])]),
            Term::app("f", vec![Term::var("x")]),
        )];
        let pairs = extract_dependency_pairs(&rules);
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].source.to_string(), "f#(s(x))");
        assert_eq!(pairs[0].target.to_string(), "f#(x)");
        assert_eq!(pairs[0].rule_index, 0);
    }

    #[test]
    fn extract_dp_no_defined_rhs() {
        // f(x) → g(x) where g is NOT a defined symbol (not on any LHS root).
        // No dependency pairs should be extracted.
        let rules = vec![RewriteRule::new(
            Term::app("f", vec![Term::var("x")]),
            Term::app("g", vec![Term::var("x")]),
        )];
        let pairs = extract_dependency_pairs(&rules);
        assert!(
            pairs.is_empty(),
            "g is not defined — no DPs expected, got {:?}",
            pairs,
        );
    }

    #[test]
    fn extract_dp_mutual_recursion() {
        // f(x) → g(x) and g(x) → f(x)
        // Defined symbols: {f, g}
        // Rule 0: f→g produces ⟨f#(x), g#(x)⟩
        // Rule 1: g→f produces ⟨g#(x), f#(x)⟩
        let rules = vec![
            RewriteRule::new(
                Term::app("f", vec![Term::var("x")]),
                Term::app("g", vec![Term::var("x")]),
            ),
            RewriteRule::new(
                Term::app("g", vec![Term::var("x")]),
                Term::app("f", vec![Term::var("x")]),
            ),
        ];
        let pairs = extract_dependency_pairs(&rules);
        assert_eq!(pairs.len(), 2);
        assert_eq!(pairs[0].source.to_string(), "f#(x)");
        assert_eq!(pairs[0].target.to_string(), "g#(x)");
        assert_eq!(pairs[1].source.to_string(), "g#(x)");
        assert_eq!(pairs[1].target.to_string(), "f#(x)");
    }

    // ── build_dependency_graph tests ────────────────────────────────────────

    #[test]
    fn build_graph_self_loop() {
        // f(s(x)) → f(x): single DP with self-loop (f#(s(x)) unifies with f#(y)).
        let rules = vec![RewriteRule::new(
            Term::app("f", vec![Term::app("s", vec![Term::var("x")])]),
            Term::app("f", vec![Term::var("x")]),
        )];
        let pairs = extract_dependency_pairs(&rules);
        assert_eq!(pairs.len(), 1);

        let sccs = build_dependency_graph(&pairs);
        // Single SCC with self-loop.
        assert_eq!(sccs.len(), 1);
        assert!(sccs[0].has_self_loop);
        assert_eq!(sccs[0].pair_indices.len(), 1);
    }

    #[test]
    fn build_graph_mutual_scc() {
        // f(x) → g(x), g(x) → f(x) — two DPs forming a mutual cycle.
        let rules = vec![
            RewriteRule::new(
                Term::app("f", vec![Term::var("x")]),
                Term::app("g", vec![Term::var("x")]),
            ),
            RewriteRule::new(
                Term::app("g", vec![Term::var("x")]),
                Term::app("f", vec![Term::var("x")]),
            ),
        ];
        let pairs = extract_dependency_pairs(&rules);
        let sccs = build_dependency_graph(&pairs);

        // Should have at least one SCC containing both DPs (indices 0 and 1).
        let multi_scc = sccs
            .iter()
            .find(|scc| scc.pair_indices.len() == 2);
        assert!(
            multi_scc.is_some(),
            "Expected a 2-element SCC for mutual recursion, got {:?}",
            sccs,
        );
    }

    // ── check_termination tests ─────────────────────────────────────────────

    #[test]
    fn termination_empty_rules() {
        assert_eq!(check_termination(&[]), TerminationResult::Terminating);
    }

    #[test]
    fn termination_no_recursion() {
        // f(x) → a (constant) — no defined symbol on RHS → no DPs → terminating.
        let rules = vec![RewriteRule::new(
            Term::app("f", vec![Term::var("x")]),
            Term::constant("a"),
        )];
        assert_eq!(check_termination(&rules), TerminationResult::Terminating);
    }

    #[test]
    fn termination_structural_decrease() {
        // f(s(x)) → f(x): the argument strictly decreases (x is a proper subterm
        // of s(x)), so this system terminates.
        let rules = vec![RewriteRule::new(
            Term::app("f", vec![Term::app("s", vec![Term::var("x")])]),
            Term::app("f", vec![Term::var("x")]),
        )];
        assert_eq!(check_termination(&rules), TerminationResult::Terminating);
    }

    #[test]
    fn termination_non_decreasing() {
        // f(x) → f(x): the argument does not decrease — self-loop with no
        // structural decrease (equal, not strictly less). This is an infinite
        // loop if the rule ever fires, but in the DP framework, having every DP
        // in the SCC be weak (equal) with none strict means we cannot prove
        // termination.
        //
        // Actually f(x) → f(x): the sole DP is ⟨f#(x), f#(x)⟩. At position 0,
        // source_arg = x and target_arg = x — they are equal. We need at least
        // one strict decrease in the SCC, so this fails.
        let rules = vec![RewriteRule::new(
            Term::app("f", vec![Term::var("x")]),
            Term::app("f", vec![Term::var("x")]),
        )];
        let result = check_termination(&rules);
        assert!(
            matches!(result, TerminationResult::PotentiallyNonTerminating { .. }),
            "Expected PotentiallyNonTerminating for f(x)→f(x), got {:?}",
            result,
        );
    }

    #[test]
    fn termination_ackermann_like_non_terminating_by_structural() {
        // A(s(x), y) → A(x, s(y)): first arg decreases, second increases.
        // Structural decrease on position 0: s(x) → x (strict decrease). Terminates.
        //
        // But combine with: A(0, y) → y (base case, no DP since rhs is a variable).
        // Only the recursive rule produces a DP. Position 0 decreases. Terminating.
        let rules = vec![
            RewriteRule::new(
                Term::app("A", vec![
                    Term::app("s", vec![Term::var("x")]),
                    Term::var("y"),
                ]),
                Term::app("A", vec![Term::var("x"), Term::app("s", vec![Term::var("y")])]),
            ),
            RewriteRule::new(
                Term::app("A", vec![Term::constant("0"), Term::var("y")]),
                Term::var("y"),
            ),
        ];
        assert_eq!(check_termination(&rules), TerminationResult::Terminating);
    }

    // ── Helpers: unification, proper subterm ────────────────────────────────

    #[test]
    fn unify_identical_vars() {
        let result = unify(&Term::var("x"), &Term::var("x"));
        assert!(result.is_some());
    }

    #[test]
    fn unify_var_with_term() {
        let result = unify(&Term::var("x"), &Term::app("f", vec![Term::var("y")]));
        assert!(result.is_some());
        let subst = result.expect("unification should succeed");
        assert_eq!(
            subst.get("x").expect("x should be bound"),
            &Term::app("f", vec![Term::var("y")]),
        );
    }

    #[test]
    fn unify_clash() {
        // f(x) vs g(x): symbol clash.
        let result = unify(
            &Term::app("f", vec![Term::var("x")]),
            &Term::app("g", vec![Term::var("x")]),
        );
        assert!(result.is_none());
    }

    #[test]
    fn unify_occurs_check() {
        // x vs f(x): occurs check should fail.
        let result = unify(&Term::var("x"), &Term::app("f", vec![Term::var("x")]));
        assert!(
            result.is_none(),
            "Occurs check should prevent x = f(x)",
        );
    }

    #[test]
    fn proper_subterm_positive() {
        // x is a proper subterm of f(x, y).
        assert!(is_proper_subterm(
            &Term::var("x"),
            &Term::app("f", vec![Term::var("x"), Term::var("y")]),
        ));
    }

    #[test]
    fn proper_subterm_not_self() {
        // f(x) is NOT a proper subterm of f(x) (must be *proper*).
        let t = Term::app("f", vec![Term::var("x")]);
        assert!(!is_proper_subterm(&t, &t));
    }

    #[test]
    fn test_analyze_from_bundle_basic() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![
            (
                "Add".to_string(),
                "Expr".to_string(),
                vec![
                    crate::SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "a".to_string(),
                    },
                    crate::SyntaxItemSpec::Terminal("+".to_string()),
                    crate::SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "b".to_string(),
                    },
                ],
            ),
        ];
        let result = analyze_from_bundle(&syntax);
        assert!(result.is_some(), "should produce termination analysis");
    }

    #[test]
    fn test_analyze_from_bundle_empty() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![];
        let result = analyze_from_bundle(&syntax);
        assert!(result.is_none(), "should return None for empty syntax");
    }
}
