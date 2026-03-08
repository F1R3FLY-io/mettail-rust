//! Critical pair detection and joinability checking for Knuth-Bendix completion.
//!
//! Implements the confluence analysis component of term rewriting system (TRS) theory.
//! Critical pairs arise when two rewrite rules overlap — i.e., the left-hand side
//! of one rule unifies with a non-variable subterm of another. A TRS is confluent
//! (Church-Rosser) if and only if all critical pairs are joinable (Knuth-Bendix
//! criterion).
//!
//! ## Theoretical Foundations
//!
//! - **Knuth & Bendix (1970)** — "Simple word problems in universal algebras."
//!   The completion procedure that extends a TRS to confluence by orienting critical
//!   pairs into new rewrite rules.
//! - **Huet (1980)** — "Confluent reductions: abstract properties and applications
//!   to term rewriting systems." Establishes that joinability of critical pairs is
//!   necessary and sufficient for local confluence (Newman's Lemma + termination →
//!   confluence).
//! - **Baader & Nipkow (1998)** — *Term Rewriting and All That*, Chapter 6.
//!   Standard reference for unification, overlap, and critical pair computation.
//!
//! ## Architecture
//!
//! ```text
//! RewriteRule set
//!       │
//!       ▼
//! detect_critical_pairs()
//!       │
//!       ▼
//! Vec<CriticalPair>
//!       │
//!       ▼
//! check_joinability() ──→ JoinabilityResult
//!       │
//!       ▼
//! check_confluence() ──→ ConfluenceAnalysis
//! ```
//!
//! ## PraTTaIL Integration
//!
//! Critical pair analysis is used to verify that user-defined rewrite/equation
//! blocks in the `language!` macro produce a confluent TRS. Non-joinable critical
//! pairs are surfaced as lint diagnostics (severity: Warning) with witness terms.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

// NOTE: Semiring import will be used when critical pair weight analysis is implemented.
#[allow(unused_imports)]
use crate::automata::semiring::Semiring;
use crate::repair::{RepairAction, RepairKind, RepairSet, RepairSuggestion};

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A term in the rewriting system.
///
/// Terms are built from variables, constants (nullary functions), and
/// function applications `f(t₁, ..., tₙ)`. This representation is shared
/// with the termination analysis module.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A variable, identified by name (e.g., `"x"`, `"y"`).
    Var(String),
    /// A function application `f(t₁, ..., tₙ)`. Constants have arity 0.
    App {
        /// Function symbol name.
        symbol: String,
        /// Subterm arguments (empty for constants).
        args: Vec<Term>,
    },
}

impl Term {
    /// Create a variable term.
    pub fn var(name: impl Into<String>) -> Self {
        Term::Var(name.into())
    }

    /// Create a constant (nullary function) term.
    pub fn constant(symbol: impl Into<String>) -> Self {
        Term::App {
            symbol: symbol.into(),
            args: Vec::new(),
        }
    }

    /// Create a function application term.
    pub fn app(symbol: impl Into<String>, args: Vec<Term>) -> Self {
        Term::App {
            symbol: symbol.into(),
            args,
        }
    }

    /// Check whether this term is a variable.
    pub fn is_var(&self) -> bool {
        matches!(self, Term::Var(_))
    }

    /// Collect all variable names occurring in this term.
    pub fn variables(&self) -> Vec<&str> {
        let mut vars = Vec::new();
        self.collect_variables(&mut vars);
        vars
    }

    fn collect_variables<'a>(&'a self, acc: &mut Vec<&'a str>) {
        match self {
            Term::Var(name) => acc.push(name.as_str()),
            Term::App { args, .. } => {
                for arg in args {
                    arg.collect_variables(acc);
                }
            }
        }
    }

    /// Apply a substitution to this term, returning a new term.
    pub fn apply_substitution(&self, subst: &HashMap<String, Term>) -> Term {
        match self {
            Term::Var(name) => {
                if let Some(replacement) = subst.get(name) {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            Term::App { symbol, args } => Term::App {
                symbol: symbol.clone(),
                args: args.iter().map(|a| a.apply_substitution(subst)).collect(),
            },
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(name) => write!(f, "{}", name),
            Term::App { symbol, args } if args.is_empty() => write!(f, "{}", symbol),
            Term::App { symbol, args } => {
                write!(f, "{}(", symbol)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A rewrite rule `l → r` in the TRS.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteRule {
    /// Left-hand side (pattern to match).
    pub lhs: Term,
    /// Right-hand side (replacement term).
    pub rhs: Term,
    /// Optional label for diagnostics.
    pub label: Option<String>,
}

impl RewriteRule {
    /// Create a new rewrite rule.
    pub fn new(lhs: Term, rhs: Term) -> Self {
        RewriteRule {
            lhs,
            rhs,
            label: None,
        }
    }

    /// Create a labeled rewrite rule.
    pub fn labeled(label: impl Into<String>, lhs: Term, rhs: Term) -> Self {
        RewriteRule {
            lhs,
            rhs,
            label: Some(label.into()),
        }
    }
}

impl fmt::Display for RewriteRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ref label) = self.label {
            write!(f, "[{}] {} → {}", label, self.lhs, self.rhs)
        } else {
            write!(f, "{} → {}", self.lhs, self.rhs)
        }
    }
}

/// A critical pair arising from overlapping rewrite rules.
///
/// When rule₁'s LHS unifies with a non-variable subterm of rule₂'s LHS at
/// position `p`, the critical pair `⟨r₁σ, l₂[r₂]_p σ⟩` is generated, where
/// `σ` is the most general unifier.
#[derive(Debug, Clone)]
pub struct CriticalPair {
    /// First reduct: the result of applying rule₁ at the overlap position.
    pub term1: Term,
    /// Second reduct: the result of applying rule₂ to the full term.
    pub term2: Term,
    /// Index of the first rule involved.
    pub rule1_index: usize,
    /// Index of the second rule involved.
    pub rule2_index: usize,
    /// Position (path of argument indices) where the overlap occurs.
    pub overlap_position: Vec<usize>,
}

impl fmt::Display for CriticalPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "⟨{}, {}⟩ (rules {}, {} at position {:?})",
            self.term1, self.term2, self.rule1_index, self.rule2_index, self.overlap_position,
        )
    }
}

/// Result of checking whether a critical pair is joinable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JoinabilityResult {
    /// The critical pair is joinable: both terms reduce to a common reduct.
    Joinable {
        /// The common normal form (if found within the reduction limit).
        common_reduct: Term,
    },
    /// The critical pair is not joinable within the given reduction bound.
    NotJoinable {
        /// Normal form of the first term (or last reduct if not normalizing).
        normal_form1: Term,
        /// Normal form of the second term (or last reduct if not normalizing).
        normal_form2: Term,
    },
    /// Could not determine joinability (reduction limit exceeded without
    /// reaching normal forms).
    Unknown {
        /// Reason the analysis was inconclusive.
        reason: String,
    },
}

impl fmt::Display for JoinabilityResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            JoinabilityResult::Joinable { common_reduct } => {
                write!(f, "Joinable (common reduct: {})", common_reduct)
            }
            JoinabilityResult::NotJoinable {
                normal_form1,
                normal_form2,
            } => {
                write!(
                    f,
                    "Not joinable ({} ≠ {})",
                    normal_form1, normal_form2,
                )
            }
            JoinabilityResult::Unknown { reason } => {
                write!(f, "Unknown ({})", reason)
            }
        }
    }
}

/// Overall result of confluence analysis for a TRS.
#[derive(Debug, Clone)]
pub struct ConfluenceAnalysis {
    /// Whether the TRS is confluent (all critical pairs joinable).
    pub is_confluent: bool,
    /// All critical pairs found.
    pub critical_pairs: Vec<CriticalPair>,
    /// Joinability results for each critical pair (parallel indexing).
    pub joinability_results: Vec<JoinabilityResult>,
    /// Number of non-joinable critical pairs.
    pub non_joinable_count: usize,
    /// Number of pairs where joinability could not be determined.
    pub unknown_count: usize,
}

impl fmt::Display for ConfluenceAnalysis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ConfluenceAnalysis {{ confluent: {}, critical_pairs: {}, non_joinable: {}, unknown: {} }}",
            self.is_confluent,
            self.critical_pairs.len(),
            self.non_joinable_count,
            self.unknown_count,
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Helpers: Unification, variable renaming, subterm positions, rewriting
// ══════════════════════════════════════════════════════════════════════════════

/// A position within a term, represented as a path of argument indices.
///
/// The empty path `[]` denotes the root. `[1, 0]` denotes "second argument,
/// then first argument of that subterm."
type Position = Vec<usize>;

/// Retrieve the subterm at a given position, or `None` if the position is invalid.
fn subterm_at<'a>(term: &'a Term, pos: &[usize]) -> Option<&'a Term> {
    if pos.is_empty() {
        return Some(term);
    }
    match term {
        Term::Var(_) => None,
        Term::App { args, .. } => {
            let idx = pos[0];
            if idx < args.len() {
                subterm_at(&args[idx], &pos[1..])
            } else {
                None
            }
        }
    }
}

/// Replace the subterm at a given position with `replacement`.
///
/// Returns `None` if the position is invalid.
#[allow(dead_code)]
fn replace_at(term: &Term, pos: &[usize], replacement: &Term) -> Option<Term> {
    if pos.is_empty() {
        return Some(replacement.clone());
    }
    match term {
        Term::Var(_) => None,
        Term::App { symbol, args } => {
            let idx = pos[0];
            if idx >= args.len() {
                return None;
            }
            let inner = replace_at(&args[idx], &pos[1..], replacement)?;
            let mut new_args = args.clone();
            new_args[idx] = inner;
            Some(Term::App {
                symbol: symbol.clone(),
                args: new_args,
            })
        }
    }
}

/// Enumerate all positions of non-variable subterms in a term.
///
/// Each position is a path of argument indices from the root.
fn non_var_positions(term: &Term) -> Vec<Position> {
    let mut positions = Vec::new();
    collect_non_var_positions(term, &mut Vec::new(), &mut positions);
    positions
}

fn collect_non_var_positions(
    term: &Term,
    current: &mut Vec<usize>,
    acc: &mut Vec<Position>,
) {
    match term {
        Term::Var(_) => {
            // Variables are excluded — we only want non-variable subterms.
        }
        Term::App { args, .. } => {
            acc.push(current.clone());
            for (i, arg) in args.iter().enumerate() {
                current.push(i);
                collect_non_var_positions(arg, current, acc);
                current.pop();
            }
        }
    }
}

/// Rename all variables in a term by appending the given suffix.
///
/// Used to ensure two rules being overlapped have disjoint variable sets.
fn rename_variables(term: &Term, suffix: &str) -> Term {
    match term {
        Term::Var(name) => Term::Var(format!("{}{}", name, suffix)),
        Term::App { symbol, args } => Term::App {
            symbol: symbol.clone(),
            args: args.iter().map(|a| rename_variables(a, suffix)).collect(),
        },
    }
}

/// Compose two substitutions: apply `second` to the range of `first`, then
/// merge, giving priority to `first`'s domain.
fn compose_substitutions(
    first: &HashMap<String, Term>,
    second: &HashMap<String, Term>,
) -> HashMap<String, Term> {
    let mut result: HashMap<String, Term> = first
        .iter()
        .map(|(k, v)| (k.clone(), v.apply_substitution(second)))
        .collect();
    for (k, v) in second {
        result.entry(k.clone()).or_insert_with(|| v.clone());
    }
    result
}

/// Robinson's unification algorithm.
///
/// Given two terms `s` and `t`, compute the most general unifier (MGU) `σ`
/// such that `sσ = tσ`, or return `None` if no such substitution exists.
///
/// Uses an iterative worklist approach (no recursion) with an occurs check
/// to prevent infinite (cyclic) substitutions.
fn unify(s: &Term, t: &Term) -> Option<HashMap<String, Term>> {
    let mut subst: HashMap<String, Term> = HashMap::new();
    let mut worklist: VecDeque<(Term, Term)> = VecDeque::new();
    worklist.push_back((s.clone(), t.clone()));

    while let Some((lhs, rhs)) = worklist.pop_front() {
        // Apply current substitution to both sides.
        let lhs = lhs.apply_substitution(&subst);
        let rhs = rhs.apply_substitution(&subst);

        if lhs == rhs {
            continue;
        }

        match (lhs, rhs) {
            (Term::Var(x), t) => {
                // Occurs check: x must not appear in t.
                if occurs(&x, &t) {
                    return None;
                }
                // Extend substitution: apply {x ↦ t} to existing bindings.
                let singleton = {
                    let mut m = HashMap::with_capacity(1);
                    m.insert(x.clone(), t.clone());
                    m
                };
                subst = compose_substitutions(&subst, &singleton);
                subst.insert(x, t);
            }
            (t, Term::Var(x)) => {
                if occurs(&x, &t) {
                    return None;
                }
                let singleton = {
                    let mut m = HashMap::with_capacity(1);
                    m.insert(x.clone(), t.clone());
                    m
                };
                subst = compose_substitutions(&subst, &singleton);
                subst.insert(x, t);
            }
            (
                Term::App {
                    symbol: f,
                    args: f_args,
                },
                Term::App {
                    symbol: g,
                    args: g_args,
                },
            ) => {
                if f != g || f_args.len() != g_args.len() {
                    return None;
                }
                for (a, b) in f_args.into_iter().zip(g_args.into_iter()) {
                    worklist.push_back((a, b));
                }
            }
        }
    }

    Some(subst)
}

/// Occurs check: does variable `var` appear anywhere in `term`?
fn occurs(var: &str, term: &Term) -> bool {
    match term {
        Term::Var(name) => name == var,
        Term::App { args, .. } => args.iter().any(|a| occurs(var, a)),
    }
}

/// Try to apply the first matching rewrite rule to the leftmost-outermost
/// redex in `term`. Returns `Some(reduct)` if a rule fired, `None` if no
/// rule applies anywhere.
fn rewrite_once(term: &Term, rules: &[RewriteRule]) -> Option<Term> {
    // Try to match at the root first (outermost).
    for rule in rules {
        if let Some(subst) = match_term(&rule.lhs, term) {
            return Some(rule.rhs.apply_substitution(&subst));
        }
    }
    // Recurse into subterms (leftmost first).
    match term {
        Term::Var(_) => None,
        Term::App { symbol, args } => {
            for (i, arg) in args.iter().enumerate() {
                if let Some(reduct) = rewrite_once(arg, rules) {
                    let mut new_args = args.clone();
                    new_args[i] = reduct;
                    return Some(Term::App {
                        symbol: symbol.clone(),
                        args: new_args,
                    });
                }
            }
            None
        }
    }
}

/// One-way pattern matching: check if `pattern` matches `term`, producing
/// a substitution for the pattern's variables. Unlike unification, the term
/// is treated as ground (its variables are not unified against).
fn match_term(pattern: &Term, term: &Term) -> Option<HashMap<String, Term>> {
    let mut subst = HashMap::new();
    if match_term_inner(pattern, term, &mut subst) {
        Some(subst)
    } else {
        None
    }
}

fn match_term_inner(
    pattern: &Term,
    term: &Term,
    subst: &mut HashMap<String, Term>,
) -> bool {
    match pattern {
        Term::Var(name) => {
            if let Some(existing) = subst.get(name) {
                existing == term
            } else {
                subst.insert(name.clone(), term.clone());
                true
            }
        }
        Term::App {
            symbol: f,
            args: f_args,
        } => match term {
            Term::Var(_) => false,
            Term::App {
                symbol: g,
                args: g_args,
            } => {
                if f != g || f_args.len() != g_args.len() {
                    return false;
                }
                for (p, t) in f_args.iter().zip(g_args.iter()) {
                    if !match_term_inner(p, t, subst) {
                        return false;
                    }
                }
                true
            }
        },
    }
}

/// Reduce a term to normal form (or as far as possible within `max_steps`).
///
/// Returns `(normal_form, true)` if a normal form was reached (no rule applies),
/// or `(last_reduct, false)` if the step limit was exhausted.
fn normalize(term: &Term, rules: &[RewriteRule], max_steps: usize) -> (Term, bool) {
    let mut current = term.clone();
    let mut visited: HashSet<Term> = HashSet::new();
    visited.insert(current.clone());

    for _ in 0..max_steps {
        match rewrite_once(&current, rules) {
            None => return (current, true),
            Some(next) => {
                if !visited.insert(next.clone()) {
                    // We have entered a cycle — cannot reach a normal form.
                    return (current, false);
                }
                current = next;
            }
        }
    }
    (current, false)
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

/// Detect all critical pairs in a set of rewrite rules.
///
/// For each pair of rules `(r_i, r_j)` (including `i = j` for self-overlaps),
/// computes all non-trivial overlaps where the LHS of `r_i` unifies with a
/// non-variable subterm of `r_j`'s LHS. Each overlap yields a critical pair.
///
/// Variables in rule `r_i` are renamed (suffixed with `"'"`)) to ensure the
/// two rules have disjoint variable sets before unification.
///
/// Self-overlaps at the root position (where `i = j`) are excluded because
/// they produce trivial critical pairs `⟨r, r⟩`.
///
/// # Arguments
///
/// * `rules` - The rewrite rules of the TRS.
///
/// # Returns
///
/// A vector of all critical pairs found.
pub fn detect_critical_pairs(rules: &[RewriteRule]) -> Vec<CriticalPair> {
    let mut pairs = Vec::new();

    for (i, rule_i) in rules.iter().enumerate() {
        // Rename variables in rule_i to avoid capture.
        let lhs_i = rename_variables(&rule_i.lhs, "'");
        let rhs_i = rename_variables(&rule_i.rhs, "'");

        for (j, rule_j) in rules.iter().enumerate() {
            // rule_j is used without renaming (its variables are kept as-is).
            let positions = non_var_positions(&rule_j.lhs);

            for pos in &positions {
                // Skip the trivial self-overlap at the root of the same rule.
                if i == j && pos.is_empty() {
                    continue;
                }

                let subterm = subterm_at(&rule_j.lhs, pos)
                    .expect("non_var_positions returned an invalid position");

                if let Some(sigma) = unify(&lhs_i, subterm) {
                    // term1: apply sigma to rhs of rule_i (the "inner" rewrite).
                    let term1 = rhs_i.apply_substitution(&sigma);

                    // term2: in rule_j's LHS, replace the subterm at `pos` with
                    // rhs_i·sigma, then apply sigma to the outer context — this
                    // is equivalent to applying sigma to (lhs_j[rhs_i / pos]).
                    // But the standard definition is:
                    //   term2 = (rule_j.rhs)·sigma
                    // because rule_j would fire at the root of lhs_j·sigma.
                    let term2 = rule_j.rhs.apply_substitution(&sigma);

                    pairs.push(CriticalPair {
                        term1,
                        term2,
                        rule1_index: i,
                        rule2_index: j,
                        overlap_position: pos.clone(),
                    });
                }
            }
        }
    }

    pairs
}

/// Check whether a single critical pair is joinable under the given TRS.
///
/// Attempts to reduce both terms of the critical pair to normal form using
/// the rewrite rules, then checks if the normal forms are syntactically equal.
///
/// Uses leftmost-outermost (normal order) reduction with a visited set to
/// detect cycles. If both terms reach syntactically equal reducts at any point
/// during normalization, the pair is joinable.
///
/// # Arguments
///
/// * `pair` - The critical pair to check.
/// * `rules` - The rewrite rules of the TRS.
/// * `max_steps` - Maximum number of reduction steps per term.
///
/// # Returns
///
/// A `JoinabilityResult` indicating whether the pair is joinable, not joinable,
/// or undetermined.
pub fn check_joinability(
    pair: &CriticalPair,
    rules: &[RewriteRule],
    max_steps: usize,
) -> JoinabilityResult {
    let (nf1, reached1) = normalize(&pair.term1, rules, max_steps);
    let (nf2, reached2) = normalize(&pair.term2, rules, max_steps);

    if nf1 == nf2 {
        return JoinabilityResult::Joinable {
            common_reduct: nf1,
        };
    }

    if reached1 && reached2 {
        // Both reached normal forms but they differ — not joinable.
        JoinabilityResult::NotJoinable {
            normal_form1: nf1,
            normal_form2: nf2,
        }
    } else {
        // At least one side did not reach a normal form within the step limit.
        JoinabilityResult::Unknown {
            reason: format!(
                "reduction limit ({}) exceeded: term1 {}normalized, term2 {}normalized",
                max_steps,
                if reached1 { "" } else { "not " },
                if reached2 { "" } else { "not " },
            ),
        }
    }
}

/// Perform a full confluence analysis on a TRS.
///
/// Computes all critical pairs via [`detect_critical_pairs`], then checks each
/// for joinability via [`check_joinability`]. The TRS is confluent if and only
/// if all critical pairs are joinable (assuming termination — see the
/// `termination` module).
///
/// # Arguments
///
/// * `rules` - The rewrite rules of the TRS.
/// * `max_steps` - Maximum reduction steps per joinability check.
///
/// # Returns
///
/// A `ConfluenceAnalysis` summarizing the results.
pub fn check_confluence(rules: &[RewriteRule], max_steps: usize) -> ConfluenceAnalysis {
    let critical_pairs = detect_critical_pairs(rules);
    let joinability_results: Vec<JoinabilityResult> = critical_pairs
        .iter()
        .map(|cp| check_joinability(cp, rules, max_steps))
        .collect();

    let non_joinable_count = joinability_results
        .iter()
        .filter(|r| matches!(r, JoinabilityResult::NotJoinable { .. }))
        .count();

    let unknown_count = joinability_results
        .iter()
        .filter(|r| matches!(r, JoinabilityResult::Unknown { .. }))
        .count();

    let is_confluent = non_joinable_count == 0 && unknown_count == 0;

    ConfluenceAnalysis {
        is_confluent,
        critical_pairs,
        joinability_results,
        non_joinable_count,
        unknown_count,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Repair suggestion generation
// ══════════════════════════════════════════════════════════════════════════════

/// Compute a structural similarity score between two terms.
///
/// Returns a value in [0.0, 1.0]:
/// - 1.0 if the terms are identical,
/// - 0.0 if they share no structure at all,
/// - intermediate values based on shared function symbols, argument counts,
///   and recursive subterm similarity.
///
/// Used to modulate confidence in repair suggestions: terms with high
/// structural similarity are more likely to benefit from an equation or
/// oriented rewrite than terms with entirely different root symbols.
fn structural_similarity(t1: &Term, t2: &Term) -> f64 {
    match (t1, t2) {
        (Term::Var(a), Term::Var(b)) => {
            if a == b { 1.0 } else { 0.5 }
        }
        (Term::Var(_), Term::App { .. }) | (Term::App { .. }, Term::Var(_)) => 0.25,
        (
            Term::App {
                symbol: f,
                args: f_args,
            },
            Term::App {
                symbol: g,
                args: g_args,
            },
        ) => {
            if f != g {
                // Different root symbols — minimal similarity.
                // Still check if any subterms share structure.
                if f_args.is_empty() && g_args.is_empty() {
                    return 0.0;
                }
                return 0.1;
            }
            // Same root symbol.
            if f_args.is_empty() && g_args.is_empty() {
                return 1.0;
            }
            if f_args.len() != g_args.len() {
                return 0.3;
            }
            // Recursively score sub-arguments.
            let arg_sim: f64 = f_args
                .iter()
                .zip(g_args.iter())
                .map(|(a, b)| structural_similarity(a, b))
                .sum();
            let avg_arg_sim = arg_sim / f_args.len() as f64;
            // Root symbol match contributes 0.5, argument similarity 0.5.
            0.5 + 0.5 * avg_arg_sim
        }
    }
}

/// Decide an orientation preference for a new rewrite rule between two terms.
///
/// Heuristic: prefer to rewrite the "larger" term (by node count) to the
/// "smaller" one, since this is more likely to preserve termination.
/// Returns `(lhs, rhs)` in the suggested orientation.
fn orient_terms<'a>(t1: &'a Term, t2: &'a Term) -> (&'a Term, &'a Term) {
    fn node_count(t: &Term) -> usize {
        match t {
            Term::Var(_) => 1,
            Term::App { args, .. } => 1 + args.iter().map(node_count).sum::<usize>(),
        }
    }
    if node_count(t1) >= node_count(t2) {
        (t1, t2)
    } else {
        (t2, t1)
    }
}

/// Generate repair suggestions from a confluence analysis result.
///
/// For each non-joinable critical pair `(t1, t2)`, two suggestions are produced:
///
/// 1. **Add an equation** `t1 = t2` — declares the terms equivalent without
///    committing to a rewrite direction. Edit cost = 1 (minimal syntactic change).
///
/// 2. **Add a rewrite rule** `t1 ~> t2` (or `t2 ~> t1`) — oriented using a
///    size heuristic (larger → smaller) to preserve termination. Edit cost = 2
///    because orientation analysis and termination checking are needed.
///
/// Confidence is modulated by `structural_similarity`:
/// - High similarity (≥ 0.5) → higher confidence (0.7–0.9) that either fix
///   will restore confluence.
/// - Low similarity (< 0.5) → lower confidence (0.4–0.6) — the terms may
///   indicate a deeper design flaw.
///
/// The `alternative_count` field on each suggestion is set to 2, reflecting
/// that both an equation and a rewrite are viable alternatives.
///
/// Unknown-joinability pairs are also processed with reduced confidence (halved),
/// since the analysis was inconclusive.
pub fn suggest_confluence_repairs(result: &ConfluenceAnalysis) -> RepairSet {
    let mut repairs = RepairSet::new();

    for (i, jr) in result.joinability_results.iter().enumerate() {
        let (t1, t2, confidence_scale) = match jr {
            JoinabilityResult::NotJoinable {
                normal_form1,
                normal_form2,
            } => (normal_form1, normal_form2, 1.0),
            JoinabilityResult::Unknown { .. } => {
                // For unknown pairs, use the original critical pair terms with
                // reduced confidence since we cannot confirm non-joinability.
                let cp = &result.critical_pairs[i];
                (&cp.term1, &cp.term2, 0.5)
            }
            JoinabilityResult::Joinable { .. } => continue,
        };

        let similarity = structural_similarity(t1, t2);
        let base_confidence = if similarity >= 0.5 {
            0.7 + 0.2 * similarity
        } else {
            0.4 + 0.2 * similarity
        };
        let confidence = base_confidence * confidence_scale;

        // Suggestion 1: Add an equation t1 = t2.
        let eq_description = format!(
            "Add equation {} = {} to restore confluence (critical pair from rules {}, {})",
            t1,
            t2,
            result.critical_pairs[i].rule1_index,
            result.critical_pairs[i].rule2_index,
        );
        repairs.add(
            RepairSuggestion::new(
                RepairKind::FixConfluence,
                eq_description,
                RepairAction::AddEquation {
                    lhs: t1.to_string(),
                    rhs: t2.to_string(),
                },
            )
            .with_confidence(confidence)
            .with_edit_cost(1)
            .with_alternatives(2),
        );

        // Suggestion 2: Add a rewrite rule, oriented by size heuristic.
        let (lhs, rhs) = orient_terms(t1, t2);
        let direction = if std::ptr::eq(lhs, t1) {
            "left-to-right"
        } else {
            "right-to-left"
        };
        let rw_description = format!(
            "Add rewrite {} -> {} ({}) to restore confluence (critical pair from rules {}, {})",
            lhs,
            rhs,
            direction,
            result.critical_pairs[i].rule1_index,
            result.critical_pairs[i].rule2_index,
        );
        repairs.add(
            RepairSuggestion::new(
                RepairKind::FixConfluence,
                rw_description,
                RepairAction::AddRewrite {
                    lhs: lhs.to_string(),
                    rhs: rhs.to_string(),
                    direction: direction.to_string(),
                },
            )
            .with_confidence(confidence * 0.9) // Slightly lower: orientation may be wrong.
            .with_edit_cost(2)
            .with_alternatives(2),
        );
    }

    repairs
}

/// Generate repair suggestions for a non-terminating rewrite cycle.
///
/// Given a sequence of terms forming a cycle `t₀ → t₁ → ... → tₙ → t₀`,
/// produces suggestions to break the cycle:
///
/// 1. **Add guard conditions** — for each rule `tᵢ → tᵢ₊₁` in the cycle,
///    suggest adding a side condition (guard) that prevents the rule from firing
///    when the cycle would recur. This is the least invasive fix.
///
/// 2. **Restrict LHS patterns** — for each rule in the cycle, suggest making
///    the LHS pattern more specific so it does not match as broadly. This reduces
///    the rule's applicability and can break the cycle.
///
/// Edit costs:
/// - Guard condition: 2 (requires adding a boolean predicate).
/// - LHS restriction: 3 (requires restructuring the pattern, potentially
///   splitting into multiple specialized rules).
///
/// Confidence is set to 0.6 for guards (commonly effective) and 0.5 for
/// restrictions (may break intended behavior).
///
/// Returns an empty `RepairSet` if the cycle has fewer than 2 terms.
pub fn suggest_termination_repair(cycle_terms: &[Term]) -> RepairSet {
    let mut repairs = RepairSet::new();

    if cycle_terms.len() < 2 {
        return repairs;
    }

    let cycle_len = cycle_terms.len();

    // For each edge in the cycle, suggest a guard and an LHS restriction.
    for i in 0..cycle_len {
        let from = &cycle_terms[i];
        let to = &cycle_terms[(i + 1) % cycle_len];

        // Suggestion 1: Add a guard condition to the rule t_i -> t_{i+1}.
        let guard_desc = format!(
            "Add guard condition to rule {} -> {} to break non-terminating cycle \
             (cycle length {})",
            from, to, cycle_len,
        );
        repairs.add(
            RepairSuggestion::new(
                RepairKind::FixTermination,
                guard_desc,
                RepairAction::Description(format!(
                    "Add a side condition (guard) to prevent the rewrite {} -> {} \
                     from firing when it would re-enter the cycle: \
                     e.g., require a decreasing measure on a well-founded order",
                    from, to,
                )),
            )
            .with_confidence(0.6)
            .with_edit_cost(2)
            .with_alternatives(cycle_len as u64),
        );

        // Suggestion 2: Restrict the LHS pattern.
        let restrict_desc = format!(
            "Restrict LHS pattern of rule {} -> {} to break non-terminating cycle \
             (cycle length {})",
            from, to, cycle_len,
        );
        repairs.add(
            RepairSuggestion::new(
                RepairKind::FixTermination,
                restrict_desc,
                RepairAction::Description(format!(
                    "Make the LHS pattern {} more specific so it does not match \
                     terms that lead back into the cycle. Consider splitting into \
                     specialized variants or adding constructor constraints.",
                    from,
                )),
            )
            .with_confidence(0.5)
            .with_edit_cost(3)
            .with_alternatives(cycle_len as u64),
        );
    }

    repairs
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Convert pipeline syntax triples into rewrite rules for TRS analysis.
///
/// Each `(label, category, items)` triple becomes a `RewriteRule` where:
/// - The LHS is `App { symbol: label, args }` with one arg per item
/// - `SyntaxItemSpec::Terminal(t)` → `Term::constant(t)`
/// - `SyntaxItemSpec::NonTerminal { category, .. }` → `Term::var(category)`
/// - `SyntaxItemSpec::IdentCapture { param_name }` → `Term::var(param_name)`
/// - `SyntaxItemSpec::Binder { param_name, .. }` → `Term::var(param_name)`
/// - Other variants (Collection, Sep, Map, Zip, BinderCollection) → `Term::var(param_name_or_label)`
/// - The RHS is `Term::var(category)` (the result sort)
///
/// Rules with fewer than 2 items are excluded (no interesting overlaps).
pub fn syntax_to_rewrite_rules(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> Vec<RewriteRule> {
    let mut rules = Vec::with_capacity(all_syntax.len());

    for (label, category, items) in all_syntax {
        if items.len() < 2 {
            continue;
        }
        let args: Vec<Term> = items
            .iter()
            .enumerate()
            .map(|(idx, item)| match item {
                crate::SyntaxItemSpec::Terminal(t) => Term::constant(t.as_str()),
                crate::SyntaxItemSpec::NonTerminal { category: c, .. } => {
                    Term::var(format!("{}_{}", c, idx))
                }
                crate::SyntaxItemSpec::IdentCapture { param_name } => {
                    Term::var(format!("{}_{}", param_name, idx))
                }
                crate::SyntaxItemSpec::Binder { param_name, .. } => {
                    Term::var(format!("{}_{}", param_name, idx))
                }
                crate::SyntaxItemSpec::Collection { param_name, .. } => {
                    Term::var(format!("{}_{}", param_name, idx))
                }
                crate::SyntaxItemSpec::Sep { .. } => Term::var(format!("sep_{}", idx)),
                crate::SyntaxItemSpec::Map { .. } => Term::var(format!("map_{}", idx)),
                crate::SyntaxItemSpec::Zip { left_name, .. } => {
                    Term::var(format!("{}_{}", left_name, idx))
                }
                crate::SyntaxItemSpec::BinderCollection { param_name, .. } => {
                    Term::var(format!("{}_{}", param_name, idx))
                }
                crate::SyntaxItemSpec::Optional { .. } => Term::var(format!("opt_{}", idx)),
            })
            .collect();

        let lhs = Term::app(label.as_str(), args);
        let rhs = Term::var(category.as_str());
        rules.push(RewriteRule::labeled(label.as_str(), lhs, rhs));
    }

    rules
}

/// Pipeline bridge: run confluence analysis on grammar syntax.
///
/// Converts `all_syntax` into rewrite rules via [`syntax_to_rewrite_rules`],
/// then runs [`check_confluence`] with the given step limit.
///
/// Returns `None` if no rewrite rules are generated (trivially confluent).
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    max_steps: usize,
) -> Option<ConfluenceAnalysis> {
    let rules = syntax_to_rewrite_rules(all_syntax);
    if rules.is_empty() {
        return None;
    }
    Some(check_confluence(&rules, max_steps))
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_display() {
        let t = Term::app(
            "f",
            vec![Term::var("x"), Term::constant("a")],
        );
        assert_eq!(t.to_string(), "f(x, a)");
    }

    #[test]
    fn term_variables() {
        let t = Term::app(
            "g",
            vec![
                Term::var("x"),
                Term::app("h", vec![Term::var("y"), Term::var("x")]),
            ],
        );
        let vars = t.variables();
        assert_eq!(vars, vec!["x", "y", "x"]);
    }

    #[test]
    fn term_substitution() {
        let t = Term::app("f", vec![Term::var("x"), Term::var("y")]);
        let mut subst = HashMap::new();
        subst.insert("x".to_string(), Term::constant("a"));
        let result = t.apply_substitution(&subst);
        assert_eq!(result.to_string(), "f(a, y)");
    }

    #[test]
    fn rewrite_rule_display() {
        let rule = RewriteRule::labeled(
            "comm",
            Term::app("plus", vec![Term::var("x"), Term::var("y")]),
            Term::app("plus", vec![Term::var("y"), Term::var("x")]),
        );
        assert_eq!(rule.to_string(), "[comm] plus(x, y) → plus(y, x)");
    }

    #[test]
    fn confluence_analysis_display() {
        let analysis = ConfluenceAnalysis {
            is_confluent: true,
            critical_pairs: Vec::new(),
            joinability_results: Vec::new(),
            non_joinable_count: 0,
            unknown_count: 0,
        };
        assert!(analysis.to_string().contains("confluent: true"));
    }

    // ──────────────────────────────────────────────────────────────────────
    // Helper function tests
    // ──────────────────────────────────────────────────────────────────────

    #[test]
    fn unify_identical_constants() {
        let a = Term::constant("a");
        let sigma = unify(&a, &a).expect("identical constants should unify");
        assert!(sigma.is_empty());
    }

    #[test]
    fn unify_var_with_constant() {
        let x = Term::var("x");
        let a = Term::constant("a");
        let sigma = unify(&x, &a).expect("var should unify with constant");
        assert_eq!(sigma.get("x"), Some(&Term::constant("a")));
    }

    #[test]
    fn unify_clash() {
        let a = Term::constant("a");
        let b = Term::constant("b");
        assert!(unify(&a, &b).is_none(), "different constants must not unify");
    }

    #[test]
    fn unify_occurs_check() {
        // x should NOT unify with f(x) — infinite type.
        let x = Term::var("x");
        let fx = Term::app("f", vec![Term::var("x")]);
        assert!(unify(&x, &fx).is_none(), "occurs check must prevent cyclic unification");
    }

    #[test]
    fn unify_nested() {
        // f(x, b) ~ f(a, y) → {x↦a, y↦b}
        let s = Term::app("f", vec![Term::var("x"), Term::constant("b")]);
        let t = Term::app("f", vec![Term::constant("a"), Term::var("y")]);
        let sigma = unify(&s, &t).expect("should unify");
        assert_eq!(s.apply_substitution(&sigma), t.apply_substitution(&sigma));
    }

    // ──────────────────────────────────────────────────────────────────────
    // Critical pair and confluence tests
    // ──────────────────────────────────────────────────────────────────────

    /// A confluent TRS for group theory (subset):
    ///   R1: f(e, x) → x          (left identity)
    ///   R2: f(i(x), x) → e       (left inverse)
    ///   R3: f(f(x,y),z) → f(x,f(y,z))  (associativity)
    ///
    /// The overlap of R1 with R3 at position [0] produces:
    ///   l1 = f(e, x')  overlaps with subterm f(x,y) of l3 = f(f(x,y),z)
    ///   MGU: {x↦e, y↦x'}  (after renaming R1 vars with ')
    ///   term1 = x' (from r1·σ)
    ///   term2 = f(e, f(x', z)) (from r3·σ) which reduces to f(x', z) via R1
    ///
    /// This is not fully confluent without additional orientation rules, but
    /// it demonstrates critical pair detection.
    #[test]
    fn detect_critical_pairs_group_fragment() {
        let rules = vec![
            // R0: f(e, x) → x
            RewriteRule::new(
                Term::app("f", vec![Term::constant("e"), Term::var("x")]),
                Term::var("x"),
            ),
            // R1: f(i(x), x) → e
            RewriteRule::new(
                Term::app("f", vec![
                    Term::app("i", vec![Term::var("x")]),
                    Term::var("x"),
                ]),
                Term::constant("e"),
            ),
            // R2: f(f(x,y),z) → f(x,f(y,z))
            RewriteRule::new(
                Term::app("f", vec![
                    Term::app("f", vec![Term::var("x"), Term::var("y")]),
                    Term::var("z"),
                ]),
                Term::app("f", vec![
                    Term::var("x"),
                    Term::app("f", vec![Term::var("y"), Term::var("z")]),
                ]),
            ),
        ];

        let pairs = detect_critical_pairs(&rules);
        // There should be at least one critical pair (R0 vs R2, R1 vs R2, etc.)
        assert!(
            !pairs.is_empty(),
            "group fragment must have critical pairs from overlapping rules"
        );

        // Verify structural invariants on every critical pair.
        for cp in &pairs {
            assert!(cp.rule1_index < rules.len());
            assert!(cp.rule2_index < rules.len());
        }
    }

    /// A trivially confluent TRS (no overlaps):
    ///   R0: a → b
    ///   R1: c → d
    /// Since the LHS of each rule is a distinct constant, there are no
    /// non-trivial overlaps and hence no critical pairs.
    #[test]
    fn no_critical_pairs_for_disjoint_rules() {
        let rules = vec![
            RewriteRule::new(Term::constant("a"), Term::constant("b")),
            RewriteRule::new(Term::constant("c"), Term::constant("d")),
        ];
        let pairs = detect_critical_pairs(&rules);
        assert!(
            pairs.is_empty(),
            "disjoint constant rules should produce zero critical pairs"
        );
    }

    /// Confluent TRS: f(f(x)) → f(x).
    /// The self-overlap at position [0] gives critical pair ⟨f(x'), f(f(x'))⟩
    /// which join to f(x') after one step.
    #[test]
    fn confluent_idempotent_rule() {
        let rules = vec![
            RewriteRule::new(
                Term::app("f", vec![Term::app("f", vec![Term::var("x")])]),
                Term::app("f", vec![Term::var("x")]),
            ),
        ];
        let analysis = check_confluence(&rules, 100);
        assert!(
            analysis.is_confluent,
            "idempotent f(f(x)) → f(x) should be confluent, got: {:?}",
            analysis.joinability_results
        );
    }

    /// Non-confluent TRS:
    ///   R0: f(x) → a
    ///   R1: f(x) → b
    /// The overlap at root between R0 and R1 (different rules) produces
    /// ⟨a, b⟩ which are distinct normal forms — not joinable.
    #[test]
    fn non_confluent_ambiguous_rules() {
        let rules = vec![
            RewriteRule::new(
                Term::app("f", vec![Term::var("x")]),
                Term::constant("a"),
            ),
            RewriteRule::new(
                Term::app("f", vec![Term::var("x")]),
                Term::constant("b"),
            ),
        ];
        let analysis = check_confluence(&rules, 100);
        assert!(
            !analysis.is_confluent,
            "f(x)→a and f(x)→b should be non-confluent"
        );
        assert!(
            analysis.non_joinable_count > 0,
            "should have at least one non-joinable critical pair"
        );
    }

    /// Check joinability on a manually constructed critical pair.
    #[test]
    fn joinability_simple() {
        // Rules: g(a) → b, g(a) → c, b → d, c → d.
        // Critical pair ⟨b, c⟩ should join at d.
        let rules = vec![
            RewriteRule::new(
                Term::app("g", vec![Term::constant("a")]),
                Term::constant("b"),
            ),
            RewriteRule::new(
                Term::app("g", vec![Term::constant("a")]),
                Term::constant("c"),
            ),
            RewriteRule::new(Term::constant("b"), Term::constant("d")),
            RewriteRule::new(Term::constant("c"), Term::constant("d")),
        ];
        let cp = CriticalPair {
            term1: Term::constant("b"),
            term2: Term::constant("c"),
            rule1_index: 0,
            rule2_index: 1,
            overlap_position: vec![],
        };
        let result = check_joinability(&cp, &rules, 100);
        assert_eq!(
            result,
            JoinabilityResult::Joinable {
                common_reduct: Term::constant("d"),
            }
        );
    }

    // ──────────────────────────────────────────────────────────────────────
    // Repair suggestion tests
    // ──────────────────────────────────────────────────────────────────────

    /// Non-confluent TRS produces repair suggestions: both an equation and
    /// an oriented rewrite for each non-joinable critical pair.
    #[test]
    fn suggest_confluence_repairs_non_confluent() {
        // f(x) → a and f(x) → b  →  critical pair ⟨a, b⟩, not joinable.
        let rules = vec![
            RewriteRule::new(
                Term::app("f", vec![Term::var("x")]),
                Term::constant("a"),
            ),
            RewriteRule::new(
                Term::app("f", vec![Term::var("x")]),
                Term::constant("b"),
            ),
        ];
        let analysis = check_confluence(&rules, 100);
        assert!(!analysis.is_confluent);

        let repairs = suggest_confluence_repairs(&analysis);
        // Each non-joinable pair yields 2 suggestions (equation + rewrite).
        assert!(
            repairs.suggestions.len() >= 2,
            "expected at least 2 repair suggestions, got {}",
            repairs.suggestions.len(),
        );

        // Check that we get both an equation and a rewrite suggestion.
        let has_equation = repairs.suggestions.iter().any(|s| {
            matches!(s.action, RepairAction::AddEquation { .. })
        });
        let has_rewrite = repairs.suggestions.iter().any(|s| {
            matches!(s.action, RepairAction::AddRewrite { .. })
        });
        assert!(has_equation, "should have an AddEquation suggestion");
        assert!(has_rewrite, "should have an AddRewrite suggestion");

        // Equation should have edit_cost = 1, rewrite edit_cost = 2.
        for s in &repairs.suggestions {
            match &s.action {
                RepairAction::AddEquation { .. } => {
                    assert_eq!(s.edit_cost, 1);
                }
                RepairAction::AddRewrite { .. } => {
                    assert_eq!(s.edit_cost, 2);
                }
                _ => panic!("unexpected repair action: {:?}", s.action),
            }
            assert!(s.confidence > 0.0 && s.confidence <= 1.0);
            assert_eq!(s.kind, RepairKind::FixConfluence);
        }
    }

    /// A confluent TRS yields zero repair suggestions.
    #[test]
    fn suggest_confluence_repairs_confluent_yields_empty() {
        let rules = vec![
            RewriteRule::new(
                Term::app("f", vec![Term::app("f", vec![Term::var("x")])]),
                Term::app("f", vec![Term::var("x")]),
            ),
        ];
        let analysis = check_confluence(&rules, 100);
        assert!(analysis.is_confluent);

        let repairs = suggest_confluence_repairs(&analysis);
        assert!(
            repairs.suggestions.is_empty(),
            "confluent TRS should produce no repair suggestions"
        );
    }

    /// Structural similarity is used for confidence: terms sharing the same
    /// root symbol get higher confidence than terms with different roots.
    #[test]
    fn suggest_confluence_repairs_confidence_reflects_similarity() {
        // Build a non-confluent analysis manually with two different pairs:
        // Pair 1: f(a) vs f(b) — same root symbol "f", higher similarity.
        // Pair 2: a vs b       — different constants, lower similarity.
        let analysis = ConfluenceAnalysis {
            is_confluent: false,
            critical_pairs: vec![
                CriticalPair {
                    term1: Term::app("f", vec![Term::constant("a")]),
                    term2: Term::app("f", vec![Term::constant("b")]),
                    rule1_index: 0,
                    rule2_index: 1,
                    overlap_position: vec![],
                },
                CriticalPair {
                    term1: Term::constant("a"),
                    term2: Term::constant("b"),
                    rule1_index: 0,
                    rule2_index: 1,
                    overlap_position: vec![],
                },
            ],
            joinability_results: vec![
                JoinabilityResult::NotJoinable {
                    normal_form1: Term::app("f", vec![Term::constant("a")]),
                    normal_form2: Term::app("f", vec![Term::constant("b")]),
                },
                JoinabilityResult::NotJoinable {
                    normal_form1: Term::constant("a"),
                    normal_form2: Term::constant("b"),
                },
            ],
            non_joinable_count: 2,
            unknown_count: 0,
        };

        let repairs = suggest_confluence_repairs(&analysis);
        // 2 pairs × 2 suggestions each = 4 total.
        assert_eq!(repairs.suggestions.len(), 4);

        // Extract equation confidences (indices 0 and 2 are equations).
        let conf_similar = repairs.suggestions[0].confidence; // f(a) vs f(b)
        let conf_dissimilar = repairs.suggestions[2].confidence; // a vs b
        assert!(
            conf_similar > conf_dissimilar,
            "higher structural similarity should yield higher confidence: {} vs {}",
            conf_similar, conf_dissimilar,
        );
    }

    /// Termination repair suggestions for a cycle of 3 terms.
    #[test]
    fn suggest_termination_repair_cycle() {
        let cycle = vec![
            Term::app("f", vec![Term::constant("a")]),
            Term::app("f", vec![Term::constant("b")]),
            Term::app("f", vec![Term::constant("c")]),
        ];
        let repairs = suggest_termination_repair(&cycle);

        // 3 edges × 2 suggestions each = 6 total.
        assert_eq!(
            repairs.suggestions.len(),
            6,
            "expected 6 suggestions for a 3-term cycle, got {}",
            repairs.suggestions.len(),
        );

        for s in &repairs.suggestions {
            assert_eq!(s.kind, RepairKind::FixTermination);
            assert!(s.confidence > 0.0 && s.confidence <= 1.0);
            assert_eq!(s.alternative_count, 3);
        }

        // Guards have edit_cost = 2, restrictions have edit_cost = 3.
        let guard_count = repairs.suggestions.iter().filter(|s| s.edit_cost == 2).count();
        let restrict_count = repairs.suggestions.iter().filter(|s| s.edit_cost == 3).count();
        assert_eq!(guard_count, 3, "expected 3 guard suggestions");
        assert_eq!(restrict_count, 3, "expected 3 restriction suggestions");
    }

    /// Termination repair with fewer than 2 terms yields no suggestions.
    #[test]
    fn suggest_termination_repair_degenerate_cycle() {
        let empty = suggest_termination_repair(&[]);
        assert!(empty.suggestions.is_empty(), "empty cycle → no suggestions");

        let single = suggest_termination_repair(&[Term::constant("a")]);
        assert!(single.suggestions.is_empty(), "single-term cycle → no suggestions");
    }

    /// Orientation heuristic: the larger term becomes the LHS of the rewrite.
    #[test]
    fn suggest_confluence_repairs_orientation() {
        // Build a non-confluent analysis where one normal form is larger.
        let big_term = Term::app("f", vec![
            Term::app("g", vec![Term::constant("a"), Term::constant("b")]),
        ]);
        let small_term = Term::constant("c");

        let analysis = ConfluenceAnalysis {
            is_confluent: false,
            critical_pairs: vec![CriticalPair {
                term1: small_term.clone(),
                term2: big_term.clone(),
                rule1_index: 0,
                rule2_index: 1,
                overlap_position: vec![],
            }],
            joinability_results: vec![JoinabilityResult::NotJoinable {
                normal_form1: small_term.clone(),
                normal_form2: big_term.clone(),
            }],
            non_joinable_count: 1,
            unknown_count: 0,
        };

        let repairs = suggest_confluence_repairs(&analysis);
        let rewrite_suggestion = repairs
            .suggestions
            .iter()
            .find(|s| matches!(s.action, RepairAction::AddRewrite { .. }))
            .expect("should have a rewrite suggestion");

        match &rewrite_suggestion.action {
            RepairAction::AddRewrite { lhs, rhs, .. } => {
                // The bigger term (f(g(a, b))) should be the LHS.
                assert_eq!(lhs, &big_term.to_string());
                assert_eq!(rhs, &small_term.to_string());
            }
            _ => unreachable!(),
        }
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
            (
                "Mul".to_string(),
                "Expr".to_string(),
                vec![
                    crate::SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "a".to_string(),
                    },
                    crate::SyntaxItemSpec::Terminal("*".to_string()),
                    crate::SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "b".to_string(),
                    },
                ],
            ),
        ];
        let result = analyze_from_bundle(&syntax, 100);
        assert!(result.is_some(), "should produce analysis for non-empty syntax");
    }

    #[test]
    fn test_analyze_from_bundle_empty() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![];
        let result = analyze_from_bundle(&syntax, 100);
        assert!(result.is_none(), "should return None for empty syntax");
    }

    #[test]
    fn test_syntax_to_rewrite_rules() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "Add".to_string(),
            "Expr".to_string(),
            vec![
                crate::SyntaxItemSpec::Terminal("+".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "a".to_string(),
                },
            ],
        )];
        let rules = syntax_to_rewrite_rules(&syntax);
        assert!(!rules.is_empty(), "should produce rewrite rules from syntax");
    }
}
