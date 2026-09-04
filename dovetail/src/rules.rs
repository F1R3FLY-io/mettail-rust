//! Rules-as-data: rewrite rules over the e-graph + an equality-saturation driver.
//!
//! Rules are DATA (`RewriteRule<L>`), not macro-generated code — a language's
//! reduction rules are loaded and run, not compiled in. Saturation grows the
//! e-graph of equalities (every rewrite adds an equality, never replacing a
//! term); the weighted [`crate::extract`] extractor then enumerates normal forms
//! best-first. **Nothing is pruned during saturation**; node and iteration
//! limits are explicit [`SaturationOutcome`] values, never silent.

use crate::hash::{HashMap, HashSet};
use std::rc::Rc;

use crate::egraph::{EClassId, EGraph, ENode};
use crate::key::SemanticHash;
use crate::set_automaton::{
    PatternId, SetAutomaton, SetAutomatonError, SetAutomatonRun, SetAutomatonStats,
};

/// A pattern over operator labels `L` with named pattern variables.
pub enum Pattern<L> {
    /// A pattern variable, binding to an e-class.
    Var(String),
    /// An operator applied to argument patterns (POSITIONAL).
    App { op: L, args: Vec<Pattern<L>> },
    /// An associative-commutative (AC) operator applied to a multiset of
    /// children: the `fixed` patterns match a SUB-MULTISET of an `op`-bag node's
    /// children (in any pairing), and `rest`, if present, binds to the multiset
    /// COMPLEMENT (a fresh canonical n-ary `op` node).
    ///
    /// On the LHS this matches every distinct sub-multiset selection + pairing as
    /// a DISTINCT alternative; the non-linear `Var` re-bind check prunes pairings
    /// whose shared variables disagree (by evidence). On the RHS it builds the
    /// result bag: each `fixed` pattern instantiated, unioned with the bound
    /// `rest` complement.
    AcApp {
        op: L,
        fixed: Vec<Pattern<L>>,
        rest: Option<String>,
    },
}

impl<L: Clone> Clone for Pattern<L> {
    fn clone(&self) -> Self {
        enum Task<'a, L> {
            Visit(&'a Pattern<L>),
            AssembleApp {
                op: L,
                child_count: usize,
            },
            AssembleAc {
                op: L,
                child_count: usize,
                rest: Option<String>,
            },
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Pattern::Var(name)) => values.push(Pattern::Var(name.clone())),
                Task::Visit(Pattern::App { op, args }) => {
                    tasks.push(Task::AssembleApp { op: op.clone(), child_count: args.len() });
                    tasks.extend(args.iter().rev().map(Task::Visit));
                },
                Task::Visit(Pattern::AcApp { op, fixed, rest }) => {
                    tasks.push(Task::AssembleAc {
                        op: op.clone(),
                        child_count: fixed.len(),
                        rest: rest.clone(),
                    });
                    tasks.extend(fixed.iter().rev().map(Task::Visit));
                },
                Task::AssembleApp { op, child_count } => {
                    let first_child = values
                        .len()
                        .checked_sub(child_count)
                        .expect("Pattern clone PDA lost an application child");
                    let args = values.split_off(first_child);
                    values.push(Pattern::App { op, args });
                },
                Task::AssembleAc { op, child_count, rest } => {
                    let first_child = values
                        .len()
                        .checked_sub(child_count)
                        .expect("Pattern clone PDA lost an AC child");
                    let fixed = values.split_off(first_child);
                    values.push(Pattern::AcApp { op, fixed, rest });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("Pattern clone PDA produced no result")
    }
}

impl<L: PartialEq> PartialEq for Pattern<L> {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            match (left, right) {
                (Pattern::Var(left), Pattern::Var(right)) if left == right => {},
                (
                    Pattern::App { op: left_op, args: left_args },
                    Pattern::App { op: right_op, args: right_args },
                ) if left_op == right_op && left_args.len() == right_args.len() => {
                    pending.extend(left_args.iter().zip(right_args).rev());
                },
                (
                    Pattern::AcApp {
                        op: left_op,
                        fixed: left_fixed,
                        rest: left_rest,
                    },
                    Pattern::AcApp {
                        op: right_op,
                        fixed: right_fixed,
                        rest: right_rest,
                    },
                ) if left_op == right_op
                    && left_rest == right_rest
                    && left_fixed.len() == right_fixed.len() =>
                {
                    pending.extend(left_fixed.iter().zip(right_fixed).rev());
                },
                _ => return false,
            }
        }
        true
    }
}

impl<L: Eq> Eq for Pattern<L> {}

impl<L: std::fmt::Debug> std::fmt::Debug for Pattern<L> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Task<'a, L> {
            Visit(&'a Pattern<L>),
            Text(&'static str),
            DebugLabel(&'a L),
            DebugString(&'a Option<String>),
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Pattern::Var(name)) => write!(formatter, "Var({name:?})")?,
                Task::Visit(Pattern::App { op, args }) => {
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Text("]"));
                    for (index, arg) in args.iter().enumerate().rev() {
                        tasks.push(Task::Visit(arg));
                        if index > 0 {
                            tasks.push(Task::Text(", "));
                        }
                    }
                    tasks.push(Task::Text("args: ["));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::DebugLabel(op));
                    tasks.push(Task::Text("App { op: "));
                },
                Task::Visit(Pattern::AcApp { op, fixed, rest }) => {
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::DebugString(rest));
                    tasks.push(Task::Text("rest: "));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Text("]"));
                    for (index, pattern) in fixed.iter().enumerate().rev() {
                        tasks.push(Task::Visit(pattern));
                        if index > 0 {
                            tasks.push(Task::Text(", "));
                        }
                    }
                    tasks.push(Task::Text("fixed: ["));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::DebugLabel(op));
                    tasks.push(Task::Text("AcApp { op: "));
                },
                Task::Text(text) => formatter.write_str(text)?,
                Task::DebugLabel(label) => write!(formatter, "{label:?}")?,
                Task::DebugString(value) => write!(formatter, "{value:?}")?,
            }
        }
        Ok(())
    }
}

impl<L> Drop for Pattern<L> {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        match self {
            Pattern::Var(_) => {},
            Pattern::App { args, .. } => pending.append(args),
            Pattern::AcApp { fixed, .. } => pending.append(fixed),
        }
        while let Some(mut pattern) = pending.pop() {
            match &mut pattern {
                Pattern::Var(_) => {},
                Pattern::App { args, .. } => pending.append(args),
                Pattern::AcApp { fixed, .. } => pending.append(fixed),
            }
        }
    }
}

impl<L> Pattern<L> {
    pub fn var(name: impl Into<String>) -> Self {
        Pattern::Var(name.into())
    }
    pub fn leaf(op: L) -> Self {
        Pattern::App { op, args: Vec::new() }
    }
    pub fn app(op: L, args: Vec<Pattern<L>>) -> Self {
        Pattern::App { op, args }
    }
    /// An AC (associative-commutative) bag pattern: `fixed` patterns match a
    /// sub-multiset of an `op`-bag; `rest` (if any) binds the complement.
    pub fn ac(op: L, fixed: Vec<Pattern<L>>, rest: Option<String>) -> Self {
        Pattern::AcApp { op, fixed, rest }
    }
}

/// A substitution from pattern-variable name to e-class.
pub type Subst = HashMap<String, EClassId>;

/// A LAZY iterator over size-`k` sub-multiset selections (by position) of a bag
/// of e-class children, paired with the multiset COMPLEMENT.
///
/// AC selection is exponential, so selections are materialized ON DEMAND (mandate
/// 2 — laziness): the iterator holds only the current `k`-combination of indices
/// and advances ONE index at a time (lexicographic next-combination, mirroring
/// `enum_vectors`'s single-coordinate advance in
/// `EnumerationCompleteness.v`/`CollectionAcLowering.v`). It never builds a `Vec`
/// of all selections.
///
/// Each `next()` yields `(selection, complement)`: `selection` is the chosen
/// positions' classes (in position order), `complement` the unchosen positions'
/// classes. Together they partition the bag (no element lost or duplicated) — the
/// `is_split` / `ac_select` contract proven in `CollectionAcLowering.v`.
pub struct LazyAcSelect {
    bag: Vec<EClassId>,
    k: usize,
    /// The current `k`-combination of indices into `bag` (strictly increasing),
    /// or `None` once exhausted.
    combo: Option<Vec<usize>>,
}

/// Allocation failure while constructing or advancing a lazy AC selector.
/// Runtime-defined theories use the fallible interface so an untrusted width
/// cannot turn process allocation failure into a partial semantic result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LazyAcSelectAllocationError;

/// One exact positional selection and its disjoint positional complement.
pub type LazyAcSelection = (Vec<EClassId>, Vec<EClassId>);

impl LazyAcSelect {
    fn new(bag: &[EClassId], k: usize) -> Self {
        Self::try_new(bag, k).expect("legacy AC selector allocation failed")
    }

    /// Construct a lazy selector with every backing allocation checked before
    /// publication.
    pub fn try_new(bag: &[EClassId], k: usize) -> Result<Self, LazyAcSelectAllocationError> {
        let n = bag.len();
        let combo = if k <= n {
            // The first combination is [0, 1, ..., k-1].
            let mut combo = Vec::new();
            combo
                .try_reserve_exact(k)
                .map_err(|_| LazyAcSelectAllocationError)?;
            combo.extend(0..k);
            Some(combo)
        } else {
            None // k > n: no size-k selection exists.
        };
        let mut owned_bag = Vec::new();
        owned_bag
            .try_reserve_exact(bag.len())
            .map_err(|_| LazyAcSelectAllocationError)?;
        owned_bag.extend_from_slice(bag);
        Ok(LazyAcSelect { bag: owned_bag, k, combo })
    }

    /// Advance `self.combo` to the lexicographically-next strictly-increasing
    /// `k`-combination of `[0, n)`, or set it to `None` when exhausted. O(k).
    fn advance(&mut self) {
        let n = self.bag.len();
        let Some(combo) = self.combo.as_mut() else {
            return;
        };
        if self.k == 0 {
            // The single empty selection has no successor.
            self.combo = None;
            return;
        }
        // Find the rightmost index that can be incremented: position `i` whose
        // value is below its ceiling `n - k + i`.
        let mut i = self.k;
        loop {
            if i == 0 {
                self.combo = None;
                return;
            }
            i -= 1;
            if combo[i] < n - self.k + i {
                combo[i] += 1;
                // Reset every position to the right to be contiguous.
                for j in (i + 1)..self.k {
                    combo[j] = combo[j - 1] + 1;
                }
                return;
            }
        }
    }

    /// Produce one exact selection/complement pair with checked allocations.
    pub fn try_next(&mut self) -> Result<Option<LazyAcSelection>, LazyAcSelectAllocationError> {
        let Some(current) = self.combo.as_ref() else {
            return Ok(None);
        };
        let mut combo = Vec::new();
        combo
            .try_reserve_exact(current.len())
            .map_err(|_| LazyAcSelectAllocationError)?;
        combo.extend_from_slice(current);

        let mut selection = Vec::new();
        selection
            .try_reserve_exact(self.k)
            .map_err(|_| LazyAcSelectAllocationError)?;
        let mut complement = Vec::new();
        complement
            .try_reserve_exact(self.bag.len() - self.k)
            .map_err(|_| LazyAcSelectAllocationError)?;
        let mut ci = 0usize;
        for (idx, &child) in self.bag.iter().enumerate() {
            if ci < combo.len() && combo[ci] == idx {
                selection.push(child);
                ci += 1;
            } else {
                complement.push(child);
            }
        }
        self.advance();
        Ok(Some((selection, complement)))
    }
}

impl Iterator for LazyAcSelect {
    type Item = (Vec<EClassId>, Vec<EClassId>);

    fn next(&mut self) -> Option<Self::Item> {
        self.try_next()
            .expect("legacy AC selector allocation failed")
    }
}

/// Construct the lazy size-`k` sub-multiset selection iterator over `bag`. See
/// [`LazyAcSelect`].
pub fn lazy_ac_select(bag: &[EClassId], k: usize) -> LazyAcSelect {
    LazyAcSelect::new(bag, k)
}

/// A rewrite rule `lhs -> rhs` (rules ARE data). RHS variables must be a subset
/// of LHS variables (every RHS var is bound by the match).
#[derive(Clone, Debug)]
pub struct RewriteRule<L> {
    pub lhs: Pattern<L>,
    pub rhs: Pattern<L>,
    pub label: Option<String>,
}

/// An opaque, serializable identifier naming a native-computed rewrite's
/// transition. The Dovetail engine is language-agnostic, so the actual
/// computation lives in a generated dispatcher (one per language); a
/// [`NativeRule`] carries only the redex pattern and this tag, keeping the
/// "rules are DATA" doctrine (see the module docs) intact — no compiled-in
/// closures live in the rule data itself.
pub type NativeOpId = u32;

/// The one compiled-in escape hatch a [`NativeRule`] fires through: given the
/// rule's [`NativeOpId`], the e-graph, and the match substitution `σ`, compute
/// the result e-class — or `None` when the redex does not reduce here (a
/// variable or otherwise-stuck child, or a failed funded admission).
///
/// This is the *language-specific* half of the "rules are DATA" split: the
/// engine holds only the [`NativeOpId`] tag, and one generated dispatcher per
/// language interprets it. It is named rather than spelled out at each of the
/// three use sites so the signature has a single definition to change, and so
/// `clippy::type_complexity` has a factored type to point at.
///
/// Written unsized (`dyn`), so callers pass it as `&NativeDispatch<'_, L>`. The
/// lifetime parameter is NOT decoration: a `dyn` type alias fixes its object
/// lifetime bound where the ALIAS is written, and the default there is
/// `'static` — not the borrow's lifetime, as it would be in the `&dyn Fn(…)`
/// these sites spelled before. Omitting `'a` therefore silently demands
/// `'static` dispatchers and rejects the borrowing closures the fold tests and
/// the generated `dovetail_report_for` build (`E0373`: "closure may outlive the
/// current function"). Naming it restores the original, strictly-more-general
/// contract.
pub type NativeDispatch<'a, L> =
    dyn Fn(NativeOpId, &mut EGraph<L>, &Subst) -> Option<EClassId> + 'a;

/// A native-computed rewrite rule `lhs ~> ⟨native op⟩`.
///
/// Where a [`RewriteRule`] rewrites `lhs` to a *structural* [`Pattern`] RHS, a
/// `NativeRule` rewrites `lhs` to a result e-class **computed** by the
/// OSLF-funded dispatcher from the matched substitution — the children extracted
/// to their current funded-best form. This is how the *fold* fragment of a GSLT
/// operational semantics (a deterministic native computation such as a numeric
/// cast `int(a, w)`) reduces *inside* equality saturation, funded like every
/// other rewrite. A native rule still only ADDS the equality `redex == result`:
/// nothing is pruned (the substructural no-contraction law), and the node budget
/// `Σ` bounds it.
#[derive(Clone, Debug)]
pub struct NativeRule<L> {
    /// The redex pattern to match (e.g. `int(?a, ?w)`).
    pub lhs: Pattern<L>,
    /// The dispatcher tag naming the native transition (the fold body).
    pub op: NativeOpId,
    /// Human-readable label for diagnostics / report provenance.
    pub label: Option<String>,
}

/// Terminal outcome of equality saturation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SaturationOutcome {
    /// A fixpoint was reached (an iteration produced no new merges).
    Converged,
    /// The node budget was hit and saturation stopped early.
    NodeLimit,
    /// `max_iters` was exhausted before a fixpoint was observed.
    IterationLimit,
}

/// Saturation counters shared by every outcome.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SatStats {
    /// Iterations performed.
    pub iterations: usize,
    /// Total merges applied.
    pub total_merges: usize,
    /// Total set-automaton scans performed by saturation.
    pub set_automaton_scans: usize,
    /// Set-automaton scans performed for compiled contiguous rule batches.
    pub set_automaton_batches: usize,
    /// Canonical e-classes considered by all saturation set-automaton scans.
    pub set_automaton_root_classes: usize,
    /// E-nodes inspected by all saturation set-automaton scans.
    pub set_automaton_root_nodes: usize,
    /// Candidate root-pattern checks after symbol/arity dispatch.
    pub set_automaton_candidate_evaluations: usize,
    /// Cache misses for compiled pattern states at canonical e-classes.
    pub set_automaton_state_evaluations: usize,
    /// Cache hits for compiled pattern states at canonical e-classes.
    pub set_automaton_state_cache_hits: usize,
    /// Per-rule searches performed outside a still-valid compiled batch.
    pub rule_searches: usize,
    /// Per-rule searches that had to use the recursive AC-capable matcher.
    pub ac_fallback_searches: usize,
    /// Compiled batch result sets invalidated by graph growth or merges.
    pub set_automaton_batch_invalidations: usize,
}

impl SatStats {
    fn record_set_automaton_scan(&mut self, stats: SetAutomatonStats) {
        self.set_automaton_scans += 1;
        self.set_automaton_root_classes += stats.root_classes;
        self.set_automaton_root_nodes += stats.root_nodes;
        self.set_automaton_candidate_evaluations += stats.candidate_evaluations;
        self.set_automaton_state_evaluations += stats.state_evaluations;
        self.set_automaton_state_cache_hits += stats.state_cache_hits;
    }

    fn record_set_automaton_batch(&mut self, stats: SetAutomatonStats) {
        self.set_automaton_batches += 1;
        self.record_set_automaton_scan(stats);
    }

    fn record_rule_search(&mut self, search: &ObservedSearch) {
        self.rule_searches += 1;
        if let Some(stats) = search.set_automaton_stats {
            self.record_set_automaton_scan(stats);
        }
        if search.used_ac_fallback {
            self.ac_fallback_searches += 1;
        }
    }
}

/// Aggregated evidence that a labeled rewrite rule produced at least one
/// e-class merge during saturation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleFiring {
    /// Human-readable rule label. `None` preserves anonymous rule identity
    /// without fabricating a name at the Dovetail layer.
    pub label: Option<String>,
    /// Number of distinct e-class merges caused by this rule.
    pub count: usize,
}

/// Per-firing σ justification: the labeled rewrite rule that fired, the redex
/// root e-class it rewrote, and the substitution σ (pattern-variable → matched
/// e-class) under which it fired.
///
/// Where [`RuleFiring`] AGGREGATES a rule's firings to a merge count, this
/// preserves each INDIVIDUAL firing's σ so a downstream runtime bridge can
/// resolve the matched sub-terms (e.g. reflect them to a Rho value). This is
/// captured additively during saturation; the [`RuleFiring`] count aggregation
/// is unchanged. σ carries e-class ids only; resolving each to its funded-best
/// sub-term is the report layer's job (see
/// `crate::report::resolve_rewrite_justifications`), where the e-graph is live.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RewriteJustification {
    /// Human-readable rule label. `None` preserves anonymous rule identity.
    pub rule_label: Option<String>,
    /// The redex root e-class that was rewritten (canonical after the merge).
    pub root: EClassId,
    /// The substitution σ that fired the rule: pattern-variable → matched e-class.
    pub subst: Subst,
}

/// Outcome of equality saturation.
#[must_use = "saturation can stop from node or iteration limits; inspect `outcome` before extracting as if complete"]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SatReport {
    pub outcome: SaturationOutcome,
    pub stats: SatStats,
    pub rule_firings: Vec<RuleFiring>,
    /// Per-firing σ justifications (rule label + redex root + substitution),
    /// captured additively alongside [`rule_firings`](Self::rule_firings). Empty
    /// unless a rewrite fired; the `rule_firings` count aggregation is unchanged.
    /// One entry per merge-causing match, in firing order.
    pub rewrite_justifications: Vec<RewriteJustification>,
}

impl SatReport {
    fn new(
        outcome: SaturationOutcome,
        stats: SatStats,
        rule_firings: Vec<RuleFiring>,
        rewrite_justifications: Vec<RewriteJustification>,
    ) -> Self {
        SatReport {
            outcome,
            stats,
            rule_firings,
            rewrite_justifications,
        }
    }
}

fn record_rule_firing(rule_firings: &mut Vec<RuleFiring>, label: &Option<String>, count: usize) {
    if count == 0 {
        return;
    }
    if let Some(existing) = rule_firings
        .iter_mut()
        .find(|entry| entry.label.as_ref() == label.as_ref())
    {
        existing.count += count;
    } else {
        rule_firings.push(RuleFiring { label: label.clone(), count });
    }
}

#[derive(Clone, Debug)]
struct PositionalRuleSegment<L> {
    start: usize,
    end: usize,
    automaton: SetAutomaton<L>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct BatchedSegmentMatches {
    grouped: Vec<Vec<(EClassId, Subst)>>,
    stats: SetAutomatonStats,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ObservedSearch {
    matches: Vec<(EClassId, Subst)>,
    set_automaton_stats: Option<SetAutomatonStats>,
    used_ac_fallback: bool,
    budget_hit: bool,
}

/// Owned, reusable Dovetail saturation program.
///
/// `CompiledRuleSet` keeps rewrite rules as data while hoisting the positional
/// set-automaton compilation out of the saturation loop boundary. Callers that
/// evaluate the same generated language rules against many input e-graphs can
/// build one value and reuse it; the legacy slice-based saturation APIs remain
/// compatibility wrappers around this type.
#[derive(Clone, Debug)]
pub struct CompiledRuleSet<L> {
    rewrite_rules: Vec<RewriteRule<L>>,
    native_rules: Vec<NativeRule<L>>,
    structural_segments: Vec<PositionalRuleSegment<L>>,
    native_segments: Vec<PositionalRuleSegment<L>>,
}

impl<L: Clone + Eq + std::hash::Hash> CompiledRuleSet<L> {
    /// Compile structural and native rules into a reusable saturation program.
    pub fn new(rewrite_rules: Vec<RewriteRule<L>>, native_rules: Vec<NativeRule<L>>) -> Self {
        let structural_segments = compile_positional_segments(&rewrite_rules, |rule| &rule.lhs);
        let native_segments = compile_positional_segments(&native_rules, |rule| &rule.lhs);
        Self {
            rewrite_rules,
            native_rules,
            structural_segments,
            native_segments,
        }
    }

    /// Compile a structural-only rule set.
    pub fn from_rewrites(rewrite_rules: Vec<RewriteRule<L>>) -> Self {
        Self::new(rewrite_rules, Vec::new())
    }

    /// Structural rewrite rules in their original order.
    pub fn rewrite_rules(&self) -> &[RewriteRule<L>] {
        &self.rewrite_rules
    }

    /// Native-computed rules in their original order.
    pub fn native_rules(&self) -> &[NativeRule<L>] {
        &self.native_rules
    }

    /// Number of contiguous positional structural rule batches.
    pub fn structural_segment_count(&self) -> usize {
        self.structural_segments.len()
    }

    /// Number of contiguous positional native rule batches.
    pub fn native_segment_count(&self) -> usize {
        self.native_segments.len()
    }
}

fn pattern_contains_ac<L>(pattern: &Pattern<L>) -> bool {
    let mut pending = vec![pattern];
    while let Some(pattern) = pending.pop() {
        match pattern {
            Pattern::Var(_) => {},
            Pattern::App { args, .. } => pending.extend(args.iter().rev()),
            Pattern::AcApp { .. } => return true,
        }
    }
    false
}

fn compile_positional_segments<T, L>(
    items: &[T],
    lhs: impl Fn(&T) -> &Pattern<L>,
) -> Vec<PositionalRuleSegment<L>>
where
    L: Clone + Eq + std::hash::Hash,
{
    let mut segments = Vec::new();
    let mut index = 0usize;
    while index < items.len() {
        if pattern_contains_ac(lhs(&items[index])) {
            index += 1;
            continue;
        }

        let start = index;
        index += 1;
        while index < items.len() && !pattern_contains_ac(lhs(&items[index])) {
            index += 1;
        }
        let end = index;

        let patterns =
            (start..end).map(|rule_idx| (PatternId(rule_idx), lhs(&items[rule_idx]).clone()));
        if let Ok(automaton) = SetAutomaton::compile_structural(patterns) {
            segments.push(PositionalRuleSegment { start, end, automaton });
        }
    }
    segments
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct RuleApplication {
    merges: usize,
    budget_hit: bool,
    graph_changed: bool,
}

impl<L: Clone + Eq + std::hash::Hash + SemanticHash> EGraph<L> {
    /// All `(root e-class, substitution)` matches of `pattern` across the graph.
    ///
    /// Takes `&mut self` because AC (`AcApp`) matching materializes a fresh
    /// canonical n-ary `op` node for each `rest` complement — an honest,
    /// budget-gated e-graph growth (the only mutation; positional matching adds
    /// nothing). Pulling AC selections is on-demand and lazy ([`lazy_ac_select`]).
    pub fn search(&mut self, pattern: &Pattern<L>) -> Vec<(EClassId, Subst)> {
        self.search_observed(pattern).matches
    }

    fn search_observed(&mut self, pattern: &Pattern<L>) -> ObservedSearch {
        if let Ok(automaton) = SetAutomaton::compile_structural([(PatternId(0), pattern.clone())]) {
            let run = automaton.search_egraph(self);
            return ObservedSearch {
                set_automaton_stats: Some(run.stats),
                matches: run
                    .into_matches()
                    .into_iter()
                    .map(|m| (m.root, m.subst))
                    .collect(),
                used_ac_fallback: false,
                budget_hit: false,
            };
        }

        let budget_was_hit = self.node_limit_reached();
        let mut out = Vec::new();
        let classes: Vec<EClassId> = self.classes().collect();
        for q in classes {
            self.collect_matches(pattern, q, &Subst::default(), &mut out);
        }
        ObservedSearch {
            matches: out,
            set_automaton_stats: None,
            used_ac_fallback: pattern_contains_ac(pattern),
            budget_hit: !budget_was_hit && self.node_limit_reached(),
        }
    }

    /// Match many positional patterns with one set-automaton scan.
    ///
    /// This is the shared Dovetail/RhoNet matching boundary for the linear
    /// fragment: callers compile a whole rule family once, inspect each
    /// candidate redex root once, and receive pattern-tagged substitutions.
    /// AC patterns intentionally reject here so callers keep using the lazy,
    /// budget-aware AC path that can materialize `rest` complements.
    pub fn search_many_structural<I>(
        &self,
        patterns: I,
    ) -> Result<SetAutomatonRun, SetAutomatonError>
    where
        I: IntoIterator<Item = (PatternId, Pattern<L>)>,
    {
        Ok(SetAutomaton::compile_structural(patterns)?.search_egraph(self))
    }

    fn collect_matches(
        &mut self,
        pattern: &Pattern<L>,
        class: EClassId,
        subst: &Subst,
        out: &mut Vec<(EClassId, Subst)>,
    ) {
        enum Goal<'a, L> {
            Match {
                pattern: &'a Pattern<L>,
                class: EClassId,
            },
            ContinuePair {
                op: &'a L,
                fixed: &'a [Pattern<L>],
                rest: Option<&'a str>,
                selection: Rc<[EClassId]>,
                complement: Rc<[EClassId]>,
                used: Vec<bool>,
                depth: usize,
            },
        }

        impl<L> Clone for Goal<'_, L> {
            fn clone(&self) -> Self {
                match self {
                    Goal::Match { pattern, class } => Goal::Match { pattern, class: *class },
                    Goal::ContinuePair {
                        op,
                        fixed,
                        rest,
                        selection,
                        complement,
                        used,
                        depth,
                    } => Goal::ContinuePair {
                        op,
                        fixed,
                        rest: *rest,
                        selection: selection.clone(),
                        complement: complement.clone(),
                        used: used.clone(),
                        depth: *depth,
                    },
                }
            }
        }

        enum Work<'a, L> {
            Run {
                goals: Vec<Goal<'a, L>>,
                subst: Subst,
            },
            Bags {
                op: &'a L,
                fixed: &'a [Pattern<L>],
                rest: Option<&'a str>,
                bags: std::vec::IntoIter<Vec<EClassId>>,
                goals: Vec<Goal<'a, L>>,
                subst: Subst,
            },
            Selections {
                op: &'a L,
                fixed: &'a [Pattern<L>],
                rest: Option<&'a str>,
                selections: LazyAcSelect,
                goals: Vec<Goal<'a, L>>,
                subst: Subst,
            },
            PairChoices {
                op: &'a L,
                fixed: &'a [Pattern<L>],
                rest: Option<&'a str>,
                selection: Rc<[EClassId]>,
                complement: Rc<[EClassId]>,
                used: Vec<bool>,
                depth: usize,
                next_index: usize,
                goals: Vec<Goal<'a, L>>,
                subst: Subst,
            },
        }

        let output_root = self.find(class);
        let mut work = vec![Work::Run {
            goals: vec![Goal::Match { pattern, class: output_root }],
            subst: subst.clone(),
        }];

        while let Some(task) = work.pop() {
            match task {
                Work::Run { mut goals, mut subst } => {
                    let Some(goal) = goals.pop() else {
                        out.push((output_root, subst));
                        continue;
                    };
                    match goal {
                        Goal::Match { pattern, class } => {
                            let class = self.find(class);
                            match pattern {
                                Pattern::Var(name) => match subst.get(name) {
                                    Some(&existing) if self.find(existing) == class => {
                                        work.push(Work::Run { goals, subst });
                                    },
                                    Some(_) => {},
                                    None => {
                                        subst.insert(name.clone(), class);
                                        work.push(Work::Run { goals, subst });
                                    },
                                },
                                Pattern::App { op, args } => {
                                    let candidates: Vec<Vec<EClassId>> = self
                                        .nodes(class)
                                        .iter()
                                        .filter(|node| {
                                            node.op == *op && node.children.len() == args.len()
                                        })
                                        .map(|node| node.children.clone())
                                        .collect();
                                    let mut original_goals = Some(goals);
                                    let mut original_subst = Some(subst);
                                    for (candidate_index, children) in
                                        candidates.into_iter().enumerate().rev()
                                    {
                                        let mut branch_goals = if candidate_index == 0 {
                                            original_goals
                                                .take()
                                                .expect("first candidate owns the goal stack")
                                        } else {
                                            original_goals
                                                .as_ref()
                                                .expect("later candidates clone the goal stack")
                                                .clone()
                                        };
                                        for (pattern, class) in args.iter().zip(children).rev() {
                                            branch_goals.push(Goal::Match { pattern, class });
                                        }
                                        let branch_subst = if candidate_index == 0 {
                                            original_subst
                                                .take()
                                                .expect("first candidate owns the substitution")
                                        } else {
                                            original_subst
                                                .as_ref()
                                                .expect("later candidates clone the substitution")
                                                .clone()
                                        };
                                        work.push(Work::Run {
                                            goals: branch_goals,
                                            subst: branch_subst,
                                        });
                                    }
                                },
                                Pattern::AcApp { op, fixed, rest } => {
                                    let bags: Vec<Vec<EClassId>> = self
                                        .nodes(class)
                                        .iter()
                                        .filter(|node| {
                                            node.op == *op && node.children.len() >= fixed.len()
                                        })
                                        .map(|node| {
                                            node.children
                                                .iter()
                                                .map(|&child| self.find(child))
                                                .collect()
                                        })
                                        .collect();
                                    work.push(Work::Bags {
                                        op,
                                        fixed,
                                        rest: rest.as_deref(),
                                        bags: bags.into_iter(),
                                        goals,
                                        subst,
                                    });
                                },
                            }
                        },
                        Goal::ContinuePair {
                            op,
                            fixed,
                            rest,
                            selection,
                            complement,
                            used,
                            depth,
                        } => {
                            if depth == fixed.len() {
                                if let Some(name) = rest {
                                    let Some(id) = self.add_canonical_bag(op.clone(), &complement)
                                    else {
                                        continue;
                                    };
                                    subst.insert(name.to_string(), id);
                                }
                                work.push(Work::Run { goals, subst });
                            } else {
                                work.push(Work::PairChoices {
                                    op,
                                    fixed,
                                    rest,
                                    selection,
                                    complement,
                                    used,
                                    depth,
                                    next_index: 0,
                                    goals,
                                    subst,
                                });
                            }
                        },
                    }
                },
                Work::Bags { op, fixed, rest, mut bags, goals, subst } => {
                    if let Some(bag) = bags.next() {
                        work.push(Work::Bags {
                            op,
                            fixed,
                            rest,
                            bags,
                            goals: goals.clone(),
                            subst: subst.clone(),
                        });
                        work.push(Work::Selections {
                            op,
                            fixed,
                            rest,
                            selections: lazy_ac_select(&bag, fixed.len()),
                            goals,
                            subst,
                        });
                    }
                },
                Work::Selections {
                    op,
                    fixed,
                    rest,
                    mut selections,
                    goals,
                    subst,
                } => {
                    if let Some((selection, complement)) = selections.next() {
                        work.push(Work::Selections {
                            op,
                            fixed,
                            rest,
                            selections,
                            goals: goals.clone(),
                            subst: subst.clone(),
                        });
                        let mut branch_goals = goals;
                        branch_goals.push(Goal::ContinuePair {
                            op,
                            fixed,
                            rest,
                            used: vec![false; selection.len()],
                            selection: Rc::from(selection.into_boxed_slice()),
                            complement: Rc::from(complement.into_boxed_slice()),
                            depth: 0,
                        });
                        work.push(Work::Run { goals: branch_goals, subst });
                    }
                },
                Work::PairChoices {
                    op,
                    fixed,
                    rest,
                    selection,
                    complement,
                    used,
                    depth,
                    mut next_index,
                    goals,
                    subst,
                } => {
                    while next_index < selection.len() && used[next_index] {
                        next_index += 1;
                    }
                    if next_index == selection.len() {
                        continue;
                    }
                    let selected = next_index;
                    work.push(Work::PairChoices {
                        op,
                        fixed,
                        rest,
                        selection: selection.clone(),
                        complement: complement.clone(),
                        used: used.clone(),
                        depth,
                        next_index: selected + 1,
                        goals: goals.clone(),
                        subst: subst.clone(),
                    });
                    let mut branch_used = used;
                    branch_used[selected] = true;
                    let mut branch_goals = goals;
                    branch_goals.push(Goal::ContinuePair {
                        op,
                        fixed,
                        rest,
                        selection: selection.clone(),
                        complement,
                        used: branch_used,
                        depth: depth + 1,
                    });
                    branch_goals.push(Goal::Match {
                        pattern: &fixed[depth],
                        class: selection[selected],
                    });
                    work.push(Work::Run { goals: branch_goals, subst });
                },
            }
        }
    }

    /// Add a fresh canonical n-ary `op` node over `children` (sorted by canonical
    /// class key — the same canonical bag order the lowering produces), within
    /// the node budget. `None` (with [`node_limit_reached`](EGraph::node_limit_reached)
    /// set) if a fresh node would overflow the budget.
    fn add_canonical_bag(&mut self, op: L, children: &[EClassId]) -> Option<EClassId> {
        let mut sorted: Vec<EClassId> = children.iter().map(|&c| self.find(c)).collect();
        // `sort_by_cached_key` computes each (non-trivial) canonical key ONCE,
        // rather than twice per comparison.
        sorted.sort_by_cached_key(|&c| self.canonical_class_key(c));
        self.try_add_with_budget(ENode::new(op, sorted))
    }

    /// Add a canonical n-ary `op` bag, FLATTENING any child that is itself an
    /// `op`-bag — the ASSOCIATIVE half of AC: `op{P, op{Q, R}} ≡ op{P, Q, R}`.
    /// A constructed rewrite result is thus one flat bag (matching the generated
    /// `normalize()`'s iterative `insert_into_<bag>`), not a bag-of-bags.
    ///
    /// Only constructed RESULTS are flattened here; seeds keep their parsed
    /// structure (the grammar already parses `{p | p | ...}` as a flat bag, so
    /// seeds carry no same-`op` nesting to peel — only a rewrite that places a
    /// bag-valued binding into a new bag introduces a layer).
    ///
    /// Iterative work-stack (no recursion, so deep nesting cannot overflow the
    /// call stack). MULTIPLICITY-preserving: a bag class spliced as two distinct
    /// siblings flattens twice (`op{op{B}, op{B}} ⇒ op{B, B}`). CYCLE-guarded by
    /// a per-splice-path ancestor set: a class reachable as its own splice
    /// ancestor — which a terminating rewrite never produces (RHS bag members are
    /// proper subterms), but the generic e-graph could after merges — is kept as
    /// a leaf rather than looping. A class is a bag iff it carries an `op`-labeled
    /// node, the same interpretation the matcher and the `rest` splice use.
    fn add_flattened_bag(&mut self, op: L, children: &[EClassId]) -> Option<EClassId> {
        let mut flat: Vec<EClassId> = Vec::with_capacity(children.len());
        // (class to place, the set of bag classes whose splice is in progress
        // strictly above it on this path). Pushed in reverse for a stable
        // left-to-right splice order (the final canonical sort makes order
        // irrelevant, but determinism aids debugging).
        let mut stack: Vec<(EClassId, HashSet<EClassId>)> = children
            .iter()
            .rev()
            .map(|&c| (self.find(c), HashSet::default()))
            .collect();
        while let Some((class, ancestors)) = stack.pop() {
            let class = self.find(class);
            let bag_children: Option<Vec<EClassId>> = if ancestors.contains(&class) {
                None // cycle on this path: keep as a leaf, do not expand.
            } else {
                self.nodes(class)
                    .iter()
                    .find(|n| n.op == op)
                    .map(|n| n.children.iter().map(|&c| self.find(c)).collect())
            };
            match bag_children {
                Some(grandchildren) => {
                    let mut child_ancestors = ancestors.clone();
                    child_ancestors.insert(class);
                    for &gc in grandchildren.iter().rev() {
                        stack.push((self.find(gc), child_ancestors.clone()));
                    }
                },
                None => flat.push(class),
            }
        }
        self.add_canonical_bag(op, &flat)
    }

    fn rhs_vars_bound(pattern: &Pattern<L>, subst: &Subst) -> bool {
        let mut pending = vec![pattern];
        while let Some(pattern) = pending.pop() {
            match pattern {
                Pattern::Var(name) => {
                    if !subst.contains_key(name) {
                        return false;
                    }
                },
                Pattern::App { args, .. } => pending.extend(args.iter().rev()),
                Pattern::AcApp { fixed, rest, .. } => {
                    if rest.as_ref().is_some_and(|name| !subst.contains_key(name)) {
                        return false;
                    }
                    pending.extend(fixed.iter().rev());
                },
            }
        }
        true
    }

    fn batched_segment_matches(&self, segment: &PositionalRuleSegment<L>) -> BatchedSegmentMatches {
        let mut grouped = vec![Vec::new(); segment.end - segment.start];
        let SetAutomatonRun { matches, stats } = segment.automaton.search_egraph(self);
        for matched in matches {
            let Some(slot) = matched.pattern.0.checked_sub(segment.start) else {
                continue;
            };
            if let Some(rule_matches) = grouped.get_mut(slot) {
                rule_matches.push((matched.root, matched.subst));
            }
        }
        BatchedSegmentMatches { grouped, stats }
    }

    fn apply_structural_matches(
        &mut self,
        rule: &RewriteRule<L>,
        matches: Vec<(EClassId, Subst)>,
        justifications: &mut Vec<RewriteJustification>,
    ) -> RuleApplication {
        let before_nodes = self.node_count();
        let mut rule_merges = 0usize;
        let mut budget_hit = false;
        for (root, subst) in matches {
            if !Self::rhs_vars_bound(&rule.rhs, &subst) {
                // Ill-formed rule for this match: reject before adding
                // any partial RHS nodes.
                continue;
            }
            if let Some(rhs_id) = self.instantiate(&rule.rhs, &subst) {
                if self.find(root) != self.find(rhs_id) {
                    self.merge(root, rhs_id);
                    rule_merges += 1;
                    // Capture this firing's σ additively (the count aggregation
                    // in `record_rule_firing` is unchanged). `subst` is no longer
                    // borrowed after the RHS instantiation above, so it moves in.
                    justifications.push(RewriteJustification {
                        rule_label: rule.label.clone(),
                        root: self.find(root),
                        subst,
                    });
                }
            } else if self.node_limit_reached() {
                budget_hit = true;
                break;
            }
            // else: a budgeted add refused a fresh node without setting
            // the sticky flag; skip defensively.
        }

        RuleApplication {
            merges: rule_merges,
            budget_hit,
            graph_changed: rule_merges > 0 || self.node_count() != before_nodes,
        }
    }

    fn apply_native_matches(
        &mut self,
        rule: &NativeRule<L>,
        matches: Vec<(EClassId, Subst)>,
        dispatch: &NativeDispatch<'_, L>,
        justifications: &mut Vec<RewriteJustification>,
    ) -> RuleApplication {
        let before_nodes = self.node_count();
        let mut rule_merges = 0usize;
        let mut budget_hit = false;
        for (root, subst) in matches {
            match dispatch(rule.op, self, &subst) {
                Some(result_id) => {
                    if self.find(root) != self.find(result_id) {
                        self.merge(root, result_id);
                        rule_merges += 1;
                        // Capture this native firing's σ additively; `subst` is
                        // no longer borrowed after `dispatch` returned, so it
                        // moves in.
                        justifications.push(RewriteJustification {
                            rule_label: rule.label.clone(),
                            root: self.find(root),
                            subst,
                        });
                    }
                },
                None if self.node_limit_reached() => {
                    budget_hit = true;
                    break;
                },
                None => {
                    // The redex does not reduce here (variable / stuck
                    // child, or unfunded admission); leave it in place,
                    // faithful to a fold premise with no solution.
                },
            }
        }

        RuleApplication {
            merges: rule_merges,
            budget_hit,
            graph_changed: rule_merges > 0 || self.node_count() != before_nodes,
        }
    }

    /// Instantiate a RHS pattern under a substitution, adding nodes within the
    /// node budget. Returns `None` if a variable is unbound (ill-formed rule) or
    /// the budget refused a fresh node (then `node_limit_reached()` is set).
    ///
    /// `pub` so the step-only rewrite enumerator (the REPL `step` rewrite-graph stepper) can build a
    /// rule's RHS class on a fresh, unsaturated single-term e-graph and splice it into the term's
    /// derivation — the same AC-flattening RHS construction saturation uses, reused read-only.
    /// Adds no behavior and no production-path cost (production saturation is unchanged).
    pub fn instantiate(&mut self, pattern: &Pattern<L>, subst: &Subst) -> Option<EClassId> {
        enum Task<'a, L> {
            Visit(&'a Pattern<L>),
            AssembleApp {
                op: L,
                child_count: usize,
            },
            AssembleAc {
                op: L,
                fixed_count: usize,
                rest: Option<&'a str>,
            },
        }

        let mut tasks = vec![Task::Visit(pattern)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Pattern::Var(name)) => {
                    values.push(self.find(*subst.get(name)?));
                },
                Task::Visit(Pattern::App { op, args }) => {
                    tasks.push(Task::AssembleApp { op: op.clone(), child_count: args.len() });
                    tasks.extend(args.iter().rev().map(Task::Visit));
                },
                Task::Visit(Pattern::AcApp { op, fixed, rest }) => {
                    tasks.push(Task::AssembleAc {
                        op: op.clone(),
                        fixed_count: fixed.len(),
                        rest: rest.as_deref(),
                    });
                    tasks.extend(fixed.iter().rev().map(Task::Visit));
                },
                Task::AssembleApp { op, child_count } => {
                    let first_child = values
                        .len()
                        .checked_sub(child_count)
                        .expect("instantiation PDA lost an application child");
                    let children = values.split_off(first_child);
                    values.push(self.try_add_with_budget(ENode::new(op, children))?);
                },
                Task::AssembleAc { op, fixed_count, rest } => {
                    let first_child = values
                        .len()
                        .checked_sub(fixed_count)
                        .expect("instantiation PDA lost an AC child");
                    let mut children = values.split_off(first_child);
                    if let Some(name) = rest {
                        children.push(self.find(*subst.get(name)?));
                    }
                    values.push(self.add_flattened_bag(op, &children)?);
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop()
    }

    /// Equality saturation: apply `rules` to a fixpoint, or until the node budget
    /// or `max_iters` is hit. Every fired rule ADDS an equality (merge); nothing
    /// is pruned. Limits are reported in [`SatReport::outcome`].
    ///
    /// This is the structural-only entry point (no native-computed rewrites). It
    /// delegates to [`saturate_with_native`](Self::saturate_with_native) with an
    /// empty native-rule set and a dispatcher that fires nothing, so every
    /// existing caller is unchanged.
    pub fn saturate(&mut self, rules: &[RewriteRule<L>], max_iters: usize) -> SatReport {
        let compiled = CompiledRuleSet::from_rewrites(rules.to_vec());
        self.saturate_compiled(&compiled, max_iters)
    }

    /// Equality saturation for an already compiled structural-only rule set.
    pub fn saturate_compiled(
        &mut self,
        compiled: &CompiledRuleSet<L>,
        max_iters: usize,
    ) -> SatReport {
        self.saturate_compiled_with_native(compiled, &|_op, _eg, _subst| None, max_iters)
    }

    /// Equality saturation over BOTH structural [`RewriteRule`]s and
    /// native-computed [`NativeRule`]s, to a fixpoint or until the node budget /
    /// `max_iters` is hit.
    ///
    /// Native rules realize the *fold* fragment of GSLT reduction. For each match
    /// `(root, subst)` of a native rule's `lhs`, `dispatch(op, self, &subst)`
    /// computes an optional result e-class — the fold body run on the
    /// funded-best children extracted from the classes in `subst` — which is then
    /// merged with `root`. `dispatch` returning `None` means the redex does not
    /// reduce here (a variable or otherwise-stuck child, or the body's funded
    /// admission failed); the redex is left in place, faithful to a fold premise
    /// with no solution.
    ///
    /// Like a structural rule, a native rule only ADDS the equality
    /// `redex == result`: nothing is pruned (the substructural no-contraction
    /// law), and the node budget `Σ` bounds it (`is_funded(Δ, Σ, margin)`). A
    /// folded redex reduces to a normal form (e.g. a cast literal) that no longer
    /// matches the redex pattern, so it fires once and saturation still reaches
    /// `Converged`/`NodeLimit`.
    pub fn saturate_with_native(
        &mut self,
        rules: &[RewriteRule<L>],
        native_rules: &[NativeRule<L>],
        dispatch: &NativeDispatch<'_, L>,
        max_iters: usize,
    ) -> SatReport {
        let compiled = CompiledRuleSet::new(rules.to_vec(), native_rules.to_vec());
        self.saturate_compiled_with_native(&compiled, dispatch, max_iters)
    }

    /// Equality saturation for an already compiled structural/native rule set.
    ///
    /// The compiled value owns the rules and their positional set automata, so
    /// callers can reuse it across many input e-graphs without rebuilding the
    /// root dispatch index each run. AC patterns still execute through the lazy
    /// matcher because their `rest` complements can grow the e-graph under the
    /// runtime node budget.
    pub fn saturate_compiled_with_native(
        &mut self,
        compiled: &CompiledRuleSet<L>,
        dispatch: &NativeDispatch<'_, L>,
        max_iters: usize,
    ) -> SatReport {
        let mut stats = SatStats::default();
        let mut rule_firings = Vec::new();
        let mut rewrite_justifications = Vec::new();
        let rules = compiled.rewrite_rules();
        let native_rules = compiled.native_rules();
        let structural_segments = &compiled.structural_segments;
        let native_segments = &compiled.native_segments;
        for iteration in 0..max_iters {
            stats.iterations = iteration + 1;
            let mut iter_merges = 0usize;
            // ── Structural rules: instantiate the pattern RHS and merge. ──
            let mut rule_idx = 0usize;
            let mut segment_idx = 0usize;
            while rule_idx < rules.len() {
                if structural_segments
                    .get(segment_idx)
                    .is_some_and(|segment| segment.start == rule_idx)
                {
                    let segment = &structural_segments[segment_idx];
                    let BatchedSegmentMatches { mut grouped, stats: batch_stats } =
                        self.batched_segment_matches(segment);
                    stats.record_set_automaton_batch(batch_stats);
                    let mut batch_valid = true;
                    for current in segment.start..segment.end {
                        let matches = if batch_valid {
                            std::mem::take(&mut grouped[current - segment.start])
                        } else {
                            let search = self.search_observed(&rules[current].lhs);
                            let budget_hit = search.budget_hit;
                            stats.record_rule_search(&search);
                            if budget_hit {
                                return SatReport::new(
                                    SaturationOutcome::NodeLimit,
                                    stats,
                                    rule_firings,
                                    rewrite_justifications,
                                );
                            }
                            search.matches
                        };
                        let applied = self.apply_structural_matches(
                            &rules[current],
                            matches,
                            &mut rewrite_justifications,
                        );
                        if applied.merges > 0 {
                            self.rebuild();
                        }
                        iter_merges += applied.merges;
                        stats.total_merges += applied.merges;
                        record_rule_firing(
                            &mut rule_firings,
                            &rules[current].label,
                            applied.merges,
                        );
                        if applied.budget_hit {
                            return SatReport::new(
                                SaturationOutcome::NodeLimit,
                                stats,
                                rule_firings,
                                rewrite_justifications,
                            );
                        }
                        if applied.graph_changed && batch_valid {
                            stats.set_automaton_batch_invalidations += 1;
                            batch_valid = false;
                        }
                    }
                    rule_idx = segment.end;
                    segment_idx += 1;
                } else {
                    let search = self.search_observed(&rules[rule_idx].lhs);
                    let budget_hit = search.budget_hit;
                    stats.record_rule_search(&search);
                    if budget_hit {
                        return SatReport::new(
                            SaturationOutcome::NodeLimit,
                            stats,
                            rule_firings,
                            rewrite_justifications,
                        );
                    }
                    let matches = search.matches;
                    let applied = self.apply_structural_matches(
                        &rules[rule_idx],
                        matches,
                        &mut rewrite_justifications,
                    );
                    if applied.merges > 0 {
                        self.rebuild();
                    }
                    iter_merges += applied.merges;
                    stats.total_merges += applied.merges;
                    record_rule_firing(&mut rule_firings, &rules[rule_idx].label, applied.merges);
                    if applied.budget_hit {
                        return SatReport::new(
                            SaturationOutcome::NodeLimit,
                            stats,
                            rule_firings,
                            rewrite_justifications,
                        );
                    }
                    rule_idx += 1;
                }
            }
            // ── Native rules: dispatch computes the funded result, then merge. ──
            let mut rule_idx = 0usize;
            let mut segment_idx = 0usize;
            while rule_idx < native_rules.len() {
                if native_segments
                    .get(segment_idx)
                    .is_some_and(|segment| segment.start == rule_idx)
                {
                    let segment = &native_segments[segment_idx];
                    let BatchedSegmentMatches { mut grouped, stats: batch_stats } =
                        self.batched_segment_matches(segment);
                    stats.record_set_automaton_batch(batch_stats);
                    let mut batch_valid = true;
                    for current in segment.start..segment.end {
                        let matches = if batch_valid {
                            std::mem::take(&mut grouped[current - segment.start])
                        } else {
                            let search = self.search_observed(&native_rules[current].lhs);
                            let budget_hit = search.budget_hit;
                            stats.record_rule_search(&search);
                            if budget_hit {
                                return SatReport::new(
                                    SaturationOutcome::NodeLimit,
                                    stats,
                                    rule_firings,
                                    rewrite_justifications,
                                );
                            }
                            search.matches
                        };
                        let applied = self.apply_native_matches(
                            &native_rules[current],
                            matches,
                            dispatch,
                            &mut rewrite_justifications,
                        );
                        if applied.merges > 0 {
                            self.rebuild();
                        }
                        iter_merges += applied.merges;
                        stats.total_merges += applied.merges;
                        record_rule_firing(
                            &mut rule_firings,
                            &native_rules[current].label,
                            applied.merges,
                        );
                        if applied.budget_hit {
                            return SatReport::new(
                                SaturationOutcome::NodeLimit,
                                stats,
                                rule_firings,
                                rewrite_justifications,
                            );
                        }
                        if applied.graph_changed && batch_valid {
                            stats.set_automaton_batch_invalidations += 1;
                            batch_valid = false;
                        }
                    }
                    rule_idx = segment.end;
                    segment_idx += 1;
                } else {
                    let search = self.search_observed(&native_rules[rule_idx].lhs);
                    let budget_hit = search.budget_hit;
                    stats.record_rule_search(&search);
                    if budget_hit {
                        return SatReport::new(
                            SaturationOutcome::NodeLimit,
                            stats,
                            rule_firings,
                            rewrite_justifications,
                        );
                    }
                    let matches = search.matches;
                    let applied = self.apply_native_matches(
                        &native_rules[rule_idx],
                        matches,
                        dispatch,
                        &mut rewrite_justifications,
                    );
                    if applied.merges > 0 {
                        self.rebuild();
                    }
                    iter_merges += applied.merges;
                    stats.total_merges += applied.merges;
                    record_rule_firing(
                        &mut rule_firings,
                        &native_rules[rule_idx].label,
                        applied.merges,
                    );
                    if applied.budget_hit {
                        return SatReport::new(
                            SaturationOutcome::NodeLimit,
                            stats,
                            rule_firings,
                            rewrite_justifications,
                        );
                    }
                    rule_idx += 1;
                }
            }
            if iter_merges == 0 {
                return SatReport::new(
                    SaturationOutcome::Converged,
                    stats,
                    rule_firings,
                    rewrite_justifications,
                );
            }
        }
        SatReport::new(
            SaturationOutcome::IterationLimit,
            stats,
            rule_firings,
            rewrite_justifications,
        )
    }
}

// ════════════════════════════════════════════════════════════════════════════
// EP-P6a DV-0 PROBE (measurement-only; 2026-06-12)
// ════════════════════════════════════════════════════════════════════════════
//
// Binding contract: docs/design/evidence-pruning/02-staged-implementation-plan.md
// §P6a. This is a MEASUREMENT-ONLY probe deciding the DV-1 gate; it implements
// NOTHING beyond the counters. It does not alter any production code path (the
// 39 baseline tests are untouched).
//
// Counters required by the contract:
//   - `enodes_added_total`            : e-nodes created DURING saturation
//                                       (post-saturation live node_count minus
//                                       the pre-saturation seed node_count).
//   - `enodes_in_extracted_derivations`: distinct e-nodes (by exact ContentKey of
//                                       the canonical (op, child-classes) node)
//                                       that appear in the chosen best derivation
//                                       trees of the demanded roots — MARKED by
//                                       walking those derivations.
//   - saturation share of eval wall-time (saturation ns / (saturation+extraction) ns).
//
// GATE: untouched-share = 1 - (in_extracted / added_total) ≥ 50% AND
//       saturation ≥ 20% of eval wall-time  →  recommend DV-1; else record the non-goal.
//
// CORPUS CAVEAT (recorded in findings.md, pre-P6 framing): when this DV-0 probe was
// written the rholang eval corpus did NOT route through dovetail — `rholang-runtime`
// runs f1r3node's RhoRuntime directly (run.rs). Post-P6, dovetail is the live
// general-purpose backend (via the `languages` `dovetail-codegen` default feature);
// rholang process terms still execute on the host RhoRuntime while dovetail reduces
// the in-engine folds. So this probe still measures the LARGEST representative
// dovetail workload: a saturate→extract arithmetic-rewrite system that mirrors the
// equality-saturation shape the flip created. The corpus-representativeness caveat
// carries to the flip epic.
#[cfg(test)]
mod dv0_probe {
    use std::collections::HashSet;
    use std::time::Instant;

    use rigail::TropicalWeight;

    use crate::egraph::{EClassId, EGraph, ENode};
    use crate::extract::{Derivation, Extractor};
    use crate::key::{ContentKey, ContentKeySet};
    use crate::rules::{Pattern, RewriteRule};

    /// Cost model: leaf digits cost their value, structural ops a flat 1, and the
    /// `h`-nesting "expander" (an unbounded-growth rule, mirroring the saturation
    /// blow-up the budget guards) costs 1 so the cheaper non-expanded form wins.
    fn weigh(n: &ENode<String>) -> TropicalWeight {
        match n.op.as_str() {
            "add" | "mul" => TropicalWeight(1.0),
            "h" => TropicalWeight(1.0),
            s => match s.parse::<f64>() {
                Ok(v) => TropicalWeight(v.max(1.0)),
                Err(_) => TropicalWeight(1.0),
            },
        }
    }

    /// The exact ContentKey of a node's CANONICAL (op, child-classes) identity —
    /// the same identity the e-graph hashconses on. Used to MARK e-nodes reached
    /// by the extracted derivations.
    fn node_key(op: &str, child_classes: &[EClassId]) -> ContentKey {
        let mut bytes = Vec::new();
        crate::key::SemanticHash::write_content(&op.to_string(), &mut bytes);
        for c in child_classes {
            crate::key::write_framed(&mut bytes, &c.0.to_le_bytes());
        }
        ContentKey::from_bytes(bytes)
    }

    /// Walk a chosen derivation tree, inserting each node's canonical key into
    /// `marked`. A derivation node carries `class` (its e-class) and `children`
    /// (the chosen child derivations), so the canonical (op, child-class) key is
    /// reconstructable and matches the e-graph's hashcons identity.
    fn mark_derivation(
        eg: &EGraph<String>,
        d: &Derivation<String, TropicalWeight>,
        marked: &mut ContentKeySet,
    ) {
        let child_classes: Vec<EClassId> = d.children.iter().map(|c| eg.find(c.class)).collect();
        marked.insert(node_key(&d.op, &child_classes));
        for c in &d.children {
            mark_derivation(eg, c, marked);
        }
    }

    /// DV-0′ (2026-06-17): the PRODUCTION-SHAPE touched set. Production extraction
    /// (`dovetail_report.rs:735/739`) uses a CONSTANT-ZERO weight + `collect_checked`
    /// (the FULL derivation stream), not the 1-best `kth` the original probe used. Under
    /// equal weights the full stream visits EVERY e-node backward-reachable from a root,
    /// so the honest "touched" set = the root-reachable e-node set, computed here directly
    /// by class→node→child reachability (sound, and cheap — no stream enumeration). The
    /// `dv0_prod_shape_reachability_equals_collect_checked` test cross-checks that this
    /// equals what a real constant-zero `collect_checked` marks.
    /// Every canonical node key currently live in the e-graph (across all classes).
    /// Used to isolate the SATURATION-ADDED population: `added = after \ seed`.
    fn all_node_keys(eg: &EGraph<String>) -> ContentKeySet {
        let mut keys = ContentKeySet::default();
        for cls in eg.classes() {
            for n in eg.nodes(cls) {
                let child_classes: Vec<EClassId> = n.children.iter().map(|&c| eg.find(c)).collect();
                keys.insert(node_key(&n.op, &child_classes));
            }
        }
        keys
    }

    fn reachable_node_keys(eg: &EGraph<String>, roots: &[EClassId]) -> ContentKeySet {
        let mut marked = ContentKeySet::default();
        let mut seen_classes: HashSet<EClassId> = HashSet::default();
        let mut stack: Vec<EClassId> = roots.iter().map(|&r| eg.find(r)).collect();
        while let Some(cls) = stack.pop() {
            let cls = eg.find(cls);
            if !seen_classes.insert(cls) {
                continue;
            }
            for n in eg.nodes(cls) {
                let child_classes: Vec<EClassId> = n.children.iter().map(|&c| eg.find(c)).collect();
                marked.insert(node_key(&n.op, &child_classes));
                for &c in &n.children {
                    stack.push(eg.find(c));
                }
            }
        }
        marked
    }

    /// Build a saturate→extract workload, returning
    /// (enodes_added_total, enodes_in_extracted_KBEST, enodes_reachable_PROD,
    ///  prod_collect_checked_marked_or_0, sat_ns, extract_ns, total_live_nodes,
    ///  demanded_roots, nf_count).
    ///
    /// `enodes_in_extracted_KBEST` is the original 1-best/k-best touched count (the
    /// INFLATED measure). `enodes_reachable_PROD` is the DV-0′ production-shape touched
    /// count (root-reachable = what constant-zero `collect_checked` marks).
    #[allow(clippy::type_complexity)]
    fn run_workload(
        seed: &str,
        depth_terms: usize,
        kbest: usize,
    ) -> (usize, usize, usize, usize, u128, u128, usize, usize, usize) {
        // ── Build the e-graph + seed a small batch of distinct arithmetic terms.
        let mut eg = EGraph::<String>::new();
        let mut roots: Vec<EClassId> = Vec::new();
        // A pool of leaves shared across the seeded terms (so saturation/congruence
        // has cross-term structure to grow, like a real reduction corpus).
        let leaves: Vec<EClassId> = (0..6)
            .map(|i| eg.add(ENode::leaf(format!("{}", i + 1))))
            .collect();
        for t in 0..depth_terms {
            // add(mul(a,b), c)  with a/b/c rotating through the leaf pool.
            let a = leaves[t % leaves.len()];
            let b = leaves[(t + 1) % leaves.len()];
            let c = leaves[(t + 2) % leaves.len()];
            let m = eg.add(ENode::new("mul".into(), vec![a, b]));
            let r = eg.add(ENode::new("add".into(), vec![m, c]));
            roots.push(r);
        }
        let _ = seed; // (seed label reserved for diagnostic naming)
        eg.rebuild();
        // DV-0′: the seed node KEYSET, so the saturation-added population is exactly
        // `after \ seed` and untouched-shares are true set-differences over it.
        let seed_keys = all_node_keys(&eg);

        // ── Rewrite system that GROWS the e-graph with equivalent-but-costlier
        //    forms (the CESK runtime-backend replacement analog: every rule adds
        //    an equality, nothing is pruned). `x -> add(x, h(x))`-style expanders plus
        //    commutativity create many materialized e-nodes that extraction will
        //    NOT choose (the cheaper original wins), which is exactly the
        //    "added but untouched" share DV-0 quantifies.
        let rules = vec![
            // commutativity of mul: mul(x,y) ~ mul(y,x)
            RewriteRule {
                lhs: Pattern::app("mul".into(), vec![Pattern::var("x"), Pattern::var("y")]),
                rhs: Pattern::app("mul".into(), vec![Pattern::var("y"), Pattern::var("x")]),
                label: Some("mul_comm".into()),
            },
            // commutativity of add
            RewriteRule {
                lhs: Pattern::app("add".into(), vec![Pattern::var("x"), Pattern::var("y")]),
                rhs: Pattern::app("add".into(), vec![Pattern::var("y"), Pattern::var("x")]),
                label: Some("add_comm".into()),
            },
            // an expander that introduces costlier equivalent structure:
            //   add(x,y) ~ add(x, mul(1, y))   (identity-via-mul, costlier ⇒ unchosen)
            RewriteRule {
                lhs: Pattern::app("add".into(), vec![Pattern::var("x"), Pattern::var("y")]),
                rhs: Pattern::app(
                    "add".into(),
                    vec![
                        Pattern::var("x"),
                        Pattern::app(
                            "mul".into(),
                            vec![Pattern::leaf("1".into()), Pattern::var("y")],
                        ),
                    ],
                ),
                label: Some("add_mul_ident".into()),
            },
        ];

        // ── SATURATION (timed). Bounded iters so commutativity doesn't ping-pong
        //    forever; the expander grows structure each pass.
        let t0 = Instant::now();
        let _report = eg.saturate(&rules, 6);
        let sat_ns = t0.elapsed().as_nanos();

        // ── DV-0′: the saturation-ADDED population as a true keyset (after \ seed).
        //    All untouched-shares below are set-differences over THIS set, so a node
        //    counts as "untouched" iff it was added by saturation AND no extraction
        //    derivation reaches it — no count/clamp imprecision, no seed contamination.
        let added_keys: ContentKeySet =
            all_node_keys(&eg).difference(&seed_keys).cloned().collect();
        let added = added_keys.len();

        // ── 1-best/k-best EXTRACTION (timed): the INFLATED legacy measure. The
        //    admissible 0̄-inside skip + a real cost weight make `kth` stop early.
        let t1 = Instant::now();
        let mut marked = ContentKeySet::default();
        let mut nf_count = 0usize;
        {
            let mut ex = Extractor::new(&eg, weigh).with_heuristic();
            for &root in &roots {
                for k in 0..kbest {
                    match ex.kth(root, k).value {
                        Some(d) => {
                            mark_derivation(&eg, &d, &mut marked);
                            nf_count += 1;
                        },
                        None => break,
                    }
                }
            }
        }
        let extract_ns = t1.elapsed().as_nanos();
        let kbest_in_added = added_keys.intersection(&marked).count();

        // ── DV-0′ PRODUCTION-SHAPE reach (constant-zero weight, full-stream).
        //    The honest touched set = root-reachable e-nodes (§2.1/§2.5 of the plan).
        let reachable = reachable_node_keys(&eg, &roots);
        let prod_in_added = added_keys.intersection(&reachable).count();

        // Cross-check on the SMALL workload only (full-stream collect_checked can be
        // large on the commutativity-saturated graph): a real constant-zero
        // `collect_checked` marks exactly the reachable ADDED nodes — validating
        // reachability as a faithful production-shape proxy (not an over/under-count).
        let prod_chkd_in_added = if depth_terms <= 4 {
            let mut prod_ex = Extractor::new(&eg, |_: &ENode<String>| TropicalWeight(0.0));
            let mut pm = ContentKeySet::default();
            for &root in &roots {
                let checked = prod_ex.derivations(eg.find(root)).collect_checked();
                for d in &checked.value {
                    mark_derivation(&eg, d, &mut pm);
                }
            }
            added_keys.intersection(&pm).count()
        } else {
            0
        };

        (
            added,
            kbest_in_added,
            prod_in_added,
            prod_chkd_in_added,
            sat_ns,
            extract_ns,
            eg.node_count(),
            roots.len(),
            nf_count,
        )
    }

    /// DV-0′ AMBIENT-FAITHFUL workload (2026-06-17): exercises the REAL AC mechanism
    /// the only live structural-saturation language (Ambient) uses — `par` bags with
    /// `open(n)`/`amb(n,p)` redexes reduced by an AcApp OpenRule, materializing the
    /// canonical-bag complement fan (`collect_ac_matches`/`add_canonical_bag`). This
    /// addresses the "re-derive against Ambient, not the synthetic arithmetic" mandate.
    /// Returns the same shape as `run_workload`.
    #[allow(clippy::type_complexity)]
    fn run_ambient_ac_workload(
        depth_terms: usize,
    ) -> (usize, usize, usize, usize, u128, u128, usize, usize, usize) {
        let mut eg = EGraph::<String>::new();
        let mut roots: Vec<EClassId> = Vec::new();
        // Inert process leaves shared across bags (give the AC complement fan width).
        let inert: Vec<EClassId> = (0..4)
            .map(|i| eg.add(ENode::leaf(format!("p{i}"))))
            .collect();
        for t in 0..depth_terms {
            let n = eg.add(ENode::leaf(format!("n{t}")));
            let p = eg.add(ENode::leaf(format!("q{t}")));
            let amb = eg.add(ENode::new("amb".into(), vec![n, p]));
            let open = eg.add(ENode::new("open".into(), vec![n]));
            // par{ open(n), amb(n,p), p0, p1, p2, p3 } — multi-element bag ⇒ the
            // OpenRule match must select {open,amb} and materialize the inert complement.
            let mut bag = vec![open, amb];
            bag.extend(inert.iter().copied());
            let par = eg.add(ENode::new("par".into(), bag));
            roots.push(par);
        }
        eg.rebuild();
        let seed_keys = all_node_keys(&eg);

        // OpenRule (AC): par{ open(n), amb(n,x), ...rest } ~> par{ x, ...rest }.
        let rules = vec![RewriteRule {
            lhs: Pattern::ac(
                "par".into(),
                vec![
                    Pattern::app("open".into(), vec![Pattern::var("n")]),
                    Pattern::app("amb".into(), vec![Pattern::var("n"), Pattern::var("x")]),
                ],
                Some("rest".into()),
            ),
            rhs: Pattern::ac("par".into(), vec![Pattern::var("x")], Some("rest".into())),
            label: Some("open_rule".into()),
        }];

        let t0 = Instant::now();
        let _report = eg.saturate(&rules, 6);
        let sat_ns = t0.elapsed().as_nanos();

        let added_keys: ContentKeySet =
            all_node_keys(&eg).difference(&seed_keys).cloned().collect();
        let added = added_keys.len();

        let t1 = Instant::now();
        let mut marked = ContentKeySet::default();
        let mut nf_count = 0usize;
        {
            // Flat weight: every node costs 1 (no arithmetic leaf values here).
            let mut ex =
                Extractor::new(&eg, |_: &ENode<String>| TropicalWeight(1.0)).with_heuristic();
            for &root in &roots {
                if let Some(d) = ex.kth(root, 0).value {
                    mark_derivation(&eg, &d, &mut marked);
                    nf_count += 1;
                }
            }
        }
        let extract_ns = t1.elapsed().as_nanos();
        let kbest_in_added = added_keys.intersection(&marked).count();

        let reachable = reachable_node_keys(&eg, &roots);
        let prod_in_added = added_keys.intersection(&reachable).count();

        // Full-stream constant-zero collect_checked cross-check (bags are bounded here).
        let prod_chkd_in_added = {
            let mut prod_ex = Extractor::new(&eg, |_: &ENode<String>| TropicalWeight(0.0));
            let mut pm = ContentKeySet::default();
            for &root in &roots {
                let checked = prod_ex.derivations(eg.find(root)).collect_checked();
                for d in &checked.value {
                    mark_derivation(&eg, d, &mut pm);
                }
            }
            added_keys.intersection(&pm).count()
        };

        (
            added,
            kbest_in_added,
            prod_in_added,
            prod_chkd_in_added,
            sat_ns,
            extract_ns,
            eg.node_count(),
            roots.len(),
            nf_count,
        )
    }

    #[test]
    fn dv0_saturation_vs_extraction_reach_report() {
        // Three workload sizes so the share is observed across scale, not a single
        // point. Printed for the ledger; the test ASSERTS only the invariants the
        // measurement relies on (it refutes nothing — DV-0 is measurement-only).
        println!(
            "\n=== EP-P6a DV-0′ PROBE (dovetail saturate→extract; 1-best vs PRODUCTION shape) ==="
        );
        println!(
            "{:<10} {:>10} {:>11} {:>9} {:>10} {:>9} {:>11} {:>9} {:>10}",
            "workload",
            "added(sat)",
            "kbest_in",
            "untch_kb%",
            "prod_reach",
            "untch_pr%",
            "prod_chkd",
            "sat%wall",
            "roots/nf"
        );
        for (name, depth, kbest) in [
            ("small_k1", 4usize, 1usize),
            ("med_k1", 12, 1),
            ("large_k1", 32, 1),
            // a k=3 variant: pulling more alternatives touches MORE nodes, the
            // honest upper bound on 1-best extraction reach.
            ("large_k3", 32, 3),
        ] {
            let (added, in_ex, reach, prod_chkd, sat_ns, ext_ns, _live, roots, nf) =
                run_workload(name, depth, kbest);
            // Inflated 1-best untouched-share (the original DV-0 measure).
            let untouched_kb = if added == 0 {
                0.0
            } else {
                100.0 * (added.saturating_sub(in_ex.min(added)) as f64) / (added as f64)
            };
            // DV-0′ honest production-shape untouched-share (root-reachable touched set).
            let untouched_pr = if added == 0 {
                0.0
            } else {
                100.0 * (added.saturating_sub(reach.min(added)) as f64) / (added as f64)
            };
            let total_ns = sat_ns + ext_ns;
            let sat_pct = if total_ns == 0 {
                0.0
            } else {
                100.0 * (sat_ns as f64) / (total_ns as f64)
            };
            println!(
                "{:<10} {:>10} {:>11} {:>8.1}% {:>10} {:>8.1}% {:>11} {:>8.1}% {:>5}/{:<4}",
                name,
                added,
                in_ex,
                untouched_kb,
                reach,
                untouched_pr,
                prod_chkd,
                sat_pct,
                roots,
                nf
            );

            // Measurement-soundness invariants (NOT pruning assertions):
            assert!(in_ex >= 1, "1-best extraction touched at least one e-node");
            assert!(reach >= in_ex, "prod reach ⊇ 1-best touched (full stream ⊇ best path)");
            // Cross-check (small workload): a real constant-zero collect_checked marks a
            // SUBSET of the reachability proxy (it can only touch reachable nodes).
            if prod_chkd > 0 {
                assert!(
                    prod_chkd <= reach,
                    "collect_checked marked ({prod_chkd}) ⊆ reachable ({reach})"
                );
            }
        }
        // ── AMBIENT-FAITHFUL AC workload (the real structural-saturation language).
        for (name, depth) in [("amb_ac_s", 3usize), ("amb_ac_m", 8), ("amb_ac_l", 16)] {
            let (added, in_ex, reach, prod_chkd, sat_ns, ext_ns, _live, roots, nf) =
                run_ambient_ac_workload(depth);
            let untouched_kb = if added == 0 {
                0.0
            } else {
                100.0 * (added.saturating_sub(in_ex.min(added)) as f64) / (added as f64)
            };
            let untouched_pr = if added == 0 {
                0.0
            } else {
                100.0 * (added.saturating_sub(reach.min(added)) as f64) / (added as f64)
            };
            let total_ns = sat_ns + ext_ns;
            let sat_pct = if total_ns == 0 {
                0.0
            } else {
                100.0 * (sat_ns as f64) / (total_ns as f64)
            };
            println!(
                "{:<10} {:>10} {:>11} {:>8.1}% {:>10} {:>8.1}% {:>11} {:>8.1}% {:>5}/{:<4}",
                name,
                added,
                in_ex,
                untouched_kb,
                reach,
                untouched_pr,
                prod_chkd,
                sat_pct,
                roots,
                nf
            );
            assert!(reach >= in_ex, "amb: prod reach ⊇ 1-best touched");
            if added > 0 {
                assert!(
                    prod_chkd <= reach,
                    "amb: collect_checked marked ({prod_chkd}) ⊆ reachable ({reach})"
                );
            }
        }
        println!(
            "GATE (DV-0′): DV-1 iff PRODUCTION untch_pr% ≥ 50% AND sat ≥ 20% of eval wall.\n\
             The 1-best untch_kb% is the INFLATED legacy measure (kth early-stop).\n\
             Production extraction = constant-zero weight + collect_checked (full stream)\n\
             ⇒ untouched = NOT-root-reachable. See /tmp/p6_probes/findings.md.\n"
        );
    }
}

#[cfg(test)]
#[path = "../tests/support/pattern_lifecycle_recursive_oracle.rs"]
mod pattern_lifecycle_recursive_oracle;

#[cfg(test)]
#[path = "../tests/support/rules_instantiation_recursive_oracle.rs"]
mod instantiation_recursive_oracle;

#[cfg(test)]
#[path = "../tests/support/rules_matching_recursive_oracle.rs"]
mod matching_recursive_oracle;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraphConfig;

    #[test]
    fn search_finds_matches() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let _fa = eg.add(ENode::new("f".into(), vec![a]));
        let pat = Pattern::app("f".to_string(), vec![Pattern::var("x")]);
        let matches = eg.search(&pat);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].1.get("x"), Some(&eg.find(a)));
    }

    #[test]
    fn search_many_structural_scans_multiple_patterns() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let b = eg.add(ENode::leaf("b".into()));
        let _fa = eg.add(ENode::new("f".into(), vec![a]));
        let _gb = eg.add(ENode::new("g".into(), vec![b]));

        let run = eg
            .search_many_structural([
                (PatternId(10), Pattern::app("f".to_string(), vec![Pattern::var("x")])),
                (PatternId(11), Pattern::app("g".to_string(), vec![Pattern::var("y")])),
            ])
            .expect("positional patterns compile");

        assert_eq!(run.matches.len(), 2);
        assert!(run
            .matches
            .iter()
            .any(|m| { m.pattern == PatternId(10) && m.subst.get("x") == Some(&eg.find(a)) }));
        assert!(run
            .matches
            .iter()
            .any(|m| { m.pattern == PatternId(11) && m.subst.get("y") == Some(&eg.find(b)) }));
        assert_eq!(run.stats.root_classes, 4);
        assert_eq!(run.stats.candidate_evaluations, 2);
    }

    #[test]
    fn search_many_structural_rejects_ac_patterns() {
        let eg = EGraph::<String>::new();
        let err = eg
            .search_many_structural([(
                PatternId(3),
                Pattern::ac("par".to_string(), vec![Pattern::var("x")], Some("rest".into())),
            )])
            .expect_err("AC patterns must stay on lazy budget-aware search");

        assert_eq!(err.unsupported_patterns(), &[PatternId(3)]);
    }

    #[test]
    fn saturate_simple_rewrite_to_fixpoint() {
        // f(x) -> x. Seed f(a). After saturation: f(a) ~ a.
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let fa = eg.add(ENode::new("f".into(), vec![a]));
        let rule = RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::var("x"),
            label: Some("unwrap_f".into()),
        };
        let rep = eg.saturate(&[rule], 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged, "reaches a fixpoint");
        assert_eq!(rep.rule_firings, vec![RuleFiring { label: Some("unwrap_f".into()), count: 1 }]);
        assert!(eg.equiv(fa, a), "f(a) ~ a after saturation");
    }

    #[test]
    fn compiled_rule_set_reuses_positional_automata_across_graphs() {
        fn seed_graph() -> (EGraph<String>, EClassId, EClassId) {
            let mut eg = EGraph::<String>::new();
            let a = eg.add(ENode::leaf("a".into()));
            let fa = eg.add(ENode::new("f".into(), vec![a]));
            (eg, a, fa)
        }

        let rules = vec![RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::var("x"),
            label: Some("unwrap_f".into()),
        }];
        let compiled = CompiledRuleSet::from_rewrites(rules.clone());
        assert_eq!(compiled.structural_segment_count(), 1);
        assert_eq!(compiled.native_segment_count(), 0);

        let (mut legacy, legacy_a, legacy_fa) = seed_graph();
        let legacy_report = legacy.saturate(&rules, 20);
        assert!(legacy.equiv(legacy_fa, legacy_a));

        let (mut compiled_first, first_a, first_fa) = seed_graph();
        let first_report = compiled_first.saturate_compiled(&compiled, 20);
        assert_eq!(first_report, legacy_report);
        assert!(compiled_first.equiv(first_fa, first_a));

        let (mut compiled_second, second_a, second_fa) = seed_graph();
        let second_report = compiled_second.saturate_compiled(&compiled, 20);
        assert_eq!(second_report, legacy_report);
        assert!(compiled_second.equiv(second_fa, second_a));
    }

    #[test]
    fn saturate_congruence_via_rule() {
        // a -> b, and f(a), f(b): after a~b, congruence gives f(a)~f(b).
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let b = eg.add(ENode::leaf("b".into()));
        let fa = eg.add(ENode::new("f".into(), vec![a]));
        let fb = eg.add(ENode::new("f".into(), vec![b]));
        let rule = RewriteRule {
            lhs: Pattern::leaf("a".to_string()),
            rhs: Pattern::leaf("b".to_string()),
            label: None,
        };
        let rep = eg.saturate(&[rule], 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged);
        assert_eq!(rep.rule_firings, vec![RuleFiring { label: None, count: 1 }]);
        assert!(eg.equiv(a, b));
        assert!(eg.equiv(fa, fb), "congruence: f(a) ~ f(b) after a ~ b");
    }

    #[test]
    fn batched_structural_segment_preserves_same_iteration_rebuild_visibility() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let b = eg.add(ENode::leaf("b".into()));
        let c = eg.add(ENode::leaf("c".into()));
        let fa = eg.add(ENode::new("f".into(), vec![a]));

        let rules = vec![
            RewriteRule {
                lhs: Pattern::leaf("a".to_string()),
                rhs: Pattern::leaf("b".to_string()),
                label: Some("a_to_b".into()),
            },
            RewriteRule {
                lhs: Pattern::app("f".to_string(), vec![Pattern::leaf("b".to_string())]),
                rhs: Pattern::leaf("c".to_string()),
                label: Some("fb_to_c".into()),
            },
        ];

        let rep = eg.saturate(&rules, 1);

        assert_eq!(rep.outcome, SaturationOutcome::IterationLimit);
        assert_eq!(
            rep.rule_firings,
            vec![
                RuleFiring { label: Some("a_to_b".into()), count: 1 },
                RuleFiring { label: Some("fb_to_c".into()), count: 1 },
            ]
        );
        assert!(eg.equiv(a, b));
        assert!(eg.equiv(fa, c));
    }

    #[test]
    fn saturation_stats_record_set_automaton_batches_and_invalidations() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let _b = eg.add(ENode::leaf("b".into()));
        let c = eg.add(ENode::leaf("c".into()));
        let fa = eg.add(ENode::new("f".into(), vec![a]));

        let rules = vec![
            RewriteRule {
                lhs: Pattern::leaf("a".to_string()),
                rhs: Pattern::leaf("b".to_string()),
                label: Some("a_to_b".into()),
            },
            RewriteRule {
                lhs: Pattern::app("f".to_string(), vec![Pattern::leaf("b".to_string())]),
                rhs: Pattern::leaf("c".to_string()),
                label: Some("fb_to_c".into()),
            },
        ];

        let rep = eg.saturate(&rules, 1);

        assert_eq!(rep.outcome, SaturationOutcome::IterationLimit);
        assert!(eg.equiv(fa, c), "invalidated batches must rescan later rules");
        assert_eq!(rep.stats.set_automaton_batches, 1);
        assert_eq!(rep.stats.set_automaton_batch_invalidations, 1);
        assert_eq!(rep.stats.rule_searches, 1);
        assert_eq!(rep.stats.ac_fallback_searches, 0);
        assert!(rep.stats.set_automaton_scans >= 2);
        assert!(rep.stats.set_automaton_root_classes > 0);
        assert!(rep.stats.set_automaton_root_nodes > 0);
        assert!(rep.stats.set_automaton_candidate_evaluations > 0);
        assert!(rep.stats.set_automaton_state_evaluations > 0);
    }

    #[test]
    fn saturation_stats_record_ac_fallback_searches() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let b = eg.add(ENode::leaf("b".into()));
        let par = eg.add(ENode::new("par".into(), vec![a, b]));
        let rules = vec![RewriteRule {
            lhs: Pattern::ac("par".to_string(), vec![Pattern::var("x")], None),
            rhs: Pattern::var("x"),
            label: Some("select_par_child".into()),
        }];

        let rep = eg.saturate(&rules, 1);

        assert_eq!(rep.outcome, SaturationOutcome::IterationLimit);
        assert!(eg.equiv(par, a) || eg.equiv(par, b));
        assert_eq!(rep.stats.set_automaton_batches, 0);
        assert_eq!(rep.stats.set_automaton_scans, 0);
        assert_eq!(rep.stats.rule_searches, 1);
        assert_eq!(rep.stats.ac_fallback_searches, 1);
    }

    #[test]
    fn native_rule_computes_result_and_converges() {
        // `double(a) ~> ⟨native: add(x, x)⟩`. The native dispatcher reads the
        // matched child class `x` from the substitution and ADDS `add(x, x)`,
        // which saturation merges with the redex. After the fixpoint,
        // `double(a) == add(a, a)` — the fold fragment reducing inside saturation.
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let dbl = eg.add(ENode::new("double".into(), vec![a]));
        let native = vec![NativeRule {
            lhs: Pattern::app("double".to_string(), vec![Pattern::var("x")]),
            op: 0,
            label: Some("double".into()),
        }];
        let dispatch =
            |_op: NativeOpId, eg: &mut EGraph<String>, subst: &Subst| -> Option<EClassId> {
                let x = eg.find(*subst.get("x")?);
                Some(eg.add(ENode::new("add".into(), vec![x, x])))
            };
        let rep = eg.saturate_with_native(&[], &native, &dispatch, 20);
        assert_eq!(
            rep.outcome,
            SaturationOutcome::Converged,
            "native saturation reaches a fixpoint"
        );
        assert_eq!(rep.rule_firings, vec![RuleFiring { label: Some("double".into()), count: 1 }]);
        let add_aa = eg.add(ENode::new("add".into(), vec![a, a]));
        assert!(eg.equiv(dbl, add_aa), "double(a) == add(a, a) after the native rule fires");
    }

    #[test]
    fn batched_native_segment_preserves_same_iteration_rebuild_visibility() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let b = eg.add(ENode::leaf("b".into()));
        let c = eg.add(ENode::leaf("c".into()));
        let fa = eg.add(ENode::new("f".into(), vec![a]));

        let native = vec![
            NativeRule {
                lhs: Pattern::leaf("a".to_string()),
                op: 1,
                label: Some("native_a_to_b".into()),
            },
            NativeRule {
                lhs: Pattern::app("f".to_string(), vec![Pattern::leaf("b".to_string())]),
                op: 2,
                label: Some("native_fb_to_c".into()),
            },
        ];
        let dispatch = |op: NativeOpId, _eg: &mut EGraph<String>, _subst: &Subst| match op {
            1 => Some(b),
            2 => Some(c),
            _ => None,
        };

        let rep = eg.saturate_with_native(&[], &native, &dispatch, 1);

        assert_eq!(rep.outcome, SaturationOutcome::IterationLimit);
        assert_eq!(
            rep.rule_firings,
            vec![
                RuleFiring {
                    label: Some("native_a_to_b".into()),
                    count: 1
                },
                RuleFiring {
                    label: Some("native_fb_to_c".into()),
                    count: 1
                },
            ]
        );
        assert!(eg.equiv(a, b));
        assert!(eg.equiv(fa, c));
    }

    #[test]
    fn native_rule_none_dispatch_is_inert_and_converges() {
        // A native rule whose dispatcher computes nothing (the funded admission
        // failed / a stuck child) leaves the graph unchanged — faithful to a
        // fold premise with no solution. No merge, immediate `Converged`.
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let fa = eg.add(ENode::new("f".into(), vec![a]));
        let native = vec![NativeRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            op: 7,
            label: None,
        }];
        let rep = eg.saturate_with_native(&[], &native, &|_, _, _| None, 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged);
        assert!(rep.rule_firings.is_empty());
        assert!(!eg.equiv(fa, a), "an inert native rule merges nothing");
    }

    #[test]
    fn saturate_delegates_to_native_unchanged() {
        // The structural-only `saturate` still behaves identically after being
        // refactored to delegate to `saturate_with_native` (empty native set,
        // no-op dispatcher) — existing callers are unaffected.
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let fa = eg.add(ENode::new("f".into(), vec![a]));
        let rule = RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::var("x"),
            label: Some("unwrap_f".into()),
        };
        let rep = eg.saturate(&[rule], 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged);
        assert!(eg.equiv(fa, a));
    }

    #[test]
    fn saturate_reports_node_limit_without_overshoot() {
        // f(x) -> f(h(x)) grows UNBOUNDEDLY: each iteration introduces a fresh
        // `h`-nesting depth that cannot collapse (unlike f(x)->f(f(x)), which
        // converges because f(f(a)) = f(class-of-f(a)) dedups). The budget caps
        // the growth and REPORTS it.
        let mut eg = EGraph::<String>::with_config(EGraphConfig { max_nodes: 5 });
        let a = eg.add(ENode::leaf("a".into()));
        let _fa = eg.add(ENode::new("f".into(), vec![a]));
        let rule = RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::app(
                "f".to_string(),
                vec![Pattern::app("h".to_string(), vec![Pattern::var("x")])],
            ),
            label: None,
        };
        let rep = eg.saturate(&[rule], 100);
        assert_eq!(
            rep.outcome,
            SaturationOutcome::NodeLimit,
            "budget overflow REPORTED, not silent"
        );
        assert!(eg.node_count() <= 5, "no overshoot past the budget");
    }

    #[test]
    fn saturate_reports_iteration_limit() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let _fa = eg.add(ENode::new("f".into(), vec![a]));
        let rule = RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::app(
                "f".to_string(),
                vec![Pattern::app("h".to_string(), vec![Pattern::var("x")])],
            ),
            label: None,
        };
        let rep = eg.saturate(&[rule], 1);
        assert_eq!(rep.outcome, SaturationOutcome::IterationLimit);
        assert_eq!(rep.stats.iterations, 1);
        assert!(rep.stats.total_merges > 0);
    }

    #[test]
    fn unbound_rhs_variable_does_not_leave_partial_nodes() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let _fa = eg.add(ENode::new("f".into(), vec![a]));
        let before = eg.node_count();
        let rule = RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::app(
                "pair".to_string(),
                vec![
                    Pattern::app("g".to_string(), vec![Pattern::var("x")]),
                    Pattern::var("missing"),
                ],
            ),
            label: Some("ill_formed_rhs".into()),
        };

        let rep = eg.saturate(&[rule], 10);

        assert_eq!(rep.outcome, SaturationOutcome::Converged);
        assert_eq!(
            eg.node_count(),
            before,
            "unbound RHS variable must reject before adding partial RHS nodes"
        );
    }

    // ════════════════════════════════════════════════════════════════════════
    //  AC (associative-commutative) matching
    // ════════════════════════════════════════════════════════════════════════

    use crate::egraph::EClassId;

    fn ids(xs: &[u32]) -> Vec<EClassId> {
        xs.iter().map(|&x| EClassId(x)).collect()
    }

    #[test]
    fn lazy_ac_select_enumerates_every_size_k_split_once() {
        // bag = [10,11,12], k=2 ⇒ C(3,2)=3 splits, complements correct.
        let bag = ids(&[10, 11, 12]);
        let got: Vec<(Vec<EClassId>, Vec<EClassId>)> = lazy_ac_select(&bag, 2).collect();
        assert_eq!(got.len(), 3, "C(3,2) = 3 size-2 selections");
        let expected = vec![
            (ids(&[10, 11]), ids(&[12])),
            (ids(&[10, 12]), ids(&[11])),
            (ids(&[11, 12]), ids(&[10])),
        ];
        assert_eq!(got, expected, "lexicographic combinations + exact complements");
    }

    #[test]
    fn lazy_ac_select_edge_cases() {
        let bag = ids(&[1, 2, 3]);
        // k = 0: one empty selection, whole bag as complement.
        let k0: Vec<_> = lazy_ac_select(&bag, 0).collect();
        assert_eq!(k0, vec![(ids(&[]), ids(&[1, 2, 3]))]);
        // k = n: one full selection, empty complement.
        let kn: Vec<_> = lazy_ac_select(&bag, 3).collect();
        assert_eq!(kn, vec![(ids(&[1, 2, 3]), ids(&[]))]);
        // k > n: no selections.
        let kbig: Vec<_> = lazy_ac_select(&bag, 4).collect();
        assert!(kbig.is_empty(), "k > n ⇒ no size-k selection");
        // empty bag, k = 0: one empty split.
        let empty: Vec<_> = lazy_ac_select(&[], 0).collect();
        assert_eq!(empty, vec![(ids(&[]), ids(&[]))]);
    }

    #[test]
    fn lazy_ac_select_is_lazy_partial_consumption() {
        // A large bag where the full combination count is astronomical; pulling a
        // few items must be cheap (no eager Vec of all selections). C(40,5) ≈ 658k
        // — we pull only 3. This terminates instantly iff the iterator is lazy.
        let bag: Vec<EClassId> = (0..40).map(EClassId).collect();
        let mut it = lazy_ac_select(&bag, 5);
        let first = it.next().expect("at least one");
        assert_eq!(first.0, ids(&[0, 1, 2, 3, 4]));
        assert_eq!(first.0.len() + first.1.len(), 40, "split partitions the bag");
        let _second = it.next().expect("second");
        let _third = it.next().expect("third");
        // (We never collect the ~658k total — the point is it didn't try to.)
    }

    #[test]
    fn ac_open_rule_single_pairing_reduces() {
        // PPar { open(n,A), n[B] } ~> PPar { A, B }  (no rest).
        // Bag node "par" over [open, amb]; open = open(n, A), amb = amb(n, B).
        // The shared name n is the non-linear constraint (here trivially shared).
        let mut eg = EGraph::<String>::new();
        let n = eg.add(ENode::leaf("n".into()));
        let va = eg.add(ENode::leaf("A".into()));
        let vb = eg.add(ENode::leaf("B".into()));
        let open = eg.add(ENode::new("open".into(), vec![n, va]));
        let amb = eg.add(ENode::new("amb".into(), vec![n, vb]));
        // canonical bag for the par node
        let mut bag = vec![open, amb];
        bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let par = eg.add(ENode::new("par".into(), bag));
        eg.rebuild();

        // OpenRule: par{ open(N,P), amb(N,Q), ...rest } ~> par{ P, Q, ...rest }.
        let rule = RewriteRule {
            lhs: Pattern::ac(
                "par".into(),
                vec![
                    Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
                    Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
                ],
                Some("rest".into()),
            ),
            rhs: Pattern::ac(
                "par".into(),
                vec![Pattern::var("P"), Pattern::var("Q")],
                Some("rest".into()),
            ),
            label: Some("OpenRule".into()),
        };
        let rep = eg.saturate(&[rule], 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged, "reaches a fixpoint");

        // The result bag par{A, B} must exist and be equivalent to the redex.
        let mut result_bag = vec![eg.find(va), eg.find(vb)];
        result_bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let expected = eg.add(ENode::new("par".into(), result_bag));
        assert!(eg.equiv(par, expected), "open(n,A) | n[B] ~> A | B");
    }

    #[test]
    fn ac_rest_complement_survives_between_positional_batches() {
        let mut eg = EGraph::<String>::new();
        let n = eg.add(ENode::leaf("n".into()));
        let va = eg.add(ENode::leaf("A".into()));
        let vb = eg.add(ENode::leaf("B".into()));
        let vc = eg.add(ENode::leaf("C".into()));
        let vd = eg.add(ENode::leaf("D".into()));
        let seed = eg.add(ENode::leaf("seed".into()));
        let seed_norm = eg.add(ENode::leaf("seed_norm".into()));
        let observed = eg.add(ENode::leaf("observed_open".into()));
        let open = eg.add(ENode::new("open".into(), vec![n, va]));
        let amb = eg.add(ENode::new("amb".into(), vec![n, vb]));
        let mut bag = vec![open, amb, vc, vd];
        bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let par = eg.add(ENode::new("par".into(), bag));
        eg.rebuild();

        let rules = vec![
            RewriteRule {
                lhs: Pattern::leaf("seed".to_string()),
                rhs: Pattern::leaf("seed_norm".to_string()),
                label: Some("seed_norm".into()),
            },
            RewriteRule {
                lhs: Pattern::ac(
                    "par".into(),
                    vec![
                        Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
                        Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
                    ],
                    Some("rest".into()),
                ),
                rhs: Pattern::app(
                    "opened".into(),
                    vec![Pattern::var("P"), Pattern::var("Q"), Pattern::var("rest")],
                ),
                label: Some("open_with_rest".into()),
            },
            RewriteRule {
                lhs: Pattern::app(
                    "opened".into(),
                    vec![Pattern::var("P"), Pattern::var("Q"), Pattern::var("R")],
                ),
                rhs: Pattern::leaf("observed_open".to_string()),
                label: Some("observed_open".into()),
            },
        ];

        let rep = eg.saturate(&rules, 1);

        assert_eq!(rep.outcome, SaturationOutcome::IterationLimit);
        assert_eq!(
            rep.rule_firings,
            vec![
                RuleFiring {
                    label: Some("seed_norm".into()),
                    count: 1
                },
                RuleFiring {
                    label: Some("open_with_rest".into()),
                    count: 1
                },
                RuleFiring {
                    label: Some("observed_open".into()),
                    count: 1
                },
            ]
        );
        assert!(eg.equiv(seed, seed_norm));
        assert!(eg.equiv(par, observed), "post-AC positional batch must observe opened node");

        let mut rest = vec![eg.find(vc), eg.find(vd)];
        rest.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let rest_bag = eg.add(ENode::new("par".into(), rest));
        let expected_opened = eg.add(ENode::new("opened".into(), vec![va, vb, rest_bag]));
        assert!(
            eg.equiv(par, expected_opened),
            "AC rest must materialize the exact complement par{{C,D}}"
        );
        assert_eq!(rep.stats.rule_searches, 1);
        assert_eq!(rep.stats.ac_fallback_searches, 1);
        assert!(rep.stats.set_automaton_batches >= 2);
    }

    #[test]
    fn ac_rest_complement_budget_refusal_reports_node_limit() {
        let mut eg = EGraph::<String>::with_config(EGraphConfig { max_nodes: 1 });
        let n = eg.add(ENode::leaf("n".into()));
        let va = eg.add(ENode::leaf("A".into()));
        let vb = eg.add(ENode::leaf("B".into()));
        let vc = eg.add(ENode::leaf("C".into()));
        let vd = eg.add(ENode::leaf("D".into()));
        let open = eg.add(ENode::new("open".into(), vec![n, va]));
        let amb = eg.add(ENode::new("amb".into(), vec![n, vb]));
        let mut bag = vec![open, amb, vc, vd];
        bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let _par = eg.add(ENode::new("par".into(), bag));
        eg.rebuild();

        let rule = RewriteRule {
            lhs: Pattern::ac(
                "par".into(),
                vec![
                    Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
                    Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
                ],
                Some("rest".into()),
            ),
            rhs: Pattern::app(
                "opened".into(),
                vec![Pattern::var("P"), Pattern::var("Q"), Pattern::var("rest")],
            ),
            label: Some("open_with_rest".into()),
        };

        let rep = eg.saturate(&[rule], 20);

        assert_eq!(rep.outcome, SaturationOutcome::NodeLimit);
        assert!(eg.node_limit_reached());
        assert!(rep.rule_firings.is_empty());
        assert_eq!(rep.stats.rule_searches, 1);
        assert_eq!(rep.stats.ac_fallback_searches, 1);
        assert_eq!(rep.stats.set_automaton_batches, 0);
    }

    #[test]
    fn ac_open_rule_shared_name_constraint_prunes_mismatch() {
        // par { open(n, A), m[B] } with n ≠ m: the shared-name N constraint is
        // UNSATISFIABLE (open's name n must equal amb's name, but the only ambient
        // has name m). No reduction must fire.
        let mut eg = EGraph::<String>::new();
        let n = eg.add(ENode::leaf("n".into()));
        let m = eg.add(ENode::leaf("m".into()));
        let va = eg.add(ENode::leaf("A".into()));
        let vb = eg.add(ENode::leaf("B".into()));
        let open = eg.add(ENode::new("open".into(), vec![n, va]));
        let amb = eg.add(ENode::new("amb".into(), vec![m, vb]));
        let mut bag = vec![open, amb];
        bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let par = eg.add(ENode::new("par".into(), bag));
        eg.rebuild();
        let before = eg.node_count();

        let rule = RewriteRule {
            lhs: Pattern::ac(
                "par".into(),
                vec![
                    Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
                    Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
                ],
                Some("rest".into()),
            ),
            rhs: Pattern::ac(
                "par".into(),
                vec![Pattern::var("P"), Pattern::var("Q")],
                Some("rest".into()),
            ),
            label: Some("OpenRule".into()),
        };
        let rep = eg.saturate(&[rule], 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged);
        // par{A,B} must NOT have been produced (the name constraint refutes the
        // only candidate pairing).
        let expected_children = {
            let mut c = vec![eg.find(va), eg.find(vb)];
            c.sort_by_cached_key(|&a| eg.canonical_class_key(a));
            c
        };
        // node_count must be unchanged (no complement/result nodes added) and the
        // would-be result is not equivalent to the redex.
        assert_eq!(eg.node_count(), before, "no AC reduction fired for n ≠ m");
        // (Adding the would-be result now is a fresh node, so it cannot be
        // equivalent to `par` unless the rule had fired.)
        let expected = eg.add(ENode::new("par".into(), expected_children));
        assert!(!eg.equiv(par, expected), "n ≠ m: open|amb must not reduce");
    }

    #[test]
    fn ac_open_rule_flattens_nested_ambient_body() {
        // Associativity: open(n, A) | n[ B | C ] ~> A | B | C  (ONE flat bag),
        // NOT A | (B | C) (a bag-of-bags). The ambient body is itself a `par`
        // bag, so opening it must SPLICE its members into the surrounding
        // parallel — the associative half of AC. Without `add_flattened_bag`
        // the redex would instead reduce to the nested `par{A, par{B,C}}`.
        let mut eg = EGraph::<String>::new();
        let n = eg.add(ENode::leaf("n".into()));
        let va = eg.add(ENode::leaf("A".into()));
        let vb = eg.add(ENode::leaf("B".into()));
        let vc = eg.add(ENode::leaf("C".into()));
        // The ambient body is itself a `par` bag { B, C }.
        let mut body_bag = vec![vb, vc];
        body_bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let body = eg.add(ENode::new("par".into(), body_bag));
        let open = eg.add(ENode::new("open".into(), vec![n, va]));
        let amb = eg.add(ENode::new("amb".into(), vec![n, body]));
        let mut bag = vec![open, amb];
        bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let par = eg.add(ENode::new("par".into(), bag));
        eg.rebuild();

        let rule = RewriteRule {
            lhs: Pattern::ac(
                "par".into(),
                vec![
                    Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
                    Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
                ],
                Some("rest".into()),
            ),
            rhs: Pattern::ac(
                "par".into(),
                vec![Pattern::var("P"), Pattern::var("Q")],
                Some("rest".into()),
            ),
            label: Some("OpenRule".into()),
        };
        let rep = eg.saturate(&[rule], 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged);

        // The FLAT result par{A, B, C} must be equivalent to the redex.
        let mut flat = vec![eg.find(va), eg.find(vb), eg.find(vc)];
        flat.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let expected_flat = eg.add(ENode::new("par".into(), flat));
        assert!(eg.equiv(par, expected_flat), "open(n,A) | n[B|C] ~> A | B | C (one flat bag)");

        // The NESTED bag-of-bags par{A, par{B,C}} must NOT be the result: it has
        // a distinct canonical key, so associativity must have flattened it away.
        let mut nested = vec![eg.find(va), eg.find(body)];
        nested.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let nested_node = eg.add(ENode::new("par".into(), nested));
        assert!(
            !eg.equiv(par, nested_node),
            "the result must be flat, never a nested bag-of-bags"
        );
    }

    #[test]
    fn ac_nonlinear_native_rule_records_one_justification_with_shared_sigma() {
        // (A-2 — closes Blocker 2) The FIRST NON-LINEAR AC NATIVE firing:
        //     par{ open(N,P), amb(N,Q), ...rest }  ~>  ⟨native reduct⟩
        // where the channel metavariable `N` occurs in BOTH structured elements. The two
        // `N` occurrences hashcons to ONE e-class (`amb`/`open` share the leaf `n`), so
        // `collect_ac_matches` (rules.rs) finds the match — the non-linear `Var` re-bind
        // check in `collect_matches` succeeds by e-class equality — and
        // `apply_native_matches` records EXACTLY ONE `RewriteJustification` whose σ binds
        // `N` to the shared class and `rest` to the multiset complement. This is the exact
        // mechanism the CommDemo Comm rule rides (its `(PFor N cont)`/`(POutput N Q)`
        // elements share the channel `N`).
        let mut eg = EGraph::<String>::new();
        let n = eg.add(ENode::leaf("n".into()));
        let va = eg.add(ENode::leaf("A".into()));
        let vb = eg.add(ENode::leaf("B".into()));
        let extra = eg.add(ENode::leaf("E".into()));
        let open = eg.add(ENode::new("open".into(), vec![n, va]));
        let amb = eg.add(ENode::new("amb".into(), vec![n, vb])); // SAME `n` → one class
        let mut bag = vec![open, amb, extra];
        bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let _par = eg.add(ENode::new("par".into(), bag));
        eg.rebuild();

        // A native AcApp rule: its dispatch computes a fresh reduct and returns it (a net
        // change → the firing is recorded), mirroring the Comm dispatch's compute-and-splice.
        let native = vec![NativeRule {
            lhs: Pattern::ac(
                "par".into(),
                vec![
                    Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
                    Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
                ],
                Some("rest".into()),
            ),
            op: 0,
            label: Some("NlComm".into()),
        }];
        let dispatch =
            |_op: NativeOpId, eg: &mut EGraph<String>, subst: &Subst| -> Option<EClassId> {
                // The non-linear channel var + rest are bound by the match (else no firing).
                let _n = *subst.get("N")?;
                let _rest = *subst.get("rest")?;
                Some(eg.add(ENode::leaf("reduct".into())))
            };
        let rep = eg.saturate_with_native(&[], &native, &dispatch, 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged);

        // EXACTLY ONE justification — the non-linear native AcApp fired once and recorded σ.
        assert_eq!(
            rep.rewrite_justifications.len(),
            1,
            "one non-linear native AC firing must be recorded, got {:?}",
            rep.rewrite_justifications
        );
        let j = &rep.rewrite_justifications[0];
        assert_eq!(j.rule_label.as_deref(), Some("NlComm"));
        // σ binds the shared `N` to the single shared channel class (the non-linear guard
        // held by e-class equality), plus the element bodies and the complement `rest`.
        assert_eq!(
            eg.find(j.subst["N"]),
            eg.find(n),
            "N is bound to the single shared channel class"
        );
        assert!(j.subst.contains_key("P"), "the open body P is bound");
        assert!(j.subst.contains_key("Q"), "the amb body Q is bound");
        assert!(j.subst.contains_key("rest"), "the complement `rest` is bound");
    }

    #[test]
    fn ac_nonlinear_native_rule_vetoes_mismatched_shared_var() {
        // (A-2 negative) par{ open(n,A), amb(m,B) } with n ≠ m: the shared-channel
        // constraint is UNSATISFIABLE, so `collect_ac_matches` finds NO pairing (the
        // non-linear `Var` re-bind check refutes `find(n) == find(m)`), and
        // `apply_native_matches` records NO justification — the Dovetail-level analogue of
        // the Comm receiver's non-linear `Receive.condition` vetoing a mismatched-channel
        // soup.
        let mut eg = EGraph::<String>::new();
        let n = eg.add(ENode::leaf("n".into()));
        let m = eg.add(ENode::leaf("m".into()));
        let va = eg.add(ENode::leaf("A".into()));
        let vb = eg.add(ENode::leaf("B".into()));
        let open = eg.add(ENode::new("open".into(), vec![n, va]));
        let amb = eg.add(ENode::new("amb".into(), vec![m, vb])); // DIFFERENT channel
        let mut bag = vec![open, amb];
        bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let _par = eg.add(ENode::new("par".into(), bag));
        eg.rebuild();

        let native = vec![NativeRule {
            lhs: Pattern::ac(
                "par".into(),
                vec![
                    Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
                    Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
                ],
                Some("rest".into()),
            ),
            op: 0,
            label: Some("NlComm".into()),
        }];
        let dispatch = |_op: NativeOpId,
                        eg: &mut EGraph<String>,
                        _subst: &Subst|
         -> Option<EClassId> { Some(eg.add(ENode::leaf("reduct".into()))) };
        let rep = eg.saturate_with_native(&[], &native, &dispatch, 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged);
        assert!(
            rep.rewrite_justifications.is_empty(),
            "a mismatched-channel soup must record NO firing (non-linear veto), got {:?}",
            rep.rewrite_justifications
        );
    }
}
