//! Bisimulation by partition refinement over a behavioral LTS — the compile-time
//! layer of the Heyting-SFA bisimulation (plan Pillar 2′ / heyting-algebra-
//! extensions.md §10.7).
//!
//! The proven Comm-reduction relation (`CommReductionCorrespondence.v`) is a
//! labeled transition system: states are processes, actions are the
//! **regularized (¬¬) minterm classes** of a `ProcessActionAlgebra` (the action
//! alphabet, decided exactly on the regular Boolean core `H_reg` of
//! [`crate::algebra_tower`]'s Heyting algebra). Two states are *bisimilar* when
//! each can match the other's labeled transitions and the targets stay related.
//!
//! This module computes the **coarsest bisimulation refining an initial coloring**
//! by signature refinement (Kanellakis–Smolka / Paige–Tarjan): repeatedly split
//! a block whenever two of its states reach *different* sets of blocks under some
//! action, until the partition is stable. The result is:
//!   - **sound** — [`Lts::is_bisimulation`] verifies the returned partition is a
//!     bisimulation (matching transitions both ways, same initial color);
//!   - **coarsest** — refinement only ever splits, so the fixpoint merges every
//!     pair of behaviorally indistinguishable states.
//!
//! This is the exact (clopen / regular) compile-time layer. Boundary gaps on the
//! semi-decidable behavioral leg (the `¬¬φ ∖ φ` region, where an action class is
//! `Sat3::DontKnow`) are closed at runtime by the Ascent `eqrel` congruence
//! fixpoint — the three-layer algorithm of §10.7. This module owns the first,
//! sound-at-compile-time layer; it never *merges* across a DontKnow boundary (it
//! only splits on confirmed action classes), so its partition is always a sound
//! under-approximation of full bisimilarity, refined (never coarsened) by the
//! runtime congruence closure.

use std::collections::BTreeMap;

/// An action label — a regularized minterm class of the process-action algebra.
pub type Action = u32;

/// A finite labeled transition system over states `0..num_states`.
#[derive(Clone, Debug, Default)]
pub struct Lts {
    /// Number of states (states are `0..num_states`).
    pub num_states: usize,
    /// Labeled transitions `(from, action, to)`.
    pub transitions: Vec<(usize, Action, usize)>,
}

impl Lts {
    /// Build an LTS over `num_states` with the given labeled transitions.
    pub fn new(num_states: usize, transitions: Vec<(usize, Action, usize)>) -> Self {
        Self { num_states, transitions }
    }

    /// Per-state outgoing adjacency `(action, target)`.
    fn adjacency(&self) -> Vec<Vec<(Action, usize)>> {
        let mut adj = vec![Vec::new(); self.num_states];
        for &(from, a, to) in &self.transitions {
            if from < self.num_states && to < self.num_states {
                adj[from].push((a, to));
            }
        }
        adj
    }

    /// One refinement step: a new block id per state, grouping states by their
    /// current block plus the *set* of `(action, target-block)` they reach.
    fn refine_once(block: &[usize], adj: &[Vec<(Action, usize)>]) -> Vec<usize> {
        let n = block.len();
        let mut signatures: Vec<(usize, Vec<(Action, usize)>)> = Vec::with_capacity(n);
        for s in 0..n {
            let mut sig: Vec<(Action, usize)> =
                adj[s].iter().map(|&(a, t)| (a, block[t])).collect();
            sig.sort_unstable();
            sig.dedup();
            signatures.push((block[s], sig));
        }
        let mut ids: BTreeMap<(usize, Vec<(Action, usize)>), usize> = BTreeMap::new();
        let mut next = vec![0usize; n];
        for (s, sig) in signatures.into_iter().enumerate() {
            let fresh = ids.len();
            next[s] = *ids.entry(sig).or_insert(fresh);
        }
        next
    }

    /// The number of distinct blocks in a partition.
    fn block_count(block: &[usize]) -> usize {
        let mut seen: BTreeMap<usize, ()> = BTreeMap::new();
        for &b in block {
            seen.insert(b, ());
        }
        seen.len()
    }

    /// The coarsest bisimulation refining `initial_colors` (one color per state):
    /// returns `block_of`, mapping each state to its bisimulation block id.
    ///
    /// Refinement only splits, so the block count is non-decreasing and bounded
    /// by `num_states`; the fixpoint is reached when a step adds no new block.
    pub fn bisimulation(&self, initial_colors: &[usize]) -> Vec<usize> {
        assert_eq!(
            initial_colors.len(),
            self.num_states,
            "initial coloring must assign one color per state"
        );
        let adj = self.adjacency();
        // Normalize the initial coloring to dense block ids.
        let mut block = Self::refine_once(initial_colors, &vec![Vec::new(); self.num_states]);
        // Re-seed with the colors actually folded in (refine_once above used empty
        // adjacency, so it grouped purely by color — exactly the normalized seed).
        loop {
            let refined = Self::refine_once(&block, &adj);
            if Self::block_count(&refined) == Self::block_count(&block) {
                return refined;
            }
            block = refined;
        }
    }

    /// Verify that `block_of` is a bisimulation w.r.t. `colors`: states in the
    /// same block share a color, and each matches the other's labeled
    /// transitions up to the partition (a sound checker, used to certify
    /// [`bisimulation`](Self::bisimulation)).
    pub fn is_bisimulation(&self, block_of: &[usize], colors: &[usize]) -> bool {
        let adj = self.adjacency();
        let n = self.num_states;
        // `s` can match every transition of `t` up to `block_of`.
        let matches = |s: usize, t: usize| -> bool {
            adj[t].iter().all(|&(a, t2)| {
                adj[s]
                    .iter()
                    .any(|&(a2, s2)| a2 == a && block_of[s2] == block_of[t2])
            })
        };
        for s in 0..n {
            for t in 0..n {
                if block_of[s] == block_of[t] {
                    if colors[s] != colors[t] {
                        return false;
                    }
                    if !matches(s, t) || !matches(t, s) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Whether two states are bisimilar under the coarsest bisimulation that
    /// refines `initial_colors`.
    pub fn bisimilar(&self, s: usize, t: usize, initial_colors: &[usize]) -> bool {
        let block = self.bisimulation(initial_colors);
        block[s] == block[t]
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge (OSLF substrate, Phase 4 — supersedes `alternating` at the
// N06-ISO / A3 codegen seams in `pipeline::analysis`)
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level bisimulation analysis result.
///
/// Shaped **identically** to [`alternating::AlternatingAnalysis`](crate::alternating::AlternatingAnalysis)'s
/// `non_bisimilar_pairs` so this is a drop-in replacement for the alternating
/// bisimulation pass at `.1` (the live flip). The agreement gate
/// (`prattail/tests/bisimulation_agreement_snapshot.rs`) proves the two passes
/// produce the *same* category-pair partition over the corpus fixtures.
#[derive(Debug, Clone)]
pub struct BisimulationAnalysis {
    /// Pairs of categories found non-bisimilar (different bisimulation blocks),
    /// in the same declaration-order pair enumeration `alternating` uses.
    pub non_bisimilar_pairs: Vec<(String, String)>,
}

/// Analyze grammar categories for bisimulation equivalence by partition
/// refinement over a single behavioral [`Lts`].
///
/// This is the [`crate::bisimulation`] counterpart to
/// [`alternating::analyze_from_bundle`](crate::alternating::analyze_from_bundle):
/// it consumes the *same* grammar-bundle inputs (`all_syntax` + `categories`)
/// and returns the *same* `non_bisimilar_pairs` partition, but computes it by the
/// Kanellakis–Smolka / Paige–Tarjan refinement of [`Lts::bisimulation`] over one
/// LTS rather than by the pairwise alternating game.
///
/// # The LTS
///
/// One state per category (each category = a state), indexed by a sorted category
/// list (stable across runs, mirroring `structural_types::category_automaton`),
/// plus a single absorbing `⊥` leaf state. For each grammar rule
/// `(label, cat, items)`:
///   - the rule label is mapped to its **regularized minterm action class** — a
///     stable id derived from the label, decided on the regular Boolean core
///     ([`Sat3::Sat`]/[`Sat3::Unsat`]) by the structural guard analysis
///     ([`crate::symbolic::analyze_from_bundle`]). An action whose class is
///     `Sat3::DontKnow` (the semi-decidable `¬¬φ ∖ φ` boundary region) is
///     **dropped** — the engine never splits on it (the module-header invariant);
///   - for each **nonterminal reference** target category `t` in `items`, a
///     transition `cat --[class]--> t` is emitted; a rule with no nonterminal
///     reference emits `cat --[class]--> ⊥`, so its label action stays observable.
///
/// The action *set* out of a category state is therefore exactly that category's
/// decidable rule-label-class set — the same discriminator the alternating game
/// uses at the root (a rule belongs to exactly one category, so distinct
/// categories with distinct rule labels are split on the first refinement step,
/// while structurally identical categories merge).
///
/// # Soundness certification
///
/// The returned partition is **certified** at runtime: after [`Lts::bisimulation`]
/// the result is checked by [`Lts::is_bisimulation`] via `assert!`, so a partition
/// that is not actually a bisimulation aborts rather than silently mis-reporting.
///
/// # Arguments
///
/// * `all_syntax` — `(rule_label, category, items)` triples from the parser
///   bundle (the same slice `alternating::analyze_from_bundle` consumes).
/// * `categories` — the grammar's [`CategoryInfo`](crate::pipeline::CategoryInfo)
///   list (declaration order is preserved for the output pair enumeration).
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> BisimulationAnalysis {
    use crate::algebra_tower::Sat3;

    if categories.is_empty() {
        return BisimulationAnalysis { non_bisimilar_pairs: Vec::new() };
    }

    // ── State indexing ──────────────────────────────────────────────────────
    // One state per category (stable, sorted — same discipline as
    // `category_automaton`), plus a single absorbing `⊥` leaf whose state id is
    // the last index. A category state holds color 0; `⊥` holds color 1, so a
    // category never merges with the leaf.
    let mut cat_names: Vec<&str> = categories.iter().map(|c| c.name.as_str()).collect();
    cat_names.sort_unstable();
    cat_names.dedup();
    let num_cats = cat_names.len();
    let bottom = num_cats; // the `⊥` leaf state id
    let num_states = num_cats + 1;

    let state_of: BTreeMap<&str, usize> =
        cat_names.iter().enumerate().map(|(i, &c)| (c, i)).collect();

    // ── Regularized minterm action classes (the `¬¬` regular core) ───────────
    // Each rule label is decided on the regular Boolean core by the structural
    // guard analysis: a satisfiable guard is `Sat`, a provably-unsatisfiable one
    // is `Unsat` (both decidable ⇒ kept); there is no semi-decidable
    // `DontKnow` at this compile-time layer, but the boundary rule is enforced
    // so a future behavioral action source cannot leak a `DontKnow` split.
    let symbolic = crate::symbolic::analyze_from_bundle(all_syntax, categories);
    let unsat_labels: std::collections::HashSet<&str> = symbolic
        .unsatisfiable_rule_labels
        .iter()
        .map(|s| s.as_str())
        .collect();

    // The structural guard is classical at this compile-time layer, so every
    // rule label is decidable: `Unsat` iff the analysis flagged it dead (a
    // provably-empty guard), else `Sat`. A genuinely semi-decidable behavioral
    // action source would instead yield `Sat3::DontKnow`, which the action loop
    // below drops (the `¬¬φ ∖ φ` boundary — never split on it).
    let class_of = |label: &str| -> Sat3 {
        match unsat_labels.contains(label) {
            true => Sat3::Unsat,
            false => Sat3::Sat,
        }
    };

    // A stable, label-determined class id: the index of the label in the sorted
    // dedup of all *decidable* rule labels. Label-determined (not
    // category-determined) so two categories sharing a rule label receive the
    // same action class and can merge — exactly the alternating criterion.
    let mut decidable_labels: Vec<&str> = Vec::with_capacity(all_syntax.len());
    for (label, _, _) in all_syntax {
        match class_of(label) {
            Sat3::Sat | Sat3::Unsat => decidable_labels.push(label.as_str()),
            Sat3::DontKnow => {},
        }
    }
    decidable_labels.sort_unstable();
    decidable_labels.dedup();
    let class_id_of: BTreeMap<&str, Action> = decidable_labels
        .iter()
        .enumerate()
        .map(|(i, &l)| (l, i as Action))
        .collect();

    // ── Build the LTS ───────────────────────────────────────────────────────
    // Preallocate: at most one transition per (rule × nonterminal reference),
    // and one per nonterminal-free rule.
    let mut transitions: Vec<(usize, Action, usize)> = Vec::with_capacity(all_syntax.len());
    for (label, cat, items) in all_syntax {
        // Drop any action whose class is not decidable on the regular core.
        let action = match class_of(label) {
            Sat3::Sat | Sat3::Unsat => match class_id_of.get(label.as_str()) {
                Some(&a) => a,
                None => continue,
            },
            Sat3::DontKnow => continue,
        };
        let from = match state_of.get(cat.as_str()) {
            Some(&s) => s,
            // A rule whose owning category is not declared cannot place an
            // observable action on any category state — skip it.
            None => continue,
        };
        // Each nonterminal reference target is a labeled transition. A rule with
        // no nonterminal reference still emits its label action, to `⊥`.
        let mut child_targets: Vec<&str> = Vec::new();
        collect_nonterminal_targets(items, &mut child_targets);
        if child_targets.is_empty() {
            transitions.push((from, action, bottom));
        } else {
            for tgt in child_targets {
                let to = state_of.get(tgt).copied().unwrap_or(bottom);
                transitions.push((from, action, to));
            }
        }
    }

    let lts = Lts::new(num_states, transitions);

    // ── Refine + certify ────────────────────────────────────────────────────
    // Category states share color 0; the `⊥` leaf is color 1 (so a category
    // never merges with the absorbing leaf — the leaf models "no further
    // structure", not "another category").
    let mut colors = vec![0usize; num_states];
    colors[bottom] = 1;
    let block = lts.bisimulation(&colors);
    assert!(
        lts.is_bisimulation(&block, &colors),
        "bisimulation partition refinement produced a non-bisimulation \
         (the soundness checker is the runtime guard for `analyze_from_bundle`)"
    );

    // ── Derive non-bisimilar pairs (declaration order, like `alternating`) ───
    // Two categories are a non-bisimilar pair iff they land in different blocks.
    // Enumerate pairs in `categories` declaration order so the output matches
    // `alternating::analyze_from_bundle`'s pair ordering (a true drop-in).
    let decl_names: Vec<&str> = categories.iter().map(|c| c.name.as_str()).collect();
    let mut non_bisimilar_pairs: Vec<(String, String)> = Vec::new();
    for i in 0..decl_names.len() {
        for j in (i + 1)..decl_names.len() {
            let (ni, nj) = (decl_names[i], decl_names[j]);
            // A category absent from the sorted index (impossible — it was built
            // from the same list) would be treated as its own singleton; guard
            // defensively rather than panic.
            let (bi, bj) = match (state_of.get(ni), state_of.get(nj)) {
                (Some(&a), Some(&b)) => (block[a], block[b]),
                _ => continue,
            };
            if bi != bj {
                non_bisimilar_pairs.push((ni.to_string(), nj.to_string()));
            }
        }
    }

    BisimulationAnalysis { non_bisimilar_pairs }
}

/// Collect the **nonterminal reference** target categories of a rule body, in
/// left-to-right order, descending into the nesting wrappers exactly as the
/// structural-child collectors do (`Optional`/`Sep`/`Map`/`Zip`).
///
/// `NonTerminal` / `Binder` / `Collection` (element category) contribute a
/// target category; `Terminal`, `IdentCapture`, and `BinderCollection`
/// contribute none. Mirrors
/// `structural_types::collect_structural_child_categories` so the LTS edges track
/// the same notion of "structural child" the rest of the substrate uses.
fn collect_nonterminal_targets<'a>(items: &'a [crate::SyntaxItemSpec], out: &mut Vec<&'a str>) {
    use crate::SyntaxItemSpec as Item;
    for item in items {
        match item {
            Item::NonTerminal { category, .. } => out.push(category.as_str()),
            Item::Binder { category, .. } => out.push(category.as_str()),
            Item::Collection { element_category, .. } => out.push(element_category.as_str()),
            Item::Optional { inner } => collect_nonterminal_targets(inner, out),
            Item::Sep { body, .. } => {
                collect_nonterminal_targets(std::slice::from_ref(body.as_ref()), out)
            },
            Item::Map { body_items } => collect_nonterminal_targets(body_items, out),
            Item::Zip { body, .. } => {
                collect_nonterminal_targets(std::slice::from_ref(body.as_ref()), out)
            },
            // Terminal, IdentCapture, BinderCollection — no nonterminal target.
            _ => {},
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // actions
    const A: Action = 0;
    const B: Action = 1;
    const C: Action = 2;

    #[test]
    fn two_copies_of_a_b_are_bisimilar() {
        // r: 0 -a-> 1 -b-> 2(leaf);   q: 3 -a-> 4 -b-> 5(leaf)
        let lts = Lts::new(6, vec![(0, A, 1), (1, B, 2), (3, A, 4), (4, B, 5)]);
        let colors = vec![0; 6];
        let block = lts.bisimulation(&colors);
        // the two roots, the two a-successors, and the two leaves each merge.
        assert_eq!(block[0], block[3], "a.b roots should be bisimilar");
        assert_eq!(block[1], block[4]);
        assert_eq!(block[2], block[5]);
        assert!(lts.is_bisimulation(&block, &colors));
    }

    #[test]
    fn branching_distinguishes_choice_placement() {
        // s: 0 -a-> 1; 1 -b-> 2; 1 -c-> 3            (a.(b+c))
        // t: 4 -a-> 5; 4 -a-> 6; 5 -b-> 7; 6 -c-> 8  (a.b + a.c)
        let lts = Lts::new(
            9,
            vec![(0, A, 1), (1, B, 2), (1, C, 3), (4, A, 5), (4, A, 6), (5, B, 7), (6, C, 8)],
        );
        let colors = vec![0; 9];
        let block = lts.bisimulation(&colors);
        // a.(b+c) is NOT bisimilar to a.b + a.c (classic CCS example).
        assert_ne!(block[0], block[4], "a.(b+c) must differ from a.b+a.c");
        // but all four 0-leaves are bisimilar.
        assert_eq!(block[2], block[3]);
        assert_eq!(block[2], block[7]);
        assert_eq!(block[2], block[8]);
        assert!(lts.is_bisimulation(&block, &colors));
    }

    #[test]
    fn initial_colors_are_respected() {
        // Two leaves with DIFFERENT colors must stay separate (labeled bisim).
        let lts = Lts::new(2, vec![]);
        let colors = vec![0, 1];
        let block = lts.bisimulation(&colors);
        assert_ne!(block[0], block[1], "distinct colors must not merge");
        assert!(lts.is_bisimulation(&block, &colors));
        // Same color ⇒ merge.
        let same = vec![7, 7];
        let block2 = lts.bisimulation(&same);
        assert_eq!(block2[0], block2[1]);
        assert!(lts.is_bisimulation(&block2, &same));
    }

    #[test]
    fn self_loop_bisimilarity() {
        // 0 -a-> 0 and 1 -a-> 1 are bisimilar (both: forever-a).
        let lts = Lts::new(3, vec![(0, A, 0), (1, A, 1), (2, B, 2)]);
        let colors = vec![0; 3];
        let block = lts.bisimulation(&colors);
        assert_eq!(block[0], block[1], "two a-self-loops are bisimilar");
        assert_ne!(block[0], block[2], "a-loop vs b-loop differ");
        assert!(lts.is_bisimulation(&block, &colors));
    }
}
