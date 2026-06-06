//! Valmari's DFA minimization (2012).
//!
//! > Antti Valmari. *Fast brief practical DFA minimization*. Information
//! > Processing Letters 112 (2012) 213–217.
//!
//! Merges equivalent DFA states — states that have the same accept status,
//! weight, alt-accept set, and transition identically on all equivalence
//! classes. This is important for grammars with many operators sharing
//! common prefixes, where minimization merges the shared prefix states.
//!
//! ## Why Valmari (and not Hopcroft)
//!
//! The previous implementation of this module used Hopcroft's algorithm.
//! It was asymptotically correct (O(n·|Σ|·log n)) but had a pathological
//! implementation shape that consumed 32+ GB of proc-macro RSS on
//! Calculator's 284-state / 60-class lexer DFA — chiefly due to
//! per-worklist-pop rescans of entire state blocks and an O(n·|Σ|)
//! state×class bitset. Rather than patch the symptoms we replaced the
//! algorithm with Valmari (2012), which has the same asymptotic bound
//! but a much friendlier constant and, crucially, drives refinement
//! from **transitions** (cords) rather than state-block/class pairs.
//! Per-transition amortized work is O(log |T|), and memory is O(n + |T|)
//! with no nested `Vec<Vec<...>>` structures.
//!
//! ## Algorithm overview (what the paper calls "refinement of two partitions")
//!
//! - **P** — a partition over states. Initialized by grouping states with
//!   identical accept-behavior (accept token + weight + alt-accepts set).
//! - **C** — a partition over transitions (cords). Initialized by grouping
//!   transitions by their `label` (equivalence class).
//!
//! Valmari's §2 (Fig. 6) dual-cursor driver walks the partitions with two
//! monotonically-increasing indices:
//!
//! ```text
//! b = 1; c = 0
//! while c < C.count:
//!     mark sources of cords in C-block c, split P, c += 1
//!     while b < P.count:
//!         mark incoming cords of P-block b, split C, b += 1
//! ```
//!
//! The cursors never retreat. Convergence is guaranteed by a single
//! property maintained in [`IndexedPartition::split`]: **the freshly
//! allocated id is always given to the smaller half**. When a block
//! below the cursor is split, the larger half keeps its old id (already
//! processed; re-processing would be redundant) while the smaller half
//! lands at `set_count - 1`, strictly ahead of the cursor — guaranteed
//! to be revisited exactly once. This is Valmari's §4 simplification
//! relative to Hopcroft: *no worklist, no dedup bitset, no per-pop
//! book-keeping*.
//!
//! The [`IndexedPartition`] type below implements both P and C with the
//! classical Valmari array layout (`elements`, `location`, `set_of`,
//! `first`, `past`, `marked_count`, `touched`) where every field is
//! `Vec<u32>` for cache locality. Splits are O(|marked|) — they never
//! touch unmarked elements of a block.
//!
//! ## Memory profile on Calculator (previous pathological case)
//!
//! - States: 284 → `IndexedPartition` size ≈ 284 × 4 = 1.1 KB per field,
//!   ~7 fields → ~8 KB total.
//! - Transitions: ≤ 284 × 60 = 17 040 → ~60 KB per field, ~7 fields → ~400 KB.
//! - Inverse CSR (head + next): ~2 × 17 040 × 4 = 136 KB.
//!
//! Total working set is comfortably under 1 MB. The old 32 GB peak is gone.

use std::cell::Cell;

use super::{ClassId, Dfa, DfaState, StateId, DEAD_STATE};
use std::collections::BTreeMap;

thread_local! {
    /// Reusable buffer of `StateId`s marked during a refinement step.
    /// Drained per iteration — retained only to avoid re-allocating.
    static MARK_STATES: Cell<Vec<StateId>> = const { Cell::new(Vec::new()) };
}

/// Valmari's "refinable partition" over `0..size` elements.
///
/// All fields are `Vec<u32>` for cache locality — on our workloads the
/// element count is small (≤ 300 states, ≤ 20 K transitions), `u32` is
/// more than enough and halves memory vs. `Vec<usize>`.
///
/// Members of block `b` occupy the contiguous slice
/// `elements[first[b] .. past[b]]`. `location[e]` is the index of
/// element `e` inside `elements`. Marked elements in a block are kept
/// as a prefix, counted by `marked[b]`. `set_of[e]` is the current
/// block id of element `e`. `set_count` is the number of live blocks
/// (blocks are never removed — only added via `split()`).
struct IndexedPartition {
    elements: Vec<u32>,
    location: Vec<u32>,
    set_of: Vec<u32>,
    first: Vec<u32>,
    past: Vec<u32>,
    marked: Vec<u32>,
    /// Blocks that currently contain at least one marked element. Cleared
    /// at the end of each `split()` call.
    touched: Vec<u32>,
    set_count: u32,
}

impl IndexedPartition {
    /// Create an empty partition that will hold `size` elements. Elements
    /// must be added via [`push_block`] immediately after construction.
    fn with_capacity(size: usize) -> Self {
        Self {
            elements: Vec::with_capacity(size),
            location: vec![0; size],
            set_of: vec![0; size],
            first: Vec::new(),
            past: Vec::new(),
            marked: Vec::new(),
            touched: Vec::new(),
            set_count: 0,
        }
    }

    /// Append a new block whose members are the elements in `members`.
    /// The block id returned is the new block's index.
    fn push_block(&mut self, members: &[u32]) -> u32 {
        let block_id = self.set_count;
        let first = self.elements.len() as u32;
        for &e in members {
            let idx = self.elements.len() as u32;
            self.elements.push(e);
            self.location[e as usize] = idx;
            self.set_of[e as usize] = block_id;
        }
        let past = self.elements.len() as u32;
        self.first.push(first);
        self.past.push(past);
        self.marked.push(0);
        self.set_count += 1;
        block_id
    }

    /// Mark element `e` in its current block. Swaps `e` into the marked
    /// prefix (the region `[first[b] .. first[b] + marked[b])`) and
    /// records the block as "touched" on the first mark.
    #[inline]
    fn mark(&mut self, e: u32) {
        let b = self.set_of[e as usize] as usize;
        let loc = self.location[e as usize];
        let boundary = self.first[b] + self.marked[b];
        if loc >= boundary {
            // Swap element `e` with the first unmarked element of block `b`.
            let other = self.elements[boundary as usize];
            self.elements[boundary as usize] = e;
            self.elements[loc as usize] = other;
            self.location[e as usize] = boundary;
            self.location[other as usize] = loc;
            if self.marked[b] == 0 {
                self.touched.push(b as u32);
            }
            self.marked[b] += 1;
        }
    }

    /// Split every touched block. The **smaller** half gets the freshly
    /// allocated block id; the larger half keeps the original id.
    ///
    /// This is the critical property on which Valmari's §2 outer loop
    /// relies: by advancing cursors `c` and `b` monotonically through
    /// the partitions and always assigning the new id to the smaller
    /// half, every cord/block that still needs processing is
    /// guaranteed to sit at an index ≥ the current cursor — so a plain
    /// `while (c < C.z)` driver reaches it without any worklist data
    /// structure (cf. Valmari 2012 §4).
    ///
    /// For each touched block `b`:
    /// - If all of `b` is marked (fully marked) or none (dead touch),
    ///   clear marks in place — no split.
    /// - Otherwise allocate `new_id` and assign the smaller of
    ///   (marked prefix, unmarked tail) to it. Rewrite `set_of` for
    ///   the moved elements; the block-interval endpoints are
    ///   updated to reflect the new layout.
    fn split(&mut self) {
        for i in 0..self.touched.len() {
            let b = self.touched[i] as usize;
            let marked = self.marked[b];
            let first = self.first[b];
            let past = self.past[b];
            let size = past - first;
            if marked > 0 && marked < size {
                let split_point = first + marked;
                let new_id = self.set_count;
                let marked_smaller = marked <= size - marked;
                if marked_smaller {
                    // New block = marked prefix [first, split_point).
                    // Old block keeps [split_point, past) — the unmarked tail.
                    self.first.push(first);
                    self.past.push(split_point);
                    self.first[b] = split_point;
                    for idx in first..split_point {
                        let e = self.elements[idx as usize];
                        self.set_of[e as usize] = new_id;
                    }
                } else {
                    // New block = unmarked tail [split_point, past).
                    // Old block keeps [first, split_point) — the marked prefix.
                    self.first.push(split_point);
                    self.past.push(past);
                    self.past[b] = split_point;
                    for idx in split_point..past {
                        let e = self.elements[idx as usize];
                        self.set_of[e as usize] = new_id;
                    }
                }
                self.marked.push(0);
                self.set_count += 1;
            }
            self.marked[b] = 0;
        }
        self.touched.clear();
    }

    /// Iterate a block's elements as a slice.
    #[inline]
    fn members(&self, block: u32) -> &[u32] {
        let first = self.first[block as usize] as usize;
        let past = self.past[block as usize] as usize;
        &self.elements[first..past]
    }
}

/// Minimize a DFA using Valmari's 2012 algorithm.
///
/// Returns a new DFA with equivalent states merged. See module docs for
/// the algorithmic shape; invariants preserved:
/// - Accept distinctions (different `accept` tokens don't merge).
/// - Weight distinctions.
/// - `alt_accepts` distinctions (full vector equality required to merge).
/// - Start state is renumbered to id 0 and `canonicalize_state_order` is
///   called to yield deterministic BFS numbering.
pub fn minimize_dfa(dfa: &Dfa) -> Dfa {
    let n = dfa.states.len();
    if n <= 1 {
        return dfa.clone();
    }

    let num_classes = dfa.num_classes;

    // --- Step 1: Enumerate transitions (compact CSR-style layout). ---
    //
    // Each live transition `(src, label, dst)` gets a unique id in the
    // `trans` vector. Dead transitions are skipped entirely so the
    // per-label transition partition stays lean.
    //
    // inverse_head[dst] is the first-index (in `trans`) of a linked
    // list of transitions with that dst; inverse_next[tid] is the
    // id of the next transition in the list. This is a CSR inverse
    // index over transitions (not states), letting us enumerate
    // "all transitions landing in a given target state" in O(degree).
    let mut trans_src: Vec<u32> = Vec::new();
    let mut trans_label: Vec<u32> = Vec::new();
    let mut trans_dst: Vec<u32> = Vec::new();
    for (state_idx, state) in dfa.states.iter().enumerate() {
        for (class_id, &target) in state.transitions.iter().enumerate() {
            if target != DEAD_STATE {
                trans_src.push(state_idx as u32);
                trans_label.push(class_id as u32);
                trans_dst.push(target);
            }
        }
    }
    let num_trans = trans_src.len();

    let mut inverse_head: Vec<i32> = vec![-1; n];
    let mut inverse_next: Vec<i32> = vec![-1; num_trans];
    for (tid, &dst) in trans_dst.iter().enumerate() {
        let head_pos = &mut inverse_head[dst as usize];
        inverse_next[tid] = *head_pos;
        *head_pos = tid as i32;
    }
    // --- Step 2: Build the state partition P. ---
    //
    // States that have different accept tokens, weights, or alt-accept sets
    // must never merge — that's what makes the lexer's disambiguation
    // correct under ambiguity. The initial partition groups states whose
    // triples `(accept, weight, alt_accepts)` coincide. A BTreeMap with
    // a composite key runs once, outside the refinement loop, so the
    // `alt_accepts` Vec clone into the key is amortized over n, not n².
    type PartitionKey<'a> = (Option<&'a super::TokenKind>, u64, Vec<(&'a super::TokenKind, u64)>);
    let mut accept_groups: BTreeMap<PartitionKey<'_>, Vec<u32>> = BTreeMap::new();
    for (i, state) in dfa.states.iter().enumerate() {
        let weight_bits = state.weight.value().to_bits();
        let alt_key: Vec<(&super::TokenKind, u64)> = state
            .alt_accepts
            .iter()
            .map(|(k, w)| (k, w.value().to_bits()))
            .collect();
        accept_groups
            .entry((state.accept.as_ref(), weight_bits, alt_key))
            .or_default()
            .push(i as u32);
    }

    let mut state_partition = IndexedPartition::with_capacity(n);
    for (_key, members) in &accept_groups {
        state_partition.push_block(members);
    }

    // --- Step 3: Build the transition partition C. ---
    //
    // Initial partition: group transitions by label. For Calculator's
    // 60-class alphabet we get at most 60 initial blocks, typically
    // fewer because some labels never transition.
    let mut by_label: Vec<Vec<u32>> = vec![Vec::new(); num_classes];
    for (tid, &label) in trans_label.iter().enumerate() {
        by_label[label as usize].push(tid as u32);
    }
    let mut transition_partition = IndexedPartition::with_capacity(num_trans);
    for members in &by_label {
        if !members.is_empty() {
            transition_partition.push_block(members);
        }
    }

    // --- Step 4: Refinement via Valmari's dual-cursor driver (§2, Fig. 6). ---
    //
    // Cursor `c` walks the transition partition; cursor `b` walks the
    // state partition. Each outer iteration processes cord block `c`
    // (marking the states it touches) then runs an inner loop over any
    // *ready* state block — a block whose id is ≥ the current `b`.
    //
    // The critical invariant: `IndexedPartition::split` always assigns
    // the NEW id to the smaller half. So when a block gets split, the
    // smaller half lands at `set_count - 1`, strictly ahead of both
    // cursors. Monotonic advancement then guarantees it will be
    // revisited exactly once — no worklist, no dedup bitset, no
    // book-keeping. `c` and `b` rise past the current partition size
    // only when the entire pending frontier is drained.
    //
    // This is the §4 simplification: "no data structure and complicated
    // tests are needed for keeping track of blocks and cords that have
    // to be used in the future for splitting."
    let mut mark_states = MARK_STATES.with(|cell| cell.take());

    let mut b_cursor: u32 = 1;
    let mut c_cursor: u32 = 0;
    while c_cursor < transition_partition.set_count {
        // --- Mark sources of cords in current transition block. ---
        mark_states.clear();
        for &tid in transition_partition.members(c_cursor) {
            mark_states.push(trans_src[tid as usize]);
        }
        for &s in &mark_states {
            state_partition.mark(s);
        }
        state_partition.split();
        c_cursor += 1;

        // --- Drain any newly ready state blocks. ---
        while b_cursor < state_partition.set_count {
            // Mark incoming cords of every state in block `b_cursor`.
            // Valmari's proof only requires that split() gave the new
            // id to the smaller half — we don't need the extra
            // "mark incoming of smaller half of the split" optimization
            // here, because block `b_cursor` is itself the smaller half
            // (or an initial block, which is effectively one-sided).
            let first = state_partition.first[b_cursor as usize] as usize;
            let past = state_partition.past[b_cursor as usize] as usize;
            for idx in first..past {
                let s = state_partition.elements[idx];
                let mut t = inverse_head[s as usize];
                while t >= 0 {
                    transition_partition.mark(t as u32);
                    t = inverse_next[t as usize];
                }
            }
            transition_partition.split();
            b_cursor += 1;
        }
    }

    // Return TLS buffers.
    MARK_STATES.with(|cell| cell.set(mark_states));

    // --- Step 6: Build the minimized DFA. ---
    //
    // One new state per final state block, with the representative's
    // accept/weight/alt_accepts. The start block gets new id 0.
    let final_block_count = state_partition.set_count;
    let mut block_to_new: Vec<StateId> = vec![DEAD_STATE; final_block_count as usize];

    let start_block = state_partition.set_of[dfa.start as usize];
    let mut new_dfa = Dfa::new(num_classes);

    block_to_new[start_block as usize] = 0;
    {
        let rep = state_partition.members(start_block)[0] as usize;
        new_dfa.states[0].accept = dfa.states[rep].accept.clone();
        new_dfa.states[0].weight = dfa.states[rep].weight;
        new_dfa.states[0].alt_accepts = dfa.states[rep].alt_accepts.clone();
    }

    for b in 0..final_block_count {
        if b == start_block {
            continue;
        }
        let rep = state_partition.members(b)[0] as usize;
        let new_id = new_dfa.add_state(DfaState {
            transitions: vec![DEAD_STATE; num_classes],
            accept: dfa.states[rep].accept.clone(),
            weight: dfa.states[rep].weight,
            alt_accepts: dfa.states[rep].alt_accepts.clone(),
        });
        block_to_new[b as usize] = new_id;
    }

    for b in 0..final_block_count {
        let rep = state_partition.members(b)[0];
        let new_id = block_to_new[b as usize];
        for class_id in 0..num_classes as ClassId {
            let target = dfa.transition(rep, class_id);
            if target != DEAD_STATE {
                let target_block = state_partition.set_of[target as usize];
                let new_target = block_to_new[target_block as usize];
                if new_target != DEAD_STATE {
                    new_dfa.set_transition(new_id, class_id, new_target);
                }
            }
        }
    }

    new_dfa.start = 0;

    // --- Step 7: Canonical BFS state reordering. ---
    // Same purpose as under the old Hopcroft impl: deterministic output.
    canonicalize_state_order(&mut new_dfa);

    new_dfa
}

/// Renumber DFA states in BFS order from the start state.
///
/// This ensures that generated match arms appear in a canonical order,
/// independent of the NFA construction strategy (DAFSA vs prefix-only trie).
/// Future grammars with shared `Ident` tokens could trigger DAFSA merging,
/// producing different NFA topologies; canonical ordering makes the output
/// deterministic regardless.
///
/// Complexity: O(S + T) where S = number of states, T = total transitions.
pub fn canonicalize_state_order(dfa: &mut Dfa) {
    let n = dfa.states.len();
    if n <= 1 {
        return;
    }

    let num_classes = dfa.num_classes;

    // BFS from start state (always 0 after minimize_dfa)
    let mut old_to_new: Vec<StateId> = vec![DEAD_STATE; n];
    let mut new_order: Vec<StateId> = Vec::with_capacity(n);
    let mut queue = std::collections::VecDeque::with_capacity(n);

    old_to_new[dfa.start as usize] = 0;
    new_order.push(dfa.start);
    queue.push_back(dfa.start);

    while let Some(old_id) = queue.pop_front() {
        for class_id in 0..num_classes {
            let target = dfa.states[old_id as usize].transitions[class_id];
            if target != DEAD_STATE && old_to_new[target as usize] == DEAD_STATE {
                let new_id = new_order.len() as StateId;
                old_to_new[target as usize] = new_id;
                new_order.push(target);
                queue.push_back(target);
            }
        }
    }

    // Check if already in BFS order (common case — skip reordering)
    let already_ordered = new_order
        .iter()
        .enumerate()
        .all(|(i, &old)| old == i as StateId);
    if already_ordered && new_order.len() == n {
        return;
    }

    // Build reordered states vector
    let mut new_states: Vec<DfaState> = Vec::with_capacity(new_order.len());
    for &old_id in &new_order {
        let old_state = &dfa.states[old_id as usize];
        let mut new_transitions = Vec::with_capacity(num_classes);
        for &target in &old_state.transitions {
            if target == DEAD_STATE {
                new_transitions.push(DEAD_STATE);
            } else {
                new_transitions.push(old_to_new[target as usize]);
            }
        }
        new_states.push(DfaState {
            transitions: new_transitions,
            accept: old_state.accept.clone(),
            weight: old_state.weight,
            alt_accepts: old_state.alt_accepts.clone(),
        });
    }

    dfa.states = new_states;
    dfa.start = 0;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::nfa::{build_nfa, BuiltinNeeds};
    use crate::automata::partition::compute_equivalence_classes;
    use crate::automata::subset::subset_construction;
    use crate::automata::TerminalPattern;
    use crate::automata::TokenKind;
    use crate::LiteralPatterns;

    #[test]
    fn test_minimize_simple() {
        let terminals = vec![
            TerminalPattern {
                text: "+".to_string(),
                kind: TokenKind::Fixed("+".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "-".to_string(),
                kind: TokenKind::Fixed("-".to_string()),
                is_keyword: false,
            },
        ];
        let needs = BuiltinNeeds {
            ident: true,
            integer: true,
            float: false,
            string_lit: false,
            boolean: false,
            rational: false,
            fixed_point: false,
        };

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);

        // Minimized DFA should have no more states than the original
        assert!(
            min_dfa.states.len() <= dfa.states.len(),
            "minimized DFA ({} states) should have no more states than original ({} states)",
            min_dfa.states.len(),
            dfa.states.len()
        );
    }

    #[test]
    fn test_canonicalize_idempotent() {
        // Canonical reordering applied twice should produce the same DFA.
        let terminals = vec![
            TerminalPattern {
                text: "+".to_string(),
                kind: TokenKind::Fixed("+".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "++".to_string(),
                kind: TokenKind::Fixed("++".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "-".to_string(),
                kind: TokenKind::Fixed("-".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "->".to_string(),
                kind: TokenKind::Fixed("->".to_string()),
                is_keyword: false,
            },
        ];
        let needs = BuiltinNeeds {
            ident: true,
            integer: true,
            float: false,
            string_lit: false,
            boolean: false,
            rational: false,
            fixed_point: false,
        };

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);

        // Snapshot state after first canonicalization (already done in minimize_dfa)
        let first_pass_states: Vec<_> = min_dfa
            .states
            .iter()
            .map(|s| (s.transitions.clone(), s.accept.clone()))
            .collect();

        // Apply canonicalization again
        let mut dfa_copy = min_dfa.clone();
        canonicalize_state_order(&mut dfa_copy);

        let second_pass_states: Vec<_> = dfa_copy
            .states
            .iter()
            .map(|s| (s.transitions.clone(), s.accept.clone()))
            .collect();

        assert_eq!(
            first_pass_states, second_pass_states,
            "canonical BFS reordering should be idempotent"
        );
    }

    #[test]
    fn test_minimize_preserves_acceptance() {
        let terminals = vec![
            TerminalPattern {
                text: "==".to_string(),
                kind: TokenKind::Fixed("==".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "=".to_string(),
                kind: TokenKind::Fixed("=".to_string()),
                is_keyword: false,
            },
        ];
        let needs = BuiltinNeeds {
            ident: false,
            integer: false,
            float: false,
            string_lit: false,
            boolean: false,
            rational: false,
            fixed_point: false,
        };

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);

        // After lexing "=", should accept Fixed("=")
        let mut state = min_dfa.start;
        let class = partition.classify(b'=');
        state = min_dfa.transition(state, class);
        assert_ne!(state, DEAD_STATE);
        assert_eq!(min_dfa.states[state as usize].accept, Some(TokenKind::Fixed("=".to_string())));

        // After lexing "==", should accept Fixed("==")
        let state2 = min_dfa.transition(state, class);
        assert_ne!(state2, DEAD_STATE);
        assert_eq!(
            min_dfa.states[state2 as usize].accept,
            Some(TokenKind::Fixed("==".to_string()))
        );
    }

    #[test]
    fn test_minimize_preserves_multi_accept() {
        // Keyword "error" overlaps with identifier — both should survive minimization
        let terminals = vec![TerminalPattern {
            text: "error".to_string(),
            kind: TokenKind::Fixed("error".to_string()),
            is_keyword: true,
        }];
        let needs = BuiltinNeeds {
            ident: true,
            integer: false,
            float: false,
            string_lit: false,
            boolean: false,
            rational: false,
            fixed_point: false,
        };

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);

        // Pre-minimization: should have ambiguous state
        assert!(
            dfa.has_ambiguous_accepts(),
            "pre-minimization DFA should have ambiguous accepts for 'error'"
        );

        let min_dfa = minimize_dfa(&dfa);

        // Post-minimization: ambiguous state must survive
        assert!(
            min_dfa.has_ambiguous_accepts(),
            "post-minimization DFA must preserve ambiguous accepts"
        );

        // Walk "error" through minimized DFA
        let mut state = min_dfa.start;
        for &byte in b"error" {
            let class = partition.classify(byte);
            state = min_dfa.transition(state, class);
            assert_ne!(state, DEAD_STATE);
        }

        let dfa_state = &min_dfa.states[state as usize];

        // Primary still Fixed("error")
        assert_eq!(dfa_state.accept, Some(TokenKind::Fixed("error".to_string())),);

        // alt_accepts preserved with both kinds
        assert!(
            dfa_state.is_ambiguous(),
            "minimized state after 'error' should still be ambiguous"
        );
        let kinds: Vec<&TokenKind> = dfa_state.alt_accepts.iter().map(|(k, _)| k).collect();
        assert!(kinds.contains(&&TokenKind::Ident));
        assert!(kinds.contains(&&TokenKind::Fixed("error".to_string())));
    }

    #[test]
    fn test_minimize_does_not_merge_ambiguous_with_unambiguous() {
        // Two keywords "if" and "in" — after "i", the DFA state is ambiguous (ident).
        // After "if" → ambiguous (keyword + ident). After "in" → ambiguous (keyword + ident).
        // After "ix" → unambiguous (just ident). Minimization must NOT merge "if" and "ix"
        // states since they differ in alt_accepts.
        let terminals = vec![TerminalPattern {
            text: "if".to_string(),
            kind: TokenKind::Fixed("if".to_string()),
            is_keyword: true,
        }];
        let needs = BuiltinNeeds {
            ident: true,
            integer: false,
            float: false,
            string_lit: false,
            boolean: false,
            rational: false,
            fixed_point: false,
        };

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);

        // Walk "if" — should be ambiguous
        let mut state_if = min_dfa.start;
        for &byte in b"if" {
            let class = partition.classify(byte);
            state_if = min_dfa.transition(state_if, class);
            assert_ne!(state_if, DEAD_STATE);
        }
        assert!(
            min_dfa.states[state_if as usize].is_ambiguous(),
            "state after 'if' should be ambiguous"
        );

        // Walk "ix" — should NOT be ambiguous (just ident)
        let mut state_ix = min_dfa.start;
        for &byte in b"ix" {
            let class = partition.classify(byte);
            state_ix = min_dfa.transition(state_ix, class);
            assert_ne!(state_ix, DEAD_STATE);
        }
        assert!(
            !min_dfa.states[state_ix as usize].is_ambiguous(),
            "state after 'ix' should NOT be ambiguous"
        );

        // They must be different states (not merged by minimization)
        assert_ne!(
            state_if, state_ix,
            "ambiguous 'if' and unambiguous 'ix' states must not be merged"
        );
    }

    /// Smoke-check: run Valmari on a Calculator-sized grammar, confirm
    /// a sensible reduction, and print timing for eyeball comparison.
    ///
    /// Not a formal benchmark, but useful during development — eyeball
    /// `cargo test -p mettail-prattail valmari_timing -- --nocapture`
    /// to see the per-call cost. The Hopcroft implementation this
    /// replaced peaked at >30 GB on a similar-shape DFA; Valmari
    /// should run in under a millisecond with negligible heap use.
    #[test]
    fn valmari_timing_smoke() {
        use std::time::Instant;

        let ops = [
            "+", "-", "*", "/", "%", "<=", ">=", "==", "!=", "<", ">", "=", "->", "=>", "(", ")",
            "[", "]", "{", "}", ",", ";", ":", "?", "!", "&", "|", "^", "~", "<<", ">>", "&&",
            "||", "++", "--", "+=", "-=", "*=", "/=", "%=",
        ];
        let mut terminals: Vec<TerminalPattern> = ops
            .iter()
            .map(|s| TerminalPattern {
                text: s.to_string(),
                kind: TokenKind::Fixed(s.to_string()),
                is_keyword: false,
            })
            .collect();
        for kw in &[
            "if", "then", "else", "while", "do", "true", "false", "let", "in", "fun", "return",
            "match", "case", "of",
        ] {
            terminals.push(TerminalPattern {
                text: kw.to_string(),
                kind: TokenKind::Fixed(kw.to_string()),
                is_keyword: true,
            });
        }
        let needs = BuiltinNeeds {
            ident: true,
            integer: true,
            float: true,
            string_lit: true,
            boolean: true,
            rational: false,
            fixed_point: false,
        };

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let pre_states = dfa.states.len();

        let runs = 20;
        let t = Instant::now();
        let mut post_states = 0;
        for _ in 0..runs {
            let min_dfa = minimize_dfa(&dfa);
            post_states = min_dfa.states.len();
        }
        let per_run_us = t.elapsed().as_micros() as f64 / runs as f64;

        eprintln!();
        eprintln!("=== Valmari minimize_dfa — Calculator-shape grammar ===");
        eprintln!("  terminals     : {}", terminals.len());
        eprintln!("  NFA states    : {}", nfa.states.len());
        eprintln!("  DFA pre-min   : {} states", pre_states);
        eprintln!("  DFA post-min  : {} states", post_states);
        eprintln!(
            "  reduction     : {:.1}%",
            (1.0 - post_states as f64 / pre_states as f64) * 100.0
        );
        eprintln!("  avg time ({}x): {:.1} µs per minimize_dfa call", runs, per_run_us);
    }
}
