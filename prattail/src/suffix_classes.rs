//! Suffix-class Parikh masks — the input-side substrate of the EP-P2
//! (Stage B) zero-posterior obligation gate.
//!
//! ## What this computes
//!
//! For each token-source POSITION `n`, the set `S[n]` of token *classes*
//! that appear on SOME path forward from `n`, as a `u128` bitmask (one
//! bit per class). This is the Rust transcription of the per-DAG-NODE
//! suffix-class relation `S` proven in
//! `formal/rocq/prattail_wpda_runtime/theories/ParikhObligationGate.v`
//! (Part 2): `S n c ⟺ some path from node n contains an edge of class c`,
//! with edge-monotonicity `S[next_pos(n, alt)] ⊆ S[n]`
//! (`mask_monotone_along_edge`) and union-over-paths soundness
//! (`lattice_union_sound`).
//!
//! The gate (Stage C) reads `S[cursor.pos]` and refutes a cursor iff its
//! TOP-frame `must` obligation demands a class the suffix cannot supply:
//! `must != 0 ∧ (must & S[pos]) != must` ⇒ no accepting continuation
//! (`top_frame_refutation_sound`).
//!
//! ## Grammar-agnosticism (binding contract)
//!
//! This module knows NOTHING about any particular grammar. The mapping
//! from a [`TokenKind`] to its class bit-index is INJECTED by the caller
//! (a `&dyn Fn(&TokenKind) -> Option<u8>`, or anything implementing
//! [`ClassOf`]). The codegen-emitted `WPDA_PARIKH_CLASS_OF` (one class per
//! grammar-declared cross-cat infix trigger terminal + one coarse class
//! for everything else) is supplied at the call site in
//! `wpda_walker.rs`, never here. `None` means "this kind carries no
//! obligation-relevant class" and contributes no bit.
//!
//! ## Two builders, two source shapes
//!
//! - [`SuffixClassMasks::from_linear`] — the LINEAR backward pass:
//!   `S[i] = {class(tok[i])} ∪ S[i+1]`, a single sweep from EOI back to
//!   position 0. Used for `SliceTokenSource` / `MultiTokenSource` /
//!   `MutableMultiTokenSource` (every consumed token advances `pos → pos+1`).
//!
//! - [`SuffixClassMasks::from_lattice`] — the LATTICE backward DP over the
//!   [`LexDag`] edge structure: `S[node] = ⋃_{(c,t) ∈ out-edges(node)}
//!   ({c} ∪ S[t])`, evaluated in reverse-topological order. The cast
//!   corpus routes through `LatticeTokenSource` whenever the lex DAG is
//!   ambiguous (`int` keyword/ident fork), so this is the **critical
//!   path** (plan §P2 round-2 M-1): a linear-only gate would never fire
//!   on its own target corpus. Node-ids are positions; two nodes may
//!   share a `byte_start`; orphan nodes appended after the EOF sentinel
//!   (M6c.7.1 soft-fail secondary-alt dead-ends) still receive a mask
//!   (∅, since they have no out-edges). Repairs allocate no DAG nodes, so
//!   `cursor.pos` always indexes a node with a computed mask.
//!
//! Both builders agree with the closed-form model `S` on the shapes they
//! cover (the linear chain is the degenerate single-out-edge DAG).

use crate::automata::TokenKind;
use crate::lexer_types::LexDag;

/// One class bitmask: bit `i` set ⟺ class `i` appears on some forward
/// path. 128 classes is far beyond the per-grammar trigger-terminal
/// count (the coarse non-trigger class takes one more bit), matching the
/// `ContextWeight`/`u128` capacity convention used elsewhere
/// (`wfst.rs::assign_context_labels`).
pub type ClassMask = u128;

/// Injected class function: maps a [`TokenKind`] to its class bit-index
/// (`0..128`), or `None` when the kind carries no obligation-relevant
/// class. Keeps this module grammar-agnostic — the concrete map is
/// codegen-emitted per language.
pub trait ClassOf {
    /// Bit-index of `kind`'s class, or `None` for "no obligation class".
    fn class_of(&self, kind: &TokenKind) -> Option<u8>;
}

impl<F> ClassOf for F
where
    F: Fn(&TokenKind) -> Option<u8>,
{
    #[inline]
    fn class_of(&self, kind: &TokenKind) -> Option<u8> {
        (self)(kind)
    }
}

/// Turn an `Option<u8>` bit-index into a singleton mask (∅ when `None`
/// or out of range).
#[inline]
fn bit_mask(idx: Option<u8>) -> ClassMask {
    match idx {
        Some(b) if (b as u32) < 128 => 1u128 << b,
        _ => 0,
    }
}

/// Per-position forward suffix-class masks.
///
/// `masks[pos]` is `S[pos]` — the union of classes reachable on any path
/// forward from `pos`. Indexed by the cursor's `pos` (a linear token
/// index for linear sources, a DAG node-id for lattice sources). Out of
/// range positions read as ∅ via [`SuffixClassMasks::mask_at`].
#[derive(Debug, Clone, Default)]
pub struct SuffixClassMasks {
    masks: Vec<ClassMask>,
}

impl SuffixClassMasks {
    /// The `S[pos]` mask, or `0` (∅) if `pos` is out of range. Out-of-range
    /// is sound-by-default for the gate: ∅ never satisfies a non-empty
    /// `must`, but the gate's I8 recovery guard and the
    /// `must != 0`-precondition mean an unknown position simply yields no
    /// extra refutation pressure beyond what the obligation itself states.
    /// Callers that need the "definitely absent" reading must ensure `pos`
    /// is a real position (it always is on the hot path: `cursor.pos`
    /// indexes a token / DAG node).
    #[inline]
    pub fn mask_at(&self, pos: usize) -> ClassMask {
        self.masks.get(pos).copied().unwrap_or(0)
    }

    /// Number of positions covered (= token count for linear sources, =
    /// `dag.nodes.len()` incl. orphans for lattice sources).
    #[inline]
    pub fn len(&self) -> usize {
        self.masks.len()
    }

    /// Whether no positions are covered.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.masks.is_empty()
    }

    /// LINEAR backward pass: `S[i] = {class(tok[i])} ∪ S[i+1]`.
    ///
    /// `kinds[i]` is the primary [`TokenKind`] at linear position `i`
    /// (typically including the trailing `Eof`). One sweep from the last
    /// position back to 0; `S[len]` (one past the end) is ∅ implicitly.
    ///
    /// This is the closed form of the model's `S` on a chain DAG: the
    /// single out-edge from `i` carries `class(tok[i])` and targets `i+1`,
    /// so `S[i] = {class(tok[i])} ∪ S[i+1]` by `S_here`/`S_step`.
    pub fn from_linear<C: ClassOf>(kinds: &[TokenKind], class_of: &C) -> Self {
        let n = kinds.len();
        let mut masks = vec![0 as ClassMask; n];
        // Backward sweep: i from n-1 down to 0. `acc` is S[i+1].
        let mut acc: ClassMask = 0;
        for i in (0..n).rev() {
            let here = bit_mask(class_of.class_of(&kinds[i]));
            // S[i] = {class(tok[i])} ∪ S[i+1]
            let s_i = here | acc;
            masks[i] = s_i;
            acc = s_i;
        }
        SuffixClassMasks { masks }
    }

    /// LATTICE backward DP over the [`LexDag`] edge structure:
    /// `S[node] = ⋃_{(c,t) ∈ out-edges(node)} ({c} ∪ S[t])`.
    ///
    /// Every node in `dag.nodes` receives a mask — including the EOF
    /// sentinel (∅: no out-edges) and any ORPHAN nodes appended after the
    /// sentinel (also ∅). `cursor.pos` always indexes one of these.
    pub fn from_lattice<C: ClassOf>(dag: &LexDag, class_of: &C) -> Self {
        let n = dag.nodes.len();
        // Precompute the per-node out-edge list: (local class contribution,
        // target node-id). One pass over the DAG; the backward DP folds them.
        let mut node_edges: Vec<Vec<(ClassMask, usize)>> = Vec::with_capacity(n);
        for node in &dag.nodes {
            let mut edges: Vec<(ClassMask, usize)> = Vec::with_capacity(node.edges.len());
            for edge in &node.edges {
                edges.push((bit_mask(class_of.class_of(&edge.kind)), edge.target_node));
            }
            node_edges.push(edges);
        }
        Self::from_node_edges(n, &node_edges)
    }

    /// TOKEN-SOURCE backward DP — the SOURCE-AGNOSTIC builder the walker
    /// uses. Reconstructs each position's out-edges purely from the
    /// [`WpdaTokenSource`] trait, so it works for BOTH linear sources
    /// (`SliceTokenSource`/`MultiTokenSource`: one primary edge,
    /// `next_pos(pos,0) = pos+1`) AND lattice sources (`LatticeTokenSource`:
    /// primary + secondary alts, each with its own `next_pos`). The result
    /// equals `from_linear`/`from_lattice` on the respective shapes (same
    /// `S[node] = ⋃ out-edges` computation).
    ///
    /// The primary edge is `(class(peek_kind(pos)), next_pos(pos, 0))`; the
    /// secondaries are `(class(alt.kind), next_pos(pos, i+1))` for each
    /// `alt` in `peek_alternatives(pos)`. Positions with no successor (EOI,
    /// orphans) contribute their own primary class but no descent — ∅ for
    /// the EOF sentinel (whose primary kind is `Eof` → no obligation class).
    pub fn from_token_source<C: ClassOf>(
        tokens: &dyn crate::wpda_runtime::WpdaTokenSource,
        class_of: &C,
    ) -> Self {
        let n = tokens.len();
        let mut node_edges: Vec<Vec<(ClassMask, usize)>> = Vec::with_capacity(n);
        for pos in 0..n {
            let mut edges: Vec<(ClassMask, usize)> = Vec::new();
            // Primary edge: the maximal-munch interpretation.
            if let Some(kind) = tokens.peek_kind(pos) {
                if let Some(target) = tokens.next_pos(pos, 0) {
                    // A real forward edge consuming the primary token.
                    edges.push((bit_mask(class_of.class_of(&kind)), target));
                } else {
                    // No successor (EOI / terminal position): the position
                    // still carries its primary class as a self-contribution
                    // with no descent. Model it as an edge whose target is
                    // itself's absence — represented by target == n (out of
                    // range) so the DP folds only the class, not a suffix.
                    edges.push((bit_mask(class_of.class_of(&kind)), n));
                }
            }
            // Secondary alternatives (lattice multi-length ambiguity).
            let alts = tokens.peek_alternatives(pos);
            for (i, alt) in alts.iter().enumerate() {
                let target = tokens.next_pos(pos, i + 1).unwrap_or(n);
                edges.push((bit_mask(class_of.class_of(&alt.kind)), target));
            }
            node_edges.push(edges);
        }
        Self::from_node_edges(n, &node_edges)
    }

    /// The shared backward-DP core: `S[node] = ⋃_{(c,t) ∈ edges(node)}
    /// (c ∪ S[t])`, evaluated in reverse-topological order via an iterative
    /// (recursion-free) post-order memoization over the edge DAG. The DAG
    /// is acyclic by construction (every edge advances to a strictly larger
    /// byte position / token index), so the memoized DFS terminates and
    /// visits every node exactly once. Out-of-range targets (`t >= n`,
    /// e.g. the EOI self-edge sentinel) contribute only their local class
    /// `c`, never a suffix. Seeds EVERY node-id so orphans / disconnected
    /// components are covered.
    fn from_node_edges(n: usize, node_edges: &[Vec<(ClassMask, usize)>]) -> Self {
        let mut masks = vec![0 as ClassMask; n];
        // `done[i]` ⟺ masks[i] is final (post-order complete).
        let mut done = vec![false; n];
        // `on_stack` guards against re-pushing a node already mid-processing
        // (a cycle — impossible here, but keeps the post-order well-defined
        // and avoids double-descending shared targets).
        let mut on_stack = vec![false; n];

        #[derive(Clone, Copy)]
        struct Frame {
            node: usize,
            /// Index into the node's edges of the NEXT child to fold.
            edge_idx: usize,
        }
        let mut stack: Vec<Frame> = Vec::new();

        // Seed every node's LOCAL contribution (the `c` of each out-edge)
        // up front so a node visited only as a fold-target already carries
        // its own classes; child suffix masks OR in during the DP.
        for (i, edges) in node_edges.iter().enumerate() {
            let mut local: ClassMask = 0;
            for (c, _t) in edges {
                local |= *c;
            }
            masks[i] = local;
        }

        for seed in 0..n {
            if done[seed] {
                continue;
            }
            stack.push(Frame { node: seed, edge_idx: 0 });
            on_stack[seed] = true;

            while let Some(top) = stack.last_mut() {
                let node_idx = top.node;
                let edges = &node_edges[node_idx];
                if top.edge_idx < edges.len() {
                    let (_c, target) = edges[top.edge_idx];
                    top.edge_idx += 1;
                    // Out-of-range target (EOI self-edge sentinel or a
                    // malformed edge): local class already folded above; no
                    // suffix to descend into.
                    if target >= n {
                        continue;
                    }
                    if done[target] {
                        masks[node_idx] |= masks[target];
                    } else if !on_stack[target] {
                        on_stack[target] = true;
                        stack.push(Frame { node: target, edge_idx: 0 });
                    }
                    // `on_stack[target] && !done` ⇒ ancestor (cycle) — never
                    // happens in this DAG; skipped.
                } else {
                    // All edges processed: finalize. Re-fold every now-final
                    // target one last time so the result is independent of
                    // the order children completed in.
                    for (_c, t) in edges {
                        if *t < n && done[*t] {
                            masks[node_idx] |= masks[*t];
                        }
                    }
                    done[node_idx] = true;
                    on_stack[node_idx] = false;
                    stack.pop();
                }
            }
        }

        SuffixClassMasks { masks }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;
    use crate::lexer_types::{LexDag, LexDagEdge, LexDagNode};

    /// Test class function: `==` → class 0, `>=` → class 1, `+` → class 2,
    /// everything else → the coarse class 7. Mirrors the codegen shape
    /// (one bit per trigger terminal + one coarse class).
    fn test_class_of(kind: &TokenKind) -> Option<u8> {
        match kind {
            TokenKind::Fixed(s) if s == "==" => Some(0),
            TokenKind::Fixed(s) if s == ">=" => Some(1),
            TokenKind::Fixed(s) if s == "+" => Some(2),
            TokenKind::Eof => None, // EOF carries no obligation class
            _ => Some(7),           // coarse "everything else"
        }
    }

    fn fixed(s: &str) -> TokenKind {
        TokenKind::Fixed(s.to_string())
    }

    fn edge(kind: TokenKind, target: usize, end_byte: usize, alt_idx: u16) -> LexDagEdge {
        LexDagEdge {
            kind,
            text: String::new(),
            end_byte,
            target_node: target,
            weight: TropicalWeight::new(0.0),
            alt_idx,
        }
    }

    #[test]
    fn linear_backward_pass_unions_suffix() {
        // tokens: ident "==" ident "+" ident Eof
        // classes:   7    0    7    2    7   (None)
        // S[5]=∅, S[4]={7}, S[3]={2,7}, S[2]={2,7}, S[1]={0,2,7}, S[0]={0,2,7}
        let kinds = vec![
            TokenKind::Ident,
            fixed("=="),
            TokenKind::Ident,
            fixed("+"),
            TokenKind::Ident,
            TokenKind::Eof,
        ];
        let m = SuffixClassMasks::from_linear(&kinds, &test_class_of);
        assert_eq!(m.len(), 6);
        let c0 = 1u128 << 0; // ==
        let c2 = 1u128 << 2; // +
        let c7 = 1u128 << 7; // coarse
        assert_eq!(m.mask_at(5), 0, "EOF position: ∅");
        assert_eq!(m.mask_at(4), c7, "last ident");
        assert_eq!(m.mask_at(3), c2 | c7, "+ then ident");
        assert_eq!(m.mask_at(2), c2 | c7, "ident + ident");
        assert_eq!(m.mask_at(1), c0 | c2 | c7, "== ahead too");
        assert_eq!(m.mask_at(0), c0 | c2 | c7, "all classes ahead");
        // out of range → ∅
        assert_eq!(m.mask_at(99), 0);
    }

    #[test]
    fn linear_empty_is_empty() {
        let kinds: Vec<TokenKind> = vec![];
        let m = SuffixClassMasks::from_linear(&kinds, &test_class_of);
        assert!(m.is_empty());
        assert_eq!(m.mask_at(0), 0);
    }

    #[test]
    fn lattice_chain_matches_linear() {
        // A linear chain DAG must produce identical masks to from_linear.
        // node0 -("==")-> node1 -("+")-> node2(EOF)
        let dag = LexDag {
            nodes: vec![
                LexDagNode {
                    byte_start: 0,
                    edges: vec![edge(fixed("=="), 1, 2, 0)],
                },
                LexDagNode {
                    byte_start: 2,
                    edges: vec![edge(fixed("+"), 2, 3, 0)],
                },
                LexDagNode { byte_start: 3, edges: vec![] }, // EOF sentinel
            ],
            byte_to_node: Default::default(),
            eof_node: 2,
        };
        let m = SuffixClassMasks::from_lattice(&dag, &test_class_of);
        let c0 = 1u128 << 0;
        let c2 = 1u128 << 2;
        assert_eq!(m.mask_at(0), c0 | c2);
        assert_eq!(m.mask_at(1), c2);
        assert_eq!(m.mask_at(2), 0);

        // Cross-check against the linear builder on the same primary chain.
        let kinds = vec![fixed("=="), fixed("+"), TokenKind::Eof];
        let lin = SuffixClassMasks::from_linear(&kinds, &test_class_of);
        assert_eq!(m.mask_at(0), lin.mask_at(0));
        assert_eq!(m.mask_at(1), lin.mask_at(1));
        assert_eq!(m.mask_at(2), lin.mask_at(2));
    }

    #[test]
    fn lattice_multi_length_fork_unions_both_paths() {
        // Multi-length ambiguity at node 0:
        //   alt0 (primary, longer): Integer "-3"  end=2 -> node 2
        //   alt1 (secondary, shorter): "-"  end=1 -> node 1
        // node1 -("3" coarse)-> node2
        // node2 -("==")-> node3(EOF)
        //
        // S[3]=∅
        // S[2]={0}                     (==)
        // S[1]={7}∪S[2]={7,0}          (coarse "3" then ==)
        // S[0]= ({7}∪S[2]) ∪ ({7}∪S[1]) = {7,0} ∪ {7,0} = {7,0}
        //   (alt0 class is coarse Integer=7→node2; alt1 class "-"=coarse 7→node1)
        let dag = LexDag {
            nodes: vec![
                // node 0: two out-edges (the fork)
                LexDagNode {
                    byte_start: 0,
                    edges: vec![
                        edge(TokenKind::Integer, 2, 2, 0), // primary, class 7
                        edge(fixed("-"), 1, 1, 1),         // secondary, class 7
                    ],
                },
                // node 1: the "3" after a bare "-"
                LexDagNode {
                    byte_start: 1,
                    edges: vec![edge(TokenKind::Integer, 2, 2, 0)], // class 7
                },
                // node 2: shared join point
                LexDagNode {
                    byte_start: 2,
                    edges: vec![edge(fixed("=="), 3, 4, 0)], // class 0
                },
                // node 3: EOF sentinel
                LexDagNode { byte_start: 4, edges: vec![] },
            ],
            byte_to_node: Default::default(),
            eof_node: 3,
        };
        let m = SuffixClassMasks::from_lattice(&dag, &test_class_of);
        let c0 = 1u128 << 0;
        let c7 = 1u128 << 7;
        assert_eq!(m.mask_at(3), 0, "EOF: ∅");
        assert_eq!(m.mask_at(2), c0, "== ahead");
        assert_eq!(m.mask_at(1), c0 | c7, "coarse then ==");
        assert_eq!(
            m.mask_at(0),
            c0 | c7,
            "union over both fork paths includes == (reachable via the join)"
        );
    }

    #[test]
    fn lattice_shared_byte_start_distinct_nodes() {
        // Two DISTINCT node-ids that share the same byte_start (the M2
        // case the model's `lattice_node_mask_welldefined` covers: masks
        // are keyed by node-id, never byte offset). node0 forks to node1
        // and node2, both with byte_start==1 but different downstream
        // classes; the masks must differ by node-id.
        //   node0 -(coarse a)-> node1   (byte_start 1)
        //   node0 -(coarse b)-> node2   (byte_start 1)
        //   node1 -("==")-> node3
        //   node2 -("+")->  node3
        //   node3 EOF
        // S[3]=∅; S[1]={0}; S[2]={2}; S[0]={7}∪S[1] ∪ {7}∪S[2] = {7,0,2}
        let dag = LexDag {
            nodes: vec![
                LexDagNode {
                    byte_start: 0,
                    edges: vec![
                        edge(TokenKind::Ident, 1, 1, 0),
                        edge(TokenKind::Ident, 2, 1, 1),
                    ],
                },
                LexDagNode {
                    byte_start: 1,
                    edges: vec![edge(fixed("=="), 3, 3, 0)],
                },
                LexDagNode {
                    byte_start: 1, // SAME byte_start as node 1, different node-id
                    edges: vec![edge(fixed("+"), 3, 2, 0)],
                },
                LexDagNode { byte_start: 3, edges: vec![] },
            ],
            byte_to_node: Default::default(),
            eof_node: 3,
        };
        let m = SuffixClassMasks::from_lattice(&dag, &test_class_of);
        let c0 = 1u128 << 0;
        let c2 = 1u128 << 2;
        let c7 = 1u128 << 7;
        assert_eq!(m.mask_at(1), c0, "node1 sees == only");
        assert_eq!(m.mask_at(2), c2, "node2 sees + only (distinct from node1)");
        assert_ne!(m.mask_at(1), m.mask_at(2), "masks keyed by node-id, not byte");
        assert_eq!(m.mask_at(0), c0 | c2 | c7, "fork union");
    }

    #[test]
    fn lattice_orphan_node_after_eof_gets_mask() {
        // M6c.7.1 soft-fail: an ORPHAN node may be appended AFTER the EOF
        // sentinel for a secondary-alt dead-end. It is disconnected from
        // the primary chain and has no out-edges → mask ∅, but it MUST
        // receive a slot so `cursor.pos` indexing it reads ∅, not a panic.
        //   node0 -("==")-> node1(EOF, idx 1)
        //   node2 = ORPHAN at idx 2 (byte_start past EOF, no edges)
        let dag = LexDag {
            nodes: vec![
                LexDagNode {
                    byte_start: 0,
                    edges: vec![edge(fixed("=="), 1, 2, 0)],
                },
                LexDagNode { byte_start: 2, edges: vec![] }, // EOF sentinel
                LexDagNode { byte_start: 2, edges: vec![] }, // ORPHAN after EOF
            ],
            byte_to_node: Default::default(),
            eof_node: 1, // NOT nodes.len()-1
        };
        let m = SuffixClassMasks::from_lattice(&dag, &test_class_of);
        let c0 = 1u128 << 0;
        assert_eq!(m.len(), 3, "all nodes incl. orphan get a slot");
        assert_eq!(m.mask_at(0), c0);
        assert_eq!(m.mask_at(1), 0, "EOF sentinel: ∅");
        assert_eq!(m.mask_at(2), 0, "orphan after EOF: ∅ (covered, no panic)");
    }

    #[test]
    fn lattice_orphan_with_outedge_after_eof() {
        // Stronger orphan case: an orphan node that itself has an out-edge
        // (a secondary-alt dead-end chain). It is still unreachable from
        // node 0, but its OWN mask must reflect its edge class — the seed
        // loop covers every node-id, not just chain-reachable ones.
        //   node0 -("==")-> node1(EOF)
        //   node2 = ORPHAN -("+")-> node3 ; node3 EOF-like, no edges
        let dag = LexDag {
            nodes: vec![
                LexDagNode {
                    byte_start: 0,
                    edges: vec![edge(fixed("=="), 1, 2, 0)],
                },
                LexDagNode { byte_start: 2, edges: vec![] },
                LexDagNode {
                    byte_start: 5,
                    edges: vec![edge(fixed("+"), 3, 6, 0)],
                },
                LexDagNode { byte_start: 6, edges: vec![] },
            ],
            byte_to_node: Default::default(),
            eof_node: 1,
        };
        let m = SuffixClassMasks::from_lattice(&dag, &test_class_of);
        let c0 = 1u128 << 0;
        let c2 = 1u128 << 2;
        assert_eq!(m.mask_at(0), c0);
        assert_eq!(m.mask_at(2), c2, "orphan's own out-edge class is captured");
        assert_eq!(m.mask_at(3), 0);
    }

    #[test]
    fn lattice_diamond_no_double_visit_issue() {
        // Diamond: node0 -> {node1, node2} -> node3. node3 is a shared
        // target reached by two paths; the memoized DFS must fold it
        // correctly without depending on visit order.
        //   node0 -(a coarse)-> node1 ; node0 -(b coarse)-> node2
        //   node1 -("==")-> node3 ; node2 -("==")-> node3
        //   node3 -("+")-> node4(EOF)
        // S[4]=∅; S[3]={2}; S[1]=S[2]={0,2}; S[0]={7,0,2}
        let dag = LexDag {
            nodes: vec![
                LexDagNode {
                    byte_start: 0,
                    edges: vec![
                        edge(TokenKind::Ident, 1, 1, 0),
                        edge(TokenKind::Ident, 2, 1, 1),
                    ],
                },
                LexDagNode {
                    byte_start: 1,
                    edges: vec![edge(fixed("=="), 3, 3, 0)],
                },
                LexDagNode {
                    byte_start: 1,
                    edges: vec![edge(fixed("=="), 3, 3, 0)],
                },
                LexDagNode {
                    byte_start: 3,
                    edges: vec![edge(fixed("+"), 4, 4, 0)],
                },
                LexDagNode { byte_start: 4, edges: vec![] },
            ],
            byte_to_node: Default::default(),
            eof_node: 4,
        };
        let m = SuffixClassMasks::from_lattice(&dag, &test_class_of);
        let c0 = 1u128 << 0;
        let c2 = 1u128 << 2;
        let c7 = 1u128 << 7;
        assert_eq!(m.mask_at(4), 0);
        assert_eq!(m.mask_at(3), c2);
        assert_eq!(m.mask_at(1), c0 | c2);
        assert_eq!(m.mask_at(2), c0 | c2);
        assert_eq!(m.mask_at(0), c0 | c2 | c7);
    }
}
