use super::*;

/// Pick the lower-cost repair between an existing best and a new candidate.
pub(crate) fn pick_better(existing: Option<RepairResult>, candidate: RepairResult) -> RepairResult {
    match existing {
        None => candidate,
        Some(prev) => {
            if candidate.cost < prev.cost {
                candidate
            } else {
                prev
            }
        },
    }
}

pub(crate) fn pick_better_if_allowed<F>(
    existing: Option<RepairResult>,
    candidate: RepairResult,
    accept_candidate: &mut F,
) -> Option<RepairResult>
where
    F: FnMut(&RepairResult) -> bool,
{
    if accept_candidate(&candidate) {
        Some(pick_better(existing, candidate))
    } else {
        existing
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Multi-token Viterbi recovery
// ══════════════════════════════════════════════════════════════════════════════

/// Find the minimum-cost sequence of repair actions to reach a sync point.
///
/// Unlike `find_best_recovery()` which evaluates single-step repairs, this
/// function builds a multi-step repair lattice and runs Viterbi to find
/// the globally optimal repair sequence.
///
/// ## Lattice structure
///
/// Nodes are token positions `[pos, pos+1, ..., pos+max_lookahead]`.
/// Edges represent repair actions:
/// - **Skip edge**: `i → i+1` with cost `SKIP_PER_TOKEN` (for each non-sync token)
/// - **Sync edge**: `i → FINAL` with cost `0.0` (when token at `i` is a sync token)
/// - **Delete edge**: `i → i+1` with cost `DELETE`
///
/// The final node is a virtual sink. Viterbi finds the minimum-cost path
/// from `pos` to the sink.
///
/// Returns `None` if no sync point is reachable within `MAX_SKIP_LOOKAHEAD`.
pub fn viterbi_recovery(
    token_ids: &[TokenId],
    pos: usize,
    sync_tokens: &BTreeSet<TokenId>,
) -> Option<RepairResult> {
    viterbi_recovery_beam(token_ids, pos, sync_tokens, None)
}

#[inline]
fn normalized_recovery_beam_width(beam_width: Option<TropicalWeight>) -> Option<TropicalWeight> {
    beam_width.filter(|beam| {
        let value = beam.value();
        value.is_finite() && value >= 0.0
    })
}

/// Find the minimum-cost recovery with optional beam pruning.
///
/// When `beam_width` is `Some(w)`, skip edges whose accumulated cost exceeds
/// `best_sync_cost + w` are pruned, reducing the search space for wide
/// lookahead windows. Negative and non-finite beam widths are treated as
/// disabled; otherwise a caller could make the cutoff lower than the current
/// complete repair and prune a cheaper future path.
pub fn viterbi_recovery_beam(
    token_ids: &[TokenId],
    pos: usize,
    sync_tokens: &BTreeSet<TokenId>,
    beam_width: Option<TropicalWeight>,
) -> Option<RepairResult> {
    let beam_width = normalized_recovery_beam_width(beam_width);
    let remaining = token_ids.get(pos..)?;
    let max_lookahead = remaining.len().min(costs::MAX_SKIP_LOOKAHEAD);

    if max_lookahead == 0 {
        return None;
    }

    // B2: Use RecoveryCost (ProductWeight<TropicalWeight, EditWeight>) throughout
    // the Viterbi lattice. Tropical cost is primary; edit count is tiebreaker.
    let num_nodes = max_lookahead + 1;
    let sink = max_lookahead;

    // dist[i] = minimum cost to reach node i from node 0
    let mut dist = vec![RecoveryCost::zero(); num_nodes]; // infinity
    dist[0] = RecoveryCost::one(); // zero cost to reach start

    // pred[i] = (predecessor node, action description)
    let mut pred: Vec<Option<(usize, &'static str)>> = vec![None; num_nodes];

    // B2: Skip edge weight — tropical + 1 edit per skip
    let skip_edge_cost = costs::joint(costs::SKIP_PER_TOKEN.value(), 1);

    // Forward pass through positions
    for i in 0..max_lookahead {
        if dist[i].is_zero() {
            continue; // unreachable
        }

        // Beam pruning: compare tropical component only
        if let Some(beam) = beam_width {
            if !dist[sink].is_zero()
                && dist[i].left.value() > dist[sink].left.value() + beam.value()
            {
                continue;
            }
        }

        let token_at_i = remaining[i];

        // If this position is a sync token, add edge to sink (free)
        if sync_tokens.contains(&token_at_i) {
            let cost_to_sink = dist[i]; // zero additional cost
            if cost_to_sink < dist[sink] {
                dist[sink] = cost_to_sink;
                pred[sink] = Some((i, "sync"));
            }
        }

        // Skip edge: i → i+1 with SKIP_PER_TOKEN cost
        if i + 1 < num_nodes {
            let new_cost = dist[i].times(&skip_edge_cost);

            // Beam pruning: compare tropical component only
            if let Some(beam) = beam_width {
                if !dist[sink].is_zero()
                    && new_cost.left.value() > dist[sink].left.value() + beam.value()
                {
                    continue;
                }
            }

            if new_cost < dist[i + 1] {
                dist[i + 1] = new_cost;
                pred[i + 1] = Some((i, "skip"));
            }
        }
    }

    // If sink is unreachable, no recovery found within lookahead window
    if dist[sink].is_zero() {
        return None;
    }

    // Backtrace to count skips
    let mut skip_count = 0;
    let mut current = sink;
    let mut sync_node = sink;

    if let Some((prev, action)) = pred[current] {
        if action == "sync" {
            sync_node = prev;
            current = prev;
        }
    }

    while let Some((prev, _action)) = pred[current] {
        if prev == 0 && current == 0 {
            break;
        }
        skip_count += 1;
        current = prev;
    }

    let sync_token = if sync_node < remaining.len() {
        remaining[sync_node]
    } else {
        return None;
    };

    Some(RepairResult {
        action: RepairAction::SkipToSync { skip_count, sync_token },
        new_pos: pos + sync_node,
        cost: dist[sink],
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Full Viterbi lattice with all repair edge types
// ══════════════════════════════════════════════════════════════════════════════

/// The kind of edge in the repair lattice, used for backtrace reconstruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RepairEdgeKind {
    /// Skip edge: advance past one token (`i → i+1`), cost = `skip_per_token`.
    Skip,
    /// Delete edge: remove one unexpected token (`i → i+1`), cost = `delete_cost`.
    Delete,
    /// Substitute edge: replace current token with a sync token (`i → i+1`),
    /// cost = `substitute_cost`.
    Substitute(TokenId),
    /// Insert edge: fabricate a missing sync token (`i → i`, self-loop),
    /// cost = `insert_cost`. Max 1 per position to prevent infinite loops.
    Insert(TokenId),
    /// Sync edge: free transition to the sink when a sync token is reached
    /// (`i → SINK`), cost = 0.
    Sync(TokenId),
    /// Swap edge: consume two positions in reversed order (`i → i+2`),
    /// cost = `swap_cost`.
    Swap,
}

/// A multi-step recovery sequence produced by the full Viterbi lattice.
///
/// Unlike `RepairResult` which encodes a single action, `RepairSequence`
/// captures the globally optimal sequence of repairs found by the Viterbi
/// search across all edge types.
#[derive(Debug, Clone)]
pub struct RepairSequence {
    /// Ordered sequence of repair actions from error position to sync point.
    ///
    /// Position-bearing actions inside a sequence use sequence-local
    /// coordinates: `0` is the `pos` passed to `viterbi_multi_step`. Replay
    /// callers add their recovery-window base position exactly once.
    pub actions: Vec<RepairAction>,
    /// New parser position after applying all repairs.
    pub new_pos: usize,
    /// B2: Joint cost — ProductWeight<TropicalWeight, EditWeight>.
    ///
    /// Tropical cost is primary (parse quality), edit-distance is tiebreaker
    /// (repair minimality). This is the Viterbi-optimal total cost.
    pub total_cost: RecoveryCost,
    /// Total edit-distance cost of the sequence (also in total_cost.right,
    /// but kept for backward compatibility with code that reads edits directly).
    pub total_edits: EditWeight,
}

impl fmt::Display for RepairSequence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "repair sequence (")?;
        for (i, action) in self.actions.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", action)?;
        }
        write!(
            f,
            ") cost: {:.2}, edits: {}, new_pos: {}",
            self.total_cost.left.value(),
            self.total_edits.0,
            self.new_pos
        )
    }
}

/// Find the minimum-cost multi-step recovery sequence using the full Viterbi lattice.
///
/// Builds a repair lattice with all edge types:
/// - **Skip**: `i → i+1`, cost `config.skip_per_token`
/// - **Delete**: `i → i+1`, cost `config.delete_cost`
/// - **Substitute**: `i → SINK`, cost `config.substitute_cost`
///   (when token is NOT a sync token)
/// - **Insert**: `i → SINK`, cost `config.insert_cost`
/// - **Swap**: `i → SINK`, cost `config.swap_cost`
///   (when the second token is a sync token revealed by the swap)
/// - **Sync**: `i → SINK`, cost 0 (when token at `i` IS a sync token)
///
/// Runs Viterbi forward pass, then backtraces to reconstruct the optimal
/// repair action sequence.
///
/// Returns `None` if no sync point or token-bearing repair target is reachable
/// within `max_skip_lookahead`.
pub fn viterbi_multi_step(
    token_ids: &[TokenId],
    pos: usize,
    sync_tokens: &BTreeSet<TokenId>,
    config: &RecoveryConfig,
) -> Option<RepairSequence> {
    let normalized_config = config.normalized_for_recovery_search();
    let config = &normalized_config;
    let remaining = token_ids.get(pos..)?;
    let max_lookahead = remaining.len().min(config.max_skip_lookahead);

    if max_lookahead == 0 {
        return None;
    }

    // Nodes: 0..max_lookahead are real token positions; max_lookahead is the
    // virtual sink reached only by Sync/Insert/Substitute/Swap completion
    // edges.
    // B2: Use RecoveryCost (ProductWeight<TropicalWeight, EditWeight>) throughout
    // the multi-step Viterbi lattice. Tropical cost is primary; edit count breaks ties.
    let num_nodes = max_lookahead + 1;
    let sink = max_lookahead;

    // dist[i] = minimum cost to reach node i from node 0
    let mut dist = vec![RecoveryCost::zero(); num_nodes]; // infinity
    dist[0] = RecoveryCost::one(); // zero cost to reach start

    // pred[i] = (predecessor node, edge kind)
    let mut pred: Vec<Option<(usize, RepairEdgeKind)>> = vec![None; num_nodes];

    // Track whether an insert edge has been applied at each position.
    let mut inserted = vec![false; max_lookahead];

    let beam_width = normalized_recovery_beam_width(config.beam_width.map(TropicalWeight::new));

    // B2: Pre-compute edge costs as RecoveryCost
    let skip_edge = costs::joint(config.skip_per_token, 1); // 1 edit per skip
    let delete_edge = costs::joint_edit(config.delete_cost, EditWeight::delete());
    let substitute_edge = costs::joint_edit(config.substitute_cost, EditWeight::substitute());
    let swap_edge = costs::joint(config.swap_cost, 1); // single edit operation
    let insert_edge = costs::joint_edit(config.insert_cost, EditWeight::insert());

    // Forward pass through positions
    for i in 0..max_lookahead {
        if dist[i].is_zero() {
            continue; // unreachable
        }

        // Beam pruning: compare tropical component only
        if let Some(beam) = beam_width {
            if !dist[sink].is_zero()
                && dist[i].left.value() > dist[sink].left.value() + beam.value()
            {
                continue;
            }
        }

        let token_at_i = remaining[i];

        // ── Sync edge: i → SINK (free) when at sync token ────────────
        if sync_tokens.contains(&token_at_i) {
            let cost_to_sink = dist[i];
            if cost_to_sink < dist[sink] {
                dist[sink] = cost_to_sink;
                pred[sink] = Some((i, RepairEdgeKind::Sync(token_at_i)));
            }
        }

        // ── Skip edge: i → i+1, cost skip_per_token ─────────────────
        // Skip advances to another real token position. Completion is via
        // a later Sync/Insert/Substitute/Swap edge into the virtual sink,
        // never by skipping directly into the sink without a sync point.
        if i + 1 < max_lookahead {
            let new_cost = dist[i].times(&skip_edge);

            if let Some(beam) = beam_width {
                if !dist[sink].is_zero()
                    && new_cost.left.value() > dist[sink].left.value() + beam.value()
                {
                    // pruned
                } else if new_cost < dist[i + 1] {
                    dist[i + 1] = new_cost;
                    pred[i + 1] = Some((i, RepairEdgeKind::Skip));
                }
            } else if new_cost < dist[i + 1] {
                dist[i + 1] = new_cost;
                pred[i + 1] = Some((i, RepairEdgeKind::Skip));
            }
        }

        // ── Delete edge: i → i+1, cost delete_cost ───────────────────
        if i + 1 < max_lookahead {
            let new_cost = dist[i].times(&delete_edge);
            if new_cost < dist[i + 1] {
                dist[i + 1] = new_cost;
                pred[i + 1] = Some((i, RepairEdgeKind::Delete));
            }
        }

        // ── Substitute edge: i → i+1, cost substitute_cost ──────────
        // Only when the token at i is NOT already a sync token
        if !sync_tokens.contains(&token_at_i) {
            for &sync_id in sync_tokens {
                let new_cost = dist[i].times(&substitute_edge);
                if new_cost < dist[sink] {
                    dist[sink] = new_cost;
                    pred[sink] = Some((i, RepairEdgeKind::Substitute(sync_id)));
                }
            }
        }

        // ── Swap edge: i → SINK, cost swap_cost ─────────────────────
        // A swap is a complete repair only when the second token is a sync
        // token that becomes first after transposition.
        if i + 1 < max_lookahead && sync_tokens.contains(&remaining[i + 1]) {
            let new_cost = dist[i].times(&swap_edge);
            if new_cost < dist[sink] {
                dist[sink] = new_cost;
                pred[sink] = Some((i, RepairEdgeKind::Swap));
            }
        }

        // ── Insert edge: i → i (self-loop), cost insert_cost ────────
        // Max 1 insert per position to prevent infinite loops
        if !inserted[i] {
            for &sync_id in sync_tokens {
                let new_cost = dist[i].times(&insert_edge);
                if new_cost < dist[sink] {
                    dist[sink] = new_cost;
                    pred[sink] = Some((i, RepairEdgeKind::Insert(sync_id)));
                    inserted[i] = true;
                }
            }
        }
    }

    // If sink is unreachable, no recovery found
    if dist[sink].is_zero() {
        return None;
    }

    // ── Backtrace: reconstruct the action sequence ───────────────────────
    let mut path_reversed: Vec<(usize, usize, RepairEdgeKind)> = Vec::new();
    let mut current = sink;
    let mut final_sync_pos = pos; // position where we sync

    while let Some((prev, edge_kind)) = pred[current] {
        if current == sink {
            final_sync_pos = match edge_kind {
                RepairEdgeKind::Sync(_) | RepairEdgeKind::Insert(_) => pos + prev,
                RepairEdgeKind::Substitute(_) => pos + prev + 1,
                RepairEdgeKind::Swap => pos + prev + 2,
                RepairEdgeKind::Skip | RepairEdgeKind::Delete => pos + prev,
            };
        }
        path_reversed.push((prev, current, edge_kind));
        current = prev;
    }

    if path_reversed.is_empty() {
        return None;
    }

    path_reversed.reverse();

    let mut actions: Vec<RepairAction> = Vec::new();
    let mut pending_skips = 0usize;

    let flush_pending_skips =
        |actions: &mut Vec<RepairAction>, pending_skips: &mut usize, target_rel: usize| {
            if *pending_skips == 0 {
                return true;
            }
            let Some(&sync_token) = remaining.get(target_rel) else {
                return false;
            };
            actions.push(RepairAction::SkipToSync { skip_count: *pending_skips, sync_token });
            *pending_skips = 0;
            true
        };

    for (prev, next, edge_kind) in path_reversed {
        match edge_kind {
            RepairEdgeKind::Sync(sync_token) => {
                if !flush_pending_skips(&mut actions, &mut pending_skips, prev) {
                    return None;
                }
                if actions.is_empty() {
                    actions.push(RepairAction::SkipToSync { skip_count: 0, sync_token });
                }
            },
            RepairEdgeKind::Skip => {
                pending_skips += next.saturating_sub(prev);
            },
            RepairEdgeKind::Delete => {
                if !flush_pending_skips(&mut actions, &mut pending_skips, prev) {
                    return None;
                }
                actions.push(RepairAction::DeleteToken);
            },
            RepairEdgeKind::Substitute(sync_id) => {
                if !flush_pending_skips(&mut actions, &mut pending_skips, prev) {
                    return None;
                }
                actions.push(RepairAction::SubstituteToken { replacement: sync_id });
            },
            RepairEdgeKind::Swap => {
                if !flush_pending_skips(&mut actions, &mut pending_skips, prev) {
                    return None;
                }
                actions.push(RepairAction::SwapTokens { pos_a: prev, pos_b: prev + 1 });
            },
            RepairEdgeKind::Insert(sync_id) => {
                if !flush_pending_skips(&mut actions, &mut pending_skips, prev) {
                    return None;
                }
                actions.push(RepairAction::InsertToken { token: sync_id });
            },
        }
    }

    if !flush_pending_skips(&mut actions, &mut pending_skips, final_sync_pos - pos) {
        return None;
    }

    // Compute total edits
    let total_edits = actions
        .iter()
        .fold(crate::automata::semiring::EditWeight::new(0), |acc, a| {
            crate::automata::semiring::EditWeight::new(acc.0.saturating_add(a.edit_cost().0))
        });

    Some(RepairSequence {
        actions,
        new_pos: final_sync_pos,
        total_cost: dist[sink],
        total_edits,
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Sprint 7 Design B: Forward-Backward Multi-Step Recovery
// ══════════════════════════════════════════════════════════════════════════════

/// Per-position posterior analysis from forward-backward on the repair lattice.
///
/// Identifies **bottleneck positions** — positions where the minimum-cost repair
/// path is forced to pass through — and computes posterior costs that reveal
/// whether a repair at position P also resolves an error at position P+k.
#[derive(Debug, Clone)]
pub struct RecoveryPosterior {
    /// Posterior cost at each position: `alpha[i] ⊗ beta[i]`.
    ///
    /// Low values indicate bottleneck positions (the repair path must pass
    /// through them). High values indicate positions with alternative paths.
    pub position_costs: Vec<TropicalWeight>,

    /// The total cost (partition function) of the repair lattice.
    pub total_cost: TropicalWeight,

    /// Bottleneck positions: indices where the posterior equals the total cost
    /// (within tolerance). Repairs at these positions are on every optimal path.
    pub bottleneck_positions: Vec<usize>,

    /// The Viterbi-optimal repair sequence (same as `viterbi_multi_step`).
    pub optimal_sequence: Option<RepairSequence>,
}

/// Build the repair lattice as an explicit edge list and run forward-backward
/// to compute posterior costs per position.
///
/// This extends `viterbi_multi_step` with backward analysis:
/// - **Forward pass**: same Viterbi lattice as `viterbi_multi_step`.
/// - **Backward pass**: total weight of all paths from each node to the sink.
/// - **Posterior**: `alpha[i] ⊗ beta[i]` per position — reveals bottlenecks.
///
/// ## Multi-error recovery
///
/// When multiple errors are close together, the backward pass reveals whether
/// fixing the first error also resolves subsequent ones (shared bottleneck).
/// If positions P and P+k are both bottleneck positions, a single repair
/// strategy must handle both.
///
/// ## ContextWeight integration
///
/// When `dispatch_context` is provided, repair edges are filtered by context
/// viability: insert/substitute actions are only emitted for sync tokens
/// reachable from the active rule set (via `RecoveryWfst::is_sync_reachable`).
pub fn viterbi_recovery_forward_backward(
    token_ids: &[TokenId],
    pos: usize,
    recovery_wfst: &RecoveryWfst,
    config: &RecoveryConfig,
    dispatch_context: Option<crate::automata::semiring::ContextWeight>,
) -> RecoveryPosterior {
    let normalized_config = config.normalized_for_recovery_search();
    let config = &normalized_config;
    let Some(remaining) = token_ids.get(pos..) else {
        return RecoveryPosterior {
            position_costs: vec![],
            total_cost: TropicalWeight::zero(),
            bottleneck_positions: vec![],
            optimal_sequence: None,
        };
    };
    let max_lookahead = remaining.len().min(config.max_skip_lookahead);

    if max_lookahead == 0 {
        return RecoveryPosterior {
            position_costs: vec![],
            total_cost: TropicalWeight::zero(),
            bottleneck_positions: vec![],
            optimal_sequence: None,
        };
    }

    let num_nodes = max_lookahead + 1; // positions 0..max_lookahead, plus sink
    let sink = max_lookahead;

    // Build explicit edge list for forward-backward
    let mut edges: Vec<Vec<(usize, TropicalWeight)>> = vec![vec![]; num_nodes];

    let skip_cost = TropicalWeight::new(config.skip_per_token);
    let delete_cost = TropicalWeight::new(config.delete_cost);
    let substitute_cost = TropicalWeight::new(config.substitute_cost);
    let insert_cost = TropicalWeight::new(config.insert_cost);
    let swap_cost = TropicalWeight::new(config.swap_cost);

    for i in 0..max_lookahead {
        let token_at_i = remaining[i];

        // Sync edge: i → sink (free) when at sync token
        if recovery_wfst.sync_tokens.contains(&token_at_i) {
            let discount = TropicalWeight::new(recovery_wfst.prediction_discount(token_at_i));
            // Context viability: if dispatch context is set, check reachability
            let context_viable = dispatch_context
                .map_or(true, |ctx| recovery_wfst.is_sync_reachable(token_at_i, ctx));
            if context_viable {
                // Sync is free but modulated by prediction discount
                let sync_weight = if discount.value() < 1.0 {
                    TropicalWeight::new(discount.value() * 0.01) // near-zero but preserves ordering
                } else {
                    TropicalWeight::one() // 0.0 = free
                };
                edges[i].push((sink, sync_weight));
            }
        }

        // Skip edge: i → i+1 over real token positions only.
        if i + 1 < max_lookahead {
            edges[i].push((i + 1, skip_cost));
        }

        // Delete edge: i → i+1 over real token positions only.
        if i + 1 < max_lookahead {
            edges[i].push((i + 1, delete_cost));
        }

        // Substitute edge: i → sink (only when not a sync token)
        if !recovery_wfst.sync_tokens.contains(&token_at_i) {
            for &sync_id in &recovery_wfst.sync_tokens {
                let context_viable = dispatch_context
                    .map_or(true, |ctx| recovery_wfst.is_sync_reachable(sync_id, ctx));
                if context_viable {
                    edges[i].push((sink, substitute_cost));
                    break; // one substitute edge per position suffices for cost analysis
                }
            }
        }

        // Swap edge: i → sink only when the second token is a sync token
        // revealed at the current position by transposition.
        if i + 1 < max_lookahead && recovery_wfst.sync_tokens.contains(&remaining[i + 1]) {
            edges[i].push((sink, swap_cost));
        }

        // Insert edge: i → sink (insert sync token to reach sync immediately)
        for &sync_id in &recovery_wfst.sync_tokens {
            let context_viable =
                dispatch_context.map_or(true, |ctx| recovery_wfst.is_sync_reachable(sync_id, ctx));
            if context_viable {
                edges[i].push((sink, insert_cost));
                break; // one insert cost per position suffices
            }
        }
    }

    // Forward and backward passes
    let alpha = crate::forward_backward::forward_scores::<TropicalWeight>(&edges, num_nodes);
    let beta = crate::forward_backward::backward_scores::<TropicalWeight>(&edges, num_nodes, sink);

    let total_cost = alpha[sink];

    // Posterior costs: alpha[i] ⊗ beta[i] for each position
    let position_costs: Vec<TropicalWeight> =
        (0..num_nodes).map(|i| alpha[i].times(&beta[i])).collect();

    // Bottleneck detection: positions where posterior ≈ total cost
    // (within tolerance 1e-6). These positions are on every optimal path.
    let tolerance = 1e-6;
    let bottleneck_positions: Vec<usize> = if total_cost.is_zero() {
        vec![]
    } else {
        (0..max_lookahead)
            .filter(|&i| {
                !position_costs[i].is_zero()
                    && (position_costs[i].value() - total_cost.value()).abs() < tolerance
            })
            .collect()
    };

    // Also run Viterbi to get the optimal sequence
    let optimal_sequence = viterbi_multi_step(token_ids, pos, &recovery_wfst.sync_tokens, config);

    RecoveryPosterior {
        position_costs,
        total_cost,
        bottleneck_positions,
        optimal_sequence,
    }
}
