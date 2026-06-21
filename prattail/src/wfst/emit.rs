use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// Dispatch code generation with weight ordering
// ══════════════════════════════════════════════════════════════════════════════

/// Generate weight-ordered backtracking dispatch code for a category.
///
/// Unlike the unweighted dispatch in `dispatch.rs`, this version orders
/// backtracking alternatives by weight: the lowest-weight (most likely) path
/// is tried first, reducing expected backtracking cost.
///
/// Returns the generated dispatch code as a String fragment, or `None` if
/// no WFST-based dispatch is needed for this category.
pub fn generate_weighted_dispatch(wfst: &PredictionWfst, category: &str) -> Option<String> {
    if wfst.actions.is_empty() {
        return None;
    }

    // Group actions by token: for each token, collect all alternatives sorted by weight
    let mut token_groups: HashMap<TokenId, Vec<&WeightedAction>> = HashMap::new();

    let start_state = &wfst.states[wfst.start as usize];
    for transition in &start_state.transitions {
        if let Some(action) = wfst.actions.get(transition.action_idx as usize) {
            token_groups
                .entry(transition.input)
                .or_default()
                .push(action);
        }
    }

    // Sort each group by weight
    for group in token_groups.values_mut() {
        group.sort_by_key(|a| a.weight);
    }

    // Count ambiguous tokens (multiple actions for same token)
    let ambiguous_count = token_groups.values().filter(|g| g.len() > 1).count();
    let deterministic_count = token_groups.values().filter(|g| g.len() == 1).count();

    // Build summary comment
    let mut buf = String::with_capacity(512);
    use std::fmt::Write;
    writeln!(
        buf,
        "// WFST prediction for {}: {} tokens ({} deterministic, {} ambiguous)",
        category,
        token_groups.len(),
        deterministic_count,
        ambiguous_count,
    )
    .expect("wfst: DOT write into in-memory String is infallible");

    // Emit per-token weight annotations as comments (for debugging/documentation)
    for (token_id, group) in &token_groups {
        if let Some(name) = wfst.token_map.name(*token_id) {
            if group.len() > 1 {
                write!(buf, "// {}: [", name)
                    .expect("wfst: DOT write into in-memory String is infallible");
                for (i, action) in group.iter().enumerate() {
                    if i > 0 {
                        buf.push_str(", ");
                    }
                    write!(buf, "w={}", action.weight)
                        .expect("wfst: DOT write into in-memory String is infallible");
                }
                writeln!(buf, "]").expect("wfst: DOT write into in-memory String is infallible");
            }
        }
    }

    Some(buf)
}
