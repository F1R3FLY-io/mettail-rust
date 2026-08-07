use mettail_rholang_adapter::{DeltaOneMatchEdge, DeltaOneMatching};

pub(crate) fn select<T>(
    edges: &[DeltaOneMatchEdge<T>],
    left_count: usize,
    right_count: usize,
) -> Vec<DeltaOneMatching> {
    fn visit<T>(
        edges: &[DeltaOneMatchEdge<T>],
        edge_indices_by_left: &[Vec<usize>],
        left: usize,
        used_rights: &mut Vec<usize>,
        current_indices: &mut Vec<usize>,
        current_cost: u128,
        best_cost: &mut Option<u128>,
        best_matchings: &mut Vec<DeltaOneMatching>,
    ) {
        if best_cost.is_some_and(|best| current_cost > best) {
            return;
        }
        if left == edge_indices_by_left.len() {
            let matching = DeltaOneMatching {
                edge_indices: current_indices.clone(),
                total_cost: current_cost,
            };
            match *best_cost {
                Some(best) if current_cost > best => {},
                Some(best) if current_cost == best => best_matchings.push(matching),
                _ => {
                    *best_cost = Some(current_cost);
                    best_matchings.clear();
                    best_matchings.push(matching);
                },
            }
            return;
        }
        for &index in &edge_indices_by_left[left] {
            let edge = &edges[index];
            if used_rights.contains(&edge.right) {
                continue;
            }
            let next_cost = current_cost + u128::from(edge.ordering_cost);
            if best_cost.is_some_and(|best| next_cost > best) {
                continue;
            }
            used_rights.push(edge.right);
            current_indices.push(index);
            visit(
                edges,
                edge_indices_by_left,
                left + 1,
                used_rights,
                current_indices,
                next_cost,
                best_cost,
                best_matchings,
            );
            current_indices.pop();
            used_rights.pop();
        }
    }

    if left_count > right_count || edges.len() < left_count {
        return Vec::new();
    }
    if left_count == 0 {
        return vec![DeltaOneMatching { edge_indices: Vec::new(), total_cost: 0 }];
    }
    let mut by_left = vec![Vec::new(); left_count];
    for (index, edge) in edges.iter().enumerate() {
        if edge.is_enabled() && edge.left < left_count && edge.right < right_count {
            by_left[edge.left].push(index);
        }
    }
    if by_left.iter().any(Vec::is_empty) {
        return Vec::new();
    }
    let mut best = Vec::new();
    visit(edges, &by_left, 0, &mut Vec::new(), &mut Vec::new(), 0, &mut None, &mut best);
    best
}
