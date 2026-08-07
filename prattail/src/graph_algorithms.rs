//! Shared stack-safe graph algorithms.

/// Return Tarjan strongly connected components in reverse topological order.
///
/// Vertices are the contiguous indices `0..adjacency.len()`. Out-of-range
/// successors are ignored so callers consuming partially validated external
/// graphs retain the historical behavior of the two-way analysis.
pub(crate) fn tarjan_scc(adjacency: &[Vec<usize>]) -> Vec<Vec<usize>> {
    #[derive(Clone, Copy)]
    struct Frame {
        vertex: usize,
        next_successor: usize,
    }

    let vertex_count = adjacency.len();
    let mut next_index = 0usize;
    let mut indices = vec![usize::MAX; vertex_count];
    let mut lowlinks = vec![0usize; vertex_count];
    let mut on_stack = vec![false; vertex_count];
    let mut component_stack = Vec::new();
    let mut components = Vec::new();

    for start in 0..vertex_count {
        if indices[start] != usize::MAX {
            continue;
        }

        indices[start] = next_index;
        lowlinks[start] = next_index;
        next_index += 1;
        component_stack.push(start);
        on_stack[start] = true;
        let mut work = vec![Frame { vertex: start, next_successor: 0 }];

        while let Some(frame) = work.last_mut() {
            let vertex = frame.vertex;
            if frame.next_successor < adjacency[vertex].len() {
                let successor = adjacency[vertex][frame.next_successor];
                frame.next_successor += 1;
                if successor >= vertex_count {
                    continue;
                }
                if indices[successor] == usize::MAX {
                    indices[successor] = next_index;
                    lowlinks[successor] = next_index;
                    next_index += 1;
                    component_stack.push(successor);
                    on_stack[successor] = true;
                    work.push(Frame { vertex: successor, next_successor: 0 });
                } else if on_stack[successor] {
                    lowlinks[vertex] = lowlinks[vertex].min(indices[successor]);
                }
                continue;
            }

            let finished = work
                .pop()
                .expect("Tarjan work stack contains its current frame");
            if lowlinks[finished.vertex] == indices[finished.vertex] {
                let mut component = Vec::new();
                loop {
                    let member = component_stack
                        .pop()
                        .expect("Tarjan component stack underflow");
                    on_stack[member] = false;
                    component.push(member);
                    if member == finished.vertex {
                        break;
                    }
                }
                components.push(component);
            }
            if let Some(parent) = work.last() {
                lowlinks[parent.vertex] = lowlinks[parent.vertex].min(lowlinks[finished.vertex]);
            }
        }
    }

    components
}

#[cfg(test)]
mod tests {
    use super::*;

    fn normalized(mut components: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
        for component in &mut components {
            component.sort_unstable();
        }
        components.sort_unstable();
        components
    }

    fn transitive_closure_oracle(adjacency: &[Vec<usize>]) -> Vec<Vec<usize>> {
        let n = adjacency.len();
        let mut reachable = vec![vec![false; n]; n];
        for (source, successors) in adjacency.iter().enumerate() {
            reachable[source][source] = true;
            for &target in successors {
                if target < n {
                    reachable[source][target] = true;
                }
            }
        }
        for pivot in 0..n {
            for source in 0..n {
                for target in 0..n {
                    reachable[source][target] |=
                        reachable[source][pivot] && reachable[pivot][target];
                }
            }
        }

        let mut assigned = vec![false; n];
        let mut components = Vec::new();
        for source in 0..n {
            if assigned[source] {
                continue;
            }
            let mut component = Vec::new();
            for target in 0..n {
                if reachable[source][target] && reachable[target][source] {
                    assigned[target] = true;
                    component.push(target);
                }
            }
            components.push(component);
        }
        components
    }

    #[test]
    fn tarjan_matches_reachability_equivalence_for_every_four_vertex_graph() {
        const N: usize = 4;
        for edge_mask in 0u32..(1u32 << (N * N)) {
            let mut adjacency = vec![Vec::new(); N];
            for source in 0..N {
                for target in 0..N {
                    if edge_mask & (1 << (source * N + target)) != 0 {
                        adjacency[source].push(target);
                    }
                }
            }
            assert_eq!(
                normalized(tarjan_scc(&adjacency)),
                normalized(transitive_closure_oracle(&adjacency)),
                "SCC mismatch for edge mask {edge_mask:#06x}",
            );
        }
    }

    #[test]
    fn tarjan_handles_a_twenty_thousand_vertex_cycle_on_a_small_stack() {
        const VERTICES: usize = 20_000;
        const STACK_SIZE: usize = 256 * 1024;

        let adjacency = (0..VERTICES)
            .map(|vertex| vec![(vertex + 1) % VERTICES])
            .collect::<Vec<_>>();
        std::thread::Builder::new()
            .name("tarjan-stack-gate".into())
            .stack_size(STACK_SIZE)
            .spawn(move || {
                let components = tarjan_scc(&adjacency);
                assert_eq!(components.len(), 1);
                assert_eq!(components[0].len(), VERTICES);
            })
            .expect("spawn Tarjan stack gate")
            .join()
            .expect("Tarjan stack gate overflowed or panicked");
    }
}
