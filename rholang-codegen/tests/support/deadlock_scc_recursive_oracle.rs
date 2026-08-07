use super::*;

fn recursive_strongly_connected_components(edges: &[BTreeSet<usize>]) -> Vec<BTreeSet<usize>> {
    struct Dfs<'a> {
        edges: &'a [BTreeSet<usize>],
        index: usize,
        stack: Vec<usize>,
        on_stack: BTreeSet<usize>,
        indices: Vec<Option<usize>>,
        lowlinks: Vec<usize>,
        components: Vec<BTreeSet<usize>>,
    }

    impl Dfs<'_> {
        fn visit(&mut self, node: usize) {
            self.indices[node] = Some(self.index);
            self.lowlinks[node] = self.index;
            self.index += 1;
            self.stack.push(node);
            self.on_stack.insert(node);

            for &next in &self.edges[node] {
                if self.indices[next].is_none() {
                    self.visit(next);
                    self.lowlinks[node] = self.lowlinks[node].min(self.lowlinks[next]);
                } else if self.on_stack.contains(&next) {
                    self.lowlinks[node] =
                        self.lowlinks[node].min(self.indices[next].expect("indexed stack node"));
                }
            }

            if self.lowlinks[node] == self.indices[node].expect("current node indexed") {
                let mut component = BTreeSet::new();
                loop {
                    let item = self.stack.pop().expect("SCC root must have stack entries");
                    self.on_stack.remove(&item);
                    component.insert(item);
                    if item == node {
                        break;
                    }
                }
                self.components.push(component);
            }
        }
    }

    let mut dfs = Dfs {
        edges,
        index: 0,
        stack: Vec::new(),
        on_stack: BTreeSet::new(),
        indices: vec![None; edges.len()],
        lowlinks: vec![0; edges.len()],
        components: Vec::new(),
    };
    for node in 0..edges.len() {
        if dfs.indices[node].is_none() {
            dfs.visit(node);
        }
    }
    dfs.components
}

fn graph(rows: &[&[usize]]) -> Vec<BTreeSet<usize>> {
    rows.iter()
        .map(|row| row.iter().copied().collect())
        .collect()
}

#[test]
fn iterative_tarjan_preserves_recursive_component_order() {
    let graphs = [
        graph(&[]),
        graph(&[&[]]),
        graph(&[&[1], &[2], &[]]),
        graph(&[&[1], &[0]]),
        graph(&[&[0]]),
        graph(&[&[1, 2], &[0, 3], &[3], &[2, 4], &[5], &[4]]),
    ];
    for edges in &graphs {
        assert_eq!(
            strongly_connected_components(edges),
            recursive_strongly_connected_components(edges)
        );
    }
}

#[test]
fn iterative_tarjan_handles_twenty_thousand_vertices_on_a_small_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("deadlock-tarjan-small-stack".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut edges = vec![BTreeSet::new(); DEPTH];
            for (node, successors) in edges.iter_mut().enumerate().take(DEPTH - 1) {
                successors.insert(node + 1);
            }
            edges[DEPTH - 1].insert(0);
            let components = strongly_connected_components(&edges);
            assert_eq!(components.len(), 1);
            assert_eq!(components[0].len(), DEPTH);
        })
        .expect("small-stack Tarjan thread must spawn")
        .join()
        .expect("iterative Tarjan must not overflow the native stack");
}
