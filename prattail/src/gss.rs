//! CEK-9A: Graph-Structured Stack (GSS) for GLL parsing.
//!
//! Generalizes the CEK continuation stack to a **graph-structured stack**
//! where multiple parse states share common continuations. This turns
//! PraTTaIL from a deterministic parser with NFA fallback into a full
//! GLL parser that handles ALL ambiguity natively.
//!
//! ## Architecture
//!
//! GSS nodes are `(pos, frame_tag)` pairs; edges are shared continuations.
//! The WFST selects the best parse from the GSS's packed parse forest.
//! Falls back to deterministic CEK for unambiguous grammars (zero overhead).
//!
//! ## References
//!
//! - Scott, E. & Johnstone, A. (2010). *GLL parsing.* ENTCS.
//! - Tomita, M. (1986). *Efficient parsing for natural language.* Kluwer.
//!
//! ## Feature Gate
//!
//! Available under `gll-parsing` feature (depends on `reactive-cek`).

use std::collections::HashMap;

// ══════════════════════════════════════════════════════════════════════════════
// GSS Types
// ══════════════════════════════════════════════════════════════════════════════

/// Unique identifier for a GSS node.
pub type GssNodeId = u32;

/// A node in the graph-structured stack.
///
/// Each node represents a parse state at a particular input position
/// with a particular frame variant on top.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GssNode {
    /// Input position.
    pub pos: usize,
    /// Frame variant tag (e.g., "InfixRHS", "RD_Let_0").
    pub frame_tag: String,
}

/// An edge in the GSS connecting a node to its successor.
#[derive(Debug, Clone)]
pub struct GssEdge {
    /// Target node ID.
    pub target: GssNodeId,
    /// Weight of this edge (from WFST prediction).
    pub weight: f64,
}

/// Graph-Structured Stack implementation.
///
/// Supports forking (multiple stack tops sharing a common suffix)
/// for GLL-style ambiguous parsing.
#[derive(Debug, Clone)]
pub struct GraphStructuredStack {
    /// Nodes in the GSS.
    nodes: Vec<GssNode>,
    /// Edges: source node ID → list of outgoing edges.
    edges: HashMap<GssNodeId, Vec<GssEdge>>,
    /// Active frontier: stack tops currently being explored.
    frontier: Vec<GssNodeId>,
    /// Node lookup: GssNode → GssNodeId for structural sharing.
    node_index: HashMap<GssNode, GssNodeId>,
}

impl GraphStructuredStack {
    /// Create a new empty GSS.
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            edges: HashMap::new(),
            frontier: Vec::new(),
            node_index: HashMap::new(),
        }
    }

    /// Get or create a GSS node, ensuring structural sharing.
    ///
    /// If a node with the same `(pos, frame_tag)` already exists,
    /// returns its ID instead of creating a duplicate.
    pub fn get_or_create_node(&mut self, node: GssNode) -> GssNodeId {
        if let Some(&id) = self.node_index.get(&node) {
            return id;
        }
        let id = self.nodes.len() as GssNodeId;
        self.node_index.insert(node.clone(), id);
        self.nodes.push(node);
        id
    }

    /// Add an edge from source to target with given weight.
    pub fn add_edge(&mut self, source: GssNodeId, target: GssNodeId, weight: f64) {
        self.edges
            .entry(source)
            .or_default()
            .push(GssEdge { target, weight });
    }

    /// Fork the stack: create a new frontier node sharing the
    /// current node's continuation.
    pub fn fork(&mut self, from: GssNodeId, new_node: GssNode, weight: f64) -> GssNodeId {
        let new_id = self.get_or_create_node(new_node);
        self.add_edge(new_id, from, weight);
        self.frontier.push(new_id);
        new_id
    }

    /// Push a node onto the active frontier.
    pub fn push_frontier(&mut self, node_id: GssNodeId) {
        self.frontier.push(node_id);
    }

    /// Pop a node from the active frontier.
    pub fn pop_frontier(&mut self) -> Option<GssNodeId> {
        self.frontier.pop()
    }

    /// Get the current frontier size.
    pub fn frontier_size(&self) -> usize {
        self.frontier.len()
    }

    /// Total number of nodes in the GSS.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Total number of edges in the GSS.
    pub fn edge_count(&self) -> usize {
        self.edges.values().map(|v| v.len()).sum()
    }

    /// Get a node by ID.
    pub fn node(&self, id: GssNodeId) -> Option<&GssNode> {
        self.nodes.get(id as usize)
    }

    /// Get outgoing edges from a node.
    pub fn edges_from(&self, id: GssNodeId) -> &[GssEdge] {
        self.edges.get(&id).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Check if the GSS is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Enumerate all paths from a frontier node to the root.
    ///
    /// Each path is a sequence of node IDs from the frontier to the
    /// bottom of the stack. Used for extracting parse forests.
    pub fn paths_to_root(&self, start: GssNodeId) -> Vec<Vec<GssNodeId>> {
        let mut result = Vec::new();
        let mut current_path = vec![start];
        self.dfs_paths(start, &mut current_path, &mut result);
        result
    }

    fn dfs_paths(
        &self,
        node: GssNodeId,
        path: &mut Vec<GssNodeId>,
        result: &mut Vec<Vec<GssNodeId>>,
    ) {
        let edges = self.edges_from(node);
        if edges.is_empty() {
            // Leaf (bottom of stack)
            result.push(path.clone());
            return;
        }
        for edge in edges {
            path.push(edge.target);
            self.dfs_paths(edge.target, path, result);
            path.pop();
        }
    }
}

impl Default for GraphStructuredStack {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Packed Parse Forest (SPPF)
// ══════════════════════════════════════════════════════════════════════════════

/// A node in the Shared Packed Parse Forest (SPPF).
///
/// Used to represent all parse trees compactly when the grammar
/// is ambiguous. Multiple derivations share common subtrees.
#[derive(Debug, Clone)]
pub enum SppfNode {
    /// A terminal leaf.
    Terminal {
        /// Token position.
        pos: usize,
        /// Token text.
        text: String,
    },
    /// An interior node (nonterminal).
    Interior {
        /// Rule label.
        label: String,
        /// Input range [start, end).
        start: usize,
        end: usize,
        /// Children (shared across packed alternatives).
        children: Vec<SppfNodeId>,
    },
    /// A packed node representing an ambiguous derivation.
    Packed {
        /// Alternative derivations.
        alternatives: Vec<Vec<SppfNodeId>>,
    },
}

/// Unique identifier for an SPPF node.
pub type SppfNodeId = u32;

/// Shared Packed Parse Forest.
#[derive(Debug, Clone, Default)]
pub struct Sppf {
    /// All nodes in the forest.
    nodes: Vec<SppfNode>,
}

impl Sppf {
    /// Create a new empty SPPF.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a node to the forest.
    pub fn add_node(&mut self, node: SppfNode) -> SppfNodeId {
        let id = self.nodes.len() as SppfNodeId;
        self.nodes.push(node);
        id
    }

    /// Get a node by ID.
    pub fn node(&self, id: SppfNodeId) -> Option<&SppfNode> {
        self.nodes.get(id as usize)
    }

    /// Total number of nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the forest is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Count the number of distinct parse trees represented.
    pub fn tree_count(&self, root: SppfNodeId) -> usize {
        match self.node(root) {
            Some(SppfNode::Terminal { .. }) => 1,
            Some(SppfNode::Interior { children, .. }) => {
                children.iter().map(|&c| self.tree_count(c)).product::<usize>().max(1)
            },
            Some(SppfNode::Packed { alternatives }) => {
                alternatives
                    .iter()
                    .map(|alt| {
                        alt.iter().map(|&c| self.tree_count(c)).product::<usize>().max(1)
                    })
                    .sum()
            },
            None => 0,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gss_create_node() {
        let mut gss = GraphStructuredStack::new();
        let node = GssNode {
            pos: 0,
            frame_tag: "InfixRHS".to_string(),
        };
        let id = gss.get_or_create_node(node.clone());
        assert_eq!(id, 0);

        // Same node should return same ID (structural sharing)
        let id2 = gss.get_or_create_node(node);
        assert_eq!(id2, 0);
        assert_eq!(gss.node_count(), 1);
    }

    #[test]
    fn test_gss_fork() {
        let mut gss = GraphStructuredStack::new();
        let root = gss.get_or_create_node(GssNode {
            pos: 0,
            frame_tag: "Root".to_string(),
        });
        gss.push_frontier(root);

        let fork1 = gss.fork(
            root,
            GssNode {
                pos: 1,
                frame_tag: "Alt_A".to_string(),
            },
            0.5,
        );
        let fork2 = gss.fork(
            root,
            GssNode {
                pos: 1,
                frame_tag: "Alt_B".to_string(),
            },
            0.7,
        );

        assert_eq!(gss.node_count(), 3);
        assert_eq!(gss.edge_count(), 2);

        // Both forks share the root as successor
        let edges1 = gss.edges_from(fork1);
        assert_eq!(edges1.len(), 1);
        assert_eq!(edges1[0].target, root);

        let edges2 = gss.edges_from(fork2);
        assert_eq!(edges2.len(), 1);
        assert_eq!(edges2[0].target, root);
    }

    #[test]
    fn test_gss_paths_to_root() {
        let mut gss = GraphStructuredStack::new();
        let root = gss.get_or_create_node(GssNode {
            pos: 0,
            frame_tag: "Root".to_string(),
        });
        let mid = gss.get_or_create_node(GssNode {
            pos: 1,
            frame_tag: "Mid".to_string(),
        });
        let top = gss.get_or_create_node(GssNode {
            pos: 2,
            frame_tag: "Top".to_string(),
        });

        gss.add_edge(mid, root, 1.0);
        gss.add_edge(top, mid, 1.0);

        let paths = gss.paths_to_root(top);
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0], vec![top, mid, root]);
    }

    #[test]
    fn test_sppf_basic() {
        let mut sppf = Sppf::new();
        let t1 = sppf.add_node(SppfNode::Terminal {
            pos: 0,
            text: "1".to_string(),
        });
        let t2 = sppf.add_node(SppfNode::Terminal {
            pos: 2,
            text: "2".to_string(),
        });
        let add = sppf.add_node(SppfNode::Interior {
            label: "Add".to_string(),
            start: 0,
            end: 3,
            children: vec![t1, t2],
        });

        assert_eq!(sppf.len(), 3);
        assert_eq!(sppf.tree_count(add), 1);
    }

    #[test]
    fn test_sppf_ambiguous() {
        let mut sppf = Sppf::new();
        let t1 = sppf.add_node(SppfNode::Terminal { pos: 0, text: "a".to_string() });
        let t2 = sppf.add_node(SppfNode::Terminal { pos: 1, text: "b".to_string() });
        let t3 = sppf.add_node(SppfNode::Terminal { pos: 2, text: "c".to_string() });

        // Two alternative derivations
        let packed = sppf.add_node(SppfNode::Packed {
            alternatives: vec![
                vec![t1, t2],
                vec![t2, t3],
            ],
        });

        assert_eq!(sppf.tree_count(packed), 2);
    }
}
