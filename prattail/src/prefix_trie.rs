//! Generic prefix trie for grammar left-factoring (A1).
//!
//! Provides a trie where keys are sequences of elements (not bytes) and values
//! are rule labels. Used at compile time during codegen to identify shared
//! prefixes among grammar rules and generate factored dispatch code.
//!
//! ## Design References
//!
//! The traversal API is inspired by:
//! - PathMap's Zipper (`descend_to()`, `child_mask()`, `child_count()`)
//! - liblevenshtein's DictZipper (`descend()`, `children()`, `path()`)
//!
//! Unlike those byte-level tries, this trie supports generic element types
//! (`K: Eq + Hash + Clone`), suitable for sequences of `RDSyntaxItem`.

use std::collections::HashMap;

/// A prefix trie node parameterized over key element type `K` and value type `V`.
///
/// Each node may hold a value (if it's the end of an inserted key) and maps
/// key elements to child nodes.
#[derive(Debug, Clone)]
pub struct PrefixTrie<K, V> {
    /// Value at this node (Some if a key ends here).
    pub value: Option<V>,
    /// Children: maps element → subtrie.
    pub children: HashMap<K, PrefixTrie<K, V>>,
}

impl<K: Eq + std::hash::Hash + Clone, V> PrefixTrie<K, V> {
    /// Create a new empty trie node.
    pub fn new() -> Self {
        PrefixTrie {
            value: None,
            children: HashMap::new(),
        }
    }

    /// Insert a key (sequence of elements) with the given value.
    pub fn insert(&mut self, key: impl IntoIterator<Item = K>, value: V) {
        let mut node = self;
        for elem in key {
            node = node.children.entry(elem).or_insert_with(PrefixTrie::new);
        }
        node.value = Some(value);
    }

    /// Returns the number of children at this node.
    pub fn child_count(&self) -> usize {
        self.children.len()
    }

    /// Returns true if this node holds a value.
    pub fn has_value(&self) -> bool {
        self.value.is_some()
    }

    /// Returns true if this trie is empty (no values, no children).
    pub fn is_empty(&self) -> bool {
        self.value.is_none() && self.children.is_empty()
    }

    /// Returns the depth of the longest shared prefix among all inserted keys.
    ///
    /// A shared prefix is a path from the root through single-child nodes.
    /// The prefix ends at the first node with >1 children, a value, or no children.
    pub fn shared_prefix_depth(&self) -> usize {
        let mut depth = 0;
        let mut node = self;
        while node.children.len() == 1 && node.value.is_none() {
            depth += 1;
            node = node.children.values().next().expect("single child exists");
        }
        depth
    }

    /// Walk the shared prefix (single-child chain from root), returning the
    /// elements along the path and a reference to the divergence node.
    pub fn shared_prefix(&self) -> (Vec<&K>, &PrefixTrie<K, V>) {
        let mut prefix = Vec::new();
        let mut node = self;
        while node.children.len() == 1 && node.value.is_none() {
            let (key, child) = node.children.iter().next().expect("single child exists");
            prefix.push(key);
            node = child;
        }
        (prefix, node)
    }

    /// Iterate over children, yielding (element, subtrie) pairs.
    ///
    /// Analogous to liblevenshtein's `DictZipper::children()`.
    pub fn children(&self) -> impl Iterator<Item = (&K, &PrefixTrie<K, V>)> {
        self.children.iter()
    }

    /// Descend to a child node by element.
    ///
    /// Analogous to PathMap's `ZipperMoving::descend_to()`.
    pub fn descend(&self, elem: &K) -> Option<&PrefixTrie<K, V>> {
        self.children.get(elem)
    }

    /// Count the total number of values (leaves) in the trie.
    pub fn count_values(&self) -> usize {
        let own = if self.value.is_some() { 1 } else { 0 };
        own + self
            .children
            .values()
            .map(|child| child.count_values())
            .sum::<usize>()
    }
}

impl<K: Eq + std::hash::Hash + Clone, V> Default for PrefixTrie<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_trie() {
        let trie: PrefixTrie<String, usize> = PrefixTrie::new();
        assert!(trie.is_empty());
        assert_eq!(trie.child_count(), 0);
        assert_eq!(trie.shared_prefix_depth(), 0);
        assert_eq!(trie.count_values(), 0);
    }

    #[test]
    fn test_single_key() {
        let mut trie = PrefixTrie::new();
        trie.insert(vec!["a", "b", "c"], 1);
        assert_eq!(trie.count_values(), 1);
        assert_eq!(trie.shared_prefix_depth(), 3); // whole path is shared (single key)
        assert!(!trie.is_empty());
    }

    #[test]
    fn test_shared_prefix_two_keys() {
        let mut trie = PrefixTrie::new();
        trie.insert(vec!["a", "b", "c"], 1);
        trie.insert(vec!["a", "b", "d"], 2);
        assert_eq!(trie.count_values(), 2);
        // Shared prefix is "a" → "b", then diverges at "c" vs "d"
        assert_eq!(trie.shared_prefix_depth(), 2);

        let (prefix, divergence) = trie.shared_prefix();
        assert_eq!(prefix.len(), 2);
        assert_eq!(divergence.child_count(), 2);
    }

    #[test]
    fn test_no_shared_prefix() {
        let mut trie = PrefixTrie::new();
        trie.insert(vec!["a", "b"], 1);
        trie.insert(vec!["c", "d"], 2);
        // Root immediately diverges (2 children)
        assert_eq!(trie.shared_prefix_depth(), 0);
        assert_eq!(trie.child_count(), 2);
    }

    #[test]
    fn test_descend() {
        let mut trie = PrefixTrie::new();
        trie.insert(vec!["x", "y", "z"], 42);

        let node_y = trie.descend(&"x").expect("x child").descend(&"y").expect("y child");
        assert_eq!(node_y.child_count(), 1);

        let node_z = node_y.descend(&"z").expect("z child");
        assert!(node_z.has_value());
        assert_eq!(*node_z.value.as_ref().expect("value"), 42);
    }

    #[test]
    fn test_children_iteration() {
        let mut trie = PrefixTrie::new();
        trie.insert(vec!["root", "a"], 1);
        trie.insert(vec!["root", "b"], 2);
        trie.insert(vec!["root", "c"], 3);

        let root_child = trie.descend(&"root").expect("root child");
        assert_eq!(root_child.child_count(), 3);

        let mut values: Vec<usize> = root_child
            .children()
            .filter_map(|(_, child)| child.value.as_ref().copied())
            .collect();
        values.sort();
        assert_eq!(values, vec![1, 2, 3]);
    }

    #[test]
    fn test_prefix_value_at_intermediate_node() {
        let mut trie = PrefixTrie::new();
        trie.insert(vec!["a", "b"], 1);
        trie.insert(vec!["a", "b", "c"], 2);
        // "a" "b" has a value AND children
        let node = trie.descend(&"a").expect("a").descend(&"b").expect("b");
        assert!(node.has_value());
        assert_eq!(node.child_count(), 1);
        // shared_prefix_depth stops at "a" "b" because it has a value
        assert_eq!(trie.shared_prefix_depth(), 2);
    }

    #[test]
    fn test_with_integer_keys() {
        let mut trie = PrefixTrie::new();
        trie.insert(vec![1, 2, 3], "rule_a");
        trie.insert(vec![1, 2, 4], "rule_b");
        trie.insert(vec![1, 5, 6], "rule_c");

        assert_eq!(trie.shared_prefix_depth(), 1); // only "1" is shared
        assert_eq!(trie.count_values(), 3);
    }
}
