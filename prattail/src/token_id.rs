//! Compact token identifier mapping for WFST labels.
//!
//! Maps token variant names (e.g., "Plus", "Ident", "Integer") to compact `u16`
//! identifiers suitable for use as WFST transition labels. This avoids string
//! comparisons in hot paths and enables efficient WFST state indexing.

use std::collections::BTreeMap;

/// Compact identifier for a token variant, used as a WFST label.
///
/// `u16` supports up to 65,535 distinct token variants, which is far more than
/// any realistic grammar (typical grammars have 20-100 token variants).
pub type TokenId = u16;

/// Sentinel value for "no token" / epsilon transition.
pub const EPSILON_TOKEN: TokenId = TokenId::MAX;

/// Bidirectional mapping between token variant names and compact `TokenId`s.
///
/// Built once per grammar during pipeline construction, then used by the
/// prediction WFST and dispatch code generation.
#[derive(Debug, Clone)]
pub struct TokenIdMap {
    /// Token variant name → compact ID.
    name_to_id: BTreeMap<String, TokenId>,
    /// Compact ID → token variant name.
    id_to_name: Vec<String>,
}

impl TokenIdMap {
    /// Create a new empty token ID map.
    pub fn new() -> Self {
        TokenIdMap {
            name_to_id: BTreeMap::new(),
            id_to_name: Vec::new(),
        }
    }

    /// Create a token ID map from a set of token variant names.
    ///
    /// Assigns IDs in sorted order (BTreeMap iteration) for determinism.
    pub fn from_names(names: impl IntoIterator<Item = String>) -> Self {
        let mut map = TokenIdMap::new();
        let mut sorted: Vec<String> = names.into_iter().collect();
        sorted.sort();
        sorted.dedup();
        for name in sorted {
            map.get_or_insert(&name);
        }
        map
    }

    /// Get the ID for a token name, inserting it if not present.
    pub fn get_or_insert(&mut self, name: &str) -> TokenId {
        if let Some(&id) = self.name_to_id.get(name) {
            return id;
        }
        let id = self.id_to_name.len() as TokenId;
        self.name_to_id.insert(name.to_string(), id);
        self.id_to_name.push(name.to_string());
        id
    }

    /// Look up the ID for a token name. Returns `None` if not registered.
    pub fn get(&self, name: &str) -> Option<TokenId> {
        self.name_to_id.get(name).copied()
    }

    /// Look up the name for a token ID. Returns `None` if out of range.
    pub fn name(&self, id: TokenId) -> Option<&str> {
        self.id_to_name.get(id as usize).map(|s| s.as_str())
    }

    /// Number of registered tokens.
    pub fn len(&self) -> usize {
        self.id_to_name.len()
    }

    /// Whether the map is empty.
    pub fn is_empty(&self) -> bool {
        self.id_to_name.is_empty()
    }

    /// Iterate over all (name, id) pairs in ID order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, TokenId)> {
        self.id_to_name
            .iter()
            .enumerate()
            .map(|(id, name)| (name.as_str(), id as TokenId))
    }
}

impl Default for TokenIdMap {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_token_id_map_basic() {
        let mut map = TokenIdMap::new();
        let plus = map.get_or_insert("Plus");
        let minus = map.get_or_insert("Minus");
        let plus2 = map.get_or_insert("Plus");

        assert_eq!(plus, 0);
        assert_eq!(minus, 1);
        assert_eq!(plus2, 0); // idempotent
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn test_token_id_map_lookup() {
        let mut map = TokenIdMap::new();
        map.get_or_insert("Ident");
        map.get_or_insert("Integer");

        assert_eq!(map.get("Ident"), Some(0));
        assert_eq!(map.get("Integer"), Some(1));
        assert_eq!(map.get("Float"), None);

        assert_eq!(map.name(0), Some("Ident"));
        assert_eq!(map.name(1), Some("Integer"));
        assert_eq!(map.name(99), None);
    }

    #[test]
    fn test_token_id_map_from_names() {
        let map = TokenIdMap::from_names(
            vec!["Plus", "Minus", "Star", "Plus"] // duplicate
                .into_iter()
                .map(String::from),
        );

        assert_eq!(map.len(), 3); // deduped
        // Sorted: Minus(0), Plus(1), Star(2)
        assert_eq!(map.get("Minus"), Some(0));
        assert_eq!(map.get("Plus"), Some(1));
        assert_eq!(map.get("Star"), Some(2));
    }

    #[test]
    fn test_token_id_map_iter() {
        let map = TokenIdMap::from_names(
            vec!["A", "B", "C"].into_iter().map(String::from),
        );

        let pairs: Vec<_> = map.iter().collect();
        assert_eq!(pairs, vec![("A", 0), ("B", 1), ("C", 2)]);
    }
}
