//! Pattern trie for fine-grained dependency stratification.
//!
//! Uses PathMap indexed by De Bruijn-canonicalized byte paths to:
//! 1. Group alpha-equivalent LHS patterns (same byte path = same alpha-class)
//! 2. Compute fine-grained dependency groups via constructor co-reference
//! 3. Detect rewrite subsumption (general pattern subsumes specific pattern)
//!
//! # Architecture
//!
//! ```text
//! Equation/Rewrite patterns
//!   → pattern_to_debruijn_bytes()    (Sprint 6b: pattern_codec.rs)
//!   → PatternIndex (PathMap + BloomFilter)
//!   → compute_fine_dependency_groups()   (union-find over constructor labels)
//!   → find_alpha_equivalent_groups()     (collision classes in LHS trie)
//!   → detect_subsumption()               (prefix + matching queries)
//! ```

use crate::ast::language::LanguageDef;
use crate::logic::bloom_filter::BloomFilter;
use crate::logic::pattern_codec::pattern_to_debruijn_bytes;
use pathmap::ring::{AlgebraicResult, Lattice, COUNTER_IDENT, SELF_IDENT};
use pathmap::zipper::{ZipperIteration, ZipperValues};
use pathmap::PathMap;
use std::collections::{HashMap, HashSet};

// ── Rule Identifiers ───────────────────────────────────────────────────────

/// Identifies a rule in the language definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RuleId {
    /// Index into `language.equations`
    Equation(usize),
    /// Index into `language.rewrites`
    Rewrite(usize),
}

// ── Lattice for Vec<RuleId> ────────────────────────────────────────────────

/// Wrapper around `Vec<RuleId>` implementing PathMap's `Lattice` trait.
///
/// - `pjoin` = set union (merge rule lists)
/// - `pmeet` = set intersection
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuleIdSet(pub Vec<RuleId>);

impl Lattice for RuleIdSet {
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        let mut merged: Vec<RuleId> = self.0.clone();
        for id in &other.0 {
            if !merged.contains(id) {
                merged.push(*id);
            }
        }
        merged.sort();
        if merged == self.0 {
            AlgebraicResult::Identity(SELF_IDENT)
        } else if merged == other.0 {
            AlgebraicResult::Identity(COUNTER_IDENT)
        } else {
            AlgebraicResult::Element(RuleIdSet(merged))
        }
    }

    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
        let other_set: HashSet<RuleId> = other.0.iter().copied().collect();
        let intersection: Vec<RuleId> = self
            .0
            .iter()
            .filter(|id| other_set.contains(id))
            .copied()
            .collect();
        if intersection.is_empty() {
            AlgebraicResult::None
        } else if intersection == self.0 {
            AlgebraicResult::Identity(SELF_IDENT)
        } else if intersection == other.0 {
            AlgebraicResult::Identity(COUNTER_IDENT)
        } else {
            AlgebraicResult::Element(RuleIdSet(intersection))
        }
    }
}

// Required trait impls for PathMap<V>
unsafe impl Send for RuleIdSet {}
unsafe impl Sync for RuleIdSet {}

// ── Pattern Index ──────────────────────────────────────────────────────────

/// Index mapping De Bruijn pattern bytes → rule identifiers.
///
/// Rules with alpha-equivalent LHS patterns map to the same trie path.
pub struct PatternIndex {
    /// LHS patterns → Vec<RuleId>
    pub lhs_trie: PathMap<RuleIdSet>,
    /// RHS patterns → Vec<RuleId>
    pub rhs_trie: PathMap<RuleIdSet>,
    /// Bloom filter over LHS pattern bytes for O(1) negative rejection
    pub lhs_bloom: BloomFilter,
    /// Constructor labels referenced per rule
    pub constructor_sets: HashMap<RuleId, HashSet<String>>,
    /// De Bruijn bytes per rule (for diagnostics and subsumption)
    pub lhs_bytes: HashMap<RuleId, Vec<u8>>,
    /// Total number of indexed rules
    pub rule_count: usize,
}

impl PatternIndex {
    /// Build a PatternIndex from all equations and rewrites in the language.
    pub fn build(language: &LanguageDef) -> Self {
        let eq_count = language.equations.len();
        let rw_count = language.rewrites.len();
        let total = eq_count + rw_count;

        let mut lhs_trie = PathMap::<RuleIdSet>::new();
        let mut rhs_trie = PathMap::<RuleIdSet>::new();
        let mut lhs_bloom = BloomFilter::new(total.max(1));
        let mut constructor_sets: HashMap<RuleId, HashSet<String>> =
            HashMap::with_capacity(total);
        let mut lhs_bytes_map: HashMap<RuleId, Vec<u8>> = HashMap::with_capacity(total);

        // Index equations
        for (i, eq) in language.equations.iter().enumerate() {
            let id = RuleId::Equation(i);
            let lhs_b = pattern_to_debruijn_bytes(&eq.left);
            let rhs_b = pattern_to_debruijn_bytes(&eq.right);

            lhs_bloom.insert_bytes(&lhs_b);

            // Insert into LHS trie
            match lhs_trie.get_mut(&lhs_b) {
                Some(set) => {
                    if !set.0.contains(&id) {
                        set.0.push(id);
                        set.0.sort();
                    }
                }
                None => {
                    lhs_trie.set_val_at(&lhs_b, RuleIdSet(vec![id]));
                }
            }

            // Insert into RHS trie
            match rhs_trie.get_mut(&rhs_b) {
                Some(set) => {
                    if !set.0.contains(&id) {
                        set.0.push(id);
                        set.0.sort();
                    }
                }
                None => {
                    rhs_trie.set_val_at(&rhs_b, RuleIdSet(vec![id]));
                }
            }

            let mut labels = HashSet::new();
            eq.left.collect_constructor_labels(&mut labels);
            eq.right.collect_constructor_labels(&mut labels);
            constructor_sets.insert(id, labels);
            lhs_bytes_map.insert(id, lhs_b);
        }

        // Index rewrites
        for (i, rw) in language.rewrites.iter().enumerate() {
            let id = RuleId::Rewrite(i);
            let lhs_b = pattern_to_debruijn_bytes(&rw.left);
            let rhs_b = pattern_to_debruijn_bytes(&rw.right);

            lhs_bloom.insert_bytes(&lhs_b);

            match lhs_trie.get_mut(&lhs_b) {
                Some(set) => {
                    if !set.0.contains(&id) {
                        set.0.push(id);
                        set.0.sort();
                    }
                }
                None => {
                    lhs_trie.set_val_at(&lhs_b, RuleIdSet(vec![id]));
                }
            }

            match rhs_trie.get_mut(&rhs_b) {
                Some(set) => {
                    if !set.0.contains(&id) {
                        set.0.push(id);
                        set.0.sort();
                    }
                }
                None => {
                    rhs_trie.set_val_at(&rhs_b, RuleIdSet(vec![id]));
                }
            }

            let mut labels = HashSet::new();
            rw.left.collect_constructor_labels(&mut labels);
            rw.right.collect_constructor_labels(&mut labels);
            constructor_sets.insert(id, labels);
            lhs_bytes_map.insert(id, lhs_b);
        }

        PatternIndex {
            lhs_trie,
            rhs_trie,
            lhs_bloom,
            constructor_sets,
            lhs_bytes: lhs_bytes_map,
            rule_count: total,
        }
    }
}

// ── Union-Find for Dependency Groups ───────────────────────────────────────

/// Simple union-find (disjoint set) for grouping rules by shared constructors.
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        UnionFind {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]]; // path halving
            x = self.parent[x];
        }
        x
    }

    fn union(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        match self.rank[ra].cmp(&self.rank[rb]) {
            std::cmp::Ordering::Less => self.parent[ra] = rb,
            std::cmp::Ordering::Greater => self.parent[rb] = ra,
            std::cmp::Ordering::Equal => {
                self.parent[rb] = ra;
                self.rank[ra] += 1;
            }
        }
    }
}

// ── Fine-Grained Dependency Groups (Sprint 6d) ────────────────────────────

/// Compute fine-grained dependency groups from the pattern index.
///
/// Two rules are in the same group if they share at least one constructor label.
/// Uses union-find over constructor label sets to compute connected components
/// of the constructor co-reference graph.
///
/// Returns groups with ≥1 rules. Groups with ≥2 rules share constructors.
/// Single-rule groups are fully independent.
pub fn compute_fine_dependency_groups(index: &PatternIndex) -> Vec<Vec<RuleId>> {
    if index.rule_count == 0 {
        return Vec::new();
    }

    // Assign each rule a sequential index
    let all_rules: Vec<RuleId> = index.constructor_sets.keys().copied().collect();
    let rule_to_idx: HashMap<RuleId, usize> = all_rules
        .iter()
        .enumerate()
        .map(|(i, &id)| (id, i))
        .collect();

    let mut uf = UnionFind::new(all_rules.len());

    // Map: constructor_label → first rule index that references it
    let mut label_to_first: HashMap<&str, usize> = HashMap::new();

    for (&rule_id, labels) in &index.constructor_sets {
        let rule_idx = rule_to_idx[&rule_id];
        for label in labels {
            match label_to_first.get(label.as_str()) {
                Some(&first_idx) => {
                    uf.union(rule_idx, first_idx);
                }
                None => {
                    label_to_first.insert(label, rule_idx);
                }
            }
        }
    }

    // Group rules by their representative
    let mut groups: HashMap<usize, Vec<RuleId>> = HashMap::new();
    for (i, &rule_id) in all_rules.iter().enumerate() {
        let rep = uf.find(i);
        groups.entry(rep).or_default().push(rule_id);
    }

    // Sort within groups for determinism
    let mut result: Vec<Vec<RuleId>> = groups.into_values().collect();
    for group in &mut result {
        group.sort();
    }
    result.sort_by(|a, b| a[0].cmp(&b[0]));
    result
}

// ── Alpha-Equivalent Pattern Grouping (Sprint 6e) ─────────────────────────

/// Find groups of rules with alpha-equivalent LHS patterns.
///
/// Rules at the same byte path in the LHS PathMap trie have alpha-equivalent
/// LHS patterns (by construction of De Bruijn canonicalization). Returns
/// groups of ≥2 rules only.
///
/// Per "Triemaps that match" §4: De Bruijn leveling ensures that
/// alpha-equivalent keys produce identical trie paths.
pub fn find_alpha_equivalent_groups(index: &PatternIndex) -> Vec<Vec<RuleId>> {
    let mut rz = index.lhs_trie.read_zipper();
    let mut groups = Vec::new();

    while rz.to_next_val() {
        if let Some(rule_set) = rz.val() {
            if rule_set.0.len() >= 2 {
                groups.push(rule_set.0.clone());
            }
        }
    }

    groups.sort_by(|a, b| a[0].cmp(&b[0]));
    groups
}

// ── Subsumption Detection (Sprint 6f) ──────────────────────────────────────

/// A subsumption relationship: `general` subsumes `specific`.
///
/// The general pattern's LHS matches strictly more terms than the specific one.
/// This is a lint/diagnostic — the specific rule may be redundant.
#[derive(Debug, Clone)]
pub struct SubsumptionPair {
    pub general: RuleId,
    pub specific: RuleId,
}

/// Detect rewrite subsumption: cases where one rule's LHS pattern is
/// strictly more general than another's.
///
/// A pattern P subsumes pattern Q if P matches all terms Q matches.
/// Simple structural criterion: P is a proper prefix of Q in the De Bruijn
/// encoding (P's byte path is a prefix of Q's) AND P ends with only
/// NewVar bytes where Q has constructor structure.
///
/// This is a conservative check — it catches common cases like:
/// - `f(x)` subsumes `f(Add(a, b))` (x matches anything, including Add(a,b))
/// - `x` subsumes everything (single NewVar)
pub fn detect_subsumption(index: &PatternIndex) -> Vec<SubsumptionPair> {
    let mut pairs = Vec::new();

    // For each pair of rules, check if one's LHS bytes is a generalization
    // of the other's using structural prefix analysis.
    let all_rules: Vec<(&RuleId, &Vec<u8>)> = index.lhs_bytes.iter().collect();

    for i in 0..all_rules.len() {
        for j in (i + 1)..all_rules.len() {
            let (&id_a, bytes_a) = all_rules[i];
            let (&id_b, bytes_b) = all_rules[j];

            if is_pattern_generalization(bytes_a, bytes_b) {
                pairs.push(SubsumptionPair {
                    general: id_a,
                    specific: id_b,
                });
            } else if is_pattern_generalization(bytes_b, bytes_a) {
                pairs.push(SubsumptionPair {
                    general: id_b,
                    specific: id_a,
                });
            }
        }
    }

    pairs
}

/// Check if `general_bytes` represents a pattern that subsumes `specific_bytes`.
///
/// A pattern G subsumes S if G is "more general" — it has variables where S
/// has concrete structure. In De Bruijn encoding:
/// - If G is a single NewVar (0xC0), it matches everything
/// - If G starts with the same constructor prefix as S but has NewVar where
///   S has deeper structure, G is more general
fn is_pattern_generalization(general: &[u8], specific: &[u8]) -> bool {
    // A single NewVar pattern subsumes everything
    if general.len() == 1 && general[0] == 0xC0 && specific.len() > 1 {
        return true;
    }

    // Walk both byte sequences in parallel
    let mut gi = 0;
    let mut si = 0;
    generalization_walk(general, specific, &mut gi, &mut si)
}

/// Recursive walk checking if general[gi..] subsumes specific[si..].
///
/// Returns true if general is strictly more general than specific at this position.
fn generalization_walk(general: &[u8], specific: &[u8], gi: &mut usize, si: &mut usize) -> bool {
    if *gi >= general.len() || *si >= specific.len() {
        return false;
    }

    let g_byte = general[*gi];
    let s_byte = specific[*si];

    // If general has a NewVar (any variable), it matches whatever specific has
    if g_byte == 0xC0 || (g_byte & 0xC0) == 0x80 {
        // General is a variable — skip it
        *gi += 1;
        // Skip the corresponding structure in specific
        skip_pattern_element(specific, si);
        // This position is a generalization (var vs structure)
        // but only if specific is NOT also just a variable
        let s_is_var = s_byte == 0xC0 || (s_byte & 0xC0) == 0x80;
        return !s_is_var;
    }

    // Both must have the same tag
    if g_byte != s_byte {
        return false;
    }

    // Same constructor application: check arity, constructor name, then recurse on args
    if (g_byte & 0xC0) == 0x00 {
        // Arity tag
        let arity = g_byte as usize;
        *gi += 1;
        *si += 1;

        // Symbol size
        if *gi >= general.len() || *si >= specific.len() {
            return false;
        }
        let g_sym = general[*gi];
        let s_sym = specific[*si];
        if g_sym != s_sym {
            return false;
        }

        let sym_size = if g_sym >= 0xC1 {
            (g_sym - 0xC0) as usize
        } else {
            return false;
        };
        *gi += 1;
        *si += 1;

        // Compare constructor name bytes
        if *gi + sym_size > general.len() || *si + sym_size > specific.len() {
            return false;
        }
        if general[*gi..*gi + sym_size] != specific[*si..*si + sym_size] {
            return false;
        }
        *gi += sym_size;
        *si += sym_size;

        // Recurse on each argument — at least one must be a generalization
        let mut any_more_general = false;
        for _ in 0..arity {
            let saved_gi = *gi;
            let saved_si = *si;
            if generalization_walk(general, specific, gi, si) {
                any_more_general = true;
            } else {
                // Must be structurally identical at this arg
                *gi = saved_gi;
                *si = saved_si;
                // Advance both by skipping the element
                let g_before = *gi;
                skip_pattern_element(general, gi);
                let s_before = *si;
                skip_pattern_element(specific, si);
                // Check the skipped bytes are identical
                if general[g_before..*gi] != specific[s_before..*si] {
                    return false;
                }
            }
        }
        return any_more_general;
    }

    false
}

/// Skip one pattern element in the byte stream, advancing `pos` past it.
fn skip_pattern_element(bytes: &[u8], pos: &mut usize) {
    if *pos >= bytes.len() {
        return;
    }

    let tag = bytes[*pos];

    // Variable (NewVar or VarRef)
    if tag == 0xC0 || (tag & 0xC0) == 0x80 {
        *pos += 1;
        return;
    }

    // Apply: arity + SymbolSize + name bytes + arity children
    if (tag & 0xC0) == 0x00 {
        let arity = tag as usize;
        *pos += 1;
        if *pos < bytes.len() {
            let sym_tag = bytes[*pos];
            if sym_tag >= 0xC1 && sym_tag <= 0xFE {
                let sym_size = (sym_tag - 0xC0) as usize;
                *pos += 1 + sym_size;
            } else {
                *pos += 1;
            }
        }
        for _ in 0..arity {
            skip_pattern_element(bytes, pos);
        }
        return;
    }

    // PraTTaIL extensions
    match tag {
        0x40 | 0x41 | 0x42 | 0x43 => {
            // Collection: tag + count + elements + rest
            *pos += 1;
            if *pos < bytes.len() {
                let count = bytes[*pos] as usize;
                *pos += 1;
                for _ in 0..count {
                    skip_pattern_element(bytes, pos);
                }
                // Rest tag
                if *pos < bytes.len() {
                    if bytes[*pos] == 0x44 {
                        // RestVar + var byte
                        *pos += 2;
                    } else if bytes[*pos] == 0x45 {
                        // NoRest
                        *pos += 1;
                    }
                }
            }
        }
        0x46 => {
            // Map: tag + n_params + param slots + collection + body
            *pos += 1;
            if *pos < bytes.len() {
                let n_params = bytes[*pos] as usize;
                *pos += 1 + n_params; // skip param slot bytes
                skip_pattern_element(bytes, pos); // collection
                skip_pattern_element(bytes, pos); // body
            }
        }
        0x47 => {
            // Zip: tag + first + second
            *pos += 1;
            skip_pattern_element(bytes, pos);
            skip_pattern_element(bytes, pos);
        }
        0x48 => {
            // Lambda: tag + slot + body
            *pos += 2;
            skip_pattern_element(bytes, pos);
        }
        0x49 => {
            // MultiLambda: tag + n_binders + binder slots + body
            *pos += 1;
            if *pos < bytes.len() {
                let n = bytes[*pos] as usize;
                *pos += 1 + n;
                skip_pattern_element(bytes, pos);
            }
        }
        0x4A => {
            // Subst: tag + var_slot + term + replacement
            *pos += 2;
            skip_pattern_element(bytes, pos);
            skip_pattern_element(bytes, pos);
        }
        0x4B => {
            // MultiSubst: tag + n_replacements + scope + replacements
            *pos += 1;
            if *pos < bytes.len() {
                let n = bytes[*pos] as usize;
                *pos += 1;
                skip_pattern_element(bytes, pos); // scope
                for _ in 0..n {
                    skip_pattern_element(bytes, pos);
                }
            }
        }
        _ => {
            // Unknown tag — advance by 1
            *pos += 1;
        }
    }
}

// ── Diagnostic Helpers ─────────────────────────────────────────────────────

/// Summarize pattern index statistics for diagnostic output.
pub fn index_summary(index: &PatternIndex) -> String {
    let dep_groups = compute_fine_dependency_groups(index);
    let alpha_groups = find_alpha_equivalent_groups(index);
    let subsumptions = detect_subsumption(index);

    format!(
        "PatternIndex: {} rules, {} dependency groups ({} independent), \
         {} alpha-equiv groups, {} subsumptions detected",
        index.rule_count,
        dep_groups.len(),
        dep_groups.iter().filter(|g| g.len() == 1).count(),
        alpha_groups.len(),
        subsumptions.len(),
    )
}

/// Get the categories involved in a dependency group.
pub fn group_categories(
    group: &[RuleId],
    index: &PatternIndex,
) -> HashSet<String> {
    let mut cats = HashSet::new();
    for id in group {
        if let Some(labels) = index.constructor_sets.get(id) {
            cats.extend(labels.iter().cloned());
        }
    }
    cats
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::pattern::{Pattern, PatternTerm};
    use crate::logic::pattern_codec::pattern_to_debruijn_bytes;
    use proc_macro2::{Ident, Span};

    fn var(name: &str) -> Pattern {
        Pattern::Term(PatternTerm::Var(Ident::new(name, Span::call_site())))
    }

    fn apply(ctor: &str, args: Vec<Pattern>) -> Pattern {
        Pattern::Term(PatternTerm::Apply {
            constructor: Ident::new(ctor, Span::call_site()),
            args,
        })
    }

    #[test]
    fn test_union_find_basic() {
        let mut uf = UnionFind::new(5);
        uf.union(0, 1);
        uf.union(2, 3);
        assert_eq!(uf.find(0), uf.find(1));
        assert_eq!(uf.find(2), uf.find(3));
        assert_ne!(uf.find(0), uf.find(2));

        uf.union(1, 3);
        assert_eq!(uf.find(0), uf.find(3));
    }

    #[test]
    fn test_skip_pattern_element() {
        // (Add x y) → [02 C4 'A' 'd' 'd' C0 C0]
        let p = apply("Add", vec![var("x"), var("y")]);
        let bytes = pattern_to_debruijn_bytes(&p);

        let mut pos = 0;
        skip_pattern_element(&bytes, &mut pos);
        assert_eq!(pos, bytes.len(), "skip should consume entire pattern");
    }

    #[test]
    fn test_subsumption_var_vs_apply() {
        // var(x) subsumes Apply(Add, [var(a), var(b)])
        let general = pattern_to_debruijn_bytes(&var("x"));
        let specific = pattern_to_debruijn_bytes(&apply("Add", vec![var("a"), var("b")]));
        assert!(
            is_pattern_generalization(&general, &specific),
            "Single variable should subsume constructor application"
        );
    }

    #[test]
    fn test_no_self_subsumption() {
        // (Add x y) does NOT subsume itself — it's the same pattern
        let bytes = pattern_to_debruijn_bytes(&apply("Add", vec![var("x"), var("y")]));
        assert!(
            !is_pattern_generalization(&bytes, &bytes),
            "A pattern should not subsume itself"
        );
    }

    #[test]
    fn test_apply_arg_generalization() {
        // (Add x y) subsumes (Add (Lit a) y) — x is more general than (Lit a)
        let general = pattern_to_debruijn_bytes(&apply("Add", vec![var("x"), var("y")]));
        let specific = pattern_to_debruijn_bytes(&apply(
            "Add",
            vec![apply("Lit", vec![var("a")]), var("y")],
        ));
        assert!(
            is_pattern_generalization(&general, &specific),
            "Variable arg should subsume constructor arg"
        );
    }

    #[test]
    fn test_rule_id_set_lattice() {
        let a = RuleIdSet(vec![RuleId::Equation(0), RuleId::Equation(1)]);
        let b = RuleIdSet(vec![RuleId::Equation(1), RuleId::Rewrite(0)]);

        match a.pjoin(&b) {
            AlgebraicResult::Element(merged) => {
                assert_eq!(merged.0.len(), 3);
                assert!(merged.0.contains(&RuleId::Equation(0)));
                assert!(merged.0.contains(&RuleId::Equation(1)));
                assert!(merged.0.contains(&RuleId::Rewrite(0)));
            }
            other => panic!("Expected Element, got {:?}", other),
        }

        match a.pmeet(&b) {
            AlgebraicResult::Element(intersection) => {
                assert_eq!(intersection.0, vec![RuleId::Equation(1)]);
            }
            AlgebraicResult::Identity(_) => {
                // Also valid if intersection equals one of them
            }
            other => panic!("Expected Element or Identity, got {:?}", other),
        }
    }
}
