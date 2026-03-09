//! AL04: Keyword recognition via minimal perfect hashing (CHD algorithm).
//!
//! Implements a compile-time Compress, Hash, Displace (CHD) minimal perfect
//! hash table for O(1) keyword→token_id lookup. This augments the DFA-based
//! lexer: after the DFA classifies a token as an identifier, the MPH table
//! is probed to check if it's actually a keyword.
//!
//! ## Algorithm
//!
//! The CHD algorithm (Belazzougui, Botelho, Dietzfelbinger 2009) constructs a
//! minimal perfect hash function in two phases:
//!
//! 1. **Bucket assignment**: Each keyword is hashed with `h1` to assign it to a
//!    bucket. Buckets are sorted by descending size (largest first).
//!
//! 2. **Displacement search**: For each bucket, a displacement value `d` is found
//!    such that `h2(key, d) mod n` maps all keys in that bucket to distinct,
//!    previously-unoccupied slots in the output table.
//!
//! At query time, lookup is O(1): compute the bucket via `h1`, retrieve the
//! displacement `d`, compute the slot via `h2(key, d)`, and verify the stored
//! key matches.
//!
//! ## Hash functions
//!
//! Uses FNV-1a (Fowler-Noll-Vo) as the base, with two independent hash values:
//! - `h1(key) = fnv1a(key)` -- bucket assignment (standard FNV-1a offset basis)
//! - `h2(key) = fnv1a_seeded(key, SEED2)` -- per-key displacement multiplier
//!
//! The slot for a key given displacement `d` is:
//!   `slot = (h1(key) + d * h2_nz(key)) % table_size`
//!
//! where `h2_nz` ensures the multiplier is nonzero modulo `table_size`.
//! This "double hashing" scheme guarantees that for any two distinct keys
//! with different `h2_nz` values, there exists a displacement `d` that
//! separates them -- unlike additive displacement which shifts all keys
//! equally.

use std::fmt::Write;

// ══════════════════════════════════════════════════════════════════════════════
// FNV-1a hash (32-bit)
// ══════════════════════════════════════════════════════════════════════════════

/// FNV-1a offset basis (32-bit).
const FNV_OFFSET_BASIS: u32 = 0x811C_9DC5;

/// FNV-1a prime (32-bit).
const FNV_PRIME: u32 = 0x0100_0193;

/// Compute FNV-1a hash of a byte slice with the standard offset basis.
#[inline]
fn fnv1a(data: &[u8]) -> u32 {
    fnv1a_seeded(data, FNV_OFFSET_BASIS)
}

/// Second seed for the independent h2 hash function.
/// Chosen as a prime far from `FNV_OFFSET_BASIS` to maximize independence.
const FNV_SEED2: u32 = 0x6C62_272E;

/// Compute FNV-1a hash of a byte slice with a custom seed as offset basis.
///
/// By varying the seed, we obtain a family of hash functions. Used to
/// construct two independent hashes h1 and h2 for double hashing.
#[inline]
fn fnv1a_seeded(data: &[u8], seed: u32) -> u32 {
    let mut hash = seed;
    for &byte in data {
        hash ^= byte as u32;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

/// Compute h2 for a key: the per-key displacement multiplier.
///
/// Returns a value in `[1, table_size)` (nonzero modulo `table_size`)
/// to ensure that varying `d` actually changes the slot.
#[inline]
fn hash2_nz(key: &[u8], table_size: u32) -> u32 {
    (fnv1a_seeded(key, FNV_SEED2) % (table_size - 1)) + 1
}

/// Compute the bucket index for a key (standard FNV-1a).
#[inline]
fn hash_bucket(key: &[u8], num_buckets: u32) -> u32 {
    fnv1a(key) % num_buckets
}

/// Compute the slot index for a key given a displacement value.
///
/// Uses double hashing: `slot = (h1(key) + d * h2_nz(key)) % table_size`.
/// Because `h2_nz` is nonzero and key-dependent, different displacements
/// move different keys by different amounts, enabling separation.
#[inline]
fn hash_slot(key: &[u8], displacement: u32, table_size: u32) -> u32 {
    let h1 = fnv1a(key);
    let h2 = hash2_nz(key, table_size);
    (h1.wrapping_add(displacement.wrapping_mul(h2))) % table_size
}

// ══════════════════════════════════════════════════════════════════════════════
// MPH table data structure
// ══════════════════════════════════════════════════════════════════════════════

/// A minimal perfect hash table for keyword→token_id lookup.
///
/// Constructed at compile time from the grammar's keyword set. At runtime,
/// provides O(1) keyword recognition with a single hash computation and
/// one string comparison for verification.
#[derive(Debug, Clone)]
pub struct MphTable {
    /// Displacement values, one per bucket. `displacements[h1(key) % num_buckets]`
    /// gives the displacement `d` used to compute the final slot.
    displacements: Vec<u32>,
    /// Slot array. Each occupied slot holds `(keyword, token_id)`. Empty slots
    /// are `None`. The slot for a key is `(h1(key) + d*h2(key)) % table_size`.
    values: Vec<Option<(String, usize)>>,
    /// Number of buckets (for h1 modular reduction). Equals `n` (number of
    /// keywords) for nonempty tables.
    num_buckets: u32,
    /// Total number of slots (prime >= max(n, 3) for nonempty tables). Zero
    /// for empty tables. May be slightly larger than n to ensure prime sizing
    /// and double-hashing correctness.
    table_size: u32,
    /// Actual number of keywords stored. May be less than `table_size` due
    /// to prime sizing.
    keyword_count: u32,
}

/// Maximum number of displacement values to try before falling back.
/// For keyword sets up to ~100, this is more than sufficient.
const MAX_DISPLACEMENT_ATTEMPTS: u32 = 4096;

/// Find the smallest prime >= n.
///
/// Used to size the hash table. A prime table size ensures that `h2_nz`
/// (which returns values in `[1, table_size-1]`) is coprime with
/// `table_size`, guaranteeing that the probe sequence `(h1 + d*h2) % p`
/// cycles through all `p` slots before repeating.
fn next_prime(n: u32) -> u32 {
    if n <= 2 {
        return 2;
    }
    let mut candidate = if n % 2 == 0 { n + 1 } else { n };
    loop {
        if is_prime(candidate) {
            return candidate;
        }
        candidate += 2;
    }
}

/// Simple trial-division primality test. Sufficient for n <= ~10000
/// (keyword counts are typically < 100).
fn is_prime(n: u32) -> bool {
    if n < 2 {
        return false;
    }
    if n < 4 {
        return true;
    }
    if n % 2 == 0 || n % 3 == 0 {
        return false;
    }
    let mut i = 5u32;
    while i.saturating_mul(i) <= n {
        if n % i == 0 || n % (i + 2) == 0 {
            return false;
        }
        i += 6;
    }
    true
}

impl MphTable {
    /// Build a minimal perfect hash table from keyword→token_id pairs.
    ///
    /// The CHD algorithm handles up to ~100 keywords efficiently. For empty
    /// inputs, returns a trivial table that always returns `None` on probe.
    ///
    /// The table size is chosen as the smallest prime >= n to ensure good
    /// double-hashing properties. This wastes at most O(log n) slots,
    /// which is negligible for typical keyword counts.
    ///
    /// # Panics
    ///
    /// Panics if a valid displacement cannot be found within
    /// `MAX_DISPLACEMENT_ATTEMPTS` iterations (extremely unlikely for
    /// reasonable keyword sets).
    pub fn build(keywords: &[(String, usize)]) -> Self {
        let n = keywords.len();
        if n == 0 {
            return MphTable {
                displacements: Vec::new(),
                values: Vec::new(),
                num_buckets: 0,
                table_size: 0,
                keyword_count: 0,
            };
        }

        // Use a prime table size >= 3 to guarantee double-hashing correctness.
        // h2_nz computes `(h2 % (table_size - 1)) + 1`, which requires
        // `table_size >= 3` so the modulus `table_size - 1 >= 2` provides
        // meaningful variation across keys.
        let table_size = next_prime(std::cmp::max(n as u32, 3));
        // Use the same number of buckets as keywords. This gives an average
        // bucket size of ~1, making displacement search fast.
        let num_buckets = n as u32;

        // Phase 1: Assign keywords to buckets via h1.
        let mut buckets: Vec<Vec<usize>> = vec![Vec::new(); num_buckets as usize];
        for (idx, (kw, _)) in keywords.iter().enumerate() {
            let bucket = hash_bucket(kw.as_bytes(), num_buckets) as usize;
            buckets[bucket].push(idx);
        }

        // Sort bucket indices by descending bucket size (process largest first).
        let mut bucket_order: Vec<usize> = (0..num_buckets as usize).collect();
        bucket_order.sort_by(|&a, &b| buckets[b].len().cmp(&buckets[a].len()));

        // Phase 2: Find displacements for each bucket.
        let mut displacements = vec![0u32; num_buckets as usize];
        let mut values: Vec<Option<(String, usize)>> = vec![None; table_size as usize];
        let mut occupied = vec![false; table_size as usize];

        for &bucket_idx in &bucket_order {
            let bucket = &buckets[bucket_idx];
            if bucket.is_empty() {
                // No keywords hash to this bucket; displacement is irrelevant.
                continue;
            }

            // Try displacement values d = 0, 1, 2, ... until all keys in this
            // bucket map to distinct, unoccupied slots.
            let mut found = false;
            'search: for d in 0..MAX_DISPLACEMENT_ATTEMPTS {
                let mut trial_slots: Vec<u32> = Vec::with_capacity(bucket.len());
                let mut trial_ok = true;

                for &kw_idx in bucket {
                    let slot = hash_slot(
                        keywords[kw_idx].0.as_bytes(),
                        d,
                        table_size,
                    ) as usize;

                    if occupied[slot] || trial_slots.contains(&(slot as u32)) {
                        trial_ok = false;
                        break;
                    }
                    trial_slots.push(slot as u32);
                }

                if trial_ok {
                    // Commit this displacement: mark slots as occupied and store values.
                    displacements[bucket_idx] = d;
                    for (i, &kw_idx) in bucket.iter().enumerate() {
                        let slot = trial_slots[i] as usize;
                        occupied[slot] = true;
                        values[slot] = Some((
                            keywords[kw_idx].0.clone(),
                            keywords[kw_idx].1,
                        ));
                    }
                    found = true;
                    break 'search;
                }
            }

            if !found {
                panic!(
                    "MphTable::build: could not find displacement for bucket {} \
                     ({} keys) within {} attempts. This should not happen for \
                     reasonable keyword sets (<=100 keywords).",
                    bucket_idx,
                    bucket.len(),
                    MAX_DISPLACEMENT_ATTEMPTS,
                );
            }
        }

        MphTable {
            displacements,
            values,
            num_buckets,
            table_size,
            keyword_count: n as u32,
        }
    }

    /// Probe the MPH table for a keyword.
    ///
    /// Returns `Some(token_id)` if `text` is a recognized keyword, or `None`
    /// if it is not. The lookup is O(1): one hash computation plus one string
    /// comparison.
    #[inline]
    pub fn probe(&self, text: &str) -> Option<usize> {
        if self.table_size == 0 {
            return None;
        }

        let key = text.as_bytes();
        let bucket = hash_bucket(key, self.num_buckets) as usize;
        let d = self.displacements[bucket];
        let slot = hash_slot(key, d, self.table_size) as usize;

        match &self.values[slot] {
            Some((stored_key, token_id)) if stored_key == text => Some(*token_id),
            _ => None,
        }
    }

    /// Number of keywords stored in the table.
    pub fn len(&self) -> usize {
        self.keyword_count as usize
    }

    /// Whether the table is empty (no keywords).
    pub fn is_empty(&self) -> bool {
        self.keyword_count == 0
    }

    /// Access the displacement array (for codegen).
    pub fn displacements(&self) -> &[u32] {
        &self.displacements
    }

    /// Access the values array (for codegen).
    pub fn values(&self) -> &[Option<(String, usize)>] {
        &self.values
    }

    /// Number of buckets (for codegen).
    pub fn num_buckets(&self) -> u32 {
        self.num_buckets
    }

    /// Table size (for codegen).
    pub fn table_size(&self) -> u32 {
        self.table_size
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Code generation: emit MPH table as Rust source
// ══════════════════════════════════════════════════════════════════════════════

/// Generate Rust source code for a static MPH keyword lookup table.
///
/// Emits:
/// - `MPH_FNV_OFFSET_BASIS`, `MPH_FNV_PRIME`, `MPH_FNV_SEED2` constants
/// - `mph_fnv1a_seeded()` seeded hash function
/// - `MPH_DISPLACEMENTS` array (one displacement per bucket)
/// - `MPH_KEYS` array (stored keys for verification)
/// - `MPH_TOKEN_IDS` array (corresponding token IDs)
/// - `MPH_NUM_BUCKETS` and `MPH_TABLE_SIZE` constants
/// - `mph_probe(text: &str) -> Option<usize>` function
///
/// The generated `mph_probe` can be called after the DFA identifies a token as
/// an identifier, to check whether it is actually a keyword.
pub fn write_mph_tables(buf: &mut String, table: &MphTable) {
    if table.is_empty() {
        // Emit a trivial probe function that always returns None.
        buf.push_str(
            "#[inline(always)] fn mph_probe(_text: &str) -> Option<usize> { None }\n",
        );
        return;
    }

    // Constants
    write!(buf, "const MPH_FNV_OFFSET_BASIS: u32 = 0x{:08X};", FNV_OFFSET_BASIS).unwrap();
    write!(buf, "const MPH_FNV_PRIME: u32 = 0x{:08X};", FNV_PRIME).unwrap();
    write!(buf, "const MPH_FNV_SEED2: u32 = 0x{:08X};", FNV_SEED2).unwrap();
    write!(buf, "const MPH_NUM_BUCKETS: u32 = {};", table.num_buckets()).unwrap();
    write!(buf, "const MPH_TABLE_SIZE: u32 = {};", table.table_size()).unwrap();

    // Displacement array
    write!(buf, "static MPH_DISPLACEMENTS: [u32; {}] = [", table.displacements().len()).unwrap();
    for (i, &d) in table.displacements().iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "{}", d).unwrap();
    }
    buf.push_str("];");

    // Keys array (for verification). None slots use "" as sentinel.
    write!(buf, "static MPH_KEYS: [&str; {}] = [", table.values().len()).unwrap();
    for (i, slot) in table.values().iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        match slot {
            Some((key, _)) => write!(buf, "\"{}\"", key).unwrap(),
            None => buf.push_str("\"\""),
        }
    }
    buf.push_str("];");

    // Token ID array. None slots use usize::MAX as sentinel.
    write!(buf, "static MPH_TOKEN_IDS: [usize; {}] = [", table.values().len()).unwrap();
    for (i, slot) in table.values().iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        match slot {
            Some((_, id)) => write!(buf, "{}", id).unwrap(),
            None => buf.push_str("usize::MAX"),
        }
    }
    buf.push_str("];");

    // Seeded FNV-1a hash function
    buf.push_str(
        "#[inline(always)] fn mph_fnv1a_seeded(data: &[u8], seed: u32) -> u32 { \
         let mut hash = seed; \
         let mut i = 0; \
         while i < data.len() { \
         hash ^= data[i] as u32; \
         hash = hash.wrapping_mul(MPH_FNV_PRIME); \
         i += 1; \
         } hash }",
    );

    // Probe function: h1 (standard FNV) for bucket, double-hash for slot
    buf.push_str(
        "#[inline(always)] fn mph_probe(text: &str) -> Option<usize> { \
         let key = text.as_bytes(); \
         let h1 = mph_fnv1a_seeded(key, MPH_FNV_OFFSET_BASIS); \
         let bucket = (h1 % MPH_NUM_BUCKETS) as usize; \
         let d = MPH_DISPLACEMENTS[bucket]; \
         let h2 = (mph_fnv1a_seeded(key, MPH_FNV_SEED2) % (MPH_TABLE_SIZE - 1)) + 1; \
         let slot = (h1.wrapping_add(d.wrapping_mul(h2)) % MPH_TABLE_SIZE) as usize; \
         if MPH_KEYS[slot] == text { Some(MPH_TOKEN_IDS[slot]) } else { None } \
         }",
    );
}

/// Build an `MphTable` from the grammar's terminal patterns.
///
/// Extracts keyword-like terminals (alphanumeric `Fixed` tokens) and assigns
/// each a sequential token ID. Returns `None` if no keywords are found.
pub fn build_mph_from_terminals(
    terminals: &[super::TerminalPattern],
) -> Option<MphTable> {
    let keywords: Vec<(String, usize)> = terminals
        .iter()
        .enumerate()
        .filter(|(_, t)| t.is_keyword)
        .map(|(idx, t)| (t.text.clone(), idx))
        .collect();

    if keywords.is_empty() {
        return None;
    }

    Some(MphTable::build(&keywords))
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fnv1a_basic() {
        // Smoke test: FNV-1a of empty string should be the offset basis.
        assert_eq!(fnv1a(b""), FNV_OFFSET_BASIS);
        // Known FNV-1a values (32-bit).
        assert_eq!(fnv1a(b"a"), 0xe40c292c);
        assert_eq!(fnv1a(b"foobar"), 0xBF9CF968);
    }

    #[test]
    fn test_empty_keyword_set() {
        let table = MphTable::build(&[]);
        assert!(table.is_empty());
        assert_eq!(table.len(), 0);
        assert_eq!(table.probe("anything"), None);
        assert_eq!(table.probe(""), None);
    }

    #[test]
    fn test_single_keyword() {
        let keywords = vec![("if".to_string(), 42)];
        let table = MphTable::build(&keywords);

        assert_eq!(table.len(), 1);
        assert!(!table.is_empty());
        assert_eq!(table.probe("if"), Some(42));
        assert_eq!(table.probe("else"), None);
        assert_eq!(table.probe("i"), None);
        assert_eq!(table.probe("iff"), None);
        assert_eq!(table.probe(""), None);
    }

    #[test]
    fn test_typical_keyword_set() {
        let keywords = vec![
            ("if".to_string(), 0),
            ("else".to_string(), 1),
            ("while".to_string(), 2),
            ("for".to_string(), 3),
            ("return".to_string(), 4),
            ("fn".to_string(), 5),
            ("let".to_string(), 6),
            ("mut".to_string(), 7),
            ("struct".to_string(), 8),
            ("enum".to_string(), 9),
        ];
        let table = MphTable::build(&keywords);

        assert_eq!(table.len(), 10);

        // All keywords should be found with correct IDs.
        for (kw, id) in &keywords {
            assert_eq!(
                table.probe(kw),
                Some(*id),
                "keyword '{}' should map to token_id {}",
                kw,
                id
            );
        }

        // Non-keywords should return None.
        assert_eq!(table.probe("match"), None);
        assert_eq!(table.probe("impl"), None);
        assert_eq!(table.probe(""), None);
        assert_eq!(table.probe("IF"), None); // case sensitive
        assert_eq!(table.probe("f"), None); // prefix of "fn" and "for"
        assert_eq!(table.probe("form"), None); // extends "for"
    }

    #[test]
    fn test_non_keywords_return_none() {
        let keywords = vec![
            ("true".to_string(), 0),
            ("false".to_string(), 1),
            ("null".to_string(), 2),
        ];
        let table = MphTable::build(&keywords);

        // Strings that are definitely not keywords.
        let non_keywords = [
            "", "t", "tr", "tru", "truee", "True", "TRUE",
            "f", "fa", "fal", "fals", "falsee", "False", "FALSE",
            "n", "nu", "nul", "nulll", "Null", "NULL",
            "hello", "world", "12345", "!@#$%",
        ];
        for nk in &non_keywords {
            assert_eq!(
                table.probe(nk),
                None,
                "'{}' should not be found in keyword table",
                nk
            );
        }
    }

    #[test]
    fn test_collision_resistance_adversarial() {
        // Test with keywords that are prefixes/suffixes of each other
        // and lexicographically close strings.
        let keywords = vec![
            ("a".to_string(), 0),
            ("ab".to_string(), 1),
            ("abc".to_string(), 2),
            ("abcd".to_string(), 3),
            ("abcde".to_string(), 4),
            ("b".to_string(), 5),
            ("ba".to_string(), 6),
            ("bac".to_string(), 7),
            ("ca".to_string(), 8),
            ("cab".to_string(), 9),
        ];
        let table = MphTable::build(&keywords);

        for (kw, id) in &keywords {
            assert_eq!(
                table.probe(kw),
                Some(*id),
                "adversarial keyword '{}' should map to {}",
                kw,
                id
            );
        }

        // Close strings that are NOT keywords.
        assert_eq!(table.probe("abcdef"), None);
        assert_eq!(table.probe("d"), None);
        assert_eq!(table.probe("ac"), None);
        assert_eq!(table.probe(""), None);
    }

    #[test]
    fn test_large_keyword_set() {
        // Test with ~50 keywords to verify CHD handles larger sets.
        let keyword_strs = [
            "abstract", "assert", "boolean", "break", "byte", "case",
            "catch", "char", "class", "const", "continue", "default",
            "do", "double", "else", "enum", "extends", "final",
            "finally", "float", "for", "goto", "if", "implements",
            "import", "instanceof", "int", "interface", "long",
            "native", "new", "package", "private", "protected",
            "public", "return", "short", "static", "strictfp",
            "super", "switch", "synchronized", "this", "throw",
            "throws", "transient", "try", "void", "volatile", "while",
        ];
        let keywords: Vec<(String, usize)> = keyword_strs
            .iter()
            .enumerate()
            .map(|(i, &s)| (s.to_string(), i))
            .collect();
        let table = MphTable::build(&keywords);

        assert_eq!(table.len(), keyword_strs.len());

        for (kw, id) in &keywords {
            assert_eq!(
                table.probe(kw),
                Some(*id),
                "Java keyword '{}' should map to {}",
                kw,
                id
            );
        }

        // Non-keywords
        assert_eq!(table.probe("var"), None);
        assert_eq!(table.probe("let"), None);
        assert_eq!(table.probe("fn"), None);
    }

    #[test]
    fn test_write_mph_tables_empty() {
        let table = MphTable::build(&[]);
        let mut buf = String::new();
        write_mph_tables(&mut buf, &table);

        assert!(buf.contains("fn mph_probe"), "should emit mph_probe function");
        assert!(buf.contains("None"), "empty table probe should return None");
    }

    #[test]
    fn test_write_mph_tables_nonempty() {
        let keywords = vec![
            ("if".to_string(), 0),
            ("else".to_string(), 1),
        ];
        let table = MphTable::build(&keywords);
        let mut buf = String::new();
        write_mph_tables(&mut buf, &table);

        // Should contain the essential components.
        assert!(buf.contains("MPH_FNV_OFFSET_BASIS"), "should emit FNV offset basis");
        assert!(buf.contains("MPH_FNV_PRIME"), "should emit FNV prime");
        assert!(buf.contains("MPH_FNV_SEED2"), "should emit FNV_SEED2 constant");
        assert!(buf.contains("MPH_NUM_BUCKETS"), "should emit num_buckets constant");
        assert!(buf.contains("MPH_TABLE_SIZE"), "should emit table_size constant");
        assert!(buf.contains("MPH_DISPLACEMENTS"), "should emit displacements array");
        assert!(buf.contains("MPH_KEYS"), "should emit keys array");
        assert!(buf.contains("MPH_TOKEN_IDS"), "should emit token_ids array");
        assert!(buf.contains("fn mph_fnv1a"), "should emit fnv1a function");
        assert!(buf.contains("fn mph_probe"), "should emit mph_probe function");
    }

    #[test]
    fn test_build_mph_from_terminals_no_keywords() {
        use super::super::{TerminalPattern, TokenKind};

        let terminals = vec![
            TerminalPattern {
                text: "+".to_string(),
                kind: TokenKind::Fixed("+".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "-".to_string(),
                kind: TokenKind::Fixed("-".to_string()),
                is_keyword: false,
            },
        ];

        assert!(build_mph_from_terminals(&terminals).is_none());
    }

    #[test]
    fn test_build_mph_from_terminals_with_keywords() {
        use super::super::{TerminalPattern, TokenKind};

        let terminals = vec![
            TerminalPattern {
                text: "+".to_string(),
                kind: TokenKind::Fixed("+".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "if".to_string(),
                kind: TokenKind::Fixed("if".to_string()),
                is_keyword: true,
            },
            TerminalPattern {
                text: "else".to_string(),
                kind: TokenKind::Fixed("else".to_string()),
                is_keyword: true,
            },
        ];

        let table = build_mph_from_terminals(&terminals).expect("should find keywords");
        assert_eq!(table.len(), 2);
        // Token IDs should be the indices of the keywords in the terminals array.
        assert_eq!(table.probe("if"), Some(1));
        assert_eq!(table.probe("else"), Some(2));
        assert_eq!(table.probe("+"), None);
    }

    #[test]
    fn test_deterministic_construction() {
        // Building the same keyword set twice should produce identical tables.
        let keywords = vec![
            ("fn".to_string(), 0),
            ("let".to_string(), 1),
            ("mut".to_string(), 2),
        ];
        let table1 = MphTable::build(&keywords);
        let table2 = MphTable::build(&keywords);

        assert_eq!(table1.displacements(), table2.displacements());
        assert_eq!(table1.num_buckets(), table2.num_buckets());
        assert_eq!(table1.table_size(), table2.table_size());

        for (v1, v2) in table1.values().iter().zip(table2.values().iter()) {
            assert_eq!(v1, v2);
        }
    }

    #[test]
    fn test_single_char_keywords() {
        // Edge case: single-character keywords.
        let keywords: Vec<(String, usize)> = ('a'..='z')
            .enumerate()
            .map(|(i, c)| (c.to_string(), i))
            .collect();
        let table = MphTable::build(&keywords);

        assert_eq!(table.len(), 26);
        for (kw, id) in &keywords {
            assert_eq!(
                table.probe(kw),
                Some(*id),
                "single-char keyword '{}' should map to {}",
                kw,
                id
            );
        }
    }
}
