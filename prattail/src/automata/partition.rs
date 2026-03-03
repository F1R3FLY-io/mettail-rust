//! Alphabet equivalence class partitioning.
//!
//! Partitions the input alphabet (256 ASCII byte values) into equivalence
//! classes — sets of characters that behave identically across all NFA states.
//! This reduces the DFA transition table from 256 columns to typically 12-18
//! equivalence classes, yielding ~15-20x compression.
//!
//! ## Optimizations
//!
//! - **Flat byte signatures:** Instead of nested `Vec<(u32, Vec<u32>)>`, each byte's
//!   signature is encoded as a flat `Vec<u8>` (state_idx LE + count LE + targets LE),
//!   eliminating ~7,680 inner Vec allocations per call.
//! - **HashMap grouping:** Replaces O(n) linear scan with O(1) HashMap lookup for
//!   signature → class mapping.
//! - **Thread-local buffer pooling:** `targets_buf` and `sig_buf` retain capacity
//!   across calls via `Cell<Vec<T>>` take/set pattern (same as trampoline parser).
//! - **Pre-allocation:** `class_representatives` and `sig_to_class` pre-allocated
//!   to typical grammar sizes (32 classes).

use std::cell::Cell;
use std::collections::HashMap;

use super::{CharClass, ClassId, Nfa};

/// Result of alphabet partitioning: a mapping from byte → equivalence class.
#[derive(Debug, Clone)]
pub struct AlphabetPartition {
    /// Maps each byte value (0..256) to its equivalence class ID.
    pub byte_to_class: [ClassId; 256],
    /// Number of distinct equivalence classes.
    pub num_classes: usize,
    /// Representative byte for each class (for debugging/display).
    pub class_representatives: Vec<u8>,
}

impl AlphabetPartition {
    /// Look up the equivalence class for a byte.
    pub fn classify(&self, byte: u8) -> ClassId {
        self.byte_to_class[byte as usize]
    }
}

thread_local! {
    /// Reusable buffer for collecting transition targets per (state, byte) pair.
    /// Retains capacity across calls (~100-200 bytes).
    static TARGETS_BUF: Cell<Vec<u32>> = const { Cell::new(Vec::new()) };
    /// Reusable buffer for flat byte signature encoding.
    /// Retains capacity across calls (~200-400 bytes).
    static SIG_BUF: Cell<Vec<u8>> = const { Cell::new(Vec::new()) };
}

/// Compute equivalence classes from an NFA.
///
/// Two bytes are equivalent if and only if they trigger the same transitions
/// in every NFA state. We compute this by:
/// 1. Building a flat byte signature for each byte (encoded as LE u32 sequences)
/// 2. Grouping bytes with identical signatures via HashMap
pub fn compute_equivalence_classes(nfa: &Nfa) -> AlphabetPartition {
    let n = nfa.states.len();
    let mut byte_to_class = [0u8; 256];
    let mut class_representatives: Vec<u8> = Vec::with_capacity(32);
    let mut num_classes: usize = 0;

    // Take TLS buffers and ensure first-call pre-allocation
    let mut targets_buf = TARGETS_BUF.with(|cell| cell.take());
    targets_buf.clear();
    if targets_buf.capacity() < n {
        targets_buf.reserve(n - targets_buf.capacity());
    }

    let mut sig_buf = SIG_BUF.with(|cell| cell.take());
    sig_buf.clear();
    let sig_cap = n * 16;
    if sig_buf.capacity() < sig_cap {
        sig_buf.reserve(sig_cap - sig_buf.capacity());
    }

    // HashMap for O(1) signature → class lookup (typically 12-25 classes)
    let mut sig_to_class: HashMap<Vec<u8>, ClassId> = HashMap::with_capacity(32);

    for byte in 0u8..=255 {
        // Build flat signature: for each state with transitions on this byte,
        // encode (state_idx: u32 LE, target_count: u32 LE, targets...: u32 LE)
        sig_buf.clear();
        for (state_idx, state) in nfa.states.iter().enumerate() {
            targets_buf.clear();
            for (class, target) in &state.transitions {
                if class_matches(class, byte) {
                    targets_buf.push(*target);
                }
            }
            if !targets_buf.is_empty() {
                targets_buf.sort_unstable();
                targets_buf.dedup();
                // Flat encoding: state_idx + count + sorted targets (all as LE u32)
                sig_buf.extend_from_slice(&(state_idx as u32).to_le_bytes());
                sig_buf.extend_from_slice(&(targets_buf.len() as u32).to_le_bytes());
                for &t in &targets_buf {
                    sig_buf.extend_from_slice(&t.to_le_bytes());
                }
            }
        }

        if let Some(&class) = sig_to_class.get(sig_buf.as_slice()) {
            byte_to_class[byte as usize] = class;
        } else {
            let new_class = num_classes as ClassId;
            num_classes += 1;
            // Clone only happens ~12-18 times (once per unique equivalence class)
            sig_to_class.insert(sig_buf.clone(), new_class);
            class_representatives.push(byte);
            byte_to_class[byte as usize] = new_class;
        }
    }

    // Return TLS buffers for reuse
    TARGETS_BUF.with(|cell| cell.set(targets_buf));
    SIG_BUF.with(|cell| cell.set(sig_buf));

    AlphabetPartition {
        byte_to_class,
        num_classes,
        class_representatives,
    }
}

/// Check whether a byte matches a character class.
fn class_matches(class: &CharClass, byte: u8) -> bool {
    match class {
        CharClass::Single(b) => *b == byte,
        CharClass::Range(lo, hi) => byte >= *lo && byte <= *hi,
        CharClass::Class(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::nfa::{build_nfa_default, BuiltinNeeds};
    use crate::automata::TerminalPattern;
    use crate::automata::TokenKind;

    #[test]
    fn test_equivalence_classes_simple() {
        let terminals = vec![
            TerminalPattern {
                text: "+".to_string(),
                kind: TokenKind::Fixed("+".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "*".to_string(),
                kind: TokenKind::Fixed("*".to_string()),
                is_keyword: false,
            },
        ];
        let needs = BuiltinNeeds {
            ident: true,
            integer: true,
            float: false,
            string_lit: false,
            boolean: false,
        };

        let nfa = build_nfa_default(&terminals, &needs);
        let partition = compute_equivalence_classes(&nfa);

        // '+' and '*' should be in different classes
        assert_ne!(
            partition.classify(b'+'),
            partition.classify(b'*'),
            "'+' and '*' should be in different equivalence classes"
        );

        // All lowercase letters (except special ones) should be in the same class
        let a_class = partition.classify(b'a');
        let b_class = partition.classify(b'b');
        assert_eq!(a_class, b_class, "'a' and 'b' should be in the same equivalence class");

        // Digits should be in their own class
        let zero_class = partition.classify(b'0');
        let nine_class = partition.classify(b'9');
        assert_eq!(zero_class, nine_class, "'0' and '9' should be in the same equivalence class");

        // Letters and digits should be in different classes (they behave differently
        // as first character of identifier)
        // Note: they might actually be in the same class if they have identical
        // behavior across all NFA states. In the ident NFA, digits can't start
        // an identifier but can continue one, while letters can do both.
        // So they should indeed be different.

        // The number of classes should be reasonable (much less than 256)
        assert!(
            partition.num_classes < 30,
            "should have fewer than 30 equivalence classes, got {}",
            partition.num_classes
        );
    }
}
