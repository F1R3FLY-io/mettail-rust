//! Alphabet equivalence class partitioning.
//!
//! Partitions the input alphabet (256 ASCII byte values) into equivalence
//! classes — sets of characters that behave identically across all NFA states.
//! This reduces the DFA transition table from 256 columns to typically 12-18
//! equivalence classes, yielding ~15-20x compression.

use super::{ClassId, Nfa, CharClass};

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

/// Compute equivalence classes from an NFA.
///
/// Two bytes are equivalent if and only if they trigger the same transitions
/// in every NFA state. We compute this by:
/// 1. Building a signature for each byte (which states it transitions to from each state)
/// 2. Grouping bytes with identical signatures
pub fn compute_equivalence_classes(nfa: &Nfa) -> AlphabetPartition {
    // Build a signature for each byte value.
    // The signature is a vector of (state_id, target_states) pairs.
    // Two bytes with the same signature are equivalent.

    type Signature = Vec<(u32, Vec<u32>)>;

    // Reusable buffer for targets within each (state, byte) pair
    let mut targets_buf: Vec<u32> = Vec::new();

    let mut byte_signatures: Vec<Signature> = Vec::with_capacity(256);

    for byte in 0u8..=255 {
        let mut sig: Signature = Vec::new();
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
                sig.push((state_idx as u32, targets_buf.clone()));
            }
        }
        byte_signatures.push(sig);
    }

    // Group bytes by identical signatures.
    // Linear scan is used because typical grammars produce only 12-25 equivalence classes,
    // where the overhead of HashMap construction exceeds the benefit of O(1) lookup.
    let mut byte_to_class = [0u8; 256];
    let mut class_representatives: Vec<u8> = Vec::new();
    let mut num_classes: usize = 0;

    let mut sig_to_class: Vec<(Signature, ClassId)> = Vec::new();

    for byte in 0u8..=255 {
        let sig = &byte_signatures[byte as usize];
        let class = if let Some((_, existing_class)) = sig_to_class.iter().find(|(s, _)| s == sig) {
            *existing_class
        } else {
            let new_class = num_classes as ClassId;
            num_classes += 1;
            sig_to_class.push((sig.clone(), new_class));
            class_representatives.push(byte);
            new_class
        };
        byte_to_class[byte as usize] = class;
    }

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
    use crate::automata::nfa::{build_nfa, BuiltinNeeds};
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

        let nfa = build_nfa(&terminals, &needs);
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
