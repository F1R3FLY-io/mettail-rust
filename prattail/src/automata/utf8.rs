//! UTF-8 byte chain decomposition for Unicode codepoint ranges.
//!
//! Decomposes Unicode codepoint ranges into byte-level NFA transitions at
//! compile time, allowing the entire downstream pipeline (partition, subset
//! construction, DFA minimization, codegen, runtime lex loop) to remain
//! unchanged. Zero UTF-8 decoding at lex time.
//!
//! Uses `regex_syntax::utf8::Utf8Sequences` for minimal byte-range chain
//! decomposition and `regex_syntax::unicode::class` for property resolution.

use regex_syntax::utf8::{Utf8Range, Utf8Sequences};

use super::{CharClass, Nfa, NfaFragment, NfaState, StateId};

// ══════════════════════════════════════════════════════════════════════════════
// Byte chain decomposition
// ══════════════════════════════════════════════════════════════════════════════

/// Add byte-level NFA transitions for codepoints in `[start_cp, end_cp]`.
///
/// Uses `Utf8Sequences` to decompose the codepoint range into minimal sets
/// of byte-range chains. Each chain becomes a sequence of NFA transitions:
/// `from →[byte₀]→ s₁ →[byte₁]→ ... →[byteₙ]→ to`.
///
/// Multiple chains (for different byte-length encodings) all share the same
/// `from` and `to` states.
pub fn add_codepoint_range(
    nfa: &mut Nfa,
    from: StateId,
    to: StateId,
    start_cp: char,
    end_cp: char,
) {
    for seq in Utf8Sequences::new(start_cp, end_cp) {
        let ranges: &[Utf8Range] = seq.as_slice();
        match ranges.len() {
            1 => {
                // Single-byte: direct transition from → to
                let r = ranges[0];
                add_byte_range_transition(nfa, from, to, r);
            }
            n => {
                // Multi-byte: chain intermediate states
                // from →[r₀]→ s₁ →[r₁]→ s₂ ... →[rₙ₋₁]→ to
                let mut current = from;
                for (i, &r) in ranges.iter().enumerate() {
                    let next = if i == n - 1 {
                        to
                    } else {
                        nfa.add_state(NfaState::new())
                    };
                    add_byte_range_transition(nfa, current, next, r);
                    current = next;
                }
            }
        }
    }
}

/// Add a single byte-range transition (single byte or range).
#[inline]
fn add_byte_range_transition(nfa: &mut Nfa, from: StateId, to: StateId, r: Utf8Range) {
    if r.start == r.end {
        nfa.add_transition(from, to, CharClass::Single(r.start));
    } else {
        nfa.add_transition(from, to, CharClass::Range(r.start, r.end));
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// NFA fragment construction
// ══════════════════════════════════════════════════════════════════════════════

/// Build an NFA fragment accepting any codepoint in the given ranges.
///
/// Each `(start, end)` pair represents an inclusive codepoint range.
/// All ranges share the same start and accept states; alternation is
/// implicit via multiple transition paths from `start`.
pub fn codepoint_ranges_to_fragment(
    nfa: &mut Nfa,
    ranges: &[(char, char)],
) -> NfaFragment {
    let start = nfa.add_state(NfaState::new());
    let accept = nfa.add_state(NfaState::new());
    for &(lo, hi) in ranges {
        add_codepoint_range(nfa, start, accept, lo, hi);
    }
    NfaFragment { start, accept }
}

// ══════════════════════════════════════════════════════════════════════════════
// Unicode property resolution
// ══════════════════════════════════════════════════════════════════════════════

/// Resolve a Unicode property name to codepoint ranges.
///
/// Supports general categories (`Letter`, `Nd`, ...), binary properties
/// (`XID_Start`, `XID_Continue`, `White_Space`, `Alphabetic`, ...),
/// and scripts (`Latin`, `Greek`, `Cyrillic`, ...).
///
/// Property names are case-insensitive and support aliases (e.g., `L` for
/// `Letter`, `Ll` for `Lowercase_Letter`).
pub fn resolve_property(name: &str) -> Result<Vec<(char, char)>, String> {
    use regex_syntax::hir::{Class, HirKind};

    // Use the regex-syntax parser's public API to resolve Unicode properties.
    // Parsing `\p{Name}` yields an HIR with a Unicode class containing all
    // codepoint ranges for the property.
    let pattern = format!(r"\p{{{}}}", name);
    let hir = regex_syntax::parse(&pattern)
        .map_err(|e| format!("unknown Unicode property '{}': {}", name, e))?;

    match hir.into_kind() {
        HirKind::Class(Class::Unicode(class)) => {
            Ok(class.ranges().iter().map(|r| (r.start(), r.end())).collect())
        }
        _ => Err(format!("unexpected HIR for property '{}'", name)),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Codepoint range complement
// ══════════════════════════════════════════════════════════════════════════════

/// Complement codepoint ranges over `[U+0000, U+10FFFF]` excluding surrogates.
///
/// The valid Unicode scalar value ranges are:
/// - `[U+0000, U+D7FF]`
/// - `[U+E000, U+10FFFF]`
///
/// Surrogates `[U+D800, U+DFFF]` are excluded from both input and output.
pub fn complement_codepoint_ranges(ranges: &[(char, char)]) -> Vec<(char, char)> {
    let merged = sort_and_merge_cp_ranges(ranges);
    let mut complement: Vec<(char, char)> = Vec::with_capacity(merged.len() + 2);

    // Valid scalar value boundaries (surrogates excluded)
    let boundaries: &[(char, char)] = &[('\u{0000}', '\u{D7FF}'), ('\u{E000}', '\u{10FFFF}')];

    for &(seg_lo, seg_hi) in boundaries {
        let mut lo = seg_lo;
        for &(range_lo, range_hi) in &merged {
            // Skip ranges entirely outside this segment
            if range_hi < seg_lo || range_lo > seg_hi {
                continue;
            }
            let clamped_lo = if range_lo > seg_lo { range_lo } else { seg_lo };
            let clamped_hi = if range_hi < seg_hi { range_hi } else { seg_hi };

            if clamped_lo > lo {
                // Gap before this range
                let gap_end =
                    char::from_u32(clamped_lo as u32 - 1).expect("valid codepoint before range");
                if lo <= gap_end {
                    complement.push((lo, gap_end));
                }
            }
            // Advance past this range
            if let Some(next) = char::from_u32(clamped_hi as u32 + 1) {
                if next <= seg_hi {
                    lo = next;
                } else {
                    lo = char::from_u32(seg_hi as u32 + 1).unwrap_or(seg_hi);
                }
            } else {
                lo = char::from_u32(seg_hi as u32 + 1).unwrap_or(seg_hi);
            }
        }
        // Remaining tail of this segment
        if lo <= seg_hi {
            complement.push((lo, seg_hi));
        }
    }

    complement
}

/// Sort and merge overlapping/adjacent codepoint ranges.
pub fn sort_and_merge_cp_ranges(ranges: &[(char, char)]) -> Vec<(char, char)> {
    if ranges.is_empty() {
        return Vec::new();
    }
    let mut sorted = ranges.to_vec();
    sorted.sort_by_key(|&(lo, _)| lo);

    let mut merged: Vec<(char, char)> = Vec::with_capacity(sorted.len());
    let (mut cur_lo, mut cur_hi) = sorted[0];

    for &(lo, hi) in &sorted[1..] {
        if (lo as u32) <= (cur_hi as u32).saturating_add(1) {
            if hi > cur_hi {
                cur_hi = hi;
            }
        } else {
            merged.push((cur_lo, cur_hi));
            cur_lo = lo;
            cur_hi = hi;
        }
    }
    merged.push((cur_lo, cur_hi));
    merged
}

// ══════════════════════════════════════════════════════════════════════════════
// Helpers
// ══════════════════════════════════════════════════════════════════════════════

/// Decode the UTF-8 character at byte position `pos` in a string.
/// Returns `(char, byte_length)` or `None` if at/past end.
pub fn decode_char_at(input: &str, pos: usize) -> Option<(char, usize)> {
    input.get(pos..)?.chars().next().map(|c| (c, c.len_utf8()))
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::{
        minimize::minimize_dfa, partition::compute_equivalence_classes, subset::subset_construction,
        Nfa, TokenKind, DEAD_STATE,
    };

    /// Build a DFA from an NFA and test if a byte sequence is accepted.
    fn nfa_accepts_bytes(nfa: &Nfa, input: &[u8]) -> bool {
        let partition = compute_equivalence_classes(nfa);
        let dfa = subset_construction(nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);
        let mut state = min_dfa.start;
        for &b in input {
            let class = partition.classify(b);
            state = min_dfa.transition(state, class);
            if state == DEAD_STATE {
                return false;
            }
        }
        min_dfa.states[state as usize].accept.is_some()
    }

    // ── Single-byte codepoint (ASCII) ────────────────────────────────────

    #[test]
    fn test_single_byte_codepoint() {
        // U+0041 'A' → single byte 0x41
        let mut nfa = Nfa::new();
        let frag = codepoint_ranges_to_fragment(&mut nfa, &[('A', 'A')]);
        nfa.add_epsilon(nfa.start, frag.start);
        nfa.states[frag.accept as usize].accept = Some(TokenKind::Ident);

        assert!(nfa_accepts_bytes(&nfa, &[0x41]));
        assert!(!nfa_accepts_bytes(&nfa, &[0x42]));
        assert!(!nfa_accepts_bytes(&nfa, &[0x41, 0x41]));
    }

    // ── 2-byte codepoint ─────────────────────────────────────────────────

    #[test]
    fn test_two_byte_codepoint() {
        // U+00E9 'é' → 0xC3 0xA9
        let mut nfa = Nfa::new();
        let frag = codepoint_ranges_to_fragment(&mut nfa, &[('é', 'é')]);
        nfa.add_epsilon(nfa.start, frag.start);
        nfa.states[frag.accept as usize].accept = Some(TokenKind::Ident);

        assert!(nfa_accepts_bytes(&nfa, "é".as_bytes()));
        assert!(!nfa_accepts_bytes(&nfa, &[0xC3])); // incomplete
        assert!(!nfa_accepts_bytes(&nfa, b"e")); // ASCII e
    }

    // ── 3-byte codepoint ─────────────────────────────────────────────────

    #[test]
    fn test_three_byte_codepoint() {
        // U+4E16 '世' → 0xE4 0xB8 0x96
        let mut nfa = Nfa::new();
        let frag = codepoint_ranges_to_fragment(&mut nfa, &[('世', '世')]);
        nfa.add_epsilon(nfa.start, frag.start);
        nfa.states[frag.accept as usize].accept = Some(TokenKind::Ident);

        assert!(nfa_accepts_bytes(&nfa, "世".as_bytes()));
        assert!(!nfa_accepts_bytes(&nfa, &[0xE4, 0xB8])); // incomplete
        assert!(!nfa_accepts_bytes(&nfa, b"a"));
    }

    // ── 4-byte codepoint ─────────────────────────────────────────────────

    #[test]
    fn test_four_byte_codepoint() {
        // U+1F600 '😀' → 0xF0 0x9F 0x98 0x80
        let mut nfa = Nfa::new();
        let frag = codepoint_ranges_to_fragment(&mut nfa, &[('\u{1F600}', '\u{1F600}')]);
        nfa.add_epsilon(nfa.start, frag.start);
        nfa.states[frag.accept as usize].accept = Some(TokenKind::Ident);

        assert!(nfa_accepts_bytes(&nfa, "😀".as_bytes()));
        assert!(!nfa_accepts_bytes(&nfa, &[0xF0, 0x9F, 0x98])); // incomplete
        assert!(!nfa_accepts_bytes(&nfa, b"a"));
    }

    // ── Codepoint range (Greek lowercase α-ω) ───────────────────────────

    #[test]
    fn test_codepoint_range_greek() {
        // U+03B1-U+03C9 (α through ω)
        let mut nfa = Nfa::new();
        let frag = codepoint_ranges_to_fragment(&mut nfa, &[('α', 'ω')]);
        nfa.add_epsilon(nfa.start, frag.start);
        nfa.states[frag.accept as usize].accept = Some(TokenKind::Ident);

        assert!(nfa_accepts_bytes(&nfa, "α".as_bytes()));
        assert!(nfa_accepts_bytes(&nfa, "β".as_bytes()));
        assert!(nfa_accepts_bytes(&nfa, "ω".as_bytes()));
        // Uppercase Greek should not match
        assert!(!nfa_accepts_bytes(&nfa, "Α".as_bytes()));
        // ASCII should not match
        assert!(!nfa_accepts_bytes(&nfa, b"a"));
    }

    // ── Property resolution ──────────────────────────────────────────────

    #[test]
    fn test_resolve_xid_start() {
        let ranges = resolve_property("XID_Start").expect("XID_Start should resolve");
        assert!(!ranges.is_empty());
        // 'a' should be in XID_Start
        assert!(ranges.iter().any(|&(lo, hi)| lo <= 'a' && 'a' <= hi));
        // '0' should NOT be in XID_Start
        assert!(!ranges.iter().any(|&(lo, hi)| lo <= '0' && '0' <= hi));
    }

    #[test]
    fn test_resolve_white_space() {
        let ranges = resolve_property("White_Space").expect("White_Space should resolve");
        assert!(!ranges.is_empty());
        // NBSP (U+00A0) should be in White_Space
        assert!(ranges.iter().any(|&(lo, hi)| lo <= '\u{00A0}' && '\u{00A0}' <= hi));
        // EN QUAD (U+2000) should be in White_Space
        assert!(ranges.iter().any(|&(lo, hi)| lo <= '\u{2000}' && '\u{2000}' <= hi));
        // IDEOGRAPHIC SPACE (U+3000) should be in White_Space
        assert!(ranges.iter().any(|&(lo, hi)| lo <= '\u{3000}' && '\u{3000}' <= hi));
    }

    #[test]
    fn test_resolve_general_category() {
        let ranges = resolve_property("Letter").expect("Letter should resolve");
        assert!(!ranges.is_empty());
        assert!(ranges.iter().any(|&(lo, hi)| lo <= 'a' && 'a' <= hi));
        assert!(ranges.iter().any(|&(lo, hi)| lo <= 'α' && 'α' <= hi));
        assert!(!ranges.iter().any(|&(lo, hi)| lo <= '0' && '0' <= hi));
    }

    #[test]
    fn test_resolve_nd() {
        let ranges = resolve_property("Nd").expect("Nd should resolve");
        assert!(!ranges.is_empty());
        // ASCII digits
        assert!(ranges.iter().any(|&(lo, hi)| lo <= '0' && '0' <= hi));
        // Arabic-Indic digits (U+0660-U+0669)
        assert!(ranges.iter().any(|&(lo, hi)| lo <= '\u{0663}' && '\u{0663}' <= hi));
    }

    #[test]
    fn test_resolve_script() {
        let ranges = resolve_property("Greek").expect("Greek should resolve");
        assert!(!ranges.is_empty());
        assert!(ranges.iter().any(|&(lo, hi)| lo <= 'α' && 'α' <= hi));
        assert!(ranges.iter().any(|&(lo, hi)| lo <= 'Ω' && 'Ω' <= hi));
        assert!(!ranges.iter().any(|&(lo, hi)| lo <= 'a' && 'a' <= hi));
    }

    #[test]
    fn test_resolve_unknown_property() {
        assert!(resolve_property("NoSuchProperty").is_err());
    }

    // ── Complement ───────────────────────────────────────────────────────

    #[test]
    fn test_complement_excludes_range() {
        let complement = complement_codepoint_ranges(&[('A', 'Z')]);
        // 'A'-'Z' should not be in the complement
        assert!(!complement.iter().any(|&(lo, hi)| lo <= 'A' && 'Z' <= hi));
        // But 'a' should be
        assert!(complement.iter().any(|&(lo, hi)| lo <= 'a' && 'a' <= hi));
        // And '0' should be
        assert!(complement.iter().any(|&(lo, hi)| lo <= '0' && '0' <= hi));
    }

    #[test]
    fn test_complement_white_space_excludes_ws() {
        let ws_ranges = resolve_property("White_Space").expect("White_Space should resolve");
        let non_ws = complement_codepoint_ranges(&ws_ranges);
        // Space should not be in non-whitespace
        assert!(!non_ws.iter().any(|&(lo, hi)| lo <= ' ' && ' ' <= hi));
        // 'a' should be in non-whitespace
        assert!(non_ws.iter().any(|&(lo, hi)| lo <= 'a' && 'a' <= hi));
    }

    // ── decode_char_at ───────────────────────────────────────────────────

    #[test]
    fn test_decode_char_at_ascii() {
        assert_eq!(decode_char_at("hello", 0), Some(('h', 1)));
        assert_eq!(decode_char_at("hello", 4), Some(('o', 1)));
    }

    #[test]
    fn test_decode_char_at_multibyte() {
        let s = "café";
        // 'c' at 0 (1 byte)
        assert_eq!(decode_char_at(s, 0), Some(('c', 1)));
        // 'é' at 3 (2 bytes in UTF-8)
        assert_eq!(decode_char_at(s, 3), Some(('é', 2)));
    }

    #[test]
    fn test_decode_char_at_emoji() {
        let s = "a😀b";
        assert_eq!(decode_char_at(s, 0), Some(('a', 1)));
        assert_eq!(decode_char_at(s, 1), Some(('😀', 4)));
        assert_eq!(decode_char_at(s, 5), Some(('b', 1)));
    }

    #[test]
    fn test_decode_char_at_past_end() {
        assert_eq!(decode_char_at("hi", 2), None);
        assert_eq!(decode_char_at("hi", 100), None);
    }
}
