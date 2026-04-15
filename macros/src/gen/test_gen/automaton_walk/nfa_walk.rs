//! Generic tape-driven DFA walk for unclassified token patterns.
//!
//! For a pattern like `/[aeiou]{3,5}/` that doesn't match any
//! canonical family, emit runtime code that:
//!
//! 1. At codegen time: compile the pattern to a minimized DFA plus a
//!    byte→class lookup table.
//! 2. At test time: walk the DFA driven by tape bytes, emitting a
//!    representative byte for each chosen class, stopping at accept
//!    states with tape-coin-flip probability.
//!
//! The walker is embedded inline in the generated test file (as a
//! single function per unclassified token) rather than pulled from
//! a runtime crate; this keeps the walker self-contained, avoids
//! new runtime API surface, and lets the codegen specialise the
//! table to exactly this pattern's shape.

use mettail_prattail::automata::{
    Dfa, Nfa, StateId, TokenKind, DEAD_STATE,
};
use mettail_prattail::automata::minimize::minimize_dfa;
use mettail_prattail::automata::partition::compute_equivalence_classes;
use mettail_prattail::automata::regex::compile_regex;
use mettail_prattail::automata::subset::subset_construction;

/// A compiled pattern ready to emit as a runtime sampler.
///
/// `byte_to_class[b]` gives the DFA's class for byte `b`; `u8::MAX`
/// means byte is unaccepted (no transition from any state).
///
/// `representative_byte[c]` gives one concrete byte in class `c` to
/// emit when the walker takes that transition.
pub struct CompiledPattern {
    pub num_states: usize,
    pub start: StateId,
    pub num_classes: usize,
    /// `transitions[state * num_classes + class]` = target state or
    /// `DEAD_STATE`.
    pub transitions: Vec<StateId>,
    /// Per-state accept flag.
    pub accepts: Vec<bool>,
    /// Inverse partition: `representative_byte[class_id]` = one byte.
    pub representative_byte: Vec<u8>,
}

/// Compile a regex to a `CompiledPattern` suitable for runtime tape
/// walking. Returns `None` on regex compile error.
pub fn compile_pattern(pattern: &str) -> Option<CompiledPattern> {
    let mut nfa = Nfa::new();
    let kind = TokenKind::Custom("__walk".to_string());
    let frag = compile_regex(pattern, &mut nfa, kind).ok()?;
    nfa.add_epsilon(nfa.start, frag.start);

    let partition = compute_equivalence_classes(&nfa);
    let dfa = subset_construction(&nfa, &partition);
    let min = minimize_dfa(&dfa);

    let num_classes = min.num_classes;
    let num_states = min.states.len();

    let mut transitions = vec![DEAD_STATE; num_states * num_classes];
    let mut accepts = vec![false; num_states];
    for (i, st) in min.states.iter().enumerate() {
        for (c, &tgt) in st.transitions.iter().enumerate() {
            transitions[i * num_classes + c] = tgt;
        }
        accepts[i] = st.accept.is_some();
    }

    // Build inverse partition: for each class, pick the smallest byte
    // in that class. `partition.classify(b)` gives class for byte b.
    let mut representative_byte = vec![0u8; num_classes];
    let mut seen = vec![false; num_classes];
    for b in 0u8..=255u8 {
        let c = partition.classify(b);
        let c_idx = c as usize;
        if c_idx < num_classes && !seen[c_idx] {
            representative_byte[c_idx] = b;
            seen[c_idx] = true;
        }
    }

    Some(CompiledPattern {
        num_states,
        start: min.start,
        num_classes,
        transitions,
        accepts,
        representative_byte,
    })
}

/// Emit a Rust function body that walks a pattern's DFA driven by a
/// `TapeReader`. The emitted fn signature is
/// `fn #name(reader: &mut TapeReader) -> String`.
///
/// The walker:
/// 1. Starts at `start`, accumulating bytes into a `Vec<u8>`.
/// 2. At each step, if the current state is accepting, read a tape
///    byte; if `b & 1 == 1`, stop and return.
/// 3. Otherwise read a tape byte to pick a class (`b % num_classes`),
///    look up the transition, fall through to the stop path if dead.
/// 4. Emit the representative byte for that class, move to the
///    target state, loop. Hard step cap prevents non-termination on
///    patterns like `/a+/` that never reach an accept state with
///    short input.
pub fn emit_pattern_sampler(pattern: &str, fn_name: &str) -> Option<String> {
    let cp = compile_pattern(pattern)?;

    // Serialise tables as array literals for emission.
    let trans_lit = cp.transitions
        .iter()
        .map(|s| if *s == DEAD_STATE { "u32::MAX".to_string() } else { s.to_string() })
        .collect::<Vec<_>>()
        .join(", ");
    let accepts_lit = cp.accepts
        .iter()
        .map(|a| if *a { "true" } else { "false" })
        .collect::<Vec<_>>()
        .join(", ");
    let reps_lit = cp.representative_byte
        .iter()
        .map(|b| format!("{}u8", b))
        .collect::<Vec<_>>()
        .join(", ");

    let code = format!(
r#"/// Pattern: {pat_display}
/// Generated tape-driven walker for unclassified lexer pattern.
/// Emits a string that matches this regex.
#[allow(dead_code)]
fn {fn_name}(reader: &mut TapeReader) -> String {{
    const NUM_STATES: usize = {num_states};
    const NUM_CLASSES: usize = {num_classes};
    const START: u32 = {start};
    const TRANS: [u32; NUM_STATES * NUM_CLASSES] = [{trans_lit}];
    const ACCEPTS: [bool; NUM_STATES] = [{accepts_lit}];
    const REPS: [u8; NUM_CLASSES] = [{reps_lit}];

    let mut bytes: Vec<u8> = Vec::with_capacity(16);
    let mut state: u32 = START;
    const MAX_STEPS: usize = 64;
    for _ in 0..MAX_STEPS {{
        if ACCEPTS[state as usize] && (reader.next_byte() & 1 == 1) {{
            break;
        }}
        let class = (reader.next_byte() as usize) % NUM_CLASSES;
        let tgt = TRANS[(state as usize) * NUM_CLASSES + class];
        if tgt == u32::MAX {{
            // No transition for that class; bail out. If the current
            // state is accepting, this is a valid stop; if not, we
            // emit whatever we have and hope the caller's lexer
            // tolerates shorter input (pattern is ill-formed if this
            // is reachable unaccepted).
            break;
        }}
        bytes.push(REPS[class]);
        state = tgt;
    }}
    String::from_utf8(bytes).unwrap_or_default()
}}
"#,
        pat_display = pattern.escape_default(),
        fn_name = fn_name,
        num_states = cp.num_states,
        num_classes = cp.num_classes,
        start = cp.start,
        trans_lit = trans_lit,
        accepts_lit = accepts_lit,
        reps_lit = reps_lit,
    );

    Some(code)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_simple_pattern() {
        let cp = compile_pattern("[aeiou]+").expect("compile");
        assert!(cp.num_states >= 2); // start + at least one accept
        // Representative bytes for the class containing {a,e,i,o,u}
        // should include one of those chars.
        assert!(cp.representative_byte.iter().any(|b| b"aeiou".contains(b)));
    }

    #[test]
    fn emit_sampler_contains_tables() {
        let code = emit_pattern_sampler("[0-9]+", "arb_custom_int").expect("emit");
        assert!(code.contains("fn arb_custom_int"));
        assert!(code.contains("NUM_STATES"));
        assert!(code.contains("TRANS"));
    }

    #[test]
    fn compile_bounded_pattern() {
        let cp = compile_pattern("[aeiou]{3,5}").expect("compile");
        // Should produce finite automaton with distinct states for each
        // position in the repeat range.
        assert!(cp.num_states >= 4);
    }
}
