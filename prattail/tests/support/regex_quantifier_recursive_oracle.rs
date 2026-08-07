//! Bounded reference equations for regex quantifier NFA construction.
//!
//! The historical helper cycle is intentionally retained only in this test
//! module. Its recursive edge is semantically bounded to one re-entry because
//! bounded repetition calls back with only `Star` or `Optional`.

use super::*;

pub(super) fn apply(nfa: &mut Nfa, frag: NfaFragment, kind: &QuantifyKind) -> NfaFragment {
    match kind {
        QuantifyKind::Star => {
            let new_start = nfa.add_state(NfaState::new());
            let new_accept = nfa.add_state(NfaState::new());
            nfa.add_epsilon(new_start, frag.start);
            nfa.add_epsilon(new_start, new_accept);
            nfa.add_epsilon(frag.accept, frag.start);
            nfa.add_epsilon(frag.accept, new_accept);
            NfaFragment { start: new_start, accept: new_accept }
        },
        QuantifyKind::Plus => {
            let new_start = nfa.add_state(NfaState::new());
            let new_accept = nfa.add_state(NfaState::new());
            nfa.add_epsilon(new_start, frag.start);
            nfa.add_epsilon(frag.accept, frag.start);
            nfa.add_epsilon(frag.accept, new_accept);
            NfaFragment { start: new_start, accept: new_accept }
        },
        QuantifyKind::Optional => {
            let new_start = nfa.add_state(NfaState::new());
            let new_accept = nfa.add_state(NfaState::new());
            nfa.add_epsilon(new_start, frag.start);
            nfa.add_epsilon(new_start, new_accept);
            nfa.add_epsilon(frag.accept, new_accept);
            NfaFragment { start: new_start, accept: new_accept }
        },
        QuantifyKind::Repeat { min, max } => apply_bounded_repeat(nfa, frag, *min, *max),
    }
}

fn apply_bounded_repeat(
    nfa: &mut Nfa,
    frag: NfaFragment,
    min: u32,
    max: Option<u32>,
) -> NfaFragment {
    if min == 0 && max == Some(0) {
        let state = nfa.add_state(NfaState::new());
        return NfaFragment { start: state, accept: state };
    }

    let mut copies = Vec::with_capacity(min as usize + 4);
    for _ in 0..min {
        copies.push(clone_fragment(nfa, &frag));
    }

    match max {
        None => {
            let star_copy = clone_fragment(nfa, &frag);
            copies.push(apply(nfa, star_copy, &QuantifyKind::Star));
        },
        Some(maximum) => {
            for _ in 0..(maximum - min) {
                let optional_copy = clone_fragment(nfa, &frag);
                copies.push(apply(nfa, optional_copy, &QuantifyKind::Optional));
            }
        },
    }

    if copies.is_empty() {
        let state = nfa.add_state(NfaState::new());
        NfaFragment { start: state, accept: state }
    } else {
        let mut result = copies.remove(0);
        for next in copies {
            nfa.add_epsilon(result.accept, next.start);
            result = NfaFragment { start: result.start, accept: next.accept };
        }
        result
    }
}
