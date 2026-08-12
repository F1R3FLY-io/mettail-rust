//! Main-thread child probe for the shared production Rholang formula PDA stack gate.
//!
//! The parent integration test constrains this process's stack before `exec`. Keeping the probe
//! separate lets the parent use the standard libtest harness—and therefore Cargo/nextest test
//! discovery—without moving the measured traversal onto libtest's spawned worker thread.

#[path = "formula_pda_carrier.rs"]
mod rholang;

use rholang::{formula, Proc};
use std::{hint::black_box, sync::Arc};

const CHILD_DEPTH: &str = "FORMULA_PDA_GATE_DEPTH";

fn main() {
    let depth = std::env::var(CHILD_DEPTH)
        .expect("formula PDA probe: missing child depth")
        .parse::<usize>()
        .expect("formula PDA probe: child depth must be an unsigned integer");

    let mut root = formula::bool_formula(true);
    for _ in 0..depth {
        root = Proc::Not(Arc::new(root));
    }

    black_box(formula::is_statically_false(&root));
    black_box(formula::is_statically_true(&root));
    black_box(formula::host_matches_verdict(&Proc::PZero, &root));

    // The minimal carrier deliberately retains derived recursive Drop. Production's generated
    // AST has an iterative destructor, so forgetting only removes adapter teardown from this
    // measurement of the shared production traversal.
    std::mem::forget(root);
}
