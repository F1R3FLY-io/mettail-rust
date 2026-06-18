//! M2L (2026-06-17): lazy ≡ eager lex-DAG equivalence gate.
//!
//! Verifies that driving the WPDS walker over a [`LazyLatticeTokenSource`]
//! (on-demand node materialization) produces results OBSERVATIONALLY IDENTICAL
//! to driving it over an eager [`LatticeTokenSource`] (whole-DAG-upfront),
//! across a corpus of full-parse and early-failure inputs, for both the
//! calculator and rhocalc grammars.
//!
//! Two layers of evidence:
//! 1. **Parse-result equivalence** (`assert_parse_eq`): the WPDA parse outcome
//!    — the realized term (by `Debug`) on success, or the error discriminant on
//!    failure — AND the final cursor position are identical between eager and
//!    lazy sources. This is the end-to-end "item 206 verified" gate.
//! 2. **Per-position observation equivalence** (`assert_dag_observations_eq`):
//!    for the full-parse inputs, every `WpdaTokenSource` method (`peek_kind`,
//!    `peek_text`, `peek_alternatives`, `is_ambiguous_at`, `end_byte`,
//!    `next_pos`, `position_order_key`, `eof_node`, `len`) returns the same
//!    value over a FULLY-materialized lazy source as over the eager DAG, for
//!    every node id. This directly confirms node-id-stable equivalence.

use mettail_languages::{calculator, rhocalc};
use mettail_prattail::wpda_runtime::{LatticeTokenSource, WpdaTokenSource};

// ── Corpora ──────────────────────────────────────────────────────────────────

/// Full-parse calculator inputs (should parse to a term).
const CALC_FULL: &[&str] = &[
    "1 + 2 * 3",
    "int(3) == 3",
    "1 - 2 - 3",
    "-3!",
    "(1 + 2) * (3 + 4)",
    "1 + 2 == 3 and 4 == 4",
    "1 ? 2 : 3 ? 4 : 5",
    "1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15 + 16 + 17 + 18 + 19 + 20",
];

/// Early-failure calculator inputs (parse error near the START of the input —
/// the lazy source should materialize only a small prefix of nodes).
const CALC_EARLY_FAIL: &[&str] = &[
    // Garbage operator pile-up right after the first atom of a long input.
    "1 + + + + + + + + + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15 + 16",
    // Unbalanced close delimiters early.
    "} } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } }",
    // Dangling cast open with a long tail of junk.
    "int( + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + + +",
    // Bad leading operator then a long arithmetic tail.
    "* 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15 + 16 + 17 + 18",
];

/// Full-parse rhocalc inputs.
const RHO_FULL: &[&str] = &[
    "{0 | 1 | 2}",
    "new(x,y) in { {x!(0) | y!(1)} }",
    "{0}",
    "{0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19}",
];

/// Early-failure rhocalc inputs.
const RHO_EARLY_FAIL: &[&str] = &[
    "{ } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } }",
    "{0 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |}",
    "new new new new new new new new new new new new new new new new new new new new",
];

// ── Equivalence drivers ────────────────────────────────────────────────────────

/// Drive the calculator WPDA parser over both an eager and a lazy source and
/// assert the parse result (term Debug / error discriminant) and final cursor
/// position match. Returns `(eager_nodes, lazy_nodes_materialized)` for the
/// space metric.
fn calc_parse_eq(input: &str) -> (usize, usize) {
    // Eager.
    let eager_dag = calculator::lex_dag(input);
    let (eager_outcome, eager_pos, eager_node_count) = match eager_dag {
        Ok(dag) => {
            let node_count = dag.nodes.len();
            let source = LatticeTokenSource::new(dag);
            let mut pos = 0usize;
            let outcome = format!("{:?}", calculator::parse_Proc_via_wpda_with_source(&source, &mut pos, 0));
            (outcome, pos, node_count)
        },
        Err(e) => (format!("LEX_ERR({})", e), 0usize, 0usize),
    };

    // Lazy.
    let lazy = calculator::lex_dag_lazy(input);
    let mut lazy_pos = 0usize;
    let lazy_outcome = format!("{:?}", calculator::parse_Proc_via_wpda_with_source(&lazy, &mut lazy_pos, 0));
    let lazy_nodes = lazy.nodes_materialized();

    // For the eager path, a hard lex error means the facade never runs the
    // walker; the lazy source models the same hard-fail by draining at the
    // frontier, so the walker produces an empty/error result. Normalize: if
    // eager lexed OK, the outcomes (term/err discriminant) and pos must match
    // EXACTLY. If eager hard-failed to lex, the lazy walker must also fail to
    // produce an accepted term (it cannot accept what does not lex).
    if eager_outcome.starts_with("LEX_ERR") {
        assert!(
            lazy_outcome.starts_with("Err"),
            "input {:?}: eager hard lex-fail but lazy did not error: lazy={}",
            input,
            lazy_outcome,
        );
    } else {
        assert_eq!(
            eager_outcome, lazy_outcome,
            "PARSE RESULT MISMATCH for calculator input {:?}\n eager: {}\n lazy:  {}",
            input, eager_outcome, lazy_outcome,
        );
        assert_eq!(
            eager_pos, lazy_pos,
            "FINAL POS MISMATCH for calculator input {:?}: eager={} lazy={}",
            input, eager_pos, lazy_pos,
        );
    }
    (eager_node_count, lazy_nodes)
}

/// Same as [`calc_parse_eq`] for rhocalc.
fn rho_parse_eq(input: &str) -> (usize, usize) {
    let eager_dag = rhocalc::lex_dag(input);
    let (eager_outcome, eager_pos, eager_node_count) = match eager_dag {
        Ok(dag) => {
            let node_count = dag.nodes.len();
            let source = LatticeTokenSource::new(dag);
            let mut pos = 0usize;
            let outcome = format!("{:?}", rhocalc::parse_Proc_via_wpda_with_source(&source, &mut pos, 0));
            (outcome, pos, node_count)
        },
        Err(e) => (format!("LEX_ERR({})", e), 0usize, 0usize),
    };

    let lazy = rhocalc::lex_dag_lazy(input);
    let mut lazy_pos = 0usize;
    let lazy_outcome = format!("{:?}", rhocalc::parse_Proc_via_wpda_with_source(&lazy, &mut lazy_pos, 0));
    let lazy_nodes = lazy.nodes_materialized();

    if eager_outcome.starts_with("LEX_ERR") {
        assert!(
            lazy_outcome.starts_with("Err"),
            "input {:?}: eager hard lex-fail but lazy did not error: lazy={}",
            input,
            lazy_outcome,
        );
    } else {
        assert_eq!(
            eager_outcome, lazy_outcome,
            "PARSE RESULT MISMATCH for rhocalc input {:?}\n eager: {}\n lazy:  {}",
            input, eager_outcome, lazy_outcome,
        );
        assert_eq!(
            eager_pos, lazy_pos,
            "FINAL POS MISMATCH for rhocalc input {:?}: eager={} lazy={}",
            input, eager_pos, lazy_pos,
        );
    }
    (eager_node_count, lazy_nodes)
}

/// Compare every `WpdaTokenSource` observation over a fully-materialized lazy
/// source against the eager DAG, node by node. This is the strongest
/// node-id-stability evidence. Only meaningful for inputs that lex OK.
fn assert_dag_observations_eq_calc(input: &str) {
    let Ok(dag) = calculator::lex_dag(input) else {
        return;
    };
    let eager = LatticeTokenSource::new(dag);
    let lazy = calculator::lex_dag_lazy(input);
    // Force the lazy source to materialize the WHOLE DAG so node ids line up
    // for an exhaustive comparison.
    lazy.force_full_materialization();

    assert_eq!(
        eager.len(),
        lazy.len(),
        "node count mismatch for {:?}: eager={} lazy={}",
        input,
        eager.len(),
        lazy.len(),
    );
    assert_eq!(
        eager.eof_node(),
        lazy.eof_node(),
        "eof_node mismatch for {:?}: eager={} lazy={}",
        input,
        eager.eof_node(),
        lazy.eof_node(),
    );
    for pos in 0..eager.len() {
        assert_eq!(
            eager.peek_kind(pos),
            lazy.peek_kind(pos),
            "peek_kind mismatch at node {} for {:?}",
            pos,
            input,
        );
        assert_eq!(
            eager.peek_text(pos),
            lazy.peek_text(pos),
            "peek_text mismatch at node {} for {:?}",
            pos,
            input,
        );
        assert_eq!(
            eager.is_ambiguous_at(pos),
            lazy.is_ambiguous_at(pos),
            "is_ambiguous_at mismatch at node {} for {:?}",
            pos,
            input,
        );
        assert_eq!(
            eager.position_order_key(pos),
            lazy.position_order_key(pos),
            "position_order_key (byte_start) mismatch at node {} for {:?}",
            pos,
            input,
        );
        // Primary + secondary alt edges: end_byte and next_pos per alt index.
        let eager_alts = eager.peek_alternatives(pos);
        let lazy_alts = lazy.peek_alternatives(pos);
        assert_eq!(
            eager_alts.len(),
            lazy_alts.len(),
            "secondary-alt count mismatch at node {} for {:?}",
            pos,
            input,
        );
        for (ea, la) in eager_alts.iter().zip(lazy_alts.iter()) {
            assert_eq!(ea.kind, la.kind, "alt kind mismatch at node {} for {:?}", pos, input);
            assert_eq!(ea.text, la.text, "alt text mismatch at node {} for {:?}", pos, input);
            assert_eq!(
                ea.end_byte, la.end_byte,
                "alt end_byte mismatch at node {} for {:?}",
                pos, input,
            );
        }
        // Per-alt end_byte and next_pos (target node), over all edge slots.
        for alt_idx in 0..(eager_alts.len() + 2) {
            assert_eq!(
                eager.end_byte(pos, alt_idx),
                lazy.end_byte(pos, alt_idx),
                "end_byte mismatch at node {} alt {} for {:?}",
                pos, alt_idx, input,
            );
            assert_eq!(
                eager.next_pos(pos, alt_idx),
                lazy.next_pos(pos, alt_idx),
                "next_pos (target_node) mismatch at node {} alt {} for {:?}",
                pos, alt_idx, input,
            );
        }
    }
}

// ── Tests ──────────────────────────────────────────────────────────────────────

#[test]
fn calc_full_parse_lazy_eq_eager() {
    for &input in CALC_FULL {
        let (eager_nodes, lazy_nodes) = calc_parse_eq(input);
        // On full-parse inputs the walker reaches EOF, so lazy materializes
        // essentially the whole DAG — no fewer nodes than make a difference,
        // but never MORE than eager.
        assert!(
            lazy_nodes <= eager_nodes,
            "lazy materialized MORE nodes than eager for {:?}: lazy={} eager={}",
            input, lazy_nodes, eager_nodes,
        );
    }
}

#[test]
fn calc_early_fail_lazy_eq_eager() {
    for &input in CALC_EARLY_FAIL {
        let (eager_nodes, lazy_nodes) = calc_parse_eq(input);
        assert!(
            lazy_nodes <= eager_nodes,
            "lazy materialized MORE nodes than eager for {:?}: lazy={} eager={}",
            input, lazy_nodes, eager_nodes,
        );
    }
}

#[test]
fn calc_full_parse_observation_eq() {
    for &input in CALC_FULL {
        assert_dag_observations_eq_calc(input);
    }
}

#[test]
fn calc_early_fail_observation_eq() {
    // The observation comparison force-materializes the lazy DAG, so it covers
    // the tail too — confirming node-id stability even where the parser never
    // reached.
    for &input in CALC_EARLY_FAIL {
        assert_dag_observations_eq_calc(input);
    }
}

#[test]
fn rho_full_parse_lazy_eq_eager() {
    for &input in RHO_FULL {
        let (eager_nodes, lazy_nodes) = rho_parse_eq(input);
        assert!(
            lazy_nodes <= eager_nodes,
            "lazy materialized MORE nodes than eager for {:?}: lazy={} eager={}",
            input, lazy_nodes, eager_nodes,
        );
    }
}

#[test]
fn rho_early_fail_lazy_eq_eager() {
    for &input in RHO_EARLY_FAIL {
        let (eager_nodes, lazy_nodes) = rho_parse_eq(input);
        assert!(
            lazy_nodes <= eager_nodes,
            "lazy materialized MORE nodes than eager for {:?}: lazy={} eager={}",
            input, lazy_nodes, eager_nodes,
        );
    }
}

/// Report the space metric: nodes the eager DAG builds vs nodes the lazy source
/// materializes for the SAME parse, for every corpus input. Printed with
/// `--nocapture`. This is the `lex_nodes_materialized` control-vs-treatment
/// measurement.
#[test]
fn report_nodes_materialized() {
    println!("\n=== lex_nodes_materialized: eager(control) vs lazy(treatment) ===");
    println!("--- calculator FULL-PARSE ---");
    for &input in CALC_FULL {
        let (eager, lazy) = calc_parse_eq(input);
        println!(
            "eager_nodes={:>4}  lazy_nodes={:>4}  saved={:>4}  input={:?}",
            eager,
            lazy,
            eager as i64 - lazy as i64,
            truncate(input, 48),
        );
    }
    println!("--- calculator EARLY-FAILURE ---");
    for &input in CALC_EARLY_FAIL {
        let (eager, lazy) = calc_parse_eq(input);
        println!(
            "eager_nodes={:>4}  lazy_nodes={:>4}  saved={:>4}  input={:?}",
            eager,
            lazy,
            eager as i64 - lazy as i64,
            truncate(input, 48),
        );
    }
    println!("--- rhocalc FULL-PARSE ---");
    for &input in RHO_FULL {
        let (eager, lazy) = rho_parse_eq(input);
        println!(
            "eager_nodes={:>4}  lazy_nodes={:>4}  saved={:>4}  input={:?}",
            eager,
            lazy,
            eager as i64 - lazy as i64,
            truncate(input, 48),
        );
    }
    println!("--- rhocalc EARLY-FAILURE ---");
    for &input in RHO_EARLY_FAIL {
        let (eager, lazy) = rho_parse_eq(input);
        println!(
            "eager_nodes={:>4}  lazy_nodes={:>4}  saved={:>4}  input={:?}",
            eager,
            lazy,
            eager as i64 - lazy as i64,
            truncate(input, 48),
        );
    }
}

/// Focused probe for the cast-then-compare divergence. Drives the lazy parse
/// for `int(3) == 3`, then dumps the lazy (post-parse, partially materialized)
/// vs eager (full) DAG observations so we can see WHERE on-demand lazy diverges.
#[test]
#[ignore]
fn probe_int_cast_compare() {
    let input = "int(3) == 3";
    // Eager full DAG.
    let dag = calculator::lex_dag(input).expect("lex");
    let eager = LatticeTokenSource::new(dag);
    println!("\n=== EAGER DAG for {:?} ===", input);
    for pos in 0..eager.len() {
        println!(
            "node {:>2}: byte_start={:?} kind={:?} text={:?} alts={} next0={:?}",
            pos,
            eager.position_order_key(pos),
            eager.peek_kind(pos),
            eager.peek_text(pos),
            eager.peek_alternatives(pos).len(),
            eager.next_pos(pos, 0),
        );
    }
    println!("eager eof_node={} len={}", eager.eof_node(), eager.len());

    // Lazy: drive the parse, observe what got materialized + eof_node timing.
    let lazy = calculator::lex_dag_lazy(input);
    let mut pos = 0usize;
    let r = calculator::parse_Proc_via_wpda_with_source(&lazy, &mut pos, 0);
    println!("\n=== LAZY parse result for {:?} ===", input);
    println!("result={:?}\nfinal_pos={} eof_node={} nodes_materialized={}", r, pos, lazy.eof_node(), lazy.nodes_materialized());
    // Now force-materialize and dump for comparison.
    lazy.force_full_materialization();
    println!("\n=== LAZY DAG (forced full) for {:?} ===", input);
    for pos in 0..lazy.len() {
        println!(
            "node {:>2}: byte_start={:?} kind={:?} text={:?} alts={} next0={:?}",
            pos,
            lazy.position_order_key(pos),
            lazy.peek_kind(pos),
            lazy.peek_text(pos),
            lazy.peek_alternatives(pos).len(),
            lazy.next_pos(pos, 0),
        );
    }
    println!("lazy eof_node={} len={}", lazy.eof_node(), lazy.len());
}

fn truncate(s: &str, n: usize) -> String {
    if s.len() <= n {
        s.to_string()
    } else {
        format!("{}…", &s[..n])
    }
}
