//! Regression for result-category Pratt floors across closed primaries.

#[path = "definitions/cross_category_pratt_floor_demo.rs"]
mod cross_category_pratt_floor_demo;
#[path = "definitions/led_test.rs"]
mod ledtest;

use cross_category_pratt_floor_demo::Proc as DemoProc;
use ledtest::Expr;

/// A self-delimited cross-category primary completed on the right-hand side
/// of `|` must resume at that operator's saved right-binding floor. Resetting
/// the floor to zero admits the second `|` inside the right operand and yields
/// an additional right-associated tree. LedTest intentionally retains other
/// lexical and projection ambiguities, so this gate classifies every returned
/// tree instead of assuming a parse count unrelated to associativity.
#[test]
fn closed_cross_category_primary_preserves_enclosing_pratt_floor() {
    mettail_runtime::clear_var_cache();
    let (alternatives, weights) = Expr::parse_via_wpda_all_with_weights("true | to_num(x) | true")
        .expect("the closed cross-category primary chain parses");

    assert!(!alternatives.is_empty());
    assert_eq!(weights.len(), alternatives.len());
    for alternative in alternatives {
        let rendered = format!("{alternative:?}");
        assert!(
            rendered.contains("ExprToNum("),
            "the corpus must traverse the closed cross-category primary: {rendered}",
        );
        assert!(
            rendered.starts_with("EPar(EPar("),
            "the only association must be left-associative: {rendered}",
        );
    }
}

/// The phase partition changes only which generated dispatch table owns a
/// led production; it must not reintroduce native-stack recursion while the
/// parser carries the right-binding floor through a long chain. Inspecting
/// the left spine iteratively also distinguishes the required association
/// without recursively formatting or comparing the generated tree.
#[test]
fn closed_cross_category_primary_is_stack_safe_in_a_deep_led_chain() {
    const OPERATOR_COUNT: usize = 20_000;

    std::thread::Builder::new()
        .name("cross-category-pratt-floor-20k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            mettail_runtime::clear_var_cache();
            let mut source = String::with_capacity(8 + OPERATOR_COUNT * 4);
            source.push_str("n!(p)");
            for _ in 1..OPERATOR_COUNT {
                source.push_str(" | p");
            }

            let alternative =
                DemoProc::parse(&source).expect("the deep cross-category led chain parses");

            let mut left_spine = &alternative;
            let mut observed = 0usize;
            while let DemoProc::Parallel(left, _) = left_spine {
                observed += 1;
                left_spine = left.as_ref();
            }
            assert_eq!(
                observed,
                OPERATOR_COUNT - 1,
                "a right-associated operator escaped the enclosing Pratt floor",
            );
        })
        .expect("the bounded-stack verification thread starts")
        .join()
        .expect("the parser remains safe on a 256 KiB native stack");
}

/// Controlled profiling entry point for the deep-led memory investigation.
///
/// This test is ignored during ordinary verification. Its environment tuple
/// selects one cell of the same/cross-category, deterministic/ambiguous, and
/// parse-one/parse-all matrix without changing the generated parser:
///
/// - `METTAIL_PRATT_PROFILE_GRAMMAR=demo|led`
/// - `METTAIL_PRATT_PROFILE_MODE=one|all-facade|all-monolithic`
/// - `METTAIL_PRATT_PROFILE_SHAPE=same|cross`
/// - `METTAIL_PRATT_PROFILE_DEPTH=<positive operand count>`
///
/// Build with the `walker-stats` feature and set `PRATTAIL_WALKER_STATS=1` to
/// obtain the existing internal cardinality and memory-attribution report.
#[test]
#[ignore = "manual bounded profiler/cardinality harness"]
fn profile_deep_led_chain_mode() {
    let grammar =
        std::env::var("METTAIL_PRATT_PROFILE_GRAMMAR").unwrap_or_else(|_| "led".to_string());
    let mode = std::env::var("METTAIL_PRATT_PROFILE_MODE")
        .unwrap_or_else(|_| "all-monolithic".to_string());
    let shape =
        std::env::var("METTAIL_PRATT_PROFILE_SHAPE").unwrap_or_else(|_| "cross".to_string());
    let depth = std::env::var("METTAIL_PRATT_PROFILE_DEPTH")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(100);
    assert!(depth > 0, "profile depth is an operand count and must be positive");

    mettail_runtime::clear_var_cache();
    let started = std::time::Instant::now();

    let (accepted, alternatives, error) = match grammar.as_str() {
        "demo" => {
            let mut source = String::with_capacity(depth.saturating_mul(4).saturating_add(8));
            match shape.as_str() {
                "same" => source.push('p'),
                "cross" => source.push_str("n!(p)"),
                other => panic!("unknown profile shape {other:?}"),
            }
            for _ in 1..depth {
                source.push_str(" | p");
            }

            match mode.as_str() {
                "one" => match DemoProc::parse_via_wpda(&source) {
                    Ok(_) => (true, 1, None),
                    Err(problem) => (false, 0, Some(problem.to_string())),
                },
                "all-facade" => match DemoProc::parse_via_wpda_all_with_weights(&source) {
                    Ok((terms, weights)) => {
                        assert_eq!(terms.len(), weights.len());
                        (true, terms.len(), None)
                    },
                    Err(problem) => (false, 0, Some(problem.to_string())),
                },
                "all-monolithic" => match DemoProc::__all_with_weights_monolithic(&source) {
                    Ok((terms, weights)) => {
                        assert_eq!(terms.len(), weights.len());
                        (true, terms.len(), None)
                    },
                    Err(problem) => (false, 0, Some(problem.to_string())),
                },
                other => panic!("unknown profile mode {other:?}"),
            }
        },
        "led" => {
            let mut source = String::with_capacity(depth.saturating_mul(7).saturating_add(16));
            source.push_str("true");
            for operand in 1..depth {
                if shape == "cross" && operand == 1 {
                    source.push_str(" | to_num(x)");
                } else {
                    source.push_str(" | true");
                }
            }
            assert!(matches!(shape.as_str(), "same" | "cross"), "unknown profile shape {shape:?}",);

            match mode.as_str() {
                "one" => match Expr::parse_via_wpda(&source) {
                    Ok(_) => (true, 1, None),
                    Err(problem) => (false, 0, Some(problem.to_string())),
                },
                "all-facade" => match Expr::parse_via_wpda_all_with_weights(&source) {
                    Ok((terms, weights)) => {
                        assert_eq!(terms.len(), weights.len());
                        (true, terms.len(), None)
                    },
                    Err(problem) => (false, 0, Some(problem.to_string())),
                },
                "all-monolithic" => match Expr::__all_with_weights_monolithic(&source) {
                    Ok((terms, weights)) => {
                        assert_eq!(terms.len(), weights.len());
                        (true, terms.len(), None)
                    },
                    Err(problem) => (false, 0, Some(problem.to_string())),
                },
                other => panic!("unknown profile mode {other:?}"),
            }
        },
        other => panic!("unknown profile grammar {other:?}"),
    };

    eprintln!(
        "PROFILE_RESULT grammar={grammar} mode={mode} shape={shape} depth={depth} \
         accepted={accepted} alternatives={alternatives} elapsed_ms={} error={error:?}",
        started.elapsed().as_millis(),
    );
}
