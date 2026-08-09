#![cfg(feature = "bench-naive-baseline")]

#[path = "support/receive_count_recursive_oracle.rs"]
mod recursive_oracle;

use mettail_rholang_runtime::bench_support::count_receive_nodes;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EPathMap, Expr, New, Par, Receive};
use std::collections::BTreeMap;

fn receive_par() -> Par {
    Par::default().with_receives(vec![Receive::default()])
}

fn epathmap_par(pathmap: EPathMap) -> Par {
    Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::EPathmapBody(pathmap)),
    }])
}

#[test]
fn receive_counter_streams_each_homogeneous_epathmap_mode() {
    let empty = epathmap_par(EPathMap::default());
    assert_eq!(count_receive_nodes(&empty), 0);
    assert_eq!(count_receive_nodes(&empty), recursive_oracle::count_receive_nodes(&empty));

    let set = epathmap_par(EPathMap::new(vec![receive_par()], Vec::new(), false, None));
    assert_eq!(count_receive_nodes(&set), 1);
    assert_eq!(count_receive_nodes(&set), recursive_oracle::count_receive_nodes(&set));

    let map = epathmap_par(EPathMap::new_map(
        vec![(receive_par(), receive_par())],
        Vec::new(),
        false,
        None,
    ));
    assert_eq!(count_receive_nodes(&map), 2);
    assert_eq!(count_receive_nodes(&map), recursive_oracle::count_receive_nodes(&map));
}

#[test]
fn receive_counter_includes_new_injection_values() {
    let nested = Par::default().with_news(vec![New {
        injections: BTreeMap::from([("rho:test:injection".to_string(), receive_par())]),
        ..New::default()
    }]);

    assert_eq!(count_receive_nodes(&nested), 1);
    assert_eq!(count_receive_nodes(&nested), recursive_oracle::count_receive_nodes(&nested));
}

#[test]
fn receive_counter_is_stack_safe_at_twenty_thousand_levels() {
    std::thread::Builder::new()
        .name("receive-count-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut nested = Par::default();
            for _ in 0..DEPTH {
                nested = Par::default()
                    .with_receives(vec![Receive { body: Some(nested), ..Receive::default() }]);
            }
            assert_eq!(count_receive_nodes(&nested), DEPTH);
        })
        .expect("the small-stack receive-count thread must spawn")
        .join()
        .expect("the iterative receive counter must not overflow a 256 KiB stack");
}
