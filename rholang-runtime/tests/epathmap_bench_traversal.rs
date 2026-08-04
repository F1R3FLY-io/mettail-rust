#![cfg(feature = "bench-naive-baseline")]

use mettail_rholang_runtime::bench_support::count_receive_nodes;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EPathMap, Expr, Par, Receive};

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

    let set = epathmap_par(EPathMap::new(vec![receive_par()], Vec::new(), false, None));
    assert_eq!(count_receive_nodes(&set), 1);

    let map = epathmap_par(EPathMap::new_map(
        vec![(receive_par(), receive_par())],
        Vec::new(),
        false,
        None,
    ));
    assert_eq!(count_receive_nodes(&map), 2);
}
