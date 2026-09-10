mod common;
use common::*;
fn main() {
    let graph = with_neutral_target(LIMITS, || false, |mut outer| {
        let value = outer.construct(ValueOp::Text("outer".into()), vec![]).expect("leaf");
        let inner_graph = with_neutral_target(LIMITS, || false, |mut inner| {
            let value = inner.construct(ValueOp::Empty, vec![]).expect("leaf");
            inner.finish_graph(value).expect("owned inner graph")
        });
        assert_eq!(inner_graph.node_count(), 1);
        let pair = outer.append(value, value).expect("same-session repeated reference");
        assert!(!outer.observe(&pair).expect("observation").single_string);
        outer.finish_graph(pair).expect("owned outer graph")
    });
    assert_eq!(graph.node_count(), 2);
}
