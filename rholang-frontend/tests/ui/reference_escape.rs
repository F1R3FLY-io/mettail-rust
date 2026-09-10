mod common;
use common::*;
fn main() {
    let _escaped = with_neutral_target(LIMITS, || false, |mut target| {
        target.construct(ValueOp::Empty, vec![]).expect("leaf")
    });
}
