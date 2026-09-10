mod common;
use common::*;
fn main() {
    let mut escaped = None;
    with_neutral_target(LIMITS, || false, |mut target| {
        escaped = Some(target.construct(ValueOp::Empty, vec![]).expect("leaf"));
    });
    drop(escaped);
}
