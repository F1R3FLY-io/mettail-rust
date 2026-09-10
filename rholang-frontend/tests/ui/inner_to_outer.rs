mod common;
use common::*;
fn main() {
    with_neutral_target(LIMITS, || false, |mut outer| {
        with_neutral_target(LIMITS, || false, |mut inner| {
            let value = inner.construct(ValueOp::Empty, vec![]).expect("leaf");
            let _ = outer.forward(value);
        });
    });
}
