mod common;
use common::*;
fn main() {
    with_neutral_target(LIMITS, || false, |mut outer| {
        let value = outer.construct(ValueOp::Empty, vec![]).expect("leaf");
        with_neutral_target(LIMITS, || false, |mut inner| {
            let _ = inner.forward(value);
        });
    });
}
