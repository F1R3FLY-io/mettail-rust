mod common;
use common::*;
fn main() {
    let _escaped = with_neutral_target(LIMITS, || false, |mut target| {
        let value = target.construct(ValueOp::Empty, vec![]).expect("leaf");
        Box::new(value) as Box<dyn std::any::Any>
    });
}
