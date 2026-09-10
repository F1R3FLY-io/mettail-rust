mod common;
use common::*;
fn main() {
    let _escaped = with_neutral_target(LIMITS, || false, |target| target);
}
