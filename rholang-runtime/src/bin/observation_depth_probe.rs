//! Minimal main-thread depth probe for the unconditional `Par` observation renderer.
//!
//! Unlike `stack_depth_probe`, this binary deliberately does not depend on the generated Rholang
//! language. It isolates observation decoding/rendering and teardown on a directly constructed
//! nested `Par`, so the former `render` slope can be measured without
//! compiling unrelated generated language modules.

use mettail_rholang_runtime::observation::render_par_text;
use mettail_runtime::RuntimeObservationValue;
use models::rust::utils::{new_elist_par, new_gint_par};
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

fn main() {
    let depth = std::env::var("GATE_DEPTH")
        .expect("observation_depth_probe: missing GATE_DEPTH")
        .parse::<usize>()
        .expect("observation_depth_probe: GATE_DEPTH must be an unsigned integer");

    match std::env::var("GATE_SUBJECT").as_deref() {
        Ok("value_traits") => observation_value_traits(depth),
        Ok("render") | Err(_) => render(depth),
        Ok(subject) => panic!("observation_depth_probe: unknown GATE_SUBJECT `{subject}`"),
    }
}

fn render(depth: usize) {
    let mut par = new_gint_par(1, Vec::new(), false);
    for _ in 0..depth {
        par = new_elist_par(vec![par], Vec::new(), false, None, Vec::new(), false);
    }

    let rendered = render_par_text(&par);
    assert!(!rendered.is_empty(), "observation_depth_probe: renderer produced no image");
    if depth > 512 {
        assert!(
            rendered.contains("(elided,"),
            "observation_depth_probe: deep image did not reach the rendering budget"
        );
    }
}

fn observation_value_traits(depth: usize) {
    let mut value = RuntimeObservationValue::Int(1);
    for _ in 0..depth {
        value = RuntimeObservationValue::Term {
            constructor: "Next".into(),
            children: vec![value],
        };
    }

    let cloned = value.clone();
    assert_eq!(value, cloned, "observation_depth_probe: clone/equality image changed");
    assert_eq!(value.cmp(&cloned), std::cmp::Ordering::Equal);

    let mut left_hash = DefaultHasher::new();
    value.hash(&mut left_hash);
    let mut right_hash = DefaultHasher::new();
    cloned.hash(&mut right_hash);
    assert_eq!(left_hash.finish(), right_hash.finish());

    let displayed = value.to_string();
    let debugged = format!("{value:?}");
    assert!(!displayed.is_empty() && !debugged.is_empty());

    // Normal scope exit exercises both explicit destructors on this process's main thread.
}
