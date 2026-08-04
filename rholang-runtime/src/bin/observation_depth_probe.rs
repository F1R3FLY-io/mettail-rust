//! Minimal main-thread depth probe for the unconditional `Par` observation renderer.
//!
//! Unlike `stack_depth_probe`, this binary deliberately does not depend on the generated Rholang
//! language. It isolates observation decoding/rendering and teardown on a directly constructed
//! nested `Par`, so the former `render` slope can be measured without
//! compiling unrelated generated language modules.

use mettail_rholang_runtime::observation::render_par_text;
use models::rust::utils::{new_elist_par, new_gint_par};

fn main() {
    let depth = std::env::var("GATE_DEPTH")
        .expect("observation_depth_probe: missing GATE_DEPTH")
        .parse::<usize>()
        .expect("observation_depth_probe: GATE_DEPTH must be an unsigned integer");

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
