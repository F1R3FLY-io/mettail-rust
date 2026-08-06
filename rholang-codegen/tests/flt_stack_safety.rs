use std::collections::BTreeMap;

use mettail_rholang_codegen::{
    reflect_flt_construction, reflect_flt_pattern, reflect_ground_term_par, FltHole, GroundTerm,
    FREE_VAR_REFLECT_LABEL,
};

#[test]
fn deep_flt_pattern_and_construction_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("flt-reflection-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut template =
                GroundTerm::new(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary("hole")]);
            let mut expected = GroundTerm::nullary("Fill");
            for _ in 0..DEPTH {
                template = GroundTerm::new("Node", vec![template]);
                expected = GroundTerm::new("Node", vec![expected]);
            }

            let pattern =
                reflect_flt_pattern(&template, &[FltHole::new("hole")], "flt-stack-safety")
                    .expect("the deep FLT pattern must reflect");
            assert_eq!(pattern.free_count, 1);
            assert_eq!(pattern.hole_bindings, [("hole".to_string(), 0)]);

            let fill = reflect_ground_term_par(&GroundTerm::nullary("Fill"), "flt-stack-safety");
            let fills = BTreeMap::from([("hole".to_string(), fill)]);
            let constructed = reflect_flt_construction(&template, &fills, "flt-stack-safety")
                .expect("the deep FLT construction must reflect");
            let ground = reflect_ground_term_par(&expected, "flt-stack-safety");
            assert_eq!(constructed, ground);

            drop(ground);
            drop(constructed);
            drop(pattern);
            drop(fills);
            drop(expected);
            drop(template);
        })
        .expect("small-stack FLT test thread must spawn");
    handle
        .join()
        .expect("FLT reflection must not overflow the native stack");
}
