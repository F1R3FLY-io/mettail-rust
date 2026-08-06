use mettail_rholang_codegen::{reflect_ground_term_par, GroundTerm};
use mettail_rholang_runtime::native_contract::par_to_ground_term;

#[test]
fn deep_reflected_term_decode_and_lifecycle_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    const FINGERPRINT: &str = "native-contract-stack-safety";
    let handle = std::thread::Builder::new()
        .name("native-contract-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut expected = GroundTerm::nullary("Leaf");
            for _ in 0..DEPTH {
                expected = GroundTerm::new("Node", vec![expected]);
            }

            let reflected = reflect_ground_term_par(&expected, FINGERPRINT);
            let decoded = par_to_ground_term(&reflected, FINGERPRINT)
                .expect("the deep reflected term must decode");
            assert_eq!(decoded, expected);

            drop(decoded);
            drop(reflected);
            drop(expected);
        })
        .expect("small-stack native-contract test thread must spawn");
    handle
        .join()
        .expect("reflected-term decoding must not overflow the native stack");
}
