use super::*;

#[test]
fn move_based_parallel_composition_matches_append_bytes_and_hash() {
    use prost::Message;
    use std::hash::{Hash, Hasher};

    let mut components = vec![
        send(ground(tag_par("parallel-oracle", "a")), vec![bv(3)]),
        new_scope(1, send(ground(tag_par("parallel-oracle", "b")), vec![bv(0), bv(2)])),
        tagged("parallel-oracle", "C", vec![bv(1)]),
    ];
    // `Par::append` preserves the longer byte-vector representation even when
    // its suffix is clear. That suffix is semantically redundant but protobuf-
    // and hash-visible, so the move-based twin must reproduce it exactly.
    components[2].par.locally_free.extend([0, 0]);
    let expected_free = union_free(
        &components
            .iter()
            .map(|component| component.free.as_slice())
            .collect::<Vec<_>>(),
    );
    let mut expected = Par::default();
    for component in components.iter().cloned() {
        expected = expected.append(component.par);
    }

    let actual = parallel(components);
    let expected_bytes = expected.encode_to_vec();
    let actual_bytes = actual.par.encode_to_vec();
    assert_eq!(actual.free, expected_free);
    assert_eq!(actual_bytes, expected_bytes);

    let hash = |bytes: &[u8]| {
        let mut state = std::collections::hash_map::DefaultHasher::new();
        bytes.hash(&mut state);
        state.finish()
    };
    assert_eq!(hash(&actual_bytes), hash(&expected_bytes));
}

#[test]
fn parallel_composition_handles_twenty_thousand_components_on_a_small_stack() {
    std::thread::Builder::new()
        .name("parallel-composition-stack-gate".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            const WIDTH: usize = 20_000;
            let components = (0..WIDTH).map(|index| {
                send(ground(tag_par("parallel-wide", "channel")), vec![bv(index % 4)])
            });
            let composed = parallel(components);
            assert_eq!(composed.par.sends.len(), WIDTH);
            assert_eq!(composed.free, [0, 1, 2, 3]);
        })
        .expect("spawn parallel-composition stack-gate thread")
        .join()
        .expect("wide parallel composition overflowed or panicked");
}
