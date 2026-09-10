use super::*;

#[test]
fn fresh_descriptors_preserve_exact_fields_and_emitted_count_boundaries() {
    for binder_count in [0, 1, 3, i32::MAX as usize] {
        let descriptor = CheckedFreshDescriptor::new(FreshShape::Plain { binder_count }, vec![])
            .expect("representable count without constructing a large body");
        assert_eq!(descriptor.binder_count(), binder_count);
        assert_eq!(descriptor.arity(), 1);
        assert_eq!(descriptor.into_parts(), (binder_count as i32, vec![], vec![]));
    }
    for count in [i32::MAX as usize + 1, usize::MAX] {
        assert_eq!(
            CheckedFreshDescriptor::new(FreshShape::Plain { binder_count: count }, vec![]),
            Err(ConstructionError::TargetIndexOutOfRange { index: count })
        );
    }
    let uris = vec!["a".into(), "z".into(), "é".into()];
    let keys = vec!["".into(), "unused".into()];
    let descriptor = CheckedFreshDescriptor::new(
        FreshShape::Uri { binder_count: 3, uris: uris.clone() },
        keys.clone(),
    )
    .expect("normalized URI and independent injection roster");
    assert_eq!(descriptor.arity(), 3);
    assert_eq!(descriptor.into_parts(), (3, uris, keys));
}

#[test]
fn fresh_descriptors_reject_invalid_layout_before_count_and_do_not_sort() {
    for (binder_count, uris) in [
        (0, vec![]),
        (1, vec![""]),
        (2, vec!["a"]),
        (1, vec!["a", "b"]),
        (2, vec!["a", "a"]),
        (2, vec!["b", "a"]),
        (usize::MAX, vec![]),
    ] {
        assert_eq!(
            CheckedFreshDescriptor::new(
                FreshShape::Uri {
                    binder_count,
                    uris: uris.into_iter().map(str::to_owned).collect(),
                },
                vec![],
            ),
            Err(ConstructionError::InvalidBinderLayout)
        );
    }
    for keys in [vec!["a", "a"], vec!["z", "a"], vec!["a", ""]] {
        assert_eq!(
            CheckedFreshDescriptor::new(
                FreshShape::Plain { binder_count: usize::MAX },
                keys.into_iter().map(str::to_owned).collect(),
            ),
            Err(ConstructionError::InvalidBinderLayout)
        );
    }
}

#[test]
fn fresh_arity_checks_body_plus_all_actual_injections_without_truncation() {
    assert_eq!(checked_fresh_arity(0), Ok(1));
    assert_eq!(checked_fresh_arity(usize::MAX - 1), Ok(usize::MAX));
    assert_eq!(checked_fresh_arity(usize::MAX), Err(ConstructionError::ArityOverflow));
    let descriptor = CheckedFreshDescriptor::new(
        FreshShape::Plain { binder_count: 0 },
        vec!["".into(), "unused".into()],
    )
    .expect("ordered keys");
    assert_eq!(descriptor.validate_injection_count(2), Ok(()));
    for count in [0, 1, 3] {
        assert_eq!(
            descriptor.validate_injection_count(count),
            Err(ConstructionError::ChildArity { expected: 3, actual: count + 1 })
        );
    }
    assert_eq!(
        descriptor.validate_injection_count(usize::MAX),
        Err(ConstructionError::ArityOverflow)
    );
}
