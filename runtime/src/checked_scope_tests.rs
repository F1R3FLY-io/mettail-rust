use super::*;
use crate::Scope;

fn bound(index: u32) -> OrdVar {
    OrdVar(Var::Bound(BoundVar {
        scope: moniker::ScopeOffset(0),
        binder: BinderIndex(index),
        pretty_name: Some("old bound hint".into()),
    }))
}

#[test]
fn paid_unbind_preserves_positions_and_uses_fresh_hints() {
    for selected in 0..3 {
        let original = vec![
            Binder(FreeVar::fresh_named("same")),
            Binder(FreeVar::fresh_unnamed()),
            Binder(FreeVar::fresh_named("same")),
        ];
        let scope = Scope::from_parts_unsafe(original.clone(), bound(selected));
        let (fresh, opened) = scope
            .try_unbind(&mut |_, _| Ok::<_, ()>(()))
            .expect("paid opening");
        assert_eq!(fresh.len(), original.len());
        for (index, binder) in fresh.iter().enumerate() {
            assert_eq!(binder.0.pretty_name, original[index].0.pretty_name);
            assert_ne!(binder.0.unique_id, original[index].0.unique_id);
            for earlier in &fresh[..index] {
                assert_ne!(binder.0.unique_id, earlier.0.unique_id);
            }
        }
        let Var::Free(opened) = opened.0 else {
            panic!("selected coordinate must open")
        };
        assert_eq!(opened.unique_id, fresh[selected as usize].0.unique_id);
        assert_eq!(opened.pretty_name, fresh[selected as usize].0.pretty_name);
        assert_eq!(scope.unsafe_pattern(), &original);
        assert_eq!(scope.unsafe_body(), &bound(selected));
    }
}

#[test]
fn paid_unbind_freshens_duplicate_original_occurrences_separately() {
    let binder = Binder(FreeVar::fresh_named("duplicate"));
    let scope = Scope::from_parts_unsafe(vec![binder.clone(), binder], bound(1));
    let (fresh, opened) = scope
        .try_unbind(&mut |_, _| Ok::<_, ()>(()))
        .expect("two fresh calls");
    assert_ne!(fresh[0].0.unique_id, fresh[1].0.unique_id);
    let Var::Free(opened) = opened.0 else {
        panic!("second occurrence must open")
    };
    assert_eq!(opened.unique_id, fresh[1].0.unique_id);
}

#[test]
fn paid_unbind_every_reservation_cut_keeps_the_original_scope() {
    struct Stop(usize);
    let source = Scope::from_parts_unsafe(
        vec![Binder(FreeVar::fresh_named("first")), Binder(FreeVar::fresh_unnamed())],
        bound(0),
    );
    let pattern = source.unsafe_pattern().clone();
    let body = source.unsafe_body().clone();
    let mut trace = Vec::new();
    assert!(source
        .try_unbind(&mut |w, u| {
            trace.push((w, u));
            Ok::<_, Stop>(())
        })
        .is_ok());
    for cut in 0..trace.len() {
        let mut actual = Vec::new();
        let result = source.try_unbind(&mut |w, u| {
            actual.push((w, u));
            if actual.len() == cut + 1 {
                Err(Stop(cut))
            } else {
                Ok(())
            }
        });
        assert!(matches!(result, Err(BindingFailure::Reservation(Stop(at))) if at == cut));
        assert_eq!(actual, trace[..=cut]);
        assert_eq!(source.unsafe_pattern(), &pattern);
        assert_eq!(source.unsafe_body(), &body);
    }
}

#[test]
fn paid_unbind_empty_roster_preserves_free_terms_and_refuses_missing_coordinates() {
    let name = FreeVar::fresh_named("free");
    let source = Scope::from_parts_unsafe(Vec::new(), OrdVar(Var::Free(name.clone())));
    let (fresh, body) = source
        .try_unbind(&mut |_, _| Ok::<_, ()>(()))
        .expect("empty scope");
    assert!(fresh.is_empty());
    assert_eq!(body, OrdVar(Var::Free(name)));
    let malformed = Scope::from_parts_unsafe(Vec::new(), bound(0));
    assert_eq!(
        malformed.try_unbind(&mut |_, _| Ok::<_, ()>(())),
        Err(BindingFailure::MissingBinder { index: 0 })
    );
}
