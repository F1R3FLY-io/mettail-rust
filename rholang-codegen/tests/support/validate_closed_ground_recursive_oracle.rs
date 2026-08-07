use super::*;
use models::rhoapi::{KeyValuePair, Var};
use models::rust::utils::{
    new_elist_par, new_emap_par, new_eset_par, new_etuple_par, new_gint_par, new_gstring_par,
};

fn recursive_is_closed_ground_value(par: &Par) -> bool {
    if !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
        || !par.conditionals.is_empty()
        || !metadata_eq(par, &[], false)
    {
        return false;
    }

    if par.exprs.is_empty() {
        return par.unforgeables.len() == 1 && par.unforgeables[0].unf_instance.is_some();
    }
    if !par.unforgeables.is_empty() {
        return false;
    }

    let [expr] = par.exprs.as_slice() else {
        return false;
    };
    let Some(expr) = expr.expr_instance.as_ref() else {
        return false;
    };

    match expr {
        ExprInstance::GBool(_)
        | ExprInstance::GInt(_)
        | ExprInstance::GString(_)
        | ExprInstance::GUri(_)
        | ExprInstance::GByteArray(_)
        | ExprInstance::GDouble(_)
        | ExprInstance::GBigInt(_)
        | ExprInstance::GBigRat(_)
        | ExprInstance::GFixedPoint(_) => true,
        ExprInstance::EListBody(list) if list.remainder.is_none() && !list.connective_used => {
            list.ps.iter().all(recursive_is_closed_ground_value)
        },
        ExprInstance::ETupleBody(tuple) if !tuple.connective_used => {
            tuple.ps.iter().all(recursive_is_closed_ground_value)
        },
        ExprInstance::ESetBody(set) if set.remainder.is_none() && !set.connective_used => {
            set.ps.iter().all(recursive_is_closed_ground_value)
        },
        ExprInstance::EMapBody(map) if map.remainder.is_none() && !map.connective_used => {
            map.kvs.iter().all(|pair| {
                pair.key
                    .as_ref()
                    .zip(pair.value.as_ref())
                    .is_some_and(|(key, value)| {
                        recursive_is_closed_ground_value(key)
                            && recursive_is_closed_ground_value(value)
                    })
            })
        },
        _ => false,
    }
}

fn list(items: Vec<Par>) -> Par {
    new_elist_par(items, Vec::new(), false, None, Vec::new(), false)
}

#[test]
fn iterative_closed_ground_validation_matches_recursive_oracle() {
    let scalar = new_gstring_par("ground".to_owned(), Vec::new(), false);
    let tuple = new_etuple_par(vec![new_gint_par(1, Vec::new(), false), scalar.clone()]);
    let set =
        new_eset_par(vec![tuple.clone(), list(vec![])], Vec::new(), false, None, Vec::new(), false);
    let map = new_emap_par(
        vec![KeyValuePair {
            key: Some(scalar.clone()),
            value: Some(set.clone()),
        }],
        Vec::new(),
        false,
        None,
        Vec::new(),
        false,
    );

    let mut bad_metadata = list(vec![scalar.clone()]);
    bad_metadata.locally_free = vec![1];
    let mut bad_remainder = list(vec![scalar.clone()]);
    let Some(ExprInstance::EListBody(body)) = bad_remainder.exprs[0].expr_instance.as_mut() else {
        unreachable!();
    };
    body.remainder = Some(Var {
        var_instance: Some(VarInstance::FreeVar(0)),
    });
    let missing_map_value = new_emap_par(
        vec![KeyValuePair { key: Some(scalar.clone()), value: None }],
        Vec::new(),
        false,
        None,
        Vec::new(),
        false,
    );
    let cases = [
        scalar,
        tuple,
        set,
        map,
        list(vec![]),
        bad_metadata,
        bad_remainder,
        missing_map_value,
        Par::default(),
    ];
    for case in &cases {
        assert_eq!(is_closed_ground_value(case), recursive_is_closed_ground_value(case));
    }
}

#[test]
fn closed_ground_validation_handles_depth_twenty_thousand_on_a_small_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("closed-ground-validation-small-stack".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut value = new_gint_par(7, Vec::new(), false);
            for _ in 0..DEPTH {
                value = list(vec![value]);
            }
            assert!(is_closed_ground_value(&value));
            drop(value);
        })
        .expect("small-stack closed-ground validation thread must spawn")
        .join()
        .expect("closed-ground validation must not overflow the native stack");
}
