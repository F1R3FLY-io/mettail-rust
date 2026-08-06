use mettail_ast::types::CollectionType;
use mettail_rholang_codegen::{reflect_ground_term_par, GroundTerm};
use models::rhoapi::expr::ExprInstance;

#[test]
fn native_set_and_map_carriers_survive_the_iterative_reflector() {
    let set = GroundTerm::collection(
        CollectionType::HashSet,
        "Set",
        vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
    );
    let reflected_set = reflect_ground_term_par(&set, "carrier-test");
    let [set_expr] = reflected_set.exprs.as_slice() else {
        panic!("a reflected set must be a single ESet expression");
    };
    let Some(ExprInstance::ESetBody(set_body)) = set_expr.expr_instance.as_ref() else {
        panic!("HashSet reflection must retain the native ESet carrier");
    };
    assert_eq!(set_body.ps.len(), 2);

    let map = GroundTerm::collection(
        CollectionType::HashMap,
        "Map",
        vec![
            GroundTerm::map_entry(GroundTerm::nullary("K1"), GroundTerm::nullary("V1")),
            GroundTerm::map_entry(GroundTerm::nullary("K2"), GroundTerm::nullary("V2")),
        ],
    );
    let reflected_map = reflect_ground_term_par(&map, "carrier-test");
    let [map_expr] = reflected_map.exprs.as_slice() else {
        panic!("a reflected map must be a single EMap expression");
    };
    let Some(ExprInstance::EMapBody(map_body)) = map_expr.expr_instance.as_ref() else {
        panic!("HashMap reflection must retain the native EMap carrier");
    };
    assert_eq!(map_body.kvs.len(), 2);
}

#[test]
fn deep_ground_reflection_and_lifecycle_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("ground-reflection-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut term = GroundTerm::nullary("Leaf");
            for _ in 0..DEPTH {
                term = GroundTerm::new("Node", vec![term]);
            }

            let cloned = term.clone();
            assert_eq!(term, cloned);
            let reflected = reflect_ground_term_par(&term, "stack-safety-test");
            assert_eq!(reflected.exprs.len(), 1);

            // These drops are part of the gate: both recursive model families
            // must dismantle the 20k-deep value without consuming native stack.
            drop(reflected);
            drop(cloned);
            drop(term);
        })
        .expect("small-stack ground-reflection test thread must spawn");
    handle
        .join()
        .expect("ground reflection and lifecycle must not overflow the native stack");
}
