use mettail_rholang_codegen::{
    ac_carrier_channel, ac_match_call_par, ac_sigma_receiver_par_with_condition,
    reflect_ground_term_par, spread_child_location, spread_root_location, CollectionType,
    GroundTerm, RhoNetAcMatchEntry,
};
use models::rhoapi::Par;
use models::rust::utils::{new_gstring_par, new_send_par};

const FINGERPRINT: &str = "ac-locator-stack-gate";
const ROOT_SITE: &str = "site0";
const OUT: &str = "OUT";
const DEPTH: usize = 16_384;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn entry() -> RhoNetAcMatchEntry {
    RhoNetAcMatchEntry {
        fired_rule_label: "Take".to_owned(),
        op: "Bag".to_owned(),
        kind: CollectionType::HashBag,
        arity: 1,
        rhs_par: Par::default(),
        condition: None,
    }
}

fn recursive_oracle(node: &GroundTerm, location: &str, entry: &RhoNetAcMatchEntry) -> Par {
    if matches!(node.coll_type, Some(CollectionType::HashBag)) {
        if node.constructor != entry.op {
            return Par::default();
        }
        let carrier = ac_carrier_channel(location, &node.constructor);
        let receiver = ac_sigma_receiver_par_with_condition(
            entry.kind.clone(),
            FINGERPRINT,
            &entry.op,
            entry.arity,
            entry.rhs_par.clone(),
            new_gstring_par(carrier.clone(), Vec::new(), false),
            entry.condition.clone(),
        );
        let delivery = new_send_par(
            new_gstring_par(carrier, Vec::new(), false),
            vec![
                reflect_ground_term_par(node, FINGERPRINT),
                new_gstring_par(OUT.to_owned(), Vec::new(), false),
            ],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        return receiver.append(delivery);
    }

    let mut result = Par::default();
    for (index, child) in node.children.iter().enumerate() {
        let child_location = spread_child_location(location, &node.constructor, index);
        result = result.append(recursive_oracle(child, &child_location, entry));
    }
    result
}

#[test]
fn iterative_locator_is_identical_to_the_recursive_semantics() {
    let subject = GroundTerm::new(
        "Root",
        vec![
            GroundTerm::new(
                "Left",
                vec![GroundTerm::collection(
                    CollectionType::HashBag,
                    "Bag",
                    vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
                )],
            ),
            GroundTerm::collection(
                CollectionType::HashBag,
                "OtherBag",
                vec![GroundTerm::collection(
                    CollectionType::HashBag,
                    "Bag",
                    vec![GroundTerm::nullary("not-reached")],
                )],
            ),
            GroundTerm::collection(CollectionType::HashBag, "Bag", vec![GroundTerm::nullary("C")]),
        ],
    );
    let entry = entry();
    let actual =
        ac_match_call_par(&subject, std::slice::from_ref(&entry), ROOT_SITE, OUT, FINGERPRINT);
    let root = spread_root_location(FINGERPRINT, ROOT_SITE);
    let expected = recursive_oracle(&subject, &root, &entry);
    assert_eq!(actual, expected);
}

#[test]
fn iterative_locator_handles_deep_subjects_on_a_small_stack() {
    std::thread::Builder::new()
        .name("rho-net-ac-locator-depth".to_owned())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut subject = GroundTerm::collection(
                CollectionType::HashBag,
                "Bag",
                vec![GroundTerm::nullary("leaf")],
            );
            for _ in 0..DEPTH {
                subject = GroundTerm::new("Wrap", vec![subject]);
            }
            let result = ac_match_call_par(&subject, &[entry()], ROOT_SITE, OUT, FINGERPRINT);
            assert_eq!(result.receives.len(), 1, "the deep terminal bag is located once");
        })
        .expect("small-stack AC locator thread starts")
        .join()
        .expect("the AC locator does not overflow the small stack");
}
