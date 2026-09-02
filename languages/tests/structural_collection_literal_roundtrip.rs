//! Compiled end-to-end gates for `StructuralV2` collection identity.
//!
//! The generator unit tests inspect emitted tokens. These tests compile those
//! tokens into a real language, execute the pooled lowering and inverse PDAs,
//! and compare the exact Dovetail root keys. The checks cover ordered values,
//! multiplicity, set/map canonicalization, key-value pairing, and all three
//! PathMap modes, including the three observably distinct empty values.

#![allow(non_local_definitions)]

#[path = "definitions/structural_collection_demo.rs"]
mod structural_collection_demo;

use mettail_runtime::{
    GeneratedSemanticKeyAbiV1, HashBag, HashMapLit, HashSetLit, Language, PathMapLit, Term,
};
use structural_collection_demo::{
    Bag, List, Map, Pathmap, Proc, Set, StructuralCollectionDemoLanguage,
    StructuralCollectionDemoTerm, StructuralCollectionDemoTermInner,
};

const MAX_NODES: usize = 100_000;

fn term(inner: StructuralCollectionDemoTermInner) -> StructuralCollectionDemoTerm {
    StructuralCollectionDemoTerm(inner)
}

fn roundtrip(input: &StructuralCollectionDemoTerm) -> StructuralCollectionDemoTerm {
    let rebuilt =
        StructuralCollectionDemoLanguage::__mettail_dovetail_structural_roundtrip(input, MAX_NODES)
            .unwrap_or_else(|error| panic!("structural round trip failed for {input:?}: {error}"));
    rebuilt
        .as_any()
        .downcast_ref::<StructuralCollectionDemoTerm>()
        .expect("round trip returned the fixture's generated term type")
        .clone()
}

fn root_key(input: &StructuralCollectionDemoTerm) -> Vec<u8> {
    let report = StructuralCollectionDemoLanguage::dovetail_report_for(input, 16, MAX_NODES)
        .unwrap_or_else(|error| panic!("Dovetail report failed for {input:?}: {error}"));
    assert!(report.is_complete(), "redex-free structural report is complete");
    assert_eq!(report.roots.len(), 1, "one typed input has one exact root");
    report.roots[0].clone()
}

fn assert_exact_roundtrip(input: StructuralCollectionDemoTerm) {
    let rebuilt = roundtrip(&input);
    assert!(
        input.term_eq(&rebuilt),
        "typed -> Dovetail -> typed must preserve the exact collection value:\n  input={input:?}\n  rebuilt={rebuilt:?}",
    );
    assert!(rebuilt.term_eq(&input), "term equality is symmetric");
    assert_eq!(
        root_key(&input),
        root_key(&rebuilt),
        "the inverse preserves the StructuralV2 exact key",
    );
}

#[test]
fn structural_control_rewrite_reaches_the_generated_typed_normal_form() {
    let input =
        term(StructuralCollectionDemoTermInner::Proc(Proc::C(std::sync::Arc::new(Proc::A))));
    let expected = term(StructuralCollectionDemoTermInner::Proc(Proc::D));
    let normal = StructuralCollectionDemoLanguage::dovetail_normal_term(&input, 16, MAX_NODES)
        .unwrap_or_else(|error| panic!("typed structural control rewrite failed: {error}"));
    let normal = normal
        .as_any()
        .downcast_ref::<StructuralCollectionDemoTerm>()
        .expect("normal form returned the fixture's generated term type");
    assert!(
        normal.term_eq(&expected),
        "the real structural rewrite must reduce C to D: {normal:?}",
    );
}

fn bag(values: impl IntoIterator<Item = Proc>) -> HashBag<Proc> {
    values.into_iter().collect()
}

fn set(values: impl IntoIterator<Item = Proc>) -> HashSetLit<Proc> {
    values.into_iter().collect()
}

fn map(values: impl IntoIterator<Item = (Proc, Proc)>) -> HashMapLit<Proc, Proc> {
    values.into_iter().collect()
}

#[test]
fn compiled_structural_roundtrip_preserves_every_collection_kind_and_pathmap_mode() {
    let list = term(StructuralCollectionDemoTermInner::List(List::ListLit(vec![
        Proc::A,
        Proc::B,
        Proc::A,
    ])));
    let bag = term(StructuralCollectionDemoTermInner::Bag(Bag::BagLit(bag([
        Proc::A,
        Proc::B,
        Proc::A,
    ]))));
    let set = term(StructuralCollectionDemoTermInner::Set(Set::SetLit(set([Proc::A, Proc::B]))));
    let map = term(StructuralCollectionDemoTermInner::Map(Map::MapLit(map([
        (Proc::A, Proc::B),
        (Proc::B, Proc::A),
    ]))));

    let mut path_set = PathMapLit::new();
    path_set.insert_set(Proc::A).expect("select set mode");
    path_set.insert_set(Proc::B).expect("remain in set mode");

    let mut path_map = PathMapLit::new();
    path_map
        .insert_map(Proc::A, Proc::B)
        .expect("select map mode");
    path_map
        .insert_map(Proc::B, Proc::A)
        .expect("remain in map mode");

    for value in [
        list,
        bag,
        set,
        map,
        term(StructuralCollectionDemoTermInner::Pathmap(Pathmap::PathmapLit(
            PathMapLit::Empty,
        ))),
        term(StructuralCollectionDemoTermInner::Pathmap(Pathmap::PathmapLit(path_set))),
        term(StructuralCollectionDemoTermInner::Pathmap(Pathmap::PathmapLit(path_map))),
    ] {
        assert_exact_roundtrip(value);
    }
}

#[test]
fn structural_keys_ignore_unordered_insertion_history_but_preserve_list_order() {
    let list_ab =
        term(StructuralCollectionDemoTermInner::List(List::ListLit(vec![Proc::A, Proc::B])));
    let list_ba =
        term(StructuralCollectionDemoTermInner::List(List::ListLit(vec![Proc::B, Proc::A])));
    assert_ne!(root_key(&list_ab), root_key(&list_ba), "list order is semantic");

    let bag_ab = term(StructuralCollectionDemoTermInner::Bag(Bag::BagLit(bag([
        Proc::A,
        Proc::B,
        Proc::A,
    ]))));
    let bag_ba = term(StructuralCollectionDemoTermInner::Bag(Bag::BagLit(bag([
        Proc::B,
        Proc::A,
        Proc::A,
    ]))));
    assert_eq!(root_key(&bag_ab), root_key(&bag_ba), "bag order is not semantic");

    let set_ab = term(StructuralCollectionDemoTermInner::Set(Set::SetLit(set([Proc::A, Proc::B]))));
    let set_ba = term(StructuralCollectionDemoTermInner::Set(Set::SetLit(set([Proc::B, Proc::A]))));
    assert_eq!(root_key(&set_ab), root_key(&set_ba), "set order is not semantic");

    let map_ab = term(StructuralCollectionDemoTermInner::Map(Map::MapLit(map([
        (Proc::A, Proc::B),
        (Proc::B, Proc::A),
    ]))));
    let map_ba = term(StructuralCollectionDemoTermInner::Map(Map::MapLit(map([
        (Proc::B, Proc::A),
        (Proc::A, Proc::B),
    ]))));
    assert_eq!(root_key(&map_ab), root_key(&map_ba), "map insertion order is not semantic");
}

#[test]
fn structural_keys_separate_display_collisions_and_all_empty_pathmap_modes() {
    let bag_a = bag([Proc::A]);
    let bag_b = bag([Proc::B]);
    assert_eq!(
        format!("{bag_a}"),
        format!("{bag_b}"),
        "control: the legacy display-only coefficients collide",
    );
    let bag_a = term(StructuralCollectionDemoTermInner::Bag(Bag::BagLit(bag_a)));
    let bag_b = term(StructuralCollectionDemoTermInner::Bag(Bag::BagLit(bag_b)));
    assert_ne!(
        root_key(&bag_a),
        root_key(&bag_b),
        "exact child structure separates equal displays",
    );

    let empty = PathMapLit::<Proc, Proc>::Empty;
    let empty_set = PathMapLit::Set(HashMapLit::<Proc, ()>::new());
    let empty_map = PathMapLit::Map(HashMapLit::<Proc, Proc>::new());
    assert_eq!(format!("{empty}"), format!("{empty_set}"));
    assert_eq!(format!("{empty_set}"), format!("{empty_map}"));

    let empty = term(StructuralCollectionDemoTermInner::Pathmap(Pathmap::PathmapLit(empty)));
    let empty_set =
        term(StructuralCollectionDemoTermInner::Pathmap(Pathmap::PathmapLit(empty_set)));
    let empty_map =
        term(StructuralCollectionDemoTermInner::Pathmap(Pathmap::PathmapLit(empty_map)));
    let keys = [root_key(&empty), root_key(&empty_set), root_key(&empty_map)];
    assert!(keys[0] != keys[1] && keys[0] != keys[2] && keys[1] != keys[2]);

    for value in [empty, empty_set, empty_map] {
        assert_exact_roundtrip(value);
    }
}

#[test]
fn compiled_artifact_advertises_the_structural_key_abi() {
    let metadata = StructuralCollectionDemoLanguage.metadata();
    let artifacts = metadata
        .generated_semantic_artifacts_v1()
        .expect("the closed fixture has exact generated semantic artifacts");
    assert_eq!(artifacts.semantic_key_abi, GeneratedSemanticKeyAbiV1::StructuralV2);
}
