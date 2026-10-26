//! Executable counterparts to the closed/open substitution laws in
//! NoAdmitTypeProjection.v. A closed result sort is not an opaque container.

#![allow(unused_imports, dead_code)]

use proptest::prelude::*;
use std::sync::Arc;

mettail_macros::language! {
    name: ClosedSubstitutionLaw,
    options { emit_tests: false, emit_simulator: false, emit_blockly: false },
    types { Name noadmit CostSig },
    terms {
        Lit . |- "n" : Name;
        Lit2 . |- "m" : Name;
        Wrapped . inner:Name |- "(" inner ")" : Name;
        Ground . name:Name |- name : CostSig;
        Join . left:CostSig, right:CostSig |- left "*" right : CostSig;
        Bag . names:HashBag(Name) |- "[" names.*sep(",") "]" : CostSig;
        Set . names:HashSet(Name) |- "<" names.*sep(",") ">" : CostSig;
        Nested . signatures:HashBag(CostSig) |- "{" signatures.*sep(",") "}" : CostSig;
    },
    equations {},
    rewrites {},
}

fn nested(base: CostSig, depth: usize) -> CostSig {
    let mut term = base;
    for _ in 0..depth {
        term = CostSig::Join(Arc::new(term), Arc::new(CostSig::Ground(Arc::new(Name::Lit))));
    }
    term
}

#[test]
fn closed_semantic_term_keeps_a_host_environment_binding() {
    let mut environment = ClosedSubstitutionLawEnv::new();
    environment
        .costsig
        .set("sig".to_owned(), CostSig::Ground(Arc::new(Name::Lit)));
    assert!(environment.costsig.get("sig").is_some());
}

#[test]
fn closed_owner_collection_binds_an_open_element_pattern_from_the_ground() {
    // Changed because `mettail_runtime` has no `native_variable` module. It
    // re-exports `get_or_create_var` at its root (runtime/src/binding.rs:53-55).
    // The code was:
    // let variable = mettail_runtime::native_variable::get_or_create_var("item");
    let variable = mettail_runtime::get_or_create_var("item");
    let ground = CostSig::Bag(mettail_runtime::HashBag::from_iter([Name::Lit]));
    let pattern = CostSig::Bag(mettail_runtime::HashBag::from_iter([Name::NVar(
        mettail_runtime::OrdVar(mettail_runtime::Var::Free(variable)),
    )]));
    let bindings = ground
        .match_pattern(&pattern)
        .expect("open element variable matches within a closed owner");
    assert_eq!(bindings.name_bindings.len(), 1);
    assert_eq!(bindings.name_bindings[0].0, "item");
    assert!(matches!(bindings.name_bindings[0].1, Name::Lit));
}

#[test]
fn closed_collection_elements_keep_structural_matching_without_a_variable_case() {
    let ground_element = CostSig::Ground(Arc::new(Name::Lit));
    let same = CostSig::Nested(mettail_runtime::HashBag::from_iter([ground_element.clone()]));
    let different = CostSig::Nested(mettail_runtime::HashBag::from_iter([CostSig::Join(
        Arc::new(ground_element.clone()),
        Arc::new(ground_element),
    )]));
    assert!(same.match_pattern(&same).is_some());
    assert!(same.match_pattern(&different).is_none());
}

fn name_variable(spelling: &str) -> Name {
    // Changed for the same root re-export as above. The code was:
    // Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
    //     mettail_runtime::native_variable::get_or_create_var(spelling),
    // )))
    Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
        mettail_runtime::get_or_create_var(spelling),
    )))
}

#[test]
fn closed_owner_bag_finds_a_non_greedy_assignment_for_open_elements() {
    let ground = CostSig::Bag(mettail_runtime::HashBag::from_iter([Name::Lit, Name::Lit2]));
    let pattern =
        CostSig::Bag(mettail_runtime::HashBag::from_iter([name_variable("bag_rest"), Name::Lit]));
    let bindings = ground
        .match_pattern(&pattern)
        .expect("perfect assignment exists");
    assert!(matches!(bindings.get_name("bag_rest"), Some(Name::Lit2)));
}

#[test]
fn structural_patterns_with_overlapping_candidates_are_not_greedily_pruned() {
    let ground = CostSig::Bag(mettail_runtime::HashBag::from_iter([
        Name::Wrapped(Arc::new(Name::Lit)),
        Name::Wrapped(Arc::new(Name::Lit2)),
    ]));
    let pattern = CostSig::Bag(mettail_runtime::HashBag::from_iter([
        Name::Wrapped(Arc::new(name_variable("wrapped_rest"))),
        Name::Wrapped(Arc::new(Name::Lit)),
    ]));
    let bindings = ground
        .match_pattern(&pattern)
        .expect("perfect assignment exists");
    assert!(matches!(bindings.get_name("wrapped_rest"), Some(Name::Lit2)));
}

#[test]
fn closed_owner_set_uses_the_same_complete_occurrence_assignment() {
    // Changed for sole-collection lane (carrier): a `HashSet(Name)` field is
    // `mettail_runtime::HashSetLit<Name>` in the generated AST, which has a
    // `FromIterator` impl (runtime/src/hashset_lit.rs:212). The code was:
    // let ground = CostSig::Set(std::collections::HashSet::from_iter([Name::Lit, Name::Lit2]));
    // let pattern =
    //     CostSig::Set(std::collections::HashSet::from_iter([name_variable("set_rest"), Name::Lit]));
    let ground = CostSig::Set(mettail_runtime::HashSetLit::from_iter([Name::Lit, Name::Lit2]));
    let pattern =
        CostSig::Set(mettail_runtime::HashSetLit::from_iter([name_variable("set_rest"), Name::Lit]));
    let bindings = ground
        .match_pattern(&pattern)
        .expect("perfect assignment exists");
    assert!(matches!(bindings.get_name("set_rest"), Some(Name::Lit2)));
}

#[test]
fn repeated_pattern_variable_occurrences_remain_independent_wildcards() {
    let ground = CostSig::Bag(mettail_runtime::HashBag::from_iter([Name::Lit, Name::Lit2]));
    let pattern = CostSig::Bag(mettail_runtime::HashBag::from_iter([
        name_variable("wildcard"),
        name_variable("wildcard"),
    ]));
    let bindings = ground
        .match_pattern(&pattern)
        .expect("two independent wildcard occurrences can claim distinct grounds");
    assert_eq!(bindings.name_bindings.len(), 2);
    assert!(bindings
        .name_bindings
        .iter()
        .all(|(name, _)| name == "wildcard"));
    assert!(bindings
        .name_bindings
        .iter()
        .any(|(_, value)| matches!(value, Name::Lit)));
    assert!(bindings
        .name_bindings
        .iter()
        .any(|(_, value)| matches!(value, Name::Lit2)));
}

proptest! {
    #[test]
    fn closed_self_substitution_is_identity_but_embedded_name_substitution_runs(
        depth in 0usize..32,
        spelling in "[a-z]{1,12}",
    ) {
        // Changed for the same root re-export as above. The code was:
        // let variable = mettail_runtime::native_variable::get_or_create_var(&spelling);
        let variable = mettail_runtime::get_or_create_var(&spelling);
        let name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(variable.clone())));
        let original = nested(CostSig::Ground(Arc::new(name)), depth);
        let expected = nested(CostSig::Ground(Arc::new(Name::Lit)), depth);

        let same_sort = original.subst(&[&variable], &[expected.clone()]);
        prop_assert_eq!(format!("{same_sort:?}"), format!("{original:?}"));

        let embedded_sort = original.subst_name(&[&variable], &[Name::Lit]);
        prop_assert_eq!(format!("{embedded_sort:?}"), format!("{expected:?}"));
    }
}
