//! AST-first Cost(Rho) wire retention. These tests never invoke the legacy parser.

use mettail_languages::rholang::Proc;
use mettail_rholang_runtime::{lower_rholang_proc, RholangAstLowerError};
use models::rhoapi::cost_signature::Value as CostValue;
use models::rust::rholang::sorter::par_sort_matcher::ParSortMatcher;
use models::rust::rholang::sorter::sortable::Sortable;
use models::rust::utils::new_gstring_par;
use proptest::prelude::*;
use prost::Message;

fn lower(source: &str) -> Result<models::rhoapi::Par, RholangAstLowerError> {
    let proc = Proc::parse_via_wpda(source).expect("MeTTaIL Cost(Rho) parse");
    lower_rholang_proc(&proc)
}

#[test]
fn signed_nil_preserves_exact_ground_principal_bytes() {
    let rho = lower("{% Nil %}[alice]").expect("signed term lowers");
    assert_eq!(rho.cost_signed_terms.len(), 1);
    let signed = &rho.cost_signed_terms[0];
    assert_eq!(signed.body.as_ref().expect("signed body").sends.len(), 0);
    let expected =
        ParSortMatcher::sort_match(&new_gstring_par("alice".to_owned(), Vec::new(), false))
            .term
            .encode_to_vec();
    assert!(matches!(
        signed.signature.as_ref().and_then(|sig| sig.value.as_ref()),
        Some(CostValue::Ground(bytes)) if bytes.as_slice() == expected.as_slice()
    ));
}

#[test]
fn quoted_name_principal_is_distinct_from_hash_signature() {
    let rho = lower("{% Nil %}[@Nil]").expect("quoted name principal lowers");
    let signature = rho.cost_signed_terms[0]
        .signature
        .as_ref()
        .expect("signature");
    assert!(matches!(signature.value.as_ref(), Some(CostValue::Name(_))));
    let hashed = lower("{% Nil %}[#(Nil)]").expect("hash signature lowers");
    let signature = hashed.cost_signed_terms[0]
        .signature
        .as_ref()
        .expect("hash signature");
    assert!(matches!(signature.value.as_ref(), Some(CostValue::Quote(_))));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(8))]

    #[test]
    fn quoted_name_and_hash_section_retain_distinct_wire_tags_for_the_same_process(
        value in 0u8..32,
    ) {
        let name = lower(&format!("{{% Nil %}}[@({value})]"))
            .expect("quoted Name ground signature lowers");
        let section = lower(&format!("{{% Nil %}}[#({value})]"))
            .expect("cryptographic section lowers");
        let name_signature = name.cost_signed_terms[0].signature.as_ref().expect("name signature");
        let section_signature = section.cost_signed_terms[0].signature.as_ref().expect("section signature");
        match (name_signature.value.as_ref(), section_signature.value.as_ref()) {
            (Some(CostValue::Name(name_process)), Some(CostValue::Quote(section_process))) => {
                prop_assert_eq!(name_process.encode_to_vec(), section_process.encode_to_vec());
                prop_assert_ne!(name_signature.encode_to_vec(), section_signature.encode_to_vec());
            }
            other => prop_assert!(false, "distinct Name/Quote wire tags required: {other:?}"),
        }
    }
}

#[test]
fn bare_stack_is_inert_evidence_not_a_mint() {
    let rho = lower("alice :: ()").expect("nonempty stack lowers");
    assert!(rho.sends.is_empty(), "source stack syntax cannot mint supply");
    assert_eq!(rho.cost_stacks.len(), 1);
    assert_eq!(rho.cost_stacks[0].cells.len(), 1);
    assert!(matches!(
        lower("(alice -o bob) :: ()"),
        Err(RholangAstLowerError::UnfundableCostSignature)
    ));
}

#[test]
fn parallel_stack_tail_retains_one_shared_prefix() {
    let rho = lower("alice :: (bob :: () | carol :: ())")
        .expect("parallel stack tail lowers without copying its prefix");
    assert!(rho.sends.is_empty(), "source stack syntax cannot mint supply");
    assert_eq!(rho.cost_stacks.len(), 1);
    let stack = &rho.cost_stacks[0];
    assert_eq!(stack.cells.len(), 1);
    assert_eq!(stack.parallel_tail.len(), 2);
    assert_eq!(stack.parallel_tail[0].cells.len(), 1);
    assert_eq!(stack.parallel_tail[1].cells.len(), 1);
    assert!(stack.parallel_tail.iter().all(|branch| branch.parallel_tail.is_empty()));
}

#[test]
fn unit_is_not_lowered_as_nil() {
    let unit = lower("()").expect("unit lowers as host tuple");
    let nil = lower("Nil").expect("nil lowers as empty process");
    assert_eq!(unit.encode_to_vec(), [0x2a, 3, 0xaa, 1, 0]);
    assert!(nil.encode_to_vec().is_empty());
    assert_ne!(unit, nil);
}

#[test]
fn authority_rewrites_without_a_checked_plan_fail_closed() {
    assert!(matches!(
        lower("{% Nil %}[alice -o bob]"),
        Err(RholangAstLowerError::UnfundableCostSignature)
    ));
    assert!(matches!(
        lower("for({% value <- @\"c\" %}[alice]){% Nil %}"),
        Err(RholangAstLowerError::CostPlanUnavailable(_))
    ));
}

#[test]
fn signed_receive_bind_retains_its_wire_signature() {
    let rho = lower("for({% value <- channel %}[alice]){ Nil }")
        .expect("signed bind lowers through the receive worklist");
    assert_eq!(rho.receives.len(), 1);
    let bind = &rho.receives[0].binds[0];
    let expected =
        ParSortMatcher::sort_match(&new_gstring_par("alice".to_owned(), Vec::new(), false))
            .term
            .encode_to_vec();
    assert!(matches!(
        bind.cost_signature.as_ref().and_then(|sig| sig.value.as_ref()),
        Some(CostValue::Ground(bytes)) if bytes.as_slice() == expected.as_slice()
    ));
}

#[test]
fn signed_receive_empty_bind_retains_its_wire_signature() {
    let rho = lower("for({% <- channel %}[alice]){ Nil }")
        .expect("signed empty bind lowers through the receive worklist");
    assert_eq!(rho.receives.len(), 1);
    let bind = &rho.receives[0].binds[0];
    assert!(bind.patterns.is_empty());
    assert!(bind.cost_signature.is_some());
}

#[test]
fn lollipop_signed_receive_keeps_both_authority_slots() {
    let rho = lower("{% for(value <- channel){ Nil } %}[alice -o bob]")
        .expect("lollipop receive lowers without a recursive parser fallback");
    assert_eq!(rho.cost_signed_terms.len(), 1);
    let outer = &rho.cost_signed_terms[0];
    let expected_alice =
        ParSortMatcher::sort_match(&new_gstring_par("alice".to_owned(), Vec::new(), false))
            .term
            .encode_to_vec();
    assert!(matches!(
        outer.signature.as_ref().and_then(|sig| sig.value.as_ref()),
        Some(CostValue::Ground(bytes)) if bytes.as_slice() == expected_alice.as_slice()
    ));
    let receive = &outer.body.as_ref().expect("outer body").receives[0];
    let continuation = receive.body.as_ref().expect("receive continuation");
    assert_eq!(continuation.cost_signed_terms.len(), 1);
    let expected_bob =
        ParSortMatcher::sort_match(&new_gstring_par("bob".to_owned(), Vec::new(), false))
            .term
            .encode_to_vec();
    assert!(matches!(
        continuation.cost_signed_terms[0]
            .signature
            .as_ref()
            .and_then(|sig| sig.value.as_ref()),
        Some(CostValue::Ground(bytes)) if bytes.as_slice() == expected_bob.as_slice()
    ));
}

#[test]
fn quote_signature_keeps_enclosing_new_binding() {
    let rho = lower("new x in {{% Nil %}[#x]}").expect("bound quote signature lowers");
    let inner = rho.news[0].p.as_ref().expect("new body");
    let signature = inner.cost_signed_terms[0]
        .signature
        .as_ref()
        .expect("signature");
    let Some(CostValue::Quote(quoted)) = signature.value.as_ref() else {
        panic!("#x must lower as a quote signature")
    };
    assert!(
        quoted.locally_free.iter().any(|bit| *bit != 0),
        "the quoted principal must retain the enclosing bound variable"
    );
}
