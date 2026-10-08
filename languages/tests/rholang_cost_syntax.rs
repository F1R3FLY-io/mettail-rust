//! Cost(Rho) surface pins for FIPS XVIII.4. These inspect generated AST nodes,
//! not a legacy Tree-Sitter parse or a reparsed display string.

use mettail_languages::rholang::source_profile::{RholangSourceProfile, SourceRole};
use mettail_languages::rholang::{
    CostSig, CostStack, CostStackChain, InputBind, Proc, SourceConstructor, SourceProfile,
    source_constructor,
};

#[test]
fn signed_term_retains_body_and_signature() {
    let parsed = Proc::parse("{% Nil %}[alice]").expect("signed term");
    assert!(matches!(parsed, Proc::PCostSignedTerm(..)));
}

#[test]
fn ordinary_send_keeps_a_signed_payload() {
    let parsed = Proc::parse("channel!({% Nil %}[alice])").expect("signed payload");
    assert!(matches!(
        parsed,
        Proc::POutput(_, ref payload)
            if matches!(payload.as_ref(), Proc::PCostSignedTerm(..))
    ));
}

#[test]
fn transfer_is_right_associative_and_compound_is_left_associative() {
    let transfer = CostSig::parse("alice -o bob -o carol").expect("transfer");
    assert!(matches!(
        transfer,
        CostSig::CostSigTransfer(_, ref right)
            if matches!(right.as_ref(), CostSig::CostSigTransfer(..))
    ));

    let compound = CostSig::parse("alice (*) bob (*) carol").expect("compound");
    assert!(matches!(
        compound,
        CostSig::CostSigCompound(ref left, _)
            if matches!(left.as_ref(), CostSig::CostSigCompound(..))
    ));

    let mixed = CostSig::parse("alice (*) bob -o carol (*) dave")
        .expect("compound must bind before transfer");
    assert!(matches!(
        mixed,
        CostSig::CostSigTransfer(ref left, ref right)
            if matches!(left.as_ref(), CostSig::CostSigCompound(..))
                && matches!(right.as_ref(), CostSig::CostSigCompound(..))
    ));
}

#[test]
fn stack_has_full_signature_grammar_but_keeps_the_cell() {
    let stack = CostStack::parse("(alice -o bob) :: ()").expect("stack cell");
    assert!(matches!(
        stack,
        CostStack::CostStackLift(ref chain)
            if matches!(chain.as_ref(), CostStackChain::CostStackChainCons(..))
    ));
    // Fundability is a semantic check. The parser must not erase transfer.
    let root = Proc::parse("alice :: ()").expect("bare nonempty stack");
    assert!(matches!(root, Proc::PCostStackCons(..)));
}

#[test]
fn empty_stack_tail_parses_independently() {
    let tail = CostStack::parse_via_wpda_all("()").expect("empty stack tail");
    assert!(
        tail.iter()
            .any(|node| matches!(node,
                CostStack::CostStackLift(chain)
                    if matches!(chain.as_ref(), CostStackChain::CostStackChainEmpty)))
    );
}

#[test]
fn nested_parallel_stack_tail_retains_one_shared_prefix() {
    fn without_group(mut stack: &CostStack) -> &CostStack {
        while let CostStack::CostStackLift(chain) = stack {
            let CostStackChain::CostStackChainGroup(inner) = chain.as_ref() else {
                break;
            };
            stack = inner.as_ref();
        }
        stack
    }

    fn has_two_cons_branches(tail: &CostStack) -> bool {
        let CostStack::CostStackPar(left, right) = without_group(tail) else {
            return false;
        };
        matches!(without_group(left), CostStack::CostStackLift(chain)
            if matches!(chain.as_ref(), CostStackChain::CostStackChainCons(..)))
            && matches!(right.as_ref(), CostStackChain::CostStackChainCons(..))
    }

    fn has_shared_prefix(reading: &CostStack) -> bool {
        let CostStack::CostStackLift(chain) = without_group(reading) else {
            return false;
        };
        let CostStackChain::CostStackChainCons(_, tail) = chain.as_ref() else {
            return false;
        };
        let CostStackChain::CostStackChainGroup(inner) = tail.as_ref() else {
            return false;
        };
        has_two_cons_branches(inner)
    }

    let siblings = CostStack::parse_via_wpda_all("bob :: () | carol :: ()")
        .expect("stack parallel precedence");
    let grouped_siblings = CostStack::parse_via_wpda_all("(bob :: () | carol :: ())")
        .expect("grouped stack parallel precedence");
    let source = "alice :: (bob :: () | carol :: ())";
    let readings = CostStack::parse_via_wpda_all(source)
        .expect("Appendix C stack parallel parses");
    let elected = Proc::parse(source).expect("process root stack reading");
    assert!(
        siblings.iter().any(has_two_cons_branches),
        "stack cons must bind tighter than stack parallel: {siblings:#?}"
    );
    assert!(
        grouped_siblings.iter().any(has_two_cons_branches),
        "grouping must preserve the stack parallel reading: {grouped_siblings:#?}"
    );
    assert!(
        readings.iter().any(has_shared_prefix),
        "no canonical shared-prefix stack reading: {readings:#?}"
    );

    assert!(matches!(
        elected,
        Proc::PCostStackCons(_, ref tail)
            if matches!(tail.as_ref(), CostStackChain::CostStackChainGroup(inner)
                if has_two_cons_branches(inner))
    ), "elected process lost the shared prefix: {elected:#?}");
}

#[test]
fn ground_signature_head_parses_independently() {
    let head = CostSig::parse_via_wpda_all("alice").expect("ground signature head");
    assert!(
        head.iter()
            .any(|node| matches!(node, CostSig::CostSigGround(..))),
        "ground-signature readings: {head:?}"
    );
}

#[test]
fn bare_unit_is_not_a_cost_stack_at_proc_root() {
    let root = Proc::parse("()").expect("ordinary unit");
    assert!(matches!(root, Proc::PUnit));
    assert!(!matches!(root, Proc::PZero | Proc::PCostStackCons(..)));
}

#[test]
fn signed_receipt_and_continuation_are_distinct_nodes() {
    let bind = InputBind::parse("{% value <- channel %}[alice]").expect("signed bind");
    assert!(matches!(bind, InputBind::InputBindCostSigned(..)));
    let continuation =
        Proc::parse("for({% value <- channel %}[alice]){% Nil %}").expect("signed continuation");
    assert!(matches!(continuation, Proc::PForCostSigned(..)));
}

#[test]
fn hash_signature_can_name_a_grouped_process() {
    let signature = CostSig::parse("#(Nil)").expect("hash signature");
    assert!(matches!(signature, CostSig::CostSigHash(..)));
}

#[test]
fn cost_surface_is_structurally_admitted_by_the_closed_public_source_profile() {
    // Admission must traverse the original children; fundability and live
    // authority are later checks, so a transfer-bearing syntax remains visible.
    for source in [
        "()",
        "{% Nil %}[@Nil]",
        "{% Nil %}[#(Nil)]",
        "{% Nil %}[alice -o bob]",
        "alice :: ()",
        "alice :: (bob :: () | carol :: ())",
        "for({% value <- channel %}[alice]){% Nil %}",
    ] {
        let proc = Proc::parse(source).expect("cost source parses");
        let mut charged_work = 0usize;
        proc.try_check_source_profile(
            SourceRole::Term,
            &RholangSourceProfile,
            &mut |work, _bytes| {
                charged_work += work;
                Ok::<(), ()>(())
            },
        )
        .unwrap_or_else(|_| panic!("cost source profile refused {source}"));
        assert!(charged_work > 0, "source profile did not charge {source}");
    }
}

#[test]
fn cost_source_profile_keeps_each_original_child_in_its_structural_role() {
    use SourceRole::{Name, NamePattern, Term};
    use source_constructor::{
        CostSig as Sig, CostStack as Stack, CostStackChain as Chain, InputBind as Bind, Proc as P,
    };

    let cases: &[(SourceConstructor, &[SourceRole])] = &[
        (SourceConstructor::Proc(P::PUnit), &[]),
        (SourceConstructor::Proc(P::PCostSignedTerm), &[Term, Term]),
        (SourceConstructor::Proc(P::PCostStackCons), &[Term, Term]),
        (SourceConstructor::CostSig(Sig::CostSigTransfer), &[Term, Term]),
        (SourceConstructor::CostSig(Sig::CostSigCompound), &[Term, Term]),
        (SourceConstructor::CostSig(Sig::CostSigGround), &[Name]),
        (SourceConstructor::CostSig(Sig::CostSigHash), &[Term]),
        (SourceConstructor::CostSig(Sig::CostSigGroup), &[Term]),
        (SourceConstructor::CostStack(Stack::CostStackLift), &[Term]),
        (SourceConstructor::CostStack(Stack::CostStackPar), &[Term, Term]),
        (SourceConstructor::CostStackChain(Chain::CostStackChainEmpty), &[]),
        (SourceConstructor::CostStackChain(Chain::CostStackChainCons), &[Term, Term]),
        (SourceConstructor::CostStackChain(Chain::CostStackChainGroup), &[Term]),
        (SourceConstructor::Proc(P::PForCostSigned), &[Term, Term]),
        (
            SourceConstructor::InputBind(Bind::InputBindCostSigned),
            &[NamePattern, Name, Term],
        ),
        (SourceConstructor::InputBind(Bind::InputBindCostSignedEmpty), &[Name, Term]),
    ];

    for &(constructor, expected) in cases {
        let fields = RholangSourceProfile
            .fields(constructor)
            .unwrap_or_else(|| panic!("unsupported cost constructor: {constructor:?}"));
        let actual: Vec<_> = fields
            .iter()
            .map(|field| field.expect("cost constructor must not hide a category child")(Term))
            .collect();
        assert_eq!(actual, expected, "wrong child roles for {constructor:?}");
    }
}
