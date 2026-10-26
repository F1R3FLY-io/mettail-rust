//! Cost(Rho) surface pins for FIPS XVIII.4. These inspect generated AST nodes,
//! not a legacy Tree-Sitter parse or a reparsed display string.

use mettail_languages::rholang::source_profile::{RholangSourceProfile, SourceRole};
use mettail_languages::rholang::{
    source_constructor, CostSig, CostStack, CostStackChain, InputBind, Proc, SourceConstructor,
    SourceProfile,
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
fn ungrouped_transfer_composition_preserves_cost_signature_rhs() {
    let source = "alice -o bob :: ()";
    let direct_stacks = CostStack::parse_via_wpda_all(source).expect("all ungrouped cost stacks");
    assert!(direct_stacks
        .iter()
        .any(|stack| matches!(stack, CostStack::CostStackLift(..))));
    let selected = Proc::parse(source).expect("transfer-headed cost stack");
    assert!(matches!(selected, Proc::PCostStackCons(..)));
    let all = Proc::parse_via_wpda_all(source).expect("all transfer-headed readings");
    assert!(all.iter().any(|term| matches!(
        term,
        Proc::PCostStackCons(sig, _)
            if matches!(sig.as_ref(), CostSig::CostSigTransfer(..))
    )));
}

#[test]
fn ungrouped_transfer_stack_cells_preserve_head_category_across_names() {
    for left in ["alice", "bob", "carol"] {
        for right in ["dave", "erin", "frank"] {
            let source = format!("{left} -o {right} :: ()");
            let readings = Proc::parse_via_wpda_all(&source).expect("ungrouped transfer stack");
            assert!(
                readings.iter().any(|term| matches!(term,
                    Proc::PCostStackCons(sig, _)
                        if matches!(sig.as_ref(), CostSig::CostSigTransfer(..)))),
                "missing transfer-headed stack reading for {source}"
            );
        }
    }
}

#[test]
fn right_associative_transfer_remains_inside_ungrouped_stack_head() {
    let readings = Proc::parse_via_wpda_all("alice -o bob -o carol :: ()")
        .expect("right-associative transfer stack");
    let has_right_associative_head = readings.iter().any(|term| match term {
        Proc::PCostStackCons(sig, _) => match sig.as_ref() {
            CostSig::CostSigTransfer(_, right) => {
                matches!(right.as_ref(), CostSig::CostSigTransfer(..))
            },
            _ => false,
        },
        _ => false,
    });
    assert!(
        has_right_associative_head,
        "ungrouped stack lost right-associative CostSig head"
    );
}

#[test]
fn hash_signature_with_parallel_body_remains_a_cost_stack_source() {
    let source = "#(Nil | Nil) :: ()";
    let selected = Proc::parse(source).expect("hash-headed cost stack");
    assert!(matches!(selected, Proc::PCostStackCons(..)));
    let all = Proc::parse_via_wpda_all(source).expect("all hash-headed readings");
    assert!(all.iter().any(|term| matches!(
        term,
        Proc::PCostStackCons(sig, _)
            if matches!(sig.as_ref(), CostSig::CostSigHash(..))
    )));
}

#[test]
fn empty_stack_tail_parses_independently() {
    let tail = CostStack::parse_via_wpda_all("()").expect("empty stack tail");
    assert!(tail.iter().any(|node| matches!(node,
                CostStack::CostStackLift(chain)
                    if matches!(chain.as_ref(), CostStackChain::CostStackChainEmpty))));
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
    let readings = CostStack::parse_via_wpda_all(source).expect("Appendix C stack parallel parses");
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

    assert!(
        matches!(
            elected,
            Proc::PCostStackCons(_, ref tail)
                if matches!(tail.as_ref(), CostStackChain::CostStackChainGroup(inner)
                    if has_two_cons_branches(inner))
        ),
        "elected process lost the shared prefix: {elected:#?}"
    );
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
    use source_constructor::{
        CostSig as Sig, CostStack as Stack, CostStackChain as Chain, InputBind as Bind, Proc as P,
    };
    use SourceRole::{Name, NamePattern, Term};

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

#[test]
fn signed_term_delimiters_preserve_complete_operator_bodies() {
    let mut failures = Vec::new();
    for source in [
        "{%Nil%}[@Nil]",
        "{%Nil == Nil%}[@Nil]",
        "{%Nil - Nil%}[@Nil]",
        "{%Nil == Nil %}[@Nil]",
    ] {
        if let Err(error) = mettail_languages::rholang::Proc::parse(source) {
            failures.push(format!("{source:?}: {error}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn nested_signed_operator_terms_preserve_the_complete_body() {
    use mettail_languages::rholang::{Int, Name};
    use std::sync::Arc;

    let signed = Arc::new(Proc::PCostSignedTerm(
        Arc::new(Proc::Eq(Arc::new(Proc::PZero), Arc::new(Proc::PZero))),
        Arc::new(CostSig::CostSigGround(Arc::new(Name::NQuoteNil))),
    ));
    let hash = CostSig::CostSigHash(Arc::clone(&signed));
    let source = hash.to_string();
    let (readings, _) = CostSig::__all_with_weights_monolithic(&source).expect("hash main parser");
    assert!(readings.contains(&hash), "signed hash body missing: {source:?}");
    assert_eq!(CostSig::parse(&source).expect("hash facade"), hash);
    let cast = Proc::IntBinProc(signed, Arc::new(Int::parse("a").expect("integer variable")));
    let source = cast.to_string();
    let (readings, _) = Proc::__all_with_weights_monolithic(&source).expect("cast main parser");
    assert!(readings.contains(&cast), "signed cast body missing: {source:?}");
    assert_eq!(Proc::parse(&source).expect("cast facade"), cast);
}
