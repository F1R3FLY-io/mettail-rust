//! Bounded recursive reference for the Rholang send-sugar canonicalizer.
//!
//! Production uses one heterogeneous post-order machine. These equations are the superseded
//! implementation and remain test-only: shallow terms establish exact behavioral equivalence,
//! while deep terms exercise only the production PDA on a deliberately small native stack.

use super::*;
use crate::rholang::Int;
use mettail_runtime::{BoundTerm, FreeVar, OrdVar, Var};
use std::sync::Arc;

fn canon_channel_name_recursive(name: &Name) -> Name {
    let lowered = crate::rholang::receive::normalize_quote_name(name);
    match &lowered {
        Name::NQuote(proc) => Name::NQuote(Arc::new(normalize_recursive(proc))),
        _ => lowered,
    }
}

fn canon_scalar_payload_recursive(payload: &Proc) -> Proc {
    crate::rholang::receive::canonicalize_arity_payload(&normalize_recursive(payload))
}

fn canon_multi_payload_recursive(first: &Proc, rest: &[Proc]) -> Proc {
    let mut items = Vec::with_capacity(1 + rest.len());
    items.push(normalize_recursive(first));
    items.extend(rest.iter().map(normalize_recursive));
    mk_proc_list(items)
}

fn canon_forrow_recursive(row: &ForRow) -> ForRow {
    match row {
        ForRow::ForRowSingleWhere(bind, guard) => {
            ForRow::ForRowSingleWhere(bind.clone(), Arc::new(normalize_recursive(guard)))
        },
        ForRow::ForRowWhere(bind, binds, guard) => {
            ForRow::ForRowWhere(bind.clone(), binds.clone(), Arc::new(normalize_recursive(guard)))
        },
        other => other.clone(),
    }
}

fn normalize_recursive(proc: &Proc) -> Proc {
    let rc = |child: &Arc<Proc>| Arc::new(normalize_recursive(child));
    let rcv = |children: &[Proc]| children.iter().map(normalize_recursive).collect();

    match proc {
        Proc::POutput(name, payload) => Proc::POutput(
            Arc::new(canon_channel_name_recursive(name)),
            Arc::new(canon_scalar_payload_recursive(payload)),
        ),
        Proc::PPersistOutput(name, payload) => Proc::PPersistOutput(
            Arc::new(canon_channel_name_recursive(name)),
            Arc::new(canon_scalar_payload_recursive(payload)),
        ),
        Proc::POutputEmpty(name) => Proc::POutput(
            Arc::new(canon_channel_name_recursive(name)),
            Arc::new(mk_proc_list(vec![])),
        ),
        Proc::PPersistOutputEmpty(name) => Proc::PPersistOutput(
            Arc::new(canon_channel_name_recursive(name)),
            Arc::new(mk_proc_list(vec![])),
        ),
        Proc::POutput2Plus(name, first, rest) => Proc::POutput(
            Arc::new(canon_channel_name_recursive(name)),
            Arc::new(canon_multi_payload_recursive(first, rest)),
        ),
        Proc::PPersistOutput2Plus(name, first, rest) => Proc::PPersistOutput(
            Arc::new(canon_channel_name_recursive(name)),
            Arc::new(canon_multi_payload_recursive(first, rest)),
        ),
        Proc::POutputNil(payload) => Proc::POutput(
            Arc::new(nquote(Proc::PZero)),
            Arc::new(canon_scalar_payload_recursive(payload)),
        ),
        Proc::PPersistOutputNil(payload) => Proc::PPersistOutput(
            Arc::new(nquote(Proc::PZero)),
            Arc::new(canon_scalar_payload_recursive(payload)),
        ),
        Proc::POutputNilEmpty => {
            Proc::POutput(Arc::new(nquote(Proc::PZero)), Arc::new(mk_proc_list(vec![])))
        },
        Proc::PPersistOutputNilEmpty => {
            Proc::PPersistOutput(Arc::new(nquote(Proc::PZero)), Arc::new(mk_proc_list(vec![])))
        },
        Proc::POutputNil2Plus(first, rest) => Proc::POutput(
            Arc::new(nquote(Proc::PZero)),
            Arc::new(canon_multi_payload_recursive(first, rest)),
        ),
        Proc::PPersistOutputNil2Plus(first, rest) => Proc::PPersistOutput(
            Arc::new(nquote(Proc::PZero)),
            Arc::new(canon_multi_payload_recursive(first, rest)),
        ),
        Proc::POutputShort(channel, payload) => Proc::POutput(
            Arc::new(nquote(normalize_recursive(channel))),
            Arc::new(canon_scalar_payload_recursive(payload)),
        ),
        Proc::PPersistOutputShort(channel, payload) => Proc::PPersistOutput(
            Arc::new(nquote(normalize_recursive(channel))),
            Arc::new(canon_scalar_payload_recursive(payload)),
        ),
        Proc::POutputShortEmpty(channel) => Proc::POutput(
            Arc::new(nquote(normalize_recursive(channel))),
            Arc::new(mk_proc_list(vec![])),
        ),
        Proc::PPersistOutputShortEmpty(channel) => Proc::PPersistOutput(
            Arc::new(nquote(normalize_recursive(channel))),
            Arc::new(mk_proc_list(vec![])),
        ),
        Proc::POutputShort2Plus(channel, first, rest) => Proc::POutput(
            Arc::new(nquote(normalize_recursive(channel))),
            Arc::new(canon_multi_payload_recursive(first, rest)),
        ),
        Proc::PPersistOutputShort2Plus(channel, first, rest) => Proc::PPersistOutput(
            Arc::new(nquote(normalize_recursive(channel))),
            Arc::new(canon_multi_payload_recursive(first, rest)),
        ),
        Proc::POutputQuoted(name, payload) => Proc::POutput(
            Arc::new(nquote(crate::rholang::receive::name_pattern_to_proc(name))),
            Arc::new(canon_scalar_payload_recursive(payload)),
        ),
        Proc::POutputQuotedEmpty(name) => Proc::POutput(
            Arc::new(nquote(crate::rholang::receive::name_pattern_to_proc(name))),
            Arc::new(mk_proc_list(vec![])),
        ),
        Proc::POutputQuoted2Plus(name, first, rest) => Proc::POutput(
            Arc::new(nquote(crate::rholang::receive::name_pattern_to_proc(name))),
            Arc::new(canon_multi_payload_recursive(first, rest)),
        ),
        Proc::PParInfix(left, right) => {
            merge_pp_parallel(normalize_recursive(left), normalize_recursive(right))
        },
        Proc::PPar(elements) => {
            let mut out = HashBag::new();
            for (element, count) in elements.iter() {
                let normalized = normalize_recursive(element);
                for _ in 0..count {
                    Proc::insert_into_ppar(&mut out, normalized.clone());
                }
            }
            Proc::PPar(out)
        },
        Proc::PNew(scope) => {
            let (binders, body) = scope.clone().unbind();
            Proc::PNew(mettail_runtime::Scope::new(binders, Arc::new(normalize_recursive(&body))))
        },
        Proc::PForUser(rows, body) => {
            let body = normalize_recursive(body);
            if crate::rholang::receive::pfor_user_still_has_query_rows(rows) {
                normalize_recursive(&crate::rholang::receive::desugar_for_rows(rows.clone(), &body))
            } else {
                Proc::PForUser(rows.iter().map(canon_forrow_recursive).collect(), Arc::new(body))
            }
        },
        Proc::GuardThen(left, right) => Proc::GuardThen(rc(left), rc(right)),
        Proc::CommWhere(first, name, second, third, fourth) => Proc::CommWhere(
            rc(first),
            Arc::new(canon_channel_name_recursive(name)),
            rc(second),
            rc(third),
            rc(fourth),
        ),
        Proc::Or(left, right) => Proc::Or(rc(left), rc(right)),
        Proc::And(left, right) => Proc::And(rc(left), rc(right)),
        Proc::Implies(left, right) => Proc::Implies(rc(left), rc(right)),
        Proc::Matches(left, right) => Proc::Matches(rc(left), rc(right)),
        Proc::SpatialPPar(left, right) => Proc::SpatialPPar(rc(left), rc(right)),
        Proc::BitOr(left, right) => Proc::BitOr(rc(left), rc(right)),
        Proc::BitAnd(left, right) => Proc::BitAnd(rc(left), rc(right)),
        Proc::BitNot(child) => Proc::BitNot(rc(child)),
        Proc::Eq(left, right) => Proc::Eq(rc(left), rc(right)),
        Proc::Ne(left, right) => Proc::Ne(rc(left), rc(right)),
        Proc::Gt(left, right) => Proc::Gt(rc(left), rc(right)),
        Proc::Lt(left, right) => Proc::Lt(rc(left), rc(right)),
        Proc::GtEq(left, right) => Proc::GtEq(rc(left), rc(right)),
        Proc::LtEq(left, right) => Proc::LtEq(rc(left), rc(right)),
        Proc::Add(left, right) => Proc::Add(rc(left), rc(right)),
        Proc::Sub(left, right) => Proc::Sub(rc(left), rc(right)),
        Proc::Mul(left, right) => Proc::Mul(rc(left), rc(right)),
        Proc::Div(left, right) => Proc::Div(rc(left), rc(right)),
        Proc::Mod(left, right) => Proc::Mod(rc(left), rc(right)),
        Proc::NegProc(child) => Proc::NegProc(rc(child)),
        Proc::Not(child) => Proc::Not(rc(child)),
        Proc::ToBool(child) => Proc::ToBool(rc(child)),
        Proc::ToStr(child) => Proc::ToStr(rc(child)),
        Proc::FractionProc(left, right) => Proc::FractionProc(rc(left), rc(right)),
        Proc::IntBinProc(child, width) => Proc::IntBinProc(rc(child), width.clone()),
        Proc::UIntBinProc(child, width) => Proc::UIntBinProc(rc(child), width.clone()),
        Proc::FloatBinProc(child, width) => Proc::FloatBinProc(rc(child), width.clone()),
        Proc::FixedBinProc(child, width) => Proc::FixedBinProc(rc(child), width.clone()),
        Proc::BigintCastProc(child) => Proc::BigintCastProc(rc(child)),
        Proc::BigratCastProc(child) => Proc::BigratCastProc(rc(child)),
        Proc::MethodCall(receiver, method, arguments) => {
            Proc::MethodCall(rc(receiver), method.clone(), rcv(arguments))
        },
        Proc::ApplyProc(left, right) => Proc::ApplyProc(rc(left), rc(right)),
        Proc::MApplyProc(receiver, arguments) => Proc::MApplyProc(rc(receiver), rcv(arguments)),
        Proc::PDrop(name) => Proc::PDrop(Arc::new(canon_channel_name_recursive(name))),
        Proc::CastList(list) => match list.as_ref() {
            List::ListLit(items) => Proc::CastList(Arc::new(List::ListLit(rcv(items)))),
            other => Proc::CastList(Arc::new(other.clone())),
        },
        Proc::CastSet(set) => match set.as_ref() {
            Set::SetLit(items) => Proc::CastSet(Arc::new(Set::SetLit(
                items.iter().map(normalize_recursive).collect(),
            ))),
            other => Proc::CastSet(Arc::new(other.clone())),
        },
        Proc::CastBag(bag) => match bag.as_ref() {
            Bag::BagLit(elements) => {
                let mut out = HashBag::new();
                for (element, count) in elements.iter() {
                    let normalized = normalize_recursive(element);
                    for _ in 0..count {
                        out.insert(normalized.clone());
                    }
                }
                Proc::CastBag(Arc::new(Bag::BagLit(out)))
            },
            other => Proc::CastBag(Arc::new(other.clone())),
        },
        Proc::CastMap(map) => match map.as_ref() {
            Map::MapLit(entries) => Proc::CastMap(Arc::new(Map::MapLit(
                entries
                    .iter()
                    .map(|(key, value)| (normalize_recursive(key), normalize_recursive(value)))
                    .collect(),
            ))),
            other => Proc::CastMap(Arc::new(other.clone())),
        },
        _ => proc.clone(),
    }
}

fn int(value: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(value)))
}

fn sugar(value: i64) -> Proc {
    Proc::POutputNil(Arc::new(int(value)))
}

fn name(label: &str) -> Name {
    Name::NVar(OrdVar(Var::Free(FreeVar::fresh_named(label))))
}

fn assert_equivalent(proc: &Proc, label: &str) {
    let driven = normalize_send_sugar_canon(proc);
    let recursive = normalize_recursive(proc);
    assert!(
        BoundTerm::term_eq(&driven, &recursive),
        "canonical result differs for {label}\ndriven: {driven:?}\nrecursive: {recursive:?}"
    );
}

#[test]
fn runtime_send_canonicalizer_matches_the_bounded_recursive_oracle() {
    let channel_name = Arc::new(Name::NQuoteShort(Arc::new(sugar(1))));
    let quoted_name = Arc::new(Name::NParen(Arc::new(Name::NQuoteShort(Arc::new(int(2))))));
    let scalar = Arc::new(sugar(3));
    let first = Arc::new(sugar(4));
    let rest = vec![sugar(5), sugar(6)];

    let mut corpus = vec![
        Proc::POutput(channel_name.clone(), scalar.clone()),
        Proc::PPersistOutput(channel_name.clone(), scalar.clone()),
        Proc::POutputEmpty(channel_name.clone()),
        Proc::PPersistOutputEmpty(channel_name.clone()),
        Proc::POutput2Plus(channel_name.clone(), first.clone(), rest.clone()),
        Proc::PPersistOutput2Plus(channel_name.clone(), first.clone(), rest.clone()),
        Proc::POutputNil(scalar.clone()),
        Proc::PPersistOutputNil(scalar.clone()),
        Proc::POutputNilEmpty,
        Proc::PPersistOutputNilEmpty,
        Proc::POutputNil2Plus(first.clone(), rest.clone()),
        Proc::PPersistOutputNil2Plus(first.clone(), rest.clone()),
        Proc::POutputShort(Arc::new(sugar(7)), scalar.clone()),
        Proc::PPersistOutputShort(Arc::new(sugar(8)), scalar.clone()),
        Proc::POutputShortEmpty(Arc::new(sugar(9))),
        Proc::PPersistOutputShortEmpty(Arc::new(sugar(10))),
        Proc::POutputShort2Plus(Arc::new(sugar(11)), first.clone(), rest.clone()),
        Proc::PPersistOutputShort2Plus(Arc::new(sugar(12)), first.clone(), rest.clone()),
        Proc::POutputQuoted(quoted_name.clone(), scalar.clone()),
        Proc::POutputQuotedEmpty(quoted_name.clone()),
        Proc::POutputQuoted2Plus(quoted_name.clone(), first.clone(), rest.clone()),
        Proc::GuardThen(Arc::new(sugar(13)), Arc::new(sugar(14))),
        Proc::CommWhere(
            Arc::new(sugar(15)),
            channel_name.clone(),
            Arc::new(sugar(16)),
            Arc::new(sugar(17)),
            Arc::new(sugar(18)),
        ),
        Proc::MethodCall(Arc::new(sugar(19)), "m".to_string(), vec![sugar(20), sugar(21)]),
        Proc::MApplyProc(Arc::new(sugar(22)), vec![sugar(23), sugar(24)]),
        Proc::PDrop(channel_name.clone()),
        Proc::CastList(Arc::new(List::ListLit(vec![sugar(25), sugar(26)]))),
    ];

    macro_rules! binary_cases {
        ($($constructor:path),* $(,)?) => {$({
            corpus.push($constructor(Arc::new(sugar(30)), Arc::new(sugar(31))));
        })*};
    }
    macro_rules! unary_cases {
        ($($constructor:path),* $(,)?) => {$({
            corpus.push($constructor(Arc::new(sugar(32))));
        })*};
    }
    binary_cases!(
        Proc::Or,
        Proc::And,
        Proc::Implies,
        Proc::Matches,
        Proc::SpatialPPar,
        Proc::BitOr,
        Proc::BitAnd,
        Proc::Eq,
        Proc::Ne,
        Proc::Gt,
        Proc::Lt,
        Proc::GtEq,
        Proc::LtEq,
        Proc::Add,
        Proc::Sub,
        Proc::Mul,
        Proc::Div,
        Proc::Mod,
        Proc::FractionProc,
        Proc::ApplyProc,
    );
    unary_cases!(
        Proc::BitNot,
        Proc::NegProc,
        Proc::Not,
        Proc::ToBool,
        Proc::ToStr,
        Proc::BigintCastProc,
        Proc::BigratCastProc,
    );

    let width = Arc::new(Int::NumLit(8));
    corpus.extend([
        Proc::IntBinProc(Arc::new(sugar(33)), width.clone()),
        Proc::UIntBinProc(Arc::new(sugar(34)), width.clone()),
        Proc::FloatBinProc(Arc::new(sugar(35)), width.clone()),
        Proc::FixedBinProc(Arc::new(sugar(36)), width),
    ]);

    let mut parallel = HashBag::new();
    parallel.insert_n(sugar(40), 3);
    parallel.insert(Proc::PParInfix(Arc::new(sugar(41)), Arc::new(sugar(42))));
    corpus.push(Proc::PPar(parallel));
    corpus.push(Proc::PParInfix(Arc::new(sugar(43)), Arc::new(sugar(44))));

    let mut set = mettail_runtime::HashSetLit::new();
    set.insert(sugar(45));
    set.insert(sugar(46));
    corpus.push(Proc::CastSet(Arc::new(Set::SetLit(set))));
    let mut bag = HashBag::new();
    bag.insert_n(sugar(47), 3);
    bag.insert(sugar(48));
    corpus.push(Proc::CastBag(Arc::new(Bag::BagLit(bag))));
    let mut map = mettail_runtime::HashMapLit::new();
    map.insert(sugar(49), sugar(50));
    map.insert(sugar(51), sugar(52));
    corpus.push(Proc::CastMap(Arc::new(Map::MapLit(map))));

    let binders = vec![mettail_runtime::Binder(mettail_runtime::get_or_create_var("canon-new"))];
    corpus.push(Proc::PNew(mettail_runtime::Scope::new(binders, Arc::new(sugar(53)))));

    let bind = Arc::new(crate::rholang::InputBind::InputBind(
        Arc::new(name("pattern")),
        Arc::new(name("channel")),
    ));
    corpus.push(Proc::PForUser(
        vec![ForRow::ForRowSingleWhere(bind.clone(), Arc::new(sugar(54)))],
        Arc::new(sugar(55)),
    ));
    let query = Arc::new(crate::rholang::InputBind::InputBindQuery(
        Arc::new(name("query-pattern")),
        Arc::new(name("query-channel")),
        vec![sugar(56)],
    ));
    corpus.push(Proc::PForUser(vec![ForRow::ForRowSingleNoWhere(query)], Arc::new(sugar(57))));

    for (index, proc) in corpus.iter().enumerate() {
        assert_equivalent(proc, &format!("constructor corpus item {index}"));
        let once = normalize_send_sugar_canon(proc);
        assert!(
            BoundTerm::term_eq(&once, &normalize_send_sugar_canon(&once)),
            "canonicalizer is not idempotent for corpus item {index}"
        );
    }
}

#[test]
fn runtime_send_canonicalizer_is_stack_safe_at_depth_20k() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("surface-send-canon-256k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut unary = sugar(1);
            for _ in 0..DEPTH {
                unary = Proc::Not(Arc::new(unary));
            }
            let normalized = normalize_send_sugar_canon(&unary);
            let mut cursor = &normalized;
            for _ in 0..DEPTH {
                let Proc::Not(inner) = cursor else {
                    panic!("canonicalizer changed the unary spine")
                };
                cursor = inner;
            }
            assert!(matches!(cursor, Proc::POutput(_, _)));

            let mut list = sugar(2);
            for _ in 0..DEPTH {
                list = Proc::CastList(Arc::new(List::ListLit(vec![list])));
            }
            let normalized = normalize_send_sugar_canon(&list);
            let mut cursor = &normalized;
            for _ in 0..DEPTH {
                let Proc::CastList(items) = cursor else {
                    panic!("canonicalizer changed the list spine")
                };
                let List::ListLit(items) = items.as_ref() else {
                    panic!("canonicalizer changed the list literal")
                };
                cursor = &items[0];
            }
            assert!(matches!(cursor, Proc::POutput(_, _)));

            let mut parallel = sugar(3);
            for value in 0..DEPTH {
                parallel = Proc::PParInfix(Arc::new(parallel), Arc::new(int(value as i64)));
            }
            let normalized = normalize_send_sugar_canon(&parallel);
            let Proc::PPar(elements) = &normalized else {
                panic!("parallel canonicalization must return PPar")
            };
            assert_eq!(elements.len(), DEPTH + 1);
        })
        .expect("spawn send canonicalizer depth gate")
        .join()
        .expect("send canonicalizer must not overflow or panic");
}
