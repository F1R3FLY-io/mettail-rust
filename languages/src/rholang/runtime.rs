use super::{Bag, Bool, ForRow, List, Map, Name, Proc, Set};
use mettail_runtime::{BoundTerm, CanonicalFixedPoint, HashBag};

fn is_collection_cast(proc: &Proc) -> bool {
    matches!(proc, Proc::CastList(_) | Proc::CastBag(_) | Proc::CastMap(_) | Proc::CastSet(_))
}

/// Is `proc` a GROUND OPERAND — a datum an operator can decide about right now?
///
/// # Why the operator fold bodies need this
///
/// An `![…]` fold body for a binary operator ends in a `_ => Proc::Err` fallback meaning "these
/// operands have no arm". That conflates two very different situations:
///
/// | situation | example | right disposition |
/// |---|---|---|
/// | the operands ARE data, and the operator is undefined on them | `1 bitand 1.0` | the `error` term |
/// | an operand is still a REDEX | `*@1 + 2` | contribute nothing; let congruence reduce it first |
///
/// The second row is not academic. Dovetail's e-graph puts a redex and its contractum in ONE
/// class, so an `error` produced from the un-reduced operand lands in the *same* class as the real
/// answer produced from the reduced one — and `__weigh` costs the nullary `Err` node (1.0) below
/// `CastBigInt(NumLit(3))` (2.0), so funded 1-best extraction reports **`error`** as the normal
/// form. Measured 2026-07-25: `*(@(1)) + 2` ⇒ `error`, `*(@(1)) == 1` ⇒ `error`
/// (`languages/tests/rholang_tests.rs::congruence::{add_cong, comparison_cong}`; both only ever
/// "passed" because `assert_reduces_to` was vacuous).
///
/// Fixing this in the macro instead — by adding the `Exec`/`ExecQuoteShort`/`ExecParenQuote` LHS
/// head `PDrop` to the generated redex-head set so the fold-readiness gate defers — was
/// implemented and MEASURED: it took the same suite from 9 failures to 104, because `*x` for a
/// free Name `x` is irreducible and must stay a value. The rationale is recorded at the rejection
/// site (`macros/src/gen/runtime/dovetail_report/typed_report.rs`, `generate_helpers`). The
/// distinction is a LANGUAGE fact — which constructors of `Proc` are data — so it lives here.
///
/// The predicate is deliberately *positive*: every ground-data constructor is listed, and
/// everything else (an operator node, a method-call chain, a `*n` drop, a send, a receive, a
/// `new`, a variable) is treated as "not decidable yet".
pub(crate) fn is_ground_operand(proc: &Proc) -> bool {
    matches!(
        proc,
        Proc::CastInt(_)
            | Proc::CastUInt32(_)
            | Proc::CastBigInt(_)
            | Proc::CastBigRat(_)
            | Proc::CastFixed(_)
            | Proc::CastFloat(_)
            | Proc::CastBool(_)
            | Proc::CastStr(_)
            | Proc::CastBytes(_)
            | Proc::CastList(_)
            | Proc::CastBag(_)
            | Proc::CastMap(_)
            | Proc::CastSet(_)
            | Proc::CastPathmap(_)
            | Proc::CastReadZipper(_)
            | Proc::CastWriteZipper(_)
            // `error` is itself data: it must PROPAGATE through an operator, not block it.
            | Proc::Err
            // `Nil` is the unit process — irreducible data for operator purposes.
            | Proc::PZero
    )
}

/// Both operands of a binary operator are ground ⇒ a `_` fallback may legitimately answer the
/// `error` term. See [`is_ground_operand`].
pub(crate) fn both_ground(a: &Proc, b: &Proc) -> bool {
    is_ground_operand(a) && is_ground_operand(b)
}

/// The `_`-fallback disposition for a BINARY operator's `![…]` fold body.
///
/// * both operands ground ⇒ the operator is genuinely undefined at these types ⇒ [`Proc::Err`]
///   (the `error` term), exactly as before;
/// * otherwise ⇒ the redex rebuilt by `redex`. Returning the redex unchanged contributes nothing
///   to its own e-class (a self-union), so congruence gets to reduce the operand and the fold
///   re-fires on the value. See [`is_ground_operand`] for the measurement behind this.
pub(crate) fn binary_fallback(a: &Proc, b: &Proc, redex: impl FnOnce() -> Proc) -> Proc {
    if both_ground(a, b) {
        Proc::Err
    } else {
        redex()
    }
}

/// The unary twin of [`binary_fallback`].
pub(crate) fn unary_fallback(a: &Proc, redex: impl FnOnce() -> Proc) -> Proc {
    if is_ground_operand(a) {
        Proc::Err
    } else {
        redex()
    }
}

/// Applies an ordered fixed-point comparison only when both values have the same declared scale.
pub(crate) fn fixed_ordered_compare(
    a: CanonicalFixedPoint,
    b: CanonicalFixedPoint,
    predicate: impl FnOnce(std::cmp::Ordering) -> bool,
) -> Proc {
    match a.checked_cmp(b) {
        Some(ordering) => Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(predicate(ordering)))),
        None => Proc::Err,
    }
}

fn compare_same_kind_collection_equality(lhs: &Proc, rhs: &Proc) -> Option<bool> {
    match (lhs, rhs) {
        (Proc::CastList(la), Proc::CastList(lb)) => match (la.as_ref(), lb.as_ref()) {
            (List::ListLit(_), List::ListLit(_)) => Some(lhs.term_eq(rhs)),
            _ => None,
        },
        (Proc::CastBag(ba), Proc::CastBag(bb)) => match (ba.as_ref(), bb.as_ref()) {
            (Bag::BagLit(ha), Bag::BagLit(hb)) => {
                let na = normalize_bag_elements(ha);
                let nb = normalize_bag_elements(hb);
                Some(BoundTerm::term_eq(&na, &nb))
            },
            _ => None,
        },
        (Proc::CastMap(ma), Proc::CastMap(mb)) => match (ma.as_ref(), mb.as_ref()) {
            (Map::MapLit(_), Map::MapLit(_)) => Some(lhs.term_eq(rhs)),
            _ => None,
        },
        (Proc::CastSet(sa), Proc::CastSet(sb)) => match (sa.as_ref(), sb.as_ref()) {
            (Set::SetLit(_), Set::SetLit(_)) => Some(lhs.term_eq(rhs)),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn compare_collection_equality(lhs: &Proc, rhs: &Proc) -> Option<bool> {
    match (lhs, rhs) {
        (Proc::CastList(_), Proc::CastList(_))
        | (Proc::CastBag(_), Proc::CastBag(_))
        | (Proc::CastMap(_), Proc::CastMap(_))
        | (Proc::CastSet(_), Proc::CastSet(_)) => compare_same_kind_collection_equality(lhs, rhs),
        (a, b) if is_collection_cast(a) || is_collection_cast(b) => Some(false),
        _ => None,
    }
}

pub(crate) fn mk_proc_list(items: Vec<Proc>) -> Proc {
    Proc::CastList(std::sync::Arc::new(List::ListLit(items)))
}

/// Build `name!(items…)` / `name!!(items…)` under Rholang's SEND ARITY CONVENTION.
///
/// A send carries exactly ONE datum `Par`, so the surface arity is encoded into that datum —
/// and the encoding is three-way, not two-way:
///
/// | surface       | items | datum      | matching bind             |
/// |---------------|-------|------------|---------------------------|
/// | `c!()`        | 0     | `⟦[]⟧`     | `for(<- c)`               |
/// | `c!(p)`       | 1     | `⟦p⟧`      | `for(@p <- c)` — VERBATIM |
/// | `c!(a, b, …)` | ≥2    | `⟦[a,b,…]⟧`| `for(@a, @b… <- c)`       |
///
/// The MONADIC row is the one that is easy to get wrong, because `[p]` looks like a harmless
/// normalization of `p` — and it is, on the term-equality path, where
/// `runtime::canon_scalar_payload` maps a scalar payload to its one-element list precisely so
/// the two spellings compare equal. It is NOT harmless on the LOWERING path, which lowers the
/// payload as written: a `[p]` datum is matched by `for(@[p] <- c)` and NOT by `for(@p <- c)`.
///
/// This function previously wrapped unconditionally, which made a 1-item send unmatchable by
/// the monadic bind it is meant for. The only surface that reaches it is the zero-argument
/// query bind `c!?()`, whose expansion `c!(*r)` carries exactly one item (the private return
/// channel) — so `for(p <- c!?()){…}` sent a datum no ordinary responder `for(@r <- c){…}`
/// could receive. Every `!?` shape test compares through the canon, where the two spellings are
/// the same key, so none of them could see it.
///
/// The convention mirrors `rholang-runtime`'s `desugar_surface_sugar_node`, which is where the
/// same three rows are applied to the parsed send spellings (`POutputEmpty` → `[]`,
/// `POutput` → verbatim, `POutput2Plus` → list).
pub(crate) fn mk_output(name: &super::Name, mut items: Vec<Proc>, persistent: bool) -> Proc {
    let payload = std::sync::Arc::new(match items.len() {
        1 => items
            .pop()
            .expect("a 1-element payload vector has an element"),
        _ => mk_proc_list(items),
    });
    if persistent {
        Proc::PPersistOutput(std::sync::Arc::new(name.clone()), payload)
    } else {
        Proc::POutput(std::sync::Arc::new(name.clone()), payload)
    }
}

pub(crate) fn merge_pp_parallel(mut lhs: Proc, mut rhs: Proc) -> Proc {
    // `PPar` is the canonical, already-flat representation emitted by the generated
    // `insert_into_ppar` constructor. Both operands are owned here, so retain their hash table
    // and its cached element hashes instead of cloning every accumulated member into a fresh
    // bag on every binary fold. Choosing the larger bag bounds a balanced merge to moving the
    // smaller side; a left fold adds only its new right-hand term.
    let lhs_bag = match &mut lhs {
        Proc::PPar(elements) => Some(std::mem::take(elements)),
        _ => None,
    };
    let rhs_bag = match &mut rhs {
        Proc::PPar(elements) => Some(std::mem::take(elements)),
        _ => None,
    };

    let bag = match (lhs_bag, rhs_bag) {
        (Some(mut left), Some(mut right)) => {
            if left.len() < right.len() {
                std::mem::swap(&mut left, &mut right);
            }
            for (element, count) in right {
                left.insert_n(element, count);
            }
            left
        },
        (Some(mut left), None) => {
            left.insert(rhs);
            left
        },
        (None, Some(mut right)) => {
            right.insert(lhs);
            right
        },
        (None, None) => {
            let mut elements = mettail_runtime::HashBag::new();
            elements.insert(lhs);
            elements.insert(rhs);
            elements
        },
    };
    Proc::PPar(bag)
}

pub(crate) fn flatten_proc_parallel_into(out: &mut HashBag<Proc>, root: &Proc) {
    flatten_proc_parallel_n_into(out, root, 1);
}

pub(crate) fn flatten_proc_parallel_n_into(
    out: &mut HashBag<Proc>,
    root: &Proc,
    root_count: usize,
) {
    let mut work = vec![(root, root_count)];
    while let Some((proc, multiplicity)) = work.pop() {
        match proc {
            Proc::PPar(elements) => {
                let start = work.len();
                for (element, count) in elements.iter() {
                    let combined = multiplicity
                        .checked_mul(count)
                        .expect("parallel multiplicity exceeds usize");
                    work.push((element, combined));
                }
                work[start..].reverse();
            },
            Proc::PParInfix(left, right) => {
                work.push((right, multiplicity));
                work.push((left, multiplicity));
            },
            other => out.insert_n(other.clone(), multiplicity),
        }
    }
}

pub(crate) fn normalize_bag_elements(bag: &HashBag<Proc>) -> HashBag<Proc> {
    let mut out = HashBag::new();
    for (elem, count) in bag.iter() {
        flatten_proc_parallel_n_into(&mut out, elem, count);
    }
    out
}

/// The `@`-send-sugar canonicalization (2026-07-06) is UNCONDITIONAL — the former
/// `PRATTAIL_NO_SEND_SUGAR_CANON` A/B kill-switch (and its pre-fix legacy
/// normalizer) was collapsed to its shipped default.
///
/// The `@Nil!(n)` number-as-process projection surface (and every `@`-send
/// sugar) is elected non-deterministically across parse contexts among its
/// eval-equal readings — `POutputNil(q)`, `POutputShort(PZero, q)`, and
/// `POutput(NQuoteNil, q)` all denote `POutput(NQuote(PZero), q)` (send `q` on
/// the null-process channel) but are DISTINCT AST variants that structural
/// `term_eq` does not unify. [`normalize_send_sugar_canon`] canonicalizes every
/// `@`-send sugar to its channel-first `POutput`/`PPersistOutput(NQuote(chan),
/// payload)` fold target, DEEPLY — the projection surface materializes in
/// operator-operand position (`p + @Nil!(1) > @Nil!(0)` nests the sugar inside
/// `Gt`/`Add`), so the canon must reach every Proc subterm.
///
/// RHOLANG-LOCAL: only rholang's `term_eq`/COMM comparison path is affected; the
/// macro-generated `.normalize()`/`semantic_hash` and every other language are
/// untouched.
fn normalize_query_send_sugar_proc(p: &Proc) -> Proc {
    normalize_send_sugar_canon(p)
}

/// M-1b: the same `@`-send-sugar canonicalization, exposed to the formula module.
///
/// `formula::host_matches_verdict` compares a ground pattern with a ground target
/// using the generated structural matcher, which does NOT unify the eval-equal
/// `@`-send spellings — while the Rholang lowering does (they all lower to the
/// same `Par`). Routing both operands through the canon that rholang's own
/// term-equality path already uses is what keeps the host and the machine from
/// disagreeing on a purely notational difference.
pub(crate) fn canon_for_term_equality(p: &Proc) -> Proc {
    normalize_send_sugar_canon(p)
}

fn nquote(p: Proc) -> Name {
    Name::NQuote(std::sync::Arc::new(p))
}

enum SendCanonJob<'a> {
    VisitProc(&'a Proc),
    FinishProc(&'a Proc),
    VisitName(&'a Name),
    FinishNameQuote,
    FinishNew(Vec<mettail_runtime::Binder<String>>),
    FinishQueryFor(&'a [ForRow]),
    FinishParallel(Vec<usize>),
}

fn take_canon_results(results: &mut Vec<Proc>, count: usize) -> Vec<Proc> {
    let start = results
        .len()
        .checked_sub(count)
        .expect("send canonicalizer result-stack underflow");
    results.split_off(start)
}

/// Collect one whole canonical parallel region before normalizing its leaves. A count is carried
/// beside each leaf instead of materializing one job per occurrence.
fn collect_parallel_canon_leaves<'a>(root: &'a Proc, leaves: &mut Vec<(&'a Proc, usize)>) {
    let mut work = vec![(root, 1usize)];
    while let Some((proc, multiplicity)) = work.pop() {
        match proc {
            Proc::PPar(elements) => {
                let start = work.len();
                for (element, count) in elements.iter() {
                    let combined = multiplicity
                        .checked_mul(count)
                        .expect("parallel multiplicity exceeds usize");
                    work.push((element, combined));
                }
                work[start..].reverse();
            },
            Proc::PParInfix(left, right) => {
                work.push((right, multiplicity));
                work.push((left, multiplicity));
            },
            leaf => leaves.push((leaf, multiplicity)),
        }
    }
}

/// Insert an already-normalized process into a canonical `PPar`, consuming the representative and
/// preserving compressed multiplicity. Only `PPar` is transparent here: `PParInfix` has already
/// been normalized by the canonicalizer and is not silently reinterpreted by this helper.
fn insert_owned_ppar_n(out: &mut HashBag<Proc>, root: Proc, root_count: usize) {
    let mut work = vec![(root, root_count)];
    while let Some((mut proc, multiplicity)) = work.pop() {
        if let Proc::PPar(elements) = &mut proc {
            let start = work.len();
            for (element, count) in std::mem::take(elements) {
                let combined = multiplicity
                    .checked_mul(count)
                    .expect("parallel multiplicity exceeds usize");
                work.push((element, combined));
            }
            work[start..].reverse();
        } else {
            out.insert_n(proc, multiplicity);
        }
    }
}

/// Deep `@`-send-sugar canonicalizer (the A/B-ON branch). Rewrites EVERY `@`-send
/// sugar variant to its channel-first `POutput`/`PPersistOutput(NQuote(chan),
/// [args])` fold target and RECURSES into every Proc subterm, so the `@Nil!(n)`
/// number-as-process projection surface unifies wherever it is elected
/// (operator operands, send payloads, containers). Grammar-faithful: each send
/// arm mirrors that rule's own `fold` action (`POutputNil → POutput(NQuote(
/// PZero), q)`, `POutputShort(p,q) → POutput(NQuote(p), q)`, `POutputQuoted(n,q)
/// → POutput(NQuote(name_pattern_to_proc(n)), q)`). Idempotent.
fn normalize_send_sugar_canon(p: &Proc) -> Proc {
    use std::sync::Arc;
    let proc_arena = typed_arena::Arena::<Proc>::new();
    let name_arena = typed_arena::Arena::<Name>::new();
    let mut jobs = vec![SendCanonJob::VisitProc(p)];
    let mut proc_results = Vec::new();
    let mut name_results = Vec::new();

    macro_rules! build_binary {
        ($constructor:path) => {{
            let right = proc_results
                .pop()
                .expect("send canonicalizer binary right result");
            let left = proc_results
                .pop()
                .expect("send canonicalizer binary left result");
            $constructor(Arc::new(left), Arc::new(right))
        }};
    }
    macro_rules! build_unary {
        ($constructor:path) => {{
            let child = proc_results.pop().expect("send canonicalizer unary result");
            $constructor(Arc::new(child))
        }};
    }

    while let Some(job) = jobs.pop() {
        match job {
            SendCanonJob::VisitProc(proc) => match proc {
                Proc::POutput(name, payload) | Proc::PPersistOutput(name, payload) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    let start = jobs.len();
                    jobs.push(SendCanonJob::VisitName(name));
                    jobs.push(SendCanonJob::VisitProc(payload));
                    jobs[start..].reverse();
                },
                Proc::POutputEmpty(name) | Proc::PPersistOutputEmpty(name) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    jobs.push(SendCanonJob::VisitName(name));
                },
                Proc::POutput2Plus(name, first, rest)
                | Proc::PPersistOutput2Plus(name, first, rest) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    let start = jobs.len();
                    jobs.push(SendCanonJob::VisitName(name));
                    jobs.push(SendCanonJob::VisitProc(first));
                    for item in rest {
                        jobs.push(SendCanonJob::VisitProc(item));
                    }
                    jobs[start..].reverse();
                },
                Proc::POutputNil(payload) | Proc::PPersistOutputNil(payload) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    jobs.push(SendCanonJob::VisitProc(payload));
                },
                Proc::POutputNilEmpty | Proc::PPersistOutputNilEmpty => {
                    let payload = Arc::new(mk_proc_list(vec![]));
                    proc_results.push(if matches!(proc, Proc::POutputNilEmpty) {
                        Proc::POutput(Arc::new(nquote(Proc::PZero)), payload)
                    } else {
                        Proc::PPersistOutput(Arc::new(nquote(Proc::PZero)), payload)
                    });
                },
                Proc::POutputNil2Plus(first, rest) | Proc::PPersistOutputNil2Plus(first, rest) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    let start = jobs.len();
                    jobs.push(SendCanonJob::VisitProc(first));
                    for item in rest {
                        jobs.push(SendCanonJob::VisitProc(item));
                    }
                    jobs[start..].reverse();
                },
                Proc::POutputShort(channel, payload)
                | Proc::PPersistOutputShort(channel, payload) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    let start = jobs.len();
                    jobs.push(SendCanonJob::VisitProc(channel));
                    jobs.push(SendCanonJob::VisitProc(payload));
                    jobs[start..].reverse();
                },
                Proc::POutputShortEmpty(channel) | Proc::PPersistOutputShortEmpty(channel) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    jobs.push(SendCanonJob::VisitProc(channel));
                },
                Proc::POutputShort2Plus(channel, first, rest)
                | Proc::PPersistOutputShort2Plus(channel, first, rest) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    let start = jobs.len();
                    jobs.push(SendCanonJob::VisitProc(channel));
                    jobs.push(SendCanonJob::VisitProc(first));
                    for item in rest {
                        jobs.push(SendCanonJob::VisitProc(item));
                    }
                    jobs[start..].reverse();
                },
                Proc::POutputQuoted(_, payload) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    jobs.push(SendCanonJob::VisitProc(payload));
                },
                Proc::POutputQuotedEmpty(name) => proc_results.push(Proc::POutput(
                    Arc::new(nquote(crate::rholang::receive::name_pattern_to_proc(name))),
                    Arc::new(mk_proc_list(vec![])),
                )),
                Proc::POutputQuoted2Plus(_, first, rest) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    let start = jobs.len();
                    jobs.push(SendCanonJob::VisitProc(first));
                    for item in rest {
                        jobs.push(SendCanonJob::VisitProc(item));
                    }
                    jobs[start..].reverse();
                },
                Proc::PPar(_) | Proc::PParInfix(_, _) => {
                    let mut leaves = Vec::new();
                    collect_parallel_canon_leaves(proc, &mut leaves);
                    let counts = leaves.iter().map(|(_, count)| *count).collect();
                    jobs.push(SendCanonJob::FinishParallel(counts));
                    let start = jobs.len();
                    for (leaf, _) in leaves {
                        jobs.push(SendCanonJob::VisitProc(leaf));
                    }
                    jobs[start..].reverse();
                },
                Proc::PNew(scope) => {
                    // This transform neither substitutes variables nor changes binder depth, so
                    // the closed body remains valid and can retain its existing bound-variable
                    // identities. Avoiding unbind/rebind also avoids a freshening traversal.
                    jobs.push(SendCanonJob::FinishNew(scope.unsafe_pattern().clone()));
                    jobs.push(SendCanonJob::VisitProc(scope.unsafe_body()));
                },
                Proc::PForUser(rows, body) => {
                    if crate::rholang::receive::pfor_user_still_has_query_rows(rows) {
                        jobs.push(SendCanonJob::FinishQueryFor(rows));
                        jobs.push(SendCanonJob::VisitProc(body));
                    } else {
                        jobs.push(SendCanonJob::FinishProc(proc));
                        let start = jobs.len();
                        jobs.push(SendCanonJob::VisitProc(body));
                        for row in rows {
                            match row {
                                ForRow::ForRowSingleWhere(_, guard)
                                | ForRow::ForRowWhere(_, _, guard) => {
                                    jobs.push(SendCanonJob::VisitProc(guard));
                                },
                                _ => {},
                            }
                        }
                        jobs[start..].reverse();
                    }
                },
                Proc::CommWhere(first, name, second, third, fourth) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    let start = jobs.len();
                    jobs.push(SendCanonJob::VisitProc(first));
                    jobs.push(SendCanonJob::VisitName(name));
                    jobs.push(SendCanonJob::VisitProc(second));
                    jobs.push(SendCanonJob::VisitProc(third));
                    jobs.push(SendCanonJob::VisitProc(fourth));
                    jobs[start..].reverse();
                },
                Proc::GuardThen(left, right)
                | Proc::Or(left, right)
                | Proc::And(left, right)
                | Proc::Implies(left, right)
                | Proc::Matches(left, right)
                | Proc::SpatialPPar(left, right)
                | Proc::BitOr(left, right)
                | Proc::BitAnd(left, right)
                | Proc::Eq(left, right)
                | Proc::Ne(left, right)
                | Proc::Gt(left, right)
                | Proc::Lt(left, right)
                | Proc::GtEq(left, right)
                | Proc::LtEq(left, right)
                | Proc::Add(left, right)
                | Proc::Sub(left, right)
                | Proc::Mul(left, right)
                | Proc::Div(left, right)
                | Proc::Mod(left, right)
                | Proc::FractionProc(left, right)
                | Proc::ApplyProc(left, right) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    jobs.push(SendCanonJob::VisitProc(right));
                    jobs.push(SendCanonJob::VisitProc(left));
                },
                Proc::BitNot(child)
                | Proc::NegProc(child)
                | Proc::Not(child)
                | Proc::ToBool(child)
                | Proc::ToStr(child)
                | Proc::BigintCastProc(child)
                | Proc::BigratCastProc(child) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    jobs.push(SendCanonJob::VisitProc(child));
                },
                Proc::IntBinProc(child, _)
                | Proc::UIntBinProc(child, _)
                | Proc::FloatBinProc(child, _)
                | Proc::FixedBinProc(child, _) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    jobs.push(SendCanonJob::VisitProc(child));
                },
                Proc::MethodCall(receiver, _, arguments)
                | Proc::MApplyProc(receiver, arguments) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    let start = jobs.len();
                    jobs.push(SendCanonJob::VisitProc(receiver));
                    for argument in arguments {
                        jobs.push(SendCanonJob::VisitProc(argument));
                    }
                    jobs[start..].reverse();
                },
                Proc::PDrop(name) => {
                    jobs.push(SendCanonJob::FinishProc(proc));
                    jobs.push(SendCanonJob::VisitName(name));
                },
                Proc::CastList(list) => match list.as_ref() {
                    List::ListLit(items) => {
                        jobs.push(SendCanonJob::FinishProc(proc));
                        for item in items.iter().rev() {
                            jobs.push(SendCanonJob::VisitProc(item));
                        }
                    },
                    _ => proc_results.push(proc.clone()),
                },
                Proc::CastSet(set) => match set.as_ref() {
                    Set::SetLit(items) => {
                        jobs.push(SendCanonJob::FinishProc(proc));
                        let start = jobs.len();
                        for item in items.iter() {
                            jobs.push(SendCanonJob::VisitProc(item));
                        }
                        jobs[start..].reverse();
                    },
                    _ => proc_results.push(proc.clone()),
                },
                Proc::CastBag(bag) => match bag.as_ref() {
                    Bag::BagLit(elements) => {
                        jobs.push(SendCanonJob::FinishProc(proc));
                        let start = jobs.len();
                        for (element, _) in elements.iter() {
                            jobs.push(SendCanonJob::VisitProc(element));
                        }
                        jobs[start..].reverse();
                    },
                    _ => proc_results.push(proc.clone()),
                },
                Proc::CastMap(map) => match map.as_ref() {
                    Map::MapLit(entries) => {
                        jobs.push(SendCanonJob::FinishProc(proc));
                        let start = jobs.len();
                        for (key, value) in entries.iter() {
                            jobs.push(SendCanonJob::VisitProc(key));
                            jobs.push(SendCanonJob::VisitProc(value));
                        }
                        jobs[start..].reverse();
                    },
                    _ => proc_results.push(proc.clone()),
                },
                // Leaves and deliberately opaque constructors retain their exact representation.
                _ => proc_results.push(proc.clone()),
            },
            SendCanonJob::VisitName(name) => {
                let lowered = crate::rholang::receive::normalize_quote_name(name);
                if matches!(lowered, Name::NQuote(_)) {
                    let lowered = name_arena.alloc(lowered);
                    let Name::NQuote(proc) = lowered else {
                        unreachable!("checked quote name")
                    };
                    jobs.push(SendCanonJob::FinishNameQuote);
                    jobs.push(SendCanonJob::VisitProc(proc));
                } else {
                    name_results.push(lowered);
                }
            },
            SendCanonJob::FinishNameQuote => {
                let proc = proc_results
                    .pop()
                    .expect("send canonicalizer quoted-name result");
                name_results.push(nquote(proc));
            },
            SendCanonJob::FinishNew(binders) => {
                let body = proc_results
                    .pop()
                    .expect("send canonicalizer new-body result");
                proc_results.push(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(
                    binders,
                    Arc::new(body),
                )));
            },
            SendCanonJob::FinishQueryFor(rows) => {
                let body = proc_results
                    .pop()
                    .expect("send canonicalizer query-body result");
                let desugared = proc_arena
                    .alloc(crate::rholang::receive::desugar_for_rows(rows.to_vec(), &body));
                jobs.push(SendCanonJob::VisitProc(desugared));
            },
            SendCanonJob::FinishParallel(counts) => {
                let normalized = take_canon_results(&mut proc_results, counts.len());
                let mut bag = HashBag::new();
                for (proc, count) in normalized.into_iter().zip(counts) {
                    insert_owned_ppar_n(&mut bag, proc, count);
                }
                proc_results.push(Proc::PPar(bag));
            },
            SendCanonJob::FinishProc(template) => {
                let rebuilt = match template {
                    Proc::POutput(_, _) | Proc::PPersistOutput(_, _) => {
                        let payload = proc_results
                            .pop()
                            .expect("send canonicalizer scalar payload");
                        let payload =
                            Arc::new(crate::rholang::receive::canonicalize_arity_payload(&payload));
                        let name =
                            Arc::new(name_results.pop().expect("send canonicalizer channel name"));
                        if matches!(template, Proc::POutput(_, _)) {
                            Proc::POutput(name, payload)
                        } else {
                            Proc::PPersistOutput(name, payload)
                        }
                    },
                    Proc::POutputEmpty(_) | Proc::PPersistOutputEmpty(_) => {
                        let name = Arc::new(
                            name_results
                                .pop()
                                .expect("send canonicalizer empty-send name"),
                        );
                        let payload = Arc::new(mk_proc_list(vec![]));
                        if matches!(template, Proc::POutputEmpty(_)) {
                            Proc::POutput(name, payload)
                        } else {
                            Proc::PPersistOutput(name, payload)
                        }
                    },
                    Proc::POutput2Plus(_, _, rest) | Proc::PPersistOutput2Plus(_, _, rest) => {
                        let payload = Arc::new(mk_proc_list(take_canon_results(
                            &mut proc_results,
                            1 + rest.len(),
                        )));
                        let name = Arc::new(
                            name_results
                                .pop()
                                .expect("send canonicalizer multi-send name"),
                        );
                        if matches!(template, Proc::POutput2Plus(_, _, _)) {
                            Proc::POutput(name, payload)
                        } else {
                            Proc::PPersistOutput(name, payload)
                        }
                    },
                    Proc::POutputNil(_) | Proc::PPersistOutputNil(_) => {
                        let payload = proc_results
                            .pop()
                            .expect("send canonicalizer nil-send payload");
                        let payload =
                            Arc::new(crate::rholang::receive::canonicalize_arity_payload(&payload));
                        if matches!(template, Proc::POutputNil(_)) {
                            Proc::POutput(Arc::new(nquote(Proc::PZero)), payload)
                        } else {
                            Proc::PPersistOutput(Arc::new(nquote(Proc::PZero)), payload)
                        }
                    },
                    Proc::POutputNil2Plus(_, rest) | Proc::PPersistOutputNil2Plus(_, rest) => {
                        let payload = Arc::new(mk_proc_list(take_canon_results(
                            &mut proc_results,
                            1 + rest.len(),
                        )));
                        if matches!(template, Proc::POutputNil2Plus(_, _)) {
                            Proc::POutput(Arc::new(nquote(Proc::PZero)), payload)
                        } else {
                            Proc::PPersistOutput(Arc::new(nquote(Proc::PZero)), payload)
                        }
                    },
                    Proc::POutputShort(_, _) | Proc::PPersistOutputShort(_, _) => {
                        let payload = proc_results
                            .pop()
                            .expect("send canonicalizer short-send payload");
                        let channel = proc_results
                            .pop()
                            .expect("send canonicalizer short-send channel");
                        let payload =
                            Arc::new(crate::rholang::receive::canonicalize_arity_payload(&payload));
                        if matches!(template, Proc::POutputShort(_, _)) {
                            Proc::POutput(Arc::new(nquote(channel)), payload)
                        } else {
                            Proc::PPersistOutput(Arc::new(nquote(channel)), payload)
                        }
                    },
                    Proc::POutputShortEmpty(_) | Proc::PPersistOutputShortEmpty(_) => {
                        let channel = proc_results
                            .pop()
                            .expect("send canonicalizer empty short-send channel");
                        let payload = Arc::new(mk_proc_list(vec![]));
                        if matches!(template, Proc::POutputShortEmpty(_)) {
                            Proc::POutput(Arc::new(nquote(channel)), payload)
                        } else {
                            Proc::PPersistOutput(Arc::new(nquote(channel)), payload)
                        }
                    },
                    Proc::POutputShort2Plus(_, _, rest)
                    | Proc::PPersistOutputShort2Plus(_, _, rest) => {
                        let values = take_canon_results(&mut proc_results, 2 + rest.len());
                        let mut values = values.into_iter();
                        let channel = values.next().expect("short-send channel result");
                        let payload = Arc::new(mk_proc_list(values.collect()));
                        if matches!(template, Proc::POutputShort2Plus(_, _, _)) {
                            Proc::POutput(Arc::new(nquote(channel)), payload)
                        } else {
                            Proc::PPersistOutput(Arc::new(nquote(channel)), payload)
                        }
                    },
                    Proc::POutputQuoted(name, _) => {
                        let payload = proc_results
                            .pop()
                            .expect("send canonicalizer quoted-send payload");
                        Proc::POutput(
                            Arc::new(nquote(crate::rholang::receive::name_pattern_to_proc(name))),
                            Arc::new(crate::rholang::receive::canonicalize_arity_payload(&payload)),
                        )
                    },
                    Proc::POutputQuoted2Plus(name, _, rest) => Proc::POutput(
                        Arc::new(nquote(crate::rholang::receive::name_pattern_to_proc(name))),
                        Arc::new(mk_proc_list(take_canon_results(
                            &mut proc_results,
                            1 + rest.len(),
                        ))),
                    ),
                    Proc::PForUser(rows, _) => {
                        let guard_count = rows
                            .iter()
                            .filter(|row| {
                                matches!(
                                    row,
                                    ForRow::ForRowSingleWhere(_, _) | ForRow::ForRowWhere(_, _, _)
                                )
                            })
                            .count();
                        let values = take_canon_results(&mut proc_results, 1 + guard_count);
                        let mut values = values.into_iter();
                        let body = values.next().expect("send canonicalizer for-body result");
                        let rows = rows
                            .iter()
                            .map(|row| match row {
                                ForRow::ForRowSingleWhere(bind, _) => ForRow::ForRowSingleWhere(
                                    bind.clone(),
                                    Arc::new(values.next().expect("single where-guard result")),
                                ),
                                ForRow::ForRowWhere(bind, binds, _) => ForRow::ForRowWhere(
                                    bind.clone(),
                                    binds.clone(),
                                    Arc::new(values.next().expect("multi where-guard result")),
                                ),
                                other => other.clone(),
                            })
                            .collect();
                        debug_assert!(values.next().is_none());
                        Proc::PForUser(rows, Arc::new(body))
                    },
                    Proc::CommWhere(_, _, _, _, _) => {
                        let fourth = proc_results.pop().expect("comm fourth result");
                        let third = proc_results.pop().expect("comm third result");
                        let second = proc_results.pop().expect("comm second result");
                        let first = proc_results.pop().expect("comm first result");
                        let name = name_results.pop().expect("comm channel result");
                        Proc::CommWhere(
                            Arc::new(first),
                            Arc::new(name),
                            Arc::new(second),
                            Arc::new(third),
                            Arc::new(fourth),
                        )
                    },
                    Proc::GuardThen(_, _) => build_binary!(Proc::GuardThen),
                    Proc::Or(_, _) => build_binary!(Proc::Or),
                    Proc::And(_, _) => build_binary!(Proc::And),
                    Proc::Implies(_, _) => build_binary!(Proc::Implies),
                    Proc::Matches(_, _) => build_binary!(Proc::Matches),
                    Proc::SpatialPPar(_, _) => build_binary!(Proc::SpatialPPar),
                    Proc::BitOr(_, _) => build_binary!(Proc::BitOr),
                    Proc::BitAnd(_, _) => build_binary!(Proc::BitAnd),
                    Proc::Eq(_, _) => build_binary!(Proc::Eq),
                    Proc::Ne(_, _) => build_binary!(Proc::Ne),
                    Proc::Gt(_, _) => build_binary!(Proc::Gt),
                    Proc::Lt(_, _) => build_binary!(Proc::Lt),
                    Proc::GtEq(_, _) => build_binary!(Proc::GtEq),
                    Proc::LtEq(_, _) => build_binary!(Proc::LtEq),
                    Proc::Add(_, _) => build_binary!(Proc::Add),
                    Proc::Sub(_, _) => build_binary!(Proc::Sub),
                    Proc::Mul(_, _) => build_binary!(Proc::Mul),
                    Proc::Div(_, _) => build_binary!(Proc::Div),
                    Proc::Mod(_, _) => build_binary!(Proc::Mod),
                    Proc::FractionProc(_, _) => build_binary!(Proc::FractionProc),
                    Proc::ApplyProc(_, _) => build_binary!(Proc::ApplyProc),
                    Proc::BitNot(_) => build_unary!(Proc::BitNot),
                    Proc::NegProc(_) => build_unary!(Proc::NegProc),
                    Proc::Not(_) => build_unary!(Proc::Not),
                    Proc::ToBool(_) => build_unary!(Proc::ToBool),
                    Proc::ToStr(_) => build_unary!(Proc::ToStr),
                    Proc::BigintCastProc(_) => build_unary!(Proc::BigintCastProc),
                    Proc::BigratCastProc(_) => build_unary!(Proc::BigratCastProc),
                    Proc::IntBinProc(_, width) => {
                        Proc::IntBinProc(Arc::new(proc_results.pop().unwrap()), width.clone())
                    },
                    Proc::UIntBinProc(_, width) => {
                        Proc::UIntBinProc(Arc::new(proc_results.pop().unwrap()), width.clone())
                    },
                    Proc::FloatBinProc(_, width) => {
                        Proc::FloatBinProc(Arc::new(proc_results.pop().unwrap()), width.clone())
                    },
                    Proc::FixedBinProc(_, width) => {
                        Proc::FixedBinProc(Arc::new(proc_results.pop().unwrap()), width.clone())
                    },
                    Proc::MethodCall(_, method, arguments) => {
                        let values = take_canon_results(&mut proc_results, 1 + arguments.len());
                        let mut values = values.into_iter();
                        Proc::MethodCall(
                            Arc::new(values.next().expect("method receiver result")),
                            method.clone(),
                            values.collect(),
                        )
                    },
                    Proc::MApplyProc(_, arguments) => {
                        let values = take_canon_results(&mut proc_results, 1 + arguments.len());
                        let mut values = values.into_iter();
                        Proc::MApplyProc(
                            Arc::new(values.next().expect("multi-apply receiver result")),
                            values.collect(),
                        )
                    },
                    Proc::PDrop(_) => {
                        Proc::PDrop(Arc::new(name_results.pop().expect("drop-name result")))
                    },
                    Proc::CastList(list) => {
                        let List::ListLit(items) = list.as_ref() else {
                            unreachable!("only list literals schedule a finish")
                        };
                        Proc::CastList(Arc::new(List::ListLit(take_canon_results(
                            &mut proc_results,
                            items.len(),
                        ))))
                    },
                    Proc::CastSet(set) => {
                        let Set::SetLit(items) = set.as_ref() else {
                            unreachable!("only set literals schedule a finish")
                        };
                        let values = take_canon_results(&mut proc_results, items.len());
                        let mut out = mettail_runtime::HashSetLit::new();
                        for value in values {
                            out.insert(value);
                        }
                        Proc::CastSet(Arc::new(Set::SetLit(out)))
                    },
                    Proc::CastBag(bag) => {
                        let Bag::BagLit(elements) = bag.as_ref() else {
                            unreachable!("only bag literals schedule a finish")
                        };
                        let values = take_canon_results(&mut proc_results, elements.iter().count());
                        let mut out = HashBag::new();
                        for (value, (_, count)) in values.into_iter().zip(elements.iter()) {
                            out.insert_n(value, count);
                        }
                        Proc::CastBag(Arc::new(Bag::BagLit(out)))
                    },
                    Proc::CastMap(map) => {
                        let Map::MapLit(entries) = map.as_ref() else {
                            unreachable!("only map literals schedule a finish")
                        };
                        let values = take_canon_results(&mut proc_results, entries.len() * 2);
                        let mut values = values.into_iter();
                        let mut out = mettail_runtime::HashMapLit::new();
                        for _ in 0..entries.len() {
                            let key = values.next().expect("map key result");
                            let value = values.next().expect("map value result");
                            out.insert(key, value);
                        }
                        Proc::CastMap(Arc::new(Map::MapLit(out)))
                    },
                    _ => unreachable!("only recursive constructors schedule a finish"),
                };
                proc_results.push(rebuilt);
            },
        }
    }

    assert!(name_results.is_empty(), "unconsumed canonical name results");
    assert_eq!(proc_results.len(), 1, "canonicalizer result imbalance");
    proc_results.pop().expect("canonicalizer root result")
}

#[cfg(test)]
#[path = "../../tests/support/rholang_runtime_recursive_oracle.rs"]
mod recursive_oracle;

impl Proc {
    pub fn term_eq(&self, other: &Self) -> bool {
        let lhs = normalize_query_send_sugar_proc(self);
        let rhs = normalize_query_send_sugar_proc(other);
        mettail_runtime::BoundTerm::term_eq(&lhs, &rhs)
    }

    /// Try exactly one custom COMM rewrite step for `PForUser` receives inside a `PPar`.
    ///
    /// This is useful for bounded semantic assertions in tests where full fixpoint search may diverge
    /// (e.g. persistent receive + persistent send loops).
    pub fn try_comm_once(&self) -> Option<Self> {
        let normalized = normalize_query_send_sugar_proc(self);
        crate::rholang::receive::try_comm_rw_proc(&normalized)
    }
}
