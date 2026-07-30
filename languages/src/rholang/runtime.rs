use super::{Bag, Bytes, ForRow, Int, List, Map, Name, Proc, Set, Str};
use mettail_runtime::{BoundTerm, HashBag};

// ══════════════════════════════════════════════════════════════════════════════════════════
// The byte-array methods (2026-07-30)
// ══════════════════════════════════════════════════════════════════════════════════════════
//
// Reachable only since the `b"…"` literal (`713e0364`) gave `Bytes` a surface. The upstream
// definitions these mirror are in `f1r3node-rust-mettail/rholang/src/rust/interpreter/reduce.rs`
// and are cited per function; the fold lane must agree with the machine lane, and before these
// arms existed it did not — `b"dead".length()` folded to the `error` term while the reducer
// answered `2`.

/// The ground byte payload of a `Proc`, or `None` when it is not a ground byte array.
///
/// One extractor, so every byte-method arm agrees about what "a byte array" is. A `Bytes` that is
/// still a variable or a redex yields `None`, which the callers turn into "no arm" rather than
/// into a wrong answer.
fn ground_bytes(proc: &Proc) -> Option<&Vec<u8>> {
    match proc {
        Proc::CastBytes(inner) => match inner.as_ref() {
            Bytes::BytesLit(bytes) => Some(bytes),
            _ => None,
        },
        _ => None,
    }
}

/// Wrap a byte vector as a `Proc`.
fn proc_bytes(bytes: Vec<u8>) -> Proc {
    Proc::CastBytes(std::sync::Arc::new(Bytes::BytesLit(bytes)))
}

/// `"…".hexToBytes()` — upstream `reduce.rs:4849`, whose decoder is
/// `StringOps::unsafe_decode_hex` (`models/src/rust/string_ops.rs:17-28`).
///
/// ⚠ **THE FILTER-AND-PAD BEHAVIOUR IS REPRODUCED DELIBERATELY, AND MUST NOT BE "FIXED".**
/// Upstream FILTERS every non-hex-digit character out of the input and then LEFT-PADS an
/// odd-length result with a `0` nibble, with the comment *"Match Scala Base16.unsafeDecode"*. The
/// consequences are lossy and surprising:
///
/// | input | upstream result | why |
/// |---|---|---|
/// | `"deadbeef"` | `[de ad be ef]` | the ordinary case |
/// | `"abc"` | `[0a bc]` | odd length ⇒ left-padded to `"0abc"` |
/// | `"de-ad"` | `[de ad]` | `-` is filtered out |
/// | `"hello world"` | `[ed]` | only `e` and `d` are hex digits |
///
/// It is nonetheless the CORRECT behaviour to implement here, and rejecting the odd or dirty input
/// would be the defect. `hexToBytes` is consensus-reachable upstream — `Registry.rho` calls it on
/// public keys — so its decoder decides COMPUTED VALUES on a live path. Upstream is a floor on
/// semantics: a deliberate, documented, load-bearing behaviour is not a bug to repair. Pinned by
/// `languages/tests/rholang_byte_methods.rs::hex_to_bytes_filters_and_pads_exactly_as_upstream_does`.
///
/// ★ NOTE THE ASYMMETRY WITH THE LITERAL, WHICH IS INTENTIONAL. The `b"…"` literal's decoder
/// (`languages/src/rholang.rs`, the `literals { Bytes { … } }` eval) accepts ONLY an even run of
/// hex digits, because a literal's job is to have exactly one reading and the regex can enforce
/// that at the lexer. A METHOD's argument is run-time data that upstream has already decided how
/// to interpret. Two decoders, two different jobs; neither should be made to serve the other.
pub(crate) fn fold_hex_to_bytes(receiver: &Proc) -> Proc {
    let text = match receiver {
        Proc::CastStr(inner) => match inner.as_ref() {
            Str::StringLit(text) => text,
            _ => return Proc::Err,
        },
        _ => return Proc::Err,
    };
    // Upstream step 1: keep only ASCII hex digits.
    let digits: Vec<u8> = text
        .bytes()
        .filter(|byte| byte.is_ascii_hexdigit())
        .collect();
    // Upstream step 2: left-pad an odd count with a zero nibble. Preallocated at the exact final
    // byte count, which is `ceil(digits / 2)`.
    let mut decoded: Vec<u8> = Vec::with_capacity(digits.len().div_ceil(2));
    let mut pending_high_nibble: Option<u8> = if digits.len() % 2 == 0 { None } else { Some(0) };
    for digit in digits {
        // Total on the filtered alphabet — `is_ascii_hexdigit` admits exactly these three ranges,
        // so the `else` branch is unreachable and is answered rather than asserted (a `panic!`
        // here would abort the process under the cranelift dev backend).
        let nibble = match digit {
            b'0'..=b'9' => digit - b'0',
            b'a'..=b'f' => digit - b'a' + 10,
            b'A'..=b'F' => digit - b'A' + 10,
            _ => return Proc::Err,
        };
        match pending_high_nibble {
            None => pending_high_nibble = Some(nibble),
            Some(high) => {
                decoded.push((high << 4) | nibble);
                pending_high_nibble = None;
            },
        }
    }
    match pending_high_nibble {
        // Unreachable: the parity was fixed before the loop. Fail closed rather than assert.
        Some(_) => Proc::Err,
        None => proc_bytes(decoded),
    }
}

/// `b"…".bytesToHex()` — upstream `reduce.rs:4893`,
/// `bytes.iter().map(|byte| format!("{:02x}", byte)).collect()`. Lowercase, two digits per byte,
/// so leading zeros are preserved and the result is a word of the `b"…"` literal language.
pub(crate) fn fold_bytes_to_hex(receiver: &Proc) -> Proc {
    let Some(bytes) = ground_bytes(receiver) else {
        return Proc::Err;
    };
    const HEX_DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut rendered = String::with_capacity(2 * bytes.len());
    for byte in bytes {
        rendered.push(HEX_DIGITS[(*byte >> 4) as usize] as char);
        rendered.push(HEX_DIGITS[(*byte & 0x0f) as usize] as char);
    }
    Proc::CastStr(std::sync::Arc::new(Str::StringLit(rendered)))
}

/// `"…".toUtf8Bytes()` — upstream `reduce.rs:4948`, `utf8_string.as_bytes().to_vec()`.
///
/// ⚠ A DIFFERENT FUNCTION FROM `hexToBytes`, and the pair `"dead"` separates them sharply: as hex
/// it is the two bytes `de ad`, as UTF-8 it is the four bytes `64 65 61 64`. Rust's `String` is
/// UTF-8 by construction, so this is total and lossless in the direction it runs.
pub(crate) fn fold_to_utf8_bytes(receiver: &Proc) -> Proc {
    match receiver {
        Proc::CastStr(inner) => match inner.as_ref() {
            Str::StringLit(text) => proc_bytes(text.as_bytes().to_vec()),
            _ => Proc::Err,
        },
        _ => Proc::Err,
    }
}

/// The byte-array arm of `nth` / `last`: the UNSIGNED byte at `index`, as an `Int`.
///
/// Upstream `reduce.rs:4670` (`nth`) and `:4753` (`last`, which binds the index to
/// `len.saturating_sub(1)` and then runs `nth`'s arm verbatim). ⚠ `new_gint_par(b as i64, …)` —
/// the cast is from `u8`, so `0x80` is `128` and never `-128`; upstream's own comment on that line
/// reads *"Convert to unsigned"*. Out of range is the `error` term, matching what every other
/// out-of-domain collection access answers here.
pub(crate) fn fold_bytes_nth(receiver: &Proc, index: usize) -> Option<Proc> {
    let bytes = ground_bytes(receiver)?;
    Some(match bytes.get(index) {
        Some(byte) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(i64::from(*byte)))),
        None => Proc::Err,
    })
}

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

pub(crate) fn mk_proc_set(items: impl IntoIterator<Item = Proc>) -> Proc {
    let mut set = mettail_runtime::HashSetLit::new();
    for item in items {
        set.insert(item);
    }
    Proc::CastSet(std::sync::Arc::new(Set::SetLit(set)))
}

pub(crate) fn normalize_collection_element(elem: &Proc) -> Proc {
    match elem {
        Proc::PDrop(n) => match n.as_ref() {
            super::Name::NQuote(p) => p.as_ref().clone(),
            super::Name::NParen(inner) => match inner.as_ref() {
                super::Name::NQuote(p) => p.as_ref().clone(),
                _ => elem.clone(),
            },
            _ => elem.clone(),
        },
        _ => elem.clone(),
    }
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

pub(crate) fn merge_pp_parallel(lhs: Proc, rhs: Proc) -> Proc {
    let mut bag = mettail_runtime::HashBag::new();
    fn flatten(bag: &mut mettail_runtime::HashBag<Proc>, p: Proc) {
        // `Proc` implements `Drop`; match by reference so we don't move `ps` out of
        // it. The catch-all still owns `p` (the borrow ends before the arm body).
        match &p {
            Proc::PPar(ps) => {
                for (elem, count) in ps.iter() {
                    for _ in 0..count {
                        flatten(bag, elem.clone());
                    }
                }
            },
            _ => bag.insert(p),
        }
    }
    flatten(&mut bag, lhs);
    flatten(&mut bag, rhs);
    Proc::PPar(bag)
}

pub(crate) fn normalize_bag_elements(bag: &HashBag<Proc>) -> HashBag<Proc> {
    fn flatten_proc_into_bag(out: &mut HashBag<Proc>, p: &Proc) {
        match p {
            Proc::PPar(ps) => {
                for (elem, count) in ps.iter() {
                    for _ in 0..count {
                        flatten_proc_into_bag(out, elem);
                    }
                }
            },
            Proc::PParInfix(a, b) => {
                flatten_proc_into_bag(out, a);
                flatten_proc_into_bag(out, b);
            },
            other => {
                out.insert(other.clone());
            },
        }
    }

    let mut out = HashBag::new();
    for (elem, count) in bag.iter() {
        for _ in 0..count {
            flatten_proc_into_bag(&mut out, elem);
        }
    }
    out
}

/// Length of a folded `CastStr` / `CastList` / `CastMap` / `CastBag` / `CastSet` literal.
pub(crate) fn fold_proc_length(p: &Proc) -> Proc {
    match p {
        Proc::CastStr(inner) => match &**inner {
            Str::StringLit(x) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(x.len() as i64))),
            _ => Proc::Err,
        },
        Proc::CastList(l) => match l.as_ref() {
            List::ListLit(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v.len() as i64))),
            _ => Proc::Err,
        },
        Proc::CastMap(m) => match m.as_ref() {
            Map::MapLit(ref payload) => {
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(payload.len() as i64)))
            },
            _ => Proc::Err,
        },
        Proc::CastBag(b) => match b.as_ref() {
            Bag::BagLit(h) => {
                let normalized = normalize_bag_elements(h);
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(normalized.len() as i64)))
            },
            _ => Proc::Err,
        },
        Proc::CastSet(s) => match s.as_ref() {
            Set::SetLit(ref payload) => {
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(payload.len() as i64)))
            },
            _ => Proc::Err,
        },
        // ★ THE BYTE ARM (2026-07-30) — upstream `reduce.rs:8775`,
        // `GByteArray(bytes) => new_gint_expr(bytes.len() as i64)`.
        //
        // ⚠ Its absence was a FOLD/MACHINE DISAGREEMENT, not merely a missing feature. `length` IS
        // a key of the interpreter's `method_table`, so `l.length()` lowers to `EMethod("length")`
        // and the reducer has answered correctly for a byte array all along; this lane answered the
        // `error` term. It was unreachable only because `Bytes` had no surface, so the disagreement
        // became live at the moment the `b"…"` literal landed and is repaired in the same campaign.
        //
        // The unit is BYTES, not hex digits: `b"dead"` is two bytes.
        Proc::CastBytes(b) => match b.as_ref() {
            Bytes::BytesLit(bytes) => {
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(bytes.len() as i64)))
            },
            _ => Proc::Err,
        },
        _ => Proc::Err,
    }
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

// ── canonical channel Name for a send: lower @Nil/@P name sugar, recurse the quoted proc ──
fn canon_channel_name(n: &Name) -> Name {
    // `Name` implements `Drop`; match by reference so we don't move a field out.
    let lowered = crate::rholang::receive::normalize_quote_name(n);
    match &lowered {
        Name::NQuote(p) => {
            Name::NQuote(std::sync::Arc::new(normalize_send_sugar_canon(p.as_ref())))
        },
        _ => lowered,
    }
}

fn nquote(p: Proc) -> Name {
    Name::NQuote(std::sync::Arc::new(p))
}

/// Scalar-send canonical payload: recurse into the payload, then arity-normalize
/// (scalar `q` → one-element list `[q]`, `CastList` kept, `PZero` → `[]`).
fn canon_scalar_payload(q: &Proc) -> Proc {
    crate::rholang::receive::canonicalize_arity_payload(&normalize_send_sugar_canon(q))
}

/// Polyadic-send canonical payload: `mk_proc_list([canon(a), ..canon(bs)])`.
fn canon_multi_payload(a: &Proc, bs: &[Proc]) -> Proc {
    let mut items = Vec::with_capacity(1 + bs.len());
    items.push(normalize_send_sugar_canon(a));
    items.extend(bs.iter().map(normalize_send_sugar_canon));
    mk_proc_list(items)
}

/// Canonicalize a `for`-row: the `where`-guard is a `Proc` that carries the
/// `@Nil!(n)` number-encoded operands (`for(p<-r where p + @Nil!(1) > @Nil!(0))`),
/// so it must be canonicalized like any other Proc subterm. The bind channels
/// are left as-is (the guard is where the projection surface materializes).
fn canon_forrow(row: &ForRow) -> ForRow {
    match row {
        ForRow::ForRowSingleWhere(b, guard) => ForRow::ForRowSingleWhere(
            b.clone(),
            std::sync::Arc::new(normalize_send_sugar_canon(guard.as_ref())),
        ),
        ForRow::ForRowWhere(b, bs, guard) => ForRow::ForRowWhere(
            b.clone(),
            bs.clone(),
            std::sync::Arc::new(normalize_send_sugar_canon(guard.as_ref())),
        ),
        other => other.clone(),
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
    let rc = |a: &Arc<Proc>| Arc::new(normalize_send_sugar_canon(a.as_ref()));
    let rcv = |v: &[Proc]| -> Vec<Proc> { v.iter().map(normalize_send_sugar_canon).collect() };

    match p {
        // ═══ @-send sugar → canonical POutput/PPersistOutput(NQuote(chan), payload) ═══
        // channel-first (n:Name): lower the channel name, recurse/arity the payload.
        Proc::POutput(n, q) => {
            Proc::POutput(Arc::new(canon_channel_name(n)), Arc::new(canon_scalar_payload(q)))
        },
        Proc::PPersistOutput(n, q) => {
            Proc::PPersistOutput(Arc::new(canon_channel_name(n)), Arc::new(canon_scalar_payload(q)))
        },
        Proc::POutputEmpty(n) => {
            Proc::POutput(Arc::new(canon_channel_name(n)), Arc::new(mk_proc_list(vec![])))
        },
        Proc::PPersistOutputEmpty(n) => {
            Proc::PPersistOutput(Arc::new(canon_channel_name(n)), Arc::new(mk_proc_list(vec![])))
        },
        Proc::POutput2Plus(n, a, bs) => {
            Proc::POutput(Arc::new(canon_channel_name(n)), Arc::new(canon_multi_payload(a, bs)))
        },
        Proc::PPersistOutput2Plus(n, a, bs) => Proc::PPersistOutput(
            Arc::new(canon_channel_name(n)),
            Arc::new(canon_multi_payload(a, bs)),
        ),
        // @Nil (fixed PZero channel)
        Proc::POutputNil(q) => {
            Proc::POutput(Arc::new(nquote(Proc::PZero)), Arc::new(canon_scalar_payload(q)))
        },
        Proc::PPersistOutputNil(q) => {
            Proc::PPersistOutput(Arc::new(nquote(Proc::PZero)), Arc::new(canon_scalar_payload(q)))
        },
        Proc::POutputNilEmpty => {
            Proc::POutput(Arc::new(nquote(Proc::PZero)), Arc::new(mk_proc_list(vec![])))
        },
        Proc::PPersistOutputNilEmpty => {
            Proc::PPersistOutput(Arc::new(nquote(Proc::PZero)), Arc::new(mk_proc_list(vec![])))
        },
        Proc::POutputNil2Plus(a, bs) => {
            Proc::POutput(Arc::new(nquote(Proc::PZero)), Arc::new(canon_multi_payload(a, bs)))
        },
        Proc::PPersistOutputNil2Plus(a, bs) => Proc::PPersistOutput(
            Arc::new(nquote(Proc::PZero)),
            Arc::new(canon_multi_payload(a, bs)),
        ),
        // @P short (p:Proc channel → NQuote(p))
        Proc::POutputShort(pc, q) => Proc::POutput(
            Arc::new(nquote(normalize_send_sugar_canon(pc))),
            Arc::new(canon_scalar_payload(q)),
        ),
        Proc::PPersistOutputShort(pc, q) => Proc::PPersistOutput(
            Arc::new(nquote(normalize_send_sugar_canon(pc))),
            Arc::new(canon_scalar_payload(q)),
        ),
        Proc::POutputShortEmpty(pc) => Proc::POutput(
            Arc::new(nquote(normalize_send_sugar_canon(pc))),
            Arc::new(mk_proc_list(vec![])),
        ),
        Proc::PPersistOutputShortEmpty(pc) => Proc::PPersistOutput(
            Arc::new(nquote(normalize_send_sugar_canon(pc))),
            Arc::new(mk_proc_list(vec![])),
        ),
        Proc::POutputShort2Plus(pc, a, bs) => Proc::POutput(
            Arc::new(nquote(normalize_send_sugar_canon(pc))),
            Arc::new(canon_multi_payload(a, bs)),
        ),
        Proc::PPersistOutputShort2Plus(pc, a, bs) => Proc::PPersistOutput(
            Arc::new(nquote(normalize_send_sugar_canon(pc))),
            Arc::new(canon_multi_payload(a, bs)),
        ),
        // @n quoted (n:Name → NQuote(name_pattern_to_proc(n)))
        Proc::POutputQuoted(n, q) => Proc::POutput(
            Arc::new(nquote(crate::rholang::receive::name_pattern_to_proc(n))),
            Arc::new(canon_scalar_payload(q)),
        ),
        Proc::POutputQuotedEmpty(n) => Proc::POutput(
            Arc::new(nquote(crate::rholang::receive::name_pattern_to_proc(n))),
            Arc::new(mk_proc_list(vec![])),
        ),
        Proc::POutputQuoted2Plus(n, a, bs) => Proc::POutput(
            Arc::new(nquote(crate::rholang::receive::name_pattern_to_proc(n))),
            Arc::new(canon_multi_payload(a, bs)),
        ),

        // ═══ containers / binders (recurse; keep the PForUser query-send desugar) ═══
        Proc::PParInfix(a, b) => {
            merge_pp_parallel(normalize_send_sugar_canon(a), normalize_send_sugar_canon(b))
        },
        Proc::PPar(ps) => {
            let mut out = mettail_runtime::HashBag::new();
            for (elem, count) in ps.iter() {
                let norm_elem = normalize_send_sugar_canon(elem);
                for _ in 0..count {
                    Proc::insert_into_ppar(&mut out, norm_elem.clone());
                }
            }
            Proc::PPar(out)
        },
        Proc::PNew(scope) => {
            let (binders, body) = scope.clone().unbind();
            let norm_body = normalize_send_sugar_canon(&body);
            Proc::PNew(mettail_runtime::Scope::new(binders, Arc::new(norm_body)))
        },
        Proc::PForUser(rows, body) => {
            let body_norm = normalize_send_sugar_canon(body.as_ref());
            if crate::rholang::receive::pfor_user_still_has_query_rows(rows) {
                normalize_send_sugar_canon(&crate::rholang::receive::desugar_for_rows(
                    rows.clone(),
                    &body_norm,
                ))
            } else {
                // The `where`-guard (which carries `@Nil!(n)` number-encoded operands) lives in
                // the ForRow, not the body — canon each row's guard.
                let rows_norm: Vec<ForRow> = rows.iter().map(canon_forrow).collect();
                Proc::PForUser(rows_norm, Arc::new(body_norm))
            }
        },
        Proc::GuardThen(a, b) => Proc::GuardThen(rc(a), rc(b)),
        Proc::CommWhere(a, n, b, c, d) => {
            Proc::CommWhere(rc(a), Arc::new(canon_channel_name(n)), rc(b), rc(c), rc(d))
        },

        // ═══ Proc operators (the projection-surface operand positions) — recurse ═══
        Proc::Or(a, b) => Proc::Or(rc(a), rc(b)),
        Proc::And(a, b) => Proc::And(rc(a), rc(b)),
        // M-0: `implies` recurses like its propositional siblings so send-sugar inside either
        // operand canonicalizes (otherwise the identity arm would freeze the sugar in place).
        Proc::Implies(a, b) => Proc::Implies(rc(a), rc(b)),
        // M-1b: the spatial surface. `matches` canonicalizes BOTH operands — the
        // target because it is an ordinary term, and the FORMULA because a formula
        // is a `Proc` sub-tree read as a pattern, so a send-sugar spelling inside it
        // must reach the same canonical form the term it is meant to match does.
        // Canonicalizing only one side would make `@Nil!(1) matches @Nil!(1)` depend
        // on which sugar each side happened to be written in.
        Proc::Matches(a, b) => Proc::Matches(rc(a), rc(b)),
        Proc::SpatialPPar(a, b) => Proc::SpatialPPar(rc(a), rc(b)),
        Proc::BitOr(a, b) => Proc::BitOr(rc(a), rc(b)),
        Proc::BitAnd(a, b) => Proc::BitAnd(rc(a), rc(b)),
        Proc::BitNot(a) => Proc::BitNot(rc(a)),
        Proc::Eq(a, b) => Proc::Eq(rc(a), rc(b)),
        Proc::Ne(a, b) => Proc::Ne(rc(a), rc(b)),
        Proc::Gt(a, b) => Proc::Gt(rc(a), rc(b)),
        Proc::Lt(a, b) => Proc::Lt(rc(a), rc(b)),
        Proc::GtEq(a, b) => Proc::GtEq(rc(a), rc(b)),
        Proc::LtEq(a, b) => Proc::LtEq(rc(a), rc(b)),
        Proc::Add(a, b) => Proc::Add(rc(a), rc(b)),
        Proc::Sub(a, b) => Proc::Sub(rc(a), rc(b)),
        Proc::Mul(a, b) => Proc::Mul(rc(a), rc(b)),
        Proc::Div(a, b) => Proc::Div(rc(a), rc(b)),
        Proc::Mod(a, b) => Proc::Mod(rc(a), rc(b)),
        Proc::NegProc(a) => Proc::NegProc(rc(a)),
        Proc::Not(a) => Proc::Not(rc(a)),
        Proc::ToBool(a) => Proc::ToBool(rc(a)),
        Proc::ToStr(a) => Proc::ToStr(rc(a)),
        Proc::FractionProc(a, b) => Proc::FractionProc(rc(a), rc(b)),
        Proc::IntBinProc(a, w) => Proc::IntBinProc(rc(a), w.clone()),
        Proc::UIntBinProc(a, w) => Proc::UIntBinProc(rc(a), w.clone()),
        Proc::FloatBinProc(a, w) => Proc::FloatBinProc(rc(a), w.clone()),
        Proc::FixedBinProc(a, w) => Proc::FixedBinProc(rc(a), w.clone()),
        Proc::BigintCastProc(a) => Proc::BigintCastProc(rc(a)),
        Proc::BigratCastProc(a) => Proc::BigratCastProc(rc(a)),
        // map / list / bag / set method ops
        Proc::MGet(a, b) => Proc::MGet(rc(a), rc(b)),
        Proc::MSet(a, b, c) => Proc::MSet(rc(a), rc(b), rc(c)),
        Proc::MContains(a, b) => Proc::MContains(rc(a), rc(b)),
        Proc::MDelete(a, b) => Proc::MDelete(rc(a), rc(b)),
        Proc::MUnion(a, b) => Proc::MUnion(rc(a), rc(b)),
        Proc::MSize(a) => Proc::MSize(rc(a)),
        Proc::MToByteArray(a) => Proc::MToByteArray(rc(a)),
        Proc::MKeys(a) => Proc::MKeys(rc(a)),
        Proc::MValues(a) => Proc::MValues(rc(a)),
        Proc::LLength(a) => Proc::LLength(rc(a)),
        Proc::LNth(a, b) => Proc::LNth(rc(a), rc(b)),
        Proc::LLast(a) => Proc::LLast(rc(a)),
        Proc::LConcat(a, b) => Proc::LConcat(rc(a), rc(b)),
        Proc::BCount(a, b) => Proc::BCount(rc(a), rc(b)),
        Proc::BDiff(a, b) => Proc::BDiff(rc(a), rc(b)),
        Proc::BRemove(a, b) => Proc::BRemove(rc(a), rc(b)),
        Proc::SAdd(a, b) => Proc::SAdd(rc(a), rc(b)),
        // pathmap / zipper ops (Proc-arg positions)
        Proc::PRestrict(a, b) => Proc::PRestrict(rc(a), rc(b)),
        Proc::PSubtract(a, b) => Proc::PSubtract(rc(a), rc(b)),
        Proc::PMeet(a, b) => Proc::PMeet(rc(a), rc(b)),
        Proc::PGetSubtrie(a) => Proc::PGetSubtrie(rc(a)),
        Proc::PGetSubtrieAt(a, b) => Proc::PGetSubtrieAt(rc(a), rc(b)),
        Proc::PReadZipper(a) => Proc::PReadZipper(rc(a)),
        Proc::PReadZipperAt(a, b) => Proc::PReadZipperAt(rc(a), rc(b)),
        Proc::PWriteZipper(a) => Proc::PWriteZipper(rc(a)),
        Proc::PWriteZipperAt(a, b) => Proc::PWriteZipperAt(rc(a), rc(b)),
        Proc::RZGetLeaf(a) => Proc::RZGetLeaf(rc(a)),
        Proc::RZDescendTo(a, b) => Proc::RZDescendTo(rc(a), rc(b)),
        Proc::RZChildCount(a) => Proc::RZChildCount(rc(a)),
        Proc::RZDescendFirst(a) => Proc::RZDescendFirst(rc(a)),
        Proc::RZToNextSibling(a) => Proc::RZToNextSibling(rc(a)),
        Proc::RZToPrevSibling(a) => Proc::RZToPrevSibling(rc(a)),
        Proc::RZDescendIndexedBranch(a, b) => Proc::RZDescendIndexedBranch(rc(a), rc(b)),
        Proc::RZAscendOne(a) => Proc::RZAscendOne(rc(a)),
        Proc::RZAscend(a, b) => Proc::RZAscend(rc(a), rc(b)),
        Proc::WZSetLeaf(a, b, c) => Proc::WZSetLeaf(rc(a), rc(b), rc(c)),
        Proc::WZSetSubtrie(a, b) => Proc::WZSetSubtrie(rc(a), rc(b)),
        Proc::WZRemoveLeaf(a) => Proc::WZRemoveLeaf(rc(a)),
        Proc::WZRemoveBranches(a) => Proc::WZRemoveBranches(rc(a)),
        Proc::WZGraft(a, b) => Proc::WZGraft(rc(a), rc(b)),
        Proc::WZJoinInto(a, b) => Proc::WZJoinInto(rc(a), rc(b)),
        // application (λ-bodies carry no operand projection surface → left to the identity arm)
        Proc::ApplyProc(a, b) => Proc::ApplyProc(rc(a), rc(b)),
        Proc::MApplyProc(a, bs) => Proc::MApplyProc(rc(a), rcv(bs)),
        // `*n` deref: recurse into the (possibly quoted) channel's process
        Proc::PDrop(n) => Proc::PDrop(Arc::new(canon_channel_name(n))),

        // ═══ collection literals — recurse into elements ═══
        Proc::CastList(l) => match l.as_ref() {
            List::ListLit(v) => Proc::CastList(Arc::new(List::ListLit(rcv(v)))),
            other => Proc::CastList(Arc::new(other.clone())),
        },
        Proc::CastSet(s) => match s.as_ref() {
            Set::SetLit(items) => {
                let mut set = mettail_runtime::HashSetLit::new();
                for e in items.iter() {
                    set.insert(normalize_send_sugar_canon(e));
                }
                Proc::CastSet(Arc::new(Set::SetLit(set)))
            },
            other => Proc::CastSet(Arc::new(other.clone())),
        },
        Proc::CastBag(bag) => match bag.as_ref() {
            Bag::BagLit(h) => {
                let mut out = mettail_runtime::HashBag::new();
                for (e, c) in h.iter() {
                    let e2 = normalize_send_sugar_canon(e);
                    for _ in 0..c {
                        out.insert(e2.clone());
                    }
                }
                Proc::CastBag(Arc::new(Bag::BagLit(out)))
            },
            other => Proc::CastBag(Arc::new(other.clone())),
        },
        Proc::CastMap(m) => match m.as_ref() {
            Map::MapLit(entries) => {
                let mut out = mettail_runtime::HashMapLit::new();
                for (k, v) in entries.iter() {
                    out.insert(normalize_send_sugar_canon(k), normalize_send_sugar_canon(v));
                }
                Proc::CastMap(Arc::new(Map::MapLit(out)))
            },
            other => Proc::CastMap(Arc::new(other.clone())),
        },

        // leaves + opaque (PZero, PVar, Err, Map/PathmapEmpty, leaf numeric/str casts,
        // zipper/pathmap casts, λ-abstractions): identity.
        _ => p.clone(),
    }
}

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
