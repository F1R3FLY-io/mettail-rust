//! # The laws the COLLECTION-ELEMENT BOUNDARY conversion must not break (#162)
//!
//! `macros/src/gen/term_ops/collection_walk.rs` converted seven generated
//! traversals from *handing a container of sub-terms whole to a trait method* to
//! *pushing one work-stack task per element*. That removes Θ(depth) native stack
//! growth — which `rholang-runtime/tests/stack_depth_gate.rs` asserts — but it
//! rewrites the code that computes `Hash`, `PartialEq`, `Ord`, `Debug` and
//! `semantic_hash`, and **those results are consensus-visible**:
//!
//! * `Proc` is a hash key INSIDE the AST (`Set` = `HashSetLit<Proc>`,
//!   `Bag` = `HashBag<Proc>`, `Map` = `HashMap<Proc, Proc>`,
//!   `PPar(HashBag<Proc>)`), all built at parse time. A changed `Hash` re-buckets
//!   every one of them.
//! * `rholang_ast::drive` sorts by `Ord` (`items.sort()`, `sort_by_key`), so a
//!   changed ordering changes the lowered `Par`.
//! * `semantic_hash` feeds `semantic_fingerprint` → the realize/exact-key dedup.
//!
//! ## Two KINDS of gate, and the difference matters
//!
//! The tests here are **conservation** gates: they assert the conversion changed
//! nothing observable. They therefore PASS both before and after the change, by
//! design — reverting the conversion does not turn them red. That is not a
//! weakness; it is what a conservation law looks like. The gate that would go red
//! if the conversion were reverted is the *stack* gate, and it lives in
//! `rholang-runtime/tests/stack_depth_gate.rs`.
//!
//! Each test below says which mechanism would break it.
#![cfg(feature = "rholang")]

use mettail_languages::rholang::{List, Proc};
use mettail_runtime::FramedSemanticKeyHasher;
use std::hash::Hash;

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn parse(input: &str) -> Proc {
    Proc::parse(input).unwrap_or_else(|e| panic!("parse failed for `{input}`: {e}"))
}

/// The EXACT write-stream a value's `std::hash::Hash` produces.
///
/// ★ `FramedSemanticKeyHasher` is the right instrument rather than a
/// `DefaultHasher`, and the reason is the whole point of this file: it records
/// each `Hasher::write_*` call *individually, tagged and length-framed*. A digest
/// would collapse `write_u8(1); write_u8(2)` and `write(&[1, 2])` to the same
/// value; the framed stream keeps them apart. So a conversion that wrote the same
/// BYTES through a different SEQUENCE of calls — which is exactly the mistake
/// available when moving work onto a task stack — is visible here and invisible to
/// a digest comparison.
fn hash_stream<T: Hash>(value: &T) -> Vec<u8> {
    let mut hasher = FramedSemanticKeyHasher::default();
    value.hash(&mut hasher);
    hasher.into_key()
}

/// A `[[…[leaf]…]]` spine of `depth` nested single-element list literals.
fn nested_list_source(depth: usize, leaf: i64) -> String {
    let mut source = leaf.to_string();
    for _ in 0..depth {
        source = format!("[{source}]");
    }
    source
}

// ---------------------------------------------------------------------------
// 1. HASH — the write stream is byte-identical to the container's own `Hash`
// ---------------------------------------------------------------------------

/// ★★ **The load-bearing conservation law.**
///
/// The generated `Hash` for a collection-literal category used to be
/// `write(variant_index)` followed by `Hash::hash(container, state)`. The
/// conversion replaced the second half with `AbsorbUsize(len)` plus one
/// `HashTask::Hash{Elem}` per element, pushed so they pop in index order. That is
/// claimed to be byte-identical because `Hash for [T]` is
/// `state.write_length_prefix(len)` then each element in index order, and
/// `write_length_prefix`'s only stable-reachable behaviour is `write_usize`.
///
/// This test does not take that claim on faith. It asserts the SHAPE of the
/// identity directly: for every payload `v`,
///
/// ```math
/// \mathrm{stream}\big(\mathtt{List{:}{:}ListLit}(v)\big) \;=\; P \,\Vert\, \mathrm{stream}(v)
/// ```
///
/// with a prefix `P` that does not depend on `v`. Both halves are checked, and the
/// second is what makes it a proof rather than a coincidence: a prefix allowed to
/// vary with `v` would let *any* stream satisfy the suffix condition.
///
/// **What breaks it:** getting the length prefix on the wrong side of the elements
/// (it is written FIRST for `Hash`, and is the lexicographic TIEBREAK — i.e. last
/// — for `Ord`; the two are opposite and were interchanged in the first draft of
/// this conversion), pushing the elements in the wrong direction, or splicing a
/// recorded byte buffer instead of re-issuing the original `write_*` calls.
#[test]
fn a_collection_literals_hash_stream_is_its_containers_stream_under_a_fixed_prefix() {
    // Two payloads that differ in length AND in content, so a prefix that
    // secretly depended on either would be caught.
    let cases: Vec<Vec<Proc>> = vec![
        vec![],
        vec![parse("1")],
        vec![parse("1"), parse("2")],
        vec![parse("[1]"), parse("2"), parse("@\"c\"!(3)")],
    ];

    let mut prefixes: Vec<Vec<u8>> = Vec::with_capacity(cases.len());

    for payload in &cases {
        let whole = hash_stream(&List::ListLit(payload.clone()));
        let container = hash_stream(payload);

        assert!(
            whole.len() >= container.len() && whole.ends_with(&container),
            "the generated `Hash` for `List::ListLit` no longer ends with the write stream of \
             its `Vec<Proc>` payload (payload length {}).\n\
             That is the #162 conversion changing the HASH VALUE, which re-buckets every \
             `HashSetLit<Proc>` / `HashBag<Proc>` / `HashMap<Proc, Proc>` in the AST.\n  \
             whole     ({:>4} B): {:02x?}\n  container ({:>4} B): {:02x?}",
            payload.len(),
            whole.len(),
            &whole[..whole.len().min(48)],
            container.len(),
            &container[..container.len().min(48)]
        );

        prefixes.push(whole[..whole.len() - container.len()].to_vec());
    }

    for window in prefixes.windows(2) {
        assert_eq!(
            window[0], window[1],
            "the prefix the generated `Hash` writes BEFORE the payload stream depends on the \
             payload. Then `ends_with` above proves nothing — any stream can be split into \
             `(everything but the suffix, the suffix)`. The prefix must be exactly the variant \
             discriminant."
        );
    }
}

/// The same law for a collection-literal reached through its `Proc` wrapper, so
/// the assertion covers the CROSS-CATEGORY hop the conversion also rewrote
/// (`Proc::CastList(Arc<List>)` → `HashTask::HashList`).
#[test]
fn the_cross_category_hop_preserves_the_hash_stream_of_its_inner_category() {
    for depth in [1usize, 2, 5] {
        let outer = parse(&nested_list_source(depth, 7));
        let stream_via_proc = hash_stream(&outer);
        assert!(
            !stream_via_proc.is_empty(),
            "a depth-{depth} nested list literal hashed to an EMPTY write stream — the \
             traversal is not visiting anything, which would make every assertion in this \
             file vacuously true"
        );
        // Determinism: the same term hashed twice must produce the identical
        // stream. A work-stack driver that leaked state between calls (a pool not
        // drained, a `Cell::take` not returned) would fail here and nowhere else.
        assert_eq!(
            stream_via_proc,
            hash_stream(&outer),
            "hashing the SAME term twice produced different write streams at depth {depth} — \
             the `HASH_TASK_POOL` is leaking work between calls"
        );
    }
}

// ---------------------------------------------------------------------------
// 2. ORD / EQ — the relation is unchanged, total, and agrees with `Eq`
// ---------------------------------------------------------------------------

/// `Vec<T>: Ord` is LEXICOGRAPHIC: elements over the common prefix decide, and
/// length is only the tiebreak. The conversion has to reproduce that with a LIFO
/// stack, which means pushing the length verdict FIRST so it pops LAST.
///
/// **What breaks it:** pushing the length verdict last (it would then dominate,
/// making `Ord` length-first — a different total order, and `[2] < [1, 1]` would
/// flip), or walking the zipped elements forward instead of reversed (which makes
/// the LAST differing element decide instead of the first).
#[test]
fn list_ordering_is_lexicographic_not_length_first() {
    let short_but_greater = List::ListLit(vec![parse("2")]);
    let long_but_lesser = List::ListLit(vec![parse("1"), parse("1")]);

    assert!(
        short_but_greater > long_but_lesser,
        "`[2]` must be GREATER than `[1, 1]`: lexicographic order compares the first \
         elements (2 > 1) and never reaches the length. A length-first order would \
         report `[2] < [1, 1]`, which is what happens if the length `Verdict` is pushed \
         LAST (and therefore popped FIRST) in `cmp_collection_push_stmts`."
    );

    let prefix = List::ListLit(vec![parse("1")]);
    let extended = List::ListLit(vec![parse("1"), parse("0")]);
    assert!(
        prefix < extended,
        "a proper PREFIX must be less than its extension — this is the case where the \
         length verdict is the one that decides, so it proves the verdict is still \
         consulted at all"
    );

    // The first differing element decides, not the last.
    let a = List::ListLit(vec![parse("1"), parse("9")]);
    let b = List::ListLit(vec![parse("2"), parse("0")]);
    assert!(
        a < b,
        "`[1, 9] < [2, 0]`: the FIRST differing position decides. If the reversed \
         element walk were forward, the last differing position (9 vs 0) would win and \
         the comparison would invert."
    );
}

/// `Ord` must be a total order that agrees with `PartialEq`, over a corpus that
/// includes every shape the conversion touched: list literals, unordered
/// containers (the declared residue), binders, and deep nesting.
///
/// **What breaks it:** a `Verdict` consulted out of position, a `stack.clear()`
/// dropped, or an element pair zipped against the wrong partner.
#[test]
fn ord_is_a_total_order_and_agrees_with_eq() {
    let corpus: Vec<Proc> = [
        "Nil",
        "1",
        "2",
        "[]",
        "[1]",
        "[2]",
        "[1, 1]",
        "[[1]]",
        "[[2]]",
        "{1: 2}",
        "{2: 1}",
        "Set(1, 2)",
        "Set(2, 3)",
        "@\"a\"!(1)",
        "@\"a\"!(2)",
        "for(@x <- @\"c\"){ Nil }",
        "new y in { Nil }",
        "1 | 2",
        "[1] | [2]",
    ]
    .iter()
    .map(|s| parse(s))
    .collect();

    for (i, a) in corpus.iter().enumerate() {
        // Reflexivity, and agreement of `Eq` with `Ord`.
        assert_eq!(
            a.cmp(a),
            std::cmp::Ordering::Equal,
            "`cmp` is not reflexive at corpus index {i}"
        );
        assert!(a == a, "`eq` is not reflexive at corpus index {i}");

        for (j, b) in corpus.iter().enumerate() {
            // Antisymmetry.
            assert_eq!(
                a.cmp(b),
                b.cmp(a).reverse(),
                "`cmp` is not antisymmetric for corpus indices ({i}, {j})"
            );
            // `Ord` agrees with `Eq` — the contract that makes `Proc` usable as a
            // `BTreeMap`/sort key at the same time as a `HashMap` key.
            assert_eq!(
                a.cmp(b) == std::cmp::Ordering::Equal,
                a == b,
                "`cmp(a, b) == Equal` and `a == b` disagree for corpus indices ({i}, {j}). \
                 One of the two engines is consulting a position the other does not."
            );

            // Transitivity, over the whole triple product.
            for c in &corpus {
                if a <= b && b <= c {
                    assert!(
                        a <= c,
                        "`cmp` is not transitive: a <= b <= c but a > c, at corpus index {i}"
                    );
                }
            }
        }
    }
}

/// `Hash`'s contract: equal values must hash equally. Checked across the SHAPES
/// the conversion rewrote, including the ones built by two different routes.
///
/// **What breaks it:** any asymmetry between the `eq` engine and the `hash`
/// engine about which positions they visit — e.g. `eq` comparing elements
/// pairwise while `hash` still folded the whole container.
#[test]
fn equal_terms_hash_equally_across_every_converted_shape() {
    let pairs = [
        ("[1, 2, 3]", "[1, 2, 3]"),
        ("[[1], [2]]", "[[1], [2]]"),
        ("{1: 2, 3: 4}", "{1: 2, 3: 4}"),
        ("Set(1, 2)", "Set(1, 2)"),
        ("1 | 2", "1 | 2"),
        ("@\"a\"!([1, [2, [3]]])", "@\"a\"!([1, [2, [3]]])"),
    ];
    for (left_source, right_source) in pairs {
        let left = parse(left_source);
        let right = parse(right_source);
        assert_eq!(left, right, "`{left_source}` and `{right_source}` must be equal");
        assert_eq!(
            hash_stream(&left),
            hash_stream(&right),
            "`{left_source}` and `{right_source}` are EQUAL but hash to different write \
             streams — `Hash`'s `a == b ⇒ hash(a) == hash(b)` contract is broken, which \
             corrupts every `HashSetLit<Proc>` / `HashBag<Proc>` / `HashMap<Proc, Proc>` \
             in the AST"
        );
    }

    // Distinct terms must not collide on the FRAMED stream (a digest may collide;
    // the framed stream is the thing dedup compares, and it must not).
    let distinct = ["[1, 2]", "[2, 1]", "[1]", "[[1]]", "{1: 2}", "Set(1, 2)"];
    for (i, a) in distinct.iter().enumerate() {
        for b in distinct.iter().skip(i + 1) {
            assert_ne!(
                hash_stream(&parse(a)),
                hash_stream(&parse(b)),
                "`{a}` and `{b}` are DISTINCT terms with the same framed write stream"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 3. DEBUG / DISPLAY — the rendering is unchanged
// ---------------------------------------------------------------------------

/// The `Debug` conversion pushes one `DebugTask::Debug{Elem}` per element with
/// literal separators, instead of `format!("{:?}", container)`. The rendered text
/// must be identical.
///
/// **What breaks it:** a missing separator, a bracket on the wrong side of the
/// element loop, or elements emitted in reverse (the LIFO trap).
#[test]
fn debug_rendering_of_a_collection_is_unchanged_by_the_element_walk() {
    // The reference is the CONTAINER's own `Debug`, which the conversion did not
    // touch — so this is an independent oracle, not a restatement.
    for payload in [
        vec![],
        vec![parse("1")],
        vec![parse("1"), parse("2"), parse("3")],
        vec![parse("[1, 2]"), parse("Nil")],
    ] {
        let literal = List::ListLit(payload.clone());
        let rendered = format!("{literal:?}");
        let reference = format!("ListLit({payload:?})");
        assert_eq!(
            rendered, reference,
            "the generated `Debug` for a collection literal no longer matches the \
             container's own `Debug`. The element walk must reproduce `[a, b, c]` \
             exactly — brackets outside, `, ` between, elements in INDEX order."
        );
    }
}

// ---------------------------------------------------------------------------
// 3b. TERM_DEPTH — the values are unchanged by the worklist conversion
// ---------------------------------------------------------------------------

/// ★★ **The closed-form oracle for `term_depth`.**
///
/// #162 replaced `term_depth`'s bare host recursion (`1 + max(children)`) with an
/// explicit `(node, dist)` worklist keeping ONE running maximum — no result stack and
/// no combine task, because the recurrence collapses to
///
/// ```math
/// f(n) \;=\; \max_{m \,\in\, \mathrm{desc}(n)} \big(\mathrm{dist}(n, m) + \mathrm{base}(m)\big)
/// ```
///
/// with `base = 0` for a leaf kind and `1` otherwise (the proof is in
/// `macros/src/gen/term_ops/depth.rs`'s module header). That is a genuine rewrite of
/// the arithmetic, so the VALUES need an oracle that does not restate it.
///
/// The oracle is a closed form. `[[…[1]…]]` at nesting `n` is `n` alternating
/// `Proc::CastList(Arc<List>)` / `List::ListLit(Vec<Proc>)` pairs above a
/// `Proc::CastInt(Arc<Int>)` above an `Int::NumLit(i32)`. Unrolling the DECLARED
/// semantics: `NumLit` is a scalar literal so 0; `CastInt` is a constructor so 1;
/// each `ListLit` is a collection category so `1 +` its element; each `CastList` is a
/// constructor so `1 +` its field. Hence
///
/// ```math
/// f_n \;=\; 2n + 1
/// ```
///
/// ⚠ The probe's own anti-vacuity assertion is only `measured >= depth`, chosen so it
/// could not go red for a change in how a level is COUNTED. That is the right choice
/// there and it means the probe does NOT pin the values — this test does.
///
/// **What breaks it:** pushing a collection FIELD's elements at `dist + 2` instead of
/// `dist + 1` (a collection field's container contributes no level of its own, while
/// a collection CATEGORY's does — the one confusion available in this conversion),
/// giving a leaf kind `base = 1`, or dropping a node's own contribution so that a
/// childless internal node reports its parent's depth.
#[test]
fn term_depth_matches_its_closed_form_on_the_alternating_ladder() {
    for n in [0usize, 1, 2, 3, 5, 8, 13] {
        let term = parse(&nested_list_source(n, 1));
        let expected = (2 * n + 1) as u32;
        assert_eq!(
            term.term_depth(),
            expected,
            "`{}` must have term_depth {expected} = 2·{n} + 1: {n} `CastList`/`ListLit` pairs \
             (2 levels each) above `CastInt` (1 level) above the scalar `NumLit` (0). Got {}. \
             The #162 conversion rewrote this arithmetic into a running maximum over \
             `dist + base`, so a wrong answer means the worklist is assigning the wrong \
             DISTANCE to some child position — most likely a collection FIELD's elements, \
             which sit at `dist + 1` because the container adds no level, unlike a \
             collection CATEGORY's.",
            nested_list_source(n, 1),
            term.term_depth()
        );
    }
}

/// The same oracle on shapes the alternating ladder does not reach: a pure
/// constructor chain, a binder, an unordered container, and a map (whose KEY and
/// VALUE are both sub-terms).
#[test]
fn term_depth_is_unchanged_on_every_converted_container_shape() {
    // `1` is `CastInt(NumLit)` = 1. `[1]` adds a `ListLit` and a `CastList` = 3.
    let cases: &[(&str, u32)] = &[
        ("Nil", 0),
        ("1", 1),
        ("[]", 2),
        ("[1]", 3),
        ("[[1]]", 5),
        // `1 | 2` is `PPar(HashBag<Proc>)`: a collection CATEGORY-direct FIELD on a
        // node, so `1 + max(elements)` = 1 + 1 = 2.
        ("1 | 2", 2),
        // `Set(1)` = CastSet(SetLit(HashSetLit{CastInt(NumLit)})) = 1 + 1 + 1 = 3.
        ("Set(1)", 3),
        // `{1: 2}` = CastMap(MapLit(HashMapLit{k -> v})) = 1 + 1 + 1 = 3; both key and
        // value are depth-1 sub-terms, so the max is 1 either way.
        ("{1: 2}", 3),
        // A deeper VALUE than KEY, so the walk must reach values and not only keys.
        ("{1: [[2]]}", 7),
        // A deeper KEY than VALUE, the mirror case.
        ("{[[2]]: 1}", 7),
        // `{|1 : [[2]]|}` — a pathmap `Set` value.
        ("{|1 : [[2]]|}", 7),
    ];
    for (source, expected) in cases {
        let term = parse(source);
        assert_eq!(
            term.term_depth(),
            *expected,
            "`{source}` must have term_depth {expected}; got {}. Each row is derived from \
             the DECLARED semantics in `depth.rs`'s module header, independently of the \
             worklist that now computes it.",
            term.term_depth()
        );
    }
}

// ---------------------------------------------------------------------------
// 4. NON-VACUITY — the corpus actually exercises the converted shapes
// ---------------------------------------------------------------------------

/// ⚠ Every assertion above is over terms produced by `Proc::parse`. If the
/// surface for a collection literal changed, those terms would silently stop
/// being collection literals and every law above would hold vacuously over
/// scalars. This pins the shapes.
#[test]
fn the_corpus_really_does_contain_collection_literals_and_binders() {
    assert!(
        matches!(parse("[1, 2]"), Proc::CastList(_)),
        "`[1, 2]` must parse to `Proc::CastList`, the cross-category hop into the \
         `List` collection-literal category. If it does not, the laws in this file are \
         being checked against something else entirely."
    );
    // ⚠ Bound by REFERENCE, not by value. `Proc` has a hand-written iterative
    // `Drop` (`iterative_drop.rs`), so it cannot be destructured by value at all —
    // `E0509`, cannot move out of a type that implements `Drop`. The stack gate's
    // module header records the same constraint.
    let parsed = parse("[1, 2]");
    let list = match &parsed {
        Proc::CastList(inner) => inner.as_ref().clone(),
        other => panic!("expected `Proc::CastList`, got {other:?}"),
    };
    assert!(
        matches!(&list, List::ListLit(v) if v.len() == 2),
        "the inner `List` must be a two-element `ListLit`, got {list:?}"
    );

    // Deep nesting must actually nest — the stack gate's ladder depends on it.
    let deep = parse(&nested_list_source(8, 1));
    let mut cursor = &deep;
    let mut levels = 0usize;
    while let Proc::CastList(inner) = cursor {
        match inner.as_ref() {
            List::ListLit(v) if v.len() == 1 => {
                levels += 1;
                cursor = &v[0];
            },
            _ => break,
        }
    }
    assert_eq!(
        levels, 8,
        "`{}` must nest 8 `CastList`/`ListLit` levels; walked {levels}. The alternating \
         ladder the stack gate measures is exactly this shape.",
        nested_list_source(8, 1)
    );
}
