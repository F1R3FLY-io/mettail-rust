//! # #154 — a binder inside a COLLECTION LITERAL must not leak its `unique_id`
//!
//! `semantic_hash` is the alpha-canonical fingerprint of a term. It backs
//! `semantic_fingerprint` → `exact_key` / `content_key`, which is the realize
//! ambiguity-dedup surface, so **its value is consensus-visible**: two nodes that
//! disagree about a fingerprint disagree about which parse alternatives are the
//! same reading.
//!
//! ## The mechanism, confirmed at source before it was fixed
//!
//! `macros/src/gen/term_ops/semantic_hash.rs` had TWO arms for containers of
//! sub-terms, and only one of them was correct:
//!
//! * `VariantKind::Collection` — a category-DIRECT collection field such as
//!   `PPar . ps:HashBag(Proc)` — routed through `semantic_hash_collection`, which
//!   hashes each element with the ELEMENT's `semantic_hash`. That was FIX-A
//!   (2026-06-29), landed for exactly this defect.
//! * `VariantKind::CollectionLiteral` — a collection CATEGORY declared as a
//!   native-type alias (`![HashMapLit<Proc, Proc>] as Map`, `PathMapLit` as
//!   `Pathmap`, `Vec<Proc>` as `List`, …) — shared the `VariantKind::Literal`
//!   arm, whose body is
//!
//!   ```text
//!   state.write_u8(#variant_idx);
//!   std::hash::Hash::hash(v, state);      ← STRUCTURAL Hash
//!   ```
//!
//! Structural `Hash` on a binder-bearing `Proc` writes the binder's moniker
//! `unique_id` — a process-global counter freshened by every `unbind` and never
//! reset. So a binder reached through a MAP LITERAL was fingerprinted with a
//! run-varying number, while the same binder reached through a `PPar` bag was not.
//!
//! ★ #154 and #162 are therefore the SAME root cause seen from two angles: the
//! `CollectionLiteral` discriminant exists so every consumer declares its intent,
//! and `semantic_hash` was one of the consumers that had not.
//!
//! ## What these tests are
//!
//! Unlike `generated_traversal_boundary_laws.rs` (conservation laws, which pass
//! before and after by design), these are **fix gates**: each one is RED against
//! the structural-`Hash` arm and GREEN against the `semantic_hash_into` arm.
#![cfg(feature = "rholang")]

use mettail_languages::rholang::Proc;
use mettail_runtime::FramedSemanticKeyHasher;

fn parse(input: &str) -> Proc {
    Proc::parse(input).unwrap_or_else(|e| panic!("parse failed for `{input}`: {e}"))
}

/// The exact framed write-stream `semantic_hash` records — the same stream that
/// backs `exact_key` ambiguity dedup.
fn semantic_key(term: &Proc) -> Vec<u8> {
    let mut hasher = FramedSemanticKeyHasher::default();
    term.semantic_hash(&mut hasher);
    hasher.into_key()
}

/// The structural `Hash` stream, for CONTRAST. `semantic_hash` and `Hash` are
/// *supposed* to differ on binder-bearing terms: the first is alpha-canonical,
/// the second is structural and includes `unique_id`.
fn structural_key(term: &Proc) -> Vec<u8> {
    use std::hash::Hash;
    let mut hasher = FramedSemanticKeyHasher::default();
    term.hash(&mut hasher);
    hasher.into_key()
}

/// Sources whose binder sits INSIDE a collection literal, one per literal shape
/// the grammar admits. Each is paired with an ALPHA-EQUIVALENT twin that differs
/// only in the bound name — hence only in `unique_id`.
///
/// ⚠ The pairs are the instrument. "Hash the same source twice" is a weaker test:
/// a cache could return an identical `unique_id` for a repeated identifier and the
/// leak would still be there. Renaming the binder forces a genuinely different
/// `unique_id` for a term that must fingerprint identically.
///
/// ★★ **Why the binder is `new` and NOT `for`, and this is a MEASUREMENT.** The
/// first draft of this file used `for(@a <- @"c"){ Nil }`, and every row was red —
/// including the `PPar` CONTROL, which was supposed to be FIX-A's already-working
/// case. Probing the shapes separately (2026-07-30) found the reason:
///
/// ```text
///   new a in { Nil }                SAME  (alpha-canonical)
///   new a in { a!(1) }              SAME  (alpha-canonical)
///   for(@a <- @"c"){ Nil }          DIFFERS  ← leaks, with NO collection anywhere
///   for(@a <- @"c"){ @a!(1) }       DIFFERS  ← leaks
///   new a in { Nil } | 1            SAME
///   for(@a <- @"c"){ Nil } | 1      DIFFERS  ← the `PPar` control, red for the SAME reason
/// ```
///
/// So `for` carries an `unique_id` leak of its OWN, reachable with no collection in
/// the term at all. That is a DIFFERENT defect in a different arm (the
/// `PForUser` / `ForRow` / `InputBind` family, not the collection-literal arm), and
/// a #154 gate built on `for` would have conflated the two: it would have stayed
/// red after this fix and been blamed on the fix. `new` isolates the arm under
/// test. The `for` leak is reported separately.
const ALPHA_TWINS_WITH_A_BINDER_INSIDE_A_LITERAL: &[(&str, &str, &str)] = &[
    ("map VALUE position", "{1: new a in { a!(1) }}", "{1: new b in { b!(1) }}"),
    ("map KEY position", "{new a in { a!(1) }: 1}", "{new b in { b!(1) }: 1}"),
    ("list ELEMENT position", "[new a in { a!(1) }]", "[new b in { b!(1) }]"),
    ("set ELEMENT position", "Set(new a in { a!(1) })", "Set(new b in { b!(1) })"),
    (
        "pathmap VALUE position",
        "{|1 : new a in { a!(1) }|}",
        "{|1 : new b in { b!(1) }|}",
    ),
    (
        "nested — a list inside a map value",
        "{1: [new a in { a!(1) }]}",
        "{1: [new b in { b!(1) }]}",
    ),
];

/// ★★ **THE #154 GATE.**
///
/// A binder inside a collection literal must be fingerprinted alpha-canonically,
/// exactly as a binder inside a `PPar` bag already was. Two alpha-equivalent
/// terms must produce the IDENTICAL framed `semantic_hash` stream.
///
/// **What makes it red:** the arm calling structural `std::hash::Hash` instead of
/// the element's `semantic_hash`. Reverting `semantic_hash`'s `CollectionLiteral`
/// arm back onto the `Literal` arm turns every row below red.
#[test]
fn a_binder_inside_a_collection_literal_is_fingerprinted_alpha_canonically() {
    let mut leaked: Vec<String> = Vec::new();
    for (position, left_source, right_source) in ALPHA_TWINS_WITH_A_BINDER_INSIDE_A_LITERAL {
        mettail_runtime::clear_var_cache();
        let left = parse(left_source);
        mettail_runtime::clear_var_cache();
        let right = parse(right_source);

        if semantic_key(&left) != semantic_key(&right) {
            leaked.push(format!(
                "  {position}: `{left_source}` vs `{right_source}`\n    left  = {:02x?}\n    \
                 right = {:02x?}",
                &semantic_key(&left)[..semantic_key(&left).len().min(40)],
                &semantic_key(&right)[..semantic_key(&right).len().min(40)],
            ));
        }
    }
    assert!(
        leaked.is_empty(),
        "#154: the semantic fingerprint of a binder inside a COLLECTION LITERAL varies with \
         the bound NAME, which means it varies with the binder's run-generated moniker \
         `unique_id`. `semantic_hash` is consensus-visible — it backs `exact_key` / \
         `content_key` realize dedup — so two nodes that generated different `unique_id`s \
         would disagree about which readings are the same.\n\
         The arm is calling structural `std::hash::Hash` on the container instead of the \
         element's `semantic_hash` (see this file's header, and \
         `semantic_hash.rs`'s `VariantKind::CollectionLiteral`).\n\
         Positions that leaked:\n{}",
        leaked.join("\n")
    );
}

/// ⚠ **THE NON-VACUITY CONTROL.** The test above would pass trivially if the
/// twins' fingerprints agreed for a reason that has nothing to do with the fix —
/// most obviously if `semantic_hash` collapsed the binder to nothing at all, or if
/// the two sources parsed to the same term because the renaming was ignored.
///
/// So: the STRUCTURAL keys of the same twins must DIFFER. That is the leak, still
/// present in `Hash` where it belongs, and it proves the twins really do carry
/// different `unique_id`s — which is what makes their `semantic_hash` agreement
/// meaningful.
#[test]
fn the_twins_really_do_carry_different_unique_ids() {
    let mut identical: Vec<&str> = Vec::new();
    for (position, left_source, right_source) in ALPHA_TWINS_WITH_A_BINDER_INSIDE_A_LITERAL {
        mettail_runtime::clear_var_cache();
        let left = parse(left_source);
        mettail_runtime::clear_var_cache();
        let right = parse(right_source);
        if structural_key(&left) == structural_key(&right) {
            identical.push(position);
        }
    }
    assert!(
        identical.is_empty(),
        "the alpha-twins have IDENTICAL structural `Hash` streams at these positions: {identical:?}.\n\
         Then they do not carry different moniker `unique_id`s, and \
         `a_binder_inside_a_collection_literal_is_fingerprinted_alpha_canonically` is a \
         VACUOUS pass — it would stay green with the defect fully present. Either the \
         binder is not reaching the literal, or `Hash` stopped being structural."
    );
}

/// The sibling that proves the fix is about the LITERAL arm and not about binders
/// in general: a binder inside a `PPar` bag — a `VariantKind::Collection` FIELD,
/// fixed by FIX-A in 2026-06-29 — was already alpha-canonical. This row is the
/// CONTROL that says the defect was specific to the collection-LITERAL arm.
#[test]
fn a_binder_inside_a_par_bag_was_already_alpha_canonical() {
    mettail_runtime::clear_var_cache();
    let left = parse("new a in { a!(1) } | 1");
    mettail_runtime::clear_var_cache();
    let right = parse("new b in { b!(1) } | 1");
    assert_eq!(
        semantic_key(&left),
        semantic_key(&right),
        "a binder inside a `PPar(HashBag<Proc>)` must be alpha-canonical — this is FIX-A's \
         own property, and if it is red the regression is in `semantic_hash_collection`, \
         not in the collection-LITERAL arm"
    );
}

/// ★★ **The COMPOSITION law for the semantic stream — a DIGEST comparison, not a
/// length or count one.**
///
/// #162 moved the `Vec` arm of `semantic_hash_collection` from
///
/// ```text
///   state.write_usize(len);  for e in coll { Elem::semantic_hash(e, state); }
/// ```
///
/// (a whole-value re-entry per element, measured 4,096 B/level) to
/// `AbsorbUsize(len)` plus one `SemHash{Elem}` task per element. That is claimed
/// to emit the identical stream, and the claim needs an instrument that a
/// *value-only* change cannot slip past: the converted and unconverted forms write
/// the SAME NUMBER OF BYTES, so any length- or count-based check is blind to a
/// reordering or a substituted element. This compares the bytes.
///
/// ```math
/// \mathrm{key}\big(\mathtt{[e_0,\;\ldots,\;e_{n-1}]}\big)
///   \;=\; P \;\Vert\; \mathrm{len}(n) \;\Vert\; \mathrm{key}(e_0) \;\Vert\; \cdots \;\Vert\; \mathrm{key}(e_{n-1})
/// ```
///
/// **What breaks it:** pushing the length prefix on the wrong side of the elements
/// (it is written FIRST here and LAST on the `Ord` side — opposite ends, and the
/// first draft of the sibling `Hash` conversion had them interchanged), or walking
/// the elements forward instead of reversed so the LIFO stack emits them backwards.
#[test]
fn the_semantic_stream_of_a_list_is_its_elements_streams_in_index_order() {
    // Elements chosen to be pairwise DISTINCT and asymmetric, so a reversal is
    // visible. A palindromic payload would make the reversed walk indistinguishable
    // from the forward one.
    let payloads: Vec<Vec<&str>> =
        vec![vec![], vec!["1"], vec!["1", "2"], vec!["1", "2", "3"], vec!["[1]", "2", "Nil"]];

    let mut prefixes: Vec<Vec<u8>> = Vec::with_capacity(payloads.len());

    for sources in &payloads {
        let whole = semantic_key(&parse(&format!("[{}]", sources.join(", "))));
        // The concatenation of the elements' own semantic streams, in INDEX order.
        let mut elements: Vec<u8> = Vec::new();
        for source in sources {
            elements.extend_from_slice(&semantic_key(&parse(source)));
        }

        assert!(
            whole.len() >= elements.len() && whole.ends_with(&elements),
            "the semantic stream of `[{}]` does not end with its elements' streams \
             concatenated in INDEX order.\n\
             `semantic_hash` is consensus-visible (`semantic_fingerprint` → \
             `exact_key`/`content_key` realize dedup), and this change is value-only in a \
             fixed-width encoding — the byte COUNT is unchanged either way, so only a digest \
             comparison can see it.\n  \
             whole    ({:>4} B): {:02x?}\n  elements ({:>4} B): {:02x?}",
            sources.join(", "),
            whole.len(),
            &whole[..whole.len().min(56)],
            elements.len(),
            &elements[..elements.len().min(56)]
        );

        prefixes.push(whole[..whole.len() - elements.len()].to_vec());
    }

    // The prefix is `variant discriminant ++ length`, so it varies with the LENGTH
    // but must be identical for two payloads of equal length. Without this the
    // `ends_with` above proves nothing — any stream splits into (rest, suffix).
    let two_of_length_two: Vec<Vec<u8>> = ["[1, 2]", "[3, 4]"]
        .iter()
        .map(|source| {
            let whole = semantic_key(&parse(source));
            let elements: Vec<u8> = source
                .trim_start_matches('[')
                .trim_end_matches(']')
                .split(", ")
                .flat_map(|e| semantic_key(&parse(e)))
                .collect();
            whole[..whole.len() - elements.len()].to_vec()
        })
        .collect();
    assert_eq!(
        two_of_length_two[0], two_of_length_two[1],
        "the prefix written before the element streams differs between two lists of the \
         SAME length, so it is carrying payload information and the composition law above \
         is not pinning anything. It must be exactly (variant discriminant, length)."
    );

    // And the prefix must GROW with length exactly once — a sanity check that the
    // length is in the prefix at all rather than silently omitted.
    assert!(
        prefixes.iter().any(|p| p != &prefixes[0]),
        "every payload length produced the SAME prefix, so the LENGTH PREFIX is not being \
         written. Two lists of different lengths whose elements' streams concatenate to \
         the same bytes would then collide."
    );
}

/// ★★ **The COLLIDING-PAIR CENSUS, made executable.**
///
/// `semantic_hash.rs` carries a long #151 block asserting that every one of the
/// eleven `variant_idx == 1` literal arms writes an indistinguishable discriminating
/// prefix, and that TWO pairs collided COMPLETELY: `Map`/`Pathmap` (because
/// `PathMapLit::hash` delegated verbatim to `HashMapLit::hash`) and `Str`/`Bytes`
/// (because both payloads were `String`). On the strength of that, a category tag
/// was written, PROVEN NECESSARY, and then disabled pending a semantics ruling.
///
/// Both pairs have since been dissolved by unrelated changes — `713e0364` gave
/// `Bytes` a real `Vec<u8>` carrier, and the homogeneous pathmap representation
/// gave the pathmap arm a container-mode discriminator. This test is that state as an ASSERTION instead of a comment,
/// because "which fingerprints collide" is precisely the kind of claim that goes
/// stale silently: nothing in the tree was watching either dissolution, and the
/// block still reads as though both pairs were live.
///
/// ⚠ The residue is recorded as a live expectation too, not as prose: `{||}` and
/// `{}` are both EMPTY, both write `variant_idx == 1` and a zero length, and
/// therefore still collide. If a future change separates them this test goes RED —
/// which is the correct outcome, and the row should then move to the
/// distinguished set with the change that did it named.
#[test]
fn the_fingerprint_collision_census_is_exactly_the_declared_one() {
    // Pairs that must be DISTINGUISHED, each with the change that distinguished them.
    let distinguished: &[(&str, &str, &str)] = &[
        (
            "Str vs Bytes — `713e0364`'s `![Vec<u8>] as Bytes` carrier: `Hash for String` \
             writes `(bytes, 0xff)` through `write_str`, `Hash for Vec<u8>` writes \
             `(write_usize(len), bytes)` through `[T]`",
            "\"a\"",
            "b\"61\"",
        ),
        (
            "Map vs Pathmap, NON-EMPTY — the pathmap writes its homogeneous container-mode \
             discriminator and the map does not",
            "{1: 2}",
            "{|1 : 2|}",
        ),
    ];
    for (why, left_source, right_source) in distinguished {
        let left = semantic_key(&parse(left_source));
        let right = semantic_key(&parse(right_source));
        assert_ne!(
            left, right,
            "`{left_source}` and `{right_source}` have IDENTICAL semantic fingerprints, but \
             they are on record as distinguished — {why}.\n\
             A collision here silently MERGES two readings at realize-time observational \
             dedup, which is the defect the #151 category tag was written for."
        );
    }

    // ★★ THE DECLARED RESIDUE IS REFUTED AT THE SURFACE, and this row records the
    // measurement rather than the claim it replaces.
    //
    // The #151 block held the category tag open for one uncovered pair: "what
    // remains uncovered is `{||}` vs `{}` (no value bytes to tag)". Measured
    // 2026-07-30 with `Proc::parse`:
    //
    //   {}        => PPar(HashBag { counts: {}, total_count: 0 })
    //   {||}      => CastPathmap(PathmapLit(PathMapLit(HashMapLit({}))))
    //   []        => CastList(ListLit([]))
    //   Set()     => CastSet(SetLit(HashSetLit({})))
    //
    // `{}` is not a map literal at all — it is the empty PAR, a `PPar` bag, a
    // different `Proc` variant with a different index and a four-lane commutative
    // digest. There is NO surface spelling in shipped rholang that yields
    // `CastMap(MapLit(∅))`, so the empty-map/empty-pathmap collision is
    // UNREACHABLE rather than merely latent.
    assert_ne!(
        semantic_key(&parse("{}")),
        semantic_key(&parse("{||}")),
        "`{{}}` and `{{||}}` now share a semantic fingerprint. Measured 2026-07-30 they did \
         not, because `{{}}` parses to `PPar(HashBag{{}})` — the empty PAR — and not to an \
         empty map literal. If they collide now, the SURFACE changed: some spelling has \
         started producing `CastMap(MapLit(∅))`, and the #151 category tag's one \
         remaining beneficiary has become reachable."
    );

    // The shape pin that makes the assertion above mean what it says. Without it,
    // `assert_ne!` would keep passing for any reason at all — including `{}` ceasing
    // to parse into anything comparable.
    assert!(
        matches!(parse("{}"), Proc::PPar(_)),
        "`{{}}` no longer parses to `Proc::PPar`. The reasoning above — that the empty-map \
         vs empty-pathmap collision is UNREACHABLE because no surface yields an empty map \
         literal — rests entirely on that fact, so it has to be re-derived."
    );
}

/// Determinism across repeated fingerprinting of the SAME term. Weaker than the
/// alpha-twin test, but it catches a different failure: a work-stack pool that
/// leaks state between `semantic_hash` calls.
#[test]
fn the_fingerprint_of_one_term_is_stable_across_repeated_calls() {
    for (position, source, _) in ALPHA_TWINS_WITH_A_BINDER_INSIDE_A_LITERAL {
        let term = parse(source);
        let first = semantic_key(&term);
        let second = semantic_key(&term);
        assert_eq!(
            first, second,
            "{position}: fingerprinting `{source}` twice gave different streams — the \
             `SEMANTIC_HASH_TASK_POOL` is leaking work between calls"
        );
        assert!(
            !first.is_empty(),
            "{position}: `{source}` fingerprinted to an EMPTY stream, so every assertion \
             about it is vacuous"
        );
    }
}
