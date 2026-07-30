//! #151 + #74 — the kv-collection repair, pinned by direct payload
//! introspection.
//!
//! # What these rows are evidence of
//!
//! Two defects met in the collection close, and a third in the codegen that
//! decides which slots ARE collections.
//!
//! **#151 — the silent cross-category drop.** The walker's `CollectionMarker`
//! close ran an element-category gate on sequence flats and skipped it on kv
//! flats, on the recorded premise that "no shipped grammar parses a kv-map with
//! cross-cat keys/values". Rholang's `{| @a : @b |}` falsifies that premise:
//! `@a` and `@b` are `Name`s where the slot's declared element category is
//! `Proc`, so the finalize action's downcast mapped both to nothing and emitted
//! an EMPTY pathmap for a two-token literal. Upstream Rholang refuses the input.
//! Accepting-and-mangling is not a superset of refusing — it is unsound.
//!
//! **#74 — the bare element's value was the key.** `{| k |}` is a legal pathmap
//! entry: the key is present and bound to NOTHING. It was materialised by
//! duplicating the key into the value slot, so `{|1|}` and `{|1:1|}` became the
//! same term and `Display` printed `{|1:1|}` for an input written `{|1|}`.
//!
//! **ROOT 3 — the misclassified slots.** 40 of rholang's 42 generated kv slots
//! were `Vec` argument lists of auto-injected higher-order-literal variants that
//! inherited `":"` from their home category. Pinned separately in the
//! macro-crate unit tests (`kv_sep_for_*` in
//! `macros/src/gen/runtime/wpda_codegen/collection.rs`) and by
//! [`rholang_has_exactly_two_kv_slots`] below.
//!
//! # Assertion form (non-negotiable)
//!
//! Every row pins the **key and the value** through [`payload`] — `len()` plus
//! `iter()` over the container itself. Never a whole `Debug` string, and never
//! `Display`:
//!
//! ⚠ **`Display` SORTS pathmap entries** (generated `display.rs`, `entries.sort_by`
//! on the formatted key), so `Display` and the payload disagree on ORDER by
//! construction. A row that asserted on `Display` would silently pass while the
//! payload was wrong, and would fail spuriously when the pre-existing sort is
//! retired. The payload is the ground truth; `Display` is a rendering of it.
//!
//! ★ **No row expects a panic.** Absence is asserted through `Result::is_err()`,
//! a reading count, or `len == 0` — never by catching an abort.
//!
//! Run: `cargo test -p languages --test pathmap_kv_category_and_unset`
//! ⚠ NEVER `-p languages --features rholang`: rholang is already in `default`
//! via `all-languages`, and naming the feature explicitly disables the default
//! set.

use mettail_languages::rholang::*;
use mettail_runtime::PathValue;
use std::hash::Hasher;

// ═══════════════════════════════════════════════════════════════════════════
// Helpers
// ═══════════════════════════════════════════════════════════════════════════

fn sem_hash(p: &Proc) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    p.semantic_hash(&mut h);
    h.finish()
}

/// The value's shape, as a short tag.
///
/// `"·"` is `PathValue::Unset` — deliberately a character no `Proc` renders as,
/// so a row that expects `Unset` cannot be satisfied by any term. A `Set(v)`
/// reports `v`'s own `Display`.
fn v_tag(v: &PathValue<Proc>) -> String {
    match v {
        PathValue::Unset => "·".to_string(),
        PathValue::Set(inner) => inner.to_string(),
    }
}

/// Direct payload introspection: `Some((len, entries))` for a `Pathmap` or `Map`
/// literal reading, `None` for anything else.
///
/// `entries` preserves the container's own iteration order (insertion order for
/// `HashMapLit`/`PathMapLit`), which is what the "never sorted" rows check.
fn payload(p: &Proc) -> Option<(usize, Vec<(String, String)>)> {
    match p {
        Proc::CastPathmap(inner) => match inner.as_ref() {
            Pathmap::PathmapLit(lit) => Some((
                lit.len(),
                lit.iter().map(|(k, v)| (k.to_string(), v_tag(v))).collect(),
            )),
            _ => None,
        },
        Proc::CastMap(inner) => match inner.as_ref() {
            Map::MapLit(lit) => Some((
                lit.len(),
                lit.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect(),
            )),
            _ => None,
        },
        _ => None,
    }
}

/// All readings of `src`, or the empty vector when the parse refused.
fn readings(src: &str) -> Vec<Proc> {
    mettail_runtime::clear_var_cache();
    Proc::parse_via_wpda_all(src).unwrap_or_default()
}

/// The collection payloads of every reading of `src` that HAS one.
fn payloads(src: &str) -> Vec<(usize, Vec<(String, String)>)> {
    readings(src).iter().filter_map(payload).collect()
}

/// The single collection payload of `src`, asserting there is exactly one
/// reading with a payload.
fn sole_payload(src: &str) -> (usize, Vec<(String, String)>) {
    let ps = payloads(src);
    assert_eq!(
        ps.len(),
        1,
        "{src:?} must yield exactly ONE reading with a collection payload, got {}: {ps:?}",
        ps.len(),
    );
    ps.into_iter().next().expect("checked len == 1 above")
}

/// The sole reading of `src` (any shape).
fn sole_reading(src: &str) -> Proc {
    let rs = readings(src);
    assert_eq!(rs.len(), 1, "{src:?} must yield exactly ONE reading, got {}", rs.len());
    rs.into_iter().next().expect("checked len == 1 above")
}

// ═══════════════════════════════════════════════════════════════════════════
// Row A ★ — the sharpest row: the empty-pathmap ghost is gone
// ═══════════════════════════════════════════════════════════════════════════

/// `{| a : b |}` is a well-formed pathmap over two `Proc` variables.
///
/// Before the fix it produced **two** readings: the correct one-entry pathmap
/// AND a ghost EMPTY pathmap, because a second lineage reached the close with
/// items the finalize action could not downcast and emitted a shorter container
/// instead of refusing. This row is the sharpest because BOTH the presence of
/// the right answer and the ABSENCE of the ghost are pinned by the same
/// assertion.
#[test]
fn row_a_well_formed_pathmap_has_exactly_one_reading_and_no_empty_ghost() {
    let (len, entries) = sole_payload("{| a : b |}");
    assert_eq!(len, 1, "one entry");
    assert_eq!(entries, vec![("a".to_string(), "b".to_string())]);
}

// ═══════════════════════════════════════════════════════════════════════════
// Rows B / C / F — the cross-category refusal, and its Map sibling
// ═══════════════════════════════════════════════════════════════════════════

/// Row B: `{| @a : @b |}` — `@a`/`@b` are `Name`s, the slot's element category
/// is `Proc`. Upstream refuses this input outright (`key_value_pair` is
/// `seq(field('key', $._proc), ':', field('value', $._proc))`); MeTTaIL used to
/// accept it AS THE EMPTY PATHMAP.
///
/// ★ Ruling A (2026-07-29): "Upstream rholang does not support k:v pairs for
/// pathmap but it does for maps, use the same semantics for pathmap k:v pairs."
/// The declared category was already correct — the gate was simply not run.
#[test]
fn row_b_cross_category_pathmap_yields_no_empty_ghost() {
    let ps = payloads("{| @a : @b |}");
    assert!(
        ps.iter().all(|(len, _)| *len != 0),
        "no reading of `{{| @a : @b |}}` may be an EMPTY pathmap — that is the \
         sub-multiset ghost this fix removes; got {ps:?}",
    );
    assert!(
        readings("{| @a : @b |}").is_empty(),
        "`{{| @a : @b |}}` is not in the language; it must produce NO reading",
    );
}

/// Row C: the `Map` sibling of row B. `{ @a : @b }` goes through the SAME
/// classifier, so it must refuse the same way — the point of collapsing the two
/// gates into one is that there is no `is_kv` difference left to be
/// inconsistent about.
#[test]
fn row_c_cross_category_map_yields_no_empty_ghost() {
    let ps = payloads("{ @a : @b }");
    assert!(
        ps.iter().all(|(len, _)| *len != 0),
        "no reading of `{{ @a : @b }}` may be an EMPTY map; got {ps:?}",
    );
}

/// Row F: the BARE cross-category element `{| @a |}`. The unset path and the
/// category path meet here: the entry is `(@a, Unset)`, and `@a` is still a
/// `Name` in a `Proc` slot.
#[test]
fn row_f_bare_cross_category_element_yields_no_empty_ghost() {
    let ps = payloads("{| @a |}");
    assert!(
        ps.iter().all(|(len, _)| *len != 0),
        "no reading of `{{| @a |}}` may be an EMPTY pathmap; got {ps:?}",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Rows D / E — #74: a bare element's value is UNSET, and unset is not `Nil`
// ═══════════════════════════════════════════════════════════════════════════

/// Row D: `{| 1 |}` — the key is present and bound to NOTHING.
///
/// The value must be `PathValue::Unset`. It used to be the KEY (`("1","1")`),
/// because the parser materialised a bare entry by re-folding the key's own SPPF
/// node into the value slot — destroying the "this was bare" fact before any
/// action could see it.
#[test]
fn row_d_bare_element_value_is_unset_not_the_key() {
    let (len, entries) = sole_payload("{| 1 |}");
    assert_eq!(len, 1);
    assert_eq!(
        entries,
        vec![("1".to_string(), "·".to_string())],
        "a bare `{{| 1 |}}` entry's value is UNSET — NOT the key, and NOT `Nil`",
    );
}

/// Row E: `{| 1 : Nil |}` is a DIFFERENT term from `{| 1 |}`, and both are
/// different from `{| 1 : 5 |}`.
///
/// ★ Ruling B: `unset ≠ Nil`. `Nil` is a value a program can write, so encoding
/// absence as `Nil` makes the two literals indistinguishable. The three-way
/// `semantic_hash` separation is what makes the ruling ENFORCEABLE rather than
/// conventional: `PathValue` writes a 1-byte tag before its payload, so the
/// three write streams differ in their bytes and no downstream fingerprint can
/// merge them.
#[test]
fn row_e_unset_nil_and_a_real_value_are_three_distinct_terms() {
    let (len, entries) = sole_payload("{| 1 : Nil |}");
    assert_eq!(len, 1);
    assert_eq!(entries, vec![("1".to_string(), "Nil".to_string())]);

    let bare = sole_reading("{| 1 |}");
    let nil = sole_reading("{| 1 : Nil |}");
    let five = sole_reading("{| 1 : 5 |}");

    let (h_bare, h_nil, h_five) = (sem_hash(&bare), sem_hash(&nil), sem_hash(&five));
    assert_ne!(h_bare, h_nil, "`{{|1|}}` and `{{|1:Nil|}}` must hash differently");
    assert_ne!(h_nil, h_five, "`{{|1:Nil|}}` and `{{|1:5|}}` must hash differently");
    assert_ne!(h_bare, h_five, "`{{|1|}}` and `{{|1:5|}}` must hash differently");

    // …and the terms themselves are distinct, not merely their digests.
    assert_ne!(bare, nil);
    assert_ne!(nil, five);
    assert_ne!(bare, five);
}

/// The Display fixpoint — the self-check for Ruling B.
///
/// `{| k |}` must round-trip through `Display`. Had the unset value been encoded
/// as `Nil`, `Display` would print `{|k:Nil|}`, which re-parses to a DIFFERENT
/// term. This row is why "unset ≠ Nil" is a soundness property here and not a
/// preference.
#[test]
fn bare_pathmap_entry_is_a_display_parse_fixpoint() {
    let bare = sole_reading("{| 1 |}");
    let printed = bare.to_string();
    assert!(
        !printed.contains("Nil"),
        "Display of `{{| 1 |}}` must not invent a value; got {printed:?}",
    );
    let reparsed = sole_reading(&printed);
    assert_eq!(
        payload(&reparsed),
        payload(&bare),
        "Display → parse must return the same payload; printed as {printed:?}",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Ruling D — `{| k : 1, k |}` is a written contradiction; refuse the literal
// ═══════════════════════════════════════════════════════════════════════════

/// One key, written twice: once WITH a value and once bare.
///
/// `IndexMap::insert` is last-write-wins, so the bare occurrence would silently
/// DELETE the value — the literal would mean something the author cannot have
/// intended, with no diagnostic. Ruling D (2026-07-29) refuses it.
///
/// ⚠ This is NOT the duplicate-key case Ruling C (#125) settles. Ruling C gives
/// pathmaps set semantics with no implicit multiplicity, so two occurrences that
/// AGREE (`{| k, k |}`, `{| k : 1, k : 1 |}`) dedup cleanly — pinned below. Only
/// a CONFLICT is refused.
#[test]
fn ruling_d_conflicting_duplicate_key_refuses_the_literal() {
    let ps = payloads("{| 1 : 2, 1 |}");
    assert!(
        ps.is_empty(),
        "`{{| 1 : 2, 1 |}}` binds one key both with and without a value — a \
         written contradiction. It must be refused, not silently resolved by \
         last-write-wins (which would DELETE the value). Got {ps:?}",
    );
}

/// Two occurrences that AGREE are not a contradiction (Ruling C).
#[test]
fn ruling_c_agreeing_duplicate_keys_dedup_without_refusing() {
    let (len, entries) = sole_payload("{| 1, 1 |}");
    assert_eq!(len, 1, "set semantics: no implicit multiplicity");
    assert_eq!(entries, vec![("1".to_string(), "·".to_string())]);

    let (len, entries) = sole_payload("{| 1 : 2, 1 : 2 |}");
    assert_eq!(len, 1);
    assert_eq!(entries, vec![("1".to_string(), "2".to_string())]);
}

// ═══════════════════════════════════════════════════════════════════════════
// Controls that must NOT discriminate
// ═══════════════════════════════════════════════════════════════════════════

/// Well-formed kv literals are untouched — same reading count, same payload.
#[test]
fn control_well_formed_kv_literals_are_unchanged() {
    for src in ["{|1:2|}", "{| 1 : 2 |}"] {
        let (len, entries) = sole_payload(src);
        assert_eq!(len, 1, "{src:?}");
        assert_eq!(entries, vec![("1".to_string(), "2".to_string())], "{src:?}");
    }
    let (len, _) = sole_payload("{| \"k\" : 1 |}");
    assert_eq!(len, 1);
}

/// ★ THE MINIMAL PAIR — Ruling A's accept row.
///
/// `{| *@a : *@b |}` differs from row B by exactly the two `*` dereferences that
/// turn the `Name`s into `Proc`s. It must still parse, with both entries intact.
/// This is what proves the gate discriminates on CATEGORY rather than refusing
/// anything that looks unusual.
#[test]
fn control_minimal_pair_dereferenced_names_still_parse() {
    let (len, entries) = sole_payload("{| *@a : *@b |}");
    assert_eq!(len, 1);
    assert_eq!(entries, vec![("*@a".to_string(), "*@b".to_string())]);
}

/// The `Map` and calculator siblings of the accept row.
#[test]
fn control_map_and_calculator_kv_literals_are_unchanged() {
    let (len, entries) = sole_payload("{ 1 : 2 }");
    assert_eq!(len, 1);
    assert_eq!(entries, vec![("1".to_string(), "2".to_string())]);
}

/// ★ THE ROW THAT PROVES THE FIX MATCHES THE EXISTING HONEST PATH.
///
/// `[@a, @b]` and `{ @a | @b }` are the SEQUENCE-side cross-category refusals —
/// the element-category gate working correctly, from before this fix. They must
/// still refuse. Had the repair changed how refusal is spelled rather than
/// extending WHERE it applies, these rows would move.
#[test]
fn control_sequence_side_cross_category_refusals_are_unchanged() {
    for src in ["[@a, @b]", "{ @a | @b }"] {
        mettail_runtime::clear_var_cache();
        assert!(
            Proc::parse_via_wpda_all(src).is_err(),
            "{src:?} must still be refused by the (pre-existing) element-category gate",
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Anti-vacuity — "always insert something" and "refuse everything" are both
// invalid fixes, and each of these rows kills one of them
// ═══════════════════════════════════════════════════════════════════════════

/// An EMPTY container is still empty. `PathValue::Unset` is a value in a slot
/// that EXISTS; nothing is ever inserted for an empty literal.
///
/// ⚠ `{ }` / `{}` are two-way ambiguous (empty par / empty map), so the empty-map
/// READING is selected by payload rather than by `sole_payload` — see
/// [`antivacuity_empty_brace_keeps_exactly_two_readings`] for the count.
#[test]
fn antivacuity_empty_containers_stay_empty() {
    for src in ["{||}", "{| |}"] {
        let (len, entries) = sole_payload(src);
        assert_eq!(len, 0, "{src:?} is the EMPTY pathmap");
        assert!(entries.is_empty(), "{src:?}");
    }
    for src in ["{ }", "{}"] {
        let ps = payloads(src);
        assert_eq!(ps.len(), 1, "{src:?} has exactly one reading with a payload: {ps:?}");
        assert_eq!(ps[0].0, 0, "{src:?}'s map reading is EMPTY");
    }
}

/// `Pathmap()` / `Map()` — the empty-container CONSTRUCTORS.
///
/// These are Dovetail fold rules, so a freshly parsed term is the unreduced
/// `Proc::PathmapEmpty` / `Proc::MapEmpty` node rather than a literal; the row
/// therefore pins the READING COUNT (the parse is unambiguous and did not
/// vanish) rather than a payload. They still matter as anti-vacuity: a repair
/// that broke empty-container construction would show up here.
#[test]
fn antivacuity_empty_container_constructors_still_parse_unambiguously() {
    for src in ["Pathmap()", "Map()"] {
        let rs = readings(src);
        assert_eq!(rs.len(), 1, "{src:?} must parse to exactly one reading; got {rs:?}");
        assert_eq!(rs[0].to_string(), src, "{src:?} must round-trip through Display");
    }
}

/// `{}` keeps EXACTLY TWO readings — the empty par `PPar(HashBag{})` and the
/// empty map `CastMap(MapLit({}))`. The user ruling of 2026-07-29 pinned this
/// count; a repair that made the close stricter across the board would collapse
/// it to one.
#[test]
fn antivacuity_empty_brace_keeps_exactly_two_readings() {
    let rs = readings("{}");
    assert_eq!(
        rs.len(),
        2,
        "`{{}}` is genuinely two-way ambiguous (empty par / empty map); got {rs:?}",
    );
}

/// ⚠ INSERTION ORDER, NEVER SORTED.
///
/// `PathMapLit`/`HashMapLit` preserve insertion order, and the payload must show
/// it. (`Display` sorts — which is exactly why these rows read the payload and
/// not the rendering.)
#[test]
fn antivacuity_multi_entry_literals_keep_insertion_order() {
    let (len, entries) = sole_payload("{| 1 : 2, 3 : 4 |}");
    assert_eq!(len, 2);
    assert_eq!(
        entries,
        vec![("1".to_string(), "2".to_string()), ("3".to_string(), "4".to_string())],
        "pathmap entries keep INSERTION order in the payload",
    );

    // The order-sensitive control: writing the same two entries the other way
    // round must produce the other order, so the row above is evidence of order
    // preservation rather than of the sorted order coinciding with it.
    let (len, entries) = sole_payload("{| 3 : 4, 1 : 2 |}");
    assert_eq!(len, 2);
    assert_eq!(
        entries,
        vec![("3".to_string(), "4".to_string()), ("1".to_string(), "2".to_string())],
        "⚠ NEVER SORTED — `{{| 3 : 4, 1 : 2 |}}` must NOT come back as `1, 3`",
    );
}

/// ★ RULING E (2026-07-29) — DISPLAY NO LONGER SORTS, AND THE ROUND TRIP PROVES
/// IT IS SAFE.
///
/// Generated `display.rs` used to run
/// `entries.sort_by(|a, b| format!("{}", a.0).cmp(&format!("{}", b.0)))` on
/// pathmap entries — a sort by the FORMATTED key, so `[10]` rendered before
/// `[9]`, and one that put `Display` in permanent disagreement with the
/// container's own `iter()`.
///
/// The sibling asymmetry that shows it was a defect rather than a policy:
/// `lower_map` (map → `EMap`) does not sort, and the `Map::MapLit` arm of the
/// trampolined lowering does not sort. Only pathmaps were sorted, in the two
/// places pathmaps are rendered or lowered.
///
/// ⚠ Removing it is Display→parse VISIBLE, which is why this row asserts the
/// FIXPOINT and not merely the absence of a sort: `Display` must emit the
/// author's order, and re-parsing that text must return the same payload in the
/// same order. Both directions are checked, on an input whose sorted order and
/// insertion order DIFFER — otherwise the row could pass while the sort was
/// still in place.
#[test]
fn ruling_e_display_preserves_source_order_and_round_trips() {
    // Insertion order `3, 1` — a sort by key (or by formatted key) would render
    // `1, 3`, so this input DISCRIMINATES.
    let src = "{| 3 : 4, 1 : 2 |}";
    let term = sole_reading(src);
    let printed = term.to_string();
    assert_eq!(
        printed, "{|3:4, 1:2|}",
        "Display must emit the AUTHOR's order, not a sorted one",
    );
    // …and the printed form re-parses to the same payload, in the same order.
    let reparsed = sole_reading(&printed);
    assert_eq!(payload(&reparsed), payload(&term), "Display → parse fixpoint");
    assert_eq!(
        payload(&term).expect("pathmap payload").1,
        vec![("3".to_string(), "4".to_string()), ("1".to_string(), "2".to_string())],
    );

    // The formatted-key ordering hazard specifically: `[10]` vs `[9]`. Under the
    // removed sort these came back `[10], [9]` (lexicographic on rendered text)
    // regardless of how they were written.
    let src = "{| [9] : 1, [10] : 2 |}";
    let term = sole_reading(src);
    assert_eq!(
        payload(&term).expect("pathmap payload").1,
        vec![("[9]".to_string(), "1".to_string()), ("[10]".to_string(), "2".to_string())],
    );
    let reparsed = sole_reading(&term.to_string());
    assert_eq!(payload(&reparsed), payload(&term), "Display → parse fixpoint");
}

/// ★ ROOT-3 REGRESSION CONTROL.
///
/// The 40 misclassified slots were the auto-injected higher-order-literal
/// applications in the `Map` and `Pathmap` categories. Moving them from the kv
/// arity law (`items == 2·(seps+1)`, items even) to the sequence law
/// (`items == seps+1`) must not make any surface vanish: 1-, 2- and 3-argument
/// applications keep their reading counts.
///
/// The multi-argument application's surface is `$$proc(lam, a1, …, aN)` and the
/// single-argument one is `$proc(lam, a)` (generated `display.rs`); each is
/// exercised bare AND inside a `Map`/`Pathmap` literal, because it is the
/// `Map`-/`Pathmap`-CATEGORY copies of these variants whose slots were
/// misclassified.
#[test]
fn antivacuity_root3_hol_application_arities_still_parse() {
    for src in [
        // Bare, in the `Proc` category.
        "$proc(^x.{ x }, 1)",
        "$$proc(^x.{ x }, 1)",
        "$$proc(^x.{ x }, 1, 2)",
        "$$proc(^x.{ x }, 1, 2, 3)",
        // Inside a Map literal — the `Map`-category copies.
        "{ $$proc(^x.{ x }, 1) : 2 }",
        "{ $$proc(^x.{ x }, 1, 2) : 2 }",
        "{ $$proc(^x.{ x }, 1, 2, 3) : 2 }",
        // Inside a Pathmap literal — the `Pathmap`-category copies.
        "{| $$proc(^x.{ x }, 1) : 2 |}",
        "{| $$proc(^x.{ x }, 1, 2) : 2 |}",
        "{| $$proc(^x.{ x }, 1, 2, 3) : 2 |}",
        // …and as a BARE pathmap element, so the unset path meets the HOL path.
        "{| $$proc(^x.{ x }, 1, 2) |}",
    ] {
        mettail_runtime::clear_var_cache();
        let parsed = Proc::parse_via_wpda_all(src);
        assert!(
            parsed.as_ref().map(|r| !r.is_empty()).unwrap_or(false),
            "{src:?} must still parse — the 40 ROOT-3 slots changed ARITY LAW, \
             and nothing may vanish; got {parsed:?}",
        );
        assert_eq!(
            parsed.as_ref().map(|r| r.len()).unwrap_or(0),
            1,
            "{src:?} must stay UNAMBIGUOUS — moving a slot from the kv arity law \
             to the sequence law must not admit a second reading either",
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Row H — the generated slot census (ROOT 3, measured on the artifact)
// ═══════════════════════════════════════════════════════════════════════════

/// Rholang's generated collection-spec table must carry exactly **2** slots with
/// a `kv_sep`: `Map::MapLit` and `Pathmap::PathmapLit`. It carried **42**.
///
/// Read off the generated artifact rather than the engine, because the count is
/// a property of what codegen EMITTED — the defect was that 40 `Vec` slots were
/// emitted as kv slots, and only the artifact shows that directly. The two
/// `kv_sep` slots and the ONE `kv_value_optional` slot are asserted together, so
/// a change that flipped every slot to non-kv (which would also make this count
/// wrong in the other direction) cannot pass.
#[test]
fn rholang_has_exactly_two_kv_slots() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../target/generated/rholang/wpda.rs");
    let Ok(src) = std::fs::read_to_string(path) else {
        // The artifact is produced by the proc-macro during this crate's own
        // build, so it is present in any tree that compiled this test. Treat a
        // missing file as a skip rather than a failure, so the row cannot go
        // green by asserting on an empty string.
        panic!("generated wpda.rs not found at {path} — the census cannot be taken");
    };
    let kv = src.matches("kv_sep: Some(\":\")").count();
    let optional = src.matches("kv_value_optional: true").count();
    assert_eq!(
        kv, 2,
        "exactly two rholang collection slots are genuine kv slots \
         (Map::MapLit and Pathmap::PathmapLit); 40 `Vec` slots of the \
         auto-injected `MApply*` variants used to inherit `\":\"` from their \
         home category",
    );
    assert_eq!(
        optional, 1,
        "exactly ONE slot is value-optional (Pathmap::PathmapLit)",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// DEFERRED — pinned so it cannot become wrong-but-accepted
// ═══════════════════════════════════════════════════════════════════════════

/// `{| @a : @b, 1 : 2 |}` — the item-vector model predicts this should reduce to
/// `{|1:2|}` (the cross-category pair dropped, the well-formed pair kept). It
/// does not: the lineage dies BEFORE the close, mid-flat, so the close-time
/// classifier never sees it.
///
/// ⚠ **This repair does not fix that, and does not claim to.** The single gate
/// lives at the collection close; an input whose frontier dies earlier is out of
/// its reach. The row is pinned as `is_err()` so no future change can silently
/// convert this error into a *wrong-but-accepted* reading — the failure mode
/// that would be strictly worse than the current honest error.
///
/// Pre-registered probe for the follow-up: build with `--features walker-trace`,
/// run with `PRATTAIL_CANONICAL_GLL_STATS=1`, and read `coll_kv_pdiv`
/// (`coll_kv_parity_divergence`). Prediction: `> 0` on this input and `== 0` on
/// `{| 1 : 2, 3 : 4 |}`, which would identify the kv-phase parity computation as
/// lineage-blind.
#[test]
fn deferred_mixed_cross_category_and_well_formed_pairs_still_error() {
    mettail_runtime::clear_var_cache();
    let parsed = Proc::parse_via_wpda_all("{| @a : @b, 1 : 2 |}");
    assert!(
        parsed.is_err(),
        "DEFERRED (not fixed by this repair): this input errors before the \
         collection close. Pinned so it cannot silently become a \
         wrong-but-accepted reading; got {parsed:?}",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Ruling F (#163, 2026-07-29) — a pathmap literal is EITHER a set of paths OR a
// map from paths to values, never both
// ═══════════════════════════════════════════════════════════════════════════
//
// # What is refused, and what is deliberately NOT
//
// `{| 1, 2 : 3 |}` writes TWO DISTINCT keys of DIFFERING VALUEDNESS: `1` is
// bound to nothing, `2` is bound to `3`. Ruling D already refuses the SAME-key
// form (`{| 1 : 2, 1 |}`), because `insert` is last-write-wins there and one
// occurrence would silently delete the other. The distinct-key form has no
// last-write-wins hazard at all — both entries survive — so it is refused for a
// DIFFERENT reason, and it therefore gets a DIFFERENT message:
//
//   * Ruling D — ONE key, TWO contradictory bindings ⇒ a written contradiction.
//   * Ruling F — TWO keys, TWO KINDS of binding    ⇒ a container with no
//     single reading: `.get` on the unvalued half cannot answer, while `.get`
//     on the valued half can.
//
// ⚠ SCOPE, RULED (#163): only the LITERAL is refused. The per-entry runtime
// error of `55571eaf` remains the disposition for a mixed map assembled through
// `pathmap_put` / `pathmap_merge` / `write_zipper_set_leaf` / `set_subtrie` /
// `graft` / `joinInto`. Closing those five runtime paths is filed SEPARATELY as
// #167 and is NOT attempted here.
//
// ⚠★ THIS CONTRADICTS #151's STATED DESIGN INTENT, DELIBERATELY. The #151 note
// held that "the mixed form must stay expressible"; the #163 ruling supersedes
// it. Both are quoted in the commit body so a future reader does not "restore"
// the mixed form as a bug fix.

/// ★ THE SUBJECT — two distinct keys, differing valuedness. REFUSED.
#[test]
fn ruling_f_mixed_valuedness_across_distinct_keys_refuses_the_literal() {
    let ps = payloads("{| 1, 2 : 3 |}");
    assert!(
        ps.is_empty(),
        "`{{| 1, 2 : 3 |}}` binds `1` to NOTHING and `2` to `3` — a container \
         that is neither a set of paths nor a map from paths to values, so \
         `.get` has no uniform answer over it. It must be refused at the \
         literal. Got {ps:?}",
    );
}

/// The same subject with the valued entry FIRST — order must not decide it.
///
/// Without this row a refusal implemented as "an unset entry after a set entry"
/// would pass the row above and leave the mirror image accepted.
#[test]
fn ruling_f_refusal_is_order_independent() {
    let ps = payloads("{| 1 : 2, 3 |}");
    assert!(
        ps.is_empty(),
        "`{{| 1 : 2, 3 |}}` is the same mixed container written in the other \
         order; a refusal that depends on entry order is not a refusal of the \
         SHAPE. Got {ps:?}",
    );
}

/// ⚠ CONTROL — the ALL-UNVALUED literal must still parse.
///
/// This is the row that keeps Ruling F from becoming "refuse any pathmap with a
/// bare entry", which would delete the `{| k |}` surface that #74 exists to
/// support.
#[test]
fn ruling_f_control_all_unvalued_still_parses() {
    let (len, entries) = sole_payload("{| 1, 2 |}");
    assert_eq!(len, 2, "`{{| 1, 2 |}}` is a two-entry SET of paths");
    assert_eq!(
        entries,
        vec![("1".to_string(), "·".to_string()), ("2".to_string(), "·".to_string())],
        "both entries are present and both are UNSET",
    );
}

/// ⚠ CONTROL — the ALL-VALUED literal must still parse.
#[test]
fn ruling_f_control_all_valued_still_parses() {
    let (len, entries) = sole_payload("{| 1 : 2, 3 : 4 |}");
    assert_eq!(len, 2, "`{{| 1 : 2, 3 : 4 |}}` is a two-entry MAP");
    assert_eq!(
        entries,
        vec![("1".to_string(), "2".to_string()), ("3".to_string(), "4".to_string())],
    );
}

/// ★ TWO REFUSALS, TWO REASONS — Ruling D's message must not be absorbed.
///
/// Both inputs are refused, but they are refused by DIFFERENT predicates, and
/// this row is what keeps the two from collapsing into one catch-all: the
/// Ruling D subject has ONE key (so the Ruling F "distinct keys of differing
/// valuedness" predicate does not even apply to it), and the Ruling F subject
/// has NO duplicate key (so Ruling D's predicate does not apply to it).
#[test]
fn ruling_d_and_ruling_f_subjects_are_disjoint_and_both_refused() {
    // Ruling D's subject: one key, two contradictory bindings.
    assert!(payloads("{| 1 : 2, 1 |}").is_empty(), "Ruling D still refuses");
    // Ruling F's subject: two keys, two kinds of binding.
    assert!(payloads("{| 1, 2 : 3 |}").is_empty(), "Ruling F refuses");
    // ★ ANTI-MERGE: a single-key pathmap of EITHER valuedness is accepted, so
    // neither refusal is "refuse anything with a `:`" or "refuse anything
    // without one".
    assert_eq!(sole_payload("{| 1 |}").0, 1, "single unvalued entry accepted");
    assert_eq!(sole_payload("{| 1 : 2 |}").0, 1, "single valued entry accepted");
}
