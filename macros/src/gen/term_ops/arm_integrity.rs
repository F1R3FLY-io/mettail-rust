//! Structural arm-integrity meta-test for collection-literal categories
//! (2026-07-25, Stage 0-b).
//!
//! # Why this file exists
//!
//! Three separate times in this project a collection-literal defect was
//! "covered" by a unit test that exercised the *helper function* rather than the
//! *emitted arm*. A helper test asserts that `collection_literal_info` returns
//! `Some(..)`; it says nothing about whether the generator that calls it
//! actually used the answer. The defect survives a green test suite.
//!
//! This module tests the EMISSION instead, and it does so generically: it
//! renders every term-op generator against
//! [`crate::gen::collection_literal_language_for_tests`] and inspects the
//! resulting token stream for the signature of a leaf-treated collection —
//! a match arm whose payload is the wildcard `_`:
//!
//! ```text
//! List :: ListLit ( _ )   ⟵ the term op cannot see the elements
//! ```
//!
//! Because it works on rendered tokens and iterates a LIST of generators, it
//! covers operations that do not exist yet: a newly added term op that emits a
//! wildcard-payload arm for a collection literal shows up as an unexpected
//! entry and fails the ratchet below.
//!
//! # Why it is a ratchet rather than a flat assertion
//!
//! At Stage 0 the defect is real and unfixed — several ops legitimately still
//! emit `_` arms. A flat "no op may do this" assertion would simply be red, and
//! a red test carries no information about *progress* and invites being
//! `#[ignore]`d, which is how this class of defect hid in the first place.
//!
//! Instead [`WILDCARD_PAYLOAD_RATCHET`] declares the EXACT set of
//! `(op, category)` pairs that still treat a collection literal as an opaque
//! leaf. The test asserts set EQUALITY, which is bidirectional and therefore
//! strictly stronger than either half alone:
//!
//! - a pair that is fixed but still listed  ⇒ FAIL ("update the ratchet") — the
//!   ratchet can never silently over-claim defects;
//! - a pair that regresses, or a NEW op that leaf-treats collections ⇒ FAIL —
//!   the ratchet can never silently acquire defects.
//!
//! Each later stage of this campaign deletes rows from the ratchet. When the
//! ratchet is empty the defect class is closed, and the test becomes exactly the
//! flat assertion it should be.
//!
//! # What this detects, and what it does NOT
//!
//! The probe is deliberately narrow and precise: it detects the WILDCARD-PAYLOAD
//! form of leaf treatment, `Cat::Label(_)`, in which the op provably cannot read
//! the elements because it never binds them.
//!
//! There is a SECOND form the probe does not see, and stating it here is part of
//! the instrument's honesty. An op may bind the payload and then still treat it
//! as an opaque leaf by using a whole-value operation on it. The live example is
//! `match_pattern`, whose emission is
//!
//! ```text
//! (Cat::Label(v1), Cat::Label(v2)) if v1 == v2 => {}
//! ```
//!
//! — the payload IS bound, so no `_` appears, yet the arm decides the match by
//! `==` on the wrapper and therefore cannot bind a pattern variable occurring
//! inside the collection. That defect is real and is owned by Stage 4; it is
//! pinned by Stage 4's own behavioural tests rather than by this structural
//! probe, because "is this whole-value operation semantically leaf-like?" is not
//! decidable from the token stream.
//!
//! The consequence for reading a green run of this module: an empty ratchet
//! would mean "no op ignores the payload", NOT "every op handles collections
//! correctly". The two instruments are complementary.

#[cfg(test)]
mod tests {
    use crate::gen::term_ops::subst::{collect_category_variants, VariantKind};
    use crate::gen::{
        collection_literal_language_for_tests, COLLECTION_LITERAL_TEST_CATEGORIES,
        OPAQUE_LITERAL_TEST_CATEGORY,
    };
    use mettail_ast::language::LanguageDef;
    use proc_macro2::TokenStream;
    use std::collections::BTreeSet;

    /// Every term-op generator, named. Adding an op here is how the meta-test
    /// grows; an op absent from this list is invisible to it, so the list is
    /// asserted complete against the module tree by
    /// [`every_term_op_module_is_covered`].
    fn all_term_op_emissions(language: &LanguageDef) -> Vec<(&'static str, TokenStream)> {
        use crate::gen::term_ops::*;
        vec![
            ("depth", depth::generate_term_depth_methods(language)),
            ("ground", ground::generate_is_ground_methods(language)),
            ("iterative_cmp", iterative_cmp::generate_iterative_cmp(language)),
            ("iterative_clone", iterative_clone::generate_iterative_clone(language)),
            ("iterative_drop", iterative_drop::generate_iterative_drop(language)),
            ("iterative_hash", iterative_hash::generate_iterative_hash(language)),
            ("match_pattern", match_pattern::generate_match_pattern(language)),
            ("normalize", normalize::generate_normalize_functions(language, &[])),
            ("normalize_flatten", normalize::generate_flatten_helpers(language)),
            (
                "parse_alt_filter",
                parse_alt_filter::generate_parse_alt_filter_methods(language),
            ),
            ("semantic_hash", semantic_hash::generate_semantic_hash(language)),
            ("subst", subst::generate_substitution(language)),
            ("subst_env", subst::generate_env_substitution(language)),
        ]
    }

    /// `(op, category)` pairs whose emission still contains a wildcard-payload
    /// arm for a collection-literal category — i.e. which still treat a
    /// collection literal as an opaque leaf.
    ///
    /// ⚠ THIS LIST MUST ONLY EVER SHRINK. Populated empirically at Stage 0 by
    /// [`print_actual_wildcard_payload_set`]; each row is a live defect with a
    /// named owner stage.
    const WILDCARD_PAYLOAD_RATCHET: &[(&str, &str)] = &[
        // ── Stage 2 CLOSED (#29) — the ten `depth`/`ground` rows are RETIRED ──
        //
        // `term_depth` reported 0 and `is_ground` reported true for EVERY collection
        // literal, however deep and however many free variables it contained:
        // `depth([1, [2, 3]])` was 0, and `[1, v].is_ground()` was true with `v` free.
        // Both arms shared the SCALAR-literal arm, which is correct for a scalar (a
        // native payload has no term structure) and wrong for a container OF TERMS.
        //
        // Both now descend, through the same `collection_max_depth` /
        // `collection_all_ground` helpers every non-literal collection already used —
        // so a literal container and a non-literal one no longer disagree about the
        // same shape. `is_ground` was the urgent half: it is consulted to decide
        // whether a term may be treated as a finished value, so a false `true`
        // silently licensed downstream code to skip required work.
        // ── ★★ #162 RETIRED (2026-07-30) — the five `iterative_drop` rows are
        // ── GONE, and the heading they sat under was WRONG.
        //
        // They were listed as:
        //
        //     ── PERMANENT — leaf treatment is CORRECT here ──
        //     `iterative_drop`: the arm extracts CHILDREN for the trampolined
        //     drop. A collection literal's wrapper owns its elements and its own
        //     `Drop` frees them, so there is no child to hand to the trampoline.
        //     The `_` is the right emission; these rows are permanent.
        //
        // ⚠ "Its own `Drop` frees them" is TRUE and is exactly the defect. A
        // `Vec<Proc>`'s derived `Drop` frees the elements RECURSIVELY — one native
        // frame per nesting level — which is precisely what the trampoline exists
        // to prevent. `ast_drop` bisected to 254 B/level (debug) and 94 (release)
        // on the `CastList`/`ListLit` ladder while its `Add`-chain twin read 0, and
        // that asymmetry is the proof: the slope arrives with the COLLECTION, not
        // with the category hop.
        //
        // Recorded as a correction rather than silently deleted, because the claim
        // was plausible enough to be written down as PERMANENT and the next reader
        // is better served knowing which argument failed.
        //
        // `parse_alt_filter`: the arm answers "is this parse alternative a
        // NATIVE LITERAL reading?", which is true of a collection literal and
        // does not depend on the payload. The `_` is the right emission; these
        // rows are permanent.
        ("parse_alt_filter", "Bag"),
        ("parse_alt_filter", "List"),
        ("parse_alt_filter", "Map"),
        ("parse_alt_filter", "Pathmap"),
        ("parse_alt_filter", "Set"),
    ];

    /// Render `tokens` and report which collection-literal categories appear in
    /// a wildcard-payload arm `Cat :: Label ( _ )`.
    ///
    /// Token rendering via `to_string()` inserts spaces around punctuation, so
    /// the emitted text is matched with whitespace tolerance rather than by a
    /// brittle literal.
    fn wildcard_payload_categories(tokens: &TokenStream) -> BTreeSet<String> {
        let text = tokens.to_string();
        let normalized: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
        let mut found = BTreeSet::new();
        for (category, label) in COLLECTION_LITERAL_TEST_CATEGORIES {
            // `Cat :: Label (_)` with any interior spacing.
            for needle in
                [format!("{category} :: {label} (_)"), format!("{category} :: {label} ( _ )")]
            {
                if normalized.contains(&needle) {
                    found.insert((*category).to_string());
                }
            }
        }
        found
    }

    /// The observed `(op, category)` wildcard-payload set for the fixture.
    fn actual_wildcard_payload_set() -> BTreeSet<(String, String)> {
        let language = collection_literal_language_for_tests();
        let mut actual = BTreeSet::new();
        for (op, tokens) in all_term_op_emissions(&language) {
            for category in wildcard_payload_categories(&tokens) {
                actual.insert((op.to_string(), category));
            }
        }
        actual
    }

    /// ★ THE STRUCTURAL META-TEST.
    ///
    /// Set EQUALITY between the declared ratchet and the observed emission.
    #[test]
    fn no_term_op_leaf_treats_a_collection_literal_beyond_the_ratchet() {
        let actual = actual_wildcard_payload_set();
        let expected: BTreeSet<(String, String)> = WILDCARD_PAYLOAD_RATCHET
            .iter()
            .map(|(op, cat)| ((*op).to_string(), (*cat).to_string()))
            .collect();

        let newly_broken: Vec<_> = actual.difference(&expected).collect();
        let newly_fixed: Vec<_> = expected.difference(&actual).collect();

        assert!(
            newly_broken.is_empty(),
            "REGRESSION: these (op, category) pairs emit a wildcard-payload arm \
             `Cat::Label(_)` for a COLLECTION-LITERAL category, meaning the op \
             cannot see the element terms. Either fix the op or, if this is a \
             newly added op that is knowingly staged, add the pair to \
             WILDCARD_PAYLOAD_RATCHET with its owner stage.\n  {newly_broken:?}"
        );
        assert!(
            newly_fixed.is_empty(),
            "STALE RATCHET: these (op, category) pairs are listed as defective \
             but no longer emit a wildcard-payload arm. Delete them from \
             WILDCARD_PAYLOAD_RATCHET — the ratchet must never over-claim.\n  \
             {newly_fixed:?}"
        );
    }

    /// The fixture is only meaningful if it actually reaches the branch. This
    /// asserts the precondition that [`crate::gen::empty_language_for_tests`]
    /// fails — and is the reason a dedicated fixture had to be introduced.
    #[test]
    fn the_fixture_actually_reaches_the_collection_literal_branch() {
        use crate::gen::term_ops::subst::{collect_category_variants, VariantKind};

        let language = collection_literal_language_for_tests();
        for (category, label) in COLLECTION_LITERAL_TEST_CATEGORIES {
            let cat = quote::format_ident!("{}", category);
            let variants = collect_category_variants(&cat, &language);
            let found = variants.iter().any(
                |v| matches!(v, VariantKind::CollectionLiteral { label: l, .. } if l == label),
            );
            assert!(
                found,
                "fixture category `{category}` must classify as \
                 VariantKind::CollectionLiteral{{ label: {label} }}; got {variants:?}"
            );
        }

        // THE CONTROL: an opaque native literal must NOT be reclassified.
        let (opaque_cat, opaque_label) = OPAQUE_LITERAL_TEST_CATEGORY;
        let cat = quote::format_ident!("{}", opaque_cat);
        let variants = collect_category_variants(&cat, &language);
        assert!(
            variants
                .iter()
                .any(|v| matches!(v, VariantKind::Literal { label: l } if l == opaque_label)),
            "opaque control `{opaque_cat}` must stay VariantKind::Literal — a \
             blanket reclassification would satisfy every collection assertion \
             above while being wrong"
        );
        assert!(
            !variants
                .iter()
                .any(|v| matches!(v, VariantKind::CollectionLiteral { .. })),
            "opaque control `{opaque_cat}` must NOT produce a CollectionLiteral"
        );
    }

    /// The empty fixture CANNOT reach the branch — recorded as an executable
    /// fact so nobody "simplifies" a collection-literal test back onto it.
    #[test]
    fn the_empty_fixture_cannot_reach_the_collection_literal_branch() {
        use crate::gen::term_ops::subst::{collect_category_variants, VariantKind};

        let language = crate::gen::empty_language_for_tests();
        for (category, _) in COLLECTION_LITERAL_TEST_CATEGORIES {
            let cat = quote::format_ident!("{}", category);
            let variants = collect_category_variants(&cat, &language);
            assert!(
                !variants
                    .iter()
                    .any(|v| matches!(v, VariantKind::CollectionLiteral { .. })),
                "empty_language_for_tests() has `types: Vec::new()`, so it can \
                 never classify `{category}` as a collection literal. Any test \
                 that means to exercise collection-literal behaviour must use \
                 collection_literal_language_for_tests()."
            );
        }
    }

    /// Guards the completeness of [`all_term_op_emissions`]: every module in
    /// `term_ops` that generates emission must be represented, so that a newly
    /// added op cannot silently escape the meta-test.
    #[test]
    fn every_term_op_module_is_covered() {
        let covered: BTreeSet<&str> = all_term_op_emissions(&collection_literal_language_for_tests())
            .into_iter()
            .map(|(op, _)| op)
            // `normalize_flatten`/`subst_env` are second entry points of modules
            // already named; reduce to the module name.
            .map(|op| match op {
                "normalize_flatten" => "normalize",
                "subst_env" => "subst",
                other => other,
            })
            .collect();

        // The emission-bearing modules declared by `term_ops/mod.rs`.
        let declared: BTreeSet<&str> = [
            "depth",
            "ground",
            "iterative_cmp",
            "iterative_clone",
            "iterative_drop",
            "iterative_hash",
            "match_pattern",
            "normalize",
            "parse_alt_filter",
            "semantic_hash",
            "subst",
        ]
        .into_iter()
        .collect();

        assert_eq!(
            covered, declared,
            "all_term_op_emissions() must cover every emission-bearing term-op \
             module; otherwise a new op can leaf-treat collection literals \
             without the meta-test noticing"
        );
    }

    #[test]
    fn readzipper_writezipper_use_the_shared_recursive_carrier() {
        use crate::gen::native_carrier::{
            NativeCarrierStorage, NativeRecursiveCarrier, ZipperAccess,
        };
        use mettail_ast::language::LangType;

        let mut language = collection_literal_language_for_tests();
        for (name, carrier) in [("ReadZipper", "ReadZipperLit"), ("WriteZipper", "WriteZipperLit")]
        {
            language.types.push(LangType {
                name: quote::format_ident!("{}", name),
                role: Default::default(),
                native_type: Some(
                    syn::parse_str::<syn::Type>(&format!(
                        "std::sync::Arc<mettail_runtime::{carrier}<Proc, Proc>>"
                    ))
                    .expect("fixture native type must parse"),
                ),
                collection_kind: None,
            });
        }

        for (name, access) in
            [("ReadZipper", ZipperAccess::Read), ("WriteZipper", ZipperAccess::Write)]
        {
            let category = quote::format_ident!("{}", name);
            let variants = collect_category_variants(&category, &language);
            assert!(variants.iter().any(|variant| matches!(
                variant,
                VariantKind::RecursiveNativeLiteral {
                    carrier: NativeRecursiveCarrier::Zipper {
                        storage: NativeCarrierStorage::Arc,
                        access: actual_access,
                        key_category,
                        value_category,
                    },
                    ..
                } if *actual_access == access
                    && key_category == "Proc"
                    && value_category == "Proc"
            )));
        }
    }
}
