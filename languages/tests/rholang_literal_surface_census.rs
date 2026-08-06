//! **THE LITERAL-SURFACE CENSUS — every category that DECLARES a literal must have one.**
//!
//! # The defect this gate exists for
//!
//! On 2026-07-29 the `Bytes` carrier was changed to `![Vec<u8>] as Bytes` — upstream's model,
//! where `RhoTypes.proto:230-232` carries `string g_string = 3` and `bytes g_byte_array = 25` as
//! two distinct wire types. The change was implemented, measured, and **HELD** (`2eebf722`)
//! because it left the category with **no surface form at all**:
//!
//! ```text
//! gen_rholang_prop::bytes_display_parse_roundtrip
//!   arb_bytes produced unparseable surface term ""
//! ```
//!
//! A `Vec<u8>` payload is not string-shaped, so no `StringLit` arm was emitted; and `Bytes`
//! declares no collection delimiters, so the collection `Display` arm wrapped its bytes in EMPTY
//! open/close. Eleven rows failed, and the value was constructible in Rust while being neither
//! writable nor printable in the language.
//!
//! The mechanism behind it generalises past `Bytes`, and that is why this file is not a
//! byte-array test. A `literals { Cat { pattern: …; eval: ![{ … }] } }` block whose category's
//! carrier belongs to no built-in token family was **parsed, validated, desugared into a
//! `TokenDef`, and compiled into the lexer DFA — and then dropped by the parser**, because
//! `classify_literal_patterned` (`macros/src/gen/runtime/wpda_codegen/prefix.rs`) looked the
//! family up from the `NativeKind` alone, got `None`, and returned
//! `AtomicShape::NonAtomic`. The token was produced and nothing could consume it. That is a
//! silent partial wiring, and `LiteralFamily::Custom` is the fix; this file is the gate that
//! keeps it fixed.
//!
//! # Why this is a gate and not a restatement
//!
//! | property | how it is obtained |
//! |---|---|
//! | the DOMAIN — which categories declare a literal | **derived** from the reconstructed `LanguageDef`, so a new `literals { … }` block joins it automatically and fails until witnessed |
//! | non-vacuity | an empty domain, or one missing `Bytes`, fails LOUDLY — the gate cannot pass by covering nothing |
//! | the check | the full round trip (`parse` then `display` then `parse`), because an unparseable rendering and a misrendered parse are one defect seen from two sides |
//!
//! Deliberately, this file references no category-specific AST variant, so it **compiles and
//! fails** against a tree in which the byte carrier has been reverted — rather than failing to
//! build, which would tell us only that a variant is missing.

#![cfg(feature = "rholang")]

use mettail_languages::rholang::Proc;
use mettail_rholang_codegen::reconstruct_language_def;
use mettail_runtime::Language;

/// One row of the census: a category that declares a `literals { … }` block, a WITNESS word of
/// its declared surface, and what that word must re-render as.
///
/// `rendered` may differ from `witness` when a non-canonical spelling normalises (a radix form,
/// a case variant); when they are equal the witness is already canonical.
struct SurfaceWitness {
    category: &'static str,
    witness: &'static str,
    rendered: &'static str,
}

/// ★ A TYPED EXCEPTION TABLE KEYED ON A DERIVED DOMAIN — not a hand-maintained mirror of one.
///
/// What must be covered is computed from the grammar; only the EVIDENCE is written here. Adding a
/// `literals { … }` block for a new category therefore fails this gate until a witness appears,
/// which is the property a hand-listed census can never have.
const SURFACE_WITNESSES: &[SurfaceWitness] = &[
    SurfaceWitness {
        category: "Int",
        witness: "7",
        rendered: "7",
    },
    SurfaceWitness {
        category: "BigInt",
        witness: "7n",
        rendered: "7n",
    },
    SurfaceWitness {
        category: "BigRat",
        witness: "3r",
        rendered: "3r",
    },
    SurfaceWitness {
        category: "Fixed",
        witness: "1.50p2",
        rendered: "1.50p2",
    },
    SurfaceWitness {
        category: "Float",
        witness: "1.5",
        rendered: "1.5",
    },
    SurfaceWitness {
        category: "Bytes",
        witness: r#"b"deadbeef""#,
        rendered: r#"b"deadbeef""#,
    },
];

/// Categories for which the grammar declares a `literals { Cat { pattern: …; eval: … } }` block.
/// DERIVED from the reconstructed `LanguageDef`, never transcribed.
fn categories_declaring_a_literal() -> Vec<String> {
    let source = mettail_languages::rholang::RholangLanguage
        .metadata()
        .definition_source()
        .expect("the rholang metadata carries its own definition source");
    let def = reconstruct_language_def(source).expect("the definition source reconstructs");
    let mut declared: Vec<String> = def
        .token_defs
        .iter()
        .filter(|td| td.from_literals && td.rust_code.is_some())
        .filter_map(|td| td.category.as_ref().map(|c| c.to_string()))
        .collect();
    declared.sort();
    declared.dedup();
    declared
}

fn parse(src: &str) -> Proc {
    mettail_runtime::clear_var_cache();
    Proc::parse(src).unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"))
}

/// ★ THE ENUMERATING GATE.
#[test]
fn every_category_declaring_a_literal_has_a_reachable_surface() {
    let declared = categories_declaring_a_literal();

    // ── the vacuity floor ────────────────────────────────────────────────────────────────
    assert!(
        !declared.is_empty(),
        "no category declares a `literals {{ … }}` block — either the grammar changed radically \
         or `definition_source` / `reconstruct_language_def` stopped seeing the block. Either \
         way this gate would otherwise pass by checking NOTHING.",
    );
    assert!(
        declared.iter().any(|c| c == "Bytes"),
        "`Bytes` must DECLARE its literal surface, and it does not. Derived domain: {declared:?}. \
         This is the floor that keeps the gate sensitive to the change it guards: with no \
         `literals {{ Bytes {{ … }} }}` block the byte carrier has NO surface form — not merely \
         no literal, which is upstream's position, but nothing renderable either. That is the \
         state `2eebf722` measured and held, where `Bytes::…(vec![])` rendered as the empty \
         string and eleven Display-roundtrip rows failed.",
    );

    // ── every derived member needs a witness, and every witness must round-trip ──────────
    for category in &declared {
        let row = SURFACE_WITNESSES
            .iter()
            .find(|w| w.category == category)
            .unwrap_or_else(|| {
                panic!(
                    "category `{category}` declares a `literals {{ … }}` block but has no witness \
                     in SURFACE_WITNESSES. A declared literal with no witness is exactly how a \
                     surface goes missing unnoticed — add a word of its declared pattern and what \
                     that word renders as."
                )
            });
        let term = parse(row.witness);
        assert_eq!(
            format!("{term}"),
            row.rendered,
            "`{}` (category `{category}`) must render as `{}`",
            row.witness,
            row.rendered,
        );
        let reparsed = parse(row.rendered);
        assert_eq!(
            format!("{reparsed}"),
            row.rendered,
            "`{}` must be a FIXPOINT of parse ∘ display for category `{category}`",
            row.rendered,
        );
    }
}
