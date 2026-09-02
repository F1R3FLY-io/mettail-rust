//! **`rust_ctor` — the constructor schema**, a sibling of [`super::debug`] and
//! [`super::display`] that says how to write a term of this language as VALID RUST SOURCE.
//!
//! # The problem this pass exists to solve
//!
//! proptest records a falsifying input as two things: a seed (`cc <hex>`) and the shrunk
//! counterexample's `Debug` text (`# shrinks to term = …`). Promoting such an entry to a
//! named regression test means writing that term as Rust. **The recorded text is not Rust**,
//! and five independent reasons make textual massaging hopeless. Each is measured against
//! this repository's own generated output:
//!
//! 1. **`Arc` is erased.** `target/generated/calculator/ast_enums.rs` declares
//!    `GtStr(std::sync::Arc<Str>, std::sync::Arc<Str>)`; `Debug` prints `GtStr(Concat(…), …)`.
//!    Every nested node needs an `Arc::new` that appears nowhere in the text.
//! 2. **`String` prints as `&str`.** `StringLit(std::string::String)` prints
//!    `StringLit("ae")`, which is a `&'static str` in source position.
//! 3. **Enum qualification is erased AND ambiguous.** `super::debug` writes the bare variant
//!    name. Calculator has twelve sibling enums and `NumLit` exists in THREE with three
//!    payload types — `Int::NumLit(i32)`, `UInt32::NumLit(u32)`,
//!    `BigInt::NumLit(CanonicalBigInt)`. The text cannot disambiguate them; only the
//!    expected type at that position can.
//! 4. **Foreign values are not constructible from their `Debug`.** `UniqueId(51)` has a
//!    private field and only `UniqueId::new()`, which draws from a process-global counter.
//!    `Ratio { numer: 0, denom: 1 }` has private fields and needs `Ratio::new(0, 1)`.
//! 5. **Some of it is not Rust syntax at all.** `HashBag { counts: {Err: 1}, total_count: 1 }`
//!    — `{K: V}` is not a Rust expression. `Fixed(-2147483648/1)` parses as division.
//!    `Scope { pattern: …, body: … }` is SYNTHESIZED by the `Debug` emitter; the real API is
//!    `Scope::from_parts_unsafe`.
//!
//! # Why the schema is emitted rather than a printer alone
//!
//! The natural shape would be a term → source printer, `fn rust_ctor(&self) -> String`. That
//! is emitted here too. But a printer needs a TERM, and for a corpus entry we do not have
//! one — we have text. The obvious way to get the term back is to replay the recorded seed,
//! and **that does not work**: proptest persists the seed of the case's FIRST generated
//! input and separately records the SHRUNK value's `Debug`
//! (`proptest-1.10.0/src/test_runner/runner.rs`, `PersistedSeed(seed)` from
//! `gen_get_seed()` beside `value` out of `TestError::Fail(_, value)`). Replaying the seed
//! re-materializes the PRE-shrink input, which is a different and much larger term.
//! Measured on Lambda's sole entry: the recorded term binds `a6`, and replay yields `a7` at
//! every depth from 1 to 4.
//!
//! So the corpus text is the only complete record of the counterexample, and the schema
//! below is what lets a reader turn that text back into a term: it carries, for every
//! variant of every category, the FIELD TYPES that the `Debug` text drops. It is derived
//! from the same [`VariantKind`]/[`FieldInfo`] walk that drives [`super::debug`], so the
//! reader and the printer cannot drift apart — a new variant appears in both or in neither.
//!
//! # Why this file is written but not `include!`d
//!
//! Every other emitter in [`crate::gen::generate_all`] spills to
//! `target/generated/<lang>/<name>.rs` AND returns an `include!`. This one only writes. The
//! schema's consumer is a TOOL — `testkit`'s corpus harvester — which reads the file from
//! disk, exactly as the Blockly front end reads `<lang>-blocks.ts` from the same directory.
//! Nothing in the language's own compilation needs it, and `include!`ing a table for 263
//! Rholang variants into every build to serve a tool that runs occasionally would be paid
//! for on every compile by everyone.
//!
//! The file is nonetheless VALID RUST (`prettyplease` round-trips it), so it can be
//! `include!`d later without change if a runtime consumer ever appears.
//!
//! # Task #69 G1
//!
//! This writer routes through [`crate::logic::writer::write_lang_module`], so its output
//! lands under `target/generated/<lang>/` like every other pass. G1
//! (`macros/tests/generated_output_locality.rs`) asserts that the set of macro-authored
//! files OUTSIDE `target/` is empty; writing inside `target/` cannot violate it. What a
//! human later pastes into a tracked test file is a human's commit, not the macro's.

use proc_macro2::TokenStream;
use quote::quote;

use mettail_ast::language::LanguageDef;

use crate::gen::native::native_type_to_full_string;
use crate::gen::native_carrier::NativeCarrierStorage;
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};

/// Marker opening the machine-readable schema inside the emitted file.
///
/// The consumer extracts everything strictly between this line and [`SCHEMA_END`]. Markers
/// are used rather than "parse the Rust and find the const" so the harvester needs no Rust
/// parser and cannot be broken by a formatting change.
pub const SCHEMA_BEGIN: &str = "@@ METTAIL-RUST-CTOR-SCHEMA v1 BEGIN @@";

/// Marker closing the machine-readable schema. See [`SCHEMA_BEGIN`].
pub const SCHEMA_END: &str = "@@ METTAIL-RUST-CTOR-SCHEMA v1 END @@";

/// Emit the constructor schema and the human-facing constructor templates for `language`.
///
/// The returned `TokenStream` is what gets written to
/// `target/generated/<lang>/rust_ctor.rs`. See the module docs for why it is written and
/// not included.
pub fn generate_rust_ctor(language: &LanguageDef) -> TokenStream {
    let schema = schema_text(language);
    let doc = format!(
        "Constructor schema for `{}` — how to write a term of this language as valid Rust.\n\
         \n\
         Consumed by `testkit`'s proptest-corpus harvester, which reads this file from disk\n\
         and uses the schema to turn a recorded `# shrinks to` Debug text back into a term\n\
         and then into constructor source. See `macros/src/gen/syntax/rust_ctor.rs` for the\n\
         five measured reasons the Debug text is not itself Rust.\n\
         \n\
         GRAMMAR OF A SCHEMA LINE (one record per line, fields separated by single spaces):\n\
         \n\
         ```text\n\
         LANG <LanguageName>\n\
         CAT  <Category> <native-type|-> \n\
         V    <Category> <Label> <kind> <field>*\n\
         ```\n\
         \n\
         `<kind>` is one of `nullary`, `literal`, `collit`, `nativezipper`, `var`,\n\
         `regular`, `coll`, `binder`, `multibinder`. Each `<field>` is a type descriptor:\n\
         \n\
         | descriptor                     | Rust field type              | Debug shape |\n\
         |--------------------------------|------------------------------|-------------|\n\
         | `cat:<C>`                      | `Arc<C>`                     | nested term |\n\
         | `var`                          | `OrdVar`                     | `OrdVar(Free(FreeVar {{ .. }}))` |\n\
         | `native:<T>`                   | `<T>`                        | that type's own Debug |\n\
         | `coll:<Kind>:<Elem>`           | `HashBag<Arc<E>>` etc.       | container Debug |\n\
         | `collit:<Kind>:<Elem>`         | `HashSetLit<E>` etc.         | container Debug |\n\
         | `zipper:<Storage>:<Ctor>:<K>:<V>` | structural zipper payload | `<Ctor>(PathMapLit<K,V>, [u8])` |\n\
         | `scope1:<BinderCat>:<BodyCat>` | `Scope<Binder<String>, Arc<B>>` | `Scope {{ pattern: Binder(..), body: .. }}` |\n\
         | `scopeN:<BinderCat>:<BodyCat>` | `Scope<Vec<Binder<String>>, Arc<B>>` | `Scope {{ pattern: [Binder(..)], body: .. }}` |\n\
         | `pred`                         | `BehavioralPred`             | its own Debug |\n\
         | `opaque:token`                 | `String`                     | string literal |\n\
         | `opaque:guest`                 | `Arc<FltNode>`               | its own Debug |\n\
         | `opt:<descriptor>`             | `Option<..>`                 | `Some(..)` / `None` |\n\
         \n\
         A `literal` variant's payload type is its CATEGORY's native type, given on the\n\
         `CAT` line — which is what disambiguates `NumLit` across the three Calculator\n\
         enums that declare it.",
        language.name
    );

    // A RAW string literal, not `Literal::string`. The escaped form collapses the whole schema
    // onto one physical line as `\n`-escapes, and the consumer extracts the block by finding the
    // marker LINES — so the newlines have to survive `prettyplease`. No schema line can contain
    // `"` or `"#`: category names, labels and type descriptors are Rust identifiers, `:` and
    // `-`. The assertion below states that as a checked invariant rather than a hope.
    // ★ #141 G9. A REAL limit of the emission, not an internal agreement: the
    // schema is carried by a `r#"…"#` literal, so a `"` in a descriptor breaks the
    // delimiter. It was an `assert!`, which is mute in a proc macro under this
    // workspace's cranelift dev backend (#141 RED-0); it is now a `compile_error!`
    // in the emitted tokens, and the `.parse()` below is no longer reached with a
    // string it cannot tokenize.
    if schema.contains('"') {
        let message = format!(
            "mettail internal error: the constructor schema for language `{}` contains a \
             double quote, which the `r#\"…\"#` literal that carries it cannot delimit. A \
             descriptor grammar changed and this emitter must change with it. This is a \
             macro bug, not a grammar bug — please report it.",
            language.name,
        );
        return quote::quote_spanned!(language.name.span() => compile_error!(#message););
    }
    let schema_lit: TokenStream = format!("r#\"{schema}\"#")
        .parse()
        .expect("a raw string literal with no embedded `\"#` is a single valid token");
    let begin = SCHEMA_BEGIN;
    let end = SCHEMA_END;

    quote! {
        #![doc = #doc]

        /// The machine-readable constructor schema.
        ///
        /// The harvester extracts the text between the two markers rather than evaluating
        /// this `const`, so it needs no Rust parser; the `const` exists so the file is
        /// valid, reviewable Rust and so a future in-process consumer can use it directly.
        pub const RUST_CTOR_SCHEMA: &str = #schema_lit;

        /// Opening marker of the extractable schema block. See [`RUST_CTOR_SCHEMA`].
        pub const RUST_CTOR_SCHEMA_BEGIN: &str = #begin;

        /// Closing marker of the extractable schema block. See [`RUST_CTOR_SCHEMA`].
        pub const RUST_CTOR_SCHEMA_END: &str = #end;
    }
}

/// The schema body, framed by [`SCHEMA_BEGIN`]/[`SCHEMA_END`].
fn schema_text(language: &LanguageDef) -> String {
    // Preallocated: one line per category plus one per variant, at ~80 bytes a line. Rholang
    // has 263 variants, so this avoids the reallocation ladder on the largest grammar.
    let variant_estimate: usize = language
        .types
        .iter()
        .map(|t| collect_category_variants(&t.name, language).len())
        .sum();
    let mut out = String::with_capacity((language.types.len() + variant_estimate + 4) * 96);

    out.push_str(SCHEMA_BEGIN);
    out.push('\n');
    out.push_str(&format!("LANG {}\n", language.name));

    for lang_type in &language.types {
        // The FULL type expression, not the last path segment. `native_type_to_string` returns
        // `Vec` for `![Vec<Proc>]` and `CanonicalBigInt` for
        // `![mettail_runtime::CanonicalBigInt]`, which is right for its own callers and wrong
        // here: the reader has to choose between `String::from("s")`, a `Ratio`, and a bare
        // integer literal, and the discriminating information is exactly what the last segment
        // drops.
        //
        // ⚠ The DECLARED type is recorded, which is not always the EMITTED field type: `![str]
        // as Str` is declared `str` and emitted `std::string::String`. The reader owns that
        // mapping, and it must, because only the reader knows it is writing an owned value into
        // a constructor position.
        let native = lang_type
            .native_type
            .as_ref()
            .map(native_type_to_full_string)
            .unwrap_or_else(|| "-".to_string());
        // The token-stream rendering inserts spaces (`Vec < Proc >`); the schema is
        // space-separated, so they are squeezed out. No Rust type is ambiguous without them.
        let native: String = native.split_whitespace().collect();
        out.push_str(&format!("CAT {} {}\n", lang_type.name, native));
    }

    for lang_type in &language.types {
        let category = &lang_type.name;
        for variant in collect_category_variants(category, language) {
            out.push_str(&variant_line(category.to_string().as_str(), &variant, language));
        }
    }

    out.push_str(SCHEMA_END);
    out.push('\n');
    out
}

/// One `V` record: category, label, kind, then one descriptor per field IN DECLARATION
/// ORDER, which is the order [`super::debug`] prints them.
fn variant_line(category: &str, variant: &VariantKind, language: &LanguageDef) -> String {
    match variant {
        // ★ #141 G5. This receipt records what the variant walk SAW; a
        // classification that refuses is a thing it saw, and eliding it would
        // make the receipt disagree with the emission it is a receipt for.
        VariantKind::Refused { label, .. } => format!("V {category} {label} refused\n"),

        VariantKind::Nullary { label } => format!("V {category} {label} nullary\n"),

        VariantKind::Literal { label } => format!("V {category} {label} literal\n"),

        VariantKind::CollectionLiteral { label, element_cat, coll_type } => {
            format!("V {category} {label} collit collit:{:?}:{element_cat}\n", coll_type)
        },

        VariantKind::RecursiveNativeLiteral { label, carrier } => {
            let storage = match carrier.storage() {
                NativeCarrierStorage::Direct => "Direct",
                NativeCarrierStorage::Arc => "Arc",
            };
            let constructor = carrier.runtime_constructor_name();
            let key = carrier.key_category();
            let value = carrier.value_category();
            format!(
                "V {category} {label} nativezipper zipper:{storage}:{constructor}:{key}:{value}\n"
            )
        },

        VariantKind::Var { label } => format!("V {category} {label} var var\n"),

        VariantKind::Regular { label, fields } => {
            let mut line = format!("V {category} {label} regular");
            for field in fields {
                line.push(' ');
                line.push_str(&field_descriptor(field, language));
            }
            line.push('\n');
            line
        },

        VariantKind::Collection { label, element_cat, coll_type } => {
            format!("V {category} {label} coll coll:{:?}:{element_cat}\n", coll_type)
        },

        VariantKind::Binder {
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
        } => {
            let mut line = format!("V {category} {label} binder");
            for field in pre_scope_fields {
                line.push(' ');
                line.push_str(&field_descriptor(field, language));
            }
            line.push_str(&format!(" scope1:{binder_cat}:{body_cat}\n"));
            line
        },

        VariantKind::MultiBinder {
            label,
            pre_scope_fields,
            binder_cat,
            body_cat,
        } => {
            let mut line = format!("V {category} {label} multibinder");
            for field in pre_scope_fields {
                line.push(' ');
                line.push_str(&field_descriptor(field, language));
            }
            line.push_str(&format!(" scopeN:{binder_cat}:{body_cat}\n"));
            line
        },
    }
}

/// The descriptor for one field, `Option`-wrapping included.
///
/// The ORDER of the tests below matters and mirrors `super::debug`'s own arm order, because
/// the two must classify a field identically: an optional collection prints
/// `Some({container Debug})` while an optional category prints `Some(<nested term>)`, and a
/// reader that classified them the other way round would consume the wrong shape.
fn field_descriptor(field: &FieldInfo, language: &LanguageDef) -> String {
    let inner = bare_field_descriptor(field, language);
    if field.is_optional {
        format!("opt:{inner}")
    } else {
        inner
    }
}

fn bare_field_descriptor(field: &FieldInfo, language: &LanguageDef) -> String {
    if let Some(kind) = field.opaque_leaf {
        return match kind {
            crate::gen::term_ops::subst::OpaqueLeafKind::TokenText => "opaque:token".to_string(),
            crate::gen::term_ops::subst::OpaqueLeafKind::GuestBody => "opaque:guest".to_string(),
        };
    }
    if field.is_predicate {
        return "pred".to_string();
    }
    if field.is_collection {
        let kind = field
            .coll_type
            .as_ref()
            .map(|c| format!("{c:?}"))
            .unwrap_or_else(|| "Vec".to_string());
        return format!("coll:{kind}:{}", field.category);
    }
    let is_known_category = language.types.iter().any(|t| t.name == field.category);
    if is_known_category {
        // A category field whose category is itself a native alias is still reached through
        // the category enum, so `cat:` is right for both. The reader resolves the payload
        // shape from the CAT line's native type.
        format!("cat:{}", field.category)
    } else {
        // Not a declared category: the field is a bare native value and `super::debug`
        // prints it with `{:?}`. `field.category` holds the Rust type name in this case.
        format!("native:{}", field.category)
    }
}
