//! In-process thread-local registry for language/fragment definitions.
//!
//! All proc-macro invocations in a crate share the same compiler process (and thread),
//! so a `thread_local!` HashMap persists across `language!` / `language_fragment!`
//! invocations within the same compilation unit.
//!
//! ## Critical Invariant
//!
//! The registry stores **raw input tokens** as binary-encoded bytes, not parsed
//! `LanguageDef` values. Registration happens immediately after parsing (before
//! validation, classification, FIRST/FOLLOW, WFST, optimization). On lookup,
//! bytes are decoded into a fresh `TokenStream` and re-parsed into a `LanguageDef`.
//!
//! This ensures:
//! - Dead rules from grammar A that become live when composed with grammar B are preserved
//! - Classification is re-derived on the merged grammar
//! - FIRST/FOLLOW sets are computed fresh on the merged grammar
//! - The WFST pipeline optimizes the unified grammar as a whole
//! - Lints and dead-rule detection run on the final merged grammar
//!
//! ## Cross-Invocation Safety
//!
//! `proc_macro2` types (`Ident`, `TokenStream`, `Literal`, etc.) are session-scoped
//! bridge handles — they become invalid after the proc-macro invocation that created
//! them completes. Storing `LanguageDef` (which contains these types) and accessing
//! it from a later invocation crashes with "Rust cannot catch foreign exceptions".
//!
//! The binary codec (`token_codec`) serializes the raw `TokenStream` into plain
//! `Vec<u8>` (no bridge dependencies). On lookup, `token_codec::decode` constructs
//! fresh bridge-valid types in the current session via `Ident::new`, `Punct::new`,
//! etc. — all with `Span::call_site()`.
//!
//! ## Drop Safety
//!
//! The registry stores only `Vec<u8>` — no `ManuallyDrop` needed since plain bytes
//! have no proc_macro bridge dependencies in their destructors.

use std::cell::RefCell;
use std::collections::HashMap;

use super::language::LanguageDef;
use super::token_codec;

/// What kind of definition was stored.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EntryKind {
    Language,
    Fragment,
}

impl EntryKind {
    /// How this kind is spelled in a diagnostic, as the macro the author wrote.
    fn macro_name(self) -> &'static str {
        match self {
            EntryKind::Language => "language!",
            EntryKind::Fragment => "language_fragment!",
        }
    }
}

thread_local! {
    /// Registry stores binary-encoded TokenStream bytes, not LanguageDef.
    /// No ManuallyDrop needed — Vec<u8> has no bridge dependencies.
    static REGISTRY: RefCell<HashMap<String, (EntryKind, Vec<u8>)>> =
        RefCell::new(HashMap::new());
}

/// The diagnostic for re-registering `name`, or `None` if the name is free.
///
/// # Why a duplicate name must be rejected rather than absorbed
///
/// The registry is keyed by NAME and is the only thing `extends:`, `includes:` and
/// `mixins:` resolve against ([`crate::merge::apply_extends`] and its siblings). Storing
/// a second definition under a name that is already taken therefore does not merely lose
/// the first definition — it silently *redirects every consumer of that name to different
/// grammar*. A third specification that says `extends: [Math]` inherits whichever `Math`
/// happened to be compiled last, and nothing anywhere reports that a choice was made.
///
/// One namespace covers both kinds deliberately: [`lookup_language_def`] resolves a name
/// to a `LanguageDef` whether it was stored by `language!` or by `language_fragment!`, so
/// a fragment and a language sharing a name are as ambiguous to a consumer as two
/// languages sharing one. Both collisions are reported, and the message names the kind on
/// each side so the author can see which two declarations are in conflict.
///
/// The check is deliberately not content-sensitive. "Same name, identical body is fine"
/// would reintroduce last-writer-wins for every case where the bodies drift by one
/// character, which is precisely the case worth catching, and it would make the rule
/// depend on invisible state instead of on the declarations themselves.
fn duplicate_registration_diagnostic(name: &str, incoming: EntryKind) -> Option<String> {
    let existing = REGISTRY.with(|r| r.borrow().get(name).map(|(kind, _)| *kind))?;
    Some(format!(
        "duplicate definition name '{name}': a {existing} with this name is already \
         registered in this compilation unit, and this {incoming} would replace it. \
         The registry is what `extends:`, `includes:` and `mixins:` resolve against, so \
         a second definition under an existing name silently changes which grammar every \
         consumer of '{name}' inherits. Rename one of the two declarations.",
        existing = existing.macro_name(),
        incoming = incoming.macro_name(),
    ))
}

/// Store a definition's raw input tokens as binary bytes under `name`.
///
/// Fails closed on a name that is already registered: see
/// [`duplicate_registration_diagnostic`]. On failure the registry is left exactly as it
/// was, so the first definition remains resolvable and the diagnostic the caller raises
/// describes the whole of what happened.
fn register(name: &str, kind: EntryKind, input: &proc_macro2::TokenStream) -> Result<(), String> {
    if let Some(diagnostic) = duplicate_registration_diagnostic(name, kind) {
        return Err(diagnostic);
    }
    let bytes = token_codec::encode(input);
    REGISTRY.with(|r| {
        r.borrow_mut().insert(name.to_string(), (kind, bytes));
    });
    Ok(())
}

/// Store a language definition's raw input tokens as binary bytes.
///
/// Called during the current proc-macro invocation (bridge active).
/// The TokenStream is encoded immediately; no bridge types are retained.
///
/// MUST be called with the **raw macro input** BEFORE any processing
/// (validation, classification, FIRST/FOLLOW, WFST, optimization).
///
/// Returns `Err` with a ready-to-emit diagnostic if `name` is already taken. The caller
/// is the proc-macro entry point, which turns it into a compile error via `abort!` —
/// the same shape as the `extends`/`includes`/`mixins` errors this module's lookups feed
/// (`macros/src/lib.rs`). Keeping the diagnostic a value rather than an abort is what
/// lets the rule be exercised by an ordinary unit test, since `proc_macro_error`'s
/// `abort!` is only usable inside a proc-macro entry point.
pub fn register_language(name: &str, input: &proc_macro2::TokenStream) -> Result<(), String> {
    register(name, EntryKind::Language, input)
}

/// Store a fragment definition's raw input tokens as binary bytes.
///
/// Fails closed on a duplicate name exactly as [`register_language`] does; fragments and
/// languages share one namespace because [`lookup_language_def`] resolves both.
pub fn register_fragment(name: &str, input: &proc_macro2::TokenStream) -> Result<(), String> {
    register(name, EntryKind::Fragment, input)
}

/// Look up a previously registered definition by name.
///
/// Decodes the stored bytes into a fresh `TokenStream` (valid in the
/// current bridge session), then parses as the appropriate type.
/// Returns `None` if the name was never registered.
pub fn lookup_language_def(name: &str) -> Option<LanguageDef> {
    REGISTRY.with(|r| {
        let map = r.borrow();
        let (kind, bytes) = map.get(name)?;
        let ts = token_codec::decode(bytes);
        match kind {
            EntryKind::Language => {
                let def: LanguageDef =
                    syn::parse2(ts).expect("registry: stored language tokens failed to re-parse");
                Some(def)
            },
            EntryKind::Fragment => {
                let frag: super::fragment::FragmentDef =
                    syn::parse2(ts).expect("registry: stored fragment tokens failed to re-parse");
                Some(frag.to_language_def())
            },
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    #[test]
    fn register_language_roundtrip() {
        let ts: proc_macro2::TokenStream = quote! {
            name: TestRegLang,
            types {
                ![i32] as Num
            },
            terms {
                Add . a:Num, b:Num |- a "+" b : Num ![a + b] fold;
            },
            equations {
            },
            rewrites {
            },
        };
        register_language("TestRegLang", &ts).expect("the name is free");
        let retrieved = lookup_language_def("TestRegLang");
        assert!(retrieved.is_some());
        let lang = retrieved.expect("just checked");
        assert_eq!(lang.name.to_string(), "TestRegLang");
        assert_eq!(lang.types.len(), 1);
        assert_eq!(lang.terms.len(), 1);
    }

    #[test]
    fn register_fragment_roundtrip() {
        let ts: proc_macro2::TokenStream = quote! {
            name: TestRegFrag,
            types {
                ![i32] as Int
            },
            terms {
                AddFrag . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
            }
        };
        register_fragment("TestRegFrag", &ts).expect("the name is free");
        let retrieved = lookup_language_def("TestRegFrag");
        assert!(retrieved.is_some());
        let lang = retrieved.expect("just checked");
        assert_eq!(lang.name.to_string(), "TestRegFrag");
        assert_eq!(lang.types.len(), 1);
        assert_eq!(lang.terms.len(), 1);
        // Fragment → LanguageDef has empty equations/rewrites/logic
        assert!(lang.equations.is_empty());
        assert!(lang.rewrites.is_empty());
        assert!(lang.logic.is_none());
    }

    #[test]
    fn lookup_nonexistent_returns_none() {
        let result = lookup_language_def("NonexistentRegistryLang");
        assert!(result.is_none());
    }

    /// A second `language!` under a taken name is REJECTED, and the first definition
    /// survives intact.
    ///
    /// This test replaces `registry_overwrites_on_duplicate_name`, which asserted the
    /// opposite — that the second registration silently won, keeping only its two terms.
    /// That behaviour was never intended: it makes the grammar a third specification
    /// inherits via `extends: [OverwriteRegLang]` depend on compilation order, with no
    /// diagnostic anywhere. It went unexercised only because no two specifications in the
    /// repository happened to share a name.
    #[test]
    fn registry_rejects_duplicate_language_name() {
        // First registration: 1 type, 1 term.
        let ts1: proc_macro2::TokenStream = quote! {
            name: DuplicateRegLang,
            types {
                ![i32] as Num
            },
            terms {
                Add . a:Num, b:Num |- a "+" b : Num ![a + b] fold;
            },
            equations {
            },
            rewrites {
            },
        };
        register_language("DuplicateRegLang", &ts1).expect("the first name is free");

        // Second registration under the SAME name: 1 type, 2 terms.
        let ts2: proc_macro2::TokenStream = quote! {
            name: DuplicateRegLang,
            types {
                ![i32] as Num
            },
            terms {
                Add . a:Num, b:Num |- a "+" b : Num ![a + b] fold;
                Sub . a:Num, b:Num |- a "-" b : Num ![a - b] fold;
            },
            equations {
            },
            rewrites {
            },
        };
        let rejected = register_language("DuplicateRegLang", &ts2)
            .expect_err("a duplicate name must be rejected, not absorbed");
        assert!(
            rejected.contains("DuplicateRegLang"),
            "the diagnostic must name the colliding definition; got: {rejected}"
        );
        assert!(
            rejected.contains("language!"),
            "the diagnostic must name the kind on each side; got: {rejected}"
        );

        // The FIRST definition is what a consumer still resolves. A rejected
        // registration must not have partially replaced it.
        let retrieved = lookup_language_def("DuplicateRegLang").expect("should exist");
        assert_eq!(
            retrieved.terms.len(),
            1,
            "the rejected registration must leave the original definition in place"
        );
    }

    /// Languages and fragments share ONE namespace, so a fragment may not take a name a
    /// language already holds. `lookup_language_def` resolves either kind, so the
    /// collision is exactly as ambiguous for a consumer as two languages would be.
    #[test]
    fn registry_rejects_a_fragment_shadowing_a_language_name() {
        let lang: proc_macro2::TokenStream = quote! {
            name: CrossKindRegName,
            types {
                ![i32] as Num
            },
            terms {
                Add . a:Num, b:Num |- a "+" b : Num ![a + b] fold;
            },
            equations {
            },
            rewrites {
            },
        };
        register_language("CrossKindRegName", &lang).expect("the name is free");

        let frag: proc_macro2::TokenStream = quote! {
            name: CrossKindRegName,
            types {
                ![i32] as Int
            },
            terms {
                AddFrag . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
            }
        };
        let rejected = register_fragment("CrossKindRegName", &frag)
            .expect_err("a fragment must not shadow a registered language name");
        assert!(
            rejected.contains("language!") && rejected.contains("language_fragment!"),
            "the diagnostic must name BOTH kinds so the author can find both \
             declarations; got: {rejected}"
        );
    }

    /// The rule is about COLLISION, not about registering at all: a free name is accepted
    /// and reports no diagnostic. Without this, a `duplicate_registration_diagnostic` that
    /// returned `Some` unconditionally would still pass the two rejection tests above.
    #[test]
    fn registry_accepts_a_free_name() {
        assert_eq!(
            duplicate_registration_diagnostic("NeverRegisteredRegName", EntryKind::Language),
            None,
            "an unused name must produce no diagnostic"
        );
        let ts: proc_macro2::TokenStream = quote! {
            name: FreeRegName,
            types {
                ![i32] as Num
            },
            terms {
                Add . a:Num, b:Num |- a "+" b : Num ![a + b] fold;
            },
            equations {
            },
            rewrites {
            },
        };
        register_language("FreeRegName", &ts).expect("a free name must be accepted");
        assert!(lookup_language_def("FreeRegName").is_some());
    }
}
