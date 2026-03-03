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
#[derive(Clone, Copy)]
enum EntryKind {
    Language,
    Fragment,
}

thread_local! {
    /// Registry stores binary-encoded TokenStream bytes, not LanguageDef.
    /// No ManuallyDrop needed — Vec<u8> has no bridge dependencies.
    static REGISTRY: RefCell<HashMap<String, (EntryKind, Vec<u8>)>> =
        RefCell::new(HashMap::new());
}

/// Store a language definition's raw input tokens as binary bytes.
///
/// Called during the current proc-macro invocation (bridge active).
/// The TokenStream is encoded immediately; no bridge types are retained.
///
/// MUST be called with the **raw macro input** BEFORE any processing
/// (validation, classification, FIRST/FOLLOW, WFST, optimization).
pub fn register_language(name: &str, input: &proc_macro2::TokenStream) {
    let bytes = token_codec::encode(input);
    REGISTRY.with(|r| {
        r.borrow_mut().insert(name.to_string(), (EntryKind::Language, bytes));
    });
}

/// Store a fragment definition's raw input tokens as binary bytes.
pub fn register_fragment(name: &str, input: &proc_macro2::TokenStream) {
    let bytes = token_codec::encode(input);
    REGISTRY.with(|r| {
        r.borrow_mut().insert(name.to_string(), (EntryKind::Fragment, bytes));
    });
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
                let def: LanguageDef = syn::parse2(ts)
                    .expect("registry: stored language tokens failed to re-parse");
                Some(def)
            }
            EntryKind::Fragment => {
                let frag: super::fragment::FragmentDef = syn::parse2(ts)
                    .expect("registry: stored fragment tokens failed to re-parse");
                Some(frag.to_language_def())
            }
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
        register_language("TestRegLang", &ts);
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
        register_fragment("TestRegFrag", &ts);
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

    #[test]
    fn registry_overwrites_on_duplicate_name() {
        // First registration: 1 type, 1 term
        let ts1: proc_macro2::TokenStream = quote! {
            name: OverwriteRegLang,
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
        register_language("OverwriteRegLang", &ts1);

        // Second registration: 1 type, 2 terms (overwrites)
        let ts2: proc_macro2::TokenStream = quote! {
            name: OverwriteRegLang,
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
        register_language("OverwriteRegLang", &ts2);

        let retrieved = lookup_language_def("OverwriteRegLang").expect("should exist");
        assert_eq!(retrieved.terms.len(), 2);
    }
}
