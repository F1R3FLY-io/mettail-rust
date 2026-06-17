//! Language struct and Term wrapper generation
//!
//! This module generates:
//! - `{Name}Term` wrapper implementing `mettail_runtime::Term`
//! - `{Name}Language` struct implementing `mettail_runtime::Language`

use crate::gen::{generate_literal_label, generate_var_label};
use mettail_ast::grammar::GrammarItem;
use mettail_ast::language::LanguageDef;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Ident, LitStr};

/// Generate the complete language implementation (Term wrapper + Language
/// struct + Language trait impl). The legacy Ascent runtime backend was retired
/// (P6); `run_ascent` resolves to the fail-closed `Language` trait default, so
/// no engine content is threaded into the generated struct.
pub fn generate_language_impl(language: &LanguageDef) -> TokenStream {
    // Stage 10.6 (2026-05-05): `reset_handle_mixfix_emitted()` call DELETED.
    // The `handle_mixfix_{Source}` thread-local dedup tracker lived inside
    // `prattail/src/trampoline.rs` (also deleted in Stage 10.6). Walker
    // (WPDS) doesn't emit `handle_mixfix_*` helpers; mixfix is encoded as
    // Reduce edges in the WPDS rule table.

    let name = &language.name;
    let name_str = name.to_string();
    let name_lower = name_str.to_lowercase();

    // Get the primary type (first type in the language)
    let primary_type = language
        .types
        .first()
        .map(|t| &t.name)
        .expect("Language must have at least one type");

    let (term_wrapper, language_struct, language_trait_impl) = if language.types.len() > 1 {
        (
            generate_term_wrapper_multi(name, language),
            generate_language_struct_multi(name, &name_str, &name_lower, language),
            generate_language_trait_impl_multi(name, &name_str, &name_lower, language),
        )
    } else {
        (
            generate_term_wrapper(name, primary_type),
            generate_language_struct(name, primary_type, &name_str, &name_lower, language),
            generate_language_trait_impl(name, primary_type, &name_str, &name_lower, language),
        )
    };

    // Per-concern spill: each of the three big sub-outputs goes to its own
    // file under `target/generated/<lang>/`. Ambient's pre-split language.rs
    // was 1,670 lines even after the ascent!{} invocation was already
    // extracted — it mixed the Term wrapper enum, the Language struct
    // definition, the Language trait impl, CEK decompose arms, and type
    // inference helpers. Splitting gives one file per concern; rustc can
    // still `include!` each independently during expansion, and humans can
    // diff per-concern changes without wading through a megafile.
    let lang_key = name_str.to_lowercase();
    let term_wrapper_include =
        crate::logic::writer::spill_and_include(&lang_key, "term_wrapper", term_wrapper);
    let language_struct_include =
        crate::logic::writer::spill_and_include(&lang_key, "language_struct", language_struct);
    let language_trait_impl_include = crate::logic::writer::spill_and_include(
        &lang_key,
        "language_trait_impl",
        language_trait_impl,
    );
    let rho_scalar_invocation_include = crate::logic::writer::spill_and_include(
        &lang_key,
        "rho_scalar_invocation",
        crate::gen::runtime::rho_invocation::generate_rho_scalar_invocation(language),
    );
    let dovetail_report_include = crate::logic::writer::spill_and_include(
        &lang_key,
        "dovetail_report",
        crate::gen::runtime::dovetail_report::generate_dovetail_report(language),
    );
    let numeric_cast_adapter_include = crate::logic::writer::spill_and_include(
        &lang_key,
        "numeric_cast_adapter",
        crate::gen::runtime::numeric_cast_adapter::generate_numeric_cast_adapter(language),
    );

    quote! {
        #term_wrapper_include
        #language_struct_include
        #language_trait_impl_include
        #rho_scalar_invocation_include
        #dovetail_report_include
        #numeric_cast_adapter_include
    }
}

/// Generate the Term wrapper struct
fn generate_term_wrapper(name: &syn::Ident, primary_type: &syn::Ident) -> TokenStream {
    let term_name = format_ident!("{}Term", name);

    quote! {
        /// Wrapper for the primary type that implements `mettail_runtime::Term`
        #[derive(Clone)]
        pub struct #term_name(pub #primary_type);

        impl mettail_runtime::Term for #term_name {
            fn clone_box(&self) -> Box<dyn mettail_runtime::Term> {
                Box::new(self.clone())
            }

            fn term_id(&self) -> u64 {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                self.0.hash(&mut hasher);
                hasher.finish()
            }

            fn term_eq(&self, other: &dyn mettail_runtime::Term) -> bool {
                if let Some(other_term) = other.as_any().downcast_ref::<#term_name>() {
                    self.0 == other_term.0
                } else {
                    false
                }
            }

            fn as_any(&self) -> &dyn std::any::Any {
                self
            }
        }

        impl std::fmt::Display for #term_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl std::fmt::Debug for #term_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", self.0)
            }
        }
    }
}

/// Generate the Term wrapper with an enum when the language has multiple types
/// (any combination of built-in or user-defined types, e.g. Int/Bool/Str or Proc/Name).
fn generate_term_wrapper_multi(name: &syn::Ident, language: &LanguageDef) -> TokenStream {
    let term_name = format_ident!("{}Term", name);
    let inner_enum_name = format_ident!("{}TermInner", name);

    let enum_variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            quote! { #cat(#cat) }
        })
        .collect();

    let display_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            quote! { #inner_enum_name::#cat(v) => write!(f, "{}", v) }
        })
        .collect();
    let debug_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            quote! { #inner_enum_name::#cat(v) => write!(f, "{:?}", v) }
        })
        .collect();

    let env_name = format_ident!("{}Env", name);
    let substitute_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("{}", cat);
            quote! { #inner_enum_name::#variant(t) => #inner_enum_name::#variant(t.substitute_env(env)) }
        })
        .collect();

    // Cross-category variable resolution: if after substitution we still have a variable,
    // look it up in other categories (e.g. "x" parsed as Int but bound as Bool -> use Bool value).
    let var_label_per_cat: Vec<(Ident, Ident)> = language
        .types
        .iter()
        .map(|t| (t.name.clone(), generate_var_label(&t.name)))
        .collect();
    let cross_resolve_arms: Vec<TokenStream> = var_label_per_cat
        .iter()
        .map(|(cat, var_label)| {
            let other_lookups: Vec<TokenStream> = language
                .types
                .iter()
                .filter(|t| t.name != *cat)
                .map(|t| {
                    let variant = format_ident!("{}", t.name);
                    let field = format_ident!("{}", t.name.to_string().to_lowercase());
                    quote! {
                        if let Some(val) = env.#field.get(&name) {
                            return #inner_enum_name::#variant(val.clone());
                        }
                    }
                })
                .collect();
            quote! {
                #inner_enum_name::#cat(#cat::#var_label(v)) => {
                    let name = match &v.0 {
                        mettail_runtime::Var::Free(fv) => fv.pretty_name.as_ref().map(|s| s.to_string()),
                        mettail_runtime::Var::Bound(bv) => bv.pretty_name.as_ref().map(|s| s.to_string()),
                    };
                    if let Some(name) = name {
                        #(#other_lookups)*
                    }
                }
            }
        })
        .collect();

    // Phase F.13 Stage 2.3.1 (2026-05-22): per-variant dispatch arms
    // for `semantic_hash` on the inner enum. Each arm emits a unique
    // discriminant byte (variant index in language.types) so distinct
    // categories don't collide, then delegates to the inner Cat's
    // `semantic_hash` (generated by `term_ops::semantic_hash`).
    let semantic_hash_dispatch_arms: Vec<TokenStream> = language
        .types
        .iter()
        .enumerate()
        .map(|(i, t)| {
            let variant = format_ident!("{}", t.name);
            let disc = i as u8;
            quote! {
                #inner_enum_name::#variant(inner) => {
                    state.write_u8(#disc);
                    inner.semantic_hash(state);
                }
            }
        })
        .collect();
    let extraction_semantic_hash_dispatch_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let variant = format_ident!("{}", t.name);
            quote! {
                #inner_enum_name::#variant(inner) => {
                    inner.semantic_hash(&mut state);
                }
            }
        })
        .collect();

    // Generate per-variant substitute_env arms for Ambiguous handling
    let ambiguous_substitute_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("{}", cat);
            quote! { #inner_enum_name::#variant(t) => #inner_enum_name::#variant(t.substitute_env(env)) }
        })
        .collect();

    // Generate cross-resolve logic for Ambiguous handling (applied per-alternative)
    let ambiguous_cross_resolve_arms: Vec<TokenStream> = var_label_per_cat
        .iter()
        .map(|(cat, var_label)| {
            let other_lookups: Vec<TokenStream> = language
                .types
                .iter()
                .filter(|t| t.name != *cat)
                .map(|t| {
                    let variant = format_ident!("{}", t.name);
                    let field = format_ident!("{}", t.name.to_string().to_lowercase());
                    quote! {
                        if let Some(val) = env.#field.get(&name) {
                            return #inner_enum_name::#variant(val.clone());
                        }
                    }
                })
                .collect();
            quote! {
                #inner_enum_name::#cat(#cat::#var_label(v)) => {
                    let name = match &v.0 {
                        mettail_runtime::Var::Free(fv) => fv.pretty_name.as_ref().map(|s| s.to_string()),
                        mettail_runtime::Var::Bound(bv) => bv.pretty_name.as_ref().map(|s| s.to_string()),
                    };
                    if let Some(name) = name {
                        #(#other_lookups)*
                    }
                }
            }
        })
        .collect();

    // Per-variant arms for iterative Hash/PartialEq/Clone on the wrapper
    // enum. These delegate to each inner category's already-iterative PDA
    // impl (from iterative_hash.rs / iterative_cmp.rs / iterative_clone.rs).
    // For the `Ambiguous(Vec<Self>)` variant, we iterate the alts with an
    // explicit work stack — no compiler-generated recursion through nested
    // Ambiguous trees. Per the stack-safety mandate.
    let wrapper_hash_arms: Vec<TokenStream> = language
        .types
        .iter()
        .enumerate()
        .map(|(i, t)| {
            let variant = format_ident!("{}", t.name);
            let idx = i as u8;
            quote! { #inner_enum_name::#variant(inner) => { state.write_u8(#idx); inner.hash(state); } }
        })
        .collect();
    let ambiguous_disc: u8 = language.types.len() as u8 + 1;
    let wrapper_eq_arms_same: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let variant = format_ident!("{}", t.name);
            quote! { (#inner_enum_name::#variant(a), #inner_enum_name::#variant(b)) => a == b }
        })
        .collect();
    // Per-category match arms that write an iterative-cloned inner value
    // into a result slot (used by the iterative Ambiguous-walk Clone impl).
    let wrapper_clone_arms_for_pda: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let variant = format_ident!("{}", t.name);
            quote! {
                #inner_enum_name::#variant(inner) => {
                    results[slot] = Some(#inner_enum_name::#variant(inner.clone()));
                }
            }
        })
        .collect();

    quote! {
        /// Inner term enum for multi-category languages (one variant per type in the language).
        /// The `Ambiguous` variant holds multiple parse alternatives that will be resolved
        /// during substitution or Ascent evaluation.
        ///
        /// `Clone`, `Hash`, and `PartialEq` are implemented manually (not
        /// derived) to avoid unbounded CPU-stack recursion through the
        /// `Ambiguous(Vec<Self>)` variant. Each impl delegates to the
        /// inner category's already-iterative PDA trait, and walks
        /// `Ambiguous` alts iteratively via an explicit work stack.
        pub enum #inner_enum_name {
            #(#enum_variants),*,
            /// Multiple parse alternatives (2+, flat — no nested Ambiguous).
            Ambiguous(Vec<#inner_enum_name>),
        }

        #[derive(Default)]
        struct __MettailSemanticKeyHasher {
            bytes: Vec<u8>,
        }

        impl __MettailSemanticKeyHasher {
            fn into_key(self) -> Vec<u8> {
                self.bytes
            }

            fn push_raw(&mut self, tag: u8, payload: &[u8]) {
                self.bytes.push(tag);
                self.bytes.extend_from_slice(&(payload.len() as u64).to_le_bytes());
                self.bytes.extend_from_slice(payload);
            }

            fn push_fixed(&mut self, tag: u8, payload: &[u8]) {
                self.bytes.push(tag);
                self.bytes.extend_from_slice(payload);
            }
        }

        impl std::hash::Hasher for __MettailSemanticKeyHasher {
            fn finish(&self) -> u64 {
                let mut h = 0xcbf29ce484222325u64;
                for b in &self.bytes {
                    h ^= *b as u64;
                    h = h.wrapping_mul(0x100000001b3);
                }
                h
            }

            fn write(&mut self, bytes: &[u8]) {
                self.push_raw(0, bytes);
            }

            fn write_u8(&mut self, i: u8) {
                self.push_fixed(1, &[i]);
            }

            fn write_u16(&mut self, i: u16) {
                self.push_fixed(2, &i.to_le_bytes());
            }

            fn write_u32(&mut self, i: u32) {
                self.push_fixed(3, &i.to_le_bytes());
            }

            fn write_u64(&mut self, i: u64) {
                self.push_fixed(4, &i.to_le_bytes());
            }

            fn write_u128(&mut self, i: u128) {
                self.push_fixed(5, &i.to_le_bytes());
            }

            fn write_usize(&mut self, i: usize) {
                self.push_fixed(6, &(i as u128).to_le_bytes());
            }

            fn write_i8(&mut self, i: i8) {
                self.push_fixed(7, &i.to_le_bytes());
            }

            fn write_i16(&mut self, i: i16) {
                self.push_fixed(8, &i.to_le_bytes());
            }

            fn write_i32(&mut self, i: i32) {
                self.push_fixed(9, &i.to_le_bytes());
            }

            fn write_i64(&mut self, i: i64) {
                self.push_fixed(10, &i.to_le_bytes());
            }

            fn write_i128(&mut self, i: i128) {
                self.push_fixed(11, &i.to_le_bytes());
            }

            fn write_isize(&mut self, i: isize) {
                self.push_fixed(12, &(i as i128).to_le_bytes());
            }
        }

        impl Clone for #inner_enum_name {
            fn clone(&self) -> Self {
                // Iterative Ambiguous-chain walk. For deeply nested
                // Ambiguous (Ambiguous(vec![Ambiguous(vec![...])])), an
                // explicit slot-buffer PDA handles the traversal without
                // CPU-stack recursion. Non-Ambiguous variants delegate
                // directly to the inner category's iterative Clone PDA.
                enum Task<'a> {
                    Visit { src: &'a #inner_enum_name, slot: usize },
                    AssembleAmbig { slot: usize, start: usize, count: usize },
                }
                let mut stack: Vec<Task<'_>> = Vec::new();
                let mut results: Vec<Option<#inner_enum_name>> = vec![None];
                stack.push(Task::Visit { src: self, slot: 0 });
                while let Some(t) = stack.pop() {
                    match t {
                        Task::Visit { src, slot } => match src {
                            #(#wrapper_clone_arms_for_pda)*
                            #inner_enum_name::Ambiguous(alts) => {
                                let start = results.len();
                                for _ in 0..alts.len() {
                                    results.push(None);
                                }
                                let count = alts.len();
                                stack.push(Task::AssembleAmbig { slot, start, count });
                                for (i, alt) in alts.iter().enumerate().rev() {
                                    stack.push(Task::Visit { src: alt, slot: start + i });
                                }
                            }
                        },
                        Task::AssembleAmbig { slot, start, count } => {
                            let mut vec: Vec<#inner_enum_name> = Vec::with_capacity(count);
                            for i in 0..count {
                                vec.push(
                                    results[start + i]
                                        .take()
                                        .expect("iterative TermInner clone: missing Ambiguous alt"),
                                );
                            }
                            results[slot] = Some(#inner_enum_name::Ambiguous(vec));
                        }
                    }
                }
                results[0].take().expect("iterative TermInner clone: root slot empty")
            }
        }

        impl std::hash::Hash for #inner_enum_name {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                // Iterative walk: for Ambiguous, push alts onto a work
                // stack rather than calling hash() recursively via derive.
                // Same-cat variants delegate to the iterative Hash PDA.
                let mut stack: Vec<&#inner_enum_name> = Vec::new();
                stack.push(self);
                while let Some(cur) = stack.pop() {
                    match cur {
                        #(#wrapper_hash_arms)*
                        #inner_enum_name::Ambiguous(alts) => {
                            state.write_u8(#ambiguous_disc);
                            state.write_usize(alts.len());
                            // Push in reverse so first alt is hashed first.
                            for alt in alts.iter().rev() {
                                stack.push(alt);
                            }
                        }
                    }
                }
            }
        }

        impl PartialEq for #inner_enum_name {
            fn eq(&self, other: &Self) -> bool {
                // Iterative deep-equality. For Ambiguous-vs-Ambiguous, walks
                // alt pairs on an explicit stack. Mismatched variants are
                // unequal (early-exit). Inner category equality goes through
                // the iterative Eq PDA.
                let mut stack: Vec<(&#inner_enum_name, &#inner_enum_name)> = Vec::new();
                stack.push((self, other));
                while let Some((a, b)) = stack.pop() {
                    let equal = match (a, b) {
                        #(#wrapper_eq_arms_same,)*
                        (#inner_enum_name::Ambiguous(la), #inner_enum_name::Ambiguous(lb)) => {
                            if la.len() != lb.len() {
                                false
                            } else {
                                for (x, y) in la.iter().zip(lb.iter()) {
                                    stack.push((x, y));
                                }
                                true
                            }
                        }
                        _ => false,
                    };
                    if !equal { return false; }
                }
                true
            }
        }

        impl Eq for #inner_enum_name {}

        impl #inner_enum_name {
            /// Phase F.13 Stage 2.3.1 (2026-05-22): semantic_hash dispatch
            /// on the inner enum — emit a per-variant discriminant byte
            /// (so distinct categories with structurally-similar inners
            /// don't accidentally collide) then delegate to the inner
            /// Cat's `semantic_hash`.
            ///
            /// For `Ambiguous(alts)`: record sorted child semantic keys
            /// so nested Ambiguous wrappers (rare; flattened before
            /// dedup) remain canonical.
            #[allow(dead_code)]
            pub fn semantic_hash<H: std::hash::Hasher>(&self, state: &mut H) {
                use std::hash::Hasher as _;
                match self {
                    #(#semantic_hash_dispatch_arms),*,
                    #inner_enum_name::Ambiguous(alts) => {
                        state.write_u8(255u8);
                        let mut sub: Vec<Vec<u8>> = alts
                            .iter()
                            .map(|a| a.semantic_fingerprint())
                            .collect();
                        sub.sort_unstable();
                        for key in sub {
                            state.write_usize(key.len());
                            state.write(&key);
                        }
                    }
                }
            }

            /// Exact semantic observation key used by ambiguity deduplication.
            /// This records the `semantic_hash` write stream itself rather than
            /// comparing a 64-bit digest of that stream.
            fn semantic_fingerprint(&self) -> Vec<u8> {
                let mut hasher = __MettailSemanticKeyHasher::default();
                self.semantic_hash(&mut hasher);
                hasher.into_key()
            }

            /// Exact semantic observation key used by result-graph extraction.
            /// Unlike `semantic_fingerprint`, this mirrors
            /// `multi_cat_union_extract`: hash the category term itself without
            /// the generated inner-enum category discriminant, so transparent
            /// cross-category quotienting and `rewrite_seed_ids` agree.
            fn extraction_semantic_fingerprint(&self) -> Vec<u8> {
                use std::hash::Hasher as _;
                let mut state = __MettailSemanticKeyHasher::default();
                match self {
                    #(#extraction_semantic_hash_dispatch_arms),*,
                    #inner_enum_name::Ambiguous(alts) => {
                        state.write_u8(255u8);
                        let mut sub: Vec<Vec<u8>> = alts
                            .iter()
                            .map(|a| a.extraction_semantic_fingerprint())
                            .collect();
                        sub.sort_unstable();
                        for key in sub {
                            state.write_usize(key.len());
                            state.write(&key);
                        }
                    }
                }
                state.into_key()
            }

            /// Collapse a vec of alternatives into a single term.
            /// Invariants: flattens nested Ambiguous, panics on empty, unwraps singletons,
            /// and deduplicates only by observational equivalence.
            ///
            /// This deliberately does not use groundness, WFST weight, or declaration order
            /// to choose a single representative from semantically distinct alternatives.
            /// Evaluation evidence is allowed to reject alternatives later; parse assembly is
            /// only allowed to merge alternatives that share a semantic hash.
            fn from_alternatives(alts: Vec<Self>) -> Self {
                let flat: Vec<Self> = alts.into_iter().flat_map(|a| match a {
                    Self::Ambiguous(inner) => inner,
                    other => vec![other],
                }).collect();
                match flat.len() {
                    0 => panic!("from_alternatives: empty alternatives"),
                    1 => flat.into_iter().next().expect("checked len == 1"),
                    _ => {
                        // Phase F.13 Stage 2.3.1 (2026-05-22):
                        // semantic-key dedup — equivalence class under
                        // Ascent's rewrite relation, not structural identity
                        // and not Display identity. Transparent projection
                        // wrappers (cast-permutation cohorts like IntToBigRat /
                        // BigIntToBigRat / IntToBigInt) collapse to a canonical
                        // core; evaluatively-distinct alts (like -3! Fact vs
                        // Neg(Fact)) are preserved.
                        //
                        // Replaces both weight/groundness selection and
                        // Display-dedup. Groundness is not semantic rejection
                        // evidence, and display-equivalent alternatives can
                        // still differ evaluatively.
                        let mut seen_keys: std::collections::HashSet<Vec<u8>> =
                            std::collections::HashSet::with_capacity(flat.len());
                        let mut deduped: Vec<Self> = Vec::with_capacity(flat.len());
                        for a in flat.into_iter() {
                            let key = a.semantic_fingerprint();
                            if seen_keys.insert(key) {
                                deduped.push(a);
                            }
                        }
                        match deduped.len() {
                            1 => deduped.into_iter().next().expect("dedup retained 1"),
                            _ => Self::Ambiguous(deduped),
                        }
                    }
                }
            }

            /// Substitute environment bindings into the term.
            /// For Ambiguous terms, substitutes each alternative independently and
            /// preserves every semantically distinct result. Substitution progress
            /// is not rejection evidence: an unchanged sibling can still be a
            /// valid alternative and must survive until evaluation/rewrite evidence
            /// proves otherwise.
            pub fn substitute_env(&self, env: &#env_name) -> Self {
                match self {
                    #inner_enum_name::Ambiguous(alts) => {
                        // Substitute each alternative (including cross-category resolution)
                        let results: Vec<Self> = alts.iter().map(|alt| {
                            let substituted = match alt {
                                #(#ambiguous_substitute_arms),*,
                                #inner_enum_name::Ambiguous(_) => unreachable!("nested Ambiguous"),
                            };
                            // Apply cross-category bare variable resolution
                            let cross_resolved = (|| -> Self {
                                match &substituted {
                                    #(#ambiguous_cross_resolve_arms)*
                                    _ => {}
                                }
                                substituted.clone()
                            })();
                            cross_resolved
                        }).collect();

                        // Semantic-key dedup
                        // (NOT Display-dedup). Display equivalence is
                        // NOT observational equivalence — see
                        // from_alternatives commentary above. Substitution
                        // progress is also not observational equivalence:
                        // keeping only changed alternatives prematurely
                        // discards unchanged siblings.
                        let mut seen_keys: std::collections::HashSet<Vec<u8>> =
                            std::collections::HashSet::new();
                        let unique: Vec<Self> = results.into_iter()
                            .filter(|a| {
                                seen_keys.insert(a.semantic_fingerprint())
                            })
                            .collect();

                        Self::from_alternatives(unique)
                    }
                    _ => {
                        let substituted = match self {
                            #(#substitute_arms),*,
                            #inner_enum_name::Ambiguous(_) => unreachable!(),
                        };
                        // Cross-category: if still a variable, try resolving from other categories
                        match &substituted {
                            #(#cross_resolve_arms)*
                            _ => {}
                        }
                        substituted
                    }
                }
            }

            /// Phase D.2 (2026-05-17): grammar-agnostic helper returning all
            /// derivation alternatives at this term node.
            ///
            /// Semantics:
            /// - For `Ambiguous(Vec<Self>)`: returns the inner vec's
            ///   elements as `&Self` references (one per alt).
            /// - For any other variant: returns a single-element vec
            ///   `vec![self]`.
            ///
            /// Used by `run_ascent_typed` (Phase D.1) to seed ALL alts
            /// into the evaluator's relation pool — fulfilling the
            /// "preserve all derivations" mandate by ensuring downstream
            /// evaluation considers every alternative the parser
            /// preserved, not just `alts[0]`.
            ///
            /// `all_displays()` is the user-facing analog returning
            /// `Vec<String>`; this method preserves typed references for
            /// internal consumers that need to inspect the AST.
            pub fn all_alts(&self) -> Vec<&Self> {
                match self {
                    #inner_enum_name::Ambiguous(alts) => alts.iter().collect(),
                    _ => vec![self],
                }
            }

            /// Phase D.5 (2026-05-17): user-facing API returning the
            /// `Display` rendering of every alternative.
            ///
            /// For non-Ambiguous terms returns a single-element vec.
            /// For `Ambiguous(Vec<_>)` returns one display per alt.
            /// Diagnostic emission (the [LANG-D11] enrichment in D.8)
            /// consumes this to surface the full alt list when no
            /// evaluator combination accepted any alt.
            pub fn all_displays(&self) -> Vec<std::string::String> {
                self.all_alts()
                    .into_iter()
                    .map(|alt| format!("{}", alt))
                    .collect()
            }
        }

        impl std::fmt::Display for #inner_enum_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    #(#display_arms),*,
                    #inner_enum_name::Ambiguous(alts) => {
                        // W7 Stage 7: Display Option D — canonicalize to lex-best
                        // primary (alts[0]) and emit a [LANG-D11] diagnostic so
                        // consumers (REPL/LSP/parity tests) can detect that
                        // ambiguity disambiguation took place. See
                        // `prattail/docs/design/wpds-migration-survey.md` (M10).
                        //
                        // Phase D.8 (2026-05-17, M14.5): emit the enriched
                        // variant carrying the full alt-display list, so
                        // consumers see every alternative the parser
                        // preserved (not just the count + lex-best).
                        let alt_displays: Vec<std::string::String> =
                            alts.iter().map(|a| format!("{}", a)).collect();
                        mettail_runtime::diagnostics::emit_d11_with_alts(
                            stringify!(#inner_enum_name),
                            "",
                            &alt_displays,
                        );
                        write!(f, "{}", alts[0])
                    }
                }
            }
        }

        impl std::fmt::Debug for #inner_enum_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    #(#debug_arms),*,
                    #inner_enum_name::Ambiguous(alts) => write!(f, "Ambiguous({:?})", alts),
                }
            }
        }

        /// Wrapper for the term that implements `mettail_runtime::Term`
        #[derive(Clone)]
        pub struct #term_name(pub #inner_enum_name);

        impl mettail_runtime::Term for #term_name {
            fn clone_box(&self) -> Box<dyn mettail_runtime::Term> {
                Box::new(self.clone())
            }

            fn term_id(&self) -> u64 {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                self.0.hash(&mut hasher);
                hasher.finish()
            }

            fn term_eq(&self, other: &dyn mettail_runtime::Term) -> bool {
                if let Some(other_term) = other.as_any().downcast_ref::<#term_name>() {
                    self.0 == other_term.0
                } else {
                    false
                }
            }

            fn as_any(&self) -> &dyn std::any::Any {
                self
            }

            /// Phase F.12.A (2026-05-20): expose every single-category
            /// alternative the parser preserved so that downstream
            /// graph-traversal callers (simulation runner, REPL exec) can
            /// seed multi-source BFS from each exact semantic alternative's
            /// `term_id` instead of from the `Ambiguous` wrapper's hash (which
            /// is structurally absent from `AscentResults.all_terms` — only
            /// single-category variants are pushed there by `run_ascent_typed`).
            ///
            /// Hash recipe MUST match `language_struct.rs` TermInfo
            /// construction: DefaultHasher applied to the inner enum
            /// variant `Inner::Cat(t)` (which is exactly what `all_alts()`
            /// returns by reference — no rewrapping needed).
            ///
            /// This also mirrors `multi_cat_union_extract`'s exact semantic-key
            /// dedup. Transparent duplicates are represented once in
            /// `AscentResults.all_terms`, so the seed list must dedup the same
            /// way instead of emitting dangling seed ids for raw parser alts
            /// that were intentionally quotient-merged.
            fn rewrite_seeds(&self) -> Vec<mettail_runtime::RewriteSeed> {
                use std::collections::hash_map::DefaultHasher;
                use std::collections::HashSet;
                use std::hash::{Hash, Hasher};
                let mut seen_keys: HashSet<Vec<u8>> = HashSet::new();
                self.0
                    .all_alts()
                    .into_iter()
                    .filter_map(|alt| {
                        if !seen_keys.insert(alt.extraction_semantic_fingerprint()) {
                            return None;
                        }
                        let mut h = DefaultHasher::new();
                        alt.hash(&mut h);
                        Some(mettail_runtime::RewriteSeed::exact(
                            h.finish(),
                            alt.extraction_semantic_fingerprint(),
                            format!("{}", alt),
                        ))
                    })
                    .collect()
            }
        }

        impl std::fmt::Display for #term_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl std::fmt::Debug for #term_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", self.0)
            }
        }
    }
}

/// Generate the Language struct with helper methods
fn generate_language_struct(
    name: &syn::Ident,
    primary_type: &syn::Ident,
    _name_str: &str,
    _name_lower: &str,
    language: &LanguageDef,
) -> TokenStream {
    let language_name = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let _metadata_name = format_ident!("{}Metadata", name);
    let env_name = format_ident!("{}Env", name);

    // Primary type, lowercased (used for WFST prediction accessor names).
    let primary_lower = primary_type.to_string().to_lowercase();
    let _primary_type_str = primary_type.to_string();

    // Generate type inference helper
    let infer_fn = format_ident!("infer_term_type_typed");
    let type_inference_impl = generate_type_inference_helpers(primary_type, language, &infer_fn);

    // Generate variable collection implementation
    let collect_fn = format_ident!("collect_all_vars_impl");
    let var_collection_impl = generate_var_collection_impl(primary_type, language, &collect_fn);

    // B6: Per-category WFST accessor identifiers
    let b6_prediction_fn = format_ident!("prediction_wfst_{}", primary_lower);
    let b6_prediction_static = format_ident!("PREDICTION_{}", primary_type);

    let parse_preserving_vars_body = quote! {
        #primary_type::parse(input).map(#term_name)
    };

    quote! {
        /// Language implementation struct
        ///
        /// Auto-generated by the `language!` macro. Implements `mettail_runtime::Language`.
        pub struct #language_name;

        impl #language_name {
            /// Parse a term from a string (clears var cache for fresh evaluation)
            pub fn parse(input: &str) -> Result<#term_name, std::string::String> {
                mettail_runtime::clear_var_cache();
                Self::parse_preserving_vars(input)
            }

            /// Parse a term without clearing var cache (for environment sharing)
            pub fn parse_preserving_vars(input: &str) -> Result<#term_name, std::string::String> {
                #parse_preserving_vars_body
            }

            /// Create a new empty environment
            pub fn create_env() -> #env_name {
                #env_name::new()
            }

            // === Type Inference Helpers ===

            /// Convert InferredType to TermType
            fn inferred_to_term_type(t: &InferredType) -> mettail_runtime::TermType {
                match t {
                    InferredType::Base(cat) => mettail_runtime::TermType::Base(format!("{:?}", cat)),
                    InferredType::Arrow(d, c) => mettail_runtime::TermType::Arrow(
                        Box::new(Self::inferred_to_term_type(d)),
                        Box::new(Self::inferred_to_term_type(c)),
                    ),
                    InferredType::MultiArrow(d, c) => mettail_runtime::TermType::MultiArrow(
                        Box::new(Self::inferred_to_term_type(d)),
                        Box::new(Self::inferred_to_term_type(c)),
                    ),
                }
            }

            /// Infer the type of a term (typed version)
            pub fn infer_term_type_typed(term: &#primary_type) -> mettail_runtime::TermType {
                #type_inference_impl
            }

            /// Infer the type of a variable in a term (typed version)
            /// This finds both free and bound variables.
            pub fn infer_var_type_typed(term: &#primary_type, var_name: &str) -> Option<mettail_runtime::TermType> {
                // First try the direct method for free variables
                if let Some(t) = term.infer_var_type(var_name) {
                    return Some(Self::inferred_to_term_type(&t));
                }
                // If not found, search through all variables including bound ones
                Self::infer_var_types_typed(term)
                    .into_iter()
                    .find(|v| v.name == var_name)
                    .map(|v| v.ty)
            }

            /// Get all variable types in a term (typed version)
            /// This includes both bound variables (from lambdas) and free variables.
            pub fn infer_var_types_typed(term: &#primary_type) -> Vec<mettail_runtime::VarTypeInfo> {
                let mut result = Vec::new();
                let mut seen = std::collections::HashSet::new();
                Self::collect_all_vars_with_types(term, term, &mut result, &mut seen);
                result
            }

            /// Collect all variables (bound and free) with their types
            /// `root_term` is the original term for context, `term` is current position
            fn collect_all_vars_with_types(
                root_term: &#primary_type,
                term: &#primary_type,
                result: &mut Vec<mettail_runtime::VarTypeInfo>,
                seen: &mut std::collections::HashSet<std::string::String>,
            ) {
                Self::collect_all_vars_impl(root_term, term, result, seen);
            }

            // ── B6: Runtime WFST query accessor ──

            /// B6: Access the prediction WFST for the primary category.
            ///
            /// Returns a reference to the lazily-initialized WFST.
            /// Use for incremental parsing queries:
            /// - `valid_continuations()`: list valid next tokens (autocomplete)
            /// - `has_valid_dispatch(token)`: early error detection
            /// - `parse_progress(state)`: progress estimation
            #[allow(non_snake_case)]
            pub fn #b6_prediction_fn() -> &'static mettail_prattail::wfst::PredictionWfst {
                &*#b6_prediction_static
            }
        }

        // Variable collection implementation with proper term traversal
        #[allow(unused_variables, unreachable_patterns)]
        impl #language_name {
            fn collect_all_vars_impl(
                root_term: &#primary_type,
                term: &#primary_type,
                result: &mut Vec<mettail_runtime::VarTypeInfo>,
                seen: &mut std::collections::HashSet<std::string::String>,
            ) {
                match term {
                    #var_collection_impl
                }
            }
        }
    }
}

/// Generate the collect_all_vars_impl method with proper traversal
fn generate_var_collection_impl(
    primary_type: &Ident,
    language: &LanguageDef,
    impl_fn_name: &Ident,
) -> TokenStream {
    let categories: Vec<_> = language.types.iter().map(|t| &t.name).collect();

    // Post-HOL-B: only emit Lam{D} / MLam{D} match arms on the primary
    // type for domains D where the HOL variants actually exist (see
    // `macros/src/logic/common.rs::compute_hol_domain_pairs`).
    let hol_pairs = crate::logic::common::compute_hol_domain_pairs(language);
    let primary_str = primary_type.to_string();

    // Generate lambda handling arms
    let mut lambda_arms: Vec<TokenStream> = Vec::new();

    for domain in &categories {
        if !hol_pairs.contains(&(primary_str.clone(), domain.to_string())) {
            continue;
        }
        let domain_lit = LitStr::new(&domain.to_string(), domain.span());
        let lam_variant = format_ident!("Lam{}", domain);
        let mlam_variant = format_ident!("MLam{}", domain);

        // LamX variant - extract binder and recurse into body
        lambda_arms.push(quote! {
            #primary_type::#lam_variant(scope) => {
                // Use unbind to get the binder with proper type
                let (binder, body) = scope.clone().unbind();
                if let Some(name) = &binder.0.pretty_name {
                    if !seen.contains(name) {
                        seen.insert(name.clone());
                        // Infer the binder's type from how it's used in the body
                        let var_type = body.infer_var_type(name)
                            .map(|t| Self::inferred_to_term_type(&t))
                            .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()));
                        result.push(mettail_runtime::VarTypeInfo {
                            name: name.clone(),
                            ty: var_type,
                        });
                    }
                }
                // Recurse into body (body is Box<T>, so deref it)
                Self::#impl_fn_name(root_term, body.as_ref(), result, seen);
            }
        });

        // MLamX variant - extract all binders and recurse into body
        lambda_arms.push(quote! {
            #primary_type::#mlam_variant(scope) => {
                // Use unbind to get binders and body with proper types
                let (binders, body) = scope.clone().unbind();
                for binder in &binders {
                    if let Some(name) = &binder.0.pretty_name {
                        if !seen.contains(name) {
                            seen.insert(name.clone());
                            // Infer the binder's type from how it's used in the body
                            let var_type = body.infer_var_type(name)
                                .map(|t| Self::inferred_to_term_type(&t))
                                .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()));
                            result.push(mettail_runtime::VarTypeInfo {
                                name: name.clone(),
                                ty: var_type,
                            });
                        }
                    }
                }
                // Recurse into body (body is Box<T>, so deref it)
                Self::#impl_fn_name(root_term, body.as_ref(), result, seen);
            }
        });

        // ApplyX variant - only recurse into lam (which has type Proc)
        // The arg has the domain type, not the primary type
        let apply_variant = format_ident!("Apply{}", domain);
        lambda_arms.push(quote! {
            #primary_type::#apply_variant(lam, _arg) => {
                Self::#impl_fn_name(root_term, lam.as_ref(), result, seen);
                // Note: _arg is of type #domain, not #primary_type, so we can't recurse on it here
            }
        });

        // MApplyX variant - only recurse into lam
        let mapply_variant = format_ident!("MApply{}", domain);
        lambda_arms.push(quote! {
            #primary_type::#mapply_variant(lam, _args) => {
                Self::#impl_fn_name(root_term, lam.as_ref(), result, seen);
                // Note: _args contains #domain values, not #primary_type, so we can't recurse on them here
            }
        });
    }

    // Generate arms for constructor variants from grammar
    let mut constructor_arms: Vec<TokenStream> = Vec::new();

    for rule in &language.terms {
        if rule.category != *primary_type {
            continue;
        }

        let label = &rule.label;

        // Skip if handled above (lambdas, applies)
        let label_str = label.to_string();
        if label_str.starts_with("Lam")
            || label_str.starts_with("MLam")
            || label_str.starts_with("Apply")
            || label_str.starts_with("MApply")
            || label_str.ends_with("Var")
        {
            continue;
        }

        // Use term_context if available for accurate field count.
        // Each TermParam becomes one field (abstractions become Scope fields).
        // Opt-Group: an Optional contributes `inner.len()` fields (each
        // wrapped as `Option<...>`), not 1 — flatten recursively.
        fn flat_field_count(params: &[mettail_ast::grammar::TermParam]) -> usize {
            use mettail_ast::grammar::TermParam;
            params
                .iter()
                .map(|p| match p {
                    TermParam::Optional { params: inner } => flat_field_count(inner),
                    _ => 1,
                })
                .sum()
        }
        let field_count = if let Some(ctx) = &rule.term_context {
            flat_field_count(ctx)
        } else {
            // Old syntax - count non-terminals but combine binder+body pairs
            let mut count = 0;
            let mut skip_next = false;
            for item in &rule.items {
                if skip_next {
                    skip_next = false;
                    continue;
                }
                match item {
                    GrammarItem::NonTerminal { .. } | GrammarItem::Collection { .. } => count += 1,
                    GrammarItem::Binder { .. } => {
                        // Binder + next NonTerminal = one Scope field
                        count += 1;
                        skip_next = true;
                    },
                    GrammarItem::Terminal(_) => {},
                }
            }
            count
        };

        if field_count == 0 {
            // Unit variant
            constructor_arms.push(quote! {
                #primary_type::#label => {}
            });
        } else {
            // Generate field patterns and recursion
            let field_names: Vec<_> = (0..field_count).map(|i| format_ident!("f{}", i)).collect();

            let field_patterns: Vec<TokenStream> =
                field_names.iter().map(|n| quote! { ref #n }).collect();

            // Generate recursion for each field based on type from term_context
            let mut recurse_calls: Vec<TokenStream> = Vec::new();

            if let Some(ctx) = &rule.term_context {
                use mettail_ast::grammar::TermParam;
                use mettail_ast::types::TypeExpr;

                // Opt-Group: emit recursion calls for a flat parallel-array
                // view of the term context. Each TermParam is consumed in
                // order (advancing field_idx by 1 for non-Optional params).
                // Optional descends into inner params with `optional_wrap=true`,
                // which gates each recursion in `if let Some(__v) = #field { ... }`.
                fn emit_recursion(
                    params: &[TermParam],
                    field_names: &[syn::Ident],
                    field_idx: &mut usize,
                    optional_wrap: bool,
                    primary_type: &syn::Ident,
                    impl_fn_name: &syn::Ident,
                    recurse_calls: &mut Vec<TokenStream>,
                ) {
                    for param in params {
                        match param {
                            TermParam::Simple { ty, .. } => {
                                let field_name = &field_names[*field_idx];
                                *field_idx += 1;
                                let inner_body: Option<TokenStream> = match ty {
                                    TypeExpr::Base(ident)
                                        if ident.to_string() == primary_type.to_string() =>
                                    {
                                        Some(quote! {
                                            Self::#impl_fn_name(root_term, __v.as_ref(), result, seen);
                                        })
                                    },
                                    TypeExpr::Collection { coll_type, element } => {
                                        if let TypeExpr::Base(id) = element.as_ref() {
                                            if id.to_string() == primary_type.to_string() {
                                                // B9 / Class 2 (2026-05-08):
                                                // branch on coll_type. Vec
                                                // yields bare elements;
                                                // HashBag/HashSet yield
                                                // (elem, count) tuples.
                                                Some(match coll_type {
                                                    mettail_ast::types::CollectionType::Vec => {
                                                        quote! {
                                                            for elem in __v.iter() {
                                                                Self::#impl_fn_name(root_term, elem, result, seen);
                                                            }
                                                        }
                                                    },
                                                    _ => quote! {
                                                        for (elem, _) in __v.iter() {
                                                            Self::#impl_fn_name(root_term, elem, result, seen);
                                                        }
                                                    },
                                                })
                                            } else {
                                                None
                                            }
                                        } else {
                                            None
                                        }
                                    },
                                    _ => None,
                                };
                                if let Some(body) = inner_body {
                                    if optional_wrap {
                                        recurse_calls.push(quote! {
                                            if let Some(__v) = #field_name.as_ref() {
                                                #body
                                            }
                                        });
                                    } else {
                                        recurse_calls.push(quote! {
                                            { let __v = #field_name; #body }
                                        });
                                    }
                                }
                            },
                            TermParam::Abstraction { ty, .. } => {
                                let field_name = &field_names[*field_idx];
                                *field_idx += 1;
                                if let TypeExpr::Arrow { codomain, .. } = ty {
                                    if let TypeExpr::Base(ident) = codomain.as_ref() {
                                        if ident.to_string() == primary_type.to_string() {
                                            let domain_str =
                                                if let TypeExpr::Arrow { domain, .. } = ty {
                                                    if let TypeExpr::Base(d) = domain.as_ref() {
                                                        d.to_string()
                                                    } else {
                                                        "Name".to_string()
                                                    }
                                                } else {
                                                    "Name".to_string()
                                                };
                                            let domain_lit =
                                                LitStr::new(&domain_str, Span::call_site());
                                            let body_block = quote! {
                                                let (binder, body) = __scope.clone().unbind();
                                                if let Some(name) = &binder.0.pretty_name {
                                                    if !seen.contains(name) {
                                                        seen.insert(name.clone());
                                                        let var_type = body.infer_var_type(name)
                                                            .map(|t| Self::inferred_to_term_type(&t))
                                                            .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()));
                                                        result.push(mettail_runtime::VarTypeInfo {
                                                            name: name.clone(),
                                                            ty: var_type,
                                                        });
                                                    }
                                                }
                                                Self::#impl_fn_name(root_term, body.as_ref(), result, seen);
                                            };
                                            if optional_wrap {
                                                recurse_calls.push(quote! {
                                                    if let Some(__scope) = #field_name.as_ref() {
                                                        #body_block
                                                    }
                                                });
                                            } else {
                                                recurse_calls.push(quote! {
                                                    { let __scope = #field_name; #body_block }
                                                });
                                            }
                                        }
                                    }
                                }
                            },
                            TermParam::MultiAbstraction { ty, .. } => {
                                let field_name = &field_names[*field_idx];
                                *field_idx += 1;
                                if let TypeExpr::Arrow { codomain, .. } = ty {
                                    if let TypeExpr::Base(ident) = codomain.as_ref() {
                                        if ident.to_string() == primary_type.to_string() {
                                            let domain_str =
                                                if let TypeExpr::Arrow { domain, .. } = ty {
                                                    if let TypeExpr::MultiBinder(inner) =
                                                        domain.as_ref()
                                                    {
                                                        if let TypeExpr::Base(d) = inner.as_ref() {
                                                            d.to_string()
                                                        } else {
                                                            "Name".to_string()
                                                        }
                                                    } else {
                                                        "Name".to_string()
                                                    }
                                                } else {
                                                    "Name".to_string()
                                                };
                                            let domain_lit =
                                                LitStr::new(&domain_str, Span::call_site());
                                            let body_block = quote! {
                                                let (binders, body) = __scope.clone().unbind();
                                                for binder in &binders {
                                                    if let Some(name) = &binder.0.pretty_name {
                                                        if !seen.contains(name) {
                                                            seen.insert(name.clone());
                                                            let var_type = body.infer_var_type(name)
                                                                .map(|t| Self::inferred_to_term_type(&t))
                                                                .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()));
                                                            result.push(mettail_runtime::VarTypeInfo {
                                                                name: name.clone(),
                                                                ty: var_type,
                                                            });
                                                        }
                                                    }
                                                }
                                                Self::#impl_fn_name(root_term, body.as_ref(), result, seen);
                                            };
                                            if optional_wrap {
                                                recurse_calls.push(quote! {
                                                    if let Some(__scope) = #field_name.as_ref() {
                                                        #body_block
                                                    }
                                                });
                                            } else {
                                                recurse_calls.push(quote! {
                                                    { let __scope = #field_name; #body_block }
                                                });
                                            }
                                        }
                                    }
                                }
                            },
                            TermParam::GuardBody { .. } => {
                                *field_idx += 1;
                                // Guard bodies are passive runtime data; no
                                // recursion needed for VarTypeInfo collection.
                            },
                            TermParam::Optional { params: inner } => {
                                emit_recursion(
                                    inner,
                                    field_names,
                                    field_idx,
                                    true, // wrap inner recursions in `if let Some(...)`
                                    primary_type,
                                    impl_fn_name,
                                    recurse_calls,
                                );
                            },
                        }
                    }
                }

                let mut idx = 0usize;
                emit_recursion(
                    ctx,
                    &field_names,
                    &mut idx,
                    false,
                    primary_type,
                    &impl_fn_name,
                    &mut recurse_calls,
                );
            } else {
                // Old-style syntax - iterate through items directly
                // For old syntax, fields are paired: Binder + NonTerminal = one Scope field
                let mut field_idx = 0;
                let mut item_idx = 0;
                while item_idx < rule.items.len() {
                    let item = &rule.items[item_idx];
                    match item {
                        GrammarItem::NonTerminal { ident: nt, .. } => {
                            let field_name = &field_names[field_idx];
                            let nt_str = nt.to_string();
                            // Only recurse if it's the primary type
                            if nt_str == primary_type.to_string() {
                                recurse_calls.push(quote! {
                                    Self::#impl_fn_name(root_term, #field_name.as_ref(), result, seen);
                                });
                            }
                            field_idx += 1;
                            item_idx += 1;
                        },
                        GrammarItem::Collection { element_type, coll_type, .. } => {
                            let field_name = &field_names[field_idx];
                            let elem_str = element_type.to_string();
                            if elem_str == primary_type.to_string() {
                                // B9 / Class 2 (2026-05-08): branch on
                                // coll_type. Vec yields bare elements;
                                // HashBag/HashSet yield (elem, count).
                                let iter_body = match coll_type {
                                    mettail_ast::types::CollectionType::Vec => quote! {
                                        for elem in #field_name.iter() {
                                            Self::#impl_fn_name(root_term, elem, result, seen);
                                        }
                                    },
                                    _ => quote! {
                                        for (elem, _) in #field_name.iter() {
                                            Self::#impl_fn_name(root_term, elem, result, seen);
                                        }
                                    },
                                };
                                recurse_calls.push(iter_body);
                            }
                            field_idx += 1;
                            item_idx += 1;
                        },
                        GrammarItem::Binder { category } => {
                            // Binder + next NonTerminal = one Scope field
                            let field_name = &field_names[field_idx];
                            let domain_lit = LitStr::new(&category.to_string(), category.span());

                            // Skip to the body item
                            item_idx += 1;
                            if item_idx < rule.items.len() {
                                if let GrammarItem::NonTerminal { ident: body_type, .. } =
                                    &rule.items[item_idx]
                                {
                                    let body_str = body_type.to_string();
                                    if body_str == primary_type.to_string() {
                                        recurse_calls.push(quote! {
                                            // Extract binder from scope using unbind
                                            let (binder, body) = #field_name.clone().unbind();
                                            if let Some(name) = &binder.0.pretty_name {
                                                if !seen.contains(name) {
                                                    seen.insert(name.clone());
                                                    let var_type = body.infer_var_type(name)
                                                        .map(|t| Self::inferred_to_term_type(&t))
                                                        .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()));
                                                    result.push(mettail_runtime::VarTypeInfo {
                                                        name: name.clone(),
                                                        ty: var_type,
                                                    });
                                                }
                                            }
                                            Self::#impl_fn_name(root_term, body.as_ref(), result, seen);
                                        });
                                    }
                                }
                            }
                            field_idx += 1;
                            item_idx += 1;
                        },
                        GrammarItem::Terminal(_) => {
                            item_idx += 1;
                        },
                    }
                }
            }

            if recurse_calls.is_empty() {
                constructor_arms.push(quote! {
                    #primary_type::#label(#(#field_patterns),*) => {}
                });
            } else {
                constructor_arms.push(quote! {
                    #primary_type::#label(#(#field_patterns),*) => {
                        #(#recurse_calls)*
                    }
                });
            }
        }
    }

    // Variable handling for free variables (e.g., PVar for Proc, NVar for Name, TVar for Term)
    let var_label = generate_var_label(primary_type);
    let primary_type_lit = LitStr::new(&primary_type.to_string(), primary_type.span());

    quote! {
        #primary_type::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv))) => {
            if let Some(name) = &fv.pretty_name {
                if !seen.contains(name) {
                    seen.insert(name.clone());
                    // Try to infer type from usage in root term
                    let var_type = root_term.infer_var_type(name)
                        .map(|t| Self::inferred_to_term_type(&t))
                        .unwrap_or_else(|| mettail_runtime::TermType::Base(#primary_type_lit.to_string()));
                    result.push(mettail_runtime::VarTypeInfo {
                        name: name.clone(),
                        ty: var_type,
                    });
                }
            }
        }
        #primary_type::#var_label(_) => {}
        #(#lambda_arms)*
        #(#constructor_arms)*
        _ => {}
    }
}

/// Generate the Language struct when the language has multiple types (multi-category parse and run).
fn generate_language_struct_multi(
    name: &syn::Ident,
    _name_str: &str,
    _name_lower: &str,
    language: &LanguageDef,
) -> TokenStream {
    let language_name = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let inner_enum_name = format_ident!("{}TermInner", name);
    let env_name = format_ident!("{}Env", name);

    // NFA-style multi-category parse: try ALL category parsers and collect successes.
    // Parse order follows declaration order so that Ambiguous alternatives are ordered
    // by the user's declared priority (first-declared category = first alternative).
    let parse_order: Vec<syn::Ident> = language.types.iter().map(|t| t.name.clone()).collect();

    // Lexer-guided parse filtering: when the language has at least one non-native category
    // (e.g. Proc, Name), skip native-only categories (e.g. Float, Int, Bool, Str) when the
    // first token is an identifier, since identifiers are not native literals.
    // For all-native languages (e.g. Calculator), no filtering is needed.
    let has_non_native = language.types.iter().any(|t| t.native_type.is_none());
    let native_cat_names: std::collections::HashSet<String> = language
        .types
        .iter()
        .filter(|t| t.native_type.is_some())
        .map(|t| t.name.to_string())
        .collect();

    // Categories whose first-syntax-item is a foreign non-terminal may have FIRST
    // sets that include Ident (via the foreign category's own FIRST). Preserve
    // these from the Ident-skip optimization so that e.g. `x == 1` can be parsed
    // as Bool via its cross-cat dispatch (EqInt / Eq etc.).
    let cats_with_foreign_nt_first: std::collections::HashSet<String> = {
        use mettail_ast::grammar::{GrammarItem, SyntaxExpr, TermParam};
        use mettail_ast::types::TypeExpr;
        let mut set = std::collections::HashSet::new();
        for rule in &language.terms {
            let cat_name = rule.category.to_string();
            // New-style rules: syntax_pattern + term_context.
            if let Some(pat) = &rule.syntax_pattern {
                if let Some(SyntaxExpr::Param(ident)) = pat.first() {
                    if let Some(term_ctx) = &rule.term_context {
                        let ty = term_ctx.iter().find_map(|tp| match tp {
                            TermParam::Simple { name, ty } if name == ident => Some(ty),
                            TermParam::Abstraction { body, ty, .. } if body == ident => Some(ty),
                            TermParam::MultiAbstraction { body, ty, .. } if body == ident => {
                                Some(ty)
                            },
                            _ => None,
                        });
                        if let Some(TypeExpr::Base(type_ident)) = ty {
                            if type_ident != &rule.category {
                                set.insert(cat_name.clone());
                            }
                        }
                    }
                }
            } else if let Some(GrammarItem::NonTerminal { ident, .. }) = rule.items.first() {
                // Old-style rules: direct GrammarItem::NonTerminal check.
                if ident != &rule.category {
                    set.insert(cat_name.clone());
                }
            }
        }
        // Tension 3 (P3-C): every native-type category gets an auto-generated
        // Var variant (e.g., Int::IVar, Float::FVar, Bool::BVar, ...) whose
        // parser prefix arm accepts `Token::Ident`. Such categories MUST be
        // tried even when the top-level first token is Ident — otherwise
        // bare `a + b` fails to parse across ambiguous numeric types.
        for t in &language.types {
            if t.native_type.is_some() {
                set.insert(t.name.to_string());
            }
        }
        set
    };
    let uses_first_tok_filter = has_non_native
        && parse_order.iter().any(|cat| {
            let cat_name = cat.to_string();
            native_cat_names.contains(&cat_name) && !cats_with_foreign_nt_first.contains(&cat_name)
        });

    let parse_tries: Vec<TokenStream> = parse_order
        .iter()
        .map(|cat| {
            let variant = format_ident!("{}", cat);
            // Stage 10b (2026-05-03): NFA spillover infrastructure excised.
            //
            // Pre-Stage-10b emitted per-cat thread-local references
            // (`NFA_PREFIX_SPILL_<CAT>`, `NFA_FORCED_PREFIX_<CAT>`,
            // `NFA_PRIMARY_WEIGHT_<CAT>`) plus an F3 lazy-spillover replay
            // loop. Under WPDS-only operation (post-Stage-3.12 atomic
            // swap), `Cat::parse → parse_<Cat>_via_wpda → walker` —
            // never reaches the trampoline NFA emitter that populates
            // `NFA_PREFIX_SPILL_<CAT>`. The replay loop iterated an
            // always-empty Vec, dead code that only added cognitive
            // load and a maintenance hazard.
            //
            // Stage 10c/d/e excise the trampoline-side NFA emitter and
            // related dead surfaces; T11 (2026-05-05) renames
            // `DispatchStrategy::NfaTryAll` → `AmbiguousFanout` (variant
            // is preserved because static-analysis lints still consume
            // the enumerated rule-label fanout set for diagnostics).
            //
            // M8b (2026-05-14): use parse_via_wpda_all so within-cat
            // multi-result is surfaced into `successes`. The cross-cat
            // flatten below (match-on-len at lines 2718-2727) then
            // folds within-cat AND cross-cat ambiguity uniformly into
            // `Ambiguous(Vec<Inner>)`.
            let try_block = quote! {
                match #cat::parse_via_wpda_all(input) {
                    Ok(terms) => {
                        for t in terms {
                            successes.push(#inner_enum_name::#variant(t));
                        }
                    },
                    Err(e) => {
                        if first_err.is_none() { first_err = Some(e.to_string()); }
                    },
                }
            };
            // Guard native categories behind an Ident check when non-native categories exist.
            // EXCEPT: if the category has any rule whose first syntax item is a foreign
            // non-terminal, its FIRST set may include Ident (via the foreign cat's own FIRST
            // or cross-cat dispatch), so it must be tried even when first_tok is Ident.
            // Example: `x == 1` must parse as Bool via EqInt (Int == Int → Bool).
            let cat_name = cat.to_string();
            if uses_first_tok_filter
                && native_cat_names.contains(&cat_name)
                && !cats_with_foreign_nt_first.contains(&cat_name)
            {
                quote! {
                    if !matches!(first_tok, Some(Token::Ident(_))) {
                        #try_block
                    }
                }
            } else {
                try_block
            }
        })
        .collect();

    let weighted_parse_tries: Vec<TokenStream> = parse_order
        .iter()
        .map(|cat| {
            let variant = format_ident!("{}", cat);
            let try_block = quote! {
                match #cat::parse_via_wpda_all_with_weights(input) {
                    Ok((terms, weights)) => {
                        if terms.len() != weights.len() {
                            if first_err.is_none() {
                                first_err = Some(format!(
                                    "{} parser returned {} terms but {} weights",
                                    stringify!(#cat),
                                    terms.len(),
                                    weights.len(),
                                ));
                            }
                        } else {
                            for (t, weight) in terms.into_iter().zip(weights.into_iter()) {
                                successes.push((
                                    #inner_enum_name::#variant(t),
                                    weight.primary.value(),
                                ));
                            }
                        }
                    },
                    Err(e) => {
                        if first_err.is_none() { first_err = Some(e.to_string()); }
                    },
                }
            };
            let cat_name = cat.to_string();
            if uses_first_tok_filter
                && native_cat_names.contains(&cat_name)
                && !cats_with_foreign_nt_first.contains(&cat_name)
            {
                quote! {
                    if !matches!(first_tok, Some(Token::Ident(_))) {
                        #try_block
                    }
                }
            } else {
                try_block
            }
        })
        .collect();

    // Lexer probe: only emitted for languages with non-native categories.
    // All-native languages (e.g. Calculator) skip this and try all parsers unconditionally.
    let lexer_probe: TokenStream = if uses_first_tok_filter {
        quote! {
            // Lex once to classify the first token for parse dispatch
            let probe_tokens = lex(input).map_err(|e| e.to_string())?;
            let first_tok = probe_tokens.first().map(|(t, _)| t);
        }
    } else {
        quote! {}
    };

    // Per-category type inference functions
    let per_cat_type_infer_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let fn_name = format_ident!("infer_{}_type", cat.to_string().to_lowercase());
            let type_impl = generate_type_inference_helpers(cat, language, &fn_name);
            quote! {
                pub fn #fn_name(term: &#cat) -> mettail_runtime::TermType {
                    #type_impl
                }
            }
        })
        .collect();

    // B6: Per-category WFST query accessors for incremental parsing.
    // Generates `prediction_wfst_<cat>()` methods that return a reference to the
    // per-category PREDICTION_Cat static, enabling runtime queries for autocomplete,
    // early error detection, and progress estimation.
    let per_cat_wfst_accessors: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let fn_name = format_ident!("prediction_wfst_{}", cat.to_string().to_lowercase());
            let prediction_name = format_ident!("PREDICTION_{}", cat);
            quote! {
                /// B6: Access the prediction WFST for this category.
                ///
                /// Returns a reference to the lazily-initialized per-category WFST.
                /// Use for incremental parsing queries:
                /// - `valid_continuations()`: list valid next tokens (autocomplete)
                /// - `has_valid_dispatch(token)`: early error detection
                /// - `parse_progress(state)`: progress estimation
                pub fn #fn_name() -> &'static mettail_prattail::wfst::PredictionWfst {
                    &*#prediction_name
                }
            }
        })
        .collect();

    // Per-category variable collection functions
    let per_cat_var_collect_fns: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let fn_name = format_ident!("collect_all_{}_vars", cat.to_string().to_lowercase());
            let var_impl = generate_var_collection_impl(cat, language, &fn_name);
            quote! {
                fn #fn_name(
                    root_term: &#cat,
                    term: &#cat,
                    result: &mut Vec<mettail_runtime::VarTypeInfo>,
                    seen: &mut std::collections::HashSet<std::string::String>,
                ) {
                    match term {
                        #var_impl
                    }
                }
            }
        })
        .collect();

    quote! {
        /// Language implementation struct (multi-category: one parser/relation per type).
        pub struct #language_name;

        impl #language_name {
            /// Parse a term from a string (clears var cache). Tries all category parsers.
            pub fn parse(input: &str) -> Result<#term_name, std::string::String> {
                mettail_runtime::clear_var_cache();
                Self::parse_preserving_vars(input)
            }

            /// Parse without clearing var cache. Tries ALL category parsers (NFA-style).
            /// If exactly 1 succeeds → unambiguous. If N succeed → `Ambiguous(Vec<Inner>)`.
            /// Reports the first parser's error when all fail.
            ///
            /// When the language has non-native categories (e.g. Proc, Name), a lexer probe
            /// classifies the first token: if it's an `Ident`, native-only categories (Float,
            /// Int, Bool, Str) are skipped since identifiers are not native literals. This
            /// reduces 6-way ambiguity to 2-way for bare variables in languages like rhocalc.
            pub fn parse_preserving_vars(input: &str) -> Result<#term_name, std::string::String> {
                #lexer_probe

                let mut successes = Vec::new();
                let mut first_err = None;
                #(#parse_tries)*
                // Stage 3.12.8 M2 (2026-05-03): post-parse spurious cross-cat
                // alternative filter. Drop alternatives whose AST is uniformly
                // auto-injected (auto-inj wrappers + no same-cat native literal)
                // ONLY when at least one non-uniformly-auto-injected alternative
                // exists. This preserves single-alt parses that legitimately
                // use auto-injected wrappers (e.g., optsmoke's user-input
                // `Int::IfElse(BoolLit, BoolToInt(BoolLit), None)` which is the
                // ONLY Int parse, even though BoolToInt is auto-injected). For
                // multi-alt parses like `(1.0+2.0)/3.0` (Float + spurious BigRat),
                // drop the BigRat alt because Float alt is non-spurious.
                if successes.len() > 1 {
                    let any_non_spurious = successes.iter()
                        .any(|s| !s.is_uniformly_auto_injected());
                    if any_non_spurious {
                        let mut filtered = Vec::with_capacity(successes.len());
                        for s in successes.into_iter() {
                            if !s.is_uniformly_auto_injected() {
                                filtered.push(s);
                            }
                        }
                        successes = filtered;
                    }
                }
                // Phase F.13 Stage 2.2 (2026-05-22): semantic-key dedup.
                // The WPDS parser can produce structurally-distinct
                // alternatives that are observationally equivalent (for
                // example, transparent auto-injection wrappers reached through
                // different lex paths). Feeding those duplicates into Ascent
                // caused exponential fixpoint blowup. Collapse only by
                // exact semantic key: Display equivalence, WFST weight, and
                // groundness are not valid parse-time rejection evidence.
                // `-3!` produces both
                // CalculatorTermInner::Int(Fact(NumLit(-3))) (evals
                // "error") and CalculatorTermInner::Int(Neg(Fact(NumLit(3))))
                // (evals "-6") — both display "-3!" but their ASTs
                // key differently and BOTH must reach Ascent.
                if successes.len() > 1 {
                    let mut seen_keys: std::collections::HashSet<Vec<u8>> =
                        std::collections::HashSet::with_capacity(successes.len());
                    let mut deduped: Vec<_> = Vec::with_capacity(successes.len());
                    for s in successes.into_iter() {
                        let key = s.semantic_fingerprint();
                        if seen_keys.insert(key) {
                            deduped.push(s);
                        }
                    }
                    successes = deduped;
                }
                match successes.len() {
                    0 => Err(first_err.unwrap_or_else(|| "Parse error".to_string())),
                    1 => Ok(#term_name(successes.into_iter().next().expect("checked len == 1"))),
                    _ => Ok(#term_name(#inner_enum_name::from_alternatives(successes)))
                }
            }

            /// Parse without clearing var cache and retain WPDA parse/evidence
            /// weights plus exact semantic keys for lazy weighted evaluation.
            ///
            /// The returned seeds use the same extraction-semantic quotient
            /// as `Term::rewrite_seeds`, so callers can feed them directly
            /// to `AscentResults::normal_forms_reachable_from_weighted_rewrite_seeds_iter`
            /// without introducing dangling or lossy seed ids.
            pub fn parse_preserving_vars_with_weighted_rewrite_seeds(
                input: &str,
            ) -> Result<(#term_name, Vec<mettail_runtime::WeightedRewriteSeed>), std::string::String> {
                #lexer_probe

                let mut successes: Vec<(#inner_enum_name, f64)> = Vec::new();
                let mut first_err = None;
                #(#weighted_parse_tries)*
                if successes.len() > 1 {
                    let any_non_spurious = successes.iter()
                        .any(|(s, _)| !s.is_uniformly_auto_injected());
                    if any_non_spurious {
                        let mut filtered = Vec::with_capacity(successes.len());
                        for (s, weight) in successes.into_iter() {
                            if !s.is_uniformly_auto_injected() {
                                filtered.push((s, weight));
                            }
                        }
                        successes = filtered;
                    }
                }
                if successes.len() > 1 {
                    let mut index_by_key: std::collections::HashMap<Vec<u8>, usize> =
                        std::collections::HashMap::with_capacity(successes.len());
                    let mut deduped: Vec<(#inner_enum_name, f64)> =
                        Vec::with_capacity(successes.len());
                    for (s, weight) in successes.into_iter() {
                        let key = s.semantic_fingerprint();
                        if let Some(&idx) = index_by_key.get(&key) {
                            if weight.total_cmp(&deduped[idx].1) == std::cmp::Ordering::Less {
                                deduped[idx] = (s, weight);
                            }
                        } else {
                            index_by_key.insert(key, deduped.len());
                            deduped.push((s, weight));
                        }
                    }
                    successes = deduped;
                }
                if successes.is_empty() {
                    return Err(first_err.unwrap_or_else(|| "Parse error".to_string()));
                }

                let mut weight_by_seed_key: std::collections::HashMap<Vec<u8>, f64> =
                    std::collections::HashMap::with_capacity(successes.len());
                for (alt, weight) in successes.iter() {
                    let key = alt.extraction_semantic_fingerprint();
                    match weight_by_seed_key.get_mut(&key) {
                        Some(best) => {
                            if weight.total_cmp(best) == std::cmp::Ordering::Less {
                                *best = *weight;
                            }
                        }
                        None => {
                            weight_by_seed_key.insert(key, *weight);
                        }
                    }
                }

                let term = match successes.len() {
                    1 => #term_name(successes.into_iter().next().expect("checked non-empty").0),
                    _ => #term_name(#inner_enum_name::from_alternatives(
                        successes.into_iter().map(|(s, _)| s).collect()
                    )),
                };

                let mut seen_seed_keys: std::collections::HashSet<Vec<u8>> =
                    std::collections::HashSet::with_capacity(weight_by_seed_key.len());
                let mut weighted_seeds: Vec<mettail_runtime::WeightedRewriteSeed> =
                    Vec::with_capacity(weight_by_seed_key.len());
                for alt in term.0.all_alts() {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};

                    let key = alt.extraction_semantic_fingerprint();
                    if !seen_seed_keys.insert(key.clone()) {
                        continue;
                    }
                    let weight = *weight_by_seed_key
                        .get(&key)
                        .expect("weighted parse seed key should come from a retained alternative");
                    let mut h = DefaultHasher::new();
                    alt.hash(&mut h);
                    weighted_seeds.push(mettail_runtime::WeightedRewriteSeed::exact(
                        h.finish(),
                        key,
                        format!("{}", alt),
                        weight,
                    ));
                }
                Ok((term, weighted_seeds))
            }

            /// Compatibility wrapper for callers that still expect tuple seed ids.
            pub fn parse_preserving_vars_with_weighted_seed_ids(
                input: &str,
            ) -> Result<(#term_name, Vec<mettail_runtime::WeightedSeedId>), std::string::String> {
                let (term, seeds) = Self::parse_preserving_vars_with_weighted_rewrite_seeds(input)?;
                Ok((
                    term,
                    seeds
                        .into_iter()
                        .map(|seed| (seed.term_id, seed.display, seed.weight))
                        .collect(),
                ))
            }

            /// Drain accumulated weight corrections from semantic disambiguation.
            ///
            /// Parse assembly no longer chooses one semantically distinct
            /// alternative by WFST weight or groundness, so it records no
            /// correction events. The method is kept as a stable API surface
            /// for callers that already drain after parse.
            pub fn drain_weight_corrections() -> Vec<mettail_prattail::wfst::WeightCorrection> {
                Vec::new()
            }

            /// Create a new empty environment
            pub fn create_env() -> #env_name {
                #env_name::new()
            }

            // === Type Inference Helpers (per-category) ===

            fn inferred_to_term_type(t: &InferredType) -> mettail_runtime::TermType {
                match t {
                    InferredType::Base(cat) => mettail_runtime::TermType::Base(format!("{:?}", cat)),
                    InferredType::Arrow(d, c) => mettail_runtime::TermType::Arrow(
                        Box::new(Self::inferred_to_term_type(d)),
                        Box::new(Self::inferred_to_term_type(c)),
                    ),
                    InferredType::MultiArrow(d, c) => mettail_runtime::TermType::MultiArrow(
                        Box::new(Self::inferred_to_term_type(d)),
                        Box::new(Self::inferred_to_term_type(c)),
                    ),
                }
            }

            #(#per_cat_type_infer_fns)*

            // ── B6: Runtime WFST query accessors ──

            #(#per_cat_wfst_accessors)*
        }

        // Variable collection implementation with proper term traversal (per-category)
        #[allow(unused_variables, unreachable_patterns)]
        impl #language_name {
            #(#per_cat_var_collect_fns)*
        }
    }
}

/// Generate the Language trait implementation
fn generate_language_trait_impl(
    name: &syn::Ident,
    primary_type: &syn::Ident,
    name_str: &str,
    _name_lower: &str,
    language: &LanguageDef,
) -> TokenStream {
    let language_name = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let metadata_name = format_ident!("{}Metadata", name);
    let env_name = format_ident!("{}Env", name);

    // Use a string literal for fn name() to avoid moving String (quote! #name_str can expand to a move)
    let name_lit = LitStr::new(name_str, name.span());

    // All categories for environment field access (include native so e.g. Calculator can list/remove Int bindings)
    let categories: Vec<_> = language.types.iter().map(|t| &t.name).collect();

    // Generate field name for primary type (lowercase)
    let primary_field = format_ident!("{}", primary_type.to_string().to_lowercase());

    // Generate remove_from_env checks for all type fields
    let remove_checks: Vec<TokenStream> = categories
        .iter()
        .map(|cat| {
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            quote! { typed_env.#field.remove(name).is_some() }
        })
        .collect();

    // Generate list_env iterations for all type fields
    let list_iterations: Vec<TokenStream> = categories
        .iter()
        .map(|cat| {
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            quote! {
                for (name, val) in typed_env.#field.iter() {
                    let comment = typed_env.comments.get(name).cloned();
                    result.push((name.clone(), format!("{}", val), comment));
                }
            }
        })
        .collect();

    // try_direct_eval: only for single-type languages whose primary type has native_type
    let primary_lang_type = language.types.first().expect("at least one type");
    let try_direct_eval_method: TokenStream = if let Some(ref native_type) =
        primary_lang_type.native_type
    {
        let literal_label = generate_literal_label(native_type);
        quote! {
            fn try_direct_eval(&self, term: &dyn mettail_runtime::Term) -> Option<Box<dyn mettail_runtime::Term>> {
                let typed_term = term.as_any().downcast_ref::<#term_name>()?;
                let v = typed_term.0.try_eval()?;
                Some(Box::new(#term_name(#primary_type::#literal_label(v))))
            }
        }
    } else {
        quote! {}
    };

    quote! {
        impl mettail_runtime::Language for #language_name {
            fn name(&self) -> &'static str {
                #name_lit
            }

            fn metadata(&self) -> &'static dyn mettail_runtime::LanguageMetadata {
                &#metadata_name
            }

            fn parse_term(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                #language_name::parse(input)
                    .map(|t| Box::new(t) as Box<dyn mettail_runtime::Term>)
            }

            fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                #language_name::parse_preserving_vars(input)
                    .map(|t| Box::new(t) as Box<dyn mettail_runtime::Term>)
            }

            #try_direct_eval_method

            fn normalize_term(&self, term: &dyn mettail_runtime::Term) -> Box<dyn mettail_runtime::Term> {
                if let Some(typed) = term.as_any().downcast_ref::<#term_name>() {
                    Box::new(#term_name(typed.0.normalize()))
                } else {
                    term.clone_box()
                }
            }

            fn create_env(&self) -> Box<dyn std::any::Any + Send + Sync> {
                Box::new(#language_name::create_env())
            }

            fn add_to_env(&self, env: &mut dyn std::any::Any, name: &str, term: &dyn mettail_runtime::Term) -> Result<(), std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;

                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;

                // Add to primary type environment
                typed_env.#primary_field.set(name.to_string(), typed_term.0.clone());
                Ok(())
            }

            fn remove_from_env(&self, env: &mut dyn std::any::Any, name: &str) -> Result<bool, std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;

                // Try to remove from all type environments
                // Non-short-circuit `|` so ALL categories are checked — names
                // added via Ambiguous populate multiple per-category envs.
                let removed = #(#remove_checks)|*;
                Ok(removed)
            }

            fn clear_env(&self, env: &mut dyn std::any::Any) {
                if let Some(typed_env) = env.downcast_mut::<#env_name>() {
                    typed_env.clear();
                }
            }

            fn substitute_env(&self, term: &dyn mettail_runtime::Term, env: &dyn std::any::Any) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                let typed_env = env
                    .downcast_ref::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;

                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;

                let substituted = typed_term.0.substitute_env(typed_env);
                Ok(Box::new(#term_name(substituted)))
            }

            fn substitute_env_preserve_structure(&self, term: &dyn mettail_runtime::Term, env: &dyn std::any::Any) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                let typed_env = env
                    .downcast_ref::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                let substituted = typed_term.0.substitute_env(typed_env);
                Ok(Box::new(#term_name(substituted)))
            }

            fn list_env(&self, env: &dyn std::any::Any) -> Vec<(std::string::String, std::string::String, Option<std::string::String>)> {
                let typed_env = match env.downcast_ref::<#env_name>() {
                    Some(e) => e,
                    None => return Vec::new(),
                };

                let mut result = Vec::new();
                // Iterate in insertion order (IndexMap preserves order)
                #(#list_iterations)*
                // Dedup by name: Ambiguous terms populate multiple per-category
                // envs via `add_to_env`, producing duplicate (name, display) entries.
                // The multi-category storage is still used internally for cross-category
                // variable resolution; users only see one binding per name.
                let mut seen = std::collections::HashSet::new();
                result.retain(|(name, _, _)| seen.insert(name.clone()));
                result
            }

            fn set_env_comment(&self, env: &mut dyn std::any::Any, name: &str, comment: std::string::String) -> Result<(), std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                typed_env.set_comment(name, comment);
                Ok(())
            }

            fn is_env_empty(&self, env: &dyn std::any::Any) -> bool {
                env.downcast_ref::<#env_name>()
                    .map(|e| e.is_empty())
                    .unwrap_or(true)
            }

            // === Type Inference Methods ===

            fn infer_term_type(&self, term: &dyn mettail_runtime::Term) -> mettail_runtime::TermType {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return mettail_runtime::TermType::Unknown,
                };
                #language_name::infer_term_type_typed(&typed_term.0)
            }

            fn infer_var_types(&self, term: &dyn mettail_runtime::Term) -> Vec<mettail_runtime::VarTypeInfo> {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return Vec::new(),
                };
                #language_name::infer_var_types_typed(&typed_term.0)
            }

            fn infer_var_type(&self, term: &dyn mettail_runtime::Term, var_name: &str) -> Option<mettail_runtime::TermType> {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return None,
                };
                #language_name::infer_var_type_typed(&typed_term.0, var_name)
            }
        }
    }
}

/// Generate the Language trait implementation when the language has multiple types (enum term).
fn generate_language_trait_impl_multi(
    name: &syn::Ident,
    name_str: &str,
    _name_lower: &str,
    language: &LanguageDef,
) -> TokenStream {
    let language_name = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let inner_enum_name = format_ident!("{}TermInner", name);
    let metadata_name = format_ident!("{}Metadata", name);
    let env_name = format_ident!("{}Env", name);
    let name_lit = LitStr::new(name_str, name.span());

    let categories: Vec<_> = language.types.iter().map(|t| &t.name).collect();
    let remove_checks: Vec<TokenStream> = categories
        .iter()
        .map(|cat| {
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            quote! { typed_env.#field.remove(name).is_some() }
        })
        .collect();
    let list_iterations: Vec<TokenStream> = categories
        .iter()
        .map(|cat| {
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            quote! {
                for (name, val) in typed_env.#field.iter() {
                    let comment = typed_env.comments.get(name).cloned();
                    result.push((name.clone(), format!("{}", val), comment));
                }
            }
        })
        .collect();

    // Before adding: remove name from all category envs so reassigning replaces (e.g. x = 1 then x = true)
    let remove_before_add: Vec<TokenStream> = categories
        .iter()
        .map(|cat| {
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            quote! { typed_env.#field.remove(name); }
        })
        .collect();

    // add_to_env: match on term.0 and set the right env field
    let add_to_env_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let field = format_ident!("{}", cat.to_string().to_lowercase());
            let variant = format_ident!("{}", cat);
            quote! { #inner_enum_name::#variant(t) => typed_env.#field.set(name.to_string(), t.clone()) }
        })
        .collect();

    // infer_term_type: dispatch to per-category type inference
    let infer_term_type_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("{}", cat);
            let fn_name = format_ident!("infer_{}_type", cat.to_string().to_lowercase());
            quote! { #inner_enum_name::#variant(inner) => #language_name::#fn_name(inner) }
        })
        .collect();

    // Primary category: first type in the language definition (e.g. Proc for rhocalc, Int for Calculator).
    // Used to prefer the primary category's type when reporting the type of an Ambiguous term.
    let primary_type = &language.types[0].name;
    let primary_variant = format_ident!("{}", primary_type);
    let primary_type_str = LitStr::new(&primary_type.to_string(), primary_type.span());

    // normalize_term for multi-type: normalize the inner variant
    let normalize_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("{}", cat);
            quote! {
                #inner_enum_name::#variant(inner) => #inner_enum_name::#variant(inner.normalize())
            }
        })
        .collect();

    // try_direct_eval for multi-type: only when at least one type has native_type
    let try_direct_eval_arms: Vec<TokenStream> = language
        .types
        .iter()
        .filter_map(|t| {
            let native_ty = t.native_type.as_ref()?;
            let cat = &t.name;
            let variant = format_ident!("{}", cat);
            let literal_label = generate_literal_label(native_ty);
            Some(quote! {
                #inner_enum_name::#variant(inner) => inner.try_eval().map(|v| #term_name(#inner_enum_name::#variant(#cat::#literal_label(v))))
            })
        })
        .collect();
    let try_direct_eval_method: TokenStream = if try_direct_eval_arms.is_empty() {
        // No native-type direct eval. For a host-less language with structural-
        // congruence equations (e.g. Ambient), emit the binder-congruence
        // NativeHandler (Inc 1): float `new`s outward to a capture-safe NF.
        if crate::gen::runtime::binder_congruence::should_emit_binder_congruence(language) {
            quote! {
                fn try_direct_eval(&self, term: &dyn mettail_runtime::Term) -> Option<Box<dyn mettail_runtime::Term>> {
                    let typed_term = term.as_any().downcast_ref::<#term_name>()?;
                    let progressed = typed_term.0.binder_congruence_nf_term()?;
                    Some(Box::new(#term_name(progressed)))
                }
            }
        } else {
            quote! {}
        }
    } else {
        quote! {
            fn try_direct_eval(&self, term: &dyn mettail_runtime::Term) -> Option<Box<dyn mettail_runtime::Term>> {
                let typed_term = term.as_any().downcast_ref::<#term_name>()?;
                let result = match &typed_term.0 {
                    #(#try_direct_eval_arms),*,
                    _ => None,
                }?;
                Some(Box::new(result))
            }
        }
    };

    // infer_var_types dispatch arms (per-category)
    let infer_var_types_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("{}", cat);
            let collect_fn = format_ident!("collect_all_{}_vars", cat.to_string().to_lowercase());
            quote! {
                #inner_enum_name::#variant(inner) => {
                    let mut result = Vec::new();
                    let mut seen = std::collections::HashSet::new();
                    #language_name::#collect_fn(inner, inner, &mut result, &mut seen);
                    result
                }
            }
        })
        .collect();

    // infer_var_type dispatch arms (per-category)
    let infer_var_type_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("{}", cat);
            let collect_fn = format_ident!("collect_all_{}_vars", cat.to_string().to_lowercase());
            quote! {
                #inner_enum_name::#variant(inner) => {
                    // Try direct method first
                    if let Some(t) = inner.infer_var_type(var_name) {
                        return Some(#language_name::inferred_to_term_type(&t));
                    }
                    // Search all variables including bound ones
                    let mut result = Vec::new();
                    let mut seen = std::collections::HashSet::new();
                    #language_name::#collect_fn(inner, inner, &mut result, &mut seen);
                    result.into_iter().find(|v| v.name == var_name).map(|v| v.ty)
                }
            }
        })
        .collect();

    quote! {
        impl mettail_runtime::Language for #language_name {
            fn name(&self) -> &'static str {
                #name_lit
            }

            fn metadata(&self) -> &'static dyn mettail_runtime::LanguageMetadata {
                &#metadata_name
            }

            fn parse_term(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                #language_name::parse(input)
                    .map(|t| Box::new(t) as Box<dyn mettail_runtime::Term>)
            }

            fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                #language_name::parse_preserving_vars(input)
                    .map(|t| Box::new(t) as Box<dyn mettail_runtime::Term>)
            }

            #try_direct_eval_method

            fn parse_term_with_weighted_seed_ids(
                &self,
                input: &str,
            ) -> Result<(Box<dyn mettail_runtime::Term>, Vec<mettail_runtime::WeightedSeedId>), std::string::String> {
                #language_name::parse_preserving_vars_with_weighted_seed_ids(input)
                    .map(|(t, seeds)| (Box::new(t) as Box<dyn mettail_runtime::Term>, seeds))
            }

            fn parse_term_with_weighted_rewrite_seeds(
                &self,
                input: &str,
            ) -> Result<(Box<dyn mettail_runtime::Term>, Vec<mettail_runtime::WeightedRewriteSeed>), std::string::String> {
                #language_name::parse_preserving_vars_with_weighted_rewrite_seeds(input)
                    .map(|(t, seeds)| (Box::new(t) as Box<dyn mettail_runtime::Term>, seeds))
            }

            fn normalize_term(&self, term: &dyn mettail_runtime::Term) -> Box<dyn mettail_runtime::Term> {
                if let Some(typed) = term.as_any().downcast_ref::<#term_name>() {
                    let normalized = match &typed.0 {
                        #inner_enum_name::Ambiguous(alts) => {
                            let normalized_alts: Vec<#inner_enum_name> = alts.iter().map(|alt| match alt {
                                #(#normalize_arms),*,
                                #inner_enum_name::Ambiguous(_) => unreachable!("nested Ambiguous"),
                            }).collect();
                            #inner_enum_name::from_alternatives(normalized_alts)
                        }
                        #(#normalize_arms),*
                    };
                    Box::new(#term_name(normalized))
                } else {
                    term.clone_box()
                }
            }

            fn create_env(&self) -> Box<dyn std::any::Any + Send + Sync> {
                Box::new(#language_name::create_env())
            }

            fn add_to_env(&self, env: &mut dyn std::any::Any, name: &str, term: &dyn mettail_runtime::Term) -> Result<(), std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                // Remove name from all categories first so reassigning replaces the binding
                #(#remove_before_add)*
                match &typed_term.0 {
                    #inner_enum_name::Ambiguous(alts) => {
                        // For ambiguous terms, add to ALL matching category envs
                        for alt in alts {
                            match alt {
                                #(#add_to_env_arms),*,
                                #inner_enum_name::Ambiguous(_) => {} // invariant: no nested
                            }
                        }
                    }
                    #(#add_to_env_arms),*
                }
                Ok(())
            }

            fn remove_from_env(&self, env: &mut dyn std::any::Any, name: &str) -> Result<bool, std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                // Non-short-circuit `|` so ALL categories are checked — names
                // added via Ambiguous populate multiple per-category envs.
                let removed = #(#remove_checks)|*;
                Ok(removed)
            }

            fn clear_env(&self, env: &mut dyn std::any::Any) {
                if let Some(typed_env) = env.downcast_mut::<#env_name>() {
                    typed_env.clear();
                }
            }

            fn substitute_env(&self, term: &dyn mettail_runtime::Term, env: &dyn std::any::Any) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                let typed_env = env
                    .downcast_ref::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                let substituted = typed_term.0.substitute_env(typed_env);
                Ok(Box::new(#term_name(substituted)))
            }

            fn substitute_env_preserve_structure(&self, term: &dyn mettail_runtime::Term, env: &dyn std::any::Any) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
                let typed_env = env
                    .downcast_ref::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                let substituted = typed_term.0.substitute_env(typed_env);
                Ok(Box::new(#term_name(substituted)))
            }

            fn list_env(&self, env: &dyn std::any::Any) -> Vec<(std::string::String, std::string::String, Option<std::string::String>)> {
                let typed_env = match env.downcast_ref::<#env_name>() {
                    Some(e) => e,
                    None => return Vec::new(),
                };
                let mut result = Vec::new();
                #(#list_iterations)*
                // Ambiguous terms populate multiple per-category envs via
                // `add_to_env`; report one binding per name (multi-category
                // storage remains for cross-category variable resolution).
                let mut seen = std::collections::HashSet::new();
                result.retain(|(name, _, _)| seen.insert(name.clone()));
                result
            }

            fn set_env_comment(&self, env: &mut dyn std::any::Any, name: &str, comment: std::string::String) -> Result<(), std::string::String> {
                let typed_env = env
                    .downcast_mut::<#env_name>()
                    .ok_or_else(|| "Invalid environment type".to_string())?;
                typed_env.set_comment(name, comment);
                Ok(())
            }

            fn is_env_empty(&self, env: &dyn std::any::Any) -> bool {
                env.downcast_ref::<#env_name>()
                    .map(|e| e.is_empty())
                    .unwrap_or(true)
            }

            fn infer_term_type(&self, term: &dyn mettail_runtime::Term) -> mettail_runtime::TermType {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return mettail_runtime::TermType::Unknown,
                };
                match &typed_term.0 {
                    #inner_enum_name::Ambiguous(alts) => {
                        // Prefer primary category type for display when present among alternatives
                        for alt in alts {
                            if matches!(alt, #inner_enum_name::#primary_variant(_)) {
                                return mettail_runtime::TermType::Base(#primary_type_str.to_string());
                            }
                        }
                        // ROOT-B bare-var-fan quotient (user policy 2026-06-11;
                        // FV: BareVarFanQuotient.v — top_is_upper_bound /
                        // quotient_preserves_alternatives / detector_sound,
                        // zero-admission): an EVIDENCE-FREE Var fan over a
                        // single identifier joins to the TOP (start) category —
                        // every category injects into it (the ProcX wrap
                        // family), so the start category is the fan's lattice
                        // join, the categorical "unknown". Detector: every
                        // alternative DISPLAYS as the same bare identifier
                        // (token-soundness: a single-Ident input admits only
                        // literal-free var/injection chains, whose terminal
                        // yield is the identifier itself). This quotients the
                        // REPORT only — the alternative list is untouched (no
                        // parse-side drop; Display-equality here selects a
                        // report, it never merges or drops alternatives).
                        let mut displays = alts.iter().map(|a| format!("{}", a));
                        if let Some(first) = displays.next() {
                            let is_bare_ident = !first.is_empty()
                                && first
                                    .chars()
                                    .next()
                                    .map(|c| c.is_alphabetic() || c == '_')
                                    .unwrap_or(false)
                                && first.chars().all(|c| c.is_alphanumeric() || c == '_');
                            if is_bare_ident && displays.all(|s| s == first) {
                                return mettail_runtime::TermType::Base(
                                    #primary_type_str.to_string(),
                                );
                            }
                        }
                        mettail_runtime::TermType::Base("Ambiguous".to_string())
                    },
                    #(#infer_term_type_arms),*
                }
            }

            fn infer_var_types(&self, term: &dyn mettail_runtime::Term) -> Vec<mettail_runtime::VarTypeInfo> {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return Vec::new(),
                };
                match &typed_term.0 {
                    #inner_enum_name::Ambiguous(alts) => {
                        // M9 (2026-05-14): UNION semantics — concat all
                        // alts' discovered vars, dedupe by name (first
                        // alt wins on conflict). Replaces the D6 arg-max
                        // ("alt with most vars") which violated the
                        // "never disambiguate early" mandate by ranking
                        // alts. Every alt now contributes its vars; the
                        // foreign-cat-collector limitation that motivated
                        // D6 is naturally absorbed because the alt whose
                        // collector finds the var still appears in the
                        // union.
                        let mut union: Vec<mettail_runtime::VarTypeInfo> = Vec::new();
                        let mut seen_names: std::collections::HashSet<String> =
                            std::collections::HashSet::new();
                        for alt in alts.iter() {
                            let sub = #term_name(alt.clone());
                            for vti in self.infer_var_types(&sub) {
                                if seen_names.insert(vti.name.clone()) {
                                    union.push(vti);
                                }
                            }
                        }
                        union
                    }
                    #(#infer_var_types_arms),*
                }
            }

            fn infer_var_type(&self, term: &dyn mettail_runtime::Term, var_name: &str) -> Option<mettail_runtime::TermType> {
                let typed_term = match term.as_any().downcast_ref::<#term_name>() {
                    Some(t) => t,
                    None => return None,
                };
                match &typed_term.0 {
                    #inner_enum_name::Ambiguous(alts) => {
                        // Phase D.6 (2026-05-17, M14.3): UNION over alts'
                        // inferred types. Pre-D.6 this picked `alts[0]`
                        // (a P4 violation). The new path collects every
                        // alt's inferred type for var_name and constructs
                        // a `TermType::Ambiguous(Vec<TermType>)` union
                        // via `TermType::union` (which collapses to a
                        // single TermType when all alts agree, or to
                        // `Unknown` when none have the var).
                        let mut tys: Vec<mettail_runtime::TermType> = Vec::new();
                        for alt in alts.iter() {
                            let sub = #term_name(alt.clone());
                            if let Some(ty) = self.infer_var_type(&sub, var_name) {
                                tys.push(ty);
                            }
                        }
                        if tys.is_empty() {
                            None
                        } else {
                            Some(mettail_runtime::TermType::union(tys))
                        }
                    }
                    #(#infer_var_type_arms),*
                }
            }
        }
    }
}

/// Generate the type inference helper for the primary type
///
/// This handles detecting lambda variants and building the full function type.
/// The domain type is inferred from how the binder is USED in the body,
/// not just from the lambda variant.
fn generate_type_inference_helpers(
    primary_type: &Ident,
    language: &LanguageDef,
    self_fn_name: &Ident,
) -> TokenStream {
    let primary_type_lit = LitStr::new(&primary_type.to_string(), primary_type.span());

    // Get all categories for lambda variant detection (including native, e.g. Int/Bool/Str)
    let categories: Vec<_> = language.types.iter().map(|t| &t.name).collect();

    // Post-HOL-B: only emit Lam{D} / MLam{D} match arms on the primary
    // type for domains D where the HOL variants actually exist.
    let hol_pairs = crate::logic::common::compute_hol_domain_pairs(language);
    let primary_str = primary_type.to_string();

    // Generate match arms for lambda variants
    let mut lambda_arms: Vec<TokenStream> = Vec::new();

    for domain in &categories {
        if !hol_pairs.contains(&(primary_str.clone(), domain.to_string())) {
            continue;
        }
        let domain_lit = LitStr::new(&domain.to_string(), domain.span());
        let lam_variant = format_ident!("Lam{}", domain);
        let mlam_variant = format_ident!("MLam{}", domain);

        // Single lambda: Lam{Domain}(scope) -> [inferred_domain -> body_type]
        // We infer the domain type from how the binder is USED in the body
        lambda_arms.push(quote! {
            #primary_type::#lam_variant(scope) => {
                // Use unbind to get binder and body with proper types
                let (binder, body) = scope.clone().unbind();
                let body_type = Self::#self_fn_name(&body);

                // Get the binder name to infer its type from usage
                let binder_name = binder.0.pretty_name.as_ref();

                // Infer the binder's type from how it's used in the body
                let domain_type = if let Some(name) = binder_name {
                    // Use infer_var_type to get the actual type from usage
                    body.infer_var_type(name)
                        .map(|t| Self::inferred_to_term_type(&t))
                        .unwrap_or_else(|| mettail_runtime::TermType::Base(#domain_lit.to_string()))
                } else {
                    // Fallback to the variant's domain type
                    mettail_runtime::TermType::Base(#domain_lit.to_string())
                };

                mettail_runtime::TermType::Arrow(
                    Box::new(domain_type),
                    Box::new(body_type),
                )
            }
        });

        // Multi lambda: MLam{Domain}(scope) -> [Domain* -> body_type]
        lambda_arms.push(quote! {
            #primary_type::#mlam_variant(scope) => {
                let (_binders, body) = scope.clone().unbind();
                let body_type = Self::#self_fn_name(&body);
                mettail_runtime::TermType::MultiArrow(
                    Box::new(mettail_runtime::TermType::Base(#domain_lit.to_string())),
                    Box::new(body_type),
                )
            }
        });
    }

    quote! {
        match term {
            #(#lambda_arms)*
            // Non-lambda terms have the primary type as their type
            _ => mettail_runtime::TermType::Base(#primary_type_lit.to_string()),
        }
    }
}

#[cfg(test)]
mod tests {
    fn from_alternatives_generated_body() -> String {
        let source = include_str!("language.rs");
        let needle = "fn from_alternatives(alts: Vec<Self>) -> Self";
        let start = source
            .find(needle)
            .expect("generated from_alternatives source is present");
        let after_signature = &source[start..];
        let open_rel = after_signature
            .find('{')
            .expect("from_alternatives has an opening brace");
        let open = start + open_rel;

        let mut depth = 0usize;
        for (offset, ch) in source[open..].char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        let end = open + offset + ch.len_utf8();
                        return source[open..end].to_string();
                    }
                },
                _ => {},
            }
        }

        panic!("from_alternatives body is balanced");
    }

    fn strip_line_comments(source: &str) -> String {
        source
            .lines()
            .map(|line| line.split_once("//").map_or(line, |(code, _)| code))
            .collect::<Vec<_>>()
            .join("\n")
    }

    #[test]
    fn generated_language_impl_inherits_metadata_runtime_default() {
        let source = include_str!("language.rs");
        let needle = concat!("fn default_runtime_", "backend(&self)");

        assert!(
            !source.contains(needle),
            "generated Language impls must inherit the metadata-driven \
             default_runtime_backend trait method"
        );
    }

    #[test]
    fn from_alternatives_deduplicates_only_by_semantic_fingerprint() {
        let body = from_alternatives_generated_body();
        let executable = strip_line_comments(&body);

        assert!(
            executable.contains("std::collections::HashSet<Vec<u8>>"),
            "from_alternatives must keep exact semantic keys, not a lossy hash"
        );
        assert!(
            executable.contains("a.semantic_fingerprint()"),
            "from_alternatives must deduplicate by observational semantic fingerprint"
        );
        assert!(
            executable.contains("seen_keys.insert(key)"),
            "from_alternatives must retain the first alternative for each exact semantic key"
        );

        for forbidden in
            ["weight", "aweight", "ground", "declaration", "display", "format!", "to_string"]
        {
            assert!(
                !executable.contains(forbidden),
                "from_alternatives executable body must not prune by `{forbidden}`"
            );
        }
    }
}
