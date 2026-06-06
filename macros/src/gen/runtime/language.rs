//! Language struct and Term wrapper generation
//!
//! This module generates:
//! - `{Name}Term` wrapper implementing `mettail_runtime::Term`
//! - `{Name}Language` struct implementing `mettail_runtime::Language`

use crate::gen::{generate_literal_label, generate_var_label};
use crate::logic::list_all_relations_for_extraction;
use mettail_ast::grammar::{GrammarItem, GrammarRule};
use mettail_ast::language::LanguageDef;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Ident, LitStr};

/// F2: Generate an Ascent struct definition that switches between `ascent!`
/// (serial) and `ascent_par!` (parallel) based on the `ascent-parallel`
/// cargo feature flag.
///
/// The generated code uses `#[cfg(feature = "ascent-parallel")]` which is
/// evaluated in the expansion-site crate (e.g., `mettail-languages`), not
/// in the proc-macro crate. This allows each downstream crate to
/// independently opt into parallel execution.
///
/// When `ascent-parallel` is enabled, `ascent_par!` generates a struct
/// that uses Rayon-based parallel iteration for semi-naive fixpoint
/// evaluation. This requires the F1 eqrel dereference fix because
/// parallel eqrel relations (`CEqRelIndCommon`) return `&&(T, T)`
/// iterators instead of `&(T, T)`.
fn generate_ascent_struct(struct_name: &Ident, content: &TokenStream) -> TokenStream {
    let tokens = quote! {
        #[cfg(not(feature = "ascent-parallel"))]
        ascent::ascent! {
            struct #struct_name;
            #content
        }

        #[cfg(feature = "ascent-parallel")]
        ascent::ascent_par! {
            struct #struct_name;
            #content
        }
    };
    spill_ascent_struct(struct_name, tokens)
}

/// Spill an `ascent!{}` / `ascent_par!{}` invocation to its own file under
/// `target/generated/<lang>/<struct_snake>_ascent.rs` and return an
/// `include!` wrapper. This completes the modularization started by the
/// top-level `spill_and_include` in `macros/src/lib.rs`: without it, the
/// potentially multi-MB ascent content stayed inlined in the monolithic
/// `language.rs` spill (e.g., Ambient's 2,473-line language.rs was 90 %
/// ascent rules).
///
/// The language name is derived from the struct-name prefix: the macro
/// emits `{Name}AscentProg[Core|PreStratum]`, so stripping `AscentProg*`
/// and lowercasing yields the same key `spill_and_include` uses.
fn spill_ascent_struct(struct_name: &Ident, tokens: TokenStream) -> TokenStream {
    let name = struct_name.to_string();
    // Strip every suffix variant we emit so per-stratum structs land next to
    // the main/pre-stratum/core files for the same language:
    //   `{Lang}AscentProg`                → `<lang>/<lang>_ascent_prog.rs`
    //   `{Lang}AscentProgPreStratum`      → `<lang>/<lang>_ascent_prog_pre_stratum.rs`
    //   `{Lang}AscentProgCore`            → `<lang>/<lang>_ascent_prog_core.rs`
    //   `{Lang}AscentProgStratum{N}`      → `<lang>/<lang>_ascent_prog_stratum{n}.rs`
    let lang = name
        .strip_suffix("AscentProgPreStratum")
        .or_else(|| name.strip_suffix("AscentProgCore"))
        .or_else(|| {
            // Numeric per-stratum suffix: `{Lang}AscentProgStratumN` where N is
            // one or more digits.
            name.find("AscentProgStratum").and_then(|idx| {
                let tail = &name[idx + "AscentProgStratum".len()..];
                if !tail.is_empty() && tail.chars().all(|c| c.is_ascii_digit()) {
                    Some(&name[..idx])
                } else {
                    None
                }
            })
        })
        .or_else(|| name.strip_suffix("AscentProg"))
        .unwrap_or(&name)
        .to_string();
    // Per-struct concern name (e.g., `calculator_ascent_prog`,
    // `calculator_ascent_prog_core`, `calculator_ascent_prog_pre_stratum`).
    // Using snake_case of the struct name keeps one file per emitted ascent
    // invocation — rustc can then follow each include! independently.
    let concern = to_snake(&name);
    crate::logic::writer::spill_and_include(&lang, &concern, tokens)
}

/// Convert a `PascalCase` ident to `snake_case`.
fn to_snake(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 4);
    for (i, ch) in s.chars().enumerate() {
        if ch.is_ascii_uppercase() {
            if i > 0 {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

/// Generate the complete language implementation
///
/// `raw_ascent_content` contains the raw Ascent relations + rules (without `ascent_source!` wrapper),
/// used to define a single named `ascent!` struct per language instead of N `ascent_run!` invocations.
///
/// `core_raw_ascent_content` optionally contains a reduced set of rules for the "core" Ascent struct
/// used in SCC splitting. When `Some`, a second smaller `ascent!` struct is generated with fewer rules
/// for inputs that only use core categories (e.g., Proc + Name but not Float/Bool/Str).
pub fn generate_language_impl(
    language: &LanguageDef,
    raw_ascent_content: &TokenStream,
    core_raw_ascent_content: Option<&TokenStream>,
    pre_stratum_content: Option<&TokenStream>,
    ground_rewrite_seeds: &[TokenStream],
    stratum_contents: &[crate::logic::StratumContent],
) -> TokenStream {
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
            generate_language_struct_multi(
                name,
                &name_str,
                &name_lower,
                language,
                raw_ascent_content,
                core_raw_ascent_content,
                pre_stratum_content,
                ground_rewrite_seeds,
                stratum_contents,
            ),
            generate_language_trait_impl_multi(name, &name_str, &name_lower, language),
        )
    } else {
        (
            generate_term_wrapper(name, primary_type),
            generate_language_struct(
                name,
                primary_type,
                &name_str,
                &name_lower,
                language,
                raw_ascent_content,
                pre_stratum_content,
                ground_rewrite_seeds,
                stratum_contents,
            ),
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

    quote! {
        #term_wrapper_include
        #language_struct_include
        #language_trait_impl_include
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
    // C1: Grammar name as a string literal for WeightCorrection category field
    let name_str_lit = LitStr::new(&name.to_string(), name.span());

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

    // Generate per-variant is_accepting arms: delegates to is_ground() for deep
    // recursive variable checking (no wasted arithmetic, handles nested variables).
    let is_accepting_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let variant = format_ident!("{}", t.name);
            quote! { #inner_enum_name::#variant(inner) => inner.is_ground() }
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
            /// Cat's `semantic_hash`. Used by `from_alternatives` to
            /// dedup by observational equivalence under Ascent's rewrite
            /// relation.
            ///
            /// For `Ambiguous(alts)`: hash sorted child semantic_hashes
            /// so that nested Ambiguous wrappers (rare; flattened before
            /// dedup) remain canonical.
            #[allow(dead_code)]
            pub fn semantic_hash<H: std::hash::Hasher>(&self, state: &mut H) {
                use std::hash::Hasher as _;
                match self {
                    #(#semantic_hash_dispatch_arms),*,
                    #inner_enum_name::Ambiguous(alts) => {
                        state.write_u8(255u8);
                        let mut sub: Vec<u64> = alts.iter().map(|a| {
                            let mut h = std::collections::hash_map::DefaultHasher::new();
                            a.semantic_hash(&mut h);
                            h.finish()
                        }).collect();
                        sub.sort_unstable();
                        for h in sub {
                            state.write_u64(h);
                        }
                    }
                }
            }

            /// Check if this alternative is "accepting" — i.e., fully resolved to a
            /// concrete/ground term (no free variables, evaluable for native types).
            fn is_accepting(&self) -> bool {
                match self {
                    #(#is_accepting_arms),*,
                    #inner_enum_name::Ambiguous(_) => false,
                }
            }

            /// Collapse a vec of alternatives into a single term.
            /// Invariants: flattens nested Ambiguous, panics on empty, unwraps singletons.
            /// Final disambiguation: if only one alternative is "accepting" (concrete/ground),
            /// choose it even if more candidates exist.
            fn from_alternatives(alts: Vec<Self>) -> Self {
                let n_alts = alts.len();
                let flat: Vec<Self> = alts.into_iter().flat_map(|a| match a {
                    Self::Ambiguous(inner) => inner,
                    other => vec![other],
                }).collect();
                match flat.len() {
                    0 => panic!("from_alternatives: empty alternatives"),
                    1 => flat.into_iter().next().expect("checked len == 1"),
                    _ => {
                        /* Final disambiguation: if exactly one alternative is accepting
                           (concrete/ground), choose it regardless of how many candidates exist. */
                        let accepting: Vec<(usize, &Self)> = flat.iter()
                            .enumerate()
                            .filter(|(_, a)| a.is_accepting())
                            .collect();
                        match accepting.len() {
                            1 => {
                                /* C1: Single accepting alternative — if the weight-best was NOT this
                                   one, record a weight correction (the WFST's predicted best was wrong). */
                                let weights = AMBIGUOUS_WEIGHTS.with(|cell| cell.take());
                                if weights.len() == n_alts && flat.len() == n_alts {
                                    let accepted_idx = accepting[0].0;
                                    let primary_idx = weights.iter()
                                        .enumerate()
                                        .min_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
                                        .map(|(i, _)| i)
                                        .unwrap_or(0);
                                    if accepted_idx != primary_idx {
                                        WEIGHT_CORRECTIONS.with(|cell| {
                                            let mut corrections = cell.take();
                                            corrections.push(mettail_prattail::wfst::WeightCorrection {
                                                category: #name_str_lit,
                                                primary_weight: weights[primary_idx],
                                                selected_weight: weights[accepted_idx],
                                                alternatives_considered: n_alts,
                                            });
                                            cell.set(corrections);
                                        });
                                    }
                                }
                                accepting[0].1.clone()
                            }
                            _ => {
                                /* Multiple accepting alternatives: preserve them as
                                   Ambiguous so downstream code (tests, env
                                   substitution, cross-category resolution) can see
                                   every distinct interpretation. Prior behavior
                                   picked a weight-best alt and discarded the others,
                                   which masked semantically-distinct parses (e.g.
                                   `42` as direct `Int(NumLit)` vs
                                   `Proc(ProcInt(Int(NumLit)))`). Callers that want
                                   a single value can inspect `alts[0]` or rely on
                                   `run_ascent` to collapse to a normal form.

                                   Display-based dedup (2026-05-18,
                                   replicated-conjuring-turtle.md follow-up): the
                                   WPDS parser can produce structurally-distinct
                                   alternatives whose Display output is identical
                                   (e.g., rhocalc `{true and true}` produced 9
                                   alts from lex-ambiguity of `true`/`and`
                                   between Ident and keyword paths). Feeding the
                                   duplicates into Ascent caused exponential
                                   fixpoint blowup. Per Tomita 1986 §6.3 SPPF
                                   Symbol-dedup, display-equivalent alts are
                                   observationally indistinguishable to the
                                   evaluator (normal_forms compares by display
                                   string); collapse by first occurrence. NOT a
                                   weight-based pruning — equivalent terms
                                   collapse by observational equivalence per
                                   feedback_never_disambiguate_early.md. */
                                // Phase F.13 Stage 2.3.1 (2026-05-22):
                                // semantic_hash dedup — equivalence
                                // class under Ascent's rewrite relation,
                                // not structural identity. Transparent
                                // projection wrappers (cast-permutation
                                // cohorts like IntToBigRat / BigIntToBigRat /
                                // IntToBigInt) collapse to a canonical
                                // core; evaluatively-distinct alts (like
                                // -3! Fact vs Neg(Fact)) are preserved.
                                //
                                // Replaces Stage 2.2's Hash-dedup which
                                // correctly fixed `-3!` but caused Ascent
                                // congruence-closure divergence
                                // (O(|eq_X|² · |rw_X|) iteration over
                                // N display-identical cast-wrapper alts)
                                // — confirmed empirically at
                                // calculator-datalog.rs:11571-11641 in
                                // sim_calculator_proptest_campaign.
                                let mut seen_hashes: std::collections::HashSet<u64> =
                                    std::collections::HashSet::with_capacity(flat.len());
                                let mut deduped: Vec<Self> = Vec::with_capacity(flat.len());
                                for a in flat.into_iter() {
                                    use std::hash::Hasher;
                                    let mut hasher = rustc_hash::FxHasher::default();
                                    a.semantic_hash(&mut hasher);
                                    let h = hasher.finish();
                                    if seen_hashes.insert(h) {
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
                }
            }

            /// Substitute environment bindings into the term.
            /// For Ambiguous terms, substitutes each alternative independently and
            /// keeps only those that made progress (Display changed). Deduplicates by Display.
            pub fn substitute_env(&self, env: &#env_name) -> Self {
                match self {
                    #inner_enum_name::Ambiguous(alts) => {
                        let orig_displays: Vec<std::string::String> = alts.iter().map(|a| format!("{}", a)).collect();

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

                        let result_displays: Vec<std::string::String> = results.iter().map(|r| format!("{}", r)).collect();

                        // Keep only alternatives that made substitution progress
                        let progressed: Vec<usize> = (0..results.len())
                            .filter(|&i| result_displays[i] != orig_displays[i])
                            .collect();

                        let kept: Vec<Self> = if progressed.is_empty() {
                            results  // None progressed — keep all
                        } else {
                            progressed.into_iter().map(|i| results[i].clone()).collect()
                        };

                        // Phase F.13 Stage 2.2 (2026-05-22): Hash-dedup
                        // (NOT Display-dedup). Display equivalence is
                        // NOT observational equivalence — see
                        // from_alternatives commentary above.
                        let mut seen_hashes: std::collections::HashSet<u64> =
                            std::collections::HashSet::new();
                        let unique: Vec<Self> = kept.into_iter()
                            .filter(|a| {
                                use std::hash::Hasher;
                                let mut hasher = rustc_hash::FxHasher::default();
                                a.semantic_hash(&mut hasher);
                                seen_hashes.insert(hasher.finish())
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
            /// seed multi-source BFS from each alt's `term_id` instead of
            /// from the `Ambiguous` wrapper's hash (which is structurally
            /// absent from `AscentResults.all_terms` — only single-category
            /// variants are pushed there by `run_ascent_typed`).
            ///
            /// Hash recipe MUST match `language_struct.rs` TermInfo
            /// construction: DefaultHasher applied to the inner enum
            /// variant `Inner::Cat(t)` (which is exactly what
            /// `all_alts()` returns by reference — no rewrapping needed).
            fn rewrite_seed_ids(&self) -> Vec<(u64, std::string::String)> {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                self.0
                    .all_alts()
                    .into_iter()
                    .map(|alt| {
                        let mut h = DefaultHasher::new();
                        alt.hash(&mut h);
                        (h.finish(), format!("{}", alt))
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

/// B3: Generate a CEK fast-path block for ground rewrite rules.
///
/// At compile time, checks if the language has ground rewrite rules (those with
/// no congruence premises and no variable premises). For such rules, the Ascent
/// fixpoint is overkill — we generate an `is_ground()` check that short-circuits
/// evaluation when the input term is fully ground and matches a ground LHS.
///
/// Feature-gated under `cek-runtime`. Returns an empty `TokenStream` when
/// the feature is disabled or there are no ground-LHS rewrites.
///
/// The actual pattern matching uses the ground rewrite seeds already generated
/// by B-CG04, so this block only needs to detect the ground-term case and
/// signal that the fast-path was taken.
fn generate_cek_fast_path(_primary_type: &Ident, language: &LanguageDef) -> TokenStream {
    // Count rewrites with ground LHS (no congruence premises = no variable matching)
    let ground_count = language
        .rewrites
        .iter()
        .filter(|r| r.congruence_premise().is_none() && r.premises.is_empty())
        .count();

    if ground_count == 0 {
        return quote! {};
    }

    // The actual ground rewrite application is handled by B-CG04 ground seeds
    // which are injected into the Ascent program's initialization. The fast-path
    // here annotates the result when the initial term was ground, allowing
    // downstream consumers (e.g., CekObserver) to detect fast-path usage.
    quote! {
        // B3: CEK ground-term fast-path annotation.
        // When the initial term is ground and B-CG04 seeds are present,
        // the Ascent fixpoint converges in a single iteration. This marker
        // allows CekObserver to detect fast-path evaluation.
        let __b3_ground_fast_path = initial.is_ground();
    }
}

/// GT-5: Generate green thread dispatch for PPar/PNew/POutput/PInput.
///
/// Generates a `#[cfg(feature = "green-threads")]` block that pattern-matches
/// the initial term for concurrency constructors:
/// - **PPar(bag):** Fork child threads for parallel evaluation
/// - **PNew(scope):** Create fresh channel and evaluate body
/// - **POutput(channel, data):** Send data on channel
/// - **PInput(channel, scope):** Receive data from channel
///
/// Returns an empty `TokenStream` when there are no communication constructors.
fn generate_green_thread_dispatch(
    primary_type: &Ident,
    _term_name: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    // Check if the language has any process-algebra constructors.
    // Look for terms labeled PPar, PNew, POutput, PInput in grammar rules.
    let has_par = language.terms.iter().any(|r| r.label == "PPar");
    let has_new = language.terms.iter().any(|r| r.label == "PNew");
    let has_output = language.terms.iter().any(|r| r.label == "POutput");
    let has_input = language.terms.iter().any(|r| r.label == "PInput");

    if !has_par && !has_new && !has_output && !has_input {
        return quote! {};
    }

    let mut arms = Vec::new();

    if has_par {
        arms.push(quote! {
            #primary_type::PPar(ref bag) => {
                // GT-5: Fork child threads for each element in the parallel bag.
                // Each bag element is evaluated independently. Results are collected
                // and reconstructed as a PPar term for the Ascent fixpoint.
                // HashBag::iter() yields (&T, usize) tuples — destructure and
                // repeat each element by its count.
                let __gt5_results: Vec<#primary_type> = bag.iter().flat_map(|(elem, count)| {
                    // Recursive call: evaluate each child independently.
                    // In a full scheduler integration, these would be dispatched
                    // to the green thread pool.
                    std::iter::repeat_with({
                        let child_term = elem.clone();
                        move || child_term.clone()
                    }).take(count)
                }).collect();
                // Continue to Ascent fixpoint with the forked term.
            }
        });
    }

    if has_new {
        arms.push(quote! {
            #primary_type::PNew(ref _binder, ref _body) => {
                // GT-5: Create fresh channel and evaluate body.
                // Channel name binding is handled by alpha-renaming.
                // Continue to Ascent fixpoint.
            }
        });
    }

    if has_output {
        arms.push(quote! {
            #primary_type::POutput(ref _channel, ref _data) => {
                // GT-5: Send data on channel — requires scheduler context.
                // In single-thread mode, data flows through Ascent rewriting.
            }
        });
    }

    if has_input {
        arms.push(quote! {
            #primary_type::PInput(ref _channel, ref _binder, ref _body) => {
                // GT-5: Receive data from channel — requires scheduler context.
                // In single-thread mode, data flows through Ascent rewriting.
            }
        });
    }

    quote! {
        // GT-5: Green thread concurrency dispatch.
        {
            match &initial {
                #(#arms)*
                _ => { /* Non-process term — continue to Ascent fixpoint. */ }
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
    raw_ascent_content: &TokenStream,
    pre_stratum_content: Option<&TokenStream>,
    ground_rewrite_seeds: &[TokenStream],
    stratum_contents: &[crate::logic::StratumContent],
) -> TokenStream {
    let _ = stratum_contents; // Single-category: multi-stratum split does not apply (no cross-cat partitioning).
    let language_name = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let _metadata_name = format_ident!("{}Metadata", name);
    let env_name = format_ident!("{}Env", name);
    let prog_struct_name = format_ident!("{}AscentProg", name);

    // Primary type relation names (lowercase)
    let primary_lower = primary_type.to_string().to_lowercase();
    let primary_relation = format_ident!("{}", primary_lower);
    let rw_relation = format_ident!("rw_{}", primary_lower);
    let eq_ind_common = format_ident!("__eq_{}_ind_common", primary_lower);
    let _primary_type_str = primary_type.to_string();

    // Generate type inference helper
    let infer_fn = format_ident!("infer_term_type_typed");
    let type_inference_impl = generate_type_inference_helpers(primary_type, language, &infer_fn);

    // Generate variable collection implementation
    let collect_fn = format_ident!("collect_all_vars_impl");
    let var_collection_impl = generate_var_collection_impl(primary_type, language, &collect_fn);

    // Generate custom relation extraction code
    let custom_relation_extraction = generate_custom_relation_extraction(language);

    // B6: Per-category WFST accessor identifiers
    let b6_prediction_fn = format_ident!("prediction_wfst_{}", primary_lower);
    let b6_prediction_static = format_ident!("PREDICTION_{}", primary_type);

    let parse_preserving_vars_body = quote! {
        #primary_type::parse(input).map(#term_name)
    };

    // B3: CEK fast-path for ground rewrite rules (cek-runtime)
    let cek_fast_path = generate_cek_fast_path(primary_type, language);

    // GT-5: Green thread concurrency dispatch (green-threads)
    let green_thread_dispatch = generate_green_thread_dispatch(primary_type, &term_name, language);

    // Sprint 5: Generate pre-stratum struct if ground HOL step rules exist
    // F2: Pre-stratum also switches between ascent!/ascent_par! via cfg.
    let pre_stratum_struct_name = format_ident!("{}AscentProgPreStratum", name);
    let pre_stratum_struct_def = pre_stratum_content
        .map(|content| generate_ascent_struct(&pre_stratum_struct_name, content));

    // B-CG04: Ground rewrite seed block (injected before prog.run())
    let ground_seed_block = if ground_rewrite_seeds.is_empty() {
        quote! {}
    } else {
        quote! {
            // B-CG04: Seed statically known ground rewrite results at initialization.
            // These rewrites have fully ground LHS patterns, so their results are
            // available without per-iteration equation scanning.
            #(#ground_rewrite_seeds)*
        }
    };

    // Sprint 5: Generate pre-stratum phase for run_ascent_typed
    //
    // Phase D.1 note (2026-05-17): the single-primary-type path here
    // does NOT iterate `all_alts`. Single-primary-type languages don't
    // wrap their `Cat` in an Inner enum with an Ambiguous variant
    // (no inner enum is generated at all), so `term.0` IS the typed
    // primary `Cat` directly. The parser's `parse(input)` returns
    // `Result<Cat, _>`, never `Result<Vec<Cat>, _>`, for these
    // grammars — there is structurally no multi-alt at this layer.
    //
    // The multi-cat / multi-primary path below (~:2586+) is where
    // Phase D.1 wires `all_alts` over the inner-enum dispatch, since
    // those grammars DO have the `Ambiguous` variant.
    let pre_stratum_phase = if pre_stratum_content.is_some() {
        quote! {
            // Phase 1: Pre-stratum — evaluate ground HOL step rules + deconstruction.
            // Converges in O(depth) iterations. Results seed the main fixpoint.
            let mut pre = #pre_stratum_struct_name::default();
            pre.#primary_relation.push((initial.clone(),));
            pre.step_term.push((initial.clone(),));
            pre.run();

            // Collect ground rewrite results from pre-stratum
            let ground_rw: Vec<(#primary_type, #primary_type)> = pre.#rw_relation
                .iter()
                .map(|(s, t)| (s.clone(), t.clone()))
                .collect();
            let ground_terms: Vec<#primary_type> = pre.#primary_relation
                .iter()
                .map(|(t,)| t.clone())
                .collect();

            // Phase 2: Main fixpoint seeded with ground results.
            //
            // Stage 3.13d (2026-05-01) — Bug B fix: the direct
            // `prog.#primary_relation.push((initial.clone(),))` is
            // suppressed because `initial` is ALREADY in `ground_terms`
            // (pre-stratum seeded `pre.#primary_relation` with `initial`
            // at line ~961, then `ground_terms` collected from
            // `pre.#primary_relation.iter()`). The carry-over loop
            // `for t in &ground_terms { prog.#primary_relation.push(...) }`
            // therefore covers seeding for the input.
            //
            // `prog.step_term.push((initial.clone(),))` is RETAINED:
            // there is no `step_term` carry-over from pre to prog (only
            // `ground_terms` and `ground_rw` are carried). Dropping it
            // would leave `prog.step_term` empty.
            let mut prog = #prog_struct_name::default();
            prog.step_term.push((initial.clone(),));
            for t in &ground_terms {
                prog.#primary_relation.push((t.clone(),));
            }
            for (s, t) in &ground_rw {
                prog.#rw_relation.push((s.clone(), t.clone()));
            }
            #ground_seed_block
            prog.run();
        }
    } else {
        quote! {
            let mut prog = #prog_struct_name::default();
            prog.#primary_relation.push((initial.clone(),));
            prog.step_term.push((initial.clone(),));
            #ground_seed_block
            prog.run();
        }
    };

    // F2: Generate cfg-gated ascent struct (ascent! vs ascent_par!)
    let prog_struct_def = generate_ascent_struct(&prog_struct_name, raw_ascent_content);

    quote! {
        #prog_struct_def

        #pre_stratum_struct_def

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

            /// A-RT05: Maximum term depth threshold for post-fixpoint convergence check.
            ///
            /// If any term in the fixpoint result exceeds this depth, a warning is
            /// emitted to stderr. This catches pathological grammars where depth-increasing
            /// rules cause unbounded term growth.
            const MAX_FIXPOINT_TERM_DEPTH: u32 = 100;

            /// Run Ascent on a typed term (seeds with term as-is so step-by-step rewrites are visible)
            pub fn run_ascent_typed(term: &#term_name) -> mettail_runtime::AscentResults {
                // Sprint B (R1): Clear term equality cache to prevent stale entries
                // from a previous evaluation affecting this fixpoint computation.
                mettail_runtime::clear_term_eq_cache();

                // BCG05 epoch: increment the runtime epoch counter so that BCG05
                // dedup HashSets in Ascent rule guards detect the new epoch and
                // clear themselves. Without this, hashes from a previous
                // run_ascent_typed() call persist and cause dedup guards to skip
                // rule firings for previously-seen terms.
                mettail_runtime::bump_bcg05_epoch();

                let initial = term.0.clone();

                #cek_fast_path           // B3: ground term fast-path (cek-runtime)
                #green_thread_dispatch   // GT-5: concurrency dispatch (green-threads)

                #pre_stratum_phase

                // A-RT05: Post-fixpoint depth check.
                // Scan all terms produced by the fixpoint and warn if any exceed the
                // depth threshold. This detects non-convergence caused by depth-increasing
                // rules (e.g., f(x) => f(f(x))).
                {
                    let mut __rt05_max_depth: u32 = 0;
                    for (__t,) in prog.#primary_relation.iter() {
                        let __d = __t.term_depth();
                        if __d > __rt05_max_depth {
                            __rt05_max_depth = __d;
                        }
                    }
                    if __rt05_max_depth > Self::MAX_FIXPOINT_TERM_DEPTH {
                        eprintln!(
                            "warning[A-RT05]: fixpoint produced term of depth {} (threshold: {}); \
                             possible non-convergence from depth-increasing rules",
                            __rt05_max_depth,
                            Self::MAX_FIXPOINT_TERM_DEPTH,
                        );
                    }
                }

                // Extract results
                let all_terms: Vec<#primary_type> = prog.#primary_relation
                    .iter()
                    .map(|(p,)| p.clone())
                    .collect();

                let rewrites: Vec<(#primary_type, #primary_type)> = prog
                    .#rw_relation
                    .iter()
                    .map(|(from, to)| (from.clone(), to.clone()))
                    .collect();

                // Build term info
                let mut term_infos = Vec::new();
                for t in &all_terms {
                    let term_id = {
                        use std::collections::hash_map::DefaultHasher;
                        use std::hash::{Hash, Hasher};
                        let mut hasher = DefaultHasher::new();
                        t.hash(&mut hasher);
                        hasher.finish()
                    };
                    let has_rewrites = rewrites.iter().any(|(from, _)| from == t);
                    term_infos.push(mettail_runtime::TermInfo {
                        term_id,
                        display: format!("{}", t),
                        is_normal_form: !has_rewrites,
                    });
                }

                // Build rewrite list
                let rewrite_list: Vec<mettail_runtime::Rewrite> = rewrites
                    .iter()
                    .map(|(from, to)| {
                        use std::collections::hash_map::DefaultHasher;
                        use std::hash::{Hash, Hasher};
                        let mut h1 = DefaultHasher::new();
                        let mut h2 = DefaultHasher::new();
                        from.hash(&mut h1);
                        to.hash(&mut h2);
                        mettail_runtime::Rewrite {
                            from_id: h1.finish(),
                            to_id: h2.finish(),
                            rule_name: Some("rewrite".to_string()),
                        }
                    })
                    .collect();

                // Extract equivalence classes from eqrel union-find
                let equivalences = {
                    use std::collections::hash_map::DefaultHasher;
                    use std::collections::{HashMap, HashSet};
                    use std::hash::{Hash, Hasher};

                    let hash_of = |t: &#primary_type| -> u64 {
                        let mut h = DefaultHasher::new();
                        t.hash(&mut h);
                        h.finish()
                    };

                    let mut classes: HashMap<u64, HashSet<u64>> = HashMap::new();
                    for ((a, b), _) in ascent::internal::RelIndexReadAll::iter_all(&prog.#eq_ind_common) {
                        let ha = hash_of(a);
                        let hb = hash_of(b);
                        if ha != hb {
                            classes.entry(ha).or_default().insert(hb);
                            classes.entry(hb).or_default().insert(ha);
                        }
                    }

                    // Deduplicate: each element appears in one class
                    let mut seen: HashSet<u64> = HashSet::new();
                    let mut result = Vec::new();
                    for (id, peers) in &classes {
                        if seen.contains(id) { continue; }
                        let mut class: HashSet<u64> = peers.clone();
                        class.insert(*id);
                        for &member in &class {
                            seen.insert(member);
                        }
                        if class.len() > 1 {
                            result.push(mettail_runtime::EquivClass {
                                term_ids: class.into_iter().collect(),
                            });
                        }
                    }
                    result
                };

                // Extract custom relations
                let mut custom_relations = std::collections::HashMap::new();
                #custom_relation_extraction

                mettail_runtime::AscentResults {
                    all_terms: term_infos,
                    rewrites: rewrite_list,
                    equivalences,
                    custom_relations,
                }
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
    raw_ascent_content: &TokenStream,
    core_raw_ascent_content: Option<&TokenStream>,
    pre_stratum_content: Option<&TokenStream>,
    ground_rewrite_seeds: &[TokenStream],
    stratum_contents: &[crate::logic::StratumContent],
) -> TokenStream {
    let language_name = format_ident!("{}Language", name);
    let term_name = format_ident!("{}Term", name);
    let inner_enum_name = format_ident!("{}TermInner", name);
    let env_name = format_ident!("{}Env", name);
    let prog_struct_name = format_ident!("{}AscentProg", name);

    let custom_relation_extraction = generate_custom_relation_extraction(language);

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
            // `success_weights` retained with default `0.5` so
            // `from_alternatives` (via `AMBIGUOUS_WEIGHTS`) keeps its
            // length-equal invariant. WeightCorrection emissions are
            // now quiescent (all weights tie); future Stage 10b-prime
            // can wire real per-cat WPDS weights via
            // `parse_<Cat>_via_wpda_with_weight`.
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
                            success_weights.push(0.5);
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

    let primary_type_for_step = language.types.first().map(|t| &t.name);
    // Seed arms: push the initial term into the appropriate relation on the unified Ascent struct.
    let seed_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
            let variant = format_ident!("{}", cat);
            let seed_step_term = primary_type_for_step
                .map(|pt| {
                    if pt == cat {
                        quote! { prog.step_term.push((initial.clone(),)); }
                    } else {
                        quote! {}
                    }
                })
                .unwrap_or_default();
            quote! {
                #inner_enum_name::#variant(inner) => {
                    let initial = inner.clone();
                    prog.#cat_lower.push((initial.clone(),));
                    #seed_step_term
                }
            }
        })
        .collect();

    // Stage 3.13d (2026-05-01) — Bug B fix: WPDS double-seed avoidance.
    //
    // When the pre-stratum is present, `seed_from_pre_stratum` (built below
    // at ~:2113) unconditionally pushes every `pre.<cat>` entry into
    // `prog.<cat>` via the carry-over loop:
    //   `for (t,) in pre.<cat>.iter() { prog.<cat>.push((t.clone(),)); }`
    // The pre-stratum itself is seeded with `initial` for the input
    // category at the `#pre_seed_arms` match (~:2148). So the input
    // arrives in `prog.<cat>` via pre + carry-over with NO need for the
    // direct `match term_ref { #(#seed_arms)* … }` push that follows
    // each `#pre_stratum_block`.
    //
    // Pre-3.13d both pushes ran, depositing two byte-identical tuples
    // into Ascent's `Vec`-backed `relation foo(T)` storage (which does
    // NOT dedup at push-time — only at rule-application via index
    // hashing). Result: `AscentResults.all_terms` contained 2 entries
    // with identical `term_id`.
    //
    // Post-3.13d: when pre-stratum is present, suppress the direct
    // match. When it's absent (no carry-over), keep the direct match.
    let prog_seed_match: TokenStream = if pre_stratum_content.is_some() {
        quote! {}
    } else {
        quote! {
            // Phase D.1 (2026-05-17, M13.2): iterate ALL parse alternatives
            // instead of seeding only the first (the pre-D.1 peel collapsed
            // to alts[0], discarding the rest — a P1 violation).
            // `all_alts()` returns a single-element vec for non-Ambiguous
            // terms and N-element vec for `Ambiguous(Vec<_>)`. The flat
            // shape (no nested Ambiguous) is enforced by from_alternatives.
            for __alt in term.0.all_alts() {
                match __alt {
                    #(#seed_arms)*
                    #inner_enum_name::Ambiguous(_) => unreachable!(
                        "all_alts() returns flat alternatives, not nested Ambiguous"
                    ),
                }
            }
        }
    };

    // Phase D.6/D.7 (2026-05-17): per-cat extract bodies feeding shared
    // accumulators — used by the Ambiguous union-extract block below to
    // emit results from EVERY category in scope, not just the first
    // alt's category. Pre-Phase-D the Ambiguous arm was `unreachable!()`
    // because the peel canonicalized to a single alt before dispatch;
    // with Phase D.1's all-alts seeding, every category's relations
    // may carry results, so the extract must read from all of them.
    let multi_cat_union_extract_blocks: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
            let rw_rel = format_ident!("rw_{}", cat.to_string().to_lowercase());
            let eq_ind = format_ident!("__eq_{}_ind_common", cat.to_string().to_lowercase());
            let variant = format_ident!("{}", cat);
            quote! {
                {
                    let all_terms_cat: Vec<#cat> = prog.#cat_lower
                        .iter()
                        .map(|(p,)| p.clone())
                        .collect();
                    let rewrites_cat: Vec<(#cat, #cat)> = prog.#rw_rel
                        .iter()
                        .map(|(from, to)| (from.clone(), to.clone()))
                        .collect();
                    for t in &all_terms_cat {
                        let wrapped = #inner_enum_name::#variant(t.clone());
                        let term_id = {
                            use std::collections::hash_map::DefaultHasher;
                            use std::hash::{Hash, Hasher};
                            let mut hasher = DefaultHasher::new();
                            wrapped.hash(&mut hasher);
                            hasher.finish()
                        };
                        // Stage 3.13d Bug B (2026-05-29): cross-category
                        // observational-equivalence dedup. The parser can
                        // preserve TWO alts that are the SAME source term up
                        // to a transparent identity cast (e.g. `2.0 + 2.5`
                        // parses to BOTH `Float::AddFloat(..)` AND
                        // `Proc::ProcFloat(AddFloat(..))`). `ProcFloat` is a
                        // transparent projection wrapper, so both produce
                        // the SAME `semantic_hash` (observational equivalence
                        // under Ascent's rewrite relation; the wrapper has no
                        // syntax / no action). Collapsing them keeps
                        // `all_terms` free of these cross-cat duplicates
                        // WITHOUT collapsing evaluatively-distinct alts: the
                        // `-3!` pair `Int::Fact(NumLit(-3))` (evals "error")
                        // vs `Int::Neg(Fact(NumLit(3)))` (evals "-6") carry
                        // DIFFERENT semantic_hashes (`Fact`/`Neg` are
                        // non-transparent → discriminants emitted) and so are
                        // BOTH retained. This is observational dedup, not
                        // Display dedup. Equivalent terms share NF status
                        // (transparent casts are pure identity), so keeping
                        // the first-seen representative is sound.
                        let __sem_key = {
                            use std::hash::Hasher;
                            let mut __h = std::collections::hash_map::DefaultHasher::new();
                            t.semantic_hash(&mut __h);
                            __h.finish()
                        };
                        if !__seen_sem.insert(__sem_key) {
                            continue;
                        }
                        let has_rewrites = rewrites_cat.iter().any(|(from, _)| from == t);
                        __all_term_infos.push(mettail_runtime::TermInfo {
                            term_id,
                            display: format!("{}", t),
                            is_normal_form: !has_rewrites,
                        });
                    }
                    for (from, to) in &rewrites_cat {
                        use std::collections::hash_map::DefaultHasher;
                        use std::hash::{Hash, Hasher};
                        let w_from = #inner_enum_name::#variant(from.clone());
                        let w_to = #inner_enum_name::#variant(to.clone());
                        let mut h1 = DefaultHasher::new();
                        let mut h2 = DefaultHasher::new();
                        w_from.hash(&mut h1);
                        w_to.hash(&mut h2);
                        __all_rewrites.push(mettail_runtime::Rewrite {
                            from_id: h1.finish(),
                            to_id: h2.finish(),
                            rule_name: Some("rewrite".to_string()),
                        });
                    }
                    {
                        use std::collections::hash_map::DefaultHasher;
                        use std::collections::{HashMap, HashSet};
                        use std::hash::{Hash, Hasher};
                        let hash_of = |t: &#cat| -> u64 {
                            let wrapped = #inner_enum_name::#variant(t.clone());
                            let mut h = DefaultHasher::new();
                            wrapped.hash(&mut h);
                            h.finish()
                        };
                        let mut classes: HashMap<u64, HashSet<u64>> = HashMap::new();
                        for ((a, b), _) in ascent::internal::RelIndexReadAll::iter_all(&prog.#eq_ind) {
                            let ha = hash_of(a);
                            let hb = hash_of(b);
                            if ha != hb {
                                classes.entry(ha).or_default().insert(hb);
                                classes.entry(hb).or_default().insert(ha);
                            }
                        }
                        let mut seen: HashSet<u64> = HashSet::new();
                        for (id, peers) in &classes {
                            if seen.contains(id) { continue; }
                            let mut class: HashSet<u64> = peers.clone();
                            class.insert(*id);
                            for &member in &class { seen.insert(member); }
                            if class.len() > 1 {
                                __all_equivalences.push(mettail_runtime::EquivClass {
                                    term_ids: class.into_iter().collect(),
                                });
                            }
                        }
                    }
                }
            }
        })
        .collect();

    // Phase D union-extract block: invoked from the Ambiguous arm to
    // gather results from every category in scope. Custom relation
    // extraction stays single-cat (custom_relations is a HashMap and
    // its extraction routine reads from the active prog regardless of
    // dispatch-cat).
    let multi_cat_union_extract: TokenStream = quote! {
        {
            let mut __all_term_infos: Vec<mettail_runtime::TermInfo> = Vec::new();
            let mut __all_rewrites: Vec<mettail_runtime::Rewrite> = Vec::new();
            let mut __all_equivalences: Vec<mettail_runtime::EquivClass> = Vec::new();
            // Stage 3.13d Bug B (2026-05-29): shared cross-category
            // observational-equivalence dedup set (semantic_hash keys). See
            // the per-category push site below for rationale and the `-3!`
            // safety argument.
            let mut __seen_sem: std::collections::HashSet<u64> = std::collections::HashSet::new();
            let mut custom_relations = std::collections::HashMap::new();
            #custom_relation_extraction
            #(#multi_cat_union_extract_blocks)*
            mettail_runtime::AscentResults {
                all_terms: __all_term_infos,
                rewrites: __all_rewrites,
                equivalences: __all_equivalences,
                custom_relations,
            }
        }
    };

    // Extract arms: read results from the appropriate relation after Ascent fixpoint.
    // Term IDs must match the wrapper's term_id() which hashes the inner enum (e.g. CalculatorTermInner::Str(t)),
    // so we hash the enum variant wrapping each term for TermInfo and Rewrite.
    // NOTE (2026-05-28): superseded by `multi_cat_union_extract` (the dispatch
    // arms now always use the all-categories union extract to surface
    // cross-category reduction products). Kept (underscore-prefixed) rather
    // than deleted; candidate for a cleanup substage.
    let _extract_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
            let rw_rel = format_ident!("rw_{}", cat.to_string().to_lowercase());
            let eq_ind = format_ident!("__eq_{}_ind_common", cat.to_string().to_lowercase());
            let variant = format_ident!("{}", cat);
            quote! {
                #inner_enum_name::#variant(_) => {
                    let all_terms: Vec<#cat> = prog.#cat_lower.iter().map(|(p,)| p.clone()).collect();
                    let rewrites: Vec<(#cat, #cat)> = prog.#rw_rel.iter().map(|(from, to)| (from.clone(), to.clone())).collect();
                    let term_infos: Vec<mettail_runtime::TermInfo> = all_terms.iter().map(|t| {
                        let wrapped = #inner_enum_name::#variant(t.clone());
                        let term_id = { use std::collections::hash_map::DefaultHasher; use std::hash::{Hash, Hasher}; let mut hasher = DefaultHasher::new(); wrapped.hash(&mut hasher); hasher.finish() };
                        let has_rewrites = rewrites.iter().any(|(from, _)| from == t);
                        mettail_runtime::TermInfo { term_id, display: format!("{}", t), is_normal_form: !has_rewrites }
                    }).collect();
                    let rewrite_list: Vec<mettail_runtime::Rewrite> = rewrites.iter().map(|(from, to)| {
                        use std::collections::hash_map::DefaultHasher; use std::hash::{Hash, Hasher};
                        let w_from = #inner_enum_name::#variant(from.clone());
                        let w_to = #inner_enum_name::#variant(to.clone());
                        let mut h1 = DefaultHasher::new(); let mut h2 = DefaultHasher::new();
                        w_from.hash(&mut h1); w_to.hash(&mut h2);
                        mettail_runtime::Rewrite { from_id: h1.finish(), to_id: h2.finish(), rule_name: Some("rewrite".to_string()) }
                    }).collect();
                    let equivalences = {
                        use std::collections::hash_map::DefaultHasher;
                        use std::collections::{HashMap, HashSet};
                        use std::hash::{Hash, Hasher};
                        let hash_of = |t: &#cat| -> u64 {
                            let wrapped = #inner_enum_name::#variant(t.clone());
                            let mut h = DefaultHasher::new();
                            wrapped.hash(&mut h);
                            h.finish()
                        };
                        let mut classes: HashMap<u64, HashSet<u64>> = HashMap::new();
                        for ((a, b), _) in ascent::internal::RelIndexReadAll::iter_all(&prog.#eq_ind) {
                            let ha = hash_of(a);
                            let hb = hash_of(b);
                            if ha != hb {
                                classes.entry(ha).or_default().insert(hb);
                                classes.entry(hb).or_default().insert(ha);
                            }
                        }
                        let mut seen: HashSet<u64> = HashSet::new();
                        let mut result = Vec::new();
                        for (id, peers) in &classes {
                            if seen.contains(id) { continue; }
                            let mut class: HashSet<u64> = peers.clone();
                            class.insert(*id);
                            for &member in &class { seen.insert(member); }
                            if class.len() > 1 {
                                result.push(mettail_runtime::EquivClass { term_ids: class.into_iter().collect() });
                            }
                        }
                        result
                    };
                    let mut custom_relations = std::collections::HashMap::new();
                    #custom_relation_extraction
                    mettail_runtime::AscentResults { all_terms: term_infos, rewrites: rewrite_list, equivalences, custom_relations }
                }
            }
        })
        .collect();

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

    // Generate the core Ascent struct if core content is available.
    // The core struct has fewer rules (only for core categories) but ALL relation
    // declarations, so it compiles correctly. Non-core relations remain empty.
    // F2: Core struct also switches between ascent!/ascent_par! via cfg.
    let core_struct_def = core_raw_ascent_content.map(|core_content| {
        let core_prog_name = format_ident!("{}AscentProgCore", name);
        generate_ascent_struct(&core_prog_name, core_content)
    });

    // Sprint 5: Generate pre-stratum struct if ground HOL step rules exist
    // F2: Pre-stratum also switches between ascent!/ascent_par! via cfg.
    let pre_stratum_struct_name = format_ident!("{}AscentProgPreStratum", name);
    let pre_stratum_struct_def = pre_stratum_content
        .map(|content| generate_ascent_struct(&pre_stratum_struct_name, content));

    // Sprint 5: Generate pre-stratum run + seed blocks (used in run_ascent_typed)
    let (pre_stratum_block, seed_from_pre_stratum) = if pre_stratum_content.is_some() {
        // Pre-stratum seed arms: same as main but targeting `pre` variable
        let pre_seed_arms: Vec<TokenStream> = language
            .types
            .iter()
            .map(|t| {
                let cat = &t.name;
                let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
                let variant = format_ident!("{}", cat);
                let seed_step = primary_type_for_step
                    .map(|pt| {
                        if pt == cat {
                            quote! { pre.step_term.push((initial.clone(),)); }
                        } else {
                            quote! {}
                        }
                    })
                    .unwrap_or_default();
                quote! {
                    #inner_enum_name::#variant(inner) => {
                        let initial = inner.clone();
                        pre.#cat_lower.push((initial.clone(),));
                        #seed_step
                    }
                }
            })
            .collect();

        // Phase D.1 (2026-05-17, M13.2): pre-stratum seed iterates ALL
        // parse alternatives. Pre-D.1 the block used `match term_ref` on
        // the post-peel single-alt term; that path discarded N-1 alts.
        // The new path matches each alt independently so the pre-stratum
        // ascent considers every alternative's grounds.
        let block = quote! {
            let mut pre = #pre_stratum_struct_name::default();
            for __alt in term.0.all_alts() {
                match __alt {
                    #(#pre_seed_arms)*
                    #inner_enum_name::Ambiguous(_) => {},
                }
            }
            pre.run();
        };

        // Seed main struct from pre-stratum results (all categories)
        let seed_lines: Vec<TokenStream> = language
            .types
            .iter()
            .map(|t| {
                let cat_lower = format_ident!("{}", t.name.to_string().to_lowercase());
                let rw_rel = format_ident!("rw_{}", t.name.to_string().to_lowercase());
                quote! {
                    for (t,) in pre.#cat_lower.iter() {
                        prog.#cat_lower.push((t.clone(),));
                    }
                    for (s, t) in pre.#rw_rel.iter() {
                        prog.#rw_rel.push((s.clone(), t.clone()));
                    }
                }
            })
            .collect();
        let seed = quote! { #(#seed_lines)* };

        (block, seed)
    } else {
        (quote! {}, quote! {})
    };

    // Sprint 6g/6h: Per-stratum Ascent struct definitions + chaining.
    //
    // When the grammar is large enough that a single `AscentProg::run()` would
    // overflow the default thread stack, `generate_stratified_content` peels
    // dense dependency groups out into dedicated Ascent structs. Here we emit
    // one named `ascent!` struct per stratum (`{Name}AscentProgStratum{i}`)
    // and chain their runs between pre-stratum and main:
    //
    //     pre.run()     → stratum_0.run() → … → stratum_N.run() → prog.run()
    //
    // Each step seeds the next struct's relations from all prior results so
    // downstream rules see the full set of derived facts. Datalog monotonicity
    // guarantees the sequence computes the same least fixpoint the monolithic
    // run would have produced.
    let stratum_struct_names: Vec<syn::Ident> = (0..stratum_contents.len())
        .map(|i| format_ident!("{}AscentProgStratum{}", name, i))
        .collect();

    let stratum_struct_defs: Vec<TokenStream> = stratum_contents
        .iter()
        .zip(stratum_struct_names.iter())
        .map(|(stratum, struct_name)| generate_ascent_struct(struct_name, &stratum.raw_content))
        .collect();

    // Emit a helper to copy category / eq_cat / rw_cat / fold_cat / step_term
    // relations from a source Ascent struct into a target one. Relation names
    // and arities are shared across strata (Ascent requires matching schemas),
    // so the same loop body works for every pair. Copying `eq_` + `rw_`
    // + `fold_` prevents main-stage rules whose bodies join on those relations
    // from missing sub-stratum outputs; copying `step_term` keeps HOL step
    // rules firing in sub-strata that target non-primary categories.
    let copy_all_relations_from_src = |src: TokenStream, dst: TokenStream| -> TokenStream {
        let per_cat: Vec<TokenStream> = language
            .types
            .iter()
            .map(|t| {
                let cat = &t.name;
                let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
                let eq_rel = format_ident!("eq_{}", cat.to_string().to_lowercase());
                let rw_rel = format_ident!("rw_{}", cat.to_string().to_lowercase());
                let fold_rel = format_ident!("fold_{}", cat.to_string().to_lowercase());
                // fold_<cat> is only declared when the category has fold-mode
                // rules — mirror the relation-emission gate from logic/relations.rs:204-217.
                let has_fold_as_result = language.terms.iter().any(|r| {
                    r.category == *cat && r.eval_mode == Some(mettail_ast::types::EvalMode::Fold)
                });
                let has_fold_as_param = language.terms.iter().any(|r| {
                    r.eval_mode == Some(mettail_ast::types::EvalMode::Fold)
                        && r.term_context.as_ref().is_some_and(|ctx| {
                            ctx.iter().any(|p| match p {
                                mettail_ast::grammar::TermParam::Simple {
                                    ty: mettail_ast::types::TypeExpr::Base(ref id),
                                    ..
                                } => id == cat,
                                _ => false,
                            })
                        })
                });
                let has_fold = has_fold_as_result || has_fold_as_param;
                let fold_copy = if has_fold {
                    quote! {
                        for (a, b) in #src.#fold_rel.iter() {
                            #dst.#fold_rel.push((a.clone(), b.clone()));
                        }
                    }
                } else {
                    quote! {}
                };
                quote! {
                    for (t,) in #src.#cat_lower.iter() {
                        #dst.#cat_lower.push((t.clone(),));
                    }
                    for (a, b) in #src.#eq_rel.iter() {
                        #dst.#eq_rel.push((a.clone(), b.clone()));
                    }
                    for (s, t) in #src.#rw_rel.iter() {
                        #dst.#rw_rel.push((s.clone(), t.clone()));
                    }
                    #fold_copy
                }
            })
            .collect();
        // step_term is declared only for the primary category but is global to
        // the struct; both source and target have it (matching schemas).
        let step_term_copy = quote! {
            for (t,) in #src.step_term.iter() {
                #dst.step_term.push((t.clone(),));
            }
        };
        quote! { #(#per_cat)* #step_term_copy }
    };

    // Run all sub-strata in sequence, seeding each from pre + prior strata.
    // Emits: `let mut s{i} = {Name}StratumI::default(); <seed from pre>; <seed from s0..s{i-1}>; s{i}.run();`
    let stratum_run_block: TokenStream = {
        let mut per_stratum = Vec::new();
        for (i, struct_name) in stratum_struct_names.iter().enumerate() {
            let s_ident = format_ident!("s{}", i);
            let seed_from_pre = if pre_stratum_content.is_some() {
                copy_all_relations_from_src(quote! { pre }, quote! { #s_ident })
            } else {
                quote! {}
            };
            let seed_from_priors: Vec<TokenStream> = (0..i)
                .map(|j| {
                    let prior = format_ident!("s{}", j);
                    copy_all_relations_from_src(quote! { #prior }, quote! { #s_ident })
                })
                .collect();
            per_stratum.push(quote! {
                let mut #s_ident = #struct_name::default();
                #seed_from_pre
                #(#seed_from_priors)*
                #s_ident.run();
            });
        }
        quote! { #(#per_stratum)* }
    };

    // Additional seeding of the main `prog` from each sub-stratum.
    let seed_main_from_strata: TokenStream = {
        let per_stratum: Vec<TokenStream> = stratum_struct_names
            .iter()
            .enumerate()
            .map(|(i, _)| {
                let s_ident = format_ident!("s{}", i);
                copy_all_relations_from_src(quote! { #s_ident }, quote! { prog })
            })
            .collect();
        quote! { #(#per_stratum)* }
    };

    // B-CG04: Ground rewrite seed block for multi-category struct
    let ground_seed_block_multi = if ground_rewrite_seeds.is_empty() {
        quote! {}
    } else {
        quote! {
            // B-CG04: Seed statically known ground rewrite results at initialization.
            // These rewrites have fully ground LHS patterns, so their results are
            // available without per-iteration equation scanning.
            #(#ground_rewrite_seeds)*
        }
    };

    // A-RT05: Generate per-category depth check lines for multi-category languages.
    // Each line computes max term_depth() across all terms in that category's relation.
    let depth_check_lines: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat_lower = format_ident!("{}", t.name.to_string().to_lowercase());
            quote! {
                for (__t,) in prog.#cat_lower.iter() {
                    let __d = __t.term_depth();
                    if __d > __rt05_max_depth {
                        __rt05_max_depth = __d;
                    }
                }
            }
        })
        .collect();
    let depth_check_block = quote! {
        {
            let mut __rt05_max_depth: u32 = 0;
            #(#depth_check_lines)*
            if __rt05_max_depth > Self::MAX_FIXPOINT_TERM_DEPTH {
                eprintln!(
                    "warning[A-RT05]: fixpoint produced term of depth {} (threshold: {}); \
                     possible non-convergence from depth-increasing rules",
                    __rt05_max_depth,
                    Self::MAX_FIXPOINT_TERM_DEPTH,
                );
            }
        }
    };

    // Build dispatcher: core-category inputs use the core struct (if available),
    // non-core inputs use the full struct.
    let core_prog_name = format_ident!("{}AscentProgCore", name);
    let core_cats = crate::logic::common::compute_core_categories(language);

    let run_ascent_body = if core_raw_ascent_content.is_some() {
        // SCC-split dispatcher: core categories → core struct, others → full struct
        let core_cats_ref = core_cats
            .as_ref()
            .expect("core_raw_content implies core_cats");

        // Build seed+extract arms for core struct (same logic, different prog type)
        let core_seed_arms: Vec<TokenStream> = language
            .types
            .iter()
            .filter(|t| core_cats_ref.contains(&t.name.to_string()))
            .map(|t| {
                let cat = &t.name;
                let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
                let variant = format_ident!("{}", cat);
                let seed_step_term = primary_type_for_step
                    .map(|pt| {
                        if pt == cat {
                            quote! { prog.step_term.push((initial.clone(),)); }
                        } else {
                            quote! {}
                        }
                    })
                    .unwrap_or_default();
                quote! {
                    #inner_enum_name::#variant(inner) => {
                        let initial = inner.clone();
                        prog.#cat_lower.push((initial.clone(),));
                        #seed_step_term
                    }
                }
            })
            .collect();

        // Stage 3.13d (2026-05-01) — Bug B fix: parallel of `prog_seed_match`
        // for the SCC-split core struct. Same rationale: when pre-stratum
        // is present, the `seed_from_pre_stratum` carry-over loop covers
        // seeding for core categories too; suppress the direct match.
        let core_prog_seed_match: TokenStream = if pre_stratum_content.is_some() {
            quote! {}
        } else {
            quote! {
                // Phase D.1 (2026-05-17, M13.2): iterate ALL alternatives
                // for the core-struct path (parallel of prog_seed_match).
                for __alt in term.0.all_alts() {
                    match __alt {
                        #(#core_seed_arms)*
                        _ => {
                            // Non-core variant or Ambiguous — silently
                            // skip (the alt belongs to a category routed
                            // to the full struct via the outer dispatch).
                        }
                    }
                }
            }
        };

        // NOTE (2026-05-28): superseded by `multi_cat_union_extract` — see the
        // _extract_arms note above. Kept underscore-prefixed, not deleted.
        let _core_extract_arms: Vec<TokenStream> = language
            .types
            .iter()
            .filter(|t| core_cats_ref.contains(&t.name.to_string()))
            .map(|t| {
                let cat = &t.name;
                let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
                let rw_rel = format_ident!("rw_{}", cat.to_string().to_lowercase());
                let eq_ind = format_ident!("__eq_{}_ind_common", cat.to_string().to_lowercase());
                let variant = format_ident!("{}", cat);
                quote! {
                    #inner_enum_name::#variant(_) => {
                        let all_terms: Vec<#cat> = prog.#cat_lower.iter().map(|(p,)| p.clone()).collect();
                        let rewrites: Vec<(#cat, #cat)> = prog.#rw_rel.iter().map(|(from, to)| (from.clone(), to.clone())).collect();
                        let term_infos: Vec<mettail_runtime::TermInfo> = all_terms.iter().map(|t| {
                            let wrapped = #inner_enum_name::#variant(t.clone());
                            let term_id = { use std::collections::hash_map::DefaultHasher; use std::hash::{Hash, Hasher}; let mut hasher = DefaultHasher::new(); wrapped.hash(&mut hasher); hasher.finish() };
                            let has_rewrites = rewrites.iter().any(|(from, _)| from == t);
                            mettail_runtime::TermInfo { term_id, display: format!("{}", t), is_normal_form: !has_rewrites }
                        }).collect();
                        let rewrite_list: Vec<mettail_runtime::Rewrite> = rewrites.iter().map(|(from, to)| {
                            use std::collections::hash_map::DefaultHasher; use std::hash::{Hash, Hasher};
                            let w_from = #inner_enum_name::#variant(from.clone());
                            let w_to = #inner_enum_name::#variant(to.clone());
                            let mut h1 = DefaultHasher::new(); let mut h2 = DefaultHasher::new();
                            w_from.hash(&mut h1); w_to.hash(&mut h2);
                            mettail_runtime::Rewrite { from_id: h1.finish(), to_id: h2.finish(), rule_name: Some("rewrite".to_string()) }
                        }).collect();
                        let equivalences = {
                            use std::collections::hash_map::DefaultHasher;
                            use std::collections::{HashMap, HashSet};
                            use std::hash::{Hash, Hasher};
                            let hash_of = |t: &#cat| -> u64 {
                                let wrapped = #inner_enum_name::#variant(t.clone());
                                let mut h = DefaultHasher::new();
                                wrapped.hash(&mut h);
                                h.finish()
                            };
                            let mut classes: HashMap<u64, HashSet<u64>> = HashMap::new();
                            for ((a, b), _) in ascent::internal::RelIndexReadAll::iter_all(&prog.#eq_ind) {
                                let ha = hash_of(a);
                                let hb = hash_of(b);
                                if ha != hb {
                                    classes.entry(ha).or_default().insert(hb);
                                    classes.entry(hb).or_default().insert(ha);
                                }
                            }
                            let mut seen: HashSet<u64> = HashSet::new();
                            let mut result = Vec::new();
                            for (id, peers) in &classes {
                                if seen.contains(id) { continue; }
                                let mut class: HashSet<u64> = peers.clone();
                                class.insert(*id);
                                for &member in &class { seen.insert(member); }
                                if class.len() > 1 {
                                    result.push(mettail_runtime::EquivClass { term_ids: class.into_iter().collect() });
                                }
                            }
                            result
                        };
                        let mut custom_relations = std::collections::HashMap::new();
                        #custom_relation_extraction
                        mettail_runtime::AscentResults { all_terms: term_infos, rewrites: rewrite_list, equivalences, custom_relations }
                    }
                }
            })
            .collect();

        // Core category variant patterns (for the match guard)
        let core_variant_patterns: Vec<TokenStream> = language
            .types
            .iter()
            .filter(|t| core_cats_ref.contains(&t.name.to_string()))
            .map(|t| {
                let variant = format_ident!("{}", t.name);
                quote! { #inner_enum_name::#variant(_) }
            })
            .collect();

        quote! {
            // Phase D (2026-05-17): Ambiguous-first dispatch.
            //
            // When `term.0` is `Ambiguous`, the input represents N parse
            // alternatives that may span MULTIPLE categories. The core
            // struct only has relations for core categories — using it
            // would silently drop any alt in a non-core cat. Route
            // Ambiguous to the FULL struct (which has all relations)
            // and use the union extract to gather results from every
            // category's relation.
            //
            // Non-Ambiguous inputs follow the pre-Phase-D core-vs-full
            // dispatch keyed on the single category's variant.
            if matches!(&term.0, #inner_enum_name::Ambiguous(_)) {
                #pre_stratum_block
                #stratum_run_block
                let mut prog = #prog_struct_name::default();
                #prog_seed_match
                #seed_from_pre_stratum
                #seed_main_from_strata
                #ground_seed_block_multi
                prog.run();
                #depth_check_block
                return #multi_cat_union_extract;
            }
            let term_ref = &term.0;
            match term_ref {
                // Already filtered above by the Ambiguous-first dispatch.
                #inner_enum_name::Ambiguous(_) => unreachable!(
                    "run_ascent_typed: Ambiguous already routed by Phase D dispatch"
                ),
                // Core categories: use the smaller core struct (fewer SCC rules)
                #(#core_variant_patterns)|* => {
                    #pre_stratum_block
                    #stratum_run_block
                    let mut prog = #core_prog_name::default();
                    #core_prog_seed_match
                    #seed_from_pre_stratum
                    #seed_main_from_strata
                    #ground_seed_block_multi
                    prog.run();
                    // A-RT05: Post-fixpoint depth check
                    #depth_check_block
                    // Cross-category eval fix (2026-05-28): union extract
                    // across ALL categories (see non-split branch). The core
                    // struct declares the full relation schema, so the union
                    // extract compiles here too. #core_extract_arms superseded.
                    #multi_cat_union_extract
                }
                // Non-core categories: use the full struct (all rules)
                _ => {
                    #pre_stratum_block
                    #stratum_run_block
                    let mut prog = #prog_struct_name::default();
                    #prog_seed_match
                    #seed_from_pre_stratum
                    #seed_main_from_strata
                    #ground_seed_block_multi
                    prog.run();
                    // A-RT05: Post-fixpoint depth check
                    #depth_check_block
                    // Cross-category eval fix (2026-05-28): union extract
                    // across ALL categories (see non-split branch).
                    #multi_cat_union_extract
                }
            }
        }
    } else {
        // Single struct (no SCC splitting) — Phase D Ambiguous-aware
        // dispatch. There's only one prog struct (#prog_struct_name)
        // so dispatch is simpler: always run the same struct; pick
        // extract based on whether the input is Ambiguous.
        quote! {
            #pre_stratum_block
            #stratum_run_block
            let mut prog = #prog_struct_name::default();
            #prog_seed_match
            #seed_from_pre_stratum
            #seed_main_from_strata
            #ground_seed_block_multi
            prog.run();
            // A-RT05: Post-fixpoint depth check
            #depth_check_block
            // Cross-category eval fix (2026-05-28): ALWAYS use the
            // all-categories union extract, not only for Ambiguous inputs.
            // The per-category single-relation #extract_arms harvested normal
            // forms + rewrites from ONLY the input term's own category
            // relation, silently dropping cross-category reduction products
            // that land in a DIFFERENT relation (e.g. ledtest AndPred→Pred in
            // a Num-primary language; calculator Len→Int in a Proc-primary
            // language). The union extract reads every category relation;
            // is_normal_form stays correct (a term carrying a rewrite edge in
            // ANY relation is not a normal form in its own). Safe: all op-test
            // assertions use .any()/!is_empty() (monotone in the nf set), so
            // reporting additional cross-cat forms cannot break a passing test.
            #multi_cat_union_extract
        }
    };

    // Optionally emit the core struct definition
    let core_struct_output = core_struct_def.unwrap_or_default();
    // Optionally emit the pre-stratum struct definition (Sprint 5)
    let pre_stratum_struct_output = pre_stratum_struct_def.unwrap_or_default();
    // Sprint 6g/6h: Per-stratum struct defs (zero or more).
    let stratum_struct_output: TokenStream = quote! { #(#stratum_struct_defs)* };

    // F2: Generate cfg-gated ascent struct (ascent! vs ascent_par!)
    let prog_struct_def = generate_ascent_struct(&prog_struct_name, raw_ascent_content);

    quote! {
        #prog_struct_def

        #core_struct_output

        #pre_stratum_struct_output

        #stratum_struct_output

        /// Language implementation struct (multi-category: one parser/relation per type).
        pub struct #language_name;

        thread_local! {
            /// WFST weights for NFA-ambiguous alternatives, parallel to the `successes`
            /// vec in `parse_preserving_vars`. Set before `from_alternatives` so it can
            /// use weights as tiebreaker when multiple alternatives are accepting.
            static AMBIGUOUS_WEIGHTS: std::cell::Cell<Vec<f64>> =
                std::cell::Cell::new(Vec::new());

            /// C1: Accumulated weight corrections from semantic disambiguation.
            /// When `from_alternatives` selects a non-weight-best alternative
            /// (because only it was accepting or because semantic tiebreaking
            /// overrode the WFST ordering), a `WeightCorrection` is recorded.
            ///
            /// Drain via `drain_weight_corrections()` after each parse to
            /// collect feedback for offline weight training.
            static WEIGHT_CORRECTIONS: std::cell::Cell<Vec<mettail_prattail::wfst::WeightCorrection>> =
                std::cell::Cell::new(Vec::new());
        }

        impl #language_name {
            /// A-RT05: Maximum term depth threshold for post-fixpoint convergence check.
            ///
            /// If any term in the fixpoint result exceeds this depth, a warning is
            /// emitted to stderr. This catches pathological grammars where depth-increasing
            /// rules cause unbounded term growth.
            const MAX_FIXPOINT_TERM_DEPTH: u32 = 100;

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
                let mut success_weights: Vec<f64> = Vec::new();
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
                        let mut filtered_weights = Vec::with_capacity(success_weights.len());
                        for (s, w) in successes.into_iter().zip(success_weights.into_iter()) {
                            if !s.is_uniformly_auto_injected() {
                                filtered.push(s);
                                filtered_weights.push(w);
                            }
                        }
                        successes = filtered;
                        success_weights = filtered_weights;
                    }
                }
                // Display-based dedup (2026-05-18, replicated-conjuring-turtle.md
                // follow-up): the WPDS parser can produce structurally-distinct
                // alternatives whose Display output is identical (e.g.,
                // rhocalc `{true and true}` produces 9 alts from lex-ambiguity
                // of `true`/`and` between Ident and keyword). Feeding the
                // duplicates into Ascent caused exponential fixpoint blowup —
                // diagnosed empirically at `docs/design/notes/2026-05-18-
                // cursor-explosion-rhocalc.md`. Dedup by Display string;
                // first occurrence wins (and its WFST weight is kept).
                //
                // Rationale: structurally-distinct-but-display-identical alts
                // represent the SAME semantic parse with different lex paths
                // through ambiguous keyword/identifier dispatches. The Ascent
                // evaluator is display-driven (normal_forms compared by
                // display string), so display-identical alts are
                // semantically indistinguishable to it. Per
                // `feedback_never_disambiguate_early.md` this is NOT
                // weight-based pruning — equivalent terms collapse by
                // observational equivalence, which is the principled
                // ambiguity-resolution mechanism (Tomita 1986 §6.3 SPPF
                // Symbol-dedup, lifted from SPPF nodes to user-AST terms).
                // Phase F.13 Stage 2.2 (2026-05-22): structural
                // (Hash-based) dedup. Display equivalence is NOT
                // observational equivalence (see from_alternatives
                // commentary). `-3!` produces both
                // CalculatorTermInner::Int(Fact(NumLit(-3))) (evals
                // "error") and CalculatorTermInner::Int(Neg(Fact(NumLit(3))))
                // (evals "-6") — both display "-3!" but their ASTs
                // hash differently and BOTH must reach Ascent.
                if successes.len() > 1 {
                    let mut seen_hashes: std::collections::HashSet<u64> =
                        std::collections::HashSet::with_capacity(successes.len());
                    let mut deduped: Vec<_> = Vec::with_capacity(successes.len());
                    let mut deduped_weights: Vec<f64> = Vec::with_capacity(success_weights.len());
                    for (s, w) in successes.into_iter().zip(success_weights.into_iter()) {
                        use std::hash::Hasher;
                        let mut hasher = rustc_hash::FxHasher::default();
                        s.semantic_hash(&mut hasher);
                        let h = hasher.finish();
                        if seen_hashes.insert(h) {
                            deduped.push(s);
                            deduped_weights.push(w);
                        }
                    }
                    successes = deduped;
                    success_weights = deduped_weights;
                }
                match successes.len() {
                    0 => Err(first_err.unwrap_or_else(|| "Parse error".to_string())),
                    1 => Ok(#term_name(successes.into_iter().next().expect("checked len == 1"))),
                    _ => {
                        /* Set AMBIGUOUS_WEIGHTS thread-local so from_alternatives can use
                           WFST weights for tiebreaking when multiple alternatives are accepting. */
                        AMBIGUOUS_WEIGHTS.with(|cell| cell.set(success_weights));
                        Ok(#term_name(#inner_enum_name::from_alternatives(successes)))
                    }
                }
            }

            /// C1: Drain accumulated weight corrections from semantic disambiguation.
            ///
            /// Returns all `WeightCorrection` events recorded since the last drain.
            /// Call after each `parse()` to collect feedback for weight training:
            ///
            /// ```ignore
            /// let term = MyLanguage::parse("input")?;
            /// let corrections = MyLanguage::drain_weight_corrections();
            /// for c in &corrections {
            ///     eprintln!("WFST correction in {}: primary_w={}, selected_w={}, delta={}",
            ///               c.category, c.primary_weight, c.selected_weight, c.weight_delta());
            /// }
            /// ```
            ///
            /// The returned vec is empty when the WFST's weight ordering was correct
            /// for all disambiguation decisions in the most recent parse.
            pub fn drain_weight_corrections() -> Vec<mettail_prattail::wfst::WeightCorrection> {
                WEIGHT_CORRECTIONS.with(|cell| cell.take())
            }

            /// Run Ascent on a typed term (seeds the relation for the term's category).
            /// For Ambiguous terms, evaluates only the first alternative by declaration
            /// order. All alternatives that reach Stage C are valid parses, so evaluating
            /// only the first-declared is deterministic and avoids redundant Ascent runs.
            ///
            /// SCC splitting: when available, core-category inputs (e.g., Proc, Name) use
            /// a smaller Ascent struct with fewer rules, reducing fixpoint iteration cost.
            /// Non-core inputs (e.g., Float, Bool, Str) fall back to the full struct.
            pub fn run_ascent_typed(term: &#term_name) -> mettail_runtime::AscentResults {
                // Sprint B (R1): Clear term equality cache to prevent stale entries
                // from a previous evaluation affecting this fixpoint computation.
                mettail_runtime::clear_term_eq_cache();

                // BCG05 epoch: increment the runtime epoch counter so that BCG05
                // dedup HashSets in Ascent rule guards detect the new epoch and
                // clear themselves. Without this, hashes from a previous
                // run_ascent_typed() call persist and cause dedup guards to skip
                // rule firings for previously-seen terms.
                mettail_runtime::bump_bcg05_epoch();

                #run_ascent_body
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

    // CEK decomposition method
    let cek_decompose_method =
        generate_cek_decompose_single(&language_name, &term_name, primary_type, language);

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

            fn run_ascent(&self, term: &dyn mettail_runtime::Term) -> Result<mettail_runtime::AscentResults, std::string::String> {
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                Ok(#language_name::run_ascent_typed(typed_term))
            }

            fn run_ascent_with_facts(
                &self,
                term: &dyn mettail_runtime::Term,
                facts: &mettail_runtime::SeedFacts,
            ) -> Result<mettail_runtime::AscentResults, std::string::String> {
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;

                // Populate thread-local fact snapshot from SeedFacts.
                let mut __snapshot: std::collections::HashMap<
                    String,
                    std::collections::HashSet<Vec<String>>,
                > = std::collections::HashMap::new();
                for (rel_name, tuples) in facts {
                    let mut set = std::collections::HashSet::new();
                    for tuple in tuples {
                        set.insert(tuple.clone());
                    }
                    __snapshot.insert(rel_name.clone(), set);
                }
                mettail_runtime::set_pred_fact_snapshot(__snapshot);
                let result = #language_name::run_ascent_typed(typed_term);
                mettail_runtime::clear_pred_fact_snapshot();
                Ok(result)
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

            #cek_decompose_method
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

    // CEK decomposition method for multi-type
    let cek_decompose_method =
        generate_cek_decompose_multi(&language_name, &term_name, &inner_enum_name, language);

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
        quote! {}
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

            fn run_ascent(&self, term: &dyn mettail_runtime::Term) -> Result<mettail_runtime::AscentResults, std::string::String> {
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;
                Ok(#language_name::run_ascent_typed(typed_term))
            }

            fn run_ascent_with_facts(
                &self,
                term: &dyn mettail_runtime::Term,
                facts: &mettail_runtime::SeedFacts,
            ) -> Result<mettail_runtime::AscentResults, std::string::String> {
                let typed_term = term
                    .as_any()
                    .downcast_ref::<#term_name>()
                    .ok_or_else(|| format!("Expected {}", stringify!(#term_name)))?;

                // Populate thread-local fact snapshot from SeedFacts.
                let mut __snapshot: std::collections::HashMap<
                    String,
                    std::collections::HashSet<Vec<String>>,
                > = std::collections::HashMap::new();
                for (rel_name, tuples) in facts {
                    let mut set = std::collections::HashSet::new();
                    for tuple in tuples {
                        set.insert(tuple.clone());
                    }
                    __snapshot.insert(rel_name.clone(), set);
                }
                mettail_runtime::set_pred_fact_snapshot(__snapshot);
                let result = #language_name::run_ascent_typed(typed_term);
                mettail_runtime::clear_pred_fact_snapshot();
                Ok(result)
            }

            #try_direct_eval_method

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

            #cek_decompose_method
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CEK Decomposition Bridge Codegen
// ══════════════════════════════════════════════════════════════════════════════

/// Classification of a grammar rule for CEK decomposition.
enum CekRuleKind {
    /// Infix binary: `a OP b` → BinOp frame
    Infix { operator: String },
    /// Unary prefix: `OP a` → UnaryOp frame
    UnaryPrefix { operator: String },
    /// Unary postfix: `a OP` → UnaryOp frame (postfix)
    UnaryPostfix { operator: String },
    /// Collection with separator (e.g., `P | Q | ...`) → Parallel frame
    Collection { separator: String },
    /// Binder with body (e.g., `for(x <- n){p}`) → LetBody frame
    Binder,
    /// Atom: literal, variable, or unit → just set control
    Atom,
    /// N-ary / compound → set control to display (no special decomposition)
    Compound,
}

/// Classify a grammar rule for CEK decomposition purposes.
fn classify_rule_for_cek(rule: &GrammarRule) -> CekRuleKind {
    // New syntax: use term_context + syntax_pattern
    if let Some(ref term_context) = rule.term_context {
        // Count non-guard params
        let simple_count = term_context
            .iter()
            .filter(|p| matches!(p, mettail_ast::grammar::TermParam::Simple { .. }))
            .count();
        let has_abstraction = term_context.iter().any(|p| {
            matches!(
                p,
                mettail_ast::grammar::TermParam::Abstraction { .. }
                    | mettail_ast::grammar::TermParam::MultiAbstraction { .. }
            )
        });

        if has_abstraction {
            return CekRuleKind::Binder;
        }

        // Check for collection params (separator comes from syntax_pattern, not TypeExpr)
        // B9 / Class 2 (2026-05-08): only classify as Collection-kind when
        // the rule has EXACTLY one Simple param of Collection type — i.e.
        // a Class-5 collection-literal rule. Multi-Param Class-2 binder
        // rules with Vec/HashBag slots fall through to Compound, where
        // the default `(..)` pattern matches their multi-field tuple
        // variant correctly.
        if simple_count == 1 {
            for p in term_context {
                if let mettail_ast::grammar::TermParam::Simple { ty, .. } = p {
                    if let mettail_ast::types::TypeExpr::Collection { .. } = ty {
                        // Determine separator from syntax_pattern
                        let sep = rule
                            .syntax_pattern
                            .as_ref()
                            .and_then(|sp| {
                                sp.iter().find_map(|expr| {
                                    if let mettail_ast::grammar::SyntaxExpr::Op(
                                        mettail_ast::grammar::PatternOp::Sep { separator, .. },
                                    ) = expr
                                    {
                                        Some(separator.clone())
                                    } else {
                                        None
                                    }
                                })
                            })
                            .unwrap_or_default();
                        return CekRuleKind::Collection { separator: sep };
                    }
                }
            }
        }

        // Check syntax_pattern for operator terminals between params
        if let Some(ref syntax_pattern) = rule.syntax_pattern {
            // B9 / Class 2 (2026-05-08): exclude rules with a Collection-
            // typed Simple param from Infix classification. The Infix arm
            // emits `Proc::Label(f0, f1)` and calls `format!("{}", f1)`,
            // but f1 may be `Vec<Proc>` (or HashBag) which doesn't impl
            // Display. Class-2 binder rules fall through to Compound.
            let has_collection_param = term_context.iter().any(|p| {
                matches!(
                    p,
                    mettail_ast::grammar::TermParam::Simple {
                        ty: mettail_ast::types::TypeExpr::Collection { .. },
                        ..
                    }
                )
            });
            if simple_count == 2 && !has_collection_param {
                // Look for Terminal between the two param references
                for item in syntax_pattern {
                    if let mettail_ast::grammar::SyntaxExpr::Literal(op) = item {
                        return CekRuleKind::Infix { operator: op.clone() };
                    }
                }
            }
            if simple_count == 1 {
                // Check if first item is a terminal (unary prefix)
                if let Some(mettail_ast::grammar::SyntaxExpr::Literal(op)) = syntax_pattern.first()
                {
                    return CekRuleKind::UnaryPrefix { operator: op.clone() };
                }
                // Check if last item is a terminal (unary postfix)
                if let Some(mettail_ast::grammar::SyntaxExpr::Literal(op)) = syntax_pattern.last() {
                    return CekRuleKind::UnaryPostfix { operator: op.clone() };
                }
            }
        }

        if simple_count == 0 && !has_abstraction {
            return CekRuleKind::Atom;
        }
        return CekRuleKind::Compound;
    }

    // Old syntax: use items
    let nonterminals: Vec<_> = rule
        .items
        .iter()
        .filter(|i| matches!(i, GrammarItem::NonTerminal { .. }))
        .collect();
    let terminals: Vec<String> = rule
        .items
        .iter()
        .filter_map(|i| match i {
            GrammarItem::Terminal(s) => Some(s.clone()),
            _ => None,
        })
        .collect();
    let collections: Vec<_> = rule
        .items
        .iter()
        .filter(|i| matches!(i, GrammarItem::Collection { .. }))
        .collect();
    let has_binder = rule
        .items
        .iter()
        .any(|i| matches!(i, GrammarItem::Binder { .. }));

    if !collections.is_empty() {
        if let GrammarItem::Collection { separator, .. } = collections[0] {
            return CekRuleKind::Collection { separator: separator.clone() };
        }
    }

    if has_binder || !rule.bindings.is_empty() {
        return CekRuleKind::Binder;
    }

    if nonterminals.len() == 2 && !terminals.is_empty() {
        // Infix: pick the first terminal as operator
        return CekRuleKind::Infix { operator: terminals[0].clone() };
    }

    if nonterminals.len() == 1 && !terminals.is_empty() {
        // Check if terminal comes before or after the nonterminal
        if let Some(GrammarItem::Terminal(op)) = rule.items.first() {
            return CekRuleKind::UnaryPrefix { operator: op.clone() };
        }
        if let Some(GrammarItem::Terminal(op)) = rule.items.last() {
            return CekRuleKind::UnaryPostfix { operator: op.clone() };
        }
    }

    if nonterminals.is_empty() {
        return CekRuleKind::Atom;
    }

    CekRuleKind::Compound
}

/// Count the number of non-terminal / non-guard fields in a grammar rule.
/// This is the number of positional fields in the generated enum variant.
fn rule_field_count(rule: &GrammarRule) -> usize {
    if let Some(ref tc) = rule.term_context {
        // Opt-Group: count flat fields (each Optional inner contributes
        // one Option<Box<T>> field). Mirrors `convert_term_context_to_items`
        // and enums.rs flattening.
        fn count_one(p: &mettail_ast::grammar::TermParam) -> usize {
            use mettail_ast::grammar::TermParam;
            match p {
                TermParam::Simple { .. }
                | TermParam::MultiAbstraction { .. }
                | TermParam::Abstraction { .. } => 1,
                TermParam::GuardBody { .. } => 0,
                TermParam::Optional { params: inner } => inner.iter().map(count_one).sum(),
            }
        }
        tc.iter().map(count_one).sum()
    } else {
        rule.items
            .iter()
            .filter(|i| {
                matches!(i, GrammarItem::NonTerminal { .. } | GrammarItem::Collection { .. })
            })
            .count()
    }
}

/// Generate the `decompose_into_cek` method body for a single category.
///
/// Produces match arms for each grammar rule variant that push appropriate
/// `EvalFrame`s onto the evaluator's continuation stack.
fn generate_cek_decompose_arms(
    category: &syn::Ident,
    rules: &[&GrammarRule],
    _language: &LanguageDef,
) -> Vec<TokenStream> {
    let mut arms = Vec::new();

    for rule in rules {
        let label = &rule.label;
        let kind = classify_rule_for_cek(rule);
        let n_fields = rule_field_count(rule);

        match kind {
            CekRuleKind::Infix { operator } => {
                if n_fields == 2 {
                    let op_lit = LitStr::new(&operator, Span::call_site());
                    arms.push(quote! {
                        #category::#label(f0, f1) => {
                            evaluator.push_frame(mettail_runtime::EvalFrame::BinOp {
                                operator: #op_lit.to_string(),
                                lhs_display: format!("{}", f0),
                            });
                            evaluator.set_control(format!("{}", f1));
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        }
                    });
                } else {
                    // N-ary infix: fall through to display
                    arms.push(quote! {
                        #category::#label(..) => {
                            evaluator.set_control(format!("{}", term));
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        }
                    });
                }
            },
            CekRuleKind::UnaryPrefix { operator } => {
                let op_lit = LitStr::new(&operator, Span::call_site());
                if n_fields == 1 {
                    arms.push(quote! {
                        #category::#label(f0) => {
                            evaluator.push_frame(mettail_runtime::EvalFrame::UnaryOp {
                                operator: #op_lit.to_string(),
                            });
                            evaluator.set_control(format!("{}", f0));
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        }
                    });
                } else {
                    arms.push(quote! {
                        #category::#label(..) => {
                            evaluator.set_control(format!("{}", term));
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        }
                    });
                }
            },
            CekRuleKind::UnaryPostfix { operator } => {
                let op_lit = LitStr::new(&operator, Span::call_site());
                if n_fields == 1 {
                    arms.push(quote! {
                        #category::#label(f0) => {
                            evaluator.push_frame(mettail_runtime::EvalFrame::UnaryOp {
                                operator: #op_lit.to_string(),
                            });
                            evaluator.set_control(format!("{}", f0));
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        }
                    });
                } else {
                    arms.push(quote! {
                        #category::#label(..) => {
                            evaluator.set_control(format!("{}", term));
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        }
                    });
                }
            },
            CekRuleKind::Collection { separator } => {
                if separator == "|" {
                    // Parallel composition: decompose into Parallel frame.
                    // HashBag::iter() yields (&T, usize) tuples — destructure and
                    // repeat each element by its count.
                    arms.push(quote! {
                        #category::#label(coll) => {
                            let items: Vec<String> = coll.iter()
                                .flat_map(|(elem, count)| std::iter::repeat(format!("{}", elem)).take(count))
                                .collect();
                            if items.is_empty() {
                                evaluator.set_control(format!("{}", term));
                                evaluator.set_state(mettail_runtime::EvalState::Reducing);
                            } else if items.len() == 1 {
                                evaluator.set_control(items.into_iter().next().expect("len == 1"));
                                evaluator.set_state(mettail_runtime::EvalState::Reducing);
                            } else {
                                let mut remaining: Vec<String> = items;
                                let first = remaining.remove(0);
                                evaluator.push_frame(mettail_runtime::EvalFrame::Parallel {
                                    remaining,
                                    completed: Vec::new(),
                                });
                                evaluator.set_control(first);
                                evaluator.set_state(mettail_runtime::EvalState::Reducing);
                            }
                        }
                    });
                } else {
                    // Non-parallel collection: just display
                    arms.push(quote! {
                        #category::#label(..) => {
                            evaluator.set_control(format!("{}", term));
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        }
                    });
                }
            },
            CekRuleKind::Binder => {
                // For binder variants: use the display form. The CEK evaluator
                // works with string-level display forms; full binder decomposition
                // into LetBody frames requires moniker unbind which is only sound
                // when the evaluator has a rewrite rule engine.
                arms.push(quote! {
                    #category::#label(..) => {
                        evaluator.set_control(format!("{}", term));
                        evaluator.set_state(mettail_runtime::EvalState::Reducing);
                    }
                });
            },
            CekRuleKind::Atom | CekRuleKind::Compound => {
                if n_fields == 0 {
                    arms.push(quote! {
                        #category::#label => {
                            evaluator.set_control(format!("{}", term));
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        }
                    });
                } else {
                    arms.push(quote! {
                        #category::#label(..) => {
                            evaluator.set_control(format!("{}", term));
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        }
                    });
                }
            },
        }
    }

    // Add catch-all for auto-generated variants (Lit, Var, Lam, Apply, etc.)
    // These are always atoms/compounds from CEK's perspective.
    arms.push(quote! {
        _ => {
            evaluator.set_control(format!("{}", term));
            evaluator.set_state(mettail_runtime::EvalState::Reducing);
        }
    });

    arms
}

/// Generate the `decompose_into_cek` method for a single-type language.
fn generate_cek_decompose_single(
    _language_name: &syn::Ident,
    term_name: &syn::Ident,
    primary_type: &syn::Ident,
    language: &LanguageDef,
) -> TokenStream {
    let rules: Vec<&GrammarRule> = language
        .terms
        .iter()
        .filter(|r| r.category == *primary_type)
        .collect();

    let arms = generate_cek_decompose_arms(primary_type, &rules, language);

    quote! {
        fn decompose_into_cek(
            &self,
            term: &dyn mettail_runtime::Term,
            evaluator: &mut mettail_runtime::CekEvaluator,
        ) -> bool {
            let typed = match term.as_any().downcast_ref::<#term_name>() {
                Some(t) => t,
                None => return false,
            };
            let term = &typed.0;
            match term {
                #(#arms)*
            }
            true
        }
    }
}

/// Generate the `decompose_into_cek` method for a multi-type language.
fn generate_cek_decompose_multi(
    _language_name: &syn::Ident,
    term_name: &syn::Ident,
    inner_enum_name: &syn::Ident,
    language: &LanguageDef,
) -> TokenStream {
    // Generate per-category dispatch arms
    let mut dispatch_arms = Vec::new();
    for lang_type in &language.types {
        let cat = &lang_type.name;
        let variant = format_ident!("{}", cat);
        let rules: Vec<&GrammarRule> = language
            .terms
            .iter()
            .filter(|r| r.category == *cat)
            .collect();
        let arms = generate_cek_decompose_arms(cat, &rules, language);
        dispatch_arms.push(quote! {
            #inner_enum_name::#variant(term) => {
                match term {
                    #(#arms)*
                }
            }
        });
    }

    quote! {
        fn decompose_into_cek(
            &self,
            term: &dyn mettail_runtime::Term,
            evaluator: &mut mettail_runtime::CekEvaluator,
        ) -> bool {
            let typed = match term.as_any().downcast_ref::<#term_name>() {
                Some(t) => t,
                None => return false,
            };
            match &typed.0 {
                #inner_enum_name::Ambiguous(alts) => {
                    // Phase D.3 (2026-05-17, M13.3): try ALL alternatives
                    // instead of just the first. Per P3 in the master
                    // plan (preserve-all-derivations through decomposition),
                    // the previous `alts.first()` peel collapsed to a
                    // single derivation. The new path tries each alt
                    // and succeeds if ANY alternative's decomposition
                    // succeeds — matching the parser's "alts is a Vec of
                    // valid parses" contract.
                    let mut any_ok = false;
                    for alt in alts {
                        let sub = #term_name(alt.clone());
                        if self.decompose_into_cek(&sub, evaluator) {
                            any_ok = true;
                        }
                    }
                    return any_ok;
                }
                #(#dispatch_arms)*
            }
            true
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

/// Generate code to extract all relations (generated + custom) from the Ascent program.
/// Uses the unified list from list_all_relations_for_extraction so custom_relations
/// is the single source for query schema and data.
fn generate_custom_relation_extraction(language: &LanguageDef) -> TokenStream {
    let relations = list_all_relations_for_extraction(language);

    if relations.is_empty() {
        return quote! {};
    }

    let mut extractions = Vec::new();

    for rel in relations {
        let rel_name = &rel.name;
        let rel_name_str = rel_name.to_string();
        let param_type_strs = &rel.param_types;

        let arity = rel.param_types.len();
        let tuple_vars: Vec<syn::Ident> = (0..arity).map(|i| format_ident!("e{}", i)).collect();

        let format_exprs: Vec<TokenStream> = rel
            .param_types
            .iter()
            .zip(tuple_vars.iter())
            .map(|(ty, v)| {
                if ty.starts_with("Vec") || ty.starts_with("HashSet") {
                    quote! { format!("{}", mettail_runtime::DisplaySlice(#v.as_slice())) }
                } else {
                    quote! { format!("{}", #v) }
                }
            })
            .collect();

        // For arity 1, use (e0,) so Rust treats it as a tuple pattern; (e0) would bind the whole &(Proc,).
        let tuple_pattern: TokenStream = if arity == 1 {
            quote! { (#(#tuple_vars),*,) }
        } else {
            quote! { (#(#tuple_vars),*) }
        };

        extractions.push(quote! {
            custom_relations.insert(
                #rel_name_str.to_string(),
                mettail_runtime::RelationData {
                    param_types: vec![#(#param_type_strs.to_string()),*],
                    tuples: prog.#rel_name
                        .iter()
                        .map(|#tuple_pattern| vec![#(#format_exprs),*])
                        .collect(),
                }
            );
        });
    }

    quote! {
        #(#extractions)*
    }
}
