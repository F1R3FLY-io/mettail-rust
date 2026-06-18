//! AC (associative-commutative) collection metapattern lowering for the Dovetail
//! report compiler.
//!
//! A collection metapattern `{ P, Q, ...rest }` appears as the sole argument of a
//! `PatternTerm::Apply { constructor, [Collection { .. }] }` (the enclosing
//! constructor supplies the operator label and the collection category — see the
//! `Pattern::Collection` doc in `ast/src/pattern.rs`). This module lowers such a
//! collection to a `Pattern::ac(op, fixed, rest)`:
//!
//! - `op` = the enclosing constructor's label (`<Lang>::<Cat>::<Label>`),
//! - `fixed` = each element pattern lowered via the parent's
//!   `pattern_to_dovetail`,
//! - `rest` = the `...rest` remainder variable name, if present.
//!
//! The matcher then matches a sub-multiset of an `op`-bag's children against
//! `fixed` (any pairing — the non-linear `Var` re-bind check prunes disagreeing
//! shared variables) and binds `rest` to the multiset complement. Only `HashBag`
//! (the genuine AC multiset) is supported; `Map`/`Zip` stay rejected upstream.

use mettail_ast::language::LanguageDef;
use mettail_ast::pattern::Pattern as AstPattern;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::quote;
use syn::LitStr;

use super::lit;

/// Lower a collection metapattern into a `Pattern::ac(op, fixed, rest)` token
/// stream. `op_label` is the enclosing constructor's resolved Dovetail label.
///
/// Returns `Err` for a non-`HashBag` collection type (Vec/HashSet/HashMap are not
/// AC multisets) — fail closed, matching the engine's `HashBag`-only AC support.
pub(crate) fn lower_ac_collection(
    language: &LanguageDef,
    op_label: &LitStr,
    coll: &AstPattern,
) -> Result<TokenStream, String> {
    let AstPattern::Collection { coll_type, elements, rest } = coll else {
        return Err("lower_ac_collection requires a Collection pattern".into());
    };

    // Only HashBag is the genuine associative-commutative multiset. An explicit
    // non-HashBag type fails closed; `None` (inferred from the constructor's
    // HashBag grammar — the only collection rule lowered here) is accepted.
    match coll_type {
        None | Some(CollectionType::HashBag) => {},
        Some(other) => {
            return Err(format!("AC collection lowering supports HashBag only, found {other:?}"));
        },
    }

    let fixed = elements
        .iter()
        // AC collection metapatterns are lowered only on the `EGraph<String>` path (the typed
        // fold path fails closed before reaching here), so the op label is always a String.
        .map(|elem| super::pattern_to_dovetail(language, elem, None))
        .collect::<Result<Vec<_>, _>>()?;

    let rest_tokens = match rest {
        Some(name) => {
            let name_lit = lit(&name.to_string());
            quote! { Some(#name_lit.to_string()) }
        },
        None => quote! { None },
    };

    Ok(quote! {
        ::dovetail::rules::Pattern::ac(
            #op_label.to_string(),
            vec![#(#fixed),*],
            #rest_tokens,
        )
    })
}
