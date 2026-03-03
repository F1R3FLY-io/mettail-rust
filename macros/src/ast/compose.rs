//! AST definitions for the `compose_languages!` macro.
//!
//! A composition combines independently defined languages (each with their own
//! parser, ascent engine, env, metadata, etc.) behind a single unified
//! `Language` trait implementation. No new parser or ascent program is
//! generated -- everything is delegated to the constituent sub-languages.
//!
//! ```ignore
//! compose_languages! {
//!     name: Combined,
//!     languages: [calculator::Calculator, rhocalc::RhoCalc],
//! }
//! ```

use syn::{
    bracketed,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
    Ident, Result as SynResult, Token,
};

/// Top-level definition produced by `compose_languages! { ... }`.
pub struct ComposeDef {
    /// The name of the composed language (e.g. `Combined`).
    pub name: Ident,
    /// References to the sub-languages being composed.
    pub languages: Vec<LanguageRef>,
}

/// A reference to a sub-language inside a composition.
///
/// The user writes `module::LanguageName` (e.g. `calculator::Calculator`).
/// `module_path` stores the module prefix (`calculator`) and `variant_name`
/// stores the language name (`Calculator`). Code generation uses
/// `module_path::CalculatorTerm`, `module_path::CalculatorLanguage`, etc.
pub struct LanguageRef {
    /// Module path prefix (e.g. `calculator` from `calculator::Calculator`).
    pub module_path: syn::Path,
    /// Short name derived from the last path segment (e.g. `Calculator`).
    pub variant_name: Ident,
}

impl Parse for ComposeDef {
    fn parse(input: ParseStream) -> SynResult<Self> {
        // ── name: Ident ──
        let kw = input.parse::<Ident>()?;
        if kw != "name" {
            return Err(syn::Error::new(kw.span(), "expected keyword `name`"));
        }
        let _colon: Token![:] = input.parse()?;
        let name: Ident = input.parse()?;
        let _comma: Token![,] = input.parse()?;

        // ── languages: [path, path, ...] ──
        let kw2 = input.parse::<Ident>()?;
        if kw2 != "languages" {
            return Err(syn::Error::new(kw2.span(), "expected keyword `languages`"));
        }
        let _colon2: Token![:] = input.parse()?;

        let content;
        bracketed!(content in input);
        let paths: Punctuated<syn::Path, Token![,]> =
            content.parse_terminated(syn::Path::parse, Token![,])?;

        if paths.is_empty() {
            return Err(syn::Error::new(
                kw2.span(),
                "`languages` list must contain at least one entry",
            ));
        }

        let mut languages = Vec::with_capacity(paths.len());
        for p in paths {
            if p.segments.len() < 2 {
                return Err(syn::Error::new(
                    p.segments
                        .first()
                        .map(|s| s.ident.span())
                        .unwrap_or(kw2.span()),
                    "language reference must include module path \
                     (e.g., `calculator::Calculator`)",
                ));
            }
            let variant_name = p
                .segments
                .last()
                .expect("path must have at least one segment")
                .ident
                .clone();
            // Rebuild module path from all segments except the last.
            // Cannot use Punctuated::pop() because it leaves a trailing separator (::),
            // causing `quote! { #path::#ty }` to emit double `::` (invalid syntax).
            // FromIterator<PathSegment> creates proper separators without trailing `::`.
            let seg_count = p.segments.len();
            let leading_colon = p.leading_colon;
            let module_segments: Punctuated<syn::PathSegment, Token![::]> = p
                .segments
                .into_iter()
                .take(seg_count - 1)
                .collect();
            let module_path = syn::Path {
                leading_colon,
                segments: module_segments,
            };
            languages.push(LanguageRef {
                module_path,
                variant_name,
            });
        }

        // Consume optional trailing comma after the closing `]`
        let _ = input.parse::<Option<Token![,]>>();

        Ok(ComposeDef { name, languages })
    }
}
