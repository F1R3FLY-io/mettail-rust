//! Greg Meredith's MeTTaIL `Module`/`Theory` surface and elaborator.
//!
//! Surface declarations elaborate into presentations. The companion canonical
//! value representation remains the authority used for identity, registry
//! storage, programmatic construction, and backend generation.

pub mod ast;
pub mod canonical;
pub mod diag;
pub mod interp;
pub mod lex;
pub mod parse;
pub mod pres;
pub mod registry;
pub mod resolve;

pub use diag::{Diag, DiagKind};
pub use pres::Presentation;

pub struct ElaboratedLanguage {
    pub presentation: Presentation,
    pub canonical_value: canonical::RhoValue,
    pub grammar_core: mettail_grammar_core::GrammarCoreV1,
    /// Non-executable negotiation metadata. A complete parser-image compiler
    /// replaces this with an executable cache artifact after lowering.
    pub parser_image_metadata: mettail_grammar_core::ParserImageV1,
}

pub fn elaborate(
    entry: &resolve::ModuleRef,
    resolver: &dyn resolve::Resolver,
) -> Result<Presentation, Diag> {
    let program = resolve::Program::load(entry, resolver)?;
    let mut interpreter = interp::Interp::new(&program);
    interpreter.run()
}

pub fn elaborate_language(
    name: &str,
    entry: &resolve::ModuleRef,
    resolver: &dyn resolve::Resolver,
) -> Result<ElaboratedLanguage, Diag> {
    let presentation = elaborate(entry, resolver)?;
    let canonical_value = canonical::presentation_to_value(name, &presentation);
    // The ordinary Rholang value is the semantic authority. Keep this decode
    // boundary even though `presentation` is already available so the surface
    // DDL and programmatically constructed values cannot acquire distinct
    // lowering behavior.
    let grammar_core = canonical::value_to_core(&canonical_value).map_err(|error| {
        Diag::new(
            DiagKind::Resolution,
            format!("cannot lower canonical language value: {error:?}"),
            lex::Span { line: 0, col: 0 },
        )
    })?;
    let parser_image_metadata = mettail_grammar_core::ParserImageV1::metadata_only(
        &grammar_core,
        env!("CARGO_PKG_VERSION"),
        "host-unicode",
    )
    .map_err(|error| {
        Diag::new(
            DiagKind::Resolution,
            format!("cannot compile parser image: {error:?}"),
            lex::Span { line: 0, col: 0 },
        )
    })?;
    Ok(ElaboratedLanguage {
        presentation,
        canonical_value,
        grammar_core,
        parser_image_metadata,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn surface_language_crosses_the_canonical_value_boundary() {
        let source = r#"
            Module Tiny {
              Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
              theory T()
            }
        "#;
        let resolver = resolve::MemResolver::new().with("Tiny.module", source);
        let entry = resolve::ModuleRef::parse("Tiny.module").expect("valid module reference");
        let language = elaborate_language("Tiny", &entry, &resolver).expect("elaborates");
        let direct = canonical::value_to_core(&language.canonical_value)
            .expect("canonical value lowers independently");

        assert_eq!(language.grammar_core.provenance.frontend, "rholang-language/2");
        assert_eq!(language.grammar_core, direct);
    }
}
