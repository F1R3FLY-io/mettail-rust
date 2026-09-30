//! Greg Meredith's MeTTaIL `Module`/`Theory` surface and elaborator.
//!
//! Surface declarations elaborate into presentations. The companion canonical
//! value representation remains the authority used for identity, registry
//! storage, programmatic construction, and backend generation.

pub mod ast;
pub mod canonical;
pub mod core_value;
pub mod diag;
pub mod interp;
pub mod lex;
pub mod module;
pub mod parse;
pub mod pres;
mod projection_compile;
pub mod registry;
pub mod resolve;
pub mod rholang_literal;
mod schema;
mod theory_compile;
pub mod wire;

pub use diag::{Diag, DiagKind, SourceProvenance};
pub use pres::Presentation;

#[derive(Debug)]
pub struct ElaboratedLanguage {
    pub presentation: Presentation,
    pub canonical_value: canonical::RhoValue,
    /// Declarative attenuation request carried beside, never inside, the
    /// immutable language/parser identity.
    pub requested_rights: mettail_grammar_core::LanguageRights,
    /// Authoritative complete syntax-and-theory artifact.
    pub language_core: mettail_grammar_core::LanguageCoreV1,
    /// Versioned semantic extension when this is a `language/4` value. The
    /// legacy core above is its unchanged parser/theory base, not an
    /// alternative installable meaning for the projected language.
    pub projected_language_core: Option<mettail_grammar_core::ProjectedLanguageCoreV1>,
    /// Compatibility projection for parser-only consumers. New installation
    /// code should retain `language_core` so theory identity is not erased.
    pub grammar_core: mettail_grammar_core::GrammarCoreV1,
}

#[derive(Debug)]
pub struct ElaboratedModuleExport {
    pub name: String,
    pub language: ElaboratedLanguage,
}

#[derive(Debug)]
pub struct ElaboratedModule {
    pub name: String,
    pub dependencies: Vec<(resolve::ModuleRef, [u8; 32])>,
    pub exports: Vec<ElaboratedModuleExport>,
    pub canonical_value: canonical::RhoValue,
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
    finish_language(name, presentation, None)
}

pub fn elaborate_language_with_host(
    name: &str,
    entry: &resolve::ModuleRef,
    resolver: &dyn resolve::Resolver,
    host: &mettail_grammar_core::ProjectionHostSignatureV1,
) -> Result<ElaboratedLanguage, Diag> {
    let presentation = elaborate(entry, resolver)?;
    finish_language(name, presentation, Some(host))
}

/// Elaborate every named `theory ...` entry of one module in source order.
///
/// The surface has no export-alias production. A direct theory application
/// supplies its declared name; compound expressions must be wrapped in a
/// named `Theory` declaration. This keeps Greg/Mike syntax intact while making
/// the module record's export names deterministic.
pub fn elaborate_module_languages(
    entry: &resolve::ModuleRef,
    resolver: &dyn resolve::Resolver,
) -> Result<ElaboratedModule, Diag> {
    let program = resolve::Program::load(entry, resolver)?;
    elaborate_program_languages(&program, entry, None)
}

pub fn elaborate_module_languages_with_host(
    entry: &resolve::ModuleRef,
    resolver: &dyn resolve::Resolver,
    host: &mettail_grammar_core::ProjectionHostSignatureV1,
) -> Result<ElaboratedModule, Diag> {
    let program = resolve::Program::load(entry, resolver)?;
    elaborate_program_languages(&program, entry, Some(host))
}

/// Elaborate an entry module already parsed by nouveau Rholang. Imported
/// modules still cross the injected resolver with their exact commitments;
/// the entry AST never becomes source text and is never parsed again.
pub fn elaborate_module_ast(
    module: ast::ModuleFile,
    resolver: &dyn resolve::Resolver,
) -> Result<ElaboratedModule, Diag> {
    let entry = resolve::ModuleRef::Registry("rho:mettail:inline-ast".into());
    elaborate_module_ast_at(&entry, module, resolver)
}

pub fn elaborate_module_ast_with_host(
    module: ast::ModuleFile,
    resolver: &dyn resolve::Resolver,
    host: &mettail_grammar_core::ProjectionHostSignatureV1,
) -> Result<ElaboratedModule, Diag> {
    let entry = resolve::ModuleRef::Registry("rho:mettail:inline-ast".into());
    elaborate_module_ast_at_with_host(&entry, module, resolver, host)
}

/// Elaborate an already-parsed module under an explicit authoritative module
/// reference. This is used for a Registry entry that has already been fetched,
/// commitment-checked, and trust-verified by the caller; only its imports may
/// consult the injected resolver.
pub fn elaborate_module_ast_at(
    entry: &resolve::ModuleRef,
    module: ast::ModuleFile,
    resolver: &dyn resolve::Resolver,
) -> Result<ElaboratedModule, Diag> {
    let program = resolve::Program::load_from_ast(entry, module, resolver)?;
    elaborate_program_languages(&program, entry, None)
}

pub fn elaborate_module_ast_at_with_host(
    entry: &resolve::ModuleRef,
    module: ast::ModuleFile,
    resolver: &dyn resolve::Resolver,
    host: &mettail_grammar_core::ProjectionHostSignatureV1,
) -> Result<ElaboratedModule, Diag> {
    let program = resolve::Program::load_from_ast(entry, module, resolver)?;
    elaborate_program_languages(&program, entry, Some(host))
}

fn elaborate_program_languages(
    program: &resolve::Program,
    entry: &resolve::ModuleRef,
    host: Option<&mettail_grammar_core::ProjectionHostSignatureV1>,
) -> Result<ElaboratedModule, Diag> {
    elaborate_loaded_module(program, entry, host)
}

fn elaborate_loaded_module(
    program: &resolve::Program,
    reference: &resolve::ModuleRef,
    host: Option<&mettail_grammar_core::ProjectionHostSignatureV1>,
) -> Result<ElaboratedModule, Diag> {
    elaborate_loaded_module_unannotated(program, reference, host).map_err(|mut error| {
        error.attach_provenance(module_provenance(program, reference));
        error
    })
}

fn module_provenance(
    program: &resolve::Program,
    reference: &resolve::ModuleRef,
) -> diag::SourceProvenance {
    diag::SourceProvenance {
        reference: reference.external_form(),
        content_commitment: program.commitment(reference),
        import_chain: vec![reference.external_form()],
    }
}

fn elaborate_loaded_module_unannotated(
    program: &resolve::Program,
    reference: &resolve::ModuleRef,
    host: Option<&mettail_grammar_core::ProjectionHostSignatureV1>,
) -> Result<ElaboratedModule, Diag> {
    let module = program.module(reference).ok_or_else(|| {
        Diag::new(
            DiagKind::Resolution,
            format!("module `{reference}` is absent from the resolved graph"),
            lex::Span { line: 0, col: 0 },
        )
    })?;
    if module.entries().count() > module::MAX_CANONICAL_MODULE_EXPORTS {
        return Err(Diag::new(
            DiagKind::ResourceLimit,
            format!("module exceeds {} language exports", module::MAX_CANONICAL_MODULE_EXPORTS),
            module.span,
        ));
    }
    let mut names = std::collections::BTreeSet::new();
    let export_names = module
        .entries()
        .map(|expression| {
            let name = expression.export_name().ok_or_else(|| {
                Diag::new(
                    DiagKind::UnnamedExport,
                    "a compound `theory` entry has no stable name; wrap it in `Theory N() { ... }` and export `theory N()`",
                    expression.span(),
                )
            })?;
            if !names.insert(name.to_string()) {
                return Err(Diag::new(
                    DiagKind::DuplicateExport,
                    format!("language export `{name}` occurs more than once"),
                    expression.span(),
                ));
            }
            Ok(name.to_string())
        })
        .collect::<Result<Vec<_>, Diag>>()?;
    let presentations = interp::Interp::run_all_at(program, reference)?;
    let exports = export_names
        .into_iter()
        .zip(presentations)
        .map(|(name, presentation)| {
            finish_language(&name, presentation, host)
                .map(|language| ElaboratedModuleExport { name, language })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let dependencies = program.dependency_lockfile_from(reference);
    let canonical_module = module::CanonicalModuleValue {
        name: module.name.clone(),
        dependencies: dependencies
            .iter()
            .map(|(reference, commitment)| module::CanonicalModuleDependency {
                reference: reference.clone(),
                commitment: *commitment,
            })
            .collect(),
        exports: exports
            .iter()
            .map(|export| module::CanonicalModuleExport {
                name: export.name.clone(),
                spec: export.language.canonical_value.clone(),
            })
            .collect(),
    };
    // Surface and structural modules cross the same closed `module/1`
    // admission boundary as programmatically assembled module values.  This
    // prevents the ergonomic frontend from bypassing identifier, dependency,
    // export-count, duplicate-name, or nested-value limits.
    let canonical_value = canonical_module.to_rho_value();
    let canonical_module = module::CanonicalModuleValue::from_rho_value(&canonical_value)
        .map_err(|error| Diag::new(DiagKind::Value, error.to_string(), module.span))?;
    let canonical_value = canonical_module.to_rho_value();
    Ok(ElaboratedModule {
        name: module.name.clone(),
        dependencies,
        exports,
        canonical_value,
    })
}

/// Elaborate a standalone, closed `Theory` declaration as a language.
///
/// A parameterized theory is intentionally not guessed into a concrete
/// language: its arguments are presentations and must be supplied explicitly
/// by a surrounding `Module` application. A zero-parameter theory has one
/// canonical application and is therefore directly installable.
pub fn elaborate_theory_language(source: &str) -> Result<ElaboratedLanguage, Diag> {
    let declaration = parse::parse_theory(source)?;
    elaborate_theory_ast(declaration)
}

/// Elaborate one standalone theory declaration already parsed by nouveau
/// Rholang. This is the structural twin of [`elaborate_theory_language`], with
/// the source parser intentionally absent.
pub fn elaborate_theory_ast(declaration: ast::TheoryDecl) -> Result<ElaboratedLanguage, Diag> {
    if !declaration.params.is_empty() {
        return Err(Diag::new(
            DiagKind::Resolution,
            format!(
                "standalone theory `{}` has {} parameter(s); install a Module that applies it",
                declaration.name,
                declaration.params.len()
            ),
            declaration.span,
        ));
    }

    let name = declaration.name.clone();
    let span = declaration.span;
    let module = ast::ModuleFile {
        imports: Vec::new(),
        name: name.clone(),
        items: vec![
            ast::ModuleItem::TheoryDecl(declaration),
            ast::ModuleItem::TheoryEntry(ast::TheoryExpr::Apply {
                head: ast::DottedPath(vec![name.clone()]),
                args: Vec::new(),
                span,
            }),
        ],
        span,
    };
    let entry = resolve::ModuleRef::Registry("rho:mettail:inline-theory".into());
    let program = resolve::Program::from_single_module(entry, module)?;
    let mut interpreter = interp::Interp::new(&program);
    let presentation = interpreter.run()?;
    finish_language(&name, presentation, None)
}

fn finish_language(
    name: &str,
    presentation: Presentation,
    host: Option<&mettail_grammar_core::ProjectionHostSignatureV1>,
) -> Result<ElaboratedLanguage, Diag> {
    let canonical_value =
        canonical::presentation_to_value(name, &presentation).map_err(|error| {
            Diag::new(DiagKind::Value, error.to_string(), lex::Span { line: 0, col: 0 })
        })?;
    // The ordinary Rholang value is the semantic authority. Keep this decode
    // boundary even though `presentation` is already available so the surface
    // DDL and programmatically constructed values cannot acquire distinct
    // lowering behavior.
    let installable = canonical::value_to_installable_any_language_core(&canonical_value, host)
        .map_err(|error| {
            Diag::new(
                DiagKind::Resolution,
                format!("cannot lower canonical language value: {error:?}"),
                lex::Span { line: 0, col: 0 },
            )
        })?;
    let (language_core, projected_language_core, requested_rights) = match installable {
        canonical::InstallableAnyLanguageCore::Legacy(installable) => {
            (installable.language, None, installable.requested_rights)
        },
        canonical::InstallableAnyLanguageCore::Projected(installable) => (
            installable.language.base.clone(),
            Some(installable.language),
            installable.requested_rights,
        ),
    };
    Ok(ElaboratedLanguage {
        presentation,
        canonical_value,
        requested_rights,
        grammar_core: language_core.grammar.clone(),
        language_core,
        projected_language_core,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn noadmit_category_survives_source_elaboration_and_canonical_roundtrip() {
        let language = elaborate_theory_language(
            r#"Theory Categories() {
                Types { OpenExpr; noadmit ClosedExpr; }
                Terms {
                    OpenLiteral . |- "open" : OpenExpr;
                    ClosedLiteral . |- "closed" : ClosedExpr;
                }
            }"#,
        )
        .expect("both category declarations elaborate");
        let (_, presentation) = canonical::value_to_presentation(&language.canonical_value)
            .expect("canonical value reconstructs the presentation");
        assert!(presentation
            .types
            .iter()
            .any(|entry| entry.cat == "OpenExpr" && entry.admits_variables));
        assert!(presentation
            .types
            .iter()
            .any(|entry| entry.cat == "ClosedExpr" && !entry.admits_variables));
        let roundtrip = canonical::value_to_core(&language.canonical_value)
            .expect("canonical value lowers independently");
        assert_eq!(language.grammar_core, roundtrip);
        assert!(roundtrip
            .categories
            .iter()
            .any(|category| category.name == "OpenExpr" && category.admits_variables));
        assert!(roundtrip
            .categories
            .iter()
            .any(|category| category.name == "ClosedExpr" && !category.admits_variables));
    }

    #[test]
    fn native_carrier_annotations_preserve_spelling_and_admission() {
        let language = elaborate_theory_language(
            r#"Theory Carriers() {
                Types {
                    noadmit Text = String;
                    noadmit Flag = bool;
                    noadmit Nat = BigInt;
                }
                Terms {
                    TextValue . |- "text" : Text;
                    FlagValue . |- "flag" : Flag;
                    NatValue . |- "nat" : Nat;
                }
            }"#,
        )
        .expect("native carrier annotations elaborate");
        let (_, presentation) = canonical::value_to_presentation(&language.canonical_value)
            .expect("native carrier maps retain presentation metadata");
        for (name, spelling) in [("Text", "String"), ("Flag", "bool"), ("Nat", "BigInt")] {
            let entry = presentation
                .types
                .iter()
                .find(|entry| entry.cat == name)
                .expect("declared category survives");
            assert!(!entry.admits_variables);
            assert_eq!(entry.carrier.as_deref(), Some(spelling));
        }
        let roundtrip = canonical::value_to_core(&language.canonical_value)
            .expect("carrier annotations lower through the canonical schema");
        assert_eq!(language.grammar_core, roundtrip);
        for name in ["Text", "Flag", "Nat"] {
            assert!(
                !roundtrip
                    .categories
                    .iter()
                    .find(|category| category.name == name)
                    .expect("lowered category")
                    .admits_variables
            );
        }
    }

    #[test]
    fn authored_native_type_matches_the_data_faithful_type_value() {
        let authored = elaborate_theory_language(
            r#"Theory Same() {
                Types { noadmit Text = String; }
                Terms { TextValue . |- "text" : Text; }
            }"#,
        )
        .expect("authored type elaborates");
        let data_faithful = elaborate_theory_language(
            r#"Theory Same() {
                Data({"types": [{"name":"Text", "carrier":"String",
                                "admits_variables":false}]})
                Terms { TextValue . |- "text" : Text; }
            }"#,
        )
        .expect("data-faithful type elaborates");
        assert_eq!(authored.canonical_value, data_faithful.canonical_value);
        assert_eq!(authored.grammar_core, data_faithful.grammar_core);
    }

    #[test]
    fn closed_regex_types_match_the_data_faithful_admission_flags_and_carriers() {
        let authored = elaborate_theory_language(
            r#"Theory RegexTypes() {
                Types {
                    noadmit Pattern; noadmit Computation;
                    noadmit NFrames; noadmit DFrames; noadmit EFrames;
                    noadmit MatchResult; noadmit ReplacementTemplate;
                    noadmit PrefixResult;
                    noadmit Scalar = String; noadmit Text = String;
                    noadmit Bool = bool; noadmit Flag = bool;
                    noadmit Nat = BigInt; noadmit Grade = BigInt;
                }
                Terms { PFail . |- "(?!)" : Pattern; }
            }"#,
        )
        .expect("authored Regex type roster elaborates");
        let data_faithful = elaborate_theory_language(
            r#"Theory RegexTypes() {
                Data({"types": [
                    {"name":"Pattern", "admits_variables":false},
                    {"name":"Computation", "admits_variables":false},
                    {"name":"NFrames", "admits_variables":false},
                    {"name":"DFrames", "admits_variables":false},
                    {"name":"EFrames", "admits_variables":false},
                    {"name":"MatchResult", "admits_variables":false},
                    {"name":"ReplacementTemplate", "admits_variables":false},
                    {"name":"PrefixResult", "admits_variables":false},
                    {"name":"Scalar", "carrier":"String", "admits_variables":false},
                    {"name":"Text", "carrier":"String", "admits_variables":false},
                    {"name":"Bool", "carrier":"bool", "admits_variables":false},
                    {"name":"Flag", "carrier":"bool", "admits_variables":false},
                    {"name":"Nat", "carrier":"BigInt", "admits_variables":false},
                    {"name":"Grade", "carrier":"BigInt", "admits_variables":false}
                ]})
                Terms { PFail . |- "(?!)" : Pattern; }
            }"#,
        )
        .expect("data-faithful closed Regex type roster elaborates");
        assert_eq!(authored.canonical_value, data_faithful.canonical_value);
        assert_eq!(authored.grammar_core, data_faithful.grammar_core);
    }

    #[test]
    fn authored_term_precedence_matches_existing_data_fields() {
        let authored = elaborate_theory_language(
            r#"Theory Operators() {
                Types { Expr; }
                Terms {
                    Atom . |- "a" : Expr;
                    Add . x:Expr, y:Expr |- x "+" y : Expr left prefix(10);
                    Post . x:Expr |- x "*" : Expr nonassoc prefix(30);
                }
            }"#,
        )
        .expect("authored term metadata elaborates");
        let data_faithful = elaborate_theory_language(
            r#"Theory Operators() {
                Types { Expr; }
                Terms { Atom . |- "a" : Expr; }
                Data({"terms": [
                    {"label":"Add", "category":"Expr",
                     "context":[["param","x","Expr"],["param","y","Expr"]],
                     "syntax":["x",["lit","+"],"y"],
                     "assoc":"left", "prefix_bp":10},
                    {"label":"Post", "category":"Expr",
                     "context":[["param","x","Expr"]],
                     "syntax":["x",["lit","*"]],
                     "assoc":"nonassoc", "prefix_bp":30}
                ]})
            }"#,
        )
        .expect("data-faithful term metadata elaborates");
        assert_eq!(authored.canonical_value, data_faithful.canonical_value);
        assert_eq!(authored.grammar_core, data_faithful.grammar_core);
    }

    #[test]
    fn duplicate_or_out_of_range_term_metadata_is_rejected() {
        for suffix in
            ["left right", "prefix(10) prefix(20)", "prefix(65536)", "prefix(-1)", "unknown"]
        {
            let source = format!(
                "Theory Invalid() {{ Types {{ Expr; }} Terms {{ Atom . |- \"a\" : Expr {suffix}; }} }}"
            );
            assert!(
                elaborate_theory_language(&source).is_err(),
                "term metadata {suffix:?} must reject"
            );
        }
    }

    #[test]
    fn regex_operator_migration_preserves_all_six_canonical_records_and_core_rules() {
        let authored = elaborate_theory_language(
            r#"Theory RegexOperators() {
                Types { Pattern; Nat; }
                Terms {
                    PFail . |- "(?!)" : Pattern;
                    PAlt . p:Pattern, q:Pattern |- p "|" q : Pattern left prefix(10);
                    PConcat . p:Pattern, q:Pattern |- p q : Pattern left prefix(20);
                    PStar . p:Pattern |- p "*" : Pattern nonassoc prefix(30);
                    PPlus . p:Pattern |- p "+" : Pattern nonassoc prefix(30);
                    POptional . p:Pattern |- p "?" : Pattern nonassoc prefix(30);
                    PRepeat . p:Pattern, lo:Nat, hi:Nat
                      |- p "{" lo "," hi "}" : Pattern nonassoc prefix(30);
                }
            }"#,
        )
        .expect("authored Regex operator roster elaborates");
        let data_faithful = elaborate_theory_language(
            r#"Theory RegexOperators() {
                Types { Pattern; Nat; }
                Terms { PFail . |- "(?!)" : Pattern; }
                Data({"terms": [
                    {"label":"PAlt", "category":"Pattern", "context":[["param","p","Pattern"],["param","q","Pattern"]], "syntax":["p",["lit","|"],"q"], "assoc":"left", "prefix_bp":10},
                    {"label":"PConcat", "category":"Pattern", "context":[["param","p","Pattern"],["param","q","Pattern"]], "syntax":["p","q"], "assoc":"left", "prefix_bp":20},
                    {"label":"PStar", "category":"Pattern", "context":[["param","p","Pattern"]], "syntax":["p",["lit","*"]], "assoc":"nonassoc", "prefix_bp":30},
                    {"label":"PPlus", "category":"Pattern", "context":[["param","p","Pattern"]], "syntax":["p",["lit","+"]], "assoc":"nonassoc", "prefix_bp":30},
                    {"label":"POptional", "category":"Pattern", "context":[["param","p","Pattern"]], "syntax":["p",["lit","?"]], "assoc":"nonassoc", "prefix_bp":30},
                    {"label":"PRepeat", "category":"Pattern", "context":[["param","p","Pattern"],["param","lo","Nat"],["param","hi","Nat"]], "syntax":["p",["lit","{"],"lo",["lit",","],"hi",["lit","}"]], "assoc":"nonassoc", "prefix_bp":30}
                ]})
            }"#,
        )
        .expect("original Regex operator roster elaborates");
        assert_eq!(authored.canonical_value, data_faithful.canonical_value);
        assert_eq!(authored.grammar_core, data_faithful.grammar_core);
    }

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

    #[test]
    fn host_bound_elaboration_retains_the_versioned_projection_core() {
        let source = r#"
            Module Predicate {
              Theory T() { Types { Bool; } Terms { BTrue . |- "yes" : Bool; } }
              theory T()
            }
        "#;
        let resolver = resolve::MemResolver::new().with("Predicate.module", source);
        let entry = resolve::ModuleRef::parse("Predicate.module").unwrap();
        let plain = elaborate_language("Predicate", &entry, &resolver).unwrap();
        // The generated Rholang frontend supplies this already-parsed AST;
        // the standalone BNFC parser deliberately does not reparse it.
        let mut module = parse::parse_module(source).unwrap();
        let ast::ModuleItem::TheoryDecl(declaration) = &mut module.items[0] else {
            panic!("first module item is its theory declaration");
        };
        let span = declaration.span;
        let body = std::mem::replace(&mut declaration.body, ast::TheoryExpr::Empty(span));
        declaration.body = ast::TheoryExpr::Build {
            base: Box::new(body),
            builder: ast::Builder::Rewrites(vec![ast::RewriteEntry::Projection(
                ast::ProjectionDecl {
                    name: "Boolean".into(),
                    guest: "Bool".into(),
                    host: "Bool".into(),
                    direction: ast::ProjectionDirection::Both,
                    body: ast::ProjectionBody::Carrier,
                    span,
                },
            )]),
            span,
        };
        assert!(elaborate_module_ast(module.clone(), &resolver).is_err());
        let host = mettail_grammar_core::ProjectionHostSignatureV1 {
            signature_fingerprint: [7; 32],
            codec_profile_fingerprint: [9; 32],
            sorts: vec![mettail_grammar_core::TheorySortV1 {
                name: "Bool".into(),
                kind: mettail_grammar_core::TheorySortKindV1::Syntax {
                    literal: Some(mettail_grammar_core::TheoryLiteralCarrierV1::Boolean),
                },
            }],
            constructors: Vec::new(),
        };
        let mut exports = elaborate_module_ast_with_host(module, &resolver, &host)
            .expect("bound host signature admits the versioned projection")
            .exports;
        let projected = exports.remove(0).language;
        let versioned = projected
            .projected_language_core
            .as_ref()
            .expect("projection retained");
        assert_eq!(versioned.projections.len(), 1);
        assert_eq!(versioned.base, projected.language_core);
        let mut equivalent_unprojected_value = projected.canonical_value.clone();
        let canonical::RhoValue::Map(ref mut equivalent_fields) = equivalent_unprojected_value
        else {
            panic!("language canonical value is a map");
        };
        equivalent_fields.remove("projections");
        equivalent_fields
            .insert("mettail".into(), canonical::RhoValue::String("language/3".into()));
        let equivalent_unprojected =
            canonical::value_to_language_core(&equivalent_unprojected_value).unwrap();
        assert_eq!(
            versioned.base.grammar_fingerprint().unwrap(),
            equivalent_unprojected.grammar_fingerprint().unwrap()
        );
        assert_ne!(
            versioned.base.grammar_fingerprint().unwrap(),
            plain.language_core.grammar_fingerprint().unwrap(),
            "different schema versions retain separate grammar identities"
        );
        let canonical::RhoValue::Map(ref map) = projected.canonical_value else {
            panic!("language canonical value is a map");
        };
        assert_eq!(map.get("mettail"), Some(&canonical::RhoValue::String("language/4".into())));
        assert!(canonical::value_to_language_core(&projected.canonical_value).is_err());
    }

    #[test]
    fn data_builder_carries_exhaustive_fields_through_source_syntax() {
        let source = r#"
            Module Dynamic {
              Theory T() {
                Data({
                  "options": {"beam_width": 1.5, "dispatch": "weighted"},
                  "types": ["Expr"],
                  "tokens": [{"name":"Word", "pattern":"[a-z]+", "category":"Expr"}],
                  "terms": [{"label":"WordExpr", "category":"Expr",
                             "syntax":[["tok","Word",Nil]]}],
                  "relations": [{"relation":"Same", "params":["Expr","Expr"],
                    "rules":[{"head":["rel","Same",["x","x"]], "body":[]}]}]
                })
              }
              theory T()
            }
        "#;
        let resolver = resolve::MemResolver::new().with("Dynamic.module", source);
        let entry = resolve::ModuleRef::parse("Dynamic.module").expect("valid reference");
        let language = elaborate_language("Dynamic", &entry, &resolver).expect("elaborates");
        assert_eq!(
            language.grammar_core.parser_configuration.beam_width,
            mettail_grammar_core::BeamWidth::Explicit(1.5)
        );
        assert_eq!(language.grammar_core.semantic_program.relations.len(), 1);
        let canonical::RhoValue::Map(spec) = &language.canonical_value else {
            panic!("map")
        };
        assert!(spec.contains_key("tokens"));
        assert!(spec.contains_key("relations"));
    }

    #[test]
    fn data_builder_promotes_oslf_content_to_language3_without_reparse() {
        let source = r#"
            Module Semantic {
              Theory T() {
                Types { Datum; Grade; }
                Terms {
                  Zero . |- "zero" : Datum;
                  Wrap . x:Datum |- "wrap" x : Datum;
                }
                Equations { (Wrap X) == (Wrap X); }
                Rewrites { Unwrap : (Wrap X) ~> X; }
                Data({
                  "oslf": {
                    "effects": [{"name":"Pure", "requires":[], "emits":[]}],
                    "actions": [{
                      "id":"step", "domain":["Datum"], "codomain":"Datum",
                      "transition":["rewrite","Unwrap"],
                      "effect":"Pure", "effect_class":"pure",
                      "required_rights":["Reduce"], "grade":"Grade",
                      "execution":"one_step"
                    }]
                  }
                })
              }
              theory T()
            }
        "#;
        let resolver = resolve::MemResolver::new().with("Semantic.module", source);
        let entry = resolve::ModuleRef::parse("Semantic.module").expect("valid reference");
        let language = elaborate_language("Semantic", &entry, &resolver).expect("elaborates");
        let canonical::RhoValue::Map(spec) = &language.canonical_value else {
            panic!("canonical language is a map")
        };
        assert_eq!(spec.get("mettail"), Some(&canonical::RhoValue::String("language/3".into())));
        assert_eq!(
            language.language_core.theory.profile,
            mettail_grammar_core::TheoryProfileV1::Oslf
        );
        assert_eq!(language.language_core.theory.actions.len(), 1);
        assert_eq!(language.language_core.theory.equations.len(), 1);
        assert_eq!(language.language_core.theory.rewrites.len(), 1);
        let rewrite = &language.language_core.theory.rewrites[0];
        assert_eq!(rewrite.name, "Unwrap");
        assert!(matches!(
            rewrite.arena.terms[rewrite.left.0 as usize].form,
            mettail_grammar_core::TheoryTermFormV1::Constructor { ref constructor, .. }
                if constructor == "Wrap"
        ));
        assert!(matches!(
            rewrite.arena.terms[rewrite.right.0 as usize].form,
            mettail_grammar_core::TheoryTermFormV1::Variable(_)
        ));
        assert_eq!(
            language.language_core.theory.actions[0].required_rights,
            mettail_grammar_core::LanguageRights::from_rights([
                mettail_grammar_core::LanguageRight::Reduce,
            ])
        );
        assert_eq!(language.grammar_core, language.language_core.grammar);
        assert!(language.grammar_core.semantic_program.equations.is_empty());
        assert!(language.grammar_core.semantic_program.rewrites.is_empty());
        assert!(language.grammar_core.semantic_dependencies.is_empty());

        let encoded = core_value::language_core_to_value(&language.language_core)
            .expect("executable LanguageCore has an exact value encoding");
        let decoded = canonical::value_to_language_core(&encoded)
            .expect("exact executable LanguageCore value decodes");
        assert_eq!(decoded, language.language_core);

        let mut changed = decoded.clone();
        changed.theory.limits.max_steps -= 1;
        assert_eq!(
            changed.grammar_fingerprint().unwrap(),
            decoded.grammar_fingerprint().unwrap(),
            "semantic limits cannot split the parser projection"
        );
        assert_ne!(
            changed.theory_fingerprint().unwrap(),
            decoded.theory_fingerprint().unwrap(),
            "semantic limits are committed by the theory identity"
        );
        assert_ne!(
            changed.fingerprint().unwrap(),
            decoded.fingerprint().unwrap(),
            "the installed-language identity commits to the entire theory"
        );
    }

    #[test]
    fn language2_rules_remain_structural_and_data_compatible() {
        let source = r#"
            Theory Structural() {
              Types { Expr; }
              Terms { Wrap . x:Expr |- "wrap" x : Expr; }
              Equations { (Wrap X) == X; }
              Rewrites { Unwrap : (Wrap X) ~> X; }
            }
        "#;
        let language = elaborate_theory_language(source).expect("language/2 rules elaborate");
        assert_eq!(
            language.language_core.theory.profile,
            mettail_grammar_core::TheoryProfileV1::StructuralOnly
        );
        assert!(language.language_core.theory.equations.is_empty());
        assert!(language.language_core.theory.rewrites.is_empty());
        assert_eq!(language.grammar_core.semantic_program.equations.len(), 1);
        assert_eq!(language.grammar_core.semantic_program.rewrites.len(), 1);
        assert_eq!(
            canonical::value_to_core(&language.canonical_value).unwrap(),
            language.grammar_core
        );
    }

    #[test]
    fn exact_language_core_data_fragment_is_a_name_checked_left_inverse() {
        let expected = mettail_grammar_core::LanguageCoreV1::structural(
            mettail_grammar_core::GrammarCoreV1::new("Exact"),
        );
        expected
            .validate()
            .expect("minimal completed language is valid");
        let fragment = core_value::language_core_to_data_fragment(&expected)
            .expect("completed language has an exact Data fragment");
        let literal = rholang_literal::render_rholang_value_literal(&fragment)
            .expect("exact fragment has a Rholang value spelling");
        let source = format!("Theory Exact() {{ Data({literal}) }}");
        let actual = elaborate_theory_language(&source).expect("exact Data theory elaborates");

        assert_eq!(actual.language_core, expected);
        assert_eq!(actual.canonical_value, core_value::language_core_to_value(&expected).unwrap());

        let renamed = source.replacen("Theory Exact", "Theory Wrong", 1);
        let error = elaborate_theory_language(&renamed)
            .expect_err("a Theory wrapper cannot rename a completed LanguageCore");
        assert!(
            error
                .msg
                .contains("does not match completed GrammarCore name"),
            "{error}"
        );
    }

    #[test]
    fn exact_language_core_data_fragment_rejects_builder_mixing() {
        let expected = mettail_grammar_core::LanguageCoreV1::structural(
            mettail_grammar_core::GrammarCoreV1::new("Exact"),
        );
        let fragment = core_value::language_core_to_data_fragment(&expected).unwrap();
        let literal = rholang_literal::render_rholang_value_literal(&fragment).unwrap();
        let source = format!("Theory Exact() {{ Types {{ Extra; }} Data({literal}) }}");
        let error = elaborate_theory_language(&source)
            .expect_err("a completed core is not an additive presentation fragment");
        assert!(error.msg.contains("may be applied only to Empty"), "{error}");
    }

    #[test]
    fn standalone_closed_theory_uses_the_same_canonical_boundary() {
        let source = r#"Theory Tiny() {
            Types { Expr; }
            Terms { Zero . |- "0" : Expr; }
        }"#;
        let language = elaborate_theory_language(source).expect("closed theory elaborates");
        assert_eq!(language.grammar_core.name, "Tiny");
        assert_eq!(
            language.grammar_core,
            canonical::value_to_core(&language.canonical_value)
                .expect("canonical value lowers independently")
        );
    }

    #[test]
    fn standalone_open_theory_requires_an_explicit_module_application() {
        let error = elaborate_theory_language("Theory Open(base: Core) { base }")
            .expect_err("an unapplied theory is not a concrete language");
        assert!(error.msg.contains("install a Module that applies it"));
    }

    fn elaborate_on_small_stack(source: String) -> Result<Presentation, Diag> {
        std::thread::Builder::new()
            .name("mettail-evaluator-small-stack".into())
            .stack_size(256 * 1024)
            .spawn(move || {
                let resolver = resolve::MemResolver::new().with("rho:stack-test", &source);
                let entry =
                    resolve::ModuleRef::parse("rho:stack-test").expect("valid module reference");
                elaborate(&entry, &resolver)
            })
            .expect("spawn evaluator worker")
            .join()
            .expect("evaluator worker must not overflow or panic")
    }

    #[test]
    fn recursive_theory_application_is_rejected_as_a_source_order_violation() {
        let error = elaborate_on_small_stack(
            "Module Cycle { Theory Loop() { Loop() } theory Loop() }".into(),
        )
        .expect_err("recursive theory must be rejected");
        assert_eq!(error.kind, DiagKind::ForwardReference);
        assert!(error.msg.contains("before its declaration"), "{error}");
    }

    #[test]
    fn long_acyclic_theory_chain_uses_the_explicit_continuation_machine() {
        const DECLARATIONS: usize = 20_000;
        let mut source = String::from("Module Chain { Theory T0() { Empty }");
        for index in 1..DECLARATIONS {
            source.push_str(&format!(" Theory T{index}() {{ T{}() }}", index - 1));
        }
        source.push_str(&format!(" theory T{}() }}", DECLARATIONS - 1));
        let presentation =
            elaborate_on_small_stack(source).expect("acyclic theory chain elaborates");
        assert!(presentation.types.is_empty());
    }

    #[test]
    fn duplicate_theory_names_are_rejected_before_indexing() {
        let error = parse::parse_module(
            "Module Duplicate { Theory T() { Empty } Theory T() { Empty } theory T() }",
        )
        .expect_err("duplicate declaration must fail");
        assert_eq!(error.kind, DiagKind::DuplicateTheory);
    }

    #[test]
    fn module_entries_and_declarations_cannot_reference_later_theories() {
        let cases = [
            ("entry-first", "Module M { theory Later() Theory Later() { Empty } }"),
            (
                "declaration-body-first",
                "Module M { Theory First() { Later() } Theory Later() { Empty } theory First() }",
            ),
        ];
        for (reference, source) in cases {
            let resolver = resolve::MemResolver::new().with(reference, source);
            let error = elaborate_module_languages(
                &resolve::ModuleRef::parse(reference).expect("reference"),
                &resolver,
            )
            .expect_err("module lookup cannot observe a later declaration");
            assert_eq!(error.kind, DiagKind::ForwardReference);
        }
    }

    #[test]
    fn structural_entry_rejects_duplicate_theories_before_indexing() {
        let declaration = parse::parse_theory(
            r#"Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }"#,
        )
        .expect("fixture theory parses");
        let module = ast::ModuleFile {
            imports: Vec::new(),
            name: "Duplicate".into(),
            items: vec![
                ast::ModuleItem::TheoryDecl(declaration.clone()),
                ast::ModuleItem::TheoryDecl(declaration),
                ast::ModuleItem::TheoryEntry(ast::TheoryExpr::Apply {
                    head: ast::DottedPath(vec!["T".into()]),
                    args: Vec::new(),
                    span: lex::Span { line: 0, col: 0 },
                }),
            ],
            span: lex::Span { line: 0, col: 0 },
        };
        let error = elaborate_module_ast(module, &resolve::MemResolver::new())
            .expect_err("a forged structural AST must not bypass duplicate checks");
        assert_eq!(error.kind, DiagKind::DuplicateTheory);
    }

    #[test]
    fn structural_entry_cannot_bypass_canonical_module_validation() {
        let declaration = parse::parse_theory(
            r#"Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }"#,
        )
        .expect("fixture theory parses");
        let module = ast::ModuleFile {
            imports: Vec::new(),
            name: "not-a-canonical-identifier".into(),
            items: vec![
                ast::ModuleItem::TheoryDecl(declaration),
                ast::ModuleItem::TheoryEntry(ast::TheoryExpr::Apply {
                    head: ast::DottedPath(vec!["T".into()]),
                    args: Vec::new(),
                    span: lex::Span { line: 0, col: 0 },
                }),
            ],
            span: lex::Span { line: 0, col: 0 },
        };
        let error = elaborate_module_ast(module, &resolve::MemResolver::new())
            .expect_err("surface modules share closed module/1 validation");
        assert_eq!(error.kind, DiagKind::Value);
        assert!(error.msg.contains("not an ASCII identifier"));
    }

    #[test]
    fn module_elaborates_every_named_entry_in_source_order() {
        let source = r#"
            Module Pair {
              Theory Left() { Types { L; } Terms { L0 . |- "l" : L; } }
              Theory Right() { Types { R; } Terms { R0 . |- "r" : R; } }
              theory Left()
              theory Right()
            }
        "#;
        let resolver = resolve::MemResolver::new().with("Pair.module", source);
        let entry = resolve::ModuleRef::parse("Pair.module").expect("valid module reference");
        let module = elaborate_module_languages(&entry, &resolver).expect("module elaborates");

        assert_eq!(module.name, "Pair");
        assert_eq!(
            module
                .exports
                .iter()
                .map(|export| export.name.as_str())
                .collect::<Vec<_>>(),
            ["Left", "Right"]
        );
        assert_eq!(module.exports[0].language.grammar_core.name, "Left");
        assert_eq!(module.exports[1].language.grammar_core.name, "Right");
    }

    #[test]
    fn an_unrelated_preceding_export_cannot_change_a_language_fingerprint() {
        let single = r#"
            Module Single {
              Theory Right() { Types { R; } Terms { R0 . |- "r" : R; } }
              theory Right()
            }
        "#;
        let pair = r#"
            Module Pair {
              Theory Left() { Types { L; } Terms { L0 . |- "l" : L; } }
              Theory Right() { Types { R; } Terms { R0 . |- "r" : R; } }
              theory Left()
              theory Right()
            }
        "#;
        let single_resolver = resolve::MemResolver::new().with("single", single);
        let pair_resolver = resolve::MemResolver::new().with("pair", pair);
        let single = elaborate_module_languages(
            &resolve::ModuleRef::parse("single").expect("reference"),
            &single_resolver,
        )
        .expect("single export");
        let pair = elaborate_module_languages(
            &resolve::ModuleRef::parse("pair").expect("reference"),
            &pair_resolver,
        )
        .expect("two exports");

        assert_eq!(
            single.exports[0]
                .language
                .grammar_core
                .fingerprint()
                .expect("fingerprint"),
            pair.exports[1]
                .language
                .grammar_core
                .fingerprint()
                .expect("fingerprint")
        );
    }

    #[test]
    fn compound_and_duplicate_module_exports_fail_closed() {
        let unnamed = r#"
            Module Unnamed {
              Theory A() { Types { A; } }
              Theory B() { Types { B; } }
              theory A() \/ B()
            }
        "#;
        let duplicate = r#"
            Module Duplicate {
              Theory A() { Types { A; } }
              theory A()
              theory A()
            }
        "#;
        for (reference, source, expected) in [
            ("unnamed", unnamed, DiagKind::UnnamedExport),
            ("duplicate", duplicate, DiagKind::DuplicateExport),
        ] {
            let resolver = resolve::MemResolver::new().with(reference, source);
            let error = elaborate_module_languages(
                &resolve::ModuleRef::parse(reference).expect("reference"),
                &resolver,
            )
            .expect_err("invalid export set must fail");
            assert_eq!(error.kind, expected);
        }
    }
}
