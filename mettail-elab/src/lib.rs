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
pub mod registry;
pub mod resolve;
pub mod rholang_literal;
mod schema;
pub mod wire;

pub use diag::{Diag, DiagKind, SourceProvenance};
pub use pres::Presentation;

#[derive(Debug)]
pub struct ElaboratedLanguage {
    pub presentation: Presentation,
    pub canonical_value: canonical::RhoValue,
    /// Authoritative complete syntax-and-theory artifact.
    pub language_core: mettail_grammar_core::LanguageCoreV1,
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
    finish_language(name, presentation)
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
    elaborate_program_languages(&program, entry)
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
    elaborate_program_languages(&program, entry)
}

fn elaborate_program_languages(
    program: &resolve::Program,
    entry: &resolve::ModuleRef,
) -> Result<ElaboratedModule, Diag> {
    let elaborated = elaborate_loaded_module(&program, entry)?;
    for (reference, expected) in program.registry_module_expectations() {
        let actual = if reference == entry {
            &elaborated.canonical_value
        } else {
            let imported = elaborate_loaded_module(&program, reference)?;
            if &imported.canonical_value != expected {
                return Err(Diag::new(
                    DiagKind::RegistryProjection,
                    format!(
                        "signed Registry module `{reference}` does not equal the canonical module/1 value elaborated from its committed source graph"
                    ),
                    program
                        .module(reference)
                        .map(|module| module.span)
                        .unwrap_or(lex::Span { line: 0, col: 0 }),
                )
                .with_provenance(module_provenance(&program, reference)));
            }
            continue;
        };
        if actual != expected {
            return Err(Diag::new(
                DiagKind::RegistryProjection,
                format!(
                    "signed Registry module `{reference}` does not equal the canonical module/1 value elaborated from its committed source graph"
                ),
                program
                    .module(reference)
                    .map(|module| module.span)
                    .unwrap_or(lex::Span { line: 0, col: 0 }),
            )
            .with_provenance(module_provenance(&program, reference)));
        }
    }
    Ok(elaborated)
}

fn elaborate_loaded_module(
    program: &resolve::Program,
    reference: &resolve::ModuleRef,
) -> Result<ElaboratedModule, Diag> {
    elaborate_loaded_module_unannotated(program, reference).map_err(|mut error| {
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
            finish_language(&name, presentation)
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
    finish_language(&name, presentation)
}

fn finish_language(name: &str, presentation: Presentation) -> Result<ElaboratedLanguage, Diag> {
    let canonical_value =
        canonical::presentation_to_value(name, &presentation).map_err(|error| {
            Diag::new(DiagKind::Value, error.to_string(), lex::Span { line: 0, col: 0 })
        })?;
    // The ordinary Rholang value is the semantic authority. Keep this decode
    // boundary even though `presentation` is already available so the surface
    // DDL and programmatically constructed values cannot acquire distinct
    // lowering behavior.
    let language_core = canonical::value_to_language_core(&canonical_value).map_err(|error| {
        Diag::new(
            DiagKind::Resolution,
            format!("cannot lower canonical language value: {error:?}"),
            lex::Span { line: 0, col: 0 },
        )
    })?;
    Ok(ElaboratedLanguage {
        presentation,
        canonical_value,
        grammar_core: language_core.grammar.clone(),
        language_core,
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
                Data({
                  "types": ["Datum", "Grade"],
                  "oslf": {
                    "effects": [{"name":"Pure", "requires":[], "emits":[]}],
                    "actions": [{
                      "id":"step", "domain":["Datum"], "codomain":"Datum",
                      "transition":["handler","mtl:handler:step/1"],
                      "effect":"Pure", "grade":"Grade"
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
        assert_eq!(language.grammar_core, language.language_core.grammar);
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
