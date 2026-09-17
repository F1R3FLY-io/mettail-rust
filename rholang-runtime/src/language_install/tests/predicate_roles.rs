use super::*;
use crate::semantic_service::{InstalledSemanticBundle, InstalledSemanticError};
use mettail_grammar_core::{LanguageCoreV1, TheorySemanticImageV1};
use mettail_rholang_codegen::ReflectedCodecBudget;

fn predicate_language() -> LanguageCoreV1 {
    let ctor = |name: &str| l([s(name)]);
    let value = m([
        ("mettail", s("language/3")),
        ("name", s("Predicate")),
        ("types", l([s("Expr")])),
        (
            "terms",
            l([("Call", "call"), ("Yes", "yes"), ("No", "no")].map(|(label, text)| {
                m([
                    ("label", s(label)),
                    ("category", s("Expr")),
                    ("syntax", l([l([s("lit"), s(text)])])),
                ])
            })),
        ),
        (
            "rewrites",
            l([m([("name", s("Match")), ("left", ctor("Call")), ("right", ctor("Yes"))])]),
        ),
        (
            "oslf",
            m([
                ("effects", l([m([("name", s("pure"))])])),
                (
                    "actions",
                    l([m([
                        ("id", s("match")),
                        ("domain", l([s("Expr")])),
                        ("codomain", s("Expr")),
                        ("transition", l([s("rewrite"), s("Match")])),
                        ("effect", s("pure")),
                        ("grade", s("Expr")),
                        ("execution", s("one_step")),
                    ])]),
                ),
                (
                    "observations",
                    l([m([
                        ("name", s("Matches")),
                        ("action", s("match")),
                        ("result", s("Expr")),
                        (
                            "predicate_role",
                            m([
                                ("input_constructor", s("Call")),
                                ("accepting", ctor("Yes")),
                                ("rejecting", ctor("No")),
                            ]),
                        ),
                    ])]),
                ),
            ]),
        ),
    ]);
    mettail_elab::canonical::value_to_language_core(&value).expect("closed predicate fixture")
}

fn invalid_cached_predicate() -> (LanguageCoreV1, TheorySemanticImageV1) {
    let mut language = predicate_language();
    let limits = TheoryImageAdmissionLimits::default();
    let mut image = compile_theory_semantic_image(&language, limits).expect("valid image");
    let role = language.theory.observations[0]
        .predicate_role
        .as_mut()
        .expect("role");
    role.rejecting = role.accepting.clone();
    // An untrusted cache can copy the new source commitment. Structural image
    // admission is not proof that the native result constants are distinct.
    image.language_fingerprint = language.fingerprint().expect("language commitment");
    image.theory_fingerprint = language.theory_fingerprint().expect("theory commitment");
    image
        .validate(&language, limits)
        .expect("source-exact image layout");
    (language, image)
}

#[test]
fn predicate_roles_reject_fresh_and_cached_invalid_constants_before_publication() {
    let (language, image) = invalid_cached_predicate();
    let value =
        mettail_elab::core_value::language_core_to_value(&language).expect("canonical role data");
    let mut record = RegistryLanguageRecord::new(value.clone());
    record.semantic_image = Some(
        image
            .encode(&language, TheoryImageAdmissionLimits::default())
            .expect("untrusted image bytes"),
    );
    let registry = MemoryRegistry {
        languages: HashMap::from([("rho:predicate".into(), record)]),
        ..MemoryRegistry::default()
    };
    let service = LanguageInstallService::new(Arc::new(registry), LanguageInstallPolicy::default());
    for candidate in [
        InstallCandidate::Canonical(value),
        InstallCandidate::RegistryLanguage("rho:predicate".into()),
    ] {
        assert!(matches!(
            service.install(candidate),
            Err(InstallServiceError::Canonical(InstallExecutableRegistryError::CompileSemantic(
                _
            )))
        ));
        assert_eq!(service.installed_count().expect("unchanged publication"), 0);
    }
    let valid = mettail_elab::core_value::language_core_to_value(&predicate_language())
        .expect("valid role data");
    service
        .install(InstallCandidate::Canonical(valid))
        .expect("valid install after both refusals");
    assert_eq!(service.installed_count().expect("one published language"), 1);
}

#[test]
fn predicate_roles_defend_the_factory_after_direct_core_table_install() {
    let (language, image) = invalid_cached_predicate();
    let parser = compile_parser_image(&language.grammar).expect("parser");
    let table = InstalledLanguageTable::new();
    let grant = table
        .install_executable_runtime(
            language,
            parser,
            image,
            LanguageRights::all(),
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            "test/predicate/1",
            [0; 32],
            TheoryImageAdmissionLimits::default(),
        )
        .expect("lower-level core table does not execute native terms");
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 1_000_000, &mut cancel);
    assert!(matches!(
        InstalledSemanticBundle::prepare(
            &table,
            &grant.handle,
            &[LanguageRight::Observe],
            &mut budget
        ),
        Err(InstalledSemanticError::PredicateRole(_))
    ));
    assert!(budget.work_used() > 0, "failed native check retains consumed work");
}
