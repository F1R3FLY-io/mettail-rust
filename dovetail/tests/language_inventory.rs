use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Requirement {
    Equation,
    DirectionalRewrite,
    CongruencePremise,
    FoldNativeHandler,
    FreshnessPremise,
    EnvRelationPremise,
    BehavioralGuard,
    SyntheticInjectionGuard,
    CollectionPattern,
    MapPattern,
    ZipPattern,
    BinderPattern,
    SubstitutionPattern,
    RhoCommHandlerContract,
    RhoResourceGuardContract,
}

struct LanguageSpec {
    rocq_name: &'static str,
    source_path: &'static str,
    display_name: &'static str,
    expected: &'static [Requirement],
}

const CURRENT_LANGUAGE_SOURCES: &[LanguageSpec] = &[
    LanguageSpec {
        rocq_name: "ambient",
        source_path: "languages/src/ambient.rs",
        display_name: "Ambient",
        expected: &[
            Requirement::Equation,
            Requirement::DirectionalRewrite,
            Requirement::CongruencePremise,
            Requirement::FreshnessPremise,
            Requirement::CollectionPattern,
            Requirement::BinderPattern,
        ],
    },
    LanguageSpec {
        rocq_name: "calculator",
        source_path: "languages/src/calculator.rs",
        display_name: "Calculator",
        expected: &[
            Requirement::DirectionalRewrite,
            Requirement::CongruencePremise,
            Requirement::FoldNativeHandler,
            Requirement::CollectionPattern,
            Requirement::MapPattern,
        ],
    },
    LanguageSpec {
        rocq_name: "class2hashmapsmoke",
        source_path: "languages/src/class2hashmapsmoke.rs",
        display_name: "Class2HashMapSmoke",
        expected: &[Requirement::MapPattern],
    },
    LanguageSpec {
        rocq_name: "class2multi",
        source_path: "languages/src/class2multi.rs",
        display_name: "Class2Multi",
        expected: &[Requirement::CollectionPattern],
    },
    LanguageSpec {
        rocq_name: "class2optsmoke",
        source_path: "languages/src/class2optsmoke.rs",
        display_name: "Class2OptSmoke",
        expected: &[Requirement::CollectionPattern],
    },
    LanguageSpec {
        rocq_name: "class2smoke",
        source_path: "languages/src/class2smoke.rs",
        display_name: "Class2Smoke",
        expected: &[Requirement::CollectionPattern],
    },
    LanguageSpec {
        rocq_name: "class3multi",
        source_path: "languages/src/class3multi.rs",
        display_name: "Class3Multi",
        expected: &[
            Requirement::CollectionPattern,
            Requirement::ZipPattern,
            Requirement::BinderPattern,
        ],
    },
    LanguageSpec {
        rocq_name: "class3opt",
        source_path: "languages/src/class3opt.rs",
        display_name: "Class3Opt",
        expected: &[
            Requirement::CollectionPattern,
            Requirement::ZipPattern,
            Requirement::BinderPattern,
        ],
    },
    LanguageSpec {
        rocq_name: "guardedrho",
        source_path: "languages/src/guarded_rho.rs",
        display_name: "GuardedRho",
        expected: &[
            Requirement::BehavioralGuard,
            Requirement::SyntheticInjectionGuard,
            Requirement::EnvRelationPremise,
            Requirement::RhoCommHandlerContract,
            Requirement::RhoResourceGuardContract,
            Requirement::CollectionPattern,
            Requirement::BinderPattern,
        ],
    },
    LanguageSpec {
        rocq_name: "lambda",
        source_path: "languages/src/lambda.rs",
        display_name: "Lambda",
        expected: &[
            Requirement::DirectionalRewrite,
            Requirement::CongruencePremise,
            Requirement::BinderPattern,
            Requirement::SubstitutionPattern,
        ],
    },
    LanguageSpec {
        rocq_name: "ledtest",
        source_path: "languages/src/led_test.rs",
        display_name: "LedTest",
        expected: &[
            Requirement::DirectionalRewrite,
            Requirement::CongruencePremise,
            Requirement::FoldNativeHandler,
        ],
    },
    LanguageSpec {
        rocq_name: "optsmoke",
        source_path: "languages/src/optsmoke.rs",
        display_name: "OptSmoke",
        expected: &[Requirement::FoldNativeHandler, Requirement::CollectionPattern],
    },
    LanguageSpec {
        rocq_name: "refinementsmoke",
        source_path: "languages/src/refinementsmoke.rs",
        display_name: "RefinementSmoke",
        expected: &[Requirement::EnvRelationPremise],
    },
    LanguageSpec {
        rocq_name: "rhocalc",
        source_path: "languages/src/rhocalc.rs",
        display_name: "RhoCalc",
        expected: &[
            Requirement::Equation,
            Requirement::DirectionalRewrite,
            Requirement::CongruencePremise,
            Requirement::FoldNativeHandler,
            Requirement::FreshnessPremise,
            Requirement::CollectionPattern,
            Requirement::MapPattern,
            Requirement::ZipPattern,
            Requirement::BinderPattern,
            Requirement::SubstitutionPattern,
            Requirement::RhoCommHandlerContract,
        ],
    },
    LanguageSpec {
        rocq_name: "basemath",
        source_path: "languages/src/composition/base_lang.rs",
        display_name: "BaseMath",
        expected: &[
            Requirement::DirectionalRewrite,
            Requirement::CongruencePremise,
            Requirement::FoldNativeHandler,
        ],
    },
    LanguageSpec {
        rocq_name: "extmath",
        source_path: "languages/src/composition/extended_lang.rs",
        display_name: "ExtMath",
        expected: &[
            Requirement::DirectionalRewrite,
            Requirement::CongruencePremise,
            Requirement::FoldNativeHandler,
        ],
    },
    LanguageSpec {
        rocq_name: "importedmath",
        source_path: "languages/src/composition/grammar_import_lang.rs",
        display_name: "ImportedMath",
        expected: &[
            Requirement::DirectionalRewrite,
            Requirement::CongruencePremise,
            Requirement::FoldNativeHandler,
        ],
    },
    LanguageSpec {
        rocq_name: "mixedmath",
        source_path: "languages/src/composition/mixed_lang.rs",
        display_name: "MixedMath",
        expected: &[
            Requirement::DirectionalRewrite,
            Requirement::CongruencePremise,
            Requirement::FoldNativeHandler,
        ],
    },
];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("dovetail crate has workspace parent")
        .to_path_buf()
}

fn read_repo_file(relative: &str) -> String {
    let path = repo_root().join(relative);
    fs::read_to_string(&path).unwrap_or_else(|err| panic!("failed to read {path:?}: {err}"))
}

fn classify_source(source: &str) -> BTreeSet<Requirement> {
    let mut reqs = BTreeSet::new();
    if source
        .lines()
        .any(|line| line.contains("|-") && line.contains(" = "))
    {
        reqs.insert(Requirement::Equation);
    }
    if source.contains("~>") || source.contains("extends: [BaseMath]") {
        reqs.insert(Requirement::DirectionalRewrite);
    }
    if (source.contains("| ") && source.contains("~>")) || source.contains("extends: [BaseMath]") {
        reqs.insert(Requirement::CongruencePremise);
    }
    if source.contains("] fold")
        || source.contains("] step")
        || source.contains("extends: [BaseMath]")
    {
        reqs.insert(Requirement::FoldNativeHandler);
    }
    if source.contains("# ") {
        reqs.insert(Requirement::FreshnessPremise);
    }
    if source.contains("logic {") || source.contains("relation ") || source.contains(" = { x:") {
        reqs.insert(Requirement::EnvRelationPremise);
    }
    if source.contains("?guard:Guard") || source.contains(" where ") {
        reqs.insert(Requirement::BehavioralGuard);
        reqs.insert(Requirement::SyntheticInjectionGuard);
    }
    if source.contains("HashBag(")
        || source.contains("Vec(")
        || source.contains("Vec<")
        || source.contains("...rest")
        || source.contains("*opt(")
        || source.contains(".*sep")
    {
        reqs.insert(Requirement::CollectionPattern);
    }
    if source.contains("HashMap<") || source.contains("HashMap(") || source.contains(":Map") {
        reqs.insert(Requirement::MapPattern);
    }
    if source.contains("*zip(") {
        reqs.insert(Requirement::ZipPattern);
    }
    if source.contains('^') && source.contains("->") {
        reqs.insert(Requirement::BinderPattern);
    }
    if source.contains("eval ") || source.contains("eval(") {
        reqs.insert(Requirement::SubstitutionPattern);
    }
    if source.contains("PInputs") || source.contains("POutput") || source.contains("PGuardedInput")
    {
        reqs.insert(Requirement::RhoCommHandlerContract);
    }
    if source.contains("guards {") {
        reqs.insert(Requirement::RhoResourceGuardContract);
    }
    reqs
}

fn relation_head(line: &str) -> Option<&str> {
    let line = line.trim();
    if !line.contains("<--") {
        return None;
    }
    let open = line.find('(')?;
    let head = line[..open].trim();
    (!head.is_empty()
        && head
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == '_'))
    .then_some(head)
}

fn declared_relation_head(line: &str) -> Option<&str> {
    let line = line.trim();
    let marker = "relation ";
    let marker_start = line.find(marker)?;
    let after_marker = &line[marker_start + marker.len()..];
    let open = after_marker.find('(')?;
    let head = after_marker[..open].trim();
    (!head.is_empty()
        && head
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == '_'))
    .then_some(head)
}

fn classify_datalog_head(head: &str) -> Option<Requirement> {
    if head.starts_with("rw_") {
        Some(Requirement::DirectionalRewrite)
    } else if head.starts_with("fold_") {
        Some(Requirement::FoldNativeHandler)
    } else if head.starts_with("eq_") {
        Some(Requirement::Equation)
    } else if head.ends_with("_contains") || head.ends_with("_vec") {
        Some(Requirement::CollectionPattern)
    } else {
        None
    }
}

#[test]
fn source_language_inventory_matches_rocq_inventory_and_taxonomy() {
    let rocq_inventory =
        read_repo_file("dovetail/formal/rocq/theories/Requirements/LanguageDefInventory.v");
    let mut aggregate = BTreeSet::new();

    for spec in CURRENT_LANGUAGE_SOURCES {
        let source = read_repo_file(spec.source_path);
        assert!(
            source.contains("language!")
                || source.contains("extends:")
                || source.contains("mixins:"),
            "{} is not a language source",
            spec.source_path
        );
        assert!(
            source.contains(&format!("name: {}", spec.display_name)),
            "{} does not declare expected language name {}",
            spec.source_path,
            spec.display_name
        );
        assert!(
            rocq_inventory.contains(&format!("inventory_name := \"{}\"", spec.rocq_name)),
            "Rocq LanguageDefInventory is missing {}",
            spec.rocq_name
        );

        let observed = classify_source(&source);
        for expected in spec.expected {
            assert!(
                observed.contains(expected),
                "{} did not classify expected requirement {:?}; observed {:?}",
                spec.source_path,
                expected,
                observed
            );
        }
        aggregate.extend(observed);
    }

    let required_language_surface = BTreeSet::from([
        Requirement::Equation,
        Requirement::DirectionalRewrite,
        Requirement::CongruencePremise,
        Requirement::FoldNativeHandler,
        Requirement::FreshnessPremise,
        Requirement::EnvRelationPremise,
        Requirement::BehavioralGuard,
        Requirement::SyntheticInjectionGuard,
        Requirement::CollectionPattern,
        Requirement::MapPattern,
        Requirement::ZipPattern,
        Requirement::BinderPattern,
        Requirement::SubstitutionPattern,
        Requirement::RhoCommHandlerContract,
        Requirement::RhoResourceGuardContract,
    ]);
    assert_eq!(
        aggregate, required_language_surface,
        "current source language inventory no longer matches the Dovetail requirement taxonomy"
    );
}

#[test]
fn generated_datalog_relation_heads_are_requirement_classified() {
    let generated_dir = repo_root().join("languages/src/generated");
    let mut datalog_files = fs::read_dir(&generated_dir)
        .unwrap_or_else(|err| panic!("failed to read {generated_dir:?}: {err}"))
        .map(|entry| entry.expect("generated dir entry").path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.ends_with("-datalog.rs"))
        })
        .collect::<Vec<_>>();
    datalog_files.sort();
    assert!(!datalog_files.is_empty(), "no generated Datalog files found");

    let mut classified = BTreeSet::new();
    let mut unknown_heads = Vec::new();
    for path in datalog_files {
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {path:?}: {err}"));
        let declared_heads = source
            .lines()
            .filter_map(declared_relation_head)
            .collect::<BTreeSet<_>>();
        assert!(
            !declared_heads.is_empty(),
            "{} has no generated relation declarations to audit",
            path.display()
        );

        for head in &declared_heads {
            if let Some(req) = classify_datalog_head(head) {
                classified.insert(req);
            }
        }

        for head in source.lines().filter_map(relation_head) {
            if let Some(req) = classify_datalog_head(head) {
                classified.insert(req);
            } else if !declared_heads.contains(head) {
                unknown_heads.push(format!("{}:{head}", path.display()));
            }
        }
    }

    assert!(
        unknown_heads.is_empty(),
        "unclassified generated Datalog relation heads: {unknown_heads:#?}"
    );
    for required in [
        Requirement::Equation,
        Requirement::DirectionalRewrite,
        Requirement::FoldNativeHandler,
        Requirement::CollectionPattern,
    ] {
        assert!(
            classified.contains(&required),
            "generated Datalog did not expose required relation family {:?}; classified {:?}",
            required,
            classified
        );
    }
}
