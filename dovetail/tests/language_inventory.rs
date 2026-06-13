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

#[derive(Debug)]
struct DiscoveredLanguage {
    rocq_name: String,
    source_path: PathBuf,
    requirements: BTreeSet<Requirement>,
}

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

fn repo_relative(path: &Path) -> String {
    path.strip_prefix(repo_root())
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

fn is_language_macro_source(source: &str) -> bool {
    source
        .lines()
        .any(|line| line.trim_start().starts_with("language!"))
}

fn declared_language_names(source: &str) -> Vec<String> {
    let mut waiting_for_name = false;
    let mut names = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("language!") {
            waiting_for_name = true;
            continue;
        }
        if !waiting_for_name {
            continue;
        }
        let Some(rest) = trimmed.strip_prefix("name:") else {
            continue;
        };
        if let Some(name) = rest
            .trim()
            .trim_end_matches(',')
            .split(|ch: char| ch.is_whitespace() || ch == ',')
            .next()
            .filter(|name| !name.is_empty())
        {
            names.push(name.to_owned());
            waiting_for_name = false;
        }
    }
    names
}

fn rocq_inventory_names(source: &str) -> BTreeSet<String> {
    let marker = "inventory_name := \"";
    source
        .lines()
        .filter_map(|line| {
            let start = line.find(marker)? + marker.len();
            let rest = &line[start..];
            let end = rest.find('"')?;
            Some(rest[..end].to_owned())
        })
        .collect()
}

fn discover_rust_files(root: &Path) -> Vec<PathBuf> {
    let mut pending = vec![root.to_path_buf()];
    let mut files = Vec::new();
    while let Some(path) = pending.pop() {
        let metadata =
            fs::metadata(&path).unwrap_or_else(|err| panic!("failed to stat {path:?}: {err}"));
        if metadata.is_dir() {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            if matches!(name, "bin" | "generated") {
                continue;
            }
            for entry in fs::read_dir(&path)
                .unwrap_or_else(|err| panic!("failed to read directory {path:?}: {err}"))
            {
                pending.push(entry.expect("source directory entry").path());
            }
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs") {
            files.push(path);
        }
    }
    files.sort();
    files
}

fn discover_language_sources() -> Vec<DiscoveredLanguage> {
    discover_rust_files(&repo_root().join("languages/src"))
        .into_iter()
        .flat_map(|path| {
            let source = fs::read_to_string(&path)
                .unwrap_or_else(|err| panic!("failed to read {path:?}: {err}"));
            if !is_language_macro_source(&source) {
                return Vec::new();
            }
            let display_names = declared_language_names(&source);
            assert!(
                !display_names.is_empty(),
                "{} contains a language! macro without a `name:` declaration",
                repo_relative(&path)
            );
            let requirements = classify_source(&source);
            display_names
                .into_iter()
                .map(|display_name| DiscoveredLanguage {
                    rocq_name: display_name.to_ascii_lowercase(),
                    source_path: path.clone(),
                    requirements: requirements.clone(),
                })
                .collect::<Vec<_>>()
        })
        .collect()
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
    let rocq_names = rocq_inventory_names(&rocq_inventory);
    let discovered_languages = discover_language_sources();
    assert!(
        !discovered_languages.is_empty(),
        "no in-repo language! macro sources discovered"
    );

    let discovered_names = discovered_languages
        .iter()
        .map(|language| language.rocq_name.clone())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        discovered_names, rocq_names,
        "Rocq LanguageDefInventory must exactly match discovered language! sources"
    );

    let mut aggregate = BTreeSet::new();

    for language in &discovered_languages {
        assert!(
            !language.requirements.is_empty(),
            "{} did not classify any Dovetail rewrite requirement",
            repo_relative(&language.source_path)
        );
        assert!(
            rocq_inventory.contains(&format!("inventory_name := \"{}\"", language.rocq_name)),
            "Rocq LanguageDefInventory is missing {}",
            language.rocq_name
        );
        aggregate.extend(language.requirements.iter().copied());
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
