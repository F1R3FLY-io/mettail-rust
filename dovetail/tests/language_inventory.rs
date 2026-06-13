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

fn rocq_current_requirement_names(source: &str) -> BTreeSet<String> {
    let marker = "Definition current_mettail_rewrite_requirements";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("Rocq coverage file missing `{marker}`"));
    let list_source = &source[start..];
    let open = list_source
        .find('[')
        .unwrap_or_else(|| panic!("Rocq current requirement list has no opening `[`"));
    let close = list_source[open..]
        .find(']')
        .unwrap_or_else(|| panic!("Rocq current requirement list has no closing `]`"));

    list_source[open + 1..open + close]
        .split(|ch: char| ch == ';' || ch.is_whitespace())
        .filter(|token| token.starts_with("Req"))
        .map(ToOwned::to_owned)
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

#[derive(Debug)]
struct RelationDecl {
    head: String,
    params: Vec<String>,
}

fn declared_relation(line: &str) -> Option<RelationDecl> {
    let line = line.trim();
    let marker = "relation ";
    let marker_start = line.find(marker)?;
    let after_marker = &line[marker_start + marker.len()..];
    let open = after_marker.find('(')?;
    let close = after_marker[open + 1..].find(')')? + open + 1;
    let head = after_marker[..open].trim();
    if head.is_empty()
        || !head
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
    {
        return None;
    }

    let params = split_relation_params(&after_marker[open + 1..close]);
    Some(RelationDecl { head: head.to_owned(), params })
}

fn split_relation_params(params: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut start = 0usize;
    let mut angle_depth = 0usize;

    for (idx, ch) in params.char_indices() {
        match ch {
            '<' => angle_depth += 1,
            '>' => angle_depth = angle_depth.saturating_sub(1),
            ',' if angle_depth == 0 => {
                let param = params[start..idx].trim();
                if !param.is_empty() {
                    out.push(param.to_owned());
                }
                start = idx + ch.len_utf8();
            },
            _ => {},
        }
    }

    let param = params[start..].trim();
    if !param.is_empty() {
        out.push(param.to_owned());
    }
    out
}

fn is_generated_category_relation(decl: &RelationDecl) -> bool {
    let [payload_type] = decl.params.as_slice() else {
        return false;
    };
    decl.head == payload_type.to_ascii_lowercase()
}

fn category_relation_heads_from_datalog(source: &str) -> BTreeSet<String> {
    let relation_prelude = source.split("// Category rules").next().unwrap_or(source);
    relation_prelude
        .lines()
        .filter_map(declared_relation)
        .filter(is_generated_category_relation)
        .map(|decl| decl.head)
        .collect()
}

fn generated_category_heads(source: &str) -> BTreeSet<String> {
    let mut in_category_info = false;
    let mut brace_depth = 0usize;
    let mut heads = BTreeSet::new();

    for line in source.lines() {
        if !in_category_info {
            if line.contains("export const categoryInfo = {") {
                in_category_info = true;
                brace_depth = 1;
            }
            continue;
        }

        let trimmed = line.trim();
        if brace_depth == 1 && trimmed.ends_with('{') {
            if let Some((head, _)) = trimmed.split_once(':') {
                let head = head.trim().trim_matches('"').trim_matches('\'');
                if !head.is_empty() {
                    heads.insert(head.to_ascii_lowercase());
                }
            }
        }

        for ch in line.chars() {
            match ch {
                '{' => brace_depth += 1,
                '}' => brace_depth = brace_depth.saturating_sub(1),
                _ => {},
            }
        }
        if brace_depth == 0 {
            break;
        }
    }

    heads
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
fn generated_category_heads_are_derived_from_relation_signatures() {
    let source = r#"
        ascent_source! {
            sample_source:

            // Relations
            relation proc(Proc);
            #[ds(crate::eqrel)] relation eq_proc(Proc, Proc);
            #[ds(crate::dual_indexed)] relation rw_proc(Proc, Proc);
            relation name(Name);
            relation step_term(Proc);
            #[ds(crate::dual_indexed)] relation ppar_contains(Proc, Proc);

            // Category rules
            proc(t) <-- proc(t);
        }
    "#;

    assert_eq!(
        category_relation_heads_from_datalog(source),
        BTreeSet::from(["name".to_owned(), "proc".to_owned()])
    );
}

fn rocq_requirement_name(requirement: Requirement) -> &'static str {
    match requirement {
        Requirement::Equation => "ReqEquation",
        Requirement::DirectionalRewrite => "ReqDirectionalRewrite",
        Requirement::CongruencePremise => "ReqCongruencePremise",
        Requirement::FoldNativeHandler => "ReqFoldNativeHandler",
        Requirement::FreshnessPremise => "ReqFreshnessPremise",
        Requirement::EnvRelationPremise => "ReqEnvRelationPremise",
        Requirement::BehavioralGuard => "ReqBehavioralGuard",
        Requirement::SyntheticInjectionGuard => "ReqSyntheticInjectionGuard",
        Requirement::CollectionPattern => "ReqCollectionPattern",
        Requirement::MapPattern => "ReqMapPattern",
        Requirement::ZipPattern => "ReqZipPattern",
        Requirement::BinderPattern => "ReqBinderPattern",
        Requirement::SubstitutionPattern => "ReqSubstitutionPattern",
        Requirement::RhoCommHandlerContract => "ReqRhoCommHandlerContract",
        Requirement::RhoResourceGuardContract => "ReqRhoResourceGuardContract",
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

    let formal_coverage =
        read_repo_file("dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v");
    let formal_requirements = rocq_current_requirement_names(&formal_coverage);
    let aggregate_requirements = aggregate
        .iter()
        .map(|requirement| rocq_requirement_name(*requirement).to_owned())
        .collect::<BTreeSet<_>>();
    assert!(
        aggregate_requirements.is_subset(&formal_requirements),
        "source-classified LanguageDef requirements are not covered by Rocq current_mettail_rewrite_requirements: source={aggregate_requirements:?}, formal={formal_requirements:?}"
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
    let mut category_metadata_pairs = 0usize;
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

        let category_path = path.with_file_name(
            path.file_name()
                .and_then(|name| name.to_str())
                .expect("generated Datalog file name")
                .replace("-datalog.rs", "-categories.ts"),
        );
        if category_path.exists() {
            category_metadata_pairs += 1;
            let category_source = fs::read_to_string(&category_path)
                .unwrap_or_else(|err| panic!("failed to read {category_path:?}: {err}"));
            let category_heads = generated_category_heads(&category_source);
            assert!(
                !category_heads.is_empty(),
                "{} has no generated category metadata heads to audit",
                category_path.display()
            );
            let relation_category_heads = category_relation_heads_from_datalog(&source);
            assert_eq!(
                category_heads, relation_category_heads,
                "{} generated category metadata must exactly match generated Datalog category relations",
                path.display(),
            );
        }
    }

    assert!(
        category_metadata_pairs > 0,
        "no generated Datalog/category metadata pairs found"
    );
    assert!(
        unknown_heads.is_empty(),
        "unclassified generated Datalog relation heads: {unknown_heads:#?}"
    );
    assert!(
        !classified.is_empty(),
        "generated Datalog did not expose any classified relation families"
    );
    let formal_coverage =
        read_repo_file("dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v");
    let formal_requirements = rocq_current_requirement_names(&formal_coverage);
    let classified_requirements = classified
        .iter()
        .map(|requirement| rocq_requirement_name(*requirement).to_owned())
        .collect::<BTreeSet<_>>();
    assert!(
        classified_requirements.is_subset(&formal_requirements),
        "generated Datalog relation families are not covered by Rocq current_mettail_rewrite_requirements: generated={classified_requirements:?}, formal={formal_requirements:?}"
    );
}
