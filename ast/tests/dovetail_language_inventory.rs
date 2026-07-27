use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use mettail_ast::grammar::{GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam};
use mettail_ast::language::{AttributeValue, BehavioralPred, LanguageDef, Premise};
use mettail_ast::pattern::{Pattern, PatternTerm};
use mettail_ast::types::EvalMode;
use syn::{Item, ItemMacro};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Requirement {
    Equation,
    DirectionalRewrite,
    CongruencePremise,
    FoldNativeHandler,
    FreshnessPremise,
    EnvRelationPremise,
    ForAllPremise,
    BehavioralGuard,
    SyntheticInjectionGuard,
    CollectionPattern,
    MapPattern,
    ZipPattern,
    BinderPattern,
    SubstitutionPattern,
    ExactContentKey,
    RhoCommHandlerContract,
    RhoResourceGuardContract,
}

/// Directories that hold no hand-written source: build output and macro output.
///
/// Nothing else is skipped. A `bin` skip used to sit here too, which made
/// `languages/src/bin/` a place a definition could be written and never audited.
const NON_SOURCE_DIRECTORIES: &[&str] = &["target", "generated"];

/// Every directory that may hold a `language!` definition: the whole `languages`
/// package.
///
/// This scan used to enumerate `languages/src` and `languages/tests/definitions`, so a
/// definition in a top-level `languages/tests/*.rs` was in NEITHER root and left the
/// formal inventory silently — which is how `Pi` and `Turing` (equations, rewrites, a
/// freshness premise, a substituting COMM, a native fold, two transition rewrites) sat
/// outside coverage until `e1bfcd38`, and how `L9FltToy`/`L9ModalToy` (a `step` rewrite
/// and native `![…]` actions each) sat outside it until the roots were widened. The
/// root is the package, and
/// [`language_declarations_cannot_hide_outside_the_scanned_roots`] proves that choice
/// covers the whole repository.
///
/// # Why the root is READ rather than written here
///
/// `dovetail/tests/language_inventory.rs` audits the identical corpus by textual scan
/// where this one uses the real `LanguageDef` parser. The two audits stay INDEPENDENT —
/// that is the point of having both, and each enforces the repository-wide totality
/// invariant on its own — but they must agree on WHAT to read. When the list was written
/// out in both files, widening one and forgetting the other would have narrowed an audit
/// silently, which is exactly the failure the totality invariant exists to prevent and
/// exactly the kind a second literal reintroduces. Both now read the single declaration in
/// the workspace manifest, `[package.metadata.mettail] language_roots`, through
/// [`mettail_ast::manifest`].
fn language_definition_roots() -> Vec<PathBuf> {
    mettail_ast::manifest::language_roots(&repo_root()).unwrap_or_else(|err| {
        panic!(
            "cannot determine the language definition roots: {err}\n\nThis audit scans \
             exactly those roots, so it must NOT continue with a guess: an empty or \
             narrowed root list would make it pass by scanning nothing."
        )
    })
}

fn language_files() -> Vec<PathBuf> {
    let mut pending: Vec<PathBuf> = language_definition_roots()
        .into_iter()
        .filter(|root| root.exists())
        .collect();
    let mut files = Vec::new();

    while let Some(path) = pending.pop() {
        let metadata =
            fs::metadata(&path).unwrap_or_else(|e| panic!("stat {}: {e}", path.display()));
        if metadata.is_dir() {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            if NON_SOURCE_DIRECTORIES.contains(&name) {
                continue;
            }
            for entry in
                fs::read_dir(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
            {
                pending.push(entry.expect("dir entry").path());
            }
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            files.push(path);
        }
    }

    files.sort();
    files
}

/// Directories the repository-wide sweep does not enter.
///
/// `target` is build output and `scratchpad` is the gitignored, harness-wiped campaign
/// scratch area — a stale probe left in either must not be able to fail this suite.
/// DOT-directories are tooling state, never hand-written source: `.git` is object
/// storage, and `.formal-tmp` holds the formal pipeline's `cargo expand` dumps, two of
/// which are 40 MB single-item files that cost 13 seconds each to parse.
fn is_swept_over(directory_name: &str) -> bool {
    directory_name.starts_with('.') || matches!(directory_name, "target" | "scratchpad")
}

/// Whether `source` could contain a `language!` INVOCATION.
///
/// A Rust macro invocation is `path`, `!`, then a delimiter, with only whitespace and
/// comments allowed in between — so a file that never spells `language!` followed by
/// `(`, `[` or `{` cannot invoke it, and this gate cannot hide a declaration from the
/// sweep. It is a strict over-approximation in the other direction (a doc comment
/// showing `language! { … }` passes), which is harmless because `syn` then decides.
///
/// The gate matters because the parse behind it is the expensive step: the workspace
/// holds 179 files that merely NAME the macro, 7.2 MB in all, one of them 1.2 MB, and
/// `syn` in a debug test binary is slow enough on that to dominate the run. The gate
/// admits 57 files totalling 1.1 MB.
fn mentions_language_invocation(source: &str) -> bool {
    let bytes = source.as_bytes();
    source.match_indices("language!").any(|(at, needle)| {
        let mut index = at + needle.len();
        loop {
            match bytes.get(index) {
                Some(byte) if byte.is_ascii_whitespace() => index += 1,
                Some(b'/') if bytes.get(index + 1) == Some(&b'/') => {
                    index = source[index..]
                        .find('\n')
                        .map_or(bytes.len(), |end| index + end + 1);
                },
                Some(b'/') if bytes.get(index + 1) == Some(&b'*') => {
                    index = source[index + 2..]
                        .find("*/")
                        .map_or(bytes.len(), |end| index + 2 + end + 2);
                },
                Some(b'{' | b'(' | b'[') => return true,
                _ => return false,
            }
        }
    })
}

/// Every file in the repository that DECLARES a `language!`, wherever it lives.
///
/// Membership is decided by PARSING: a file is a declaration site iff `syn` finds an
/// item-level `language!` macro in it. That is exact where a text search is not — the
/// macro is named in documentation across a dozen crates, and emitted inside `quote!`
/// templates in `macros/`, none of which is a definition. Only files that could
/// possibly invoke it are parsed, so the sweep stays cheap.
///
/// A file that mentions `language!` but does not parse as Rust is reported rather than
/// skipped: silence there would be a hole of exactly the shape this sweep closes.
fn repository_language_declarations() -> BTreeSet<PathBuf> {
    let mut pending = vec![repo_root()];
    let mut declaring = BTreeSet::new();
    let mut unparsable = Vec::new();

    while let Some(path) = pending.pop() {
        let Ok(metadata) = fs::metadata(&path) else {
            continue; // a broken symlink is not a declaration
        };
        if metadata.is_dir() {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            if is_swept_over(name) {
                continue;
            }
            let Ok(entries) = fs::read_dir(&path) else {
                continue;
            };
            for entry in entries {
                pending.push(entry.expect("repository dir entry").path());
            }
            continue;
        }
        if path.extension().is_some_and(|ext| ext == "rs") {
            let source = fs::read_to_string(&path).unwrap_or_default();
            if !mentions_language_invocation(&source) {
                continue;
            }
            match syn::parse_file(&source) {
                Ok(file) => {
                    let mut found = Vec::new();
                    collect_language_macros(&file.items, &mut found);
                    if !found.is_empty() {
                        declaring.insert(path);
                    }
                },
                Err(_) => {
                    let mentions_at_item_position = source
                        .lines()
                        .any(|line| line.trim_start().starts_with("language!"));
                    if mentions_at_item_position {
                        unparsable.push(path.display().to_string());
                    }
                },
            }
        }
    }

    assert!(
        unparsable.is_empty(),
        "file(s) look like they declare a `language!` but do not parse as Rust, so the \
         sweep cannot tell whether they are inventoried: {unparsable:#?}"
    );
    declaring
}

/// A `parse_only: true` language is a syntax/lex-only test/demo fixture (no
/// reduction semantics) and is excluded from the production LanguageDefInventory.
fn is_parse_only(def: &LanguageDef) -> bool {
    matches!(def.options.get("parse_only"), Some(AttributeValue::Bool(true)))
}

/// Whether a language declares any reduction semantics. A `parse_only` language
/// MUST NOT — the inventory guard fails loudly otherwise, so a real reduction
/// language cannot hide behind the flag to escape the formal rewrite inventory.
fn has_reduction_semantics(def: &LanguageDef) -> bool {
    !def.equations.is_empty()
        || !def.rewrites.is_empty()
        || def.logic.is_some()
        || def.guard_config.is_some()
        || def
            .terms
            .iter()
            .any(|rule| rule.eval_mode.is_some() || rule.rust_code.is_some())
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .to_path_buf()
}

fn read_repo_file(relative: &str) -> String {
    let path = repo_root().join(relative);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

// `rocq_inventory_names` was removed with the name-level equality it served (task #69 S5):
// it scraped `inventory_name := "…"` out of `LanguageDefInventory.v` purely so this audit
// could compare name SETS. The mechanical inventory is generated now, and nothing else
// called it.

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

fn rocq_requirement_name(requirement: Requirement) -> &'static str {
    match requirement {
        Requirement::Equation => "ReqEquation",
        Requirement::DirectionalRewrite => "ReqDirectionalRewrite",
        Requirement::CongruencePremise => "ReqCongruencePremise",
        Requirement::FoldNativeHandler => "ReqFoldNativeHandler",
        Requirement::FreshnessPremise => "ReqFreshnessPremise",
        Requirement::EnvRelationPremise => "ReqEnvRelationPremise",
        Requirement::ForAllPremise => "ReqForAllPremise",
        Requirement::BehavioralGuard => "ReqBehavioralGuard",
        Requirement::SyntheticInjectionGuard => "ReqSyntheticInjectionGuard",
        Requirement::CollectionPattern => "ReqCollectionPattern",
        Requirement::MapPattern => "ReqMapPattern",
        Requirement::ZipPattern => "ReqZipPattern",
        Requirement::BinderPattern => "ReqBinderPattern",
        Requirement::SubstitutionPattern => "ReqSubstitutionPattern",
        Requirement::ExactContentKey => "ReqExactContentKey",
        Requirement::RhoCommHandlerContract => "ReqRhoCommHandlerContract",
        Requirement::RhoResourceGuardContract => "ReqRhoResourceGuardContract",
    }
}

fn collect_language_macros(items: &[Item], out: &mut Vec<LanguageDef>) {
    for item in items {
        match item {
            Item::Macro(item_macro) => collect_language_macro(item_macro, out),
            Item::Mod(item_mod) => {
                if let Some((_, nested)) = &item_mod.content {
                    collect_language_macros(nested, out);
                }
            },
            _ => {},
        }
    }
}

fn collect_language_macro(item_macro: &ItemMacro, out: &mut Vec<LanguageDef>) {
    if item_macro.mac.path.is_ident("language") {
        let def: LanguageDef = syn::parse2(item_macro.mac.tokens.clone())
            .unwrap_or_else(|e| panic!("parse language! body: {e}"));
        out.push(def);
    }
}

fn add_pattern_requirements(pattern: &Pattern, out: &mut BTreeSet<Requirement>) {
    match pattern {
        Pattern::Term(term) => add_pattern_term_requirements(term, out),
        Pattern::Collection { elements, .. } => {
            out.insert(Requirement::CollectionPattern);
            for element in elements {
                add_pattern_requirements(element, out);
            }
        },
        Pattern::Map { collection, body, .. } => {
            out.insert(Requirement::MapPattern);
            add_pattern_requirements(collection, out);
            add_pattern_requirements(body, out);
        },
        Pattern::Zip { first, second } => {
            out.insert(Requirement::ZipPattern);
            add_pattern_requirements(first, out);
            add_pattern_requirements(second, out);
        },
    }
}

fn add_pattern_term_requirements(term: &PatternTerm, out: &mut BTreeSet<Requirement>) {
    match term {
        PatternTerm::Var(_) => {
            out.insert(Requirement::ExactContentKey);
        },
        PatternTerm::Apply { args, .. } => {
            out.insert(Requirement::ExactContentKey);
            for arg in args {
                add_pattern_requirements(arg, out);
            }
        },
        PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
            out.insert(Requirement::BinderPattern);
            add_pattern_requirements(body, out);
        },
        PatternTerm::Subst { term, replacement, .. } => {
            out.insert(Requirement::SubstitutionPattern);
            add_pattern_requirements(term, out);
            add_pattern_requirements(replacement, out);
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            out.insert(Requirement::SubstitutionPattern);
            add_pattern_requirements(scope, out);
            for replacement in replacements {
                add_pattern_requirements(replacement, out);
            }
        },
    }
}

fn add_premise_requirements(premise: &Premise, out: &mut BTreeSet<Requirement>) {
    match premise {
        Premise::Freshness(_) => {
            out.insert(Requirement::FreshnessPremise);
        },
        Premise::Congruence { .. } => {
            out.insert(Requirement::CongruencePremise);
        },
        Premise::RelationQuery { .. } => {
            out.insert(Requirement::EnvRelationPremise);
        },
        Premise::ForAll { body, .. } => {
            out.insert(Requirement::ForAllPremise);
            add_premise_requirements(body, out);
        },
        Premise::BehavioralGuard(pred) => add_behavioral_pred_requirements(pred, out),
        Premise::SyntheticInjGuard { .. } => {
            out.insert(Requirement::SyntheticInjectionGuard);
        },
    }
}

fn add_behavioral_pred_requirements(pred: &BehavioralPred, out: &mut BTreeSet<Requirement>) {
    out.insert(Requirement::BehavioralGuard);
    match pred {
        BehavioralPred::RelationQuery { .. } | BehavioralPred::Top => {},
        BehavioralPred::Quantified { body, .. } => {
            out.insert(Requirement::ForAllPremise);
            add_behavioral_pred_requirements(body, out);
        },
        BehavioralPred::And(left, right)
        | BehavioralPred::Or(left, right)
        | BehavioralPred::Implies(left, right) => {
            add_behavioral_pred_requirements(left, out);
            add_behavioral_pred_requirements(right, out);
        },
        BehavioralPred::Not(body) => add_behavioral_pred_requirements(body, out),
        BehavioralPred::AcMatch { .. } => {
            out.insert(Requirement::CollectionPattern);
        },
    }
}

fn add_term_param_requirements(param: &TermParam, out: &mut BTreeSet<Requirement>) {
    match param {
        TermParam::Simple { .. } => {},
        TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. } => {
            out.insert(Requirement::BinderPattern);
        },
        TermParam::GuardBody { .. } => {
            out.insert(Requirement::BehavioralGuard);
            out.insert(Requirement::RhoResourceGuardContract);
        },
        TermParam::Optional { params } => {
            for nested in params {
                add_term_param_requirements(nested, out);
            }
        },
    }
}

fn add_syntax_expr_requirements(expr: &SyntaxExpr, out: &mut BTreeSet<Requirement>) {
    match expr {
        SyntaxExpr::Literal(_)
        | SyntaxExpr::Param(_)
        | SyntaxExpr::TokenKind { .. }
        | SyntaxExpr::GuestBody { .. } => {},
        SyntaxExpr::Op(op) => add_pattern_op_requirements(op, out),
    }
}

fn add_pattern_op_requirements(op: &PatternOp, out: &mut BTreeSet<Requirement>) {
    match op {
        PatternOp::Sep { source, .. } => {
            out.insert(Requirement::CollectionPattern);
            if let Some(source) = source {
                add_pattern_op_requirements(source, out);
            }
        },
        PatternOp::Zip { .. } => {
            out.insert(Requirement::ZipPattern);
        },
        PatternOp::Map { source, body, .. } => {
            out.insert(Requirement::MapPattern);
            add_pattern_op_requirements(source, out);
            for expr in body {
                add_syntax_expr_requirements(expr, out);
            }
        },
        PatternOp::Opt { inner } => {
            for expr in inner {
                add_syntax_expr_requirements(expr, out);
            }
        },
        PatternOp::Var(_) => {},
    }
}

fn add_rule_requirements(rule: &GrammarRule, out: &mut BTreeSet<Requirement>) {
    for item in &rule.items {
        match item {
            GrammarItem::Terminal(_) | GrammarItem::NonTerminal { .. } => {},
            GrammarItem::Binder { .. } => {
                out.insert(Requirement::BinderPattern);
            },
            GrammarItem::Collection { .. } => {
                out.insert(Requirement::CollectionPattern);
            },
        }
    }
    if let Some(params) = &rule.term_context {
        for param in params {
            add_term_param_requirements(param, out);
        }
    }
    if let Some(pattern) = &rule.syntax_pattern {
        for expr in pattern {
            add_syntax_expr_requirements(expr, out);
        }
    }
    match rule.eval_mode {
        Some(EvalMode::Fold) => {
            out.insert(Requirement::FoldNativeHandler);
        },
        Some(EvalMode::Step) => {
            out.insert(Requirement::DirectionalRewrite);
        },
        None => {},
    }
    if rule.rust_code.is_some() {
        out.insert(Requirement::FoldNativeHandler);
    }
}

fn classify_language(def: &LanguageDef) -> BTreeSet<Requirement> {
    let mut out = BTreeSet::new();
    out.insert(Requirement::ExactContentKey);
    for rule in &def.terms {
        add_rule_requirements(rule, &mut out);
    }
    if !def.equations.is_empty() {
        out.insert(Requirement::Equation);
    }
    for equation in &def.equations {
        add_pattern_requirements(&equation.left, &mut out);
        add_pattern_requirements(&equation.right, &mut out);
        for premise in &equation.premises {
            add_premise_requirements(premise, &mut out);
        }
    }
    if !def.rewrites.is_empty() {
        out.insert(Requirement::DirectionalRewrite);
    }
    for rewrite in &def.rewrites {
        add_pattern_requirements(&rewrite.left, &mut out);
        add_pattern_requirements(&rewrite.right, &mut out);
        for premise in &rewrite.premises {
            add_premise_requirements(premise, &mut out);
        }
        if rewrite.is_congruence_rule() {
            out.insert(Requirement::CongruencePremise);
        }
    }
    if def.logic.is_some() {
        out.insert(Requirement::EnvRelationPremise);
    }
    if let Some(guards) = &def.guard_config {
        out.insert(Requirement::BehavioralGuard);
        if guards.channels.is_some() {
            out.insert(Requirement::RhoCommHandlerContract);
            out.insert(Requirement::RhoResourceGuardContract);
        }
    }
    out
}

/// No `language!` in this repository lies outside the files this audit parses.
///
/// The structural twin of `dovetail/tests/language_inventory.rs`'s check of the same
/// name. Both are needed: the two audits read the corpus differently (this one parses,
/// the other scans text), so each must prove its own reach. Failing here means a
/// definition would be classified by neither, and its requirements would exist only in
/// the source.
#[test]
fn language_declarations_cannot_hide_outside_the_scanned_roots() {
    let audited: BTreeSet<PathBuf> = language_files().into_iter().collect();
    let declaring = repository_language_declarations();

    let escaped = declaring
        .difference(&audited)
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>();
    assert!(
        escaped.is_empty(),
        "{} file(s) declare a `language!` that this audit never parses, so nothing \
         checks their requirements against the Rocq inventory:\n{}\n\nMove the \
         definition under a scanned root, or widen `language_definition_roots`.",
        escaped.len(),
        escaped.join("\n  "),
    );

    assert!(
        declaring.len() >= 40,
        "the repository-wide sweep found only {} declaring file(s); it is not reaching \
         the source tree",
        declaring.len()
    );

    // The case the previous roots missed: a definition in a top-level
    // `languages/tests/*.rs`.
    let canary = repo_root().join("languages/tests/inventory_discovery_canary.rs");
    assert!(
        declaring.contains(&canary) && audited.contains(&canary),
        "the discovery canary must be both recognised and audited"
    );
}

#[test]
fn current_language_defs_have_dovetail_requirement_inventory() {
    let mut languages = Vec::new();
    let source_files = language_files();
    for path in &source_files {
        let source =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        // A file that declares a `language!` necessarily contains that text, so this
        // gate cannot hide a definition — it only spares `syn` the generated test
        // binaries and simulators the widened root now walks. Anything that passes the
        // gate is still parsed and decided structurally.
        if !source.contains("language!") {
            continue;
        }
        let file =
            syn::parse_file(&source).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
        collect_language_macros(&file.items, &mut languages);
    }

    assert!(!languages.is_empty(), "expected at least one in-repo language! definition");

    // Parse-only fixtures (syntax/lex demonstrations that declare
    // `options { parse_only: true }`, e.g. the keyword-reservation FortranModel/
    // ReservedModel) are excluded from the production LanguageDefInventory.
    // Fail-closed: a language is inventoried unless it explicitly opts out here.
    // Anti-loophole: a parse_only language must carry NO reduction semantics, or
    // this fails loudly — a real reduction language cannot hide behind the flag.
    for language in &languages {
        if is_parse_only(language) {
            assert!(
                !has_reduction_semantics(language),
                "language `{}` is marked `parse_only: true` but declares reduction \
                 semantics (equations/rewrites/logic/guards/fold/eval); parse_only \
                 is for syntax-only fixtures",
                language.name
            );
        }
    }
    let production: Vec<&LanguageDef> = languages
        .iter()
        .filter(|language| !is_parse_only(language))
        .collect();

    let language_names = production
        .iter()
        .map(|language| language.name.to_string().to_ascii_lowercase())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        language_names.len(),
        production.len(),
        "duplicate in-repo production language! names discovered"
    );
    // ── NAME-LEVEL EQUALITY IS GONE (task #69 S5) ────────────────────────────────
    //
    // This used to assert that the parsed production name set EQUALLED the names written
    // out in `LanguageDefInventory.v`, and that the two had the same cardinality. Adding a
    // language whose requirements were already covered therefore failed a Rocq-facing test
    // for a purely clerical reason, since the proofs in that file depend on the
    // REQUIREMENTS and never on the names. The mechanical inventory is now derived into
    // `LanguageDefInventoryGenerated.v` (see
    // `dovetail/tests/language_inventory.rs::generated_rocq_inventory_matches_the_discovered_sources`),
    // and what is asserted below is the property with formal content: every requirement
    // this parser observes is inside the taxonomy Rocq proves covered.
    //
    // The duplicate-name check above SURVIVES, and is now the only name-level assertion
    // here. It is about this repository's own coherence rather than about Rocq, and it is
    // the parser-side counterpart to `ast::registry`'s duplicate-registration error.

    assert!(
        source_files.len() >= languages.len(),
        "language source discovery found fewer Rust files than language definitions: files={}, languages={}",
        source_files.len(),
        languages.len()
    );

    let mut aggregate = BTreeSet::new();
    for language in &production {
        let reqs = classify_language(language);
        assert!(
            !reqs.is_empty(),
            "language {} produced an empty Dovetail requirement set",
            language.name
        );
        aggregate.extend(reqs);
    }

    assert!(
        !aggregate.is_empty(),
        "parsed LanguageDef inventory did not observe any Dovetail requirement"
    );

    let formal_coverage =
        read_repo_file("dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v");
    let formal_requirements = rocq_current_requirement_names(&formal_coverage);
    let aggregate_requirements = aggregate
        .iter()
        .map(|requirement| rocq_requirement_name(*requirement).to_owned())
        .collect::<BTreeSet<_>>();
    assert!(
        aggregate_requirements.is_subset(&formal_requirements),
        "parsed LanguageDef requirements are not covered by Rocq current_mettail_rewrite_requirements: parsed={aggregate_requirements:?}, formal={formal_requirements:?}"
    );
}
