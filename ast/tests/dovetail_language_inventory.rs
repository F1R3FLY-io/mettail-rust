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

fn language_files() -> Vec<PathBuf> {
    let root = repo_root().join("languages/src");
    let mut pending = vec![root];
    let mut files = Vec::new();

    while let Some(path) = pending.pop() {
        let metadata =
            fs::metadata(&path).unwrap_or_else(|e| panic!("stat {}: {e}", path.display()));
        if metadata.is_dir() {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            if matches!(name, "bin" | "generated") {
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
        SyntaxExpr::Literal(_) | SyntaxExpr::Param(_) | SyntaxExpr::TokenKind { .. } => {},
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

#[test]
fn current_language_defs_have_dovetail_requirement_inventory() {
    let mut languages = Vec::new();
    let source_files = language_files();
    for path in &source_files {
        let source =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let file =
            syn::parse_file(&source).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
        collect_language_macros(&file.items, &mut languages);
    }

    let rocq_inventory =
        read_repo_file("dovetail/formal/rocq/theories/Requirements/LanguageDefInventory.v");
    let rocq_names = rocq_inventory_names(&rocq_inventory);

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
    let production: Vec<&LanguageDef> =
        languages.iter().filter(|language| !is_parse_only(language)).collect();

    let language_names = production
        .iter()
        .map(|language| language.name.to_string().to_ascii_lowercase())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        language_names.len(),
        production.len(),
        "duplicate in-repo production language! names discovered"
    );
    assert_eq!(
        language_names, rocq_names,
        "AST LanguageDef parser inventory (production languages) must exactly match Rocq LanguageDefInventory"
    );

    assert_eq!(
        rocq_names.len(),
        production.len(),
        "Rocq LanguageDefInventory and parsed production language! inventory have different cardinality"
    );

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
