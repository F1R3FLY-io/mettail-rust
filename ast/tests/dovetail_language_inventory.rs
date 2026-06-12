use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use mettail_ast::grammar::{GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam};
use mettail_ast::language::{BehavioralPred, LanguageDef, Premise};
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
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .join("languages/src");
    let mut files = Vec::new();
    for dir in [root.clone(), root.join("composition")] {
        for entry in fs::read_dir(&dir).unwrap_or_else(|e| panic!("read {}: {e}", dir.display())) {
            let path = entry.expect("dir entry").path();
            if path.extension().is_some_and(|ext| ext == "rs") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
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
        SyntaxExpr::Literal(_) | SyntaxExpr::Param(_) => {},
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
    for path in language_files() {
        let source =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let file =
            syn::parse_file(&source).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
        collect_language_macros(&file.items, &mut languages);
    }

    assert!(
        languages.len() >= 16,
        "expected the current in-repo language! inventory, got {}",
        languages.len()
    );

    let mut aggregate = BTreeSet::new();
    for language in &languages {
        let reqs = classify_language(language);
        assert!(
            !reqs.is_empty(),
            "language {} produced an empty Dovetail requirement set",
            language.name
        );
        aggregate.extend(reqs);
    }

    for required in [
        Requirement::Equation,
        Requirement::DirectionalRewrite,
        Requirement::CongruencePremise,
        Requirement::FoldNativeHandler,
        Requirement::FreshnessPremise,
        Requirement::CollectionPattern,
        Requirement::BinderPattern,
        Requirement::SubstitutionPattern,
        Requirement::ExactContentKey,
    ] {
        assert!(
            aggregate.contains(&required),
            "aggregate LanguageDef inventory did not observe {required:?}"
        );
    }
}
