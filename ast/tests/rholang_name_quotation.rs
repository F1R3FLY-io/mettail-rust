//! Derived guard for the upstream Rholang rule that a `Name` is a quoted `Proc`.
//!
//! The subject is computed from the parsed `language!` definition: every `Name` production
//! carrying a direct `Proc` parameter is inspected.  No roster of quote-rule labels or source
//! lines is maintained here, so adding another process-to-name surface automatically widens the
//! check.  Grouping rules such as `Name -> "(" Name ")"` are outside the subject because they do
//! not turn a process into a name.

use mettail_ast::grammar::{SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use std::fs;
use std::path::PathBuf;
use syn::{Item, ItemMacro};

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("ast crate has a workspace parent")
        .to_path_buf()
}

fn rholang_definition() -> LanguageDef {
    let path = workspace_root().join("languages/src/rholang.rs");
    let source = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|error| panic!("parse {} as Rust: {error}", path.display()));

    fn find(items: &[Item]) -> Option<LanguageDef> {
        for item in items {
            match item {
                Item::Macro(ItemMacro { mac, .. }) if mac.path.is_ident("language") => {
                    let definition: LanguageDef = syn::parse2(mac.tokens.clone())
                        .unwrap_or_else(|error| panic!("parse Rholang language body: {error}"));
                    if definition.name == "Rholang" {
                        return Some(definition);
                    }
                },
                Item::Mod(module) => {
                    if let Some((_, nested)) = &module.content {
                        if let Some(definition) = find(nested) {
                            return Some(definition);
                        }
                    }
                },
                _ => {},
            }
        }
        None
    }

    find(&file.items).expect("languages/src/rholang.rs declares `language! { name: Rholang }`")
}

#[test]
fn every_direct_process_to_name_surface_requires_the_quote_prefix() {
    let definition = rholang_definition();
    let mut audited = Vec::new();
    let mut violations = Vec::new();

    for rule in &definition.terms {
        if rule.category != "Name" {
            continue;
        }
        let process_parameters: Vec<_> = rule
            .term_context
            .as_deref()
            .unwrap_or_default()
            .iter()
            .filter_map(|parameter| match parameter {
                TermParam::Simple { name, ty } if ty.to_string() == "Proc" => Some(name),
                _ => None,
            })
            .collect();
        if process_parameters.is_empty() {
            continue;
        }

        audited.push(rule.label.to_string());
        let syntax = rule.syntax_pattern.as_deref().unwrap_or_default();
        let first_process = syntax.iter().position(
            |part| matches!(part, SyntaxExpr::Param(name) if process_parameters.contains(&name)),
        );
        let quote_prefix = syntax
            .iter()
            .position(|part| matches!(part, SyntaxExpr::Literal(text) if text == "@"));

        if first_process.is_none()
            || quote_prefix.is_none()
            || quote_prefix.expect("checked") > first_process.expect("checked")
        {
            violations.push(format!("{}: {syntax:#?}", rule.label));
        }
    }

    assert!(
        audited.len() >= 2,
        "anti-vacuity: expected multiple derived process-to-name productions, found {audited:?}"
    );
    assert!(
        violations.is_empty(),
        "a `Name` production admits a direct `Proc` without first consuming upstream Rholang's \
         required `@` quote prefix:\n{}",
        violations.join("\n"),
    );
}
