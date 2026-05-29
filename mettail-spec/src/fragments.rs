use mettail_ast::fragments::{
    parse_equations_fragment, parse_literals_fragment, parse_relations_fragment,
    parse_rewrites_fragment, parse_terms_fragment, parse_types_fragment,
};
use mettail_ast::grammar::GrammarRule;
use proc_macro2::TokenStream;
use syn::Ident;

use crate::error::{Result, SpecError};
use crate::ntir::Presentation;
use crate::surface::SuffixKind;

pub fn apply_suffix(
    pres: &mut Presentation,
    kind: SuffixKind,
    tokens: TokenStream,
    raw: &str,
    module: &str,
) -> Result<()> {
    merge_raw_source(pres, kind, raw);
    match kind {
        SuffixKind::Types => {
            let types = parse_types_fragment(tokens).map_err(|e| SpecError::Fragment {
                module: module.to_string(),
                kind: "types".into(),
                source: e,
            })?;
            merge_types(pres, types)?;
        },
        SuffixKind::Terms => {
            let terms = parse_terms_fragment(tokens).map_err(|e| SpecError::Fragment {
                module: module.to_string(),
                kind: "terms".into(),
                source: e,
            })?;
            merge_terms(pres, terms)?;
        },
        SuffixKind::Literals => {
            let lit = parse_literals_fragment(tokens).map_err(|e| SpecError::Fragment {
                module: module.to_string(),
                kind: "literals".into(),
                source: e,
            })?;
            merge_literals(pres, lit)?;
        },
        SuffixKind::Equations => {
            let eqs = parse_equations_fragment(tokens).map_err(|e| SpecError::Fragment {
                module: module.to_string(),
                kind: "equations".into(),
                source: e,
            })?;
            merge_equations(pres, eqs)?;
        },
        SuffixKind::Rewrites => {
            let rws = parse_rewrites_fragment(tokens).map_err(|e| SpecError::Fragment {
                module: module.to_string(),
                kind: "rewrites".into(),
                source: e,
            })?;
            merge_rewrites(pres, rws)?;
        },
        SuffixKind::Relations => {
            let logic = parse_relations_fragment(tokens).map_err(|e| SpecError::Fragment {
                module: module.to_string(),
                kind: "relations".into(),
                source: e,
            })?;
            merge_logic(pres, logic)?;
        },
        SuffixKind::Exports => {
            let map = parse_exports_map(raw)?;
            apply_exports(pres, &map)?;
        },
        SuffixKind::Replacements => {
            let rules = parse_replacement_rules(tokens, raw, module)?;
            apply_replacements(pres, rules)?;
        },
    }
    Ok(())
}

/// Parse `exports { Elem => Proc , ... }` body (without outer braces).
pub fn parse_exports_map(raw: &str) -> Result<Vec<(String, String)>> {
    let mut out = Vec::new();
    for part in raw.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let (from, to) = part.split_once("=>").ok_or_else(|| SpecError::Assemble {
            message: format!("invalid export mapping '{part}' (expected 'From => To')"),
        })?;
        out.push((from.trim().to_string(), to.trim().to_string()));
    }
    Ok(out)
}

fn apply_exports(pres: &mut Presentation, map: &[(String, String)]) -> Result<()> {
    for (from, to) in map {
        rename_category(pres, from, to)?;
    }
    Ok(())
}

fn rename_category(pres: &mut Presentation, from: &str, to: &str) -> Result<()> {
    if from == to {
        return Ok(());
    }
    let to_ident = Ident::new(to, proc_macro2::Span::call_site());
    let from_ident = Ident::new(from, proc_macro2::Span::call_site());

    for ty in &mut pres.types {
        if ty.name == from {
            ty.name = to_ident.clone();
        }
    }
    for rule in &mut pres.terms {
        if rule.category == from_ident {
            rule.category = to_ident.clone();
        }
        for item in &mut rule.items {
            if let mettail_ast::grammar::GrammarItem::NonTerminal(nt) = item {
                if *nt == from_ident {
                    *nt = to_ident.clone();
                }
            }
        }
    }
    Ok(())
}

fn parse_replacement_rules(
    _tokens: TokenStream,
    raw: &str,
    module: &str,
) -> Result<Vec<(String, GrammarRule)>> {
    let mut rules = Vec::new();
    for segment in raw.split(';').map(str::trim).filter(|s| !s.is_empty()) {
        let (label, rhs) = segment
            .split_once("=>")
            .ok_or_else(|| SpecError::Assemble {
                message: format!("invalid replacement '{segment}'"),
            })?;
        let label = label.trim().trim_start_matches("[]").trim();
        let rhs = rhs.trim().trim_end_matches(';').trim();
        let rhs = format!("{rhs} ;");
        let mut parsed = parse_terms_from_rho_snippet(&rhs, module)?;
        if parsed.len() != 1 {
            return Err(SpecError::Assemble {
                message: format!("replacement for '{label}' must be exactly one term rule"),
            });
        }
        let rule = parsed.remove(0);
        rules.push((label.to_string(), rule));
    }
    Ok(rules)
}

/// Parse BNFC term rules using the `.rho` lexer/parser (same path as `terms { … }` suffixes).
fn parse_terms_from_rho_snippet(rhs: &str, module: &str) -> Result<Vec<GrammarRule>> {
    let synthetic = format!(
        "module InlineReplacements {{
  export extender E() {{
    empty
    terms {{ {} }}
  }}
}}
",
        rhs
    );
    let path = std::path::PathBuf::from(module);
    let file = crate::parser::parse_file(path, &synthetic).map_err(|e| SpecError::Assemble {
        message: format!("replacement snippet parse failed: {e}"),
    })?;
    let extender = file
        .module
        .items
        .iter()
        .find_map(|item| match item {
            crate::surface::ContentItem::Extender(e) => Some(e),
            _ => None,
        })
        .ok_or_else(|| SpecError::Assemble {
            message: "replacement snippet missing extender".into(),
        })?;
    let pres = crate::assemble::eval_extender_expr(
        &extender.body,
        &std::collections::HashMap::new(),
        module,
    )?;
    Ok(pres.terms)
}

fn apply_replacements(pres: &mut Presentation, rules: Vec<(String, GrammarRule)>) -> Result<()> {
    for (label, new_rule) in rules {
        if let Some(idx) = pres.terms.iter().position(|r| r.label == label) {
            pres.terms[idx] = new_rule;
            pres.term_label_conflicts.remove(&label);
        } else {
            return Err(SpecError::Assemble {
                message: format!("replacement target term '{label}' not found"),
            });
        }
    }
    Ok(())
}

fn merge_raw_source(pres: &mut Presentation, kind: SuffixKind, raw: &str) {
    let slot = match kind {
        SuffixKind::Types => &mut pres.sources.types,
        SuffixKind::Terms => &mut pres.sources.terms,
        SuffixKind::Literals => &mut pres.sources.literals,
        SuffixKind::Equations => &mut pres.sources.equations,
        SuffixKind::Rewrites => &mut pres.sources.rewrites,
        SuffixKind::Relations => &mut pres.sources.logic,
        SuffixKind::Exports | SuffixKind::Replacements => return,
    };
    match slot {
        Some(existing) => {
            existing.push('\n');
            existing.push_str(raw);
        },
        None => *slot = Some(raw.to_string()),
    }
}

fn merge_types(pres: &mut Presentation, delta: Vec<mettail_ast::language::LangType>) -> Result<()> {
    for t in delta {
        let name = t.name.to_string();
        if pres.types.iter().any(|x| x.name == name) {
            return Err(SpecError::Assemble {
                message: format!("duplicate type '{name}'"),
            });
        }
        pres.types.push(t);
    }
    Ok(())
}

fn merge_terms(
    pres: &mut Presentation,
    delta: Vec<mettail_ast::grammar::GrammarRule>,
) -> Result<()> {
    for r in delta {
        let label = r.label.to_string();
        if pres.terms.iter().any(|x| x.label == label) {
            return Err(SpecError::Assemble {
                message: format!("duplicate term label '{label}'"),
            });
        }
        pres.terms.push(r);
    }
    Ok(())
}

fn merge_literals(
    pres: &mut Presentation,
    block: mettail_ast::language::LiteralBlock,
) -> Result<()> {
    if pres.literals.is_some() {
        return Err(SpecError::Assemble {
            message: "literals block already present".into(),
        });
    }
    pres.literals = Some(block);
    Ok(())
}

fn merge_equations(
    pres: &mut Presentation,
    delta: Vec<mettail_ast::language::Equation>,
) -> Result<()> {
    for e in delta {
        let name = e.name.to_string();
        if pres.equations.iter().any(|x| x.name == name) {
            return Err(SpecError::Assemble {
                message: format!("duplicate equation '{name}'"),
            });
        }
        pres.equations.push(e);
    }
    Ok(())
}

fn merge_rewrites(
    pres: &mut Presentation,
    delta: Vec<mettail_ast::language::RewriteRule>,
) -> Result<()> {
    for r in delta {
        let name = r.name.to_string();
        if pres.rewrites.iter().any(|x| x.name == name) {
            return Err(SpecError::Assemble {
                message: format!("duplicate rewrite '{name}'"),
            });
        }
        pres.rewrites.push(r);
    }
    Ok(())
}

fn merge_logic(pres: &mut Presentation, block: mettail_ast::language::LogicBlock) -> Result<()> {
    if pres.logic.is_some() {
        return Err(SpecError::Assemble {
            message: "logic/relations block already present".into(),
        });
    }
    pres.logic = Some(block);
    Ok(())
}

pub fn merge_presentations(mut base: Presentation, overlay: Presentation) -> Result<Presentation> {
    merge_types(&mut base, overlay.types)?;
    if let Some(l) = overlay.literals {
        merge_literals(&mut base, l)?;
    }
    merge_terms(&mut base, overlay.terms)?;
    merge_equations(&mut base, overlay.equations)?;
    merge_rewrites(&mut base, overlay.rewrites)?;
    if let Some(logic) = overlay.logic {
        merge_logic(&mut base, logic)?;
    }
    if overlay.semantics != crate::ntir::SemanticsTarget::Unknown {
        base.semantics = overlay.semantics;
    }
    if overlay.context_template.is_some() {
        base.context_template = overlay.context_template;
    }
    base.rust_island_snippets
        .extend(overlay.rust_island_snippets);
    base.proc_artifacts.extend(overlay.proc_artifacts);
    merge_sources(&mut base.sources, &overlay.sources);
    Ok(base)
}

pub fn merge_presentations_right_biased(
    mut base: Presentation,
    overlay: Presentation,
) -> Result<Presentation> {
    merge_types_right_biased(&mut base, overlay.types);
    if let Some(literals) = overlay.literals {
        base.literals = Some(literals);
    }
    merge_terms_right_biased(&mut base, overlay.terms);
    merge_equations_right_biased(&mut base, overlay.equations);
    merge_rewrites_right_biased(&mut base, overlay.rewrites);
    if let Some(logic) = overlay.logic {
        base.logic = Some(logic);
    }
    if overlay.semantics != crate::ntir::SemanticsTarget::Unknown {
        base.semantics = overlay.semantics;
    }
    if overlay.context_template.is_some() {
        base.context_template = overlay.context_template;
    }
    base.rust_island_snippets
        .extend(overlay.rust_island_snippets);
    base.proc_artifacts.extend(overlay.proc_artifacts);
    merge_sources(&mut base.sources, &overlay.sources);
    base.term_label_conflicts
        .extend(overlay.term_label_conflicts);
    Ok(base)
}

pub fn merge_presentations_union(
    mut left: Presentation,
    right: Presentation,
) -> Result<Presentation> {
    ensure_no_type_overlap(&left, &right)?;
    ensure_no_named_overlap(
        left.equations.iter().map(|x| x.name.to_string()),
        right.equations.iter().map(|x| x.name.to_string()),
        "equation",
    )?;
    ensure_no_named_overlap(
        left.rewrites.iter().map(|x| x.name.to_string()),
        right.rewrites.iter().map(|x| x.name.to_string()),
        "rewrite",
    )?;
    if left.literals.is_some() && right.literals.is_some() {
        return Err(SpecError::Assemble {
            message: "union conflict: duplicate literals blocks; keep disjoint or remove one side"
                .into(),
        });
    }
    if left.logic.is_some() && right.logic.is_some() {
        return Err(SpecError::Assemble {
            message:
                "union conflict: duplicate logic/relations blocks; keep disjoint or remove one side"
                    .into(),
        });
    }

    merge_types_right_biased(&mut left, right.types);
    if let Some(literals) = right.literals {
        left.literals = Some(literals);
    }
    merge_terms_union(&mut left, right.terms);
    merge_equations_right_biased(&mut left, right.equations);
    merge_rewrites_right_biased(&mut left, right.rewrites);
    if let Some(logic) = right.logic {
        left.logic = Some(logic);
    }
    if right.semantics != crate::ntir::SemanticsTarget::Unknown {
        left.semantics = right.semantics;
    }
    if right.context_template.is_some() {
        left.context_template = right.context_template;
    }
    left.rust_island_snippets.extend(right.rust_island_snippets);
    left.proc_artifacts.extend(right.proc_artifacts);
    merge_sources(&mut left.sources, &right.sources);
    left.term_label_conflicts.extend(right.term_label_conflicts);
    Ok(left)
}

fn merge_types_right_biased(pres: &mut Presentation, delta: Vec<mettail_ast::language::LangType>) {
    for item in delta {
        let name = item.name.to_string();
        if let Some(idx) = pres.types.iter().position(|x| x.name == name) {
            pres.types[idx] = item;
        } else {
            pres.types.push(item);
        }
    }
}

fn merge_terms_right_biased(
    pres: &mut Presentation,
    delta: Vec<mettail_ast::grammar::GrammarRule>,
) {
    for item in delta {
        let label = item.label.to_string();
        if let Some(idx) = pres.terms.iter().position(|x| x.label == label) {
            pres.terms[idx] = item;
        } else {
            pres.terms.push(item);
        }
    }
}

fn merge_terms_union(pres: &mut Presentation, delta: Vec<mettail_ast::grammar::GrammarRule>) {
    for item in delta {
        let label = item.label.to_string();
        if let Some(idx) = pres.terms.iter().position(|x| x.label == label) {
            pres.terms[idx] = item;
            pres.term_label_conflicts.insert(label);
        } else {
            pres.terms.push(item);
        }
    }
}

fn merge_equations_right_biased(
    pres: &mut Presentation,
    delta: Vec<mettail_ast::language::Equation>,
) {
    for item in delta {
        let name = item.name.to_string();
        if let Some(idx) = pres.equations.iter().position(|x| x.name == name) {
            pres.equations[idx] = item;
        } else {
            pres.equations.push(item);
        }
    }
}

fn merge_rewrites_right_biased(
    pres: &mut Presentation,
    delta: Vec<mettail_ast::language::RewriteRule>,
) {
    for item in delta {
        let name = item.name.to_string();
        if let Some(idx) = pres.rewrites.iter().position(|x| x.name == name) {
            pres.rewrites[idx] = item;
        } else {
            pres.rewrites.push(item);
        }
    }
}

fn merge_sources(base: &mut crate::ntir::TheorySources, overlay: &crate::ntir::TheorySources) {
    merge_source_opt(&mut base.types, &overlay.types);
    merge_source_opt(&mut base.literals, &overlay.literals);
    merge_source_opt(&mut base.terms, &overlay.terms);
    merge_source_opt(&mut base.equations, &overlay.equations);
    merge_source_opt(&mut base.rewrites, &overlay.rewrites);
    merge_source_opt(&mut base.logic, &overlay.logic);
}

fn merge_source_opt(base: &mut Option<String>, overlay: &Option<String>) {
    if let Some(o) = overlay {
        match base {
            Some(b) => {
                b.push('\n');
                b.push_str(o);
            },
            None => *base = Some(o.clone()),
        }
    }
}

fn ensure_no_type_overlap(left: &Presentation, right: &Presentation) -> Result<()> {
    ensure_no_named_overlap(
        left.types.iter().map(|x| x.name.to_string()),
        right.types.iter().map(|x| x.name.to_string()),
        "type",
    )
}

fn ensure_no_named_overlap<I, J>(left: I, right: J, kind: &str) -> Result<()>
where
    I: Iterator<Item = String>,
    J: Iterator<Item = String>,
{
    let right_names: std::collections::BTreeSet<String> = right.collect();
    let overlaps: Vec<String> = left.filter(|name| right_names.contains(name)).collect();
    if overlaps.is_empty() {
        return Ok(());
    }
    Err(SpecError::Assemble {
        message: format!("union conflict: duplicate {kind}(s): {}", overlaps.join(", ")),
    })
}

#[cfg(test)]
mod tests {
    use super::merge_presentations_union;
    use crate::ntir::Presentation;
    use mettail_ast::language::LogicBlock;
    use proc_macro2::TokenStream;

    #[test]
    fn union_conflict_on_duplicate_logic_fails() {
        let left = Presentation {
            logic: Some(LogicBlock {
                relations: Vec::new(),
                content: TokenStream::new(),
            }),
            ..Presentation::default()
        };
        let right = Presentation {
            logic: Some(LogicBlock {
                relations: Vec::new(),
                content: TokenStream::new(),
            }),
            ..Presentation::default()
        };

        let err = match merge_presentations_union(left, right) {
            Ok(_) => panic!("expected logic conflict"),
            Err(err) => err,
        };
        assert!(err.to_string().contains("logic/relations"), "unexpected error: {err}");
    }
}
