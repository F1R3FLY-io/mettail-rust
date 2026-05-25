use mettail_ast::fragments::{
    parse_equations_fragment, parse_literals_fragment, parse_relations_fragment,
    parse_rewrites_fragment, parse_terms_fragment, parse_types_fragment,
};
use proc_macro2::TokenStream;

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
    merge_sources(&mut base.sources, &overlay.sources);
    Ok(base)
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
