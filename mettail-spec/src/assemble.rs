use std::collections::HashMap;

use crate::error::{Result, SpecError};
use crate::eval::{evaluate_graph, resolve_language_path, EvaluatedGraph};
use crate::fragments::{apply_suffix, merge_presentations};
use crate::island::{process_island, IslandArtifact};
use crate::ntir::ProcArtifact;
use crate::ntir::{Ntir, Presentation, SemanticsTarget};
use crate::resolve::ResolvedGraph;
use crate::semantics::lower_context_stub;
use crate::surface::IslandToken;
use crate::surface::{ContentItem, ExtenderExpr, LanguageExpr};

pub fn compile_language(
    graph: &ResolvedGraph,
    evaluated: &EvaluatedGraph,
    language_name: &str,
) -> Result<Ntir> {
    let entry = graph
        .vertices
        .get(&graph.entry)
        .ok_or_else(|| SpecError::Assemble { message: "missing entry module".into() })?;

    let lang_decl = entry
        .file
        .module
        .items
        .iter()
        .find_map(|item| match item {
            ContentItem::Language(l) if l.exported && l.name == language_name => Some(l.clone()),
            _ => None,
        })
        .ok_or_else(|| SpecError::Assemble {
            message: format!("exported language '{language_name}' not found in entry module"),
        })?;

    let pres = assemble_language_expr(graph, evaluated, &entry.file.imports, &lang_decl.expr)?;
    let lowered_context = pres.context_template.as_ref().map(lower_context_stub);
    Ok(pres.into_ntir(language_name.to_string(), lowered_context))
}

pub fn assemble_language_expr(
    graph: &ResolvedGraph,
    evaluated: &EvaluatedGraph,
    entry_imports: &[crate::surface::Import],
    expr: &LanguageExpr,
) -> Result<Presentation> {
    if expr.segments.len() == 1 {
        let name = &expr.segments[0];
        let entry_env = evaluated
            .envs
            .get(&graph.entry)
            .ok_or_else(|| SpecError::Assemble { message: "missing entry env".into() })?;
        if let Some(binding) = entry_env.extenders.get(name) {
            let arg_pres: Vec<Presentation> = expr
                .args
                .as_ref()
                .map(|args| {
                    args.iter()
                        .map(|a| assemble_language_expr(graph, evaluated, entry_imports, a))
                        .collect::<Result<_>>()
                })
                .transpose()?
                .unwrap_or_default();
            return apply_extender(
                &binding.decl,
                &arg_pres,
                &binding.decl.body,
                &graph.entry.0.display().to_string(),
            );
        }
    }

    if let Some(args) = &expr.args {
        let (module_id, decl, _) = resolve_language_path(entry_imports, graph, &graph.entry, expr)?;
        let arg_pres: Vec<Presentation> = args
            .iter()
            .map(|a| assemble_language_expr(graph, evaluated, entry_imports, a))
            .collect::<Result<_>>()?;
        apply_extender(&decl, &arg_pres, &decl.body, &module_id.0.display().to_string())
    } else if expr.segments.len() == 1 {
        // local extender reference in entry module
        let name = &expr.segments[0];
        let entry_env = evaluated
            .envs
            .get(&graph.entry)
            .ok_or_else(|| SpecError::Assemble { message: "missing entry env".into() })?;
        if let Some(binding) = entry_env.extenders.get(name) {
            return apply_extender(
                &binding.decl,
                &[],
                &binding.decl.body,
                &graph.entry.0.display().to_string(),
            );
        }
        Err(SpecError::Assemble {
            message: format!("unresolved extender or language '{name}'"),
        })
    } else {
        let (module_id, decl, call_args) =
            resolve_language_path(entry_imports, graph, &graph.entry, expr)?;
        let arg_pres: Vec<Presentation> = call_args
            .iter()
            .map(|a| assemble_language_expr(graph, evaluated, entry_imports, a))
            .collect::<Result<_>>()?;
        apply_extender(&decl, &arg_pres, &decl.body, &module_id.0.display().to_string())
    }
}

fn apply_extender(
    decl: &crate::surface::ExtenderDecl,
    args: &[Presentation],
    body: &ExtenderExpr,
    module_label: &str,
) -> Result<Presentation> {
    let mut param_map: HashMap<String, Presentation> = HashMap::new();
    for (param, arg) in decl.params.iter().zip(args.iter()) {
        param_map.insert(param.clone(), arg.clone());
    }
    eval_extender_expr(body, &param_map, module_label)
}

pub(crate) fn eval_extender_expr(
    expr: &ExtenderExpr,
    params: &HashMap<String, Presentation>,
    module: &str,
) -> Result<Presentation> {
    match expr {
        ExtenderExpr::Empty => Ok(Presentation::empty()),
        ExtenderExpr::Union(_, _) => Err(SpecError::Assemble {
            message: "extender union (/\\) is not implemented in Phase 1".into(),
        }),
        ExtenderExpr::Group(inner) => eval_extender_expr(inner, params, module),
        ExtenderExpr::Suffix { inner, kind, tokens, raw, .. } => {
            let mut pres = eval_extender_expr(inner, params, module)?;
            apply_suffix(&mut pres, *kind, tokens.clone(), raw, module)?;
            Ok(pres)
        },
        ExtenderExpr::Semantics { inner, target } => {
            let mut pres = eval_extender_expr(inner, params, module)?;
            pres.semantics = semantics_from_expr(target)?;
            Ok(pres)
        },
        ExtenderExpr::Context { inner, template } => {
            let mut pres = eval_extender_expr(inner, params, module)?;
            pres.context_template = Some(template.clone());
            Ok(pres)
        },
        ExtenderExpr::Call { name, args } => {
            if let Some(base) = params.get(name) {
                if args.is_empty() {
                    return Ok(base.clone());
                }
                let mut pres = base.clone();
                for arg_expr in args {
                    let nested = eval_extender_expr(arg_expr, params, module)?;
                    pres = merge_presentations(pres, nested)?;
                }
                return Ok(pres);
            }
            if args.is_empty() {
                return Err(SpecError::Assemble {
                    message: format!("unknown extender reference '{name}'"),
                });
            }
            let mut pres = Presentation::empty();
            for a in args {
                let nested = eval_extender_expr(a, params, module)?;
                pres = merge_presentations(pres, nested)?;
            }
            Ok(pres)
        },
        ExtenderExpr::Island(token) => presentation_from_island(token),
    }
}

fn presentation_from_island(token: &IslandToken) -> Result<Presentation> {
    let artifact = process_island(token)?;
    let mut pres = Presentation::empty();
    match artifact {
        IslandArtifact::RustContext { snippet } => {
            pres.rust_island_snippets.push(snippet);
        },
        IslandArtifact::RholangProc { gst } => {
            pres.proc_artifacts
                .push(ProcArtifact { lang: token.lang.clone(), gst });
        },
    }
    Ok(pres)
}

fn semantics_from_expr(expr: &LanguageExpr) -> Result<SemanticsTarget> {
    match expr.segments.as_slice() {
        [s] if s == "Rust" => Ok(SemanticsTarget::Rust),
        _ => Err(SpecError::Assemble {
            message: format!("unknown semantics target '{}'", expr.segments.join(".")),
        }),
    }
}

pub fn compile_entry(entry_path: std::path::PathBuf, language_name: Option<&str>) -> Result<Ntir> {
    let graph = crate::resolve::resolve_graph(entry_path)?;
    let evaluated = evaluate_graph(&graph)?;
    let entry = graph.vertices.get(&graph.entry).unwrap();
    let name = language_name.map(|s| s.to_string()).unwrap_or_else(|| {
        entry
            .file
            .module
            .items
            .iter()
            .find_map(|i| match i {
                ContentItem::Language(l) if l.exported => Some(l.name.clone()),
                _ => None,
            })
            .expect("entry must export a language when --language omitted")
    });
    compile_language(&graph, &evaluated, &name)
}

pub fn validate_ntir(ntir: &Ntir) -> Result<()> {
    let def = ntir.to_language_def();
    mettail_ast::validation::validate_language(&def).map_err(|e| SpecError::Validation(e.message()))
}
