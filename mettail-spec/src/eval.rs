use std::collections::HashMap;

use crate::error::{Result, SpecError};
use crate::resolve::{ModuleId, ResolvedGraph};
use crate::surface::{ContentItem, ExtenderDecl, LanguageDecl, LanguageExpr, Module, SpaceDecl, ProcContent};

#[derive(Debug, Clone)]
pub struct ExtenderBinding {
    pub decl: ExtenderDecl,
    pub module: ModuleId,
}

#[derive(Debug, Clone)]
pub struct LanguageBinding {
    pub decl: LanguageDecl,
    pub module: ModuleId,
}

#[derive(Debug, Clone, Default)]
pub struct ModuleEnv {
    pub extenders: HashMap<String, ExtenderBinding>,
    pub languages: HashMap<String, LanguageBinding>,
    pub spaces: HashMap<String, SpaceDecl>,
    pub procs: Vec<ProcContent>,
}

#[derive(Debug, Clone)]
pub struct EvaluatedGraph {
    pub envs: HashMap<ModuleId, ModuleEnv>,
}

pub fn evaluate_graph(graph: &ResolvedGraph) -> Result<EvaluatedGraph> {
    let mut envs = HashMap::new();
    for mid in &graph.order {
        let vertex = graph.vertices.get(mid).expect("vertex");
        let env = eval_module(&vertex.file.module, mid)?;
        envs.insert(mid.clone(), env);
    }
    Ok(EvaluatedGraph { envs })
}

fn eval_module(module: &Module, module_id: &ModuleId) -> Result<ModuleEnv> {
    let mut env = ModuleEnv::default();
    for item in &module.items {
        match item {
            ContentItem::Extender(decl) => {
                if decl.exported {
                    env.extenders.insert(
                        decl.name.clone(),
                        ExtenderBinding {
                            decl: decl.clone(),
                            module: module_id.clone(),
                        },
                    );
                }
            },
            ContentItem::Language(decl) => {
                if decl.exported {
                    env.languages.insert(
                        decl.name.clone(),
                        LanguageBinding {
                            decl: decl.clone(),
                            module: ModuleId(std::path::PathBuf::new()),
                        },
                    );
                }
            },
            ContentItem::Space(decl) => {
                if decl.exported {
                    env.spaces.insert(decl.name.clone(), decl.clone());
                }
            },
            ContentItem::Nested(nested) => {
                let nested_env = eval_module(nested, module_id)?;
                for (k, v) in nested_env.extenders {
                    env.extenders.entry(k).or_insert(v);
                }
                for (k, v) in nested_env.languages {
                    env.languages.entry(k).or_insert(v);
                }
                env.procs.extend(nested_env.procs);
            },
            ContentItem::Proc(p) => {
                // Rholang evaluation stub to unblock module spine + runtime hooks stories
                println!("STUB: Evaluating {} process: {}", p.lang, p.raw);
                env.procs.push(p.clone());
            },
        }
    }
    Ok(env)
}

/// Resolve a path like `M.Complex` against import aliases in the entry module file.
pub fn resolve_language_path(
    entry_imports: &[crate::surface::Import],
    graph: &ResolvedGraph,
    entry_id: &ModuleId,
    expr: &LanguageExpr,
) -> Result<(ModuleId, ExtenderDecl, Vec<LanguageExpr>)> {
    let (alias, rest) = expr
        .segments
        .split_first()
        .ok_or_else(|| SpecError::Assemble { message: "empty language path".into() })?;

    let import = entry_imports
        .iter()
        .find(|i| {
            i.alias.as_deref() == Some(alias) || (i.alias.is_none() && i.path.contains(alias))
        })
        .ok_or_else(|| SpecError::Assemble {
            message: format!("unknown import alias '{alias}'"),
        })?;

    let target_path = graph
        .vertices
        .get(entry_id)
        .map(|v| v.id.0.parent().unwrap_or(std::path::Path::new(".")))
        .unwrap_or(std::path::Path::new("."))
        .join(&import.path);
    let target_id =
        ModuleId(std::fs::canonicalize(&target_path).map_err(|_| SpecError::Assemble {
            message: format!("cannot resolve import path for alias '{alias}'"),
        })?);

    let ext_name = rest.first().ok_or_else(|| SpecError::Assemble {
        message: format!("path must include extender name after '{alias}'"),
    })?;

    let vertex = graph
        .vertices
        .get(&target_id)
        .ok_or_else(|| SpecError::Assemble {
            message: format!("module not loaded for alias '{alias}'"),
        })?;

    let binding = vertex
        .file
        .module
        .items
        .iter()
        .find_map(|item| match item {
            ContentItem::Extender(e) if e.exported && e.name == *ext_name => Some(e.clone()),
            _ => None,
        })
        .ok_or_else(|| SpecError::Assemble {
            message: format!("exported extender '{ext_name}' not found in module"),
        })?;

    let args = expr.args.clone().unwrap_or_default();
    Ok((target_id, binding, args))
}
