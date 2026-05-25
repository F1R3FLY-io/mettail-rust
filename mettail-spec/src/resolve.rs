use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use indexmap::IndexMap;

use crate::error::{Result, SpecError};
use crate::parser;
use crate::surface::SurfaceFile;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModuleId(pub PathBuf);

#[derive(Debug, Clone)]
pub struct ModuleVertex {
    pub id: ModuleId,
    pub file: SurfaceFile,
}

#[derive(Debug, Clone)]
pub struct ResolvedGraph {
    pub entry: ModuleId,
    pub vertices: IndexMap<ModuleId, ModuleVertex>,
    pub order: Vec<ModuleId>,
}

pub fn resolve_graph(entry_path: PathBuf) -> Result<ResolvedGraph> {
    let entry_canon = canonicalize(&entry_path)?;
    let entry_id = ModuleId(entry_canon.clone());

    let mut vertices: IndexMap<ModuleId, ModuleVertex> = IndexMap::new();
    let mut edges: Vec<(ModuleId, ModuleId)> = Vec::new();
    let mut stack: Vec<PathBuf> = vec![entry_canon.clone()];

    while let Some(path) = stack.pop() {
        let id = ModuleId(path.clone());
        if vertices.contains_key(&id) {
            continue;
        }
        let source = fs::read_to_string(&path)
            .map_err(|e| SpecError::Io { path: path.clone(), source: e })?;
        let file = parser::parse_file(path.clone(), &source)?;
        let base_dir = path.parent().unwrap_or(Path::new("."));

        for imp in &file.imports {
            let resolved = resolve_import_path(base_dir, &imp.path)?;
            let dep_id = ModuleId(resolved.clone());
            // importee must be evaluated before importer
            edges.push((dep_id.clone(), id.clone()));
            if !vertices.contains_key(&dep_id) {
                stack.push(resolved);
            }
        }

        vertices.insert(id.clone(), ModuleVertex { id: id.clone(), file });
    }

    detect_cycle(&entry_id, &edges)?;

    let order = topo_sort(&vertices.keys().cloned().collect::<Vec<_>>(), &edges)?;

    Ok(ResolvedGraph { entry: entry_id, vertices, order })
}

fn canonicalize(path: &Path) -> Result<PathBuf> {
    fs::canonicalize(path).map_err(|e| SpecError::Io { path: path.to_path_buf(), source: e })
}

fn resolve_import_path(base_dir: &Path, quoted: &str) -> Result<PathBuf> {
    let p = base_dir.join(quoted);
    if p.exists() {
        return canonicalize(&p);
    }
    Err(SpecError::ImportNotFound { path: p, from: base_dir.to_path_buf() })
}

fn detect_cycle(entry: &ModuleId, edges: &[(ModuleId, ModuleId)]) -> Result<()> {
    let mut adj: HashMap<ModuleId, Vec<ModuleId>> = HashMap::new();
    for (a, b) in edges {
        adj.entry(a.clone()).or_default().push(b.clone());
    }

    let mut visiting: HashSet<ModuleId> = HashSet::new();
    let mut visited: HashSet<ModuleId> = HashSet::new();
    let mut path: Vec<ModuleId> = Vec::new();

    fn dfs(
        node: &ModuleId,
        adj: &HashMap<ModuleId, Vec<ModuleId>>,
        visiting: &mut HashSet<ModuleId>,
        visited: &mut HashSet<ModuleId>,
        path: &mut Vec<ModuleId>,
    ) -> Option<Vec<ModuleId>> {
        if visiting.contains(node) {
            let pos = path.iter().position(|x| x == node).unwrap_or(0);
            let mut cycle = path[pos..].to_vec();
            cycle.push(node.clone());
            return Some(cycle);
        }
        if visited.contains(node) {
            return None;
        }
        visiting.insert(node.clone());
        path.push(node.clone());
        if let Some(neighbors) = adj.get(node) {
            for n in neighbors {
                if let Some(c) = dfs(n, adj, visiting, visited, path) {
                    return Some(c);
                }
            }
        }
        path.pop();
        visiting.remove(node);
        visited.insert(node.clone());
        None
    }

    if let Some(cycle) = dfs(entry, &adj, &mut visiting, &mut visited, &mut path) {
        let trace: Vec<String> = cycle.iter().map(|m| m.0.display().to_string()).collect();
        return Err(SpecError::ImportCycle { trace });
    }
    Ok(())
}

fn topo_sort(nodes: &[ModuleId], edges: &[(ModuleId, ModuleId)]) -> Result<Vec<ModuleId>> {
    let mut indegree: HashMap<ModuleId, usize> = HashMap::new();
    let mut adj: HashMap<ModuleId, Vec<ModuleId>> = HashMap::new();
    for n in nodes {
        indegree.entry(n.clone()).or_insert(0);
    }
    for (a, b) in edges {
        adj.entry(a.clone()).or_default().push(b.clone());
        *indegree.entry(b.clone()).or_insert(0) += 1;
    }

    let mut queue: Vec<ModuleId> = indegree
        .iter()
        .filter(|(_, &d)| d == 0)
        .map(|(k, _)| k.clone())
        .collect();
    queue.sort_by_key(|m| m.0.display().to_string());

    let mut order = Vec::new();
    while let Some(n) = queue.first().cloned() {
        queue.remove(0);
        order.push(n.clone());
        if let Some(neigh) = adj.get(&n) {
            for m in neigh {
                let d = indegree.get_mut(m).unwrap();
                *d -= 1;
                if *d == 0 {
                    queue.push(m.clone());
                    queue.sort_by_key(|m| m.0.display().to_string());
                }
            }
        }
    }

    if order.len() != nodes.len() {
        return Err(SpecError::Other("topological sort failed (cycle)".into()));
    }
    Ok(order)
}
