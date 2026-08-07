//! Source-derived census of recursive data-type lifecycle implementations.
//!
//! Recursive call sites and recursive data ownership are separate hazards.  The
//! hand-written recursion census covers the former; this gate covers compiler-
//! generated trait walkers and implicit recursive destruction for the latter.
//! The inventory is derived from production Rust sources so adding a recursive
//! field or derive cannot silently escape a hand-maintained list.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use quote::ToTokens;
use syn::visit_mut::{self, VisitMut};
use syn::{Attribute, Fields, GenericArgument, Generics, ItemImpl, PathArguments, Type, UseTree};

const CRATE_ROOTS: &[&str] = &[
    "ast/src",
    "macros/src",
    "runtime/src",
    "rholang-runtime/src",
    "rholang-codegen/src",
    "dovetail/src",
    "dovetail-runtime/src",
    "prattail/src",
    "rigail/src",
    "query/src",
    "repl/src",
    "simulation/src",
    "testkit/src",
    "rholang-adapter/src",
];

const CLONE: u16 = 1 << 0;
const DEBUG: u16 = 1 << 1;
const PARTIAL_EQ: u16 = 1 << 2;
const PARTIAL_ORD: u16 = 1 << 3;
const ORD: u16 = 1 << 4;
const HASH: u16 = 1 << 5;
const SERIALIZE: u16 = 1 << 6;
const DESERIALIZE: u16 = 1 << 7;
const MESSAGE: u16 = 1 << 8;
const ENCODE: u16 = 1 << 9;
const DECODE: u16 = 1 << 10;
const DROP: u16 = 1 << 11;
const DISPLAY: u16 = 1 << 12;
const ALL_OPERATIONS: u16 = (1 << 13) - 1;

const DERIVE_OPERATIONS: &[(&str, u16)] = &[
    ("Clone", CLONE),
    ("Debug", DEBUG),
    ("PartialEq", PARTIAL_EQ),
    ("PartialOrd", PARTIAL_ORD),
    ("Ord", ORD),
    ("Hash", HASH),
    ("Serialize", SERIALIZE),
    ("Deserialize", DESERIALIZE),
    ("Message", MESSAGE),
    ("Encode", ENCODE),
    ("Decode", DECODE),
    ("BorrowDecode", DECODE),
];

/// Private representation nodes whose recursive destruction is explicitly
/// drained by an enclosing public owner.  Every row is checked against a real
/// `Drop` implementation on the named owner; it is not a general exemption.
const ENCLOSING_DROP_OWNERS: &[(&str, &str, &str)] = &[
    ("dovetail/src/key.rs", "ContentKeyKind", "ContentKey"),
    ("dovetail/src/key.rs", "ContentKeyInner", "ContentKey"),
    ("rholang-runtime/src/speculation.rs", "TraceLink", "ReductionTrace"),
];

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct TypeReference {
    path: Vec<String>,
    /// Operations whose standard implementation follows this edge.
    operations: u16,
}

#[derive(Clone, Debug)]
struct Definition {
    file: String,
    crate_key: String,
    module: Vec<String>,
    name: String,
    references: Vec<TypeReference>,
    derives: BTreeSet<String>,
    type_parameters: BTreeSet<String>,
}

#[derive(Clone, Debug)]
struct ImplRecord {
    file: String,
    crate_key: String,
    module: Vec<String>,
    self_path: Vec<String>,
    trait_name: String,
}

#[derive(Clone, Debug)]
struct ImportRecord {
    crate_key: String,
    module: Vec<String>,
    alias: String,
    path: Vec<String>,
}

struct TypeCollector {
    file: String,
    crate_key: String,
    base_module: Vec<String>,
    inline_modules: Vec<String>,
    definitions: Vec<Definition>,
    implementations: Vec<ImplRecord>,
    imports: Vec<ImportRecord>,
    test_depth: usize,
}

impl TypeCollector {
    fn new(file: String, crate_key: String, base_module: Vec<String>) -> Self {
        Self {
            file,
            crate_key,
            base_module,
            inline_modules: Vec::new(),
            definitions: Vec::new(),
            implementations: Vec::new(),
            imports: Vec::new(),
            test_depth: 0,
        }
    }

    fn module(&self) -> Vec<String> {
        self.base_module
            .iter()
            .chain(&self.inline_modules)
            .cloned()
            .collect()
    }
}

fn is_test_only(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attribute| {
        if attribute.path().is_ident("test") {
            return true;
        }
        attribute.path().is_ident("cfg")
            && attribute
                .meta
                .to_token_stream()
                .to_string()
                .replace(' ', "")
                .contains("test")
    })
}

fn derives(attrs: &[Attribute]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for attribute in attrs {
        if !attribute.path().is_ident("derive") {
            continue;
        }
        attribute
            .parse_nested_meta(|meta| {
                if let Some(ident) = meta.path.get_ident() {
                    out.insert(ident.to_string());
                } else if let Some(segment) = meta.path.segments.last() {
                    out.insert(segment.ident.to_string());
                }
                Ok(())
            })
            .expect("a parsed Rust source file has a valid derive attribute");
    }
    out
}

fn type_references(ty: &Type, operations: u16, out: &mut Vec<TypeReference>) {
    let mut pending = vec![(ty, operations)];
    while let Some((ty, operations)) = pending.pop() {
        if operations == 0 {
            continue;
        }
        match ty {
            Type::Array(array) => pending.push((&array.elem, operations)),
            Type::Group(group) => pending.push((&group.elem, operations)),
            Type::Paren(paren) => pending.push((&paren.elem, operations)),
            Type::Slice(slice) => pending.push((&slice.elem, operations)),
            Type::Tuple(tuple) => {
                pending.extend(tuple.elems.iter().map(|elem| (elem, operations)));
            },
            Type::Path(path) => {
                let Some(segment) = path.path.segments.last() else {
                    continue;
                };
                let name = segment.ident.to_string();
                if matches!(name.as_str(), "PhantomData" | "Weak") {
                    continue;
                }
                out.push(TypeReference {
                    path: path
                        .path
                        .segments
                        .iter()
                        .map(|part| part.ident.to_string())
                        .collect(),
                    operations,
                });

                let child_operations = match name.as_str() {
                    // Cloning a shared pointer increments its count; it does not
                    // clone the recursively owned payload. Its other structural
                    // traits and last-owner destruction do follow the edge.
                    "Arc" | "Rc" => operations & !CLONE,
                    // ManuallyDrop suppresses only implicit destruction.
                    "ManuallyDrop" => operations & !DROP,
                    _ => operations,
                };
                if let PathArguments::AngleBracketed(arguments) = &segment.arguments {
                    for argument in &arguments.args {
                        match argument {
                            GenericArgument::Type(inner) => {
                                pending.push((inner, child_operations));
                            },
                            GenericArgument::AssocType(binding) => {
                                pending.push((&binding.ty, child_operations));
                            },
                            GenericArgument::Constraint(_)
                            | GenericArgument::Lifetime(_)
                            | GenericArgument::Const(_)
                            | GenericArgument::AssocConst(_)
                            | _ => {},
                        }
                    }
                }
                if let Some(qself) = &path.qself {
                    pending.push((&qself.ty, operations));
                }
            },
            Type::Reference(reference) => {
                // References neither clone nor destroy the referent. Formatting,
                // comparison, hashing, and serialization do inspect it.
                pending.push((&reference.elem, operations & !(CLONE | DROP | DESERIALIZE)));
            },
            Type::Ptr(_) | Type::BareFn(_) => {},
            _ => {},
        }
    }
}

fn field_references(fields: &Fields) -> Vec<TypeReference> {
    let mut out = Vec::new();
    for field in fields {
        type_references(&field.ty, ALL_OPERATIONS, &mut out);
    }
    out
}

fn type_path(ty: &Type) -> Option<Vec<String>> {
    match ty {
        Type::Path(path) if path.qself.is_none() => Some(
            path.path
                .segments
                .iter()
                .map(|segment| segment.ident.to_string())
                .collect(),
        ),
        Type::Group(group) => type_path(&group.elem),
        Type::Paren(paren) => type_path(&paren.elem),
        _ => None,
    }
}

impl TypeCollector {
    fn add_definition(
        &mut self,
        name: String,
        attrs: &[Attribute],
        generics: &Generics,
        fields: &[&Fields],
    ) {
        if self.test_depth != 0 || is_test_only(attrs) {
            return;
        }
        let mut references = Vec::new();
        for field_set in fields {
            references.extend(field_references(field_set));
        }
        self.definitions.push(Definition {
            file: self.file.clone(),
            crate_key: self.crate_key.clone(),
            module: self.module(),
            name,
            references,
            derives: derives(attrs),
            type_parameters: generics
                .type_params()
                .map(|parameter| parameter.ident.to_string())
                .collect(),
        });
    }
}

fn flatten_use_tree(
    tree: &UseTree,
    prefix: &mut Vec<String>,
    out: &mut Vec<(String, Vec<String>)>,
) {
    match tree {
        UseTree::Path(path) => {
            prefix.push(path.ident.to_string());
            flatten_use_tree(&path.tree, prefix, out);
            prefix.pop();
        },
        UseTree::Name(name) => {
            let name = name.ident.to_string();
            let mut path = prefix.clone();
            path.push(name.clone());
            out.push((name, path));
        },
        UseTree::Rename(rename) => {
            let mut path = prefix.clone();
            path.push(rename.ident.to_string());
            out.push((rename.rename.to_string(), path));
        },
        UseTree::Group(group) => {
            for item in &group.items {
                flatten_use_tree(item, prefix, out);
            }
        },
        UseTree::Glob(_) => {},
    }
}

impl VisitMut for TypeCollector {
    fn visit_item_mod_mut(&mut self, node: &mut syn::ItemMod) {
        let test = is_test_only(&node.attrs);
        self.test_depth += usize::from(test);
        let inline = node.content.is_some();
        if inline {
            self.inline_modules.push(node.ident.to_string());
        }
        visit_mut::visit_item_mod_mut(self, node);
        if inline {
            self.inline_modules.pop();
        }
        self.test_depth -= usize::from(test);
    }

    fn visit_item_struct_mut(&mut self, node: &mut syn::ItemStruct) {
        self.add_definition(node.ident.to_string(), &node.attrs, &node.generics, &[&node.fields]);
        visit_mut::visit_item_struct_mut(self, node);
    }

    fn visit_item_enum_mut(&mut self, node: &mut syn::ItemEnum) {
        let fields = node
            .variants
            .iter()
            .map(|variant| &variant.fields)
            .collect::<Vec<_>>();
        self.add_definition(node.ident.to_string(), &node.attrs, &node.generics, &fields);
        visit_mut::visit_item_enum_mut(self, node);
    }

    fn visit_item_type_mut(&mut self, node: &mut syn::ItemType) {
        if self.test_depth == 0 && !is_test_only(&node.attrs) {
            let mut references = Vec::new();
            type_references(&node.ty, ALL_OPERATIONS, &mut references);
            self.definitions.push(Definition {
                file: self.file.clone(),
                crate_key: self.crate_key.clone(),
                module: self.module(),
                name: node.ident.to_string(),
                references,
                derives: BTreeSet::new(),
                type_parameters: node
                    .generics
                    .type_params()
                    .map(|parameter| parameter.ident.to_string())
                    .collect(),
            });
        }
        visit_mut::visit_item_type_mut(self, node);
    }

    fn visit_item_use_mut(&mut self, node: &mut syn::ItemUse) {
        if self.test_depth == 0 && !is_test_only(&node.attrs) {
            let mut flattened = Vec::new();
            flatten_use_tree(&node.tree, &mut Vec::new(), &mut flattened);
            let module = self.module();
            self.imports
                .extend(flattened.into_iter().map(|(alias, path)| ImportRecord {
                    crate_key: self.crate_key.clone(),
                    module: module.clone(),
                    alias,
                    path,
                }));
        }
        visit_mut::visit_item_use_mut(self, node);
    }

    fn visit_item_impl_mut(&mut self, node: &mut ItemImpl) {
        if self.test_depth == 0 && !is_test_only(&node.attrs) {
            if let (Some((polarity, trait_path, _)), Some(self_path)) =
                (&node.trait_, type_path(&node.self_ty))
            {
                if polarity.is_none() {
                    if let Some(trait_name) = trait_path.segments.last() {
                        self.implementations.push(ImplRecord {
                            file: self.file.clone(),
                            crate_key: self.crate_key.clone(),
                            module: self.module(),
                            self_path,
                            trait_name: trait_name.ident.to_string(),
                        });
                    }
                }
            }
        }
        visit_mut::visit_item_impl_mut(self, node);
    }
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("ast is a workspace member")
        .to_path_buf()
}

#[derive(Clone, Debug)]
struct CrateInfo {
    key: String,
    source_root: PathBuf,
    aliases: BTreeSet<String>,
}

fn manifest_library_name(manifest: &Path) -> Option<String> {
    let source = std::fs::read_to_string(manifest).ok()?;
    let mut in_lib = false;
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            in_lib = trimmed == "[lib]";
            continue;
        }
        if !in_lib {
            continue;
        }
        let Some(value) = trimmed.strip_prefix("name") else {
            continue;
        };
        let Some(value) = value.trim_start().strip_prefix('=') else {
            continue;
        };
        return Some(value.trim().trim_matches('"').to_string());
    }
    None
}

fn crate_infos(root: &Path) -> Vec<CrateInfo> {
    CRATE_ROOTS
        .iter()
        .map(|source_root| {
            let source_root = root.join(source_root);
            let crate_dir = source_root
                .parent()
                .expect("a crate source root has a parent directory");
            let key = crate_dir
                .file_name()
                .expect("a crate directory has a name")
                .to_string_lossy()
                .replace('-', "_");
            let mut aliases = BTreeSet::from([key.clone()]);
            if let Some(library_name) = manifest_library_name(&crate_dir.join("Cargo.toml")) {
                aliases.insert(library_name);
            }
            CrateInfo { key, source_root, aliases }
        })
        .collect()
}

fn source_files(crates: &[CrateInfo]) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let mut pending = crates
        .iter()
        .map(|crate_info| crate_info.source_root.clone())
        .collect::<Vec<_>>();
    while let Some(dir) = pending.pop() {
        let Ok(entries) = std::fs::read_dir(dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if path.is_dir() {
                if matches!(name.as_ref(), "target" | ".git" | ".claude" | "node_modules") {
                    continue;
                }
                pending.push(path);
            } else if name.ends_with(".rs") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

fn file_module(source_root: &Path, file: &Path) -> Vec<String> {
    let relative = file
        .strip_prefix(source_root)
        .expect("a scanned source belongs to its crate source root");
    let mut components = relative
        .components()
        .map(|component| component.as_os_str().to_string_lossy().to_string())
        .collect::<Vec<_>>();
    let file_name = components
        .pop()
        .expect("a Rust source path has a file name");
    let stem = file_name.strip_suffix(".rs").unwrap_or(&file_name);
    if !matches!(stem, "lib" | "main" | "mod") {
        components.push(stem.to_string());
    }
    components
}

fn strongly_connected(graph: &[BTreeSet<usize>]) -> Vec<Vec<usize>> {
    struct DfsFrame<'graph> {
        node: usize,
        parent: Option<usize>,
        successors: std::collections::btree_set::Iter<'graph, usize>,
    }

    let len = graph.len();
    let mut next_index = 0;
    let mut indexes = vec![None; len];
    let mut lowlinks = vec![0; len];
    let mut tarjan_stack = Vec::new();
    let mut on_stack = vec![false; len];
    let mut components = Vec::new();

    for root in 0..len {
        if indexes[root].is_some() {
            continue;
        }
        indexes[root] = Some(next_index);
        lowlinks[root] = next_index;
        next_index += 1;
        tarjan_stack.push(root);
        on_stack[root] = true;

        let mut dfs = vec![DfsFrame {
            node: root,
            parent: None,
            successors: graph[root].iter(),
        }];
        while !dfs.is_empty() {
            let edge = {
                let frame = dfs.last_mut().expect("non-empty DFS stack");
                frame
                    .successors
                    .next()
                    .copied()
                    .map(|next| (frame.node, next))
            };
            if let Some((node, next)) = edge {
                if indexes[next].is_none() {
                    indexes[next] = Some(next_index);
                    lowlinks[next] = next_index;
                    next_index += 1;
                    tarjan_stack.push(next);
                    on_stack[next] = true;
                    dfs.push(DfsFrame {
                        node: next,
                        parent: Some(node),
                        successors: graph[next].iter(),
                    });
                } else if on_stack[next] {
                    lowlinks[node] =
                        lowlinks[node].min(indexes[next].expect("an on-stack node has an index"));
                }
                continue;
            }

            let frame = dfs.pop().expect("non-empty DFS stack");
            let node = frame.node;
            if let Some(parent) = frame.parent {
                lowlinks[parent] = lowlinks[parent].min(lowlinks[node]);
            }
            if lowlinks[node] == indexes[node].expect("a discovered node has an index") {
                let mut component = Vec::new();
                loop {
                    let member = tarjan_stack.pop().expect("Tarjan stack contains its root");
                    on_stack[member] = false;
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                components.push(component);
            }
        }
    }
    components
}

#[test]
fn iterative_tarjan_handles_20k_cycle_on_256k_native_stack() {
    std::thread::Builder::new()
        .name("recursive-lifecycle-tarjan".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut graph = vec![BTreeSet::new(); 20_000];
            for (node, successors) in graph.iter_mut().enumerate().take(19_999) {
                successors.insert(node + 1);
            }
            graph[19_999].insert(0);

            let components = strongly_connected(&graph);
            assert_eq!(components.len(), 1);
            assert_eq!(components[0].len(), 20_000);
        })
        .expect("spawn iterative Tarjan test thread")
        .join()
        .expect("iterative Tarjan test thread panicked");
}

fn crate_aliases(crates: &[CrateInfo]) -> BTreeMap<String, BTreeSet<String>> {
    let mut aliases = BTreeMap::<String, BTreeSet<String>>::new();
    for crate_info in crates {
        for alias in &crate_info.aliases {
            aliases
                .entry(alias.clone())
                .or_default()
                .insert(crate_info.key.clone());
        }
    }
    aliases
}

fn import_map(
    imports: &[ImportRecord],
) -> BTreeMap<(String, Vec<String>, String), Vec<Vec<String>>> {
    let mut map = BTreeMap::<(String, Vec<String>, String), Vec<Vec<String>>>::new();
    for import in imports {
        map.entry((import.crate_key.clone(), import.module.clone(), import.alias.clone()))
            .or_default()
            .push(import.path.clone());
    }
    map
}

struct ResolutionContext<'a> {
    crate_key: &'a str,
    module: &'a [String],
    current: Option<usize>,
    type_parameters: &'a BTreeSet<String>,
}

fn resolve_path(
    original_path: &[String],
    context: ResolutionContext<'_>,
    definitions: &[Definition],
    by_name: &BTreeMap<String, Vec<usize>>,
    aliases: &BTreeMap<String, BTreeSet<String>>,
    imports: &BTreeMap<(String, Vec<String>, String), Vec<Vec<String>>>,
) -> Vec<usize> {
    let Some(first) = original_path.first() else {
        return Vec::new();
    };
    if original_path.len() == 1 && context.type_parameters.contains(first) {
        return Vec::new();
    }
    if original_path.as_ref() == ["Self"] {
        return context.current.into_iter().collect();
    }

    let mut path = original_path.to_vec();
    if let Some(imported) =
        imports.get(&(context.crate_key.to_string(), context.module.to_vec(), first.clone()))
    {
        let distinct = imported.iter().collect::<BTreeSet<_>>();
        if distinct.len() == 1 {
            let mut expanded = imported[0].clone();
            expanded.extend_from_slice(&original_path[1..]);
            path = expanded;
        }
    }

    let Some(name) = path.last() else {
        return Vec::new();
    };
    let Some(candidates) = by_name.get(name) else {
        return Vec::new();
    };
    if path.len() == 1 {
        let same_module = candidates
            .iter()
            .copied()
            .filter(|candidate| {
                let definition = &definitions[*candidate];
                definition.crate_key == context.crate_key && definition.module == context.module
            })
            .collect::<Vec<_>>();
        if !same_module.is_empty() {
            return same_module;
        }
        let same_crate = candidates
            .iter()
            .copied()
            .filter(|candidate| definitions[*candidate].crate_key == context.crate_key)
            .collect::<Vec<_>>();
        if same_crate.len() == 1 {
            return same_crate;
        }
        return (candidates.len() == 1)
            .then(|| candidates.clone())
            .unwrap_or_default();
    }

    let qualifiers = &path[..path.len() - 1];
    let mut exact_crate = None::<String>;
    let mut exact_module = None::<Vec<String>>;
    match qualifiers.first().map(String::as_str) {
        Some("crate") => {
            exact_crate = Some(context.crate_key.to_string());
            exact_module = Some(qualifiers[1..].to_vec());
        },
        Some("self") => {
            exact_crate = Some(context.crate_key.to_string());
            exact_module = Some(
                context
                    .module
                    .iter()
                    .cloned()
                    .chain(qualifiers[1..].iter().cloned())
                    .collect(),
            );
        },
        Some("super") => {
            let super_count = qualifiers
                .iter()
                .take_while(|part| part.as_str() == "super")
                .count();
            if super_count <= context.module.len() {
                let mut module = context.module[..context.module.len() - super_count].to_vec();
                module.extend_from_slice(&qualifiers[super_count..]);
                exact_crate = Some(context.crate_key.to_string());
                exact_module = Some(module);
            }
        },
        Some(alias) => {
            if let Some(crate_keys) = aliases.get(alias) {
                if crate_keys.len() == 1 {
                    exact_crate = crate_keys.iter().next().cloned();
                    exact_module = Some(qualifiers[1..].to_vec());
                }
            }
        },
        None => {},
    }
    if let (Some(crate_key), Some(module)) = (exact_crate, exact_module) {
        return candidates
            .iter()
            .copied()
            .filter(|candidate| {
                definitions[*candidate].crate_key == crate_key
                    && definitions[*candidate].module == module
            })
            .collect();
    }

    let mut local_modules = Vec::new();
    local_modules.push(
        context
            .module
            .iter()
            .cloned()
            .chain(qualifiers.iter().cloned())
            .collect::<Vec<_>>(),
    );
    local_modules.push(qualifiers.to_vec());
    let local = candidates
        .iter()
        .copied()
        .filter(|candidate| {
            let definition = &definitions[*candidate];
            definition.crate_key == context.crate_key && local_modules.contains(&definition.module)
        })
        .collect::<Vec<_>>();
    if !local.is_empty() {
        return local;
    }

    let suffix = candidates
        .iter()
        .copied()
        .filter(|candidate| definitions[*candidate].module.ends_with(qualifiers))
        .collect::<Vec<_>>();
    if suffix.len() == 1 {
        return suffix;
    }
    if candidates.len() == 1 && Some(candidates[0]) != context.current {
        return candidates.clone();
    }
    Vec::new()
}

fn operation_graph(
    definitions: &[Definition],
    by_name: &BTreeMap<String, Vec<usize>>,
    operation: u16,
    aliases: &BTreeMap<String, BTreeSet<String>>,
    imports: &BTreeMap<(String, Vec<String>, String), Vec<Vec<String>>>,
) -> Vec<BTreeSet<usize>> {
    let mut graph = vec![BTreeSet::new(); definitions.len()];
    for (index, definition) in definitions.iter().enumerate() {
        for reference in &definition.references {
            if reference.operations & operation == 0 {
                continue;
            }
            for candidate in resolve_path(
                &reference.path,
                ResolutionContext {
                    crate_key: &definition.crate_key,
                    module: &definition.module,
                    current: Some(index),
                    type_parameters: &definition.type_parameters,
                },
                definitions,
                by_name,
                aliases,
                imports,
            ) {
                graph[index].insert(candidate);
            }
        }
    }
    graph
}

fn recursive_components(graph: &[BTreeSet<usize>]) -> Vec<Vec<usize>> {
    strongly_connected(graph)
        .into_iter()
        .filter(|component| {
            component.len() > 1
                || component
                    .first()
                    .is_some_and(|node| graph[*node].contains(node))
        })
        .collect()
}

fn recursive_nodes(graph: &[BTreeSet<usize>]) -> BTreeSet<usize> {
    recursive_components(graph).into_iter().flatten().collect()
}

struct Census {
    files: Vec<PathBuf>,
    definitions: Vec<Definition>,
    by_name: BTreeMap<String, Vec<usize>>,
    aliases: BTreeMap<String, BTreeSet<String>>,
    imports: BTreeMap<(String, Vec<String>, String), Vec<Vec<String>>>,
    implementations: BTreeMap<String, BTreeSet<usize>>,
}

impl Census {
    fn graph(&self, operation: u16) -> Vec<BTreeSet<usize>> {
        operation_graph(&self.definitions, &self.by_name, operation, &self.aliases, &self.imports)
    }

    fn implementation_nodes(&self, trait_name: &str) -> BTreeSet<usize> {
        self.implementations
            .get(trait_name)
            .cloned()
            .unwrap_or_default()
    }
}

fn finish_census(
    files: Vec<PathBuf>,
    definitions: Vec<Definition>,
    implementation_records: Vec<ImplRecord>,
    import_records: Vec<ImportRecord>,
    aliases: BTreeMap<String, BTreeSet<String>>,
) -> Census {
    let mut by_name = BTreeMap::<String, Vec<usize>>::new();
    for (index, definition) in definitions.iter().enumerate() {
        by_name
            .entry(definition.name.clone())
            .or_default()
            .push(index);
    }
    let imports = import_map(&import_records);
    let no_type_parameters = BTreeSet::new();
    let mut implementations = BTreeMap::<String, BTreeSet<usize>>::new();
    for implementation in implementation_records {
        let nodes = resolve_path(
            &implementation.self_path,
            ResolutionContext {
                crate_key: &implementation.crate_key,
                module: &implementation.module,
                current: None,
                type_parameters: &no_type_parameters,
            },
            &definitions,
            &by_name,
            &aliases,
            &imports,
        );
        if nodes.is_empty()
            && definitions.iter().any(|definition| {
                definition.file == implementation.file
                    && implementation.self_path.last() == Some(&definition.name)
            })
        {
            panic!(
                "failed to resolve local implementation {} for {} in {}",
                implementation.trait_name,
                implementation.self_path.join("::"),
                implementation.file
            );
        }
        implementations
            .entry(implementation.trait_name)
            .or_default()
            .extend(nodes);
    }
    Census {
        files,
        definitions,
        by_name,
        aliases,
        imports,
        implementations,
    }
}

fn collect_workspace(root: &Path) -> Census {
    let crates = crate_infos(root);
    let aliases = crate_aliases(&crates);
    let files = source_files(&crates);
    let mut definitions = Vec::new();
    let mut implementations = Vec::new();
    let mut imports = Vec::new();
    for path in &files {
        let crate_info = crates
            .iter()
            .find(|crate_info| path.starts_with(&crate_info.source_root))
            .expect("a scanned source belongs to one configured crate");
        let relative = path
            .strip_prefix(root)
            .unwrap_or(path)
            .to_string_lossy()
            .replace('\\', "/");
        let source = std::fs::read_to_string(path).expect("production Rust source is readable");
        let mut syntax = syn::parse_file(&source)
            .unwrap_or_else(|error| panic!("failed to parse {}: {error}", path.display()));
        let mut collector = TypeCollector::new(
            relative,
            crate_info.key.clone(),
            file_module(&crate_info.source_root, path),
        );
        collector.visit_file_mut(&mut syntax);
        definitions.extend(collector.definitions);
        implementations.extend(collector.implementations);
        imports.extend(collector.imports);
    }
    finish_census(files, definitions, implementations, imports, aliases)
}

fn collect_fixture(source: &str) -> Census {
    let mut syntax = syn::parse_file(source).expect("synthetic lifecycle fixture parses");
    let mut collector =
        TypeCollector::new("fixture/src/lib.rs".to_string(), "fixture".to_string(), Vec::new());
    collector.visit_file_mut(&mut syntax);
    finish_census(
        vec![PathBuf::from("fixture/src/lib.rs")],
        collector.definitions,
        collector.implementations,
        collector.imports,
        BTreeMap::from([("fixture".to_string(), BTreeSet::from(["fixture".to_string()]))]),
    )
}

fn definition_label(definition: &Definition) -> String {
    let module = if definition.module.is_empty() {
        String::new()
    } else {
        format!("{}::", definition.module.join("::"))
    };
    format!("{}::{module}{} [{}]", definition.crate_key, definition.name, definition.file)
}

fn render_component(
    component: &[usize],
    graph: &[BTreeSet<usize>],
    definitions: &[Definition],
) -> String {
    let members = component.iter().copied().collect::<BTreeSet<_>>();
    let mut labels = component
        .iter()
        .map(|node| definition_label(&definitions[*node]))
        .collect::<Vec<_>>();
    labels.sort();
    let mut edges = component
        .iter()
        .flat_map(|from| {
            graph[*from]
                .iter()
                .filter(|to| members.contains(to))
                .map(|to| {
                    format!(
                        "{} -> {}",
                        definition_label(&definitions[*from]),
                        definition_label(&definitions[*to])
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    edges.sort();
    format!("members=[{}]; edges=[{}]", labels.join("; "), edges.join("; "))
}

fn component_by_node(graph: &[BTreeSet<usize>]) -> BTreeMap<usize, Vec<usize>> {
    let mut out = BTreeMap::new();
    for component in recursive_components(graph) {
        for node in &component {
            out.insert(*node, component.clone());
        }
    }
    out
}

fn reachable(graph: &[BTreeSet<usize>], start: usize, target: usize) -> bool {
    let mut pending = vec![start];
    let mut seen = BTreeSet::new();
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        if node == target {
            return true;
        }
        pending.extend(graph[node].iter().copied());
    }
    false
}

fn enclosing_owner_evidence(
    census: &Census,
    rows: &[(&str, &str, &str)],
) -> Result<BTreeSet<usize>, Vec<String>> {
    let drop_graph = census.graph(DROP);
    let recursive_drop = recursive_nodes(&drop_graph);
    let explicit_drop = census.implementation_nodes("Drop");
    let mut helpers = BTreeSet::new();
    let mut errors = Vec::new();
    for (file, helper_name, owner_name) in rows {
        let helper = census
            .definitions
            .iter()
            .enumerate()
            .filter(|(_, definition)| definition.file == *file && definition.name == *helper_name)
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let owner = census
            .definitions
            .iter()
            .enumerate()
            .filter(|(_, definition)| definition.file == *file && definition.name == *owner_name)
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if helper.len() != 1 || owner.len() != 1 {
            errors.push(format!(
                "{file}::{helper_name} -> {owner_name}: expected one exact helper and owner, found {} and {}",
                helper.len(),
                owner.len()
            ));
            continue;
        }
        let helper = helper[0];
        let owner = owner[0];
        if !recursive_drop.contains(&helper) {
            errors.push(format!(
                "{} is dispositioned as recursively owned but is not in a Drop SCC",
                definition_label(&census.definitions[helper])
            ));
        }
        if !explicit_drop.contains(&owner) {
            errors.push(format!(
                "{} has no exact explicit Drop implementation",
                definition_label(&census.definitions[owner])
            ));
        }
        if !reachable(&drop_graph, owner, helper) {
            errors.push(format!(
                "{} does not own a Drop-reachable path to {}",
                definition_label(&census.definitions[owner]),
                definition_label(&census.definitions[helper])
            ));
        }
        helpers.insert(helper);
    }
    if errors.is_empty() {
        Ok(helpers)
    } else {
        Err(errors)
    }
}

fn lifecycle_violations(census: &Census, enclosing_helpers: &BTreeSet<usize>) -> Vec<String> {
    let mut violations = Vec::new();
    for (derive, operation) in DERIVE_OPERATIONS {
        let graph = census.graph(*operation);
        let components = component_by_node(&graph);
        for (node, component) in &components {
            if census.definitions[*node].derives.contains(*derive) {
                violations.push(format!(
                    "{} derives recursive {derive}; {}",
                    definition_label(&census.definitions[*node]),
                    render_component(component, &graph, &census.definitions)
                ));
            }
        }
    }

    let drop_graph = census.graph(DROP);
    let components = component_by_node(&drop_graph);
    let explicit_drop = census.implementation_nodes("Drop");
    for (node, component) in components {
        if !explicit_drop.contains(&node) && !enclosing_helpers.contains(&node) {
            violations.push(format!(
                "{} has recursive implicit Drop; {}",
                definition_label(&census.definitions[node]),
                render_component(&component, &drop_graph, &census.definitions)
            ));
        }
    }
    violations.sort();
    violations
}

fn node_named(census: &Census, module: &[&str], name: &str) -> usize {
    let module = module
        .iter()
        .map(|part| part.to_string())
        .collect::<Vec<_>>();
    census
        .definitions
        .iter()
        .position(|definition| definition.module == module && definition.name == name)
        .unwrap_or_else(|| panic!("fixture definition {}::{name} is missing", module.join("::")))
}

#[test]
fn ownership_wrappers_and_qualified_paths_have_trait_specific_edges() {
    let census = collect_fixture(
        r#"
        struct Direct(Option<Box<Direct>>);
        struct Shared(std::sync::Arc<Shared>);
        struct Manual(std::mem::ManuallyDrop<Box<Manual>>);
        struct Borrowed<'a>(&'a Borrowed<'a>);
        struct SelfNamed(Box<Self>);
        mod left { pub struct Node(pub Option<Box<Node>>); }
        mod right {
            use super::left::Node as LeftNode;
            pub struct Node(pub Option<Box<Node>>);
            pub struct Qualified(pub super::left::Node);
            pub struct Imported(pub LeftNode);
        }
        struct Node(external::Node);
        "#,
    );
    let direct = node_named(&census, &[], "Direct");
    let shared = node_named(&census, &[], "Shared");
    let manual = node_named(&census, &[], "Manual");
    let borrowed = node_named(&census, &[], "Borrowed");
    let self_named = node_named(&census, &[], "SelfNamed");
    let left = node_named(&census, &["left"], "Node");
    let right = node_named(&census, &["right"], "Node");
    let qualified = node_named(&census, &["right"], "Qualified");
    let imported = node_named(&census, &["right"], "Imported");
    let external_same_name = node_named(&census, &[], "Node");

    for operation in [CLONE, DEBUG, PARTIAL_EQ, HASH, SERIALIZE, DISPLAY, DROP] {
        let graph = census.graph(operation);
        assert!(graph[direct].contains(&direct));
        assert!(graph[self_named].contains(&self_named));
    }
    assert!(!census.graph(CLONE)[shared].contains(&shared));
    assert!(census.graph(DROP)[shared].contains(&shared));
    assert!(!census.graph(DROP)[manual].contains(&manual));
    assert!(census.graph(CLONE)[manual].contains(&manual));
    assert!(!census.graph(CLONE)[borrowed].contains(&borrowed));
    assert!(!census.graph(DROP)[borrowed].contains(&borrowed));
    assert!(!census.graph(DESERIALIZE)[borrowed].contains(&borrowed));
    assert!(census.graph(DEBUG)[borrowed].contains(&borrowed));
    assert!(census.graph(SERIALIZE)[borrowed].contains(&borrowed));
    assert!(census.graph(DROP)[qualified].contains(&left));
    assert!(!census.graph(DROP)[qualified].contains(&right));
    assert!(census.graph(DROP)[imported].contains(&left));
    assert!(!census.graph(DROP)[imported].contains(&right));
    assert!(!census.graph(DROP)[external_same_name].contains(&external_same_name));
}

#[test]
fn unsafe_derive_mutation_is_detected_and_shared_clone_is_not() {
    let unsafe_census = collect_fixture("#[derive(Clone)] struct Recursive(Box<Recursive>);");
    let violations = lifecycle_violations(&unsafe_census, &BTreeSet::new());
    assert!(
        violations
            .iter()
            .any(|violation| violation.contains("derives recursive Clone")),
        "the planted recursive Clone derive escaped the census: {violations:?}"
    );

    let shared_census = collect_fixture(
        "#[derive(Clone)] struct Recursive(std::sync::Arc<Recursive>); impl Drop for Recursive { fn drop(&mut self) {} }",
    );
    let violations = lifecycle_violations(&shared_census, &BTreeSet::new());
    assert!(
        violations
            .iter()
            .all(|violation| !violation.contains("derives recursive Clone")),
        "Arc clone was misclassified as payload recursion: {violations:?}"
    );
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum VisitEvent {
    Enter(u8),
    Exit(u8),
}

#[derive(Clone, Debug)]
enum OracleTree {
    Node(u8, Vec<OracleTree>),
}

fn recursive_events(tree: &OracleTree, out: &mut Vec<VisitEvent>) {
    match tree {
        OracleTree::Node(tag, children) => {
            out.push(VisitEvent::Enter(*tag));
            for child in children {
                recursive_events(child, out);
            }
            out.push(VisitEvent::Exit(*tag));
        },
    }
}

fn pda_events(tree: &OracleTree) -> Vec<VisitEvent> {
    enum Task<'tree> {
        Visit(&'tree OracleTree),
        Exit(u8),
    }
    let mut work = vec![Task::Visit(tree)];
    let mut out = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(OracleTree::Node(tag, children)) => {
                out.push(VisitEvent::Enter(*tag));
                work.push(Task::Exit(*tag));
                work.extend(children.iter().rev().map(Task::Visit));
            },
            Task::Exit(tag) => out.push(VisitEvent::Exit(tag)),
        }
    }
    out
}

fn oracle_tree_strategy() -> impl proptest::strategy::Strategy<Value = OracleTree> {
    use proptest::prelude::*;
    any::<u8>()
        .prop_map(|tag| OracleTree::Node(tag, Vec::new()))
        .prop_recursive(8, 256, 8, |inner| {
            (any::<u8>(), proptest::collection::vec(inner, 0..=4))
                .prop_map(|(tag, children)| OracleTree::Node(tag, children))
        })
}

proptest::proptest! {
    #[test]
    fn explicit_lifecycle_visit_machine_matches_recursive_equation(tree in oracle_tree_strategy()) {
        let mut expected = Vec::new();
        recursive_events(&tree, &mut expected);
        proptest::prop_assert_eq!(pda_events(&tree), expected);
    }
}

#[test]
fn recursive_types_have_explicit_stack_safe_lifecycle_implementations() {
    let root = workspace_root();
    let census = collect_workspace(&root);
    assert!(!census.files.is_empty(), "recursive lifecycle census scanned no source files");
    assert!(
        census.definitions.len() >= 1_000,
        "recursive lifecycle census parsed only {} definitions from {} files",
        census.definitions.len(),
        census.files.len()
    );

    let enclosing_helpers = enclosing_owner_evidence(&census, ENCLOSING_DROP_OWNERS)
        .unwrap_or_else(|errors| {
            panic!("invalid enclosing-owner dispositions:\n  {}", errors.join("\n  "))
        });
    let violations = lifecycle_violations(&census, &enclosing_helpers);

    let mut summaries = Vec::new();
    for (derive, operation) in DERIVE_OPERATIONS {
        let graph = census.graph(*operation);
        let components = recursive_components(&graph);
        let nodes = components.iter().map(Vec::len).sum::<usize>();
        assert!(
            nodes > 0,
            "the {derive} lifecycle graph went vacuous over {} definitions",
            census.definitions.len()
        );
        summaries.push(format!("{derive}={nodes}/{}", components.len()));
    }
    let display_graph = census.graph(DISPLAY);
    let recursive_display = recursive_nodes(&display_graph);
    let manual_display = census.implementation_nodes("Display");
    let display_candidates = recursive_display.intersection(&manual_display).count();

    println!(
        "  recursive lifecycle census: {} definitions, {} source files; {}; Display candidates={display_candidates}; enclosing owners={}",
        census.definitions.len(),
        census.files.len(),
        summaries.join(", "),
        enclosing_helpers.len()
    );
    assert!(
        violations.is_empty(),
        "RECURSIVE LIFECYCLE EXPOSURES remain in {} operation/type pair(s):\n  {}\n\n\
         Replace recursive derives and implicit destruction with explicit heap-backed lifecycle \
         machines. Manual Display implementations are covered by the hand-written recursion \
         census. Do not add a depth cap or enlarge the native stack.",
        violations.len(),
        violations.join("\n  ")
    );
}
