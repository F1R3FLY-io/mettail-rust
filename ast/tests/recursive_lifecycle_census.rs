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
use syn::{Attribute, Fields, GenericArgument, ItemImpl, PathArguments, Type};

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
const ALL_OPERATIONS: u16 = (1 << 12) - 1;

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
    name: String,
    /// Operations whose standard implementation follows this edge.
    operations: u16,
    /// `other_crate::SameName` must not be mistaken for a self edge.
    externally_qualified: bool,
}

#[derive(Clone, Debug)]
struct Definition {
    file: String,
    name: String,
    references: Vec<TypeReference>,
    derives: BTreeSet<String>,
}

#[derive(Default)]
struct TypeCollector {
    definitions: Vec<Definition>,
    implementations: BTreeSet<(String, String)>,
    test_depth: usize,
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
    if operations == 0 {
        return;
    }
    match ty {
        Type::Array(array) => type_references(&array.elem, operations, out),
        Type::Group(group) => type_references(&group.elem, operations, out),
        Type::Paren(paren) => type_references(&paren.elem, operations, out),
        Type::Slice(slice) => type_references(&slice.elem, operations, out),
        Type::Tuple(tuple) => {
            for elem in &tuple.elems {
                type_references(elem, operations, out);
            }
        },
        Type::Path(path) => {
            let Some(segment) = path.path.segments.last() else {
                return;
            };
            let name = segment.ident.to_string();
            if matches!(name.as_str(), "PhantomData" | "Weak") {
                return;
            }
            let first = path
                .path
                .segments
                .first()
                .map(|part| part.ident.to_string());
            let externally_qualified = path.path.segments.len() > 1
                && !matches!(first.as_deref(), Some("crate" | "self" | "super" | "Self"));
            out.push(TypeReference {
                name: name.clone(),
                operations,
                externally_qualified,
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
                            type_references(inner, child_operations, out);
                        },
                        GenericArgument::AssocType(binding) => {
                            type_references(&binding.ty, child_operations, out);
                        },
                        GenericArgument::Constraint(_)
                        | GenericArgument::Lifetime(_)
                        | GenericArgument::Const(_)
                        | GenericArgument::AssocConst(_)
                        | _ => {},
                    }
                }
            }
        },
        Type::Reference(reference) => {
            // References neither clone nor destroy the referent. Formatting,
            // comparison, hashing, and serialization do inspect it.
            type_references(&reference.elem, operations & !(CLONE | DROP | DESERIALIZE), out);
        },
        Type::Ptr(_) | Type::BareFn(_) => {},
        _ => {},
    }
}

fn field_references(fields: &Fields) -> Vec<TypeReference> {
    let mut out = Vec::new();
    for field in fields {
        type_references(&field.ty, ALL_OPERATIONS, &mut out);
    }
    out
}

fn terminal_type_name(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(path) => path
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string()),
        Type::Group(group) => terminal_type_name(&group.elem),
        Type::Paren(paren) => terminal_type_name(&paren.elem),
        _ => None,
    }
}

impl TypeCollector {
    fn add_definition(&mut self, name: String, attrs: &[Attribute], fields: &[&Fields]) {
        if self.test_depth != 0 || is_test_only(attrs) {
            return;
        }
        let mut references = Vec::new();
        for field_set in fields {
            references.extend(field_references(field_set));
        }
        self.definitions.push(Definition {
            file: String::new(),
            name,
            references,
            derives: derives(attrs),
        });
    }
}

impl VisitMut for TypeCollector {
    fn visit_item_mod_mut(&mut self, node: &mut syn::ItemMod) {
        let test = is_test_only(&node.attrs);
        self.test_depth += usize::from(test);
        visit_mut::visit_item_mod_mut(self, node);
        self.test_depth -= usize::from(test);
    }

    fn visit_item_struct_mut(&mut self, node: &mut syn::ItemStruct) {
        self.add_definition(node.ident.to_string(), &node.attrs, &[&node.fields]);
        visit_mut::visit_item_struct_mut(self, node);
    }

    fn visit_item_enum_mut(&mut self, node: &mut syn::ItemEnum) {
        let fields = node
            .variants
            .iter()
            .map(|variant| &variant.fields)
            .collect::<Vec<_>>();
        self.add_definition(node.ident.to_string(), &node.attrs, &fields);
        visit_mut::visit_item_enum_mut(self, node);
    }

    fn visit_item_impl_mut(&mut self, node: &mut ItemImpl) {
        if self.test_depth == 0 && !is_test_only(&node.attrs) {
            if let (Some((_, trait_path, _)), Some(type_name)) =
                (&node.trait_, terminal_type_name(&node.self_ty))
            {
                if let Some(trait_name) = trait_path.segments.last() {
                    self.implementations
                        .insert((type_name, trait_name.ident.to_string()));
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

fn source_files(root: &Path) -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if path.is_dir() {
                if matches!(name.as_ref(), "target" | ".git" | ".claude" | "node_modules") {
                    continue;
                }
                walk(&path, out);
            } else if name.ends_with(".rs") {
                out.push(path);
            }
        }
    }

    let mut files = Vec::new();
    for crate_root in CRATE_ROOTS {
        walk(&root.join(crate_root), &mut files);
    }
    files.sort();
    files
}

fn strongly_connected(graph: &[BTreeSet<usize>]) -> Vec<Vec<usize>> {
    struct Tarjan<'graph> {
        graph: &'graph [BTreeSet<usize>],
        next_index: usize,
        indexes: Vec<Option<usize>>,
        lowlinks: Vec<usize>,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        components: Vec<Vec<usize>>,
    }

    impl Tarjan<'_> {
        fn visit(&mut self, node: usize) {
            let index = self.next_index;
            self.next_index += 1;
            self.indexes[node] = Some(index);
            self.lowlinks[node] = index;
            self.stack.push(node);
            self.on_stack[node] = true;

            for &next in &self.graph[node] {
                if self.indexes[next].is_none() {
                    self.visit(next);
                    self.lowlinks[node] = self.lowlinks[node].min(self.lowlinks[next]);
                } else if self.on_stack[next] {
                    self.lowlinks[node] = self.lowlinks[node]
                        .min(self.indexes[next].expect("an on-stack node has an index"));
                }
            }

            if self.lowlinks[node] == index {
                let mut component = Vec::new();
                loop {
                    let member = self.stack.pop().expect("Tarjan stack contains its root");
                    self.on_stack[member] = false;
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                self.components.push(component);
            }
        }
    }

    let len = graph.len();
    let mut tarjan = Tarjan {
        graph,
        next_index: 0,
        indexes: vec![None; len],
        lowlinks: vec![0; len],
        stack: Vec::new(),
        on_stack: vec![false; len],
        components: Vec::new(),
    };
    for node in 0..len {
        if tarjan.indexes[node].is_none() {
            tarjan.visit(node);
        }
    }
    tarjan.components
}

fn operation_graph(
    definitions: &[Definition],
    by_name: &BTreeMap<String, Vec<usize>>,
    operation: u16,
) -> Vec<BTreeSet<usize>> {
    let mut graph = vec![BTreeSet::new(); definitions.len()];
    for (index, definition) in definitions.iter().enumerate() {
        for reference in &definition.references {
            if reference.operations & operation == 0 {
                continue;
            }
            let Some(candidates) = by_name.get(&reference.name) else {
                continue;
            };
            if reference.name == definition.name && !reference.externally_qualified {
                graph[index].insert(index);
                continue;
            }
            let same_file = candidates
                .iter()
                .copied()
                .filter(|candidate| definitions[*candidate].file == definition.file)
                .collect::<Vec<_>>();
            if same_file.len() == 1 && !(same_file[0] == index && reference.externally_qualified) {
                graph[index].insert(same_file[0]);
            } else if candidates.len() == 1
                && !(candidates[0] == index && reference.externally_qualified)
            {
                graph[index].insert(candidates[0]);
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

#[test]
fn recursive_types_have_explicit_stack_safe_lifecycle_implementations() {
    let root = workspace_root();
    let files = source_files(&root);
    assert!(!files.is_empty(), "recursive lifecycle census scanned no source files");

    let mut definitions = Vec::new();
    let mut implementations = BTreeSet::new();
    for path in &files {
        let source = std::fs::read_to_string(path).expect("production Rust source is readable");
        let mut syntax = syn::parse_file(&source)
            .unwrap_or_else(|error| panic!("failed to parse {}: {error}", path.display()));
        let mut collector = TypeCollector::default();
        collector.visit_file_mut(&mut syntax);
        let relative = path
            .strip_prefix(&root)
            .unwrap_or(path)
            .to_string_lossy()
            .replace('\\', "/");
        for mut definition in collector.definitions {
            definition.file = relative.clone();
            definitions.push(definition);
        }
        implementations.extend(collector.implementations);
    }

    let mut by_name: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (index, definition) in definitions.iter().enumerate() {
        by_name
            .entry(definition.name.clone())
            .or_default()
            .push(index);
    }

    let drop_graph = operation_graph(&definitions, &by_name, DROP);
    let recursive = recursive_components(&drop_graph);
    assert!(
        !recursive.is_empty(),
        "recursive lifecycle census went vacuous over {} definitions in {} files",
        definitions.len(),
        files.len()
    );

    let recursive_drop_nodes = recursive.iter().flatten().copied().collect::<BTreeSet<_>>();
    let recursive_by_derive = DERIVE_OPERATIONS
        .iter()
        .map(|(derive, operation)| {
            (*derive, recursive_nodes(&operation_graph(&definitions, &by_name, *operation)))
        })
        .collect::<BTreeMap<_, _>>();

    for (file, helper, owner) in ENCLOSING_DROP_OWNERS {
        assert!(
            implementations.contains(&(owner.to_string(), "Drop".to_string())),
            "enclosing-drop disposition {file}::{helper} names {owner}, but {owner} has no \
             explicit Drop implementation"
        );
    }

    let mut violations = Vec::new();
    let recursive_any = recursive_by_derive
        .values()
        .flatten()
        .copied()
        .chain(recursive_drop_nodes.iter().copied())
        .collect::<BTreeSet<_>>();
    for node in recursive_any {
        let definition = &definitions[node];
        let unsafe_derives = DERIVE_OPERATIONS
            .iter()
            .filter(|(derive, _)| {
                definition.derives.contains(*derive)
                    && recursive_by_derive
                        .get(derive)
                        .is_some_and(|nodes| nodes.contains(&node))
            })
            .map(|(derive, _)| *derive)
            .collect::<Vec<_>>();
        let explicit_drop = implementations.contains(&(definition.name.clone(), "Drop".into()));
        let enclosing_owner = ENCLOSING_DROP_OWNERS
            .iter()
            .find_map(|(file, helper, owner)| {
                (definition.file == *file && definition.name == *helper).then_some(*owner)
            });
        let unsafe_drop =
            recursive_drop_nodes.contains(&node) && !explicit_drop && enclosing_owner.is_none();
        if !unsafe_derives.is_empty() || unsafe_drop {
            violations.push(format!(
                "{}::{}: recursive derives [{}]; explicit Drop = {}{}",
                definition.file,
                definition.name,
                unsafe_derives.join(", "),
                explicit_drop,
                enclosing_owner
                    .map(|owner| format!(" (drained by {owner})"))
                    .unwrap_or_default()
            ));
        }
    }

    println!(
        "  recursive lifecycle census: {} recursive type(s) in {} component(s), {} source file(s)",
        recursive.iter().map(Vec::len).sum::<usize>(),
        recursive.len(),
        files.len()
    );
    assert!(
        violations.is_empty(),
        "RECURSIVE LIFECYCLE EXPOSURES remain in {} type(s):\n  {}\n\n\
         Replace recursive derives and implicit destruction with explicit heap-backed lifecycle \
         machines. Do not add a depth cap or enlarge the native stack.",
        violations.len(),
        violations.join("\n  ")
    );
}
