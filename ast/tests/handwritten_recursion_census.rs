//! ★★★ **The DERIVED census of hand-written recursion — mettail half.**
//!
//! The f1r3node half is `f1r3node-rust-mettail/rholang/tests/handwritten_recursion_census.rs`
//! and carries the full rationale. This file is the same algorithm over the other repository,
//! which is what the owner's scope-(a) ruling — *both repos, all crates* — requires.
//!
//! # What is different here, and why the two cannot be one file
//!
//! mettail's recursion splits three ways, and only one of the three is this file's:
//!
//! | surface | census | why |
//! |---|---|---|
//! | **generated files** | `GENERATED_FILE_CENSUS` in `rholang-runtime/tests/stack_depth_gate.rs` | reads `target/generated/`, i.e. the ARTEFACT |
//! | **macro-expansion-time recursion** | ⇐ **this file** | an emitter walking a `LanguageDef` at compile time |
//! | **the recursion an emitter EMITS** | `GENERATED_FILE_CENSUS`, not here | ⚠ invisible to a source scan: `dovetail_report` is `term_depth`'s **40-site** caller and every one of those sites exists only after expansion |
//!
//! ⇒ **A green run here says nothing about generated output**, and that boundary is the one
//! thing a reader must not blur. `macros/src/gen/term_ops/depth.rs` appearing below means *the
//! emitter walks the language definition recursively*, not that `term_depth` recurses — the
//! latter is `stack_depth_gate.rs`'s subject.
//!
//! # The term family is the DSL's, not the runtime's
//!
//! f1r3node's family is `rhoapi`'s messages. mettail's hand-written traversals walk the
//! **language definition** — `LanguageDef`, `RuleDef`, `TypeExpr`, `Pattern`, `Premise` — and
//! the AST types those describe. A cycle over them is a compile-time exposure: it runs inside
//! the proc-macro, where an overflow aborts the build with no unwind.
//!
//! ⚠ `panic!` does not unwind across the `proc_macro` bridge under cranelift, so an emitter
//! that overflows prints nothing. That is why compile-time recursion deserves a census at all
//! and is not merely a tidiness concern.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use quote::ToTokens;
use syn::visit_mut::{self, VisitMut};
use syn::{Attribute, Expr, FnArg, ItemImpl, ItemMod, ItemTrait, Pat, Type};

const CRATE_ROOTS: &[&str] = &[
    "ast/src",
    "macros/src",
    "runtime/src",
    "rholang-runtime/src",
    // The recursive lowering oracle was deliberately moved out of production
    // sources. Keep this one test-only directory in the scan so the census has
    // a real, independently known mutual-recursion calibration target.
    "rholang-runtime/tests/support",
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

/// The DSL's own term family — what a compile-time traversal walks.
const TERM_FAMILY: &[&str] = &[
    "Proc",
    "Name",
    "TypeExpr",
    "Pattern",
    "Term",
    "LanguageDef",
    "RuleDef",
    "Premise",
    "Rewrite",
    "Equation",
    "GroundTerm",
    "RuntimeObservationValue",
    "BodyAtom",
    "Query",
    "TermParam",
    "SyntaxExpr",
    "PatternOp",
    "Condition",
    "BehavioralPred",
    "BehavioralFormula",
    "QDomain",
    "RefinementPredicate",
    "ConstraintDomain",
    "TreeConstraintExpr",
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Disposition {
    /// A deliberate reference implementation retained for a differential.
    OracleTwin(&'static str),
    /// Recursion over a bounded structure — a fixed-arity walk, a grammar of known shape, a
    /// fixture builder whose depth the caller chooses.
    NotATermDepthCycle(&'static str),
}

/// ★★ The FILE SET is derived; only the disposition is declared. A file that grows a
/// term-family cycle without a row fails this test **by name**.
const RECURSION_DISPOSITIONS: &[(&str, Disposition)] = &[
    (
        "rholang-runtime/tests/support/rholang_ast_recursive_oracle.rs",
        Disposition::OracleTwin(
            "the pre-conversion lowering recursion is retained only for exact differential tests",
        ),
    ),
    (
        "rholang-runtime/tests/support/observation_scan_recursive_oracle.rs",
        Disposition::OracleTwin(
            "the pre-conversion observation recursion is retained only for exact ordered differentials",
        ),
    ),
    (
        "testkit/src/analytical/confluence.rs",
        Disposition::NotATermDepthCycle(
            "analytical confluence traverses the finite rule graph rather than term depth",
        ),
    ),
    (
        "rholang-runtime/tests/support/stack_depth_probe.rs",
        Disposition::NotATermDepthCycle(
            "the deliberately recursive calibration probe is caller-bounded test support",
        ),
    ),
];

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("`ast` is a workspace member, so its manifest dir has a parent")
        .to_path_buf()
}

fn source_files(root: &Path) -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for e in entries.flatten() {
            let p = e.path();
            let name = e.file_name();
            let name = name.to_string_lossy();
            if p.is_dir() {
                if matches!(name.as_ref(), "target" | ".git" | ".claude" | "node_modules") {
                    continue;
                }
                walk(&p, out);
            } else if name.ends_with(".rs") {
                out.push(p);
            }
        }
    }
    let mut out = Vec::new();
    for r in CRATE_ROOTS {
        let d = root.join(r);
        if d.is_dir() {
            walk(&d, &mut out);
        }
    }
    out.sort();
    out
}

type Node = (usize, String, usize); // (file index, qualified display name, file-local ordinal)

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum FunctionOwner {
    Free(String),
    Impl {
        display: String,
        type_name: Option<String>,
    },
    Trait(String),
}

impl FunctionOwner {
    fn label(&self, name: &str) -> String {
        match self {
            Self::Free(module) if module.is_empty() => name.to_string(),
            Self::Free(module) => format!("{module}::{name}"),
            Self::Impl { display, .. } => format!("{display}::{name}"),
            Self::Trait(display) => format!("trait {display}::{name}"),
        }
    }

    fn is_free(&self) -> bool {
        matches!(self, Self::Free(_))
    }

    fn module(&self) -> Option<&str> {
        match self {
            Self::Free(module) => Some(module),
            Self::Impl { .. } | Self::Trait(_) => None,
        }
    }

    fn type_name(&self) -> Option<&str> {
        match self {
            Self::Impl { type_name, .. } => type_name.as_deref(),
            Self::Trait(name) => Some(name),
            Self::Free(_) => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum CallSite {
    Direct(String),
    Qualified(Vec<String>),
    Method {
        name: String,
        self_receiver: bool,
        receiver_type: Option<String>,
        simple_receiver: bool,
    },
}

struct ParsedFunction {
    name: String,
    owner: FunctionOwner,
    calls: BTreeSet<CallSite>,
    mentions_term_family: bool,
}

struct FunctionDef {
    owner: FunctionOwner,
    calls: BTreeSet<CallSite>,
    mentions_term_family: bool,
}

fn terminal_type_ident(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(path) => path
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string()),
        Type::Reference(reference) => terminal_type_ident(&reference.elem),
        Type::Ptr(pointer) => terminal_type_ident(&pointer.elem),
        Type::Paren(paren) => terminal_type_ident(&paren.elem),
        Type::Group(group) => terminal_type_ident(&group.elem),
        Type::Slice(slice) => terminal_type_ident(&slice.elem),
        Type::Array(array) => terminal_type_ident(&array.elem),
        Type::TraitObject(object) => object.bounds.iter().find_map(|bound| match bound {
            syn::TypeParamBound::Trait(trait_bound) => trait_bound
                .path
                .segments
                .last()
                .map(|segment| segment.ident.to_string()),
            _ => None,
        }),
        Type::ImplTrait(object) => object.bounds.iter().find_map(|bound| match bound {
            syn::TypeParamBound::Trait(trait_bound) => trait_bound
                .path
                .segments
                .last()
                .map(|segment| segment.ident.to_string()),
            _ => None,
        }),
        _ => None,
    }
}

fn path_parts(path: &syn::Path) -> Vec<String> {
    path.segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect()
}

fn simple_expr_ident(expr: &Expr) -> Option<String> {
    let Expr::Path(path) = expr else { return None };
    if path.qself.is_none() && path.path.segments.len() == 1 {
        path.path
            .segments
            .first()
            .map(|segment| segment.ident.to_string())
    } else {
        None
    }
}

struct CallCollector {
    calls: BTreeSet<CallSite>,
    parameter_types: BTreeMap<String, String>,
}

impl VisitMut for CallCollector {
    fn visit_expr_call_mut(&mut self, node: &mut syn::ExprCall) {
        if let Expr::Path(path) = node.func.as_ref() {
            let parts = path_parts(&path.path);
            match parts.as_slice() {
                [name] => {
                    self.calls.insert(CallSite::Direct(name.clone()));
                },
                [] => {},
                _ => {
                    self.calls.insert(CallSite::Qualified(parts));
                },
            }
        }
        visit_mut::visit_expr_call_mut(self, node);
    }

    fn visit_expr_method_call_mut(&mut self, node: &mut syn::ExprMethodCall) {
        let receiver = simple_expr_ident(&node.receiver);
        let self_receiver = receiver.as_deref() == Some("self");
        let receiver_type = receiver
            .as_ref()
            .and_then(|name| self.parameter_types.get(name).cloned());
        self.calls.insert(CallSite::Method {
            name: node.method.to_string(),
            self_receiver,
            receiver_type,
            simple_receiver: receiver.is_some(),
        });
        visit_mut::visit_expr_method_call_mut(self, node);
    }

    fn visit_expr_path_mut(&mut self, node: &mut syn::ExprPath) {
        // Qualified function values such as `Pattern::free_vars` can be invoked by
        // iterator adaptors without appearing as an `ExprCall`. Record them; the
        // resolver discards paths that do not name a known function.
        let parts = path_parts(&node.path);
        if parts.len() > 1 {
            self.calls.insert(CallSite::Qualified(parts));
        }
        visit_mut::visit_expr_path_mut(self, node);
    }
}

fn signature_parameter_types(signature: &syn::Signature) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for input in &signature.inputs {
        let FnArg::Typed(argument) = input else {
            continue;
        };
        let Pat::Ident(pattern) = argument.pat.as_ref() else {
            continue;
        };
        if let Some(ty) = terminal_type_ident(&argument.ty) {
            out.insert(pattern.ident.to_string(), ty);
        }
    }
    out
}

fn token_idents(tokens: proc_macro2::TokenStream) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut work = vec![tokens];
    while let Some(stream) = work.pop() {
        for token in stream {
            match token {
                proc_macro2::TokenTree::Group(group) => work.push(group.stream()),
                proc_macro2::TokenTree::Ident(ident) => {
                    out.insert(ident.to_string());
                },
                proc_macro2::TokenTree::Punct(_) | proc_macro2::TokenTree::Literal(_) => {},
            }
        }
    }
    out
}

fn is_test_only(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attribute| {
        let last = attribute
            .path()
            .segments
            .last()
            .map(|segment| segment.ident.to_string());
        if last.as_deref() == Some("test") {
            return true;
        }
        if attribute.path().is_ident("cfg") {
            let compact = attribute
                .meta
                .to_token_stream()
                .to_string()
                .replace(' ', "");
            return compact == "cfg(test)";
        }
        false
    })
}

struct FunctionCollector {
    module: Vec<String>,
    owner: Option<FunctionOwner>,
    functions: Vec<ParsedFunction>,
}

impl FunctionCollector {
    fn collect(&mut self, signature: &syn::Signature, block: &syn::Block) {
        let owner = self
            .owner
            .clone()
            .unwrap_or_else(|| FunctionOwner::Free(self.module.join("::")));
        let mut block = block.clone();
        let mut calls = CallCollector {
            calls: BTreeSet::new(),
            parameter_types: signature_parameter_types(signature),
        };
        calls.visit_block_mut(&mut block);

        let mut tokens = proc_macro2::TokenStream::new();
        signature.to_tokens(&mut tokens);
        block.to_tokens(&mut tokens);
        let idents = token_idents(tokens);
        let mentions_term_family = TERM_FAMILY.iter().any(|ty| idents.contains(*ty));
        self.functions.push(ParsedFunction {
            name: signature.ident.to_string(),
            owner,
            calls: calls.calls,
            mentions_term_family,
        });
    }
}

impl VisitMut for FunctionCollector {
    fn visit_item_mod_mut(&mut self, node: &mut ItemMod) {
        if is_test_only(&node.attrs) {
            return;
        }
        self.module.push(node.ident.to_string());
        visit_mut::visit_item_mod_mut(self, node);
        self.module.pop();
    }

    fn visit_item_fn_mut(&mut self, node: &mut syn::ItemFn) {
        if is_test_only(&node.attrs) {
            return;
        }
        let saved_owner = self.owner.take();
        self.collect(&node.sig, &node.block);
        visit_mut::visit_item_fn_mut(self, node);
        self.owner = saved_owner;
    }

    fn visit_item_impl_mut(&mut self, node: &mut ItemImpl) {
        if is_test_only(&node.attrs) {
            return;
        }
        let display = node.self_ty.to_token_stream().to_string();
        let owner = FunctionOwner::Impl {
            type_name: terminal_type_ident(&node.self_ty),
            display,
        };
        let saved_owner = self.owner.replace(owner);
        visit_mut::visit_item_impl_mut(self, node);
        self.owner = saved_owner;
    }

    fn visit_impl_item_fn_mut(&mut self, node: &mut syn::ImplItemFn) {
        if is_test_only(&node.attrs) {
            return;
        }
        self.collect(&node.sig, &node.block);
        visit_mut::visit_impl_item_fn_mut(self, node);
    }

    fn visit_item_trait_mut(&mut self, node: &mut ItemTrait) {
        if is_test_only(&node.attrs) {
            return;
        }
        let saved_owner = self
            .owner
            .replace(FunctionOwner::Trait(node.ident.to_string()));
        visit_mut::visit_item_trait_mut(self, node);
        self.owner = saved_owner;
    }

    fn visit_trait_item_fn_mut(&mut self, node: &mut syn::TraitItemFn) {
        if is_test_only(&node.attrs) {
            return;
        }
        if let Some(block) = &node.default {
            self.collect(&node.sig, block);
        }
        visit_mut::visit_trait_item_fn_mut(self, node);
    }
}

fn functions_in_file(src: &str, path: &Path) -> Vec<ParsedFunction> {
    let mut file = syn::parse_file(src).unwrap_or_else(|error| {
        panic!("cannot parse `{}` for recursion census: {error}", path.display())
    });
    let mut collector = FunctionCollector {
        module: Vec::new(),
        owner: None,
        functions: Vec::new(),
    };
    collector.visit_file_mut(&mut file);
    collector.functions
}

/// Tarjan's SCC, iterative — a recursive implementation inside the census that finds
/// unbounded recursion would be this campaign's own defect, in its own instrument.
fn strongly_connected(graph: &BTreeMap<Node, BTreeSet<Node>>) -> Vec<Vec<Node>> {
    let nodes: Vec<Node> = graph.keys().cloned().collect();
    let idx_of: BTreeMap<Node, usize> = nodes
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, n)| (n, i))
        .collect();
    let adj: Vec<Vec<usize>> = nodes
        .iter()
        .map(|n| {
            graph[n]
                .iter()
                .filter_map(|m| idx_of.get(m).copied())
                .collect()
        })
        .collect();

    let n = nodes.len();
    let (mut index, mut low) = (vec![usize::MAX; n], vec![0usize; n]);
    let mut on_stack = vec![false; n];
    let (mut stack, mut counter, mut out) = (Vec::new(), 0usize, Vec::new());

    for s in 0..n {
        if index[s] != usize::MAX {
            continue;
        }
        let mut work: Vec<(usize, usize)> = vec![(s, 0)];
        index[s] = counter;
        low[s] = counter;
        counter += 1;
        stack.push(s);
        on_stack[s] = true;

        while let Some(&mut (v, ref mut pi)) = work.last_mut() {
            if *pi < adj[v].len() {
                let w = adj[v][*pi];
                *pi += 1;
                if index[w] == usize::MAX {
                    index[w] = counter;
                    low[w] = counter;
                    counter += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    work.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                work.pop();
                if let Some(&(u, _)) = work.last() {
                    low[u] = low[u].min(low[v]);
                }
                if low[v] == index[v] {
                    let mut comp = Vec::new();
                    while let Some(w) = stack.pop() {
                        on_stack[w] = false;
                        comp.push(nodes[w].clone());
                        if w == v {
                            break;
                        }
                    }
                    out.push(comp);
                }
            }
        }
    }
    out
}

struct Census {
    recursive: usize,
    term_family: Vec<Vec<Node>>,
    scanned: usize,
    rel: Vec<String>,
}

fn resolve_call(
    current: &Node,
    caller: &FunctionDef,
    call: &CallSite,
    definitions: &BTreeMap<Node, FunctionDef>,
    by_name: &BTreeMap<String, BTreeSet<Node>>,
) -> BTreeSet<Node> {
    let name = match call {
        CallSite::Direct(name) | CallSite::Method { name, .. } => name,
        CallSite::Qualified(parts) => {
            let Some(name) = parts.last() else {
                return BTreeSet::new();
            };
            name
        },
    };
    let Some(named) = by_name.get(name) else {
        return BTreeSet::new();
    };

    let matching = |predicate: &dyn Fn(&FunctionDef) -> bool| {
        named
            .iter()
            .filter(|node| definitions.get(*node).is_some_and(predicate))
            .cloned()
            .collect::<BTreeSet<_>>()
    };

    match call {
        CallSite::Direct(_) => {
            let same_module = named
                .iter()
                .filter(|node| {
                    node.0 == current.0
                        && definitions.get(*node).is_some_and(|candidate| {
                            candidate.owner.is_free()
                                && candidate.owner.module() == caller.owner.module()
                        })
                })
                .cloned()
                .collect::<BTreeSet<_>>();
            if !same_module.is_empty() {
                return same_module;
            }
            let same_file = named
                .iter()
                .filter(|node| {
                    node.0 == current.0
                        && definitions
                            .get(*node)
                            .is_some_and(|candidate| candidate.owner.is_free())
                })
                .cloned()
                .collect::<BTreeSet<_>>();
            if !same_file.is_empty() {
                return same_file;
            }
            let free = matching(&|candidate| candidate.owner.is_free());
            let files = free.iter().map(|node| node.0).collect::<BTreeSet<_>>();
            if files.len() == 1 {
                free
            } else {
                BTreeSet::new()
            }
        },
        CallSite::Qualified(parts) => {
            let qualifier = parts.get(parts.len().saturating_sub(2)).map(String::as_str);
            if matches!(qualifier, Some("Self" | "self")) {
                return matching(&|candidate| candidate.owner == caller.owner);
            }
            let Some(qualifier) = qualifier else {
                return BTreeSet::new();
            };
            matching(&|candidate| {
                candidate.owner.type_name() == Some(qualifier)
                    || candidate
                        .owner
                        .module()
                        .and_then(|module| module.rsplit("::").next())
                        == Some(qualifier)
            })
        },
        CallSite::Method {
            self_receiver,
            receiver_type,
            simple_receiver,
            ..
        } => {
            if *self_receiver {
                return matching(&|candidate| candidate.owner == caller.owner);
            }
            if let Some(receiver_type) = receiver_type {
                let typed = matching(&|candidate| {
                    candidate.owner.type_name() == Some(receiver_type.as_str())
                });
                if !typed.is_empty() {
                    return typed;
                }
            }
            // An untyped local or compound receiver is not enough evidence to
            // invent an edge. In particular, `guest.parse()` and
            // `self.inner.parse()` are ordinary delegation and must not become
            // self-cycles merely because the wrapper exposes the same method name.
            // Direct `self.method()` and typed parameters were resolved above.
            let _ = simple_receiver;
            BTreeSet::new()
        },
    }
}

fn run_census() -> Census {
    let root = workspace_root();
    let files = source_files(&root);
    assert!(
        !files.is_empty(),
        "the census found NO source files under {CRATE_ROOTS:?}. An empty scan makes every \
         assertion below vacuous."
    );
    let rel: Vec<String> = files
        .iter()
        .map(|p| {
            p.strip_prefix(&root)
                .unwrap_or(p)
                .to_string_lossy()
                .replace('\\', "/")
        })
        .collect();

    let mut definitions: BTreeMap<Node, FunctionDef> = BTreeMap::new();
    let mut by_name: BTreeMap<String, BTreeSet<Node>> = BTreeMap::new();

    for (fi, path) in files.iter().enumerate() {
        let Ok(src) = std::fs::read_to_string(path) else {
            continue;
        };
        for (ordinal, parsed) in functions_in_file(&src, path).into_iter().enumerate() {
            let node = (fi, parsed.owner.label(&parsed.name), ordinal);
            by_name
                .entry(parsed.name.clone())
                .or_default()
                .insert(node.clone());
            definitions.insert(
                node,
                FunctionDef {
                    owner: parsed.owner,
                    calls: parsed.calls,
                    mentions_term_family: parsed.mentions_term_family,
                },
            );
        }
    }

    let mut graph: BTreeMap<Node, BTreeSet<Node>> = BTreeMap::new();
    for (node, definition) in &definitions {
        let mut out = BTreeSet::new();
        for call in &definition.calls {
            out.extend(resolve_call(node, definition, call, &definitions, &by_name));
        }
        graph.insert(node.clone(), out);
    }

    let comps = strongly_connected(&graph);
    let recursive: Vec<Vec<Node>> = comps
        .into_iter()
        .filter(|c| c.len() > 1 || graph.get(&c[0]).is_some_and(|a| a.contains(&c[0])))
        .collect();

    if std::env::var_os("METTAIL_RECURSION_CENSUS_DUMP").is_some() {
        for component in &recursive {
            let members = component
                .iter()
                .map(|(file, function, ordinal)| format!("{}::{function}#{ordinal}", rel[*file]))
                .collect::<Vec<_>>()
                .join(" <-> ");
            println!("RECURSION_COMPONENT {members}");
        }
    }

    let term_family: Vec<Vec<Node>> = recursive
        .iter()
        .filter(|c| {
            c.iter().any(|node| {
                definitions
                    .get(node)
                    .is_some_and(|definition| definition.mentions_term_family)
            })
        })
        .cloned()
        .collect();

    Census {
        recursive: recursive.len(),
        term_family,
        scanned: files.len(),
        rel,
    }
}

/// ★★ Every file carrying a term-family cycle has a disposition; a new one FAILS BY NAME.
#[test]
fn every_handwritten_term_recursion_has_a_disposition() {
    let c = run_census();

    let mut with_recursion: BTreeMap<String, usize> = BTreeMap::new();
    let mut components_by_file: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for comp in &c.term_family {
        let members = comp
            .iter()
            .map(|(file, function, ordinal)| format!("{}::{function}#{ordinal}", c.rel[*file]))
            .collect::<Vec<_>>()
            .join(" <-> ");
        for (fi, _, _) in comp {
            let file = c.rel[*fi].clone();
            let e = with_recursion.entry(file.clone()).or_insert(0);
            *e = (*e).max(comp.len());
            components_by_file
                .entry(file)
                .or_default()
                .insert(members.clone());
        }
    }

    let mutual = c.term_family.iter().filter(|x| x.len() > 1).count();
    assert!(
        c.recursive > 0 && !c.term_family.is_empty(),
        "CENSUS WENT VACUOUS: scanned {} source file(s) but found {} recursive component(s), \
         {} over the term family. The dedicated lowering-oracle test separately pins a \
         47-member mutual component, so aggregate floors must not be used here: successful PDA \
         conversions are specifically intended to drive these counts down.",
        c.scanned,
        c.recursive,
        c.term_family.len(),
    );

    let declared: BTreeSet<&str> = RECURSION_DISPOSITIONS.iter().map(|(f, _)| *f).collect();
    let undispositioned: Vec<String> = with_recursion
        .iter()
        .filter(|(f, _)| !declared.contains(f.as_str()))
        .map(|(f, n)| {
            let members = components_by_file
                .get(f)
                .map(|components| {
                    components
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                        .join("\n      ")
                })
                .unwrap_or_default();
            format!("{f}  (largest component: {n})\n      {members}")
        })
        .collect();

    assert!(
        undispositioned.is_empty(),
        "UNDISPOSITIONED HAND-WRITTEN RECURSION over the term family, in {} file(s):\n  {}\n\n\
         Each contains a call-graph cycle whose members mention the DSL's term family, and \
         nothing says what is known about it.\n\n\
         Add a row to `RECURSION_DISPOSITIONS`: `OracleTwin(why)` or \
         `NotATermDepthCycle(why)`. A live production term-depth cycle is intentionally \
         unrepresentable: convert it to a PDA/iterative traversal before updating this exact \
         current-state table.\n\n\
         ⚠ If this is an EMITTER, say so: an emitter's own recursion walks the language \
         definition at expansion time and is a different traversal from the one it emits. The \
         emitted form's obligation belongs to `GENERATED_FILE_CENSUS`.",
        undispositioned.len(),
        undispositioned.join("\n  ")
    );

    assert_eq!(
        declared.len(),
        RECURSION_DISPOSITIONS.len(),
        "DUPLICATE RECURSION DISPOSITION: the declared table has {} row(s) but only {} unique \
         file name(s). A duplicate makes one disposition shadow another instead of describing \
         one exact derived file set.",
        RECURSION_DISPOSITIONS.len(),
        declared.len(),
    );
    let active: BTreeSet<&str> = with_recursion.keys().map(String::as_str).collect();
    let stale: Vec<&str> = declared.difference(&active).copied().collect();
    assert!(
        stale.is_empty(),
        "STALE HAND-WRITTEN RECURSION DISPOSITIONS remain for {} file(s):\n  {}\n\n\
         The file set is derived in both directions. Remove rows whose term-family SCC was \
         converted or disappeared; historical conversion evidence belongs in the living \
         stack-safety report, not in a current-state disposition table.",
        stale.len(),
        stale.join("\n  "),
    );

    println!(
        "  mettail recursion census: {} recursive component(s), {} over the term family ({} \
         mutual), across {} exactly dispositioned file(s)",
        c.recursive,
        c.term_family.len(),
        mutual,
        with_recursion.len(),
    );
}

/// ⭑ The calibration: the lowering oracle twin is the largest known cycle in this tree, and
/// the census must keep finding it.
///
/// ⚠ Asserted as a floor rather than an equality — this census is loose in the safe direction,
/// so demanding an exact size would make a correct over-report look like a failure.
#[test]
fn the_lowering_oracle_twin_is_found() {
    let c = run_census();
    const FILE: &str = "rholang-runtime/tests/support/rholang_ast_recursive_oracle.rs";
    const AT_LEAST: usize = 47;

    let biggest = c
        .term_family
        .iter()
        .filter(|comp| comp.iter().any(|(fi, _, _)| c.rel[*fi] == FILE))
        .map(|comp| comp.len())
        .max()
        .unwrap_or(0);

    assert!(
        biggest >= AT_LEAST,
        "CALIBRATION LOST: the largest term-family component in `{FILE}` has {biggest} \
         member(s), below the {AT_LEAST} this census was calibrated against.\n\n\
         That file is the pre-conversion `lower_arm_*` family, held verbatim as the oracle the \
         converted lowering is differentialled against. Either it was genuinely retired — say \
         so and move its disposition — or THE CENSUS HAS STOPPED WORKING and its other results \
         cannot be trusted."
    );
    println!("  oracle-twin calibration: largest component in {FILE} = {biggest}");
}
