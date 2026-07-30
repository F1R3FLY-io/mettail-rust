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
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Disposition {
    /// A deliberate reference implementation retained for a differential.
    OracleTwin(&'static str),
    /// Driven by a `rholang-runtime/tests/stack_depth_gate.rs` subject.
    Measured(&'static str),
    /// ⚠ A live Θ(depth) exposure with no subject. **This variant is the backlog.**
    Unmeasured(&'static str),
    /// Recursion over a bounded structure — a fixed-arity walk, a grammar of known shape, a
    /// fixture builder whose depth the caller chooses.
    NotATermDepthCycle(&'static str),
}

/// ★★ The FILE SET is derived; only the disposition is declared. A file that grows a
/// term-family cycle without a row fails this test **by name**.
const RECURSION_DISPOSITIONS: &[(&str, Disposition)] = &[
    // ── oracle twins: their recursion IS the point ─────────────────────────────────
    (
        "rholang-runtime/src/rholang_ast/recursive_oracle.rs",
        Disposition::OracleTwin(
            "★ the 92-member lowering oracle — the pre-conversion `lower_arm_*` family, held \
             verbatim so the converted lowering can be differentialled against it",
        ),
    ),
    // ── the term-op EMITTERS: Phase 5's targets ────────────────────────────────────
    (
        "macros/src/gen/term_ops/depth.rs",
        Disposition::NotATermDepthCycle(
            "⚠ READ THE BOUNDARY: this is the EMITTER of `term_depth`, and its own recursion \
             walks the `LanguageDef`'s finite category graph at macro-expansion time. What it \
             EMITS is measured as gate subject `ast_term_depth`; the two are different \
             traversals over different data and only the emitted one is depth-exposed",
        ),
    ),
    (
        "macros/src/gen/term_ops/ground.rs",
        Disposition::NotATermDepthCycle("emitter of `is_ground`; same boundary as depth.rs"),
    ),
    (
        "macros/src/gen/term_ops/subst.rs",
        Disposition::NotATermDepthCycle(
            "emitter of `subst`/`env_subst`; ⚠ the EMITTED `env_subst` is one of the six \
             `UNMEASURED_TRAVERSALS` and is Phase 5's first target — that obligation lives in \
             `GENERATED_FILE_CENSUS`, not here",
        ),
    ),
    (
        "macros/src/gen/syntax/display.rs",
        Disposition::NotATermDepthCycle("emitter of `Display`; emitted form is `ast_display`"),
    ),
    (
        "macros/src/gen/runtime/dovetail_report.rs",
        Disposition::NotATermDepthCycle(
            "⚠ emitter of the Dovetail report. The EMITTED `__mettail_dovetail_build_*_d` is \
             `UNMEASURED_TRAVERSALS`' largest member (14,328 self-calls) and is `term_depth`'s \
             40-site caller — sites that exist only after expansion and that NO source scan, \
             including this one, can see",
        ),
    ),
    (
        "macros/src/gen/runtime/dovetail_report/ac.rs",
        Disposition::NotATermDepthCycle("AC-carrier emitter"),
    ),
    (
        "macros/src/gen/runtime/metadata.rs",
        Disposition::NotATermDepthCycle("metadata emitter over the declaration set"),
    ),
    (
        "macros/src/gen/runtime/wpda_codegen/facade.rs",
        Disposition::NotATermDepthCycle("WPDA emitter over the grammar"),
    ),
    (
        "macros/src/gen/runtime/wpda_codegen/collection.rs",
        Disposition::NotATermDepthCycle("collection-shape emitter"),
    ),
    (
        "macros/src/gen/runtime/wpda_codegen/forks.rs",
        Disposition::NotATermDepthCycle("fork emitter"),
    ),
    (
        "macros/src/gen/syntax/parser/prattail_bridge.rs",
        Disposition::NotATermDepthCycle("bridge emitter"),
    ),
    (
        "macros/src/gen/test_gen/strategies.rs",
        Disposition::NotATermDepthCycle(
            "proptest strategy emitter; the generated strategies bound their own depth",
        ),
    ),
    // ── the DSL parser and grammar machinery ───────────────────────────────────────
    (
        "ast/src/language/parse.rs",
        Disposition::Unmeasured(
            "⚠ a 30-member cycle parsing the `language!` DSL. Depth is bounded by the SOURCE a \
             developer writes rather than by a deploy, so it is not adversary-controlled — but \
             it runs inside the proc macro, where an overflow aborts the build printing \
             nothing, and nothing measures it",
        ),
    ),
    (
        "ast/src/identity.rs",
        Disposition::Unmeasured("9-member cycle over rule identity; no subject"),
    ),
    (
        "ast/src/pattern.rs",
        Disposition::Unmeasured("pattern walk, no subject"),
    ),
    (
        "ast/src/types.rs",
        Disposition::Unmeasured("`TypeExpr` walk — nesting is bounded by the declared type"),
    ),
    (
        "ast/src/validation/validator.rs",
        Disposition::Unmeasured("validation walk over the declaration set"),
    ),
    (
        "ast/src/validation/typechecker.rs",
        Disposition::Unmeasured("type walk over `TypeExpr`"),
    ),
    // ── prattail: the parser generator ─────────────────────────────────────────────
    (
        "prattail/src/automata/codegen.rs",
        Disposition::NotATermDepthCycle(
            "lexer codegen over a finite mode map; shares a component with runtime_types.rs",
        ),
    ),
    (
        "prattail/src/runtime_types.rs",
        Disposition::NotATermDepthCycle("the other half of the lexer-codegen component"),
    ),
    (
        "prattail/src/ebnf.rs",
        Disposition::NotATermDepthCycle(
            "EBNF rendering; the component is inflated by same-file `#[test]` functions, which \
             is the over-report this census accepts",
        ),
    ),
    (
        "prattail/src/wpda_walker.rs",
        Disposition::Unmeasured(
            "⚠ the k-best realization family. Walks an SPPF whose depth follows the INPUT, so \
             this one IS input-shaped; measured by mettail's `parse_depth`/`parse_width` \
             subjects only at the recognizer boundary, not here",
        ),
    ),
    (
        "prattail/src/parser/predicate_pratt.rs",
        Disposition::Unmeasured(
            "the semantic-predicate Pratt parser — a 12-member cycle whose depth follows the \
             predicate expression a developer writes",
        ),
    ),
    (
        "prattail/src/egraph.rs",
        Disposition::Unmeasured("e-graph walk"),
    ),
    // ── rholang-codegen ────────────────────────────────────────────────────────────
    (
        "rholang-codegen/src/rho_net_lower.rs",
        Disposition::Unmeasured(
            "17-member cycle spanning three files (lower/drive/ruleset) that lowers a rule set \
             to a Rho-net; cross-file, so a per-file scan cannot see it",
        ),
    ),
    (
        "rholang-codegen/src/rho_net_drive.rs",
        Disposition::Unmeasured("second file of the rho-net lowering cycle"),
    ),
    (
        "rholang-codegen/src/rho_net_ruleset.rs",
        Disposition::Unmeasured("third file of the rho-net lowering cycle"),
    ),
    (
        "rholang-codegen/src/rho_net_float.rs",
        Disposition::Unmeasured("float lowering"),
    ),
    // ── runtime and dovetail ───────────────────────────────────────────────────────
    (
        "rholang-runtime/src/rholang_ast.rs",
        Disposition::Measured("gate subjects `lower_depth`, `lower_par`, `render`"),
    ),
    ("dovetail/src/rules.rs", Disposition::Unmeasured("rule-set walk")),
    // ── test support ───────────────────────────────────────────────────────────────
    (
        "testkit/src/ctor.rs",
        Disposition::NotATermDepthCycle("fixture constructor; the caller chooses the depth"),
    ),
    // ── ★ THE TAIL, and it is the part a hand-written list would have lost ─────────
    //
    // Every row below is a component of size 1 or 2 that the census found and a by-eye survey
    // did not: the survey was ordered by component size and stopped at the visible clusters.
    // ⚠ **#121 was a 2-cycle.** Size is not severity, and an ordering by size is exactly the
    // reading that let it hide. These are dispositioned individually rather than waved through
    // as "small".
    //
    // ★ Most are EMITTERS. An emitter's own recursion walks the `LanguageDef` at expansion
    // time over a finite category graph; what it EMITS is `GENERATED_FILE_CENSUS`' subject.
    // Where the emitted form is a known live exposure, the row says so.
    (
        "macros/src/gen/runtime/rho_invocation.rs",
        Disposition::Unmeasured(
            "⚠ a SEVEN-member component, the largest in the tail. This is `flt_reflect`'s \
             emitter — and `flt_reflect.rs` is one of the six `UNMEASURED_TRAVERSALS`, whose \
             obligation is BYTE-IDENTITY rather than a depth ladder because it crosses the \
             in-Rho ABI. Phase 5 converts it LAST for that reason",
        ),
    ),
    (
        "macros/src/gen/native/eval.rs",
        Disposition::NotATermDepthCycle(
            "emitter of `try_eval`; its emitted form became gate subjects `ast_try_eval` and \
             `ast_try_eval_cast` at `ed44c429`",
        ),
    ),
    (
        "macros/src/gen/runtime/language.rs",
        Disposition::Unmeasured(
            "emitter of `collect_all_*_vars` — `language_struct.rs` is one of the six \
             `UNMEASURED_TRAVERSALS`",
        ),
    ),
    (
        "macros/src/gen/syntax/var_inference.rs",
        Disposition::Unmeasured(
            "emitter of `infer_var_type` — `var_inference.rs` is one of the six \
             `UNMEASURED_TRAVERSALS` (2,643 self-calls in the artefact)",
        ),
    ),
    (
        "macros/src/gen/runtime/dovetail_report/typed_report.rs",
        Disposition::NotATermDepthCycle(
            "the other half of the Dovetail emitter; see `dovetail_report.rs`",
        ),
    ),
    (
        "macros/src/gen/capture.rs",
        Disposition::NotATermDepthCycle(
            "⚠ NOT an emitter — it contains zero `quote!` invocations and appears in no \
             `GENERATED_FILE_CENSUS` row. `walk_pattern` recurses over a syntax pattern at \
             expansion time; the pattern is what a developer wrote",
        ),
    ),
    (
        "macros/src/gen/runtime/binder_congruence.rs",
        Disposition::NotATermDepthCycle("binder-congruence emitter over the declaration set"),
    ),
    (
        "macros/src/gen/runtime/wpda_codegen/binder.rs",
        Disposition::NotATermDepthCycle("WPDA binder emitter"),
    ),
    (
        "macros/src/gen/runtime/wpda_codegen/prefix.rs",
        Disposition::NotATermDepthCycle("WPDA prefix emitter"),
    ),
    (
        "macros/src/gen/types/enums.rs",
        Disposition::NotATermDepthCycle("AST enum emitter over the category set"),
    ),
    (
        "macros/src/gen/test_gen/simulation_tests.rs",
        Disposition::NotATermDepthCycle("simulation-test emitter"),
    ),
    (
        "macros/src/logic/stratification.rs",
        Disposition::NotATermDepthCycle(
            "stratification over the rule dependency graph — finite by construction, and the \
             analysis exists precisely to establish that",
        ),
    ),
    (
        "ast/src/grammar.rs",
        Disposition::Unmeasured("grammar walk over the declaration set"),
    ),
    (
        "ast/src/grammar_shapes.rs",
        Disposition::Unmeasured("shape classification over `TypeExpr`"),
    ),
    (
        "dovetail/src/set_automaton.rs",
        Disposition::Unmeasured("set-automaton construction over the rule set"),
    ),
    (
        "prattail/src/confluence.rs",
        Disposition::NotATermDepthCycle(
            "confluence analysis over the rule graph; bounded by the rule set",
        ),
    ),
    (
        "prattail/src/termination.rs",
        Disposition::NotATermDepthCycle("termination analysis over the rule graph"),
    ),
    (
        "prattail/src/letprop.rs",
        Disposition::NotATermDepthCycle("let-propagation over a parsed expression"),
    ),
    (
        "prattail/src/tree_automaton.rs",
        Disposition::Unmeasured("tree-automaton construction"),
    ),
    (
        "testkit/src/analytical/confluence.rs",
        Disposition::NotATermDepthCycle("the analytical confluence checker's rule-graph walk"),
    ),
    (
        "rholang-codegen/src/backend.rs",
        Disposition::Unmeasured("backend dispatch over the lowering"),
    ),
    (
        "rholang-codegen/src/rho_net.rs",
        Disposition::Unmeasured("rho-net construction"),
    ),
    (
        "rholang-codegen/src/rho_net_naive_kt.rs",
        Disposition::NotATermDepthCycle("the naive reference backend, kept for differentials"),
    ),
    (
        "rholang-runtime/src/run.rs",
        Disposition::NotATermDepthCycle("the REPL/run driver loop"),
    ),
    (
        "rholang-runtime/src/bin/stack_depth_probe.rs",
        Disposition::NotATermDepthCycle(
            "★ THE PROBE ITSELF. Its `ast_recursion_control` subject is DELIBERATELY \
             host-recursive and is never to be converted — it is the classifier's non-vacuity \
             anchor, and without it `measured_shape` would answer `Flat` for everything",
        ),
    ),
    (
        "repl/src/observation_surface.rs",
        Disposition::NotATermDepthCycle("REPL rendering surface"),
    ),
];

/// ⚠ Non-vacuity floor on the derived file set. Measured at the commit that introduced this
/// file: **58** files carry a term-family cycle. The floor sits below that so a legitimate
/// conversion can retire files without editing it.
const MIN_FILES_WITH_TERM_RECURSION: usize = 30;

/// ⚠ Floor on MUTUAL components — the class every prior census was blind to. Measured: **43**.
const MIN_MUTUAL_COMPONENTS: usize = 25;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("`ast` is a workspace member, so its manifest dir has a parent")
        .to_path_buf()
}

fn source_files(root: &Path) -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else { return };
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

/// `(name, body)`; an unbalanced body runs to EOF — over-report, never under-report.
fn fn_bodies(src: &str) -> Vec<(String, String)> {
    let bytes = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0usize;
    while let Some(at) = src[i..].find("fn ") {
        let start = i + at;
        let ok_before = start == 0
            || !matches!(bytes[start - 1], b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_');
        i = start + 3;
        if !ok_before {
            continue;
        }
        let name: String = src[i..]
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        if name.is_empty() {
            continue;
        }
        let Some(brace) = src[i..].find('{') else { continue };
        let bstart = i + brace;
        let mut depth = 0i32;
        let mut closed = None;
        for (k, c) in src[bstart..].char_indices() {
            match c {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        closed = Some(bstart + k);
                        break;
                    }
                }
                _ => {}
            }
        }
        out.push((name, src[bstart..closed.unwrap_or(src.len())].to_string()));
    }
    out
}

/// Identifiers in call position; whitespace before the `(` is tolerated.
fn callees(body: &str) -> BTreeSet<String> {
    let b = body.as_bytes();
    let mut out = BTreeSet::new();
    let mut start: Option<usize> = None;
    for (i, c) in body.char_indices() {
        if c.is_ascii_alphanumeric() || c == '_' {
            if start.is_none() {
                start = Some(i);
            }
            continue;
        }
        let Some(s) = start.take() else { continue };
        if !b[s].is_ascii_lowercase() {
            continue;
        }
        let mut j = i;
        while j < b.len() && (b[j] as char).is_whitespace() {
            j += 1;
        }
        if j < b.len() && b[j] == b'(' {
            out.insert(body[s..i].to_string());
        }
    }
    out
}

type Node = (usize, String);

/// Tarjan's SCC, iterative — a recursive implementation inside the census that finds
/// unbounded recursion would be this campaign's own defect, in its own instrument.
fn strongly_connected(graph: &BTreeMap<Node, BTreeSet<Node>>) -> Vec<Vec<Node>> {
    let nodes: Vec<Node> = graph.keys().cloned().collect();
    let idx_of: BTreeMap<Node, usize> =
        nodes.iter().cloned().enumerate().map(|(i, n)| (n, i)).collect();
    let adj: Vec<Vec<usize>> = nodes
        .iter()
        .map(|n| graph[n].iter().filter_map(|m| idx_of.get(m).copied()).collect())
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

    let mut bodies: BTreeMap<Node, BTreeSet<String>> = BTreeMap::new();
    let mut text: BTreeMap<Node, String> = BTreeMap::new();
    let mut defined_in: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();

    for (fi, path) in files.iter().enumerate() {
        let Ok(src) = std::fs::read_to_string(path) else { continue };
        for (name, body) in fn_bodies(&src) {
            defined_in.entry(name.clone()).or_default().insert(fi);
            let key = (fi, name);
            bodies.insert(key.clone(), callees(&body));
            text.insert(key, body);
        }
    }

    let mut graph: BTreeMap<Node, BTreeSet<Node>> = BTreeMap::new();
    for (node, cs) in &bodies {
        let mut out = BTreeSet::new();
        for c in cs {
            let Some(where_) = defined_in.get(c) else { continue };
            let same = (node.0, c.clone());
            if bodies.contains_key(&same) {
                out.insert(same);
            } else if where_.len() == 1 {
                out.insert((*where_.iter().next().expect("non-empty"), c.clone()));
            }
        }
        graph.insert(node.clone(), out);
    }

    let comps = strongly_connected(&graph);
    let recursive: Vec<Vec<Node>> = comps
        .into_iter()
        .filter(|c| c.len() > 1 || graph.get(&c[0]).is_some_and(|a| a.contains(&c[0])))
        .collect();

    let term_family: Vec<Vec<Node>> = recursive
        .iter()
        .filter(|c| {
            c.iter().any(|n| {
                text.get(n).is_some_and(|t| {
                    TERM_FAMILY.iter().any(|ty| {
                        t.match_indices(ty).any(|(i, _)| {
                            let before = t[..i].chars().next_back();
                            let after = t[i + ty.len()..].chars().next();
                            !before.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
                                && !after.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
                        })
                    })
                })
            })
        })
        .cloned()
        .collect();

    Census { recursive: recursive.len(), term_family, scanned: files.len(), rel }
}

/// ★★ Every file carrying a term-family cycle has a disposition; a new one FAILS BY NAME.
#[test]
fn every_handwritten_term_recursion_has_a_disposition() {
    let c = run_census();

    let mut with_recursion: BTreeMap<String, usize> = BTreeMap::new();
    for comp in &c.term_family {
        for (fi, _) in comp {
            let e = with_recursion.entry(c.rel[*fi].clone()).or_insert(0);
            *e = (*e).max(comp.len());
        }
    }

    assert!(
        with_recursion.len() >= MIN_FILES_WITH_TERM_RECURSION,
        "CENSUS WENT VACUOUS: only {} file(s) carry a term-family cycle, below the floor of \
         {MIN_FILES_WITH_TERM_RECURSION}. That is not good news — it means the scan stopped \
         seeing things. Scanned {} file(s).",
        with_recursion.len(),
        c.scanned
    );

    let mutual = c.term_family.iter().filter(|x| x.len() > 1).count();
    assert!(
        mutual >= MIN_MUTUAL_COMPONENTS,
        "MUTUAL-RECURSION DETECTION WENT VACUOUS: {mutual} mutual component(s), below the floor \
         of {MIN_MUTUAL_COMPONENTS}. Mutual recursion is the entire reason this computes SCCs."
    );

    let declared: BTreeSet<&str> = RECURSION_DISPOSITIONS.iter().map(|(f, _)| *f).collect();
    let undispositioned: Vec<String> = with_recursion
        .iter()
        .filter(|(f, _)| !declared.contains(f.as_str()))
        .map(|(f, n)| format!("{f}  (largest component: {n})"))
        .collect();

    assert!(
        undispositioned.is_empty(),
        "UNDISPOSITIONED HAND-WRITTEN RECURSION over the term family, in {} file(s):\n  {}\n\n\
         Each contains a call-graph cycle whose members mention the DSL's term family, and \
         nothing says what is known about it.\n\n\
         Add a row to `RECURSION_DISPOSITIONS`: `Measured(subject)`, `OracleTwin(why)`, \
         `NotATermDepthCycle(why)`, or ⚠ `Unmeasured(why)`.\n\n\
         ★ `Unmeasured` is a legitimate and honest answer. A DISPOSITION IS A VALUE, NOT AN \
         ABSENCE — what is refused is saying nothing.\n\n\
         ⚠ If this is an EMITTER, say so: an emitter's own recursion walks the language \
         definition at expansion time and is a different traversal from the one it emits. The \
         emitted form's obligation belongs to `GENERATED_FILE_CENSUS`.",
        undispositioned.len(),
        undispositioned.join("\n  ")
    );

    let unmeasured: Vec<&str> = RECURSION_DISPOSITIONS
        .iter()
        .filter(|(_, d)| matches!(d, Disposition::Unmeasured(_)))
        .map(|(f, _)| *f)
        .collect();
    println!(
        "  mettail recursion census: {} recursive component(s), {} over the term family ({} \
         mutual), across {} file(s); {} UNMEASURED",
        c.recursive,
        c.term_family.len(),
        mutual,
        with_recursion.len(),
        unmeasured.len()
    );
    for f in &unmeasured {
        println!("    UNMEASURED: {f}");
    }
}

/// ⭑ The calibration: the lowering oracle twin is the largest known cycle in this tree, and
/// the census must keep finding it.
///
/// ⚠ Asserted as a floor rather than an equality — this census is loose in the safe direction,
/// so demanding an exact size would make a correct over-report look like a failure.
#[test]
fn the_lowering_oracle_twin_is_found() {
    let c = run_census();
    const FILE: &str = "rholang-runtime/src/rholang_ast/recursive_oracle.rs";
    const AT_LEAST: usize = 60;

    let biggest = c
        .term_family
        .iter()
        .filter(|comp| comp.iter().any(|(fi, _)| c.rel[*fi] == FILE))
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
