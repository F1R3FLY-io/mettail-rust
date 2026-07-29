//! The child half of `tests/stack_depth_gate.rs`: one subject, run **on this process's main
//! thread**, under whatever `RLIMIT_STACK` the parent set before `exec`.
//!
//! # ★ Why this is a separate program rather than a `#[test]`
//!
//! The defect being gated is on the **main thread**. `rholang-runtime/src/bin/rholang.rs` is
//! `#[tokio::main] async fn main`, so parsing and lowering run there, and a main thread's size
//! is fixed by `RLIMIT_STACK` before `main` is entered — `RUST_MIN_STACK` cannot reach it (a
//! sweep from 1 MiB to 32 MiB once reported "ok" at every value *because it was controlling
//! nothing*).
//!
//! The gate's earlier probe ran each subject on a `std::thread::Builder::stack_size` thread.
//! That is a precise instrument, but it measures a **proxy**: a spawned thread's stack is one
//! `mmap` with a guard page, while the main thread's is a kernel-grown VMA bounded by the
//! rlimit, and it is the latter that production faults on. So the probe now measures the thing
//! itself.
//!
//! ⚠ It cannot be a `#[test]` in the gate binary, and the reason is mechanical rather than
//! stylistic: **libtest runs every test on a spawned thread** (`run_test_inner` always calls
//! `thread::Builder::spawn`, falling back to the current thread only when the OS refuses).
//! A `#[test]` body therefore *cannot* execute on a main thread, whatever the parent sets. A
//! plain `fn main` can, so the probe is a `[[bin]]` and the parent reaches it through
//! `CARGO_BIN_EXE_stack_depth_probe`.
//!
//! # Protocol
//!
//! ```text
//! GATE_SUBJECT=<name>   which traversal to run
//! GATE_DEPTH=<n>        nesting depth, or sibling count for the `*_width` subjects
//! ```
//!
//! The stack bound is NOT passed as an environment variable: the parent installs it as
//! `RLIMIT_STACK` in the forked child before `exec`, which is exactly what `ulimit -s` does in
//! the shell harness of the audit's Appendix A. Exit status 0 means the subject survived;
//! anything else (including the `SIGSEGV` of a guard-page hit) means it did not.
//!
//! # ⚠ Teardown is a DIFFERENT traversal, and only one side of it needs help
//!
//! * `Proc` (the input) is already safe: the `language!` macro gives the AST family a pooled,
//!   *iterative* `Drop`. A plain `drop` is correct, and the fact that it is correct is part of
//!   what the gate asserts — if that ever became derived glue, every depth subject would grow a
//!   slope and the gate would go red without needing a new subject to notice.
//! * `Par` (the output) is not: it is a `prost` message tree with a **derived recursive**
//!   `Drop`, so every subject tears it down with f1r3node's own iterative
//!   `par_children::dismantle`, written for exactly this reason.
//!
//! ★ That `Par::drop` is one of the two traversals the lowering conversion does NOT fix. See
//! the gate's `THE_RESIDUE` note.

use std::sync::Arc;

use mettail_languages::rholang::{Int, List, Proc};
use mettail_rholang_runtime::rholang_ast::{lower_proc_in_env, BoundEnv};
use mettail_runtime::{Binder, Scope};
use models::rust::rholang::par_children::dismantle;

// ---------------------------------------------------------------------------
// term construction — ITERATIVE, so the builder itself is never the constraint
// ---------------------------------------------------------------------------

fn int(n: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(n)))
}

fn list(items: Vec<Proc>) -> Proc {
    Proc::CastList(Arc::new(List::ListLit(items)))
}

/// `[[[…[1]…]]]` with `depth` bracket levels — the reported shape.
fn nested_list(depth: usize) -> Proc {
    let mut p = int(1);
    for _ in 0..depth {
        p = list(vec![p]);
    }
    p
}

/// `[0, 1, …, width-1]` — the WIDTH counterpart of [`nested_list`].
fn wide_list(width: usize) -> Proc {
    let mut items = Vec::with_capacity(width);
    for i in 0..width {
        items.push(int(i as i64));
    }
    list(items)
}

/// `(((…(1 + 1)… + 1) + 1)` with `depth` additions: a chain through the BINARY arithmetic arms
/// rather than the collection arm, so a conversion that flattens only `CastList` cannot pass by
/// accident.
fn nested_add(depth: usize) -> Proc {
    let mut p = int(1);
    for _ in 0..depth {
        p = Proc::Add(Arc::new(p), Arc::new(int(1)));
    }
    p
}

/// `a | (b | (c | …))` with `depth` levels: the `PParInfix` arm, which recurses on BOTH
/// operands.
fn nested_par(depth: usize) -> Proc {
    let mut p = Proc::PZero;
    for _ in 0..depth {
        p = Proc::PParInfix(Arc::new(Proc::PZero), Arc::new(p));
    }
    p
}

/// `- - - … - 1` with `depth` signs: the `Int::NegInt` chain, which had its OWN Θ(depth) axis
/// through `lower_int_value` — a function that is not a member of the 87-strong lowering
/// component and would have survived a conversion scoped to it.
fn nested_neg(depth: usize) -> Proc {
    let mut n = Int::NumLit(1);
    for _ in 0..depth {
        n = Int::NegInt(Arc::new(n));
    }
    Proc::CastInt(Arc::new(n))
}

/// `1 matches (1 and (1 and (…)))` with `depth` connectives: the FORMULA compiler's own depth
/// axis, which reaches `lower_proc` only at its leaves.
fn nested_formula(depth: usize) -> Proc {
    let mut f = int(1);
    for _ in 0..depth {
        f = Proc::And(Arc::new(int(1)), Arc::new(f));
    }
    Proc::Matches(Arc::new(int(1)), Arc::new(f))
}

/// `new a in { new a in { … } }` with `depth` scopes: the binder-site axis, where each level
/// materialises a fresh `BoundEnv`.
fn nested_new(depth: usize) -> Proc {
    // ⚠ Built STRUCTURALLY, not parsed. An earlier revision built this ladder from source, which
    // put the parser — itself Θ(depth) at ~1,240 B/level (`parse_depth`) — inside the subject and
    // made its slope unattributable. A subject that measures two traversals measures neither.
    let mut p = int(1);
    for i in 0..depth {
        let binder = Binder(mettail_runtime::get_or_create_var(format!("c{i}")));
        p = Proc::PNew(Scope::new(vec![binder], Arc::new(p)));
    }
    p
}

/// The reported reproducer as a SOURCE string: `@"OUT"!([[[…[1]…]]])`.
fn reproducer_source(depth: usize) -> String {
    // 8 chars of frame + 2 chars per level + a digit; preallocate exactly.
    let mut s = String::with_capacity(2 * depth + 16);
    s.push_str("@\"OUT\"!(");
    for _ in 0..depth {
        s.push('[');
    }
    s.push('1');
    for _ in 0..depth {
        s.push(']');
    }
    s.push(')');
    s
}

// ---------------------------------------------------------------------------
// subjects
// ---------------------------------------------------------------------------

/// Lower `term`, then remove BOTH teardowns from the measurement.
///
/// ★ The `Proc` is `mem::forget`ed rather than dropped, and that is a MEASURED correction rather
/// than a convenience. The gate used to `drop(term)` here, on the stated grounds that the
/// `language!` macro gives the AST family a pooled, *iterative* `Drop` so a plain drop is O(1) in
/// stack. **That is true of a pure `Proc` chain and false of this one.** `nested_list` alternates
/// `Proc::CastList(Arc<List>)` with `List::ListLit(Vec<Proc>)`, and the teardown hops through
/// `List` on every level; bisected, `ast_drop` — which does nothing BUT build and drop — costs
/// **254 B/level**, while `lower_add` (a pure `Proc` chain) is flat. So the generated iterative
/// `Drop` does not cover the cross-type hop.
///
/// Leaving it in would have made every lowering subject read `max(lowering, AST drop)` and put a
/// slope on a converted traversal that does not have one. The teardown keeps its own subject
/// (`ast_drop`) and its own number instead, which is what "one subject, one traversal" means.
/// Leaking is correct here and nowhere else: the probe process exits immediately after.
fn lower(term: Proc) {
    let env = BoundEnv::new();
    let par = lower_proc_in_env(&term, &env).expect("stack_depth_probe: lowering failed");
    dismantle(par);
    std::mem::forget(term);
}

fn lower_depth_body(depth: usize) {
    lower(nested_list(depth));
}

fn lower_width_body(width: usize) {
    lower(wide_list(width));
}

fn lower_add_body(depth: usize) {
    lower(nested_add(depth));
}

fn lower_par_body(depth: usize) {
    lower(nested_par(depth));
}

fn lower_neg_body(depth: usize) {
    lower(nested_neg(depth));
}

fn lower_formula_body(depth: usize) {
    lower(nested_formula(depth));
}

fn lower_new_body(depth: usize) {
    lower(nested_new(depth));
}

/// The reported reproducer end-to-end: PARSE the source, then lower it. The only subject with
/// the parser in its path, on purpose.
fn reproducer_body(depth: usize) {
    let source = reproducer_source(depth);
    let term = Proc::parse_via_wpda(&source).expect("stack_depth_probe: reproducer did not parse");
    lower(term);
}

/// **M-6 — the PARSER's own constant.** It is not binding at the depths the lowering used to
/// fault at, but "not binding" and "not present" are different claims.
fn parse_depth_body(depth: usize) {
    let source = reproducer_source(depth);
    let term = Proc::parse_via_wpda(&source).expect("stack_depth_probe: reproducer did not parse");
    drop(term);
}

fn parse_width_body(width: usize) {
    let mut s = String::with_capacity(4 * width + 16);
    s.push_str("@\"OUT\"!([");
    for i in 0..width {
        if i > 0 {
            s.push_str(", ");
        }
        s.push_str(&i.to_string());
    }
    s.push_str("])");
    let term = Proc::parse_via_wpda(&s).expect("stack_depth_probe: wide source did not parse");
    drop(term);
}

/// ★ THE RESIDUE, subject 1: the derived recursive `Drop` of a deep `Par`.
///
/// Lower the term, then let the `Par` fall out of scope INSTEAD of dismantling it. Everything
/// else is `lower_depth`, so the difference between the two ladders is the teardown and nothing
/// else. This subject is expected to have a slope: it measures a traversal the lowering
/// conversion does not touch, and it exists so that "not fixed" is a NUMBER rather than a
/// footnote.
fn par_drop_body(depth: usize) {
    let term = nested_list(depth);
    let env = BoundEnv::new();
    let par = lower_proc_in_env(&term, &env).expect("stack_depth_probe: lowering failed");
    drop(par);
    drop(term);
}

/// ★ THE RESIDUE, subject 2: rendering the observation.
///
/// `rholang`'s main thread lowers, runs, and then RENDERS what it observed, through
/// `observation::render_par_text` — which decodes the `Par` back to a
/// `RuntimeObservationValue` and formats it, both recursively. Same construction as
/// [`par_drop_body`]: lower, then render, so the ladder isolates the renderer against
/// `lower_depth`'s.
fn render_body(depth: usize) {
    let term = nested_list(depth);
    let env = BoundEnv::new();
    let par = lower_proc_in_env(&term, &env).expect("stack_depth_probe: lowering failed");
    let rendered = mettail_rholang_runtime::observation::render_par_text(&par);
    // Consume the rendering so it cannot be optimized away.
    assert!(!rendered.is_empty(), "stack_depth_probe: the renderer produced nothing");
    dismantle(par);
    drop(term);
}

/// ★ THE RESIDUE, subject 3: the AST's own teardown across a CROSS-TYPE hop.
///
/// Build the deep `Proc` and drop it — no lowering at all, so the ladder is the teardown and the
/// (iterative, flat) builder. Bisected debug at 16 and 4,096: **254 B/level**, against **0** for
/// [`lower_leak_body`], which builds the identical term and forgets it. So the build is flat and
/// the DROP is not.
///
/// The `language!` macro's pooled iterative `Drop` covers a pure `Proc` chain — `lower_add`
/// (`Proc::Add(Arc<Proc>, Arc<Proc>)`) is flat — but `nested_list` alternates
/// `Proc::CastList(Arc<List>)` with `List::ListLit(Vec<Proc>)`, and the worklist evidently does
/// not follow the hop through `List`. That is a defect in the generated teardown, in
/// `macros/src/gen/`, NOT in the lowering, and it is recorded here so it is a number rather than
/// a suspicion.
fn ast_drop_body(depth: usize) {
    let term = nested_list(depth);
    drop(term);
}

/// ★ DISCRIMINATOR 2: lower, and LEAK both sides.
///
/// `std::mem::forget` on the `Par` and on the `Proc` removes every teardown traversal from the
/// ladder, so what is left is the lowering and nothing else. This is the subject that says
/// whether the conversion did its job, as distinct from whether the surrounding harness is
/// clean. Leaking is correct here and nowhere else: the process exits immediately after.
fn lower_leak_body(depth: usize) {
    let term = nested_list(depth);
    let env = BoundEnv::new();
    let par = lower_proc_in_env(&term, &env).expect("stack_depth_probe: lowering failed");
    std::mem::forget(par);
    std::mem::forget(term);
}

/// ★ DISCRIMINATOR: build the `new` ladder and LEAK it — no lowering.
///
/// `Scope::new` closes the body over its binder, and moniker's `close_term` walks the whole body.
/// So the BUILDER of this ladder may itself be Θ(depth), and a `lower_new` slope would then be
/// unattributable. This subject separates the two.
fn new_build_body(depth: usize) {
    let term = nested_new(depth);
    std::mem::forget(term);
}

// ---------------------------------------------------------------------------
// ★★ THE GENERATED TRAIT DRIVERS — nine `*_iterative` engines, eight of which had
// NO subject here at all.
//
// `macros/src/gen/` emits nine work-stack drivers over the AST family:
// `iterative_cmp` (PartialEq/Eq/PartialOrd/Ord), `iterative_hash` (Hash),
// `iterative_drop` (Drop), `debug` (Debug), `display` (Display), plus the inherent
// `semantic_hash`, `subst`, `normalize` and `match_pattern`. Only `Drop` was gated
// (as `ast_drop`) — and it is the one that turned out NOT to be flat, at 254 B/level,
// because `nested_list` alternates `Proc::CastList(Arc<List>)` with
// `List::ListLit(Vec<Proc>)` and the worklist does not follow that cross-type hop.
//
// ⚠ So "generated" must not be read as "verified flat", and the remaining eight were
// UNMEASURED rather than known-good. These subjects close that gap.
//
// ★ EVERY subject here builds on `nested_list` — deliberately the SAME cross-type shape
// that exposed the `ast_drop` defect — and `mem::forget`s its terms, so the ladder is the
// driver under test and never `ast_drop`'s own slope. One subject, one traversal.
// ---------------------------------------------------------------------------

/// [`nested_list`] with the LEAF integer chosen, so two ladders can be made to differ at
/// the deepest point and nowhere else.
fn nested_list_leaf(depth: usize, leaf: i64) -> Proc {
    let mut p = int(leaf);
    for _ in 0..depth {
        p = list(vec![p]);
    }
    p
}

/// [`nested_list`] whose leaf is a FREE VARIABLE, so a substitution must walk the whole
/// spine to reach the only thing it will rewrite.
fn nested_list_var(depth: usize, name: &str) -> Proc {
    let fv = mettail_runtime::get_or_create_var(name.to_string());
    let mut p = Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv)));
    for _ in 0..depth {
        p = list(vec![p]);
    }
    p
}

/// `PartialEq` — `iterative_cmp.rs`.
///
/// ⚠ ANTI-VACUITY: `eq` short-circuits at the first UNEQUAL field, so the twins must compare
/// **equal** or the ladder measures one frame. They are built INDEPENDENTLY rather than cloned,
/// because `Clone` is `Arc::clone` here and a cloned twin would share every child pointer — an
/// impl that opened with a pointer-equality fast path would then return without descending.
fn ast_eq_body(depth: usize) {
    let a = nested_list(depth);
    let b = nested_list(depth);
    assert!(a == b, "stack_depth_probe: ast_eq twins must be EQUAL or the walk short-circuits");
    std::mem::forget(a);
    std::mem::forget(b);
}

/// `Ord::cmp` — `iterative_cmp.rs`.
///
/// ⚠ ANTI-VACUITY: `cmp` short-circuits at the first unequal field, so the twins differ ONLY at
/// the leaf and the comparison must descend the whole spine to decide.
fn ast_cmp_body(depth: usize) {
    let a = nested_list_leaf(depth, 1);
    let b = nested_list_leaf(depth, 2);
    assert!(a < b, "stack_depth_probe: ast_cmp twins must differ at the LEAF, a < b");
    std::mem::forget(a);
    std::mem::forget(b);
}

/// `Hash` — `iterative_hash.rs`.
///
/// ⚠ ANTI-VACUITY: hashing cannot short-circuit, but it is invisible — a driver that hashed only
/// the root would still "work". Two different leaves must therefore produce two different digests.
fn ast_hash_body(depth: usize) {
    use std::hash::{Hash, Hasher};
    let hash_of = |p: &Proc| {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        p.hash(&mut h);
        h.finish()
    };
    let a = nested_list_leaf(depth, 1);
    let b = nested_list_leaf(depth, 2);
    assert_ne!(
        hash_of(&a),
        hash_of(&b),
        "stack_depth_probe: ast_hash must reach the LEAF — two leaves gave one digest"
    );
    std::mem::forget(a);
    std::mem::forget(b);
}

/// `Debug` — `debug.rs`.
///
/// ⚠ ANTI-VACUITY: the rendering must GROW with depth, or the formatter stopped early.
fn ast_debug_body(depth: usize) {
    let a = nested_list(depth);
    let rendered = format!("{a:?}");
    assert!(
        rendered.len() > depth,
        "stack_depth_probe: ast_debug rendered {} bytes at depth {depth} — it stopped early",
        rendered.len()
    );
    std::mem::forget(a);
}

/// `Display` — `display.rs`.
///
/// ⚠ ANTI-VACUITY: same rule as [`ast_debug_body`].
fn ast_display_body(depth: usize) {
    let a = nested_list(depth);
    let rendered = format!("{a}");
    assert!(
        rendered.len() > depth,
        "stack_depth_probe: ast_display rendered {} bytes at depth {depth} — it stopped early",
        rendered.len()
    );
    std::mem::forget(a);
}

/// $`\alpha`$-canonical identity — `semantic_hash.rs`.
///
/// ⚠ ANTI-VACUITY: as for `ast_hash`, two leaves must give two digests.
fn ast_semantic_hash_body(depth: usize) {
    use std::hash::Hasher;
    let hash_of = |p: &Proc| {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        p.semantic_hash(&mut h);
        h.finish()
    };
    let a = nested_list_leaf(depth, 1);
    let b = nested_list_leaf(depth, 2);
    assert_ne!(
        hash_of(&a),
        hash_of(&b),
        "stack_depth_probe: ast_semantic_hash must reach the LEAF"
    );
    std::mem::forget(a);
    std::mem::forget(b);
}

/// Capture-avoiding substitution — `subst.rs`.
///
/// ⚠ ANTI-VACUITY: the variable sits at the LEAF, so the substitution must traverse the entire
/// spine to find it, and the result must actually differ from the input.
fn ast_subst_body(depth: usize) {
    let term = nested_list_var(depth, "probe_subst_x");
    let fv = mettail_runtime::get_or_create_var("probe_subst_x".to_string());
    let replaced = term.substitute(&fv, &int(7));
    assert!(
        replaced != term,
        "stack_depth_probe: ast_subst did not reach the LEAF variable"
    );
    std::mem::forget(term);
    std::mem::forget(replaced);
}

/// Collection canonicalisation — `normalize.rs`.
///
/// ⚠ ANTI-VACUITY: normalising a canonical term is the identity, so the assertion is that the
/// result still carries the depth it was given — a driver that returned a truncated term would
/// otherwise read as flat and correct.
fn ast_normalize_body(depth: usize) {
    let term = nested_list(depth);
    let normalized = term.normalize();
    assert!(
        normalized == term,
        "stack_depth_probe: ast_normalize is not the identity on a canonical term"
    );
    std::mem::forget(term);
    std::mem::forget(normalized);
}

/// Pattern matching — `match_pattern.rs`.
///
/// ⚠ ANTI-VACUITY: the pattern must MATCH, or the walk stops at the first mismatch. A term is
/// matched against an independently-built structural twin of itself.
fn ast_match_pattern_body(depth: usize) {
    let term = nested_list(depth);
    let pattern = nested_list(depth);
    assert!(
        term.match_pattern(&pattern).is_some(),
        "stack_depth_probe: ast_match_pattern must MATCH or the walk short-circuits"
    );
    std::mem::forget(term);
    std::mem::forget(pattern);
}

/// ★ THE CONTROL for the eight subjects above: build the twin pair and forget it, running NO
/// driver at all. Whatever slope the builders and the `Arc` bumps carry is in this ladder too,
/// so a driver's slope is `subject − build_twins` and never the harness's own cost.
fn build_twins_body(depth: usize) {
    let a = nested_list_leaf(depth, 1);
    let b = nested_list_leaf(depth, 2);
    std::mem::forget(a);
    std::mem::forget(b);
}

// ---------------------------------------------------------------------------
// ★★ THE MECHANISM TEST — the same eight drivers on a shape with NO cross-type hop.
//
// The `*_add` twins below are identical in every respect except the SHAPE they walk:
// `nested_add` is `Proc::Add(Arc<Proc>, Arc<Proc>)`, a pure single-type chain, where
// `nested_list` alternates `Proc::CastList(Arc<List>)` with `List::ListLit(Vec<Proc>)`.
//
// The hypothesis under test is the one `ast_drop`'s note states: the generated work stacks
// are typed per category, and a driver does not follow an edge that leaves its own type.
// It predicts a SHARP result — every `*_add` twin flat, every `nested_list` original sloped.
// Anything else refutes it, and a partial result localises the defect further.
// ---------------------------------------------------------------------------

/// [`nested_add`] with the LEAF chosen, for the comparison subjects' anti-vacuity.
fn nested_add_leaf(depth: usize, leaf: i64) -> Proc {
    let mut p = int(leaf);
    for _ in 0..depth {
        p = Proc::Add(Arc::new(p), Arc::new(int(1)));
    }
    p
}

/// [`nested_add`] whose leaf is a free variable, for `ast_subst_add`.
fn nested_add_var(depth: usize, name: &str) -> Proc {
    let fv = mettail_runtime::get_or_create_var(name.to_string());
    let mut p = Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv)));
    for _ in 0..depth {
        p = Proc::Add(Arc::new(p), Arc::new(int(1)));
    }
    p
}

fn ast_eq_add_body(depth: usize) {
    let a = nested_add(depth);
    let b = nested_add(depth);
    assert!(a == b, "stack_depth_probe: ast_eq_add twins must be EQUAL");
    std::mem::forget(a);
    std::mem::forget(b);
}

fn ast_cmp_add_body(depth: usize) {
    let a = nested_add_leaf(depth, 1);
    let b = nested_add_leaf(depth, 2);
    assert!(a != b, "stack_depth_probe: ast_cmp_add twins must differ at the LEAF");
    let _ = a.cmp(&b);
    std::mem::forget(a);
    std::mem::forget(b);
}

fn ast_hash_add_body(depth: usize) {
    use std::hash::{Hash, Hasher};
    let hash_of = |p: &Proc| {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        p.hash(&mut h);
        h.finish()
    };
    let a = nested_add_leaf(depth, 1);
    let b = nested_add_leaf(depth, 2);
    assert_ne!(hash_of(&a), hash_of(&b), "stack_depth_probe: ast_hash_add must reach the LEAF");
    std::mem::forget(a);
    std::mem::forget(b);
}

fn ast_debug_add_body(depth: usize) {
    let a = nested_add(depth);
    let rendered = format!("{a:?}");
    assert!(rendered.len() > depth, "stack_depth_probe: ast_debug_add stopped early");
    std::mem::forget(a);
}

fn ast_display_add_body(depth: usize) {
    let a = nested_add(depth);
    let rendered = format!("{a}");
    assert!(rendered.len() > depth, "stack_depth_probe: ast_display_add stopped early");
    std::mem::forget(a);
}

fn ast_semantic_hash_add_body(depth: usize) {
    use std::hash::Hasher;
    let hash_of = |p: &Proc| {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        p.semantic_hash(&mut h);
        h.finish()
    };
    let a = nested_add_leaf(depth, 1);
    let b = nested_add_leaf(depth, 2);
    assert_ne!(
        hash_of(&a),
        hash_of(&b),
        "stack_depth_probe: ast_semantic_hash_add must reach the LEAF"
    );
    std::mem::forget(a);
    std::mem::forget(b);
}

fn ast_subst_add_body(depth: usize) {
    let term = nested_add_var(depth, "probe_subst_y");
    let fv = mettail_runtime::get_or_create_var("probe_subst_y".to_string());
    let replaced = term.substitute(&fv, &int(7));
    assert!(replaced != term, "stack_depth_probe: ast_subst_add did not reach the LEAF");
    std::mem::forget(term);
    std::mem::forget(replaced);
}

fn ast_normalize_add_body(depth: usize) {
    let term = nested_add(depth);
    let normalized = term.normalize();
    assert!(normalized == term, "stack_depth_probe: ast_normalize_add is not the identity");
    std::mem::forget(term);
    std::mem::forget(normalized);
}

fn ast_match_pattern_add_body(depth: usize) {
    let term = nested_add(depth);
    let pattern = nested_add(depth);
    assert!(
        term.match_pattern(&pattern).is_some(),
        "stack_depth_probe: ast_match_pattern_add must MATCH"
    );
    std::mem::forget(term);
    std::mem::forget(pattern);
}

/// ★★ `Clone` — and it is NOT a generated driver, which is the whole point.
///
/// `iterative_clone.rs` existed and was DELETED (`651499e2`). The ARC refactor
/// (`9c55d81d`) changed recursive AST children from `Box<Cat>` to `Arc<Cat>`, so the derived
/// `Clone` is `Arc::clone` per child — a refcount increment that stops at the `Arc` boundary
/// and never descends the subtree. This subject is the executable form of that claim: it
/// clones a deep term on the ALTERNATING ladder, where every other driver is sloped.
///
/// ⚠ ANTI-VACUITY: the clone must be OBSERVED, or the optimiser may drop it entirely. Its
/// root discriminant is compared and both terms are then forgotten.
fn ast_clone_body(depth: usize) {
    let a = nested_list(depth);
    let b = a.clone();
    assert!(
        std::mem::discriminant(&a) == std::mem::discriminant(&b),
        "stack_depth_probe: ast_clone produced a different variant"
    );
    std::mem::forget(a);
    std::mem::forget(b);
}

/// `Clone` on the pure chain, for the 2x2.
fn ast_clone_add_body(depth: usize) {
    let a = nested_add(depth);
    let b = a.clone();
    assert!(
        std::mem::discriminant(&a) == std::mem::discriminant(&b),
        "stack_depth_probe: ast_clone_add produced a different variant"
    );
    std::mem::forget(a);
    std::mem::forget(b);
}

/// ★ THE ALLOCATION control for [`ast_clone_body`]: build the term and forget it, WITHOUT
/// cloning. Under DHAT the difference between this and `ast_clone` is exactly what one clone
/// of a depth-N term allocates, so the O(1)-vs-O(N) question is answered by subtraction
/// rather than by reading the type definition.
fn build_one_body(depth: usize) {
    let a = nested_list(depth);
    std::mem::forget(a);
}

/// The `*_add` control, matching [`build_twins_body`].
fn build_twins_add_body(depth: usize) {
    let a = nested_add_leaf(depth, 1);
    let b = nested_add_leaf(depth, 2);
    std::mem::forget(a);
    std::mem::forget(b);
}

/// The `*_add` teardown, matching `ast_drop`. `lower_add` is already known flat, so this says
/// whether the pure-`Proc` chain is flat under the generated `Drop` as the note claims.
fn ast_drop_add_body(depth: usize) {
    let term = nested_add(depth);
    drop(term);
}

/// Names the subject a child should run. Kept in one place so the parent and the child cannot
/// drift; the parent names subjects by the same strings.
fn subject(name: &str) -> fn(usize) {
    match name {
        // -------- depth axis: the converted lowering --------
        "lower_depth" => lower_depth_body,
        "lower_add" => lower_add_body,
        "lower_par" => lower_par_body,
        "lower_neg" => lower_neg_body,
        "lower_formula" => lower_formula_body,
        "lower_new" => lower_new_body,
        "reproducer" => reproducer_body,
        "lower_leak" => lower_leak_body,
        // -------- the GENERATED TRAIT DRIVERS (eight that had no subject) --------
        "ast_eq" => ast_eq_body,
        "ast_cmp" => ast_cmp_body,
        "ast_hash" => ast_hash_body,
        "ast_debug" => ast_debug_body,
        "ast_display" => ast_display_body,
        "ast_semantic_hash" => ast_semantic_hash_body,
        "ast_subst" => ast_subst_body,
        "ast_normalize" => ast_normalize_body,
        "ast_match_pattern" => ast_match_pattern_body,
        // -------- the MECHANISM TEST: same drivers, no cross-type hop --------
        "ast_eq_add" => ast_eq_add_body,
        "ast_cmp_add" => ast_cmp_add_body,
        "ast_hash_add" => ast_hash_add_body,
        "ast_debug_add" => ast_debug_add_body,
        "ast_display_add" => ast_display_add_body,
        "ast_semantic_hash_add" => ast_semantic_hash_add_body,
        "ast_subst_add" => ast_subst_add_body,
        "ast_normalize_add" => ast_normalize_add_body,
        "ast_match_pattern_add" => ast_match_pattern_add_body,
        // -------- discriminators --------
        // -------- ★ Clone: stack-safe by REPRESENTATION, not by a driver --------
        "ast_clone" => ast_clone_body,
        "ast_clone_add" => ast_clone_add_body,
        "build_one" => build_one_body,
        // -------- discriminators --------
        "ast_drop" => ast_drop_body,
        "ast_drop_add" => ast_drop_add_body,
        "build_twins" => build_twins_body,
        "build_twins_add" => build_twins_add_body,
        "new_build" => new_build_body,
        // -------- depth axis: NOT converted, measured anyway --------
        "parse_depth" => parse_depth_body,
        "par_drop" => par_drop_body,
        "render" => render_body,
        // -------- width axis --------
        "lower_width" => lower_width_body,
        "parse_width" => parse_width_body,
        other => panic!("stack_depth_probe: unknown GATE_SUBJECT={other:?}"),
    }
}

fn main() {
    let name = std::env::var("GATE_SUBJECT").expect("stack_depth_probe: GATE_SUBJECT must be set");
    let depth: usize = std::env::var("GATE_DEPTH")
        .expect("stack_depth_probe: GATE_DEPTH must accompany GATE_SUBJECT")
        .parse()
        .expect("stack_depth_probe: GATE_DEPTH must be an integer");
    // ★ On the MAIN thread. No `thread::Builder`, no `stack_size`, no `RUST_MIN_STACK`: the
    // only thing bounding this call is the `RLIMIT_STACK` the parent installed before `exec`.
    subject(&name)(depth);
}
