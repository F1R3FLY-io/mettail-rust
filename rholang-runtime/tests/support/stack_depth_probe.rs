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
//! # ⚠ Teardown is a DIFFERENT traversal
//!
//! * `Proc` (the input) is already safe: the `language!` macro gives the AST family a pooled,
//!   *iterative* `Drop`. A plain `drop` is correct, and the fact that it is correct is part of
//!   what the gate asserts — if that ever became derived glue, every depth subject would grow a
//!   slope and the gate would go red without needing a new subject to notice.
//! * `Par` (the output) is safe too: f1r3node's schema generator emits recursive trait
//!   implementations, including `Drop`, over an explicit PDA. Most subjects still use
//!   `par_children::dismantle` to isolate the traversal they intend to measure; `par_drop`
//!   independently gates the production destructor.
//!
//! ★ Keeping teardown as a separate subject is what prevents a regression there from being
//! misattributed to lowering.

use std::sync::Arc;

use mettail_languages::rholang::{
    BigRat, Int, List, Name, Proc, RholangEnv, RholangLanguage, RholangTerm, RholangTermInner,
};
use mettail_rholang_codegen::FltReflect;
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

/// `- - - … - leaf` as a bare `Int`, with `depth` signs and the LEAF chosen.
///
/// ★ [`nested_neg`] wraps the same chain in a `Proc::CastInt` because its consumer is the
/// LOWERING. `try_eval` is a method on `Int` (`eval` is generated only for categories with a
/// `native_type`, and `Proc` has none), so its ladder must hand over the `Int` itself.
///
/// The leaf is a parameter for the same reason `nested_list_leaf`'s is: two chains that differ
/// ONLY at the deepest point force any evaluator to reach the bottom before it can tell them
/// apart. See [`ast_try_eval_body`]'s anti-vacuity.
fn nested_neg_int_leaf(depth: usize, leaf: i64) -> Int {
    let mut n = Int::NumLit(leaf);
    for _ in 0..depth {
        n = Int::NegInt(Arc::new(n));
    }
    n
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

/// **M-6 — the parser path in isolation.** The historical path grew after its large fixed
/// intercept; current generated semantic-hash and collection drivers make this fixture flat.
/// It retains an independent wide-ladder gate so that state cannot regress silently.
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

/// The generated production `Drop` of a deep `Par`.
///
/// Lower the term, then let the `Par` fall out of scope INSTEAD of dismantling it. Everything
/// else is `lower_depth`, so the difference between the two ladders is the teardown and nothing
/// else. The schema generator now implements this traversal with an explicit PDA; this subject
/// proves its native-stack requirement remains independent of nesting depth.
fn par_drop_body(depth: usize) {
    let term = nested_list(depth);
    let env = BoundEnv::new();
    let par = lower_proc_in_env(&term, &env).expect("stack_depth_probe: lowering failed");
    drop(par);
    drop(term);
}

/// Observation decoding and rendering, isolated from both recursive teardowns.
///
/// `rholang`'s main thread lowers, runs, and then RENDERS what it observed, through
/// `observation::render_par_text` — which decodes the `Par` back to a
/// `RuntimeObservationValue` and formats it. Same construction as [`lower_depth_body`]: lower,
/// render, dismantle the `Par`, and forget the generated AST. Forgetting the input is
/// deliberate: `nested_list`'s cross-category `Proc`/`List` teardown has its own probe
/// (`ast_drop`), and including it here would make this subject measure two unrelated traversals.
fn render_body(depth: usize) {
    let term = nested_list(depth);
    let env = BoundEnv::new();
    let par = lower_proc_in_env(&term, &env).expect("stack_depth_probe: lowering failed");
    let rendered = mettail_rholang_runtime::observation::render_par_text(&par);
    // Consume the rendering so it cannot be optimized away.
    assert!(!rendered.is_empty(), "stack_depth_probe: the renderer produced nothing");
    dismantle(par);
    std::mem::forget(term);
}

/// Historical AST teardown residue, retained as a flat regression subject.
///
/// Build the deep `Proc` and drop it — no lowering at all, so the ladder is the teardown and the
/// (iterative, flat) builder. Bisected debug at 16 and 4,096: **254 B/level**, against **0** for
/// [`lower_leak_body`], which builds the identical term and forgets it. In that build the slope
/// belonged to `Drop`, not the builder.
///
/// The `language!` macro's pooled iterative `Drop` covers a pure `Proc` chain — `lower_add`
/// (`Proc::Add(Arc<Proc>, Arc<Proc>)`) is flat — but `nested_list` alternates
/// `Proc::CastList(Arc<List>)` with `List::ListLit(Vec<Proc>)`, and somewhere across that
/// alternation the worklist is abandoned. That is a defect in the generated teardown, in
/// `macros/src/gen/`, NOT in the lowering, and it is recorded here so it is a number rather than
/// a suspicion. The collection-element driver conversion subsequently closed that escape.
///
/// ★★ **CORRECTION (2026-07-29).** This note used to say the worklist *"does not follow the hop
/// through `List`"* — i.e. that a driver abandons its work stack when an edge leaves its own
/// category. **That explanation is REFUTED.** The cross-category hop is handled correctly; the
/// escape is one level further down, at the COLLECTION-ELEMENT boundary. Read
/// `target/generated/rholang/iterative_cmp.rs`:
///
/// ```text
/// :2174  (Proc::CastList(ref l0), Proc::CastList(ref r0)) => {
/// :2175      stack.push(CmpTask::CmpList(&**l0 as *const _, &**r0 as *const _));   ← the HOP,
/// :2176  }                                                                            PUSHED
///
/// :11128 (List::ListLit(a), List::ListLit(b)) => {
/// :11129     if a != b {                       ← `a`,`b` are `&Vec<Proc>`; `!=` is PartialEq,
/// :11130         return false;                    which re-enters the driver per element by
/// :11131     }                                    HOST RECURSION. THE ESCAPE.
/// ```
///
/// The `Ord` half does the same thing with `let ord = a.cmp(b);` at `:34250`. So the shape of the
/// defect is `Category → Vec<Elem> → Elem`: iterative down to the collection, then a WHOLE-VALUE
/// delegation to a trait method that has no access to the work stack.
///
/// ★ And `display.rs` proves flat is achievable on the identical shape — `:14827` pushes one
/// `DisplayTask::DisplayProc` per element instead of delegating, and `ast_display` measures
/// **0 B/level in both profiles**. It is the model the rewrite should copy, not a lucky case.
/// The generated `Drop` now follows that model, and the permanent gate requires `ast_drop` to
/// remain flat across the wide ladder.
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
// ★★ THE GENERATED TRAIT DRIVERS — historical census and current closure probes.
//
// `macros/src/gen/` emits nine work-stack drivers over the AST family:
// `iterative_cmp` (PartialEq/Eq/PartialOrd/Ord), `iterative_hash` (Hash),
// `iterative_drop` (Drop), `debug` (Debug), `display` (Display), plus the inherent
// `semantic_hash`, `subst`, `normalize` and `match_pattern`. Initially only `Drop` was gated
// (as `ast_drop`) — and it was the one that turned out NOT to be flat, at 254 B/level,
// because `nested_list` alternates `Proc::CastList(Arc<List>)` with
// `List::ListLit(Vec<Proc>)` and the worklist is abandoned somewhere in that alternation.
//
// ★★ ...and there is a TENTH, `term_depth`, which has no work stack at all. See
// `ast_term_depth_body`. The count of nine was itself the kind of hand-maintained figure this
// gate exists to distrust. The derived census and per-driver subjects below now cover the
// generated family, and all production rows are required to be flat.
//
// ⚠ WHERE the worklist is abandoned was long recorded WRONGLY as "the cross-type hop". It is
// the COLLECTION-ELEMENT boundary; see the correction on `ast_drop_body` for the generated
// lines that show the hop being pushed and the elements being delegated.
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
    assert!(
        a == b,
        "stack_depth_probe: ast_eq twins must be EQUAL or the walk short-circuits"
    );
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
    assert!(replaced != term, "stack_depth_probe: ast_subst did not reach the LEAF variable");
    std::mem::forget(term);
    std::mem::forget(replaced);
}

/// Environment substitution through the same generated substitution PDA as
/// [`ast_subst_body`].
///
/// The old generated-file census classified `env_subst.rs` as host-recursive because a
/// textual self-call detector saw every host category's fixed-point wrapper call its own
/// `subst_by_name_*` method. The method itself seeds `SUBST_TASK_POOL` and enters
/// `subst_iterative`; it does not recursively descend the term. This subject exercises the
/// environment-specific `SubstOp::EnvProc` arm so that correction is measured rather than
/// inferred from the neighbouring eager-substitution subject.
fn ast_env_subst_body(depth: usize) {
    let term = nested_list_var(depth, "probe_env_subst_x");
    let mut env = RholangEnv::new();
    env.proc.set("probe_env_subst_x".to_owned(), int(7));
    let replaced = term.substitute_env_no_normalize(&env);
    let expected_depth = u32::try_from(depth)
        .expect("stack_depth_probe: requested depth does not fit the generated u32 depth API");
    let actual_depth = replaced.term_depth();
    assert!(
        actual_depth >= expected_depth,
        "stack_depth_probe: ast_env_subst truncated the depth-{depth} spine to depth {actual_depth}"
    );
    assert!(
        replaced.is_ground(),
        "stack_depth_probe: ast_env_subst did not reach and replace the leaf variable"
    );
    std::mem::forget(term);
    std::mem::forget(replaced);
}

/// The generated parse-alternative filter on a pure same-category `Proc::Add` spine.
///
/// Every `Add` must be traversed before the deepest auto-injection-equivalent
/// `Proc::POutputEmpty` wrapper can set the flag that makes the result `true`. A shallow or
/// truncated traversal therefore answers `false`; the groundness conjunct independently drains
/// the same spine through the generated ground-check PDA.
fn ast_parse_alt_filter_body(depth: usize) {
    // `CastInt` is a normal Rholang rule, not one of the generated filter's
    // auto-injection-equivalent wrappers. Seed the leftmost leaf with a rule
    // that is actually in that set, then hide it behind the full Add spine.
    let mut term = Proc::POutputEmpty(Arc::new(Name::NQuoteNil));
    for _ in 0..depth {
        term = Proc::Add(Arc::new(term), Arc::new(int(1)));
    }
    assert!(
        term.is_uniformly_auto_injected(),
        "stack_depth_probe: ast_parse_alt_filter did not reach the deepest auto-injected wrapper"
    );
    std::mem::forget(term);
}

/// Both generated variable-inference visitors on a same-category spine whose only matching
/// variable is the deepest leaf. Returning `Some` is the anti-vacuity witness that neither
/// visitor skipped or truncated the traversal.
fn ast_var_inference_body(depth: usize) {
    const NAME: &str = "probe_var_inference_x";
    let term = nested_add_var(depth, NAME);
    assert!(
        term.infer_var_category(NAME).is_some(),
        "stack_depth_probe: infer_var_category did not reach the depth-{depth} leaf"
    );
    assert!(
        term.infer_var_type(NAME).is_some(),
        "stack_depth_probe: infer_var_type did not reach the depth-{depth} leaf"
    );
    std::mem::forget(term);
}

/// The generated Language-level all-variable collector. Its recursive predecessor walked the
/// same-category tree separately from `infer_var_type`; this subject therefore cannot borrow the
/// inference PDA's evidence. The deepest free variable must appear in the returned inventory.
fn ast_language_var_collect_body(depth: usize) {
    const NAME: &str = "probe_language_collect_x";
    let term = RholangTerm(RholangTermInner::Proc(nested_add_var(depth, NAME)));
    let variables = RholangLanguage.infer_var_types(&term);
    assert!(
        variables.iter().any(|info| info.name == NAME),
        "stack_depth_probe: Language variable collector did not reach the depth-{depth} leaf"
    );
    std::mem::forget(term);
}

/// Generated `Term → GroundTerm` reflection, including the mutually-recursive cross-category
/// calls used by match/drive and the public FLT bridge. The parser has its own independent flat
/// subject; this one chooses the structurally reflectable `Add` spine and verifies the reflected
/// result reaches the deepest literal before its stack-safe lifecycle dismantles it.
fn ast_flt_reflect_body(depth: usize) {
    let term = RholangTerm(RholangTermInner::Proc(nested_add(depth)));
    let reflected = RholangLanguage
        .reflect_flt_term(&term)
        .expect("stack_depth_probe: generated FLT reflector rejected the Add spine");
    let mut pending = vec![(&reflected, 0usize)];
    let mut measured = 0usize;
    while let Some((term, level)) = pending.pop() {
        measured = measured.max(level);
        pending.extend(term.children.iter().map(|child| (child, level + 1)));
    }
    assert!(
        measured >= depth,
        "stack_depth_probe: generated FLT reflection stopped at {measured}, before depth {depth}"
    );
    drop(reflected);
    std::mem::forget(term);
}

/// Generated typed Dovetail lowering AND derivation reconstruction — the final uncovered
/// mutually-recursive generated SCC in the artifact census.
///
/// The fixture deliberately uses the pure structural `Proc::Add` ladder. Unlike a `ListLit`
/// category literal (which is one opaque Dovetail leaf), every `Add` level becomes an e-node and
/// must be visited by typed lowering and typed reconstruction. The generated diagnostic seam
/// skips saturation so rewrite complexity cannot mask the traversal's stack shape.
fn ast_dovetail_report_body(depth: usize) {
    let term = RholangTerm(RholangTermInner::Proc(nested_add(depth)));
    let normal = RholangLanguage::__mettail_dovetail_structural_roundtrip(&term, 1_000_000)
        .expect("stack_depth_probe: Dovetail structural roundtrip failed");
    let measured = match normal.as_any().downcast_ref::<RholangTerm>().map(|t| &t.0) {
        Some(RholangTermInner::Proc(proc)) => proc.term_depth() as usize,
        other => panic!(
            "stack_depth_probe: Dovetail structural roundtrip returned a non-Proc root: {other:?}"
        ),
    };
    assert!(
        measured >= depth,
        "stack_depth_probe: Dovetail reconstruction stopped at {measured}, before depth {depth}",
    );
    // Teardown has its own subjects. This row isolates lowering + extraction + reconstruction.
    std::mem::forget(term);
    std::mem::forget(normal);
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

/// ★★ THE TENTH DRIVER — `term_depth()`, and it is not a worklist driver at all.
///
/// The section header above says `macros/src/gen/` emits NINE work-stack drivers. That count was
/// short by one, and the tenth is the worst of them: `macros/src/gen/term_ops/depth.rs` emits
/// `term_depth` as plain HOST RECURSION with no stack, no worklist and no pooling —
///
/// ```text
/// VariantKind::Regular            => 1 + f0.term_depth()
/// VariantKind::CollectionLiteral  => 1 + coll.iter().map(|x| x.term_depth()).max().unwrap_or(0)
/// VariantKind::Binder             => 1 + scope.inner().unsafe_body.term_depth()
/// ```
///
/// — and it is compiled into every language (`macros/src/gen/mod.rs:161`, `:241`), so it is live
/// code rather than a dormant emitter. It was found while looking for an eq-free anti-vacuity
/// check for [`ast_subst_noassert_body`]: `term_depth()` is the obvious instrument for
/// *"the result still carries the depth it was given"*, and reading it before using it is the
/// only reason the confound control is not measuring a fresh Θ(depth) traversal of its own.
///
/// ⚠ It differs from the other nine in a way that matters for the rewrite: the nine escape a
/// worklist they DO have, at one boundary (the collection element). This one has no worklist to
/// escape, so it is not a boundary fix — it is a conversion.
///
/// ★ Its saving grace, established by call-site search and stated because a severity claim needs
/// it: **`term_depth()` has no caller.** Outside the generator that emits it and its own
/// recursive self-calls, nothing in the workspace invokes it — the A-RT05 post-fixpoint
/// convergence check it was written for does not call it either. So it is a latent trap for the
/// next caller rather than a live exposure, and it is measured here so that "latent" is a number.
///
/// ⚠⚠ **BOTH HALVES OF THAT PARAGRAPH ARE NOW FALSE, and it is kept as a correction.**
///
/// * **It HAS callers.** `target/generated/rholang/dovetail_report.rs` invokes it at 40 sites —
///   `__max_depth = __max_depth.max(value.term_depth())`, one per `RholangTermInner` arm inside
///   the Dovetail e-graph build — emitted by
///   `macros/src/gen/runtime/dovetail_report/typed_report.rs:1845/1933/2659/2677`. The "nothing
///   invokes it" reading came from grepping the SOURCE tree, where the only occurrences are the
///   emitter's own `quote!` fragments; the call sites exist only after expansion. A generated
///   method's callers can be generated too, and a source grep cannot see them.
/// * **It is no longer sloped.** #162 converted it to an explicit `(node, dist)` worklist with one
///   running maximum. Measured on this build: 3,408 -> -1 B/level (debug), 207 -> 0 (release), and
///   the `*_add` twin 2,367 -> 1.
///
/// The subject stays, because a converted driver needs watching at least as much as an
/// unconverted one.
///
/// ⚠ ANTI-VACUITY: the measured depth must GROW with the ladder, or the walk stopped early. The
/// bound is `>= depth` rather than the exact `2·depth + 1` the arm arithmetic predicts, so the
/// assertion cannot go red for a change in how a level is COUNTED while still failing for any
/// walk that does not reach the bottom.
fn ast_term_depth_body(depth: usize) {
    let a = nested_list(depth);
    let measured = a.term_depth();
    assert!(
        measured as usize >= depth,
        "stack_depth_probe: ast_term_depth measured {measured} on a depth-{depth} spine — it \
         stopped early"
    );
    std::mem::forget(a);
}

/// ★★ **`is_ground` — the ELEVENTH driver, and the subject that did not exist.**
///
/// `macros/src/gen/term_ops/ground.rs` emitted bare host recursion (`f0.is_ground()`,
/// `coll.iter().all(|x| x.is_ground())`), the same shape `term_depth` had before #162. It is
/// compiled into every language and it has a generated caller at
/// `target/generated/rholang/parse_alt_filter.rs`.
///
/// ⚠★★ **Why this subject is the actual fix for #189, and the conversion only the easy half.**
/// `stack_depth_gate`'s `the_sloped_driver_set_is_exactly_the_declared_one` totals in BOTH
/// directions over a universe it enumerates from [`SUBJECTS`] at run time — declared-but-absent
/// and present-but-undeclared both fail. That is a strong instrument and it was completely blind
/// here: a driver with **no subject** is not a row in the table to be totalled. A bidirectional
/// totality gate over a universe that does not contain the defect cannot see the defect. That is
/// how the tenth driver hid, and then this eleventh one.
///
/// ⚠ ANTI-VACUITY, and it has to run the OTHER way from `ast_term_depth`'s. `is_ground` returns
/// `true` by DRAINING the whole work stack and `false` by stopping at the first `Var` leaf, so a
/// ground fixture is the weaker instrument: an implementation that pushed nothing at all would
/// answer `true` immediately and pass. The fixture is therefore a spine whose ONLY leaf is a FREE
/// VARIABLE, asserted NOT ground — which can only be answered correctly by descending the entire
/// spine to reach it. Same reasoning as `ast_cmp`'s "twins differ only at the leaf".
fn ast_is_ground_body(depth: usize) {
    let a = nested_list_var(depth, "g");
    assert!(
        !a.is_ground(),
        "stack_depth_probe: ast_is_ground reported a depth-{depth} spine GROUND when its only \
         leaf is a FREE VARIABLE — the walk never reached the bottom, so the ladder measures \
         nothing"
    );
    // The ground twin, so the drain-to-completion path is exercised on the same ladder rather
    // than only the short-circuit path. A conversion could be flat on one and not the other.
    let b = nested_list(depth);
    assert!(
        b.is_ground(),
        "stack_depth_probe: ast_is_ground reported a depth-{depth} spine of integer literals \
         NOT ground — some arm answers `false` for a term with no variable in it"
    );
    std::mem::forget(a);
    std::mem::forget(b);
}

/// [`ast_is_ground_body`] on the pure `Proc::Add` chain — the MECHANISM twin. The other drivers'
/// `*_add` ladders are flat because the pure chain has no collection element to delegate at; a
/// driver with no worklist at all does not benefit from that, so before #189 this twin is where
/// the slope shows without any collection in the picture.
fn ast_is_ground_add_body(depth: usize) {
    let a = nested_add_var(depth, "g");
    assert!(
        !a.is_ground(),
        "stack_depth_probe: ast_is_ground_add reported a depth-{depth} Add chain GROUND when its \
         only leaf is a FREE VARIABLE — the walk never reached the bottom"
    );
    let b = nested_add(depth);
    assert!(
        b.is_ground(),
        "stack_depth_probe: ast_is_ground_add reported a depth-{depth} Add chain of integer \
         literals NOT ground"
    );
    std::mem::forget(a);
    std::mem::forget(b);
}

// ---------------------------------------------------------------------------
// ★★ `try_eval` — the TWELFTH driver, and the census row that named it was WRONG about why.
//
// `GENERATED_FILE_CENSUS`'s `eval.rs` row read: *"PARTIALLY converted: `Int` has an
// `__EvalFrame` worklist, the other 15 categories are plain host recursion."* The second half
// is FALSE, and the way it is false matters more than the fact.
//
// ★ THE DECIDING FUNCTION, read from `macros/src/gen/native/eval.rs` @ `717efdc5`:
//
//   * `generate_eval_method` emits `eval`/`try_eval` ONLY for categories with a `native_type`
//     (`None => continue`, :367). Rholang has SIXTEEN such categories, which is where the
//     "15 others" came from.
//   * The worklist form is chosen by `pda_supported && !pda_reduce_arms.is_empty()` (:1201),
//     and `pda_reduce_arms` is filled ONLY by the HOL branch (`else if let Some(ref
//     rust_code_block) = rule.rust_code`, :590) — one Reduce variant per HOL rule.
//   * ⇒ a category takes the recursive branch **exactly when it has no HOL rule**, and a
//     category with no HOL rule has NO SAME-CATEGORY CHILD to recurse into. Its arms are the
//     literal (`Some(n.clone())`), the Var (`None`), the auto-injected CASTS, and `_ => None`.
//
// So the recursive branch is not "plain host recursion" — for the same-category axis it is not
// recursion at all. Rholang's `terms { }` block declares exactly ONE HOL rule over a native
// category (`NegInt . a:Int |- "-" a : Int ![(-a)]`, `languages/src/rholang.rs:1257`), which is
// why `Int` alone carries a worklist and why nothing else has anything to convert.
//
// ★ MEASURED over the artifact as well as derived from the emitter: a census of all 54
// generated `eval.rs` files (62 `try_eval` impls) finds ZERO non-cast `try_eval()` call sites in
// any Rholang category. Every one of Rholang's 12 call sites sits under a `<Src>To<Tgt>`
// auto-injected projection label, i.e. is CROSS-category by construction.
//
// ⚠ WHAT IS LEFT, and it is a real bound rather than an absence. The cross-category calls form
// the LOSSLESS CAST LATTICE, and its host depth is the lattice's HEIGHT, not the term's:
//
//     BigRat → {BigInt, Fixed, Float, Int, UInt32, Bool}
//     BigInt → {Int, UInt32, Bool}          Int → {UInt32, Bool}        UInt32 → {Bool}
//     Bool, Fixed, Float, Str, Bytes, List, Bag, Map, Set, Pathmap, ReadZipper, WriteZipper → ∅
//
// — a strict partial order (`BigRat ▸ BigInt ▸ Int ▸ UInt32 ▸ Bool` is its longest chain), so at
// most FIVE host frames for any term of any depth. The two subjects below measure the claim
// instead of asserting it: `ast_try_eval` drives the worklist down a depth-N chain, and
// `ast_try_eval_cast` puts a lattice hop ON TOP of the same chain so the composition is on one
// ladder. Both must read flat, or the derivation above is wrong somewhere.
// ---------------------------------------------------------------------------

/// **`try_eval` on the `Int::NegInt` chain — the WORKLIST path, at depth.**
///
/// This is `Int`'s `__EvalFrame` driver descending `depth` levels of `NegInt`. It is also the
/// MECHANISM twin the other subjects spell `*_add`: a pure same-category chain with no
/// collection and no category hop, so a flat reading here cannot be a collection arm's doing.
///
/// ⚠ ANTI-VACUITY, twice over, because `try_eval` answers `Option` and BOTH failure modes are
/// silent:
///
/// 1. **The exact value.** `NegInt^d(NumLit(1))` is `+1` for even `d` and `−1` for odd `d`, and
///    it is that only if all `d` negations were applied. An evaluator that stopped early
///    returns the wrong SIGN, not `None`.
/// 2. **The leaf discrimination.** Two chains that differ only at the deepest literal must
///    evaluate differently — the same rule `ast_cmp_body` obeys. A driver that answered from
///    the top `NegInt` alone would satisfy (1) by luck on one parity and fail this.
fn ast_try_eval_body(depth: usize) {
    let a = nested_neg_int_leaf(depth, 1);
    let expected = if depth % 2 == 0 { 1i64 } else { -1i64 };
    assert_eq!(
        a.try_eval(),
        Some(expected),
        "stack_depth_probe: ast_try_eval on a depth-{depth} NegInt chain over `1` must be \
         {expected} — a different value means the walk did not apply every negation, and `None` \
         means it did not reach the literal at all"
    );
    let b = nested_neg_int_leaf(depth, 2);
    assert_ne!(
        a.try_eval(),
        b.try_eval(),
        "stack_depth_probe: ast_try_eval gave the SAME value for two depth-{depth} chains that \
         differ only at their deepest literal — the ladder is not being descended"
    );
    std::mem::forget(a);
    std::mem::forget(b);
}

/// **`try_eval` across the CAST LATTICE, composed with the worklist.**
///
/// `BigRat::IntToBigRat(NegInt^depth(NumLit(leaf)))`. `BigRat` has no HOL rule, so it takes the
/// recursive branch; its `IntToBigRat` arm makes ONE cross-category call into `Int::try_eval`,
/// which is the worklist. The composition is what a real term exercises and what neither
/// subject alone would show: if the lattice hop were per-LEVEL rather than per-EDGE, this ladder
/// would slope where [`ast_try_eval_body`] does not.
///
/// ⚠ ANTI-VACUITY: the leaf discrimination again. `CanonicalBigRat` compares by value, so two
/// chains differing only at the deepest literal must produce different rationals — which
/// requires descending `Int`'s whole chain and then applying the coercion.
fn ast_try_eval_cast_body(depth: usize) {
    let a = BigRat::IntToBigRat(Arc::new(nested_neg_int_leaf(depth, 1)));
    let b = BigRat::IntToBigRat(Arc::new(nested_neg_int_leaf(depth, 2)));
    let va = a.try_eval();
    assert!(
        va.is_some(),
        "stack_depth_probe: ast_try_eval_cast answered None on a depth-{depth} chain under a \
         lossless `Int ▸ BigRat` projection — the inner chain evaluates, so a None here is the \
         cast arm failing to reach it"
    );
    assert_ne!(
        va,
        b.try_eval(),
        "stack_depth_probe: ast_try_eval_cast gave the SAME rational for two depth-{depth} \
         chains differing only at their deepest literal — the cast arm is not descending"
    );
    std::mem::forget(a);
    std::mem::forget(b);
}

/// ★★ **THE POSITIVE CONTROL FOR THE CLASSIFIER, and it exists because #162 emptied the sloped
/// set.**
///
/// `the_sloped_driver_set_is_exactly_the_declared_one` decides Flat vs Sloped with ONE fixed-stack
/// question: *does this subject survive 1 MiB at depth `CLASSIFY_DEPTH`?* That is sound only if
/// `CLASSIFY_DEPTH` is deep enough to exhaust 1 MiB for a subject that really does slope — and the
/// constant was calibrated against `ast_drop` at 94 B/level, then against `ast_term_depth` at 207.
/// #162 converted both. With every `ast_*` subject flat, **the classifier would return `Flat` for
/// everything even if `CLASSIFY_DEPTH` were 4**, and the whole gate would pass vacuously.
///
/// This subject is the anchor that keeps it honest: a DELIBERATELY host-recursive walk of the same
/// `Proc::CastList` / `List::ListLit` ladder every other subject uses, owned by this file and
/// never converted. It is declared `Sloped`, so the gate fails if the classifier stops being able
/// to see a slope at all.
///
/// ⚠ It measures nothing about the generated drivers and is not a defect. It is an instrument
/// check — the depth-gate equivalent of the `MIN_DRIVER_SUBJECTS` floor on the enumeration.
fn recursion_control_depth(term: &Proc) -> usize {
    match term {
        Proc::CastList(inner) => 1 + recursion_control_depth_list(inner),
        _ => 0,
    }
}

/// The `List` half of [`recursion_control_depth`]'s deliberate mutual recursion.
fn recursion_control_depth_list(term: &List) -> usize {
    match term {
        List::ListLit(elements) => {
            let mut deepest = 0usize;
            for element in elements {
                deepest = deepest.max(recursion_control_depth(element));
            }
            1 + deepest
        },
        _ => 0,
    }
}

/// [`recursion_control_depth`] on the alternating ladder. Declared `Sloped`, and the gate's only
/// remaining sloped subject.
fn ast_recursion_control_body(depth: usize) {
    let a = nested_list(depth);
    let measured = recursion_control_depth(&a);
    assert!(
        measured >= depth,
        "stack_depth_probe: ast_recursion_control measured {measured} on a depth-{depth} spine — \
         the control must actually WALK the ladder or it proves nothing about the classifier"
    );
    std::mem::forget(a);
}

/// [`ast_term_depth_body`] on the pure chain. ★ Expected SLOPED where every other `*_add` twin is
/// flat: the pure chain's flatness elsewhere comes from there being no collection element to
/// delegate, and a driver with no worklist at all does not benefit from that.
fn ast_term_depth_add_body(depth: usize) {
    let a = nested_add(depth);
    let measured = a.term_depth();
    assert!(
        measured as usize >= depth,
        "stack_depth_probe: ast_term_depth_add measured {measured} on a depth-{depth} chain"
    );
    std::mem::forget(a);
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
// ★★ IS A GENERATED DRIVER REACHABLE FROM RHOLANG SOURCE? — a THREE-RUNG differential.
//
// ⚠ Measured slopes are not measured severity. `ast_cmp` bisects to 10,592 B/level (debug) on
// the alternating ladder, but a driver reachable only from a test fixture is a latent defect
// while one reachable from a parse is the 8.8 kB class (`291bc217`). The difference is a CALL
// SITE, and these three subjects turn it into a number instead of a `rg` result.
//
// ★ The call sites, read from the production lowering (`rholang-runtime/src/rholang_ast.rs`,
// `fn drive` @ 1695 — NOT the `#[cfg(test)]` `recursive_oracle`):
//
//   * 1851 `Proc::CastBag(Bag::BagLit(entries))` → `entries.sort_by_key(|(item, _)| *item)`
//   * 1885 `Proc::CastSet(Set::SetLit(items))`   → `items.sort()` on a `Vec<&Proc>`   (TERM)
//   * 2259 `Proc::CastSet(Set::SetLit(items))`   → `items.sort()` on a `Vec<&Proc>`   (PATTERN)
//
// `Vec<&Proc>::sort` is `Ord` on `Proc`, which is `iterative_cmp.rs` — `ast_cmp`'s driver, on
// whole sub-terms, inside the very function whose Θ(depth) recursion was the reported SIGSEGV.
//
// ★ And the SET LITERAL ITSELF is hash-keyed: `Set` is `mettail_runtime::HashSetLit<Proc>`
// (`languages/src/rholang.rs:202`), `Bag` is `HashBag<Proc>` = `HashMap<Proc, usize, FxHasher>`,
// `Map` is `HashMap<Proc, Proc>`. So building any of them from source runs `Hash` — and `Eq` on
// collision — over whole deeply-nested sub-terms at CONSTRUCTION time.
//
// The three rungs separate those two mechanisms, on one parse-and-lower path each:
//
// | subject            | source                                  | hashes keys | sorts elements |
// |--------------------|-----------------------------------------|:-----------:|:--------------:|
// | `list_pair_lower`  | `@"OUT"!([ [[…1…]], [[…2…]] ])`         | no          | no             |
// | `map_pair_lower`   | `@"OUT"!({ [[…1…]] : 0, [[…2…]] : 0 })` | YES         | no             |
// | `set_pair_lower`   | `@"OUT"!(Set( [[…1…]], [[…2…]] ))`      | YES         | YES            |
//
// Every rung parses two spines of the SAME depth and lowers them through the SAME `drive`, so
// the parser's own 1,408 B/level is present in all three and cancels in the differences:
// `map − list` is the hash-insert, and `set − map` is the sort, i.e. `ast_cmp`.
//
// ⚠ Two deep elements, not one, and that is required rather than tidy: `Vec::sort` on a
// one-element slice performs ZERO comparisons, so a single-element `Set` would exercise the
// call site and measure nothing. The two leaves differ (`1` vs `2`) so the comparison must
// descend both spines to their bottom to decide — the same anti-vacuity rule `ast_cmp_body`
// obeys, transplanted onto the source path.
// ---------------------------------------------------------------------------

/// `[[[…[leaf]…]]]` with `depth` bracket levels, appended to `out`.
fn push_deep_element(out: &mut String, depth: usize, leaf: char) {
    for _ in 0..depth {
        out.push('[');
    }
    out.push(leaf);
    for _ in 0..depth {
        out.push(']');
    }
}

/// `@"OUT"!([ [[…1…]], [[…2…]] ])` — the CONTROL: a list literal neither hashes nor sorts.
fn list_pair_source(depth: usize) -> String {
    let mut source = String::with_capacity(4 * depth + 32);
    source.push_str("@\"OUT\"!([");
    push_deep_element(&mut source, depth, '1');
    source.push_str(", ");
    push_deep_element(&mut source, depth, '2');
    source.push_str("])");
    source
}

/// `@"OUT"!({ [[…1…]] : 0, [[…2…]] : 0 })` — a map literal: hashes its keys, sorts nothing.
fn map_pair_source(depth: usize) -> String {
    let mut source = String::with_capacity(4 * depth + 40);
    source.push_str("@\"OUT\"!({");
    push_deep_element(&mut source, depth, '1');
    source.push_str(" : 0, ");
    push_deep_element(&mut source, depth, '2');
    source.push_str(" : 0})");
    source
}

/// `@"OUT"!(Set( [[…1…]], [[…2…]] ))` — a set literal: hashes its elements AND sorts them in
/// `drive`.
fn set_pair_source(depth: usize) -> String {
    let mut source = String::with_capacity(4 * depth + 40);
    source.push_str("@\"OUT\"!(Set(");
    push_deep_element(&mut source, depth, '1');
    source.push_str(", ");
    push_deep_element(&mut source, depth, '2');
    source.push_str("))");
    source
}

/// ★ The PARSE-ONLY rungs, which exist because the lower-only reading was AMBIGUOUS.
///
/// Bisected debug, 16 → 1,024: `list_pair_lower` 950 B/level but `map_pair_lower` **10,491** —
/// an 11.0× jump from replacing a list literal with a hash-keyed one. That localises the cost to
/// the collection literal, but NOT to a phase: a hash-keyed literal is built twice over, once by
/// the parser's own reduce action (`HashMapLit::<Proc, Proc>::default()` then
/// `container.insert(k, v)`, emitted into `wpda.rs`) and again read by `drive`. These rungs stop
/// after the parse so the two phases can be told apart.
///
/// ⚠ They `mem::forget` rather than `drop`, unlike [`parse_depth_body`], and that is deliberate:
/// `drop` of a deep `Proc` is `ast_drop` (252 B/level debug, 94 release), so a dropping parse
/// rung reads `max(parser, teardown)` and could not be differenced against a forgetting one.
fn list_pair_parse_body(depth: usize) {
    let source = list_pair_source(depth);
    let term = Proc::parse_via_wpda(&source).expect("stack_depth_probe: list_pair did not parse");
    std::mem::forget(term);
}

fn map_pair_parse_body(depth: usize) {
    let source = map_pair_source(depth);
    let term = Proc::parse_via_wpda(&source).expect("stack_depth_probe: map_pair did not parse");
    std::mem::forget(term);
}

fn set_pair_parse_body(depth: usize) {
    let source = set_pair_source(depth);
    let term = Proc::parse_via_wpda(&source).expect("stack_depth_probe: set_pair did not parse");
    std::mem::forget(term);
}

fn list_pair_lower_body(depth: usize) {
    let source = list_pair_source(depth);
    let term = Proc::parse_via_wpda(&source).expect("stack_depth_probe: list_pair did not parse");
    lower(term);
}

fn map_pair_lower_body(depth: usize) {
    let source = map_pair_source(depth);
    let term = Proc::parse_via_wpda(&source).expect("stack_depth_probe: map_pair did not parse");
    lower(term);
}

fn set_pair_lower_body(depth: usize) {
    let source = set_pair_source(depth);
    let term = Proc::parse_via_wpda(&source).expect("stack_depth_probe: set_pair did not parse");
    lower(term);
}

// ---------------------------------------------------------------------------
// ★★ #174 — NAMING the hash-keyed collection cost, by taking the mechanism OUT of the pipeline.
//
// The three `*_pair_lower` rungs above localise the cost to "the hash-keyed literal" and to the
// LOWER phase (the `*_pair_parse` rungs read flat), but a phase is not a mechanism. These two
// subjects run the suspected mechanism on its own, with `lower_depth` — build + lower +
// dismantle, no hashing — as the negative control on the identical term.
//
// ★ THE SUSPECT, read from the `models` crate (`../f1r3node-rust-mettail`) @ its checked-out
// revision, following the ONE structural difference between an `EList` and an `EMap`/`ESet`:
//
//   `rholang_ast.rs:2460  new_emap_par(pairs, …)`
//     → `models/src/rust/utils.rs:715  new_emap_expr`
//     → `EMapBody(ParMapTypeMapper::par_map_to_emap(ParMap::new(…)))`
//     → `models/src/rust/par_map.rs:18  ParMap::new`  → `SortedParMap::create_from_vec`
//     → `models/src/rust/sorted_par_map.rs:30`  `let map: HashMap<Par, Par> = vec.into_iter().collect();`
//     → `models/src/lib.rs:284  impl Hash for Par`  ← HAND-WRITTEN AND HOST-RECURSIVE
//
//   `rholang_ast.rs:2424  new_elist_par(items, …)`
//     → `models/src/rust/utils.rs:897  new_elist_expr` → `EListBody(EList { ps: Vec<Par>, … })`
//     → a plain vector. NO hash, NO sort, NO `Ord`.
//
// `impl Hash for Par` is `self.sends.hash(state); … self.exprs.hash(state); …` — `Vec<Expr>` →
// `Expr` → nested `Par` → `Par::hash` again, on the native stack, once per level. `impl
// PartialEq for Par` next to it (`:265`) has the same shape and runs on hash collision.
//
// ⚠ THIS IS NOT A MeTTaIL DRIVER, which is exactly why the figure "matched no driver measured
// in isolation". It is in `models`, the same crate and the same class as `par_drop` — the
// derived/hand-written impls this workspace's conversion does not own. It is recorded here so
// the number has a NAME and an ADDRESS, and the repair is f1r3node's to make.
// ---------------------------------------------------------------------------

/// **`Par`'s hash, alone, on a term `lower_depth` already walks flat.**
///
/// Build `nested_list(depth)`, lower it with the CONVERTED iterative `drive` (flat — that is
/// `lower_depth`), then hash the resulting `Par`. The only thing this subject adds over
/// [`lower_depth_body`] is `models::lib.rs`'s `impl Hash for Par`, so the DIFFERENCE between
/// the two ladders is that impl and nothing else.
///
/// ⚠ ANTI-VACUITY: two spines differing only at their deepest literal must hash DIFFERENTLY.
/// A `Hash` impl that stopped at the top `Par` would agree on both and read flat for the wrong
/// reason — the same failure `ast_cmp_body`'s twins guard against.
fn par_hash_body(depth: usize) {
    use std::hash::{Hash, Hasher};
    let env = BoundEnv::new();
    let a = nested_list_leaf(depth, 1);
    let b = nested_list_leaf(depth, 2);
    let par_a = lower_proc_in_env(&a, &env).expect("stack_depth_probe: par_hash lowering failed");
    let par_b = lower_proc_in_env(&b, &env).expect("stack_depth_probe: par_hash lowering failed");
    let digest = |p: &models::rhoapi::Par| {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        p.hash(&mut hasher);
        hasher.finish()
    };
    assert_ne!(
        digest(&par_a),
        digest(&par_b),
        "stack_depth_probe: par_hash produced the SAME digest for two depth-{depth} Pars that \
         differ only at their deepest literal — `Hash for Par` is not descending, so this ladder \
         measures nothing"
    );
    dismantle(par_a);
    dismantle(par_b);
    std::mem::forget(a);
    std::mem::forget(b);
}

/// **The composed cell: the `HashMap<Par, Par>` collect that `SortedParMap::create_from_vec`
/// performs, on deep keys.**
///
/// This is [`par_hash_body`]'s mechanism in the shape the lowering actually uses it — as MAP
/// KEYS — so a slope here is the `map_pair_lower` residue reproduced with the parser, the
/// `drive` worklist and the `Kont::MapLit` assembly all removed from the picture.
///
/// ⚠ ANTI-VACUITY: the two keys differ only at their deepest literal, so a map that ended up
/// with ONE entry means `Hash`+`Eq` collapsed two distinct deep terms and the ladder is
/// measuring a degenerate insert.
fn par_hashmap_body(depth: usize) {
    let env = BoundEnv::new();
    let a = nested_list_leaf(depth, 1);
    let b = nested_list_leaf(depth, 2);
    let par_a =
        lower_proc_in_env(&a, &env).expect("stack_depth_probe: par_hashmap lowering failed");
    let par_b =
        lower_proc_in_env(&b, &env).expect("stack_depth_probe: par_hashmap lowering failed");
    let nil = models::rust::utils::new_gint_par(0, Vec::new(), false);
    let map: std::collections::HashMap<models::rhoapi::Par, models::rhoapi::Par> =
        vec![(par_a, nil.clone()), (par_b, nil)]
            .into_iter()
            .collect();
    assert_eq!(
        map.len(),
        2,
        "stack_depth_probe: par_hashmap collapsed two depth-{depth} keys that differ at their \
         deepest literal into {} entry(ies) — `Hash`/`Eq` for `Par` did not descend, so the \
         insert measured nothing",
        map.len()
    );
    std::mem::forget(map);
    std::mem::forget(a);
    std::mem::forget(b);
}

/// ★ Not a ladder — an INSTRUMENT. Prints the byte length of each rung's source at `depth`, so
/// "how many source bytes reach the ceiling" is read off the same string the ladder parses
/// rather than recomputed by hand in a report.
fn report_source_bytes_body(depth: usize) {
    println!("depth={depth}");
    println!("  list_pair_source  {} bytes", list_pair_source(depth).len());
    println!("  map_pair_source   {} bytes", map_pair_source(depth).len());
    println!("  set_pair_source   {} bytes", set_pair_source(depth).len());
    println!("  reproducer_source {} bytes", reproducer_source(depth).len());
}

// ---------------------------------------------------------------------------
// ★★ THE CONFOUND CONTROL — five of the nine readings may not be their own drivers.
//
// `ast_eq`, `ast_normalize`, `ast_match_pattern` and `ast_subst` all bisected to ~6,140
// B/level in debug and ~175 in release, on the alternating ladder. ★ That the figures are
// numerically INDISTINGUISHABLE is itself the evidence: four independent traversals do not
// agree to three significant figures by coincidence — they agree because they share a
// component.
//
// The shared component is each subject's own ANTI-VACUITY ASSERTION. `ast_subst` closes with
// `assert!(replaced != term)` and `ast_normalize` with `assert!(normalized == term)`, and
// `!=`/`==` on `Proc` is `PartialEq` — which is `iterative_cmp.rs`, i.e. `ast_eq`'s driver,
// re-entered on the same deep term. So those two ladders may be measuring `ast_eq` twice and
// their own subject not at all.
//
// The generated source predicts they will read FLAT once the assertion is eq-free:
//
//   * `subst.rs`'s `List::ListLit(ref coll)` arm PUSHES a `SubstTask::VisitProc` for every
//     element (`for (idx, elem) in coll.iter().enumerate().rev()`). It is a real worklist
//     descent with zero host recursion — heap growth, not stack growth.
//   * `normalize.rs`'s arm is `List::ListLit(v) => results[slot] = Some(…ListLit(v.clone()))`
//     — a CLONE-LEAF. It never descends into the elements at all, so `normalize` on this
//     ladder visits `Proc::CastList` → `norm_visit_list` → clone and stops: exactly two
//     worklist steps at ANY depth. And `Proc::clone` is `Arc::clone` per child (`ast_clone`,
//     measured flat), so the clone is O(width) heap and O(1) stack.
//
// ⚠ THE ANTI-VACUITY CHECK MAY NOT USE `term_depth()`, and that is a measured constraint
// rather than a preference. `macros/src/gen/term_ops/depth.rs` emits `term_depth` as
// `1 + coll.iter().map(|x| x.term_depth()).max().unwrap_or(0)` — plain HOST RECURSION, with no
// worklist anywhere. It is a TENTH Θ(depth) traversal in this family, not a neutral instrument,
// and using it here would have replaced `ast_eq`'s slope with its own.
//
// ★ So the check below is a probe-LOCAL iterative walk, using no generated driver at all: it
// descends the result's spine with a `while`/`loop` over borrows, counts the levels it crossed,
// and reads the leaf. It is shape-forced in the same sense the other subjects are — the
// threshold SCALES WITH DEPTH (`levels == depth`), so a driver that stopped early fails — and
// it is O(1) in stack by construction, so it cannot contribute a slope of its own.
// ---------------------------------------------------------------------------

/// Walk a [`nested_list`] spine to its leaf ITERATIVELY, counting levels.
///
/// Returns `(levels, leaf)`: `levels` is the number of `CastList`/singleton-`ListLit` pairs
/// crossed, and `leaf` borrows the first `Proc` that is not one. Uses a `loop` over borrows —
/// no `PartialEq`, no `Debug`, no `Display`, no `clone`, no generated driver of any kind — so a
/// subject can observe its driver's result all the way to the deepest level without re-entering
/// another driver to do it.
fn spine_leaf(term: &Proc) -> (usize, &Proc) {
    let mut cursor = term;
    let mut levels = 0usize;
    loop {
        match cursor {
            Proc::CastList(inner) => match &**inner {
                List::ListLit(items) if items.len() == 1 => {
                    levels += 1;
                    cursor = &items[0];
                },
                _ => return (levels, cursor),
            },
            _ => return (levels, cursor),
        }
    }
}

/// [`spine_leaf`] for the pure `Proc::Add(Arc<Proc>, Arc<Proc>)` chain, which nests on its LEFT
/// operand.
fn add_spine_leaf(term: &Proc) -> (usize, &Proc) {
    let mut cursor = term;
    let mut levels = 0usize;
    while let Proc::Add(lhs, _) = cursor {
        levels += 1;
        cursor = &**lhs;
    }
    (levels, cursor)
}

/// The `i64` under a `CastInt(NumLit(_))` leaf, or `None`. Reads through borrows only, so it
/// cannot contribute a traversal.
fn leaf_num(leaf: &Proc) -> Option<i64> {
    match leaf {
        Proc::CastInt(inner) => match &**inner {
            Int::NumLit(value) => Some(*value),
            _ => None,
        },
        _ => None,
    }
}

/// `ast_subst` with the `PartialEq` assertion REPLACED by an eq-free one — the confound control.
///
/// Identical to [`ast_subst_body`] in every respect except the anti-vacuity check: instead of
/// `assert!(replaced != term)`, which re-enters `iterative_cmp`, it walks the result's spine
/// with [`spine_leaf`] and requires that the walk crossed all `depth` levels AND that the leaf
/// is the substituted `7` rather than the free variable it replaced. That is a STRICTLY
/// STRONGER statement than `replaced != term` — inequality is satisfied by a difference
/// anywhere, while this pins the change to the deepest level — and it is O(1) in stack.
fn ast_subst_noassert_body(depth: usize) {
    let term = nested_list_var(depth, "probe_subst_x");
    let fv = mettail_runtime::get_or_create_var("probe_subst_x".to_string());
    let replaced = term.substitute(&fv, &int(7));
    let (levels, leaf) = spine_leaf(&replaced);
    assert_eq!(
        levels, depth,
        "stack_depth_probe: ast_subst_noassert result carries {levels} levels, not {depth} — the \
         substitution did not rebuild the whole spine"
    );
    assert_eq!(
        leaf_num(leaf),
        Some(7),
        "stack_depth_probe: ast_subst_noassert did not reach the LEAF variable — the leaf is not \
         the substituted 7"
    );
    std::hint::black_box(&replaced);
    std::mem::forget(term);
    std::mem::forget(replaced);
}

/// `ast_normalize` with the `PartialEq` assertion REPLACED by an eq-free one.
///
/// [`ast_normalize_body`] asserts `normalized == term`, which is `iterative_cmp` on two deep
/// terms. The eq-free form asserts the same intent — *the result still carries the depth it was
/// given, and its leaf survived* — by walking the result's spine iteratively.
fn ast_normalize_noassert_body(depth: usize) {
    let term = nested_list(depth);
    let normalized = term.normalize();
    let (levels, leaf) = spine_leaf(&normalized);
    assert_eq!(
        levels, depth,
        "stack_depth_probe: ast_normalize_noassert result carries {levels} levels, not {depth} — \
         normalisation is not the identity on a canonical term"
    );
    assert_eq!(
        leaf_num(leaf),
        Some(1),
        "stack_depth_probe: ast_normalize_noassert lost the leaf literal"
    );
    std::hint::black_box(&normalized);
    std::mem::forget(term);
    std::mem::forget(normalized);
}

/// [`ast_subst_noassert_body`] on the PURE chain, so the control has both ladders.
fn ast_subst_noassert_add_body(depth: usize) {
    let term = nested_add_var(depth, "probe_subst_y");
    let fv = mettail_runtime::get_or_create_var("probe_subst_y".to_string());
    let replaced = term.substitute(&fv, &int(7));
    let (levels, leaf) = add_spine_leaf(&replaced);
    assert_eq!(
        levels, depth,
        "stack_depth_probe: ast_subst_noassert_add result carries {levels} levels, not {depth}"
    );
    assert_eq!(
        leaf_num(leaf),
        Some(7),
        "stack_depth_probe: ast_subst_noassert_add did not reach the LEAF variable"
    );
    std::hint::black_box(&replaced);
    std::mem::forget(term);
    std::mem::forget(replaced);
}

/// [`ast_normalize_noassert_body`] on the PURE chain.
fn ast_normalize_noassert_add_body(depth: usize) {
    let term = nested_add(depth);
    let normalized = term.normalize();
    let (levels, leaf) = add_spine_leaf(&normalized);
    assert_eq!(
        levels, depth,
        "stack_depth_probe: ast_normalize_noassert_add result carries {levels} levels, not {depth}"
    );
    assert_eq!(
        leaf_num(leaf),
        Some(1),
        "stack_depth_probe: ast_normalize_noassert_add lost the leaf literal"
    );
    std::hint::black_box(&normalized);
    std::mem::forget(term);
    std::mem::forget(normalized);
}

// ---------------------------------------------------------------------------
// ★★ THE MECHANISM TEST — the same eight drivers on a shape with NO cross-type hop.
//
// The `*_add` twins below are identical in every respect except the SHAPE they walk:
// `nested_add` is `Proc::Add(Arc<Proc>, Arc<Proc>)`, a pure single-type chain, where
// `nested_list` alternates `Proc::CastList(Arc<List>)` with `List::ListLit(Vec<Proc>)`.
//
// ★★ RESULT (bisected 2026-07-29, both profiles, 16 → 4,096): the prediction of a SHARP split
// HELD — every `*_add` twin is flat (0–1 B/level) while its `nested_list` original is sloped —
// but the EXPLANATION the split was offered for did not.
//
// The hypothesis was: *"the generated work stacks are typed per category, and a driver does not
// follow an edge that leaves its own type."* That is REFUTED at the source. `iterative_cmp.rs`
// pushes `CmpTask::CmpList` for `Proc::CastList(Arc<List>)` (`:2175`) — the cross-category edge
// IS followed. What the `*_add` chain actually lacks is not a category hop but a COLLECTION: it
// is `Proc::Add(Arc<Proc>, Arc<Proc>)`, all fields single sub-terms, so there is no `Vec<Proc>`
// to hand whole to a trait method. `nested_list` has one, and `if a != b` on it (`:11129`) is
// where the work stack is left behind.
//
// ⚠ So this 2x2 is still the right experiment and its numbers still stand; only the label on the
// axis changed, from "cross-type hop" to "collection-element boundary". A ladder that varies two
// things at once — category hop AND collection-ness — cannot tell them apart, and this one did
// vary both. It was the generated source, not the ladder, that decided between them.
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
///
/// ★★ A TABLE rather than a bare `match`, and the reason is a gate the parent could not
/// otherwise write. `stack_depth_gate`'s driver classification has to answer *"is the set of
/// SLOPED drivers still exactly the expected one?"*, and the two ways that question fails are
/// (a) a driver leaves the set silently and (b) a **new** driver appears in it. Catching (b)
/// requires knowing the universe, and a parent that hand-mirrors this list cannot know it — a
/// subject added here and not there is simply never classified, which is a vacuous pass.
///
/// So the parent ENUMERATES this table at run time (`GATE_SUBJECT=list_subjects`, which prints
/// one name per line) and fails if any `ast_*` name it reads is absent from its own declared
/// partition. The table is the single source of truth; the parent holds only the expectation.
///
/// ⚠ `list_subjects` is deliberately NOT a row: it takes no depth and measures nothing, and a
/// row for it would appear in the universe the parent must classify.
const SUBJECTS: &[(&str, fn(usize))] = &[
    // -------- depth axis: the converted lowering --------
    ("lower_depth", lower_depth_body),
    ("lower_add", lower_add_body),
    ("lower_par", lower_par_body),
    ("lower_neg", lower_neg_body),
    ("lower_formula", lower_formula_body),
    ("lower_new", lower_new_body),
    ("reproducer", reproducer_body),
    ("lower_leak", lower_leak_body),
    // -------- the GENERATED TRAIT DRIVERS (eight that had no subject) --------
    ("ast_eq", ast_eq_body),
    ("ast_cmp", ast_cmp_body),
    ("ast_hash", ast_hash_body),
    ("ast_debug", ast_debug_body),
    ("ast_display", ast_display_body),
    ("ast_semantic_hash", ast_semantic_hash_body),
    ("ast_subst", ast_subst_body),
    ("ast_env_subst", ast_env_subst_body),
    ("ast_parse_alt_filter", ast_parse_alt_filter_body),
    ("ast_var_inference", ast_var_inference_body),
    ("ast_language_var_collect", ast_language_var_collect_body),
    ("ast_flt_reflect", ast_flt_reflect_body),
    ("ast_dovetail_report", ast_dovetail_report_body),
    ("ast_normalize", ast_normalize_body),
    ("ast_match_pattern", ast_match_pattern_body),
    // -------- ★ the TENTH driver: host-recursive, no worklist at all --------
    ("ast_term_depth", ast_term_depth_body),
    ("ast_term_depth_add", ast_term_depth_add_body),
    // -------- ★★ the ELEVENTH driver (#189): host-recursive AND with no subject at all -----
    //
    // The tenth was found because it had a subject that measured a slope. The eleventh could
    // not be found that way, because the thing missing was the subject. See
    // `ast_is_ground_body`, and `stack_depth_gate`'s
    // `every_generated_traversal_has_a_probe_subject`, which derives the universe from the
    // GENERATED TREE rather than from this table — because this table is the thing that was
    // incomplete.
    ("ast_is_ground", ast_is_ground_body),
    ("ast_is_ground_add", ast_is_ground_add_body),
    // -------- ★★ the TWELFTH driver: `try_eval`, whose census row was wrong about WHY -----
    //
    // The row said fifteen categories were "plain host recursion". The emitter says a category
    // takes the recursive branch exactly when it has NO HOL rule, and a category with no HOL
    // rule has no same-category child to recurse into. What is left is the CAST LATTICE, whose
    // height is a property of the grammar and not of the term. See `ast_try_eval_body`.
    ("ast_try_eval", ast_try_eval_body),
    ("ast_try_eval_cast", ast_try_eval_cast_body),
    // The classifier's own non-vacuity anchor — see `ast_recursion_control_body`.
    ("ast_recursion_control", ast_recursion_control_body),
    // -------- ★ the CONFOUND CONTROL: the same drivers, anti-vacuity WITHOUT `PartialEq` -----
    ("ast_subst_noassert", ast_subst_noassert_body),
    ("ast_normalize_noassert", ast_normalize_noassert_body),
    ("ast_subst_noassert_add", ast_subst_noassert_add_body),
    ("ast_normalize_noassert_add", ast_normalize_noassert_add_body),
    // -------- ★ SOURCE REACHABILITY: parse-only and parse+lower, three shapes each --------
    ("list_pair_parse", list_pair_parse_body),
    ("map_pair_parse", map_pair_parse_body),
    ("set_pair_parse", set_pair_parse_body),
    ("list_pair_lower", list_pair_lower_body),
    ("map_pair_lower", map_pair_lower_body),
    ("set_pair_lower", set_pair_lower_body),
    ("report_source_bytes", report_source_bytes_body),
    // -------- ★★ #174: the hash-keyed collection cost, isolated from its pipeline --------
    ("par_hash", par_hash_body),
    ("par_hashmap", par_hashmap_body),
    // -------- the MECHANISM TEST: same drivers, no cross-type hop --------
    ("ast_eq_add", ast_eq_add_body),
    ("ast_cmp_add", ast_cmp_add_body),
    ("ast_hash_add", ast_hash_add_body),
    ("ast_debug_add", ast_debug_add_body),
    ("ast_display_add", ast_display_add_body),
    ("ast_semantic_hash_add", ast_semantic_hash_add_body),
    ("ast_subst_add", ast_subst_add_body),
    ("ast_normalize_add", ast_normalize_add_body),
    ("ast_match_pattern_add", ast_match_pattern_add_body),
    // -------- ★ Clone: stack-safe by REPRESENTATION, not by a driver --------
    ("ast_clone", ast_clone_body),
    ("ast_clone_add", ast_clone_add_body),
    ("build_one", build_one_body),
    // -------- discriminators --------
    ("ast_drop", ast_drop_body),
    ("ast_drop_add", ast_drop_add_body),
    ("build_twins", build_twins_body),
    ("build_twins_add", build_twins_add_body),
    ("new_build", new_build_body),
    // -------- independent closure probes for non-lowering production paths --------
    ("parse_depth", parse_depth_body),
    ("par_drop", par_drop_body),
    ("render", render_body),
    // -------- width axis --------
    ("lower_width", lower_width_body),
    ("parse_width", parse_width_body),
];

/// The body [`SUBJECTS`] names `name`, or a panic naming what was asked for.
fn subject(name: &str) -> fn(usize) {
    match SUBJECTS
        .iter()
        .find(|(subject_name, _)| *subject_name == name)
    {
        Some((_, body)) => *body,
        None => panic!("stack_depth_probe: unknown GATE_SUBJECT={name:?}"),
    }
}

/// The subject name the parent uses to enumerate [`SUBJECTS`]. Not a row in it — see the table's
/// note.
const LIST_SUBJECTS: &str = "list_subjects";

fn main() {
    let name = std::env::var("GATE_SUBJECT").expect("stack_depth_probe: GATE_SUBJECT must be set");
    // ★ The enumeration mode, handled BEFORE `GATE_DEPTH` is read: it has no depth, and requiring
    // one would make the parent pass a meaningless number to learn the subject list.
    if name == LIST_SUBJECTS {
        for (subject_name, _) in SUBJECTS {
            println!("{subject_name}");
        }
        return;
    }
    let depth: usize = std::env::var("GATE_DEPTH")
        .expect("stack_depth_probe: GATE_DEPTH must accompany GATE_SUBJECT")
        .parse()
        .expect("stack_depth_probe: GATE_DEPTH must be an integer");
    // ★ On the MAIN thread. No `thread::Builder`, no `stack_size`, no `RUST_MIN_STACK`: the
    // only thing bounding this call is the `RLIMIT_STACK` the parent installed before `exec`.
    subject(&name)(depth);
}

