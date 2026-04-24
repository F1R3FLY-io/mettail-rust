# PDA Stack-Safety Completion — Session Handoff

**Session end date:** 2026-04-21
**Branch:** `feature/wfst-architecture` (merging `main`)
**Merge status:** content structurally complete; committed-worthy once the remaining PDA work lands and `test_bool_from_list_elem` no longer stack-overflows.

This document is the authoritative handoff for the in-flight stack-safety refactor. Read it top-to-bottom before touching any generator code. Every code location has file:line refs; every claim has a verification command.

---

## 1. Invariant to enforce

**Every tree-shaped operation emitted by the `language!` proc macro must use an explicit work-stack (`Vec<Frame>`). Zero recursion, zero mutual recursion, in the generated code.**

Already-safe emitters (the templates to follow):
- `macros/src/gen/syntax/display.rs` — `DisplayTask` enum + `DISPLAY_TASK_POOL` TLS + `display_iterative` driver. See lines 258-302, 465-479.
- `macros/src/gen/term_ops/iterative_clone.rs` — slot-buffer PDA with `AnyClonedTerm` heterogeneous enum for cross-category tree rebuild. **THIS is the canonical template for anything that rebuilds cross-category trees** (subst, normalize non-native). Lines 70 (AnyClonedTerm), 100 (CloneTask + TLS), 301 (driver), 413/513/583/715 (per-variant-kind Visit arms), 891/1004/1062/1199 (Assemble arms).
- `macros/src/gen/term_ops/match_pattern.rs` — similar (MatchTask + MATCH_TASK_POOL).
- `macros/src/gen/term_ops/iterative_cmp.rs`, `iterative_drop.rs`, `iterative_hash.rs` — similar.
- `prattail/src/trampoline.rs` — parser trampoline, explicit continuation stack.

---

## 2. What landed in the most recent session (verified)

### 2.1 Group A–E (pre-PDA merge work)

| Task | Status | Files |
|---|---|---|
| #52 Group E: Option→Err wiring in HOL step rules | ✅ | `macros/src/logic/mod.rs:2146-2309` (binary/unary/nary step emitters — detect `category_has_err` via `fold_field_count(r) == 0` on `Err` variant; emit `match safe_code { Some(v)=>Cat::NumLit(v), None=>Cat::Err }`). `macros/src/gen/native/eval.rs:160-174` (`hol_int_fact_option` detection + match-wrap for the eval path) |
| #53 Group D: Factorial errors on negative | ✅ | `languages/src/calculator.rs:117` (added `Err . |- "error" : Int ;`) and `:209-213` (`Fact . a:Int |- a "!" : Int ![{ if a < 0 { None } else { Some((1..=a).product::<i32>()) } }] step;`). Test body updated at `languages/tests/calculator.rs:722-727` |
| #54 Group B.1: Preserve display-equal alternatives | ✅ | `macros/src/gen/runtime/language.rs:389-477` — `from_alternatives` always preserves `Self::Ambiguous(flat)` when multiple alts are accepting (was previously collapsing via weight-best) |
| #55 Group B.2+C: Ambiguous recursion in substitute_env | ✅ | `macros/src/gen/runtime/language.rs:479-538` (Ambiguous arm recurses into each alt); `:2493-2516` and `:2862-2880` (`list_env` dedup by name); `:2457` and `:2828` (`remove_from_env` uses non-short-circuit `|` so ALL categories get cleared) |
| #56 Group A Option 2: Token::Integer suffix tag | ✅ | `prattail/src/int_lit.rs:168-245` — new `IntSuffix` enum + `from_text` + `matches_i32/u32/…`. `prattail/src/lib.rs:415` re-exports it. `prattail/src/automata/codegen.rs:409` (Token enum emission carries `(i64, IntSuffix)`). `:506` (Display), `:708-717` (accept_token), `:1105-1115` (token_kind_to_constructor), `:2296-2308` (token_variant_id). `prattail/src/trampoline.rs:5173-5230` (write_native_literal_arm: i32/u32/u64 gates on `suffix.matches_*()`). Ditto `pratt.rs` 14 sites, `unified_trampoline.rs` 1 site, `recursive.rs` 1 site, `automata/mod.rs:183` pattern string. **Fixes `test_int_parse_rejects_u32_suffix` and `test_uint32_bitwise`.** |

### 2.2 PDA work (this session)

| Task | Status | Files |
|---|---|---|
| #59 PDA classifier zero-ary + non-native cross-cat | ✅ | `macros/src/gen/native/eval.rs:25-49` — `classify_hol_rule_for_pda` accepts `rule.term_context.is_none()` as `Some(Vec::new())` (zero-ary rule = no children to recurse into, PDA-compatible). `:500-670` — `CrossKind::{Native, Borrow}` enum; `Borrow` stores `Box<Cat>` cloned in Visit and re-binds as `&Cat` at Reduce time. Applies to ALL non-native cross-cat fields (e.g. `Proc` in `Int::BigintCast.a:Proc`). **This is what made `Int::try_eval` PDA — enables deep-eval tests on 2MB stack.** |
| #60 eval() via try_eval().expect | ✅ | `macros/src/gen/native/eval.rs:726-749` — `pub fn eval() -> T { self.try_eval().expect(...) }`. Single-line delegate; indirectly PDA via try_eval's work-stack. Semantics change: overflow now panics uniformly (was: wrap in release, panic in debug). No tests regressed. |
| #64 MApply display iterative | ✅ | `macros/src/gen/syntax/display.rs:461-483` — reverse-iterate `args`, push each as `DisplayTask::Display<ArgCat>(arg as *const _, 0)` plus `WriteLiteral(", ")` separator. Original code inlined `arg.to_string()` per element, which re-entered Display. |
| #63 partial: native-type normalize PDA | ✅ | `macros/src/gen/term_ops/normalize.rs:140-422` — REPLACED the native-type branch with per-category `__NormTask<'a>` + `Assemble<Label>` frames + `Vec<Option<Self>>` slot buffer. Covers Int/UInt32/BigInt/BigRat/Fixed/Float/Bool/Str/List/Bag/Map. Cross-cat fields stored as `Box<OtherCat>` in the Assemble variant (or `OrdVar<Cat>` for Var kind) and re-cloned at Assemble time. Zero-ary rules emit a no-frame Visit arm. Var kind emits `return None`-equivalent (early bail). |
| #63 partial: `insert_into_<label>` iterative | ✅ | `macros/src/gen/term_ops/normalize.rs:40-83` — `generate_flatten_helpers` — replaced `Self::insert_into_<label>(bag, e.clone())` recursive call with explicit `Vec<Cat>` work stack. Matches `current` via `matches!`+`if let` ref-pattern because `#category` implements `Drop`. |

### 2.3 Verification of landed work (all on default 2 MB stack, no RUST_MIN_STACK override)

- **Baseline at session start:** 138 pass / 12 fail on calc.
- **Current:** 207 pass / 2-3 fail visible before `test_bool_from_list_elem` SIGABRT.
  - `test_try_eval_deep_addint_10000`, `test_try_eval_deep_neg_10000`, `test_try_eval_deep_mixed_ops_1000`, `test_try_eval_deep_fact_no_panic`: **all pass** (previously required RUST_MIN_STACK=16M).
- **Net:** +69 passing tests, architectural stack-safety for native-type eval and normalize.

Repro command for the PDA emission (confirm generated code is iterative):
```
grep -A2 "pub fn try_eval" target/generated/calculator/eval.rs | head -20
# Should show `__EvalFrame` enum + `while let Some(__frame) = work.pop()`.
# Should NOT show `match self { ... a.as_ref().try_eval() ... }`.
```

---

## 3. What remains — priority-ordered with exact specs

### 3.1 Task #62 — subst PDA (PRIORITY — unblocks `test_bool_from_list_elem`)

**Root cause (per Explore audit 2026-04-21):**
- `macros/src/gen/term_ops/subst.rs:460-540` — `generate_subst_by_name_arm` emits `Box::new((**f).subst_by_name_<cat>(env_map))` for each field.
- For cross-category fields, `.subst_by_name_<cat>` dispatches to the field's OWN category's method, which then recurses.
- Proc's `subst_by_name_proc` → field is Int → calls `Int::subst_by_name_proc` → Int has Proc field (`IntBin`) → calls `Proc::subst_by_name_proc` → ... **unbounded mutual recursion**.
- `macros/src/gen/term_ops/subst.rs:202-213` — `substitute_env` runs a fixed-point of 100 iterations × 13 `subst_by_name_*` calls per iteration × mutual recursion per call.
- For a 5-deep AST with cross-cat nesting, stack blows via 13-way hop.

**Fix per approved plan** (plan-agent output, 2026-04-21):

Replace `macros/src/gen/term_ops/subst.rs` entirely with a slot-buffer PDA using heterogeneous `AnySubstTerm` enum + single `SubstTask` enum + unified `subst_iterative` driver. Pattern mirrors `iterative_clone.rs`.

**Emit at language level** (once per language-macro invocation):

```rust
enum AnySubstTerm {
    WrapProc(Proc),
    WrapName(Name),
    WrapInt(Int),
    // ... one per category
}

enum SubstTask<'a> {
    // One Visit variant per category, per operation flavor:
    //   - SameCatSubst (substitute / subst): vars&[], repls&[]
    //   - CrossCatSubst (subst_<repl>): vars&[], repls&[Repl]
    //   - EnvSubst (subst_by_name_<repl>): env_map&IndexMap
    //   - Unify (unify_freevars_impl): no args
    // Represented by an ops side-stack; task carries `op_idx: usize`.
    Visit_<Cat> { src: *const Cat, slot: usize, op_idx: usize },
    // One Assemble variant per (category, rule). Child slots are `usize`s;
    // cross-cat cloned fields and binder patterns stored inline.
    AssembleRegular_<Cat>_<Label> { slot, child_slots: [usize; N], op_idx },
    AssembleCollection_<Cat>_<Label> { slot, elem_start, elem_count, op_idx },
    AssembleBinder_<Cat>_<Label> { slot, pre_slots, cloned_pattern: Binder<FreeVar<String>>, body_slot, op_idx },
    AssembleMultiBinder_<Cat>_<Label> { slot, pre_slots, cloned_pattern: Vec<Binder<…>>, body_slot, op_idx },
}

enum SubstOp<'a> {
    SameCatSubst { vars: &'a [&'a FreeVar<String>], repls: &'a [CurrentCat] },
    CrossCatSubst_<Repl> { vars: &'a [&'a FreeVar<String>], repls: &'a [Repl] },
    EnvSubst_<Repl> { env_map: &'a IndexMap<String, Repl> },
    Unify,
}

thread_local! {
    static SUBST_TASK_POOL:   Cell<Vec<SubstTask<'_>>>           = Cell::new(Vec::new());
    static SUBST_RESULT_POOL: Cell<Vec<Option<AnySubstTerm>>>    = Cell::new(Vec::new());
    static SUBST_OP_POOL:     Cell<Vec<SubstOp<'_>>>             = Cell::new(Vec::new());
}

fn subst_iterative(
    stack: &mut Vec<SubstTask<'_>>,
    results: &mut Vec<Option<AnySubstTerm>>,
    ops: &mut Vec<SubstOp<'_>>,
) { /* main driver; while let Some(t) = stack.pop() */ }
```

**Public methods** (all 13 per category × N categories) become thin wrappers:
```rust
pub fn subst_by_name_<cat>(&self, env_map: &IndexMap<String, Cat>) -> Self {
    SUBST_TASK_POOL.with(|t| SUBST_RESULT_POOL.with(|r| SUBST_OP_POOL.with(|o| {
        let mut stack = t.take(); stack.clear();
        let mut results = r.take(); results.clear();
        let mut ops = o.take(); ops.clear();
        results.push(None);
        ops.push(SubstOp::EnvSubst_<Cat>(env_map));
        stack.push(SubstTask::Visit_<Self::Cat> { src: self, slot: 0, op_idx: 0 });
        subst_iterative(&mut stack, &mut results, &mut ops);
        let root = match results[0].take() {
            Some(AnySubstTerm::Wrap<Cat>(v)) => v,
            _ => unreachable!(),
        };
        t.set(stack); r.set(results); o.set(ops);
        root
    })))
}
```

**Lifetime handling:** use `*const Cat` raw pointers throughout, as `iterative_clone.rs` does. The pointers are valid for the whole `subst_iterative` call because the root `self` borrows live for that scope. `SubstTask` does NOT need a lifetime parameter in the Cell (same trick as clone).

**Binder handling:** when a Binder/MultiBinder is visited, the op's `vars` or `env_map` is filtered (shadowed binder names removed) and pushed as a NEW op onto `ops`. The Visit for the body carries `op_idx: ops.len() - 1`. Assemble for the binder POPS the filtered op back off when reconstructing.

**Deleted functions** (replaced by the new driver/emitter):
- `generate_unify_freevars_arm` (line 258)
- `generate_subst_by_name_arm` (line 460)
- `generate_category_substitution` (line 735) — becomes the thin-wrapper emitter
- `generate_subst_impl` (line 1169)
- `generate_subst_arm` (line 1357)
- `generate_var_subst_arm` (line 1408)
- `generate_regular_subst_arm` (line 1431)
- `generate_collection_subst_arm` (line 1489)
- `generate_binder_subst_arm` (line 1529)
- `generate_multi_binder_subst_arm` (line 1624)

**Preserved surface** (all methods users + downstream code call — keep unchanged signatures):
- `substitute(&self, var: &FreeVar<String>, repl: &Self) -> Self`
- `multi_substitute(&self, vars: &[...], repls: &[Self]) -> Self`
- `subst(&self, vars: &[...], repls: &[Self]) -> Self`
- `subst_<cat>(&self, vars: &[...], repls: &[<Cat>]) -> Self`
- `substitute_<cat>(&self, var, repl: &<Cat>) -> Self`
- `multi_substitute_<cat>(&self, vars, repls: &[<Cat>]) -> Self`
- `subst_by_name_<cat>(&self, env_map: &IndexMap<...>) -> Self`
- `substitute_env(&self, env: &<Env>) -> Self` — keep fixed-point loop; each iter runs PDA once
- `unify_freevars(&self) -> Self`
- `unify_freevars_impl(&self, ...) -> Self`

**Verification commands:**
```
# Confirm no recursive subst_by_name_* sites in generated output:
grep -c "\.subst_by_name_" target/generated/calculator/env_subst.rs
# Should be 0 in match arms (only allowed in the top-level wrapper).

# Run the regression test that currently overflows:
cargo test -p mettail-languages --test calculator -- test_bool_from_list_elem
# Must PASS without RUST_MIN_STACK.

# Run full workspace to confirm no regressions:
cargo test --workspace
```

### 3.2 Task #63 — Proc/Name::normalize non-native PDA

**Root cause:**
- `macros/src/gen/term_ops/normalize.rs:454-751` — non-native normalize emission is `match self { ... Box::new(f.as_ref().normalize()) ... }`.
- Recursion sites: collection rule (`:491`), multi-binder (`:527`), single-field regular (`:558`), multi-field regular (`:594`, `:604`), binder scope body (~`:489`).
- `generate_beta_reduction_arms` (line 762) emits `lam.normalize() + arg.normalize() + body.substitute_<dom>(arg).normalize()` triple-nested recursion.
- `generate_cancellation_pair_arm` (line 644) emits `inner.normalize()` then variant-check then `p.normalize()` if cancel fires.

**Fix per approved plan:**

Apply the same slot-buffer PDA as `iterative_clone.rs` — emit a language-wide `AnyNormalizedTerm` enum and single `normalize_iterative` driver. Frame variants:

```rust
enum NormTask<'a> {
    Visit<Cat>      { src: *const Cat, slot: usize },
    VisitOwned<Cat> { src: Box<Cat>, slot: usize },   // for β-rescheduled bodies
    AssembleRegular_<Cat>_<Label>      { slot, same_slots, cross_clones },
    AssembleCollection_<Cat>_<Label>   { slot, elem_start, elem_count, counts_vec },
    AssembleBinder_<Cat>_<Label>       { slot, pre_slots, cloned_pattern, body_slot },
    AssembleMultiBinder_<Cat>_<Label>  { slot, pre_slots, cloned_pattern, body_slot },
    AssembleBetaApply_<Cat>_<Dom>      { slot, lam_slot, arg_slot },    // β-reduce
    AssembleBetaMApply_<Cat>_<Dom>     { slot, lam_slot, args_start, args_count },
    AssembleCancel_<Outer>_<Inner>     { slot, inner_slot },            // cancellation pair
}
```

**β-reduction flow in AssembleBetaApply:**
1. Pop `lam_normalized` from `lam_slot`, `arg_normalized` from `arg_slot`.
2. If `lam_normalized` matches `Cat::Lam<Dom>(scope)`:
   - `let (binder, body) = scope.clone().unbind();`
   - Call **subst PDA** (separate TLS pool): `let substituted = body.substitute_<dom>(&binder.0, &arg_normalized);`
   - Push `VisitOwned<Cat>::{ src: Box::new(substituted), slot }` to renormalize.
3. Else: `results[slot] = Some(AnyNormalizedTerm::Wrap<Cat>(Cat::Apply<Dom>(Box::new(lam_normalized), Box::new(arg_normalized))));`

**Chains of β-redexes** (Church numerals): grow on the heap's `stack: Vec<NormTask>` and `results: Vec<Option<...>>`, NOT on the call stack. Ω still diverges but by heap growth, which matches the invariant.

**Cancellation pair flow in AssembleCancel:**
1. Pop `inner_normalized` from `inner_slot`.
2. If `inner_normalized` matches `Inner::<inner_ctor>(p)`: push `VisitOwned<Cat>::{ src: p, slot }` (unwrap and re-visit).
3. Else: `results[slot] = Some(...Wrap<Cat>(Outer::<outer_ctor>(Box::new(other))));`

**Separate TLS pool from subst:** `NORM_TASK_POOL`, `NORM_RESULT_POOL`. When β calls subst, subst uses its own pool — no clash. The `cell.take/set` pattern (display.rs precedent at lines 1505-1521) handles outer-pool preservation across re-entrancy.

**Keep native-type normalize PDA untouched** — it already works and uses per-category `__NormTask<'a>` local enums. The new code is a SECOND branch in `generate_normalize_functions` for the non-native path.

**Verification:**
```
cargo test -p mettail-languages
# All tests pass, specifically:
cargo test -p mettail-languages --test calculator -- test_bool_from_list_elem
# and rhocalc/ambient/lambda HOL-heavy tests (see .rs files in languages/tests/).
```

### 3.3 Task #61 — compile_error! on unclassifiable rules (final cleanup)

After #62 and #63 land:

1. Remove the recursive fallback at `macros/src/gen/native/eval.rs:718-723` — replace with `compile_error!("mettail: cannot emit stack-safe try_eval for rule {cat}::{label} — report grammar as macro bug")`.
2. Ensure every classifier (for subst, normalize) likewise emits `compile_error!` if any rule doesn't map to a WorkStackPattern variant.
3. Delete any `legacy_generate_*` functions left as dead code from earlier commits.

**No feature flags, no shadow mode, no runtime fallback.** The invariant is: if codegen can't produce iterative code, that's a macro bug to report, not a runtime condition to tolerate.

### 3.4 Task #58 — HashMap ordering flakes (`test_map_keys`, `test_map_values`)

**Root cause:** `std::collections::HashMap` iteration order is non-deterministic. Tests at `languages/tests/calculator.rs:15+` assert specific `keys/values` order, which is only guaranteed by `IndexMap` (insertion order) or `BTreeMap` (sorted).

**Fix options:**
- **(a)** Switch the macro's generated `Map` type from `HashMap` to `IndexMap` in `runtime/src/hashmap_lit.rs` or wherever Map lit is emitted. Deterministic ordering guaranteed.
- **(b)** Rewrite the tests to be order-independent (sort or use set-based assertions).

Recommend **(a)** — insertion-order is what users intuitively expect.

### 3.5 Task #11 — Merge miscellaneous (.gitignore, docs)

Outstanding untracked files per `git status`:
- Merge `.gitignore` additions from main and feature.
- Several new docs in `docs/design/made/` and `docs/design/made/native-types/` (BigInt library selection, BigRat design, numeric casting, etc.) — all already added in staged area; review and commit.
- Remove `docs/design/exploring/*` files that were renamed to `made/` (git detects as renames).

### 3.6 Task #13 — Phase 6-7: merge commit + REPL smoke

After all tests green on default stack:
```
cargo test --workspace  # must pass
cargo run -p mettail-repl -- calculator-casting.txt
cargo run -p mettail-repl -- rhocalc-casting.txt
# Plus any feature-branch-added examples.

# Stage + commit
git status --short  # review
git ls-files -u | awk '{print $NF}' | sort -u | while read p; do git add -- "$p"; done
git add <unresolved conflict resolutions>  # per A.1/A.2 of the merge plan
git commit  # editor opens with the merge summary
```

Commit message scaffold (per `wobbly-dazzling-sifakis.md` plan):
- Mention: main features preserved (numeric types, literals{}, bitwise, HashMap, BigInt/BigRat/Fixed).
- Mention: feature features preserved (WFST/CPS/CESK, predicated types, tokens{}, guards{}).
- Mention: TokenFamily typed-dispatch refactor, Token::Integer(i64, IntSuffix) suffix tag.
- Mention: PDA stack-safety refactor (try_eval, eval, normalize native types and Proc/Name, subst/unify_freevars, MApply display, flatten helpers) — deep inputs (10k+ nodes) parse + eval on default 2 MB stack.
- Mention: peak rustc RSS reduced from 96 GB → X GB if re-measured.

### 3.7 Task #40 — Bit-parallel DFA minimization (POST-MERGE BACKLOG — do NOT do before merge commits)

### 3.8 Task #41 — HOL-B v2 structural gating (POST-MERGE BACKLOG)

---

## 4. Currently-failing tests (minus PDA-fix-dependent)

As of the last full-suite run (test 19 + test 20 after #56 landed):

| Test | Cause | Fix |
|---|---|---|
| `test_bool_from_list_elem` | Stack overflow, root cause is Task #62 subst mutual recursion | #62 |
| `test_bool_from_uint_bigint_bigrat` | #56 strict suffix-match rejects `bool(0u32)` — Ambiguous-dispatch cross-cat fallback missing | Parser-layer Ambiguous-dispatch: when Int::parse rejects suffixed token, try UInt32/BigInt before erroring. See `prattail/src/dispatch.rs` cross-cat fallback. |
| `test_cast_uint_modular_u32` | Same as above — `uint(257u32, 8)` picks Int dispatch first | Same fix |
| `simulator_regression_cross_cat_dispatch_chaining` | Related to Ambiguous + dispatch ordering | Same fix |
| `test_map_keys` | HashMap non-deterministic iteration | #58 |
| `test_map_values` | Same | #58 |

All other calc tests pass. Rhocalc / ambient / lambda / guarded_rho test suites NOT yet re-verified post-PDA (run `cargo test --workspace` after #62+#63 land).

---

## 5. Pitfalls encountered this session (avoid in continuation)

1. **SIGABRT hides backtraces.** Rust's stack-overflow detector runs `rust_runtime_on_stack_overflow` which writes the message and calls `abort()` with no room for a backtrace. `RUST_BACKTRACE=full` does NOT help. To diagnose: use `gdb` attach, or add `eprintln!(depth)` instrumentation before committing to a fix.

2. **`cargo test` with multiple positional test names fails.** Use `--exact` per test, or a substring filter, or `--skip <name>` for the opposite.

3. **Pattern `&**arg` fails for `Vec<Cat>` elements.** `args.iter()` yields `&Cat` (not `&Box<Cat>`), so `&**arg` tries to deref `Cat` which doesn't impl `Deref`. Use `arg as *const _` instead.

4. **`match elem { Cat::Label(inner) => ... }` fails for `Cat: Drop`.** The match tries to move `inner` out, violating Drop. Use `matches!(&current, Cat::Label(_))` + `if let Cat::Label(inner) = &current` (ref pattern on `&Cat`).

5. **Build `cargo test` runs `cargo build` first, which regenerates macros.** Iteration time is ~10-15 min per cycle on this codebase (calculator's 24k-line generated test file is expensive to compile). Plan commits that can land independently; avoid sequencing many small changes that each trigger full rebuilds.

6. **Token::Integer schema change (2 fields vs 1) broke `token_variant_id` emitter** (`automata/codegen.rs:2296-2308`) — had to special-case the 2-field family. Any future schema changes to Token variants must sweep `TokenFamily::has_payload()` *and* the 2-field special case.

7. **Ambiguous preservation + strict suffix matching interact badly.** When `from_alternatives` preserves alternatives and `Int::parse` rejects suffixed-mismatch tokens, the parser's dispatch machinery must try OTHER categories' parsers as fallback. Current code commits to the first category's parser and errors. This is NOT a PDA issue — it's a separate parser-layer fix for Ambiguous Fallback-on-Failure dispatch.

8. **Recursive fallback in emitters is a latent time bomb.** Whenever a classifier returns None (can't handle a rule), the existing eval.rs falls back to recursive `match self`. ANY grammar change that trips the classifier silently regresses stack safety. Task #61 replaces these fallbacks with `compile_error!` so the issue surfaces at macro-expansion time.

---

## 6. Exact file paths + function names for the continuation

### Task #62 (subst PDA)

**Modify:**
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/term_ops/subst.rs` — entire rewrite. 1715 lines.

**Template:**
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/term_ops/iterative_clone.rs` — 1412 lines, same structure as target.

**Functions to delete + replace:**
- `generate_substitution` (public entry, line 100) — rewrite to emit the new driver + wrappers.
- `generate_env_substitution` (line 117) — rewrite.
- `generate_unify_freevars_arm` (line 258) — merge into driver as `Unify` op variant.
- `generate_subst_by_name_arm` (line 460) — replace with driver's Visit arms.
- `generate_category_substitution` (line 735) — replace with thin-wrapper emitter.
- `generate_subst_impl` (line 1169) — merge into driver.
- `generate_subst_arm` (line 1357) — obsolete.
- `generate_var_subst_arm` (line 1408) — merge into driver's Var handling.
- `generate_regular_subst_arm` (line 1431) — merge into driver's Regular Visit arm.
- `generate_collection_subst_arm` (line 1489) — merge into driver's Collection Visit arm.
- `generate_binder_subst_arm` (line 1529) — merge into driver's Binder Visit arm.
- `generate_multi_binder_subst_arm` (line 1624) — merge into driver's MultiBinder Visit arm.

**New functions to emit:**
- `generate_any_subst_term_enum(language)` — emits `enum AnySubstTerm { Wrap<Cat>(<Cat>) for each cat }`.
- `generate_subst_task_enum(language)` — emits `enum SubstTask<'a> { Visit_<Cat> { … } per cat, Assemble<Cat>_<Label> { … } per rule }`.
- `generate_subst_op_enum(language)` — emits `enum SubstOp<'a> { SameCatSubst, CrossCatSubst_<Repl>, EnvSubst_<Repl>, Unify }`.
- `generate_subst_iterative_driver(language)` — emits the main `fn subst_iterative(...)`.
- `generate_subst_wrappers(language, category)` — emits all 13 public method wrappers per category.

**Entry (top of `generate_substitution`):**
```rust
pub fn generate_substitution(language: &LanguageDef) -> TokenStream {
    let tls = generate_subst_tls_pools();
    let any_term = generate_any_subst_term_enum(language);
    let task = generate_subst_task_enum(language);
    let op = generate_subst_op_enum(language);
    let driver = generate_subst_iterative_driver(language);
    let wrappers: Vec<_> = language.types.iter()
        .filter(|t| t.exported)
        .map(|t| generate_subst_wrappers(language, &t.name))
        .collect();
    quote! { #tls #any_term #task #op #driver #(#wrappers)* }
}
```

### Task #63 (non-native normalize PDA)

**Modify:**
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/term_ops/normalize.rs` — non-native branch starting line 454. Native branch (lines 140-422) already PDA, untouched.

**Template:**
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/term_ops/iterative_clone.rs`

**Functions to replace:**
- Match-arm generator logic inside `generate_normalize_functions` (lines 454-751) for non-native categories only.
- `generate_beta_reduction_arms` (line 762) → emit `AssembleBetaApply_<Cat>_<Dom>` frames instead of recursive arms.
- `generate_cancellation_pair_arm` (line 644) → emit `AssembleCancel_<Outer>_<Inner>` frame.

**Reuse:**
- `generate_flatten_helpers` (line 12-102) — already iterative per Task #63c (5c).

### Task #61 (compile_error cleanup)

**Modify:**
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/native/eval.rs:718-723` — replace recursive fallback with `compile_error!`.
- Remove any `legacy_generate_*` dead code in `subst.rs` and `normalize.rs` after #62, #63 land.

---

## 7. Test suite state

To measure post-completion:
```
# Native 2MB stack — must pass without RUST_MIN_STACK override:
cargo test -p mettail-languages --test calculator
cargo test -p mettail-languages --test rhocalc
cargo test -p mettail-languages --test ambient
cargo test -p mettail-languages --test lambda
cargo test -p mettail-languages --test guarded_rho

# Full workspace:
cargo test --workspace

# Deep-recursion regression tests to add:
# `languages/tests/deep_pda_regression.rs`
#   - test_subst_deep_cross_cat_proc_int_alternation_1000
#   - test_normalize_deep_apply_chain_1000
#   - test_normalize_church_numeral_100_successor
```

---

## 8. Task status summary (authoritative)

| ID | Status | Subject |
|---|---|---|
| #52 | completed | Group E: Option→Err wiring in HOL step rules |
| #53 | completed | Group D: Factorial errors on negative |
| #54 | completed | Group B.1: Preserve display-equal alternatives |
| #55 | completed | Group B.2+C: Ambiguous recursion in substitute_env |
| #56 | completed | Group A Option 2: Token::Integer suffix tag |
| #59 | completed | PDA classify zero-ary + non-native cross-cat |
| #60 | completed | PDA eval() via try_eval().expect() |
| #64 | completed | PDA display.rs MApply fix |
| #63 | **pending** (partial: native normalize + flatten helper done; Proc/Name non-native remains) | PDA normalize iterative rewrite |
| #62 | **pending** (not started — PRIORITY) | PDA subst iterative rewrite |
| #61 | pending (blocked on #62, #63) | compile_error! on unclassifiable rules |
| #58 | pending | HashMap ordering flakes (map_keys, map_values) |
| #11 | pending | Merge miscellaneous (.gitignore, docs) |
| #13 | pending | Phase 6-7: git commit merge + REPL smoke |
| #40 | pending (POST-MERGE BACKLOG) | Bit-parallel DFA minimization |
| #41 | pending (POST-MERGE BACKLOG) | HOL-B v2 structural gating |
| #12 | in_progress (wraps up on #62+#63 green) | Phase 5: Test suite passes |
| Earlier tasks #1-#51 | all completed — see TaskList |

---

## 9. Pre-session context (for reference)

The merge `main` → `feature/wfst-architecture` was structurally complete before this session started. This session focused on:
- Finalizing content-level merge work (Groups A-E).
- Introducing PDA stack-safety for deep-input handling (the reason `test_try_eval_deep_mixed_ops_1000` previously required `RUST_MIN_STACK=16M`).

The merge commit is blocked ONLY on Task #62 (subst PDA) landing cleanly so that `test_bool_from_list_elem` passes on default 2 MB stack.

See also:
- `/home/dylon/.claude/plans/wobbly-dazzling-sifakis.md` — original merge recovery plan.
- `/home/dylon/.claude/projects/-home-dylon-Workspace-f1r3fly-io-mettail-rust/memory/*` — session memory files covering feedback, design decisions, architectural context.
