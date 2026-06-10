# Evidence-Gated Cross-Cat Dispatch — the FV-derived fix for cast-then-compare (Task #21 / Phase 5A)

> Status: **DESIGN (FV-grounded), pre-implementation.** `feature/wfst-architecture @ 32fbf254`.
> Supersedes the post-resolution approach (efec0eb7's reentry synth + this session's reverted
> projection/direct-injection/EOI-salvage experiments), which formal verification proved
> **insufficient** for the output injection. Authored 2026-06-10 after the user-chosen pivot.

## 1. The problem, and why the post-resolution path cannot close it

The cast-then-compare family — `int(3) == 3`, `float(3) >= 3.0`, `cast_error_fixed != 0.0`, and the
`comparison_after_cast_results::*` / `operator_chains_after_casts::*` / `string_edge_cases::*` /
`gen_calculator_op` `*casterrfixed*` / `rhocalc int_of_float_add` cluster — fails because a
**category-changing infix** `op : c → d` (e.g. `EqInt : Int "==" Int → Bool`, `NeFixed : Fixed → Bool`)
cannot attach to a **cast result** operand.

Calculator categories: `Proc=0, UInt32=1, Int=2, BigInt=3, BigRat=4, Fixed=5, Float=6, Bool=7`.
`Proc` is the start category; each category `X` injects to `Proc` via a `ProcX` rule
(`ProcBool = Proc::=Bool = (cat 0, rule 2)`).

The literal `3 == 3` works: the root dispatches the **cross-cat-LHS delegate** for `3` — the
`ProcBool ← EqInt ← Int-LHS` chain — so the cursor parsing `3` is a *Bool-context worker*; when `EqInt`
fires, the `Bool[0,3]` result is hosted by that worker's continuation (`ProcBool`) → `Proc[0,3]` root.

The cast `int(3)` is **denied that chain**: the lex-fork (`forks.rs::emit_lex_fork_at_prefix_dispatch`,
the `51d57c91` keyword-reservation fall-through) routes the cast keyword `int` to the *single* cast arm
(`Int ::= "int" "(" … ")"`), **bypassing** the Pass-0 `CrossCatLhs{Int}` arm
(`prefix.rs::emit_unified_arm:1301-1323`) that exists for it. So `int(3)` is parsed by an *Int-context
worker* (`ProcInt`).

**The FV-proven wall (`CastRehostOutputProjection.v`, this session):** a worker's continuation injects
its **dispatch-time** category. The Int-context cast worker injects `c=Int`, **never** `d=Bool`. The
hosting law (`CastCompareFrontierBound.hosting_requires_return_cat`) says the `Bool` result is hosted
iff its return-context is `Bool`. A *post-resolution* fix can re-host the GSS **frame**
(`rehost_accepts`) but **cannot change the worker's continuation**
(`rehost_preserves_cont`, `rehosted_cast_worker_still_cannot_host_d`). Empirically (this session):
synthesizing a `CrossCatProjection{wrap=(0,2)}` frame + a direct `intern_coercion_over_body` DID intern
the correct `Proc[0,6]` SPPF root — but EOI acceptance is **cursor-based** (`is_accepting_config`,
`wpda_walker.rs:5978/4482`), so no accepting cursor surfaces it, and an EOI SPPF-salvage realized empty
(deeper reconstruction glue). Layer after layer = the architecture rejecting a post-resolution output
injection. **The FV predicted this.**

⇒ The output injection requires a **dispatch-time `d`-worker**. That is the pivot.

## 2. The FV-derived solution: dispatch-time, lookahead-gated, merged cross-cat-LHS delegate

Route cast triggers into the cross-cat-LHS delegate **at dispatch** (exactly as the literal `3` is),
so the worker IS a proper `d`-worker — the output injection is then native, no glue. Two dangers, each
fenced by an existing zero-admission model:

- **Blowup** — speculating the delegate for *every* `c`-sourced category-changing infix, re-parsing
  the cast body per speculation, is `K^depth` on nested casts (the **falsified** naive fall-through:
  327 cursors / 10 regressions). Fenced by:
  - **`CastLookaheadGateBound.v`** — dispatch the delegate for infix `op_i` **only when the lookahead
    token ∈ FIRST(`op_i`'s trigger)**. Definite, monotone-under-continuation evidence (the trigger is
    literally in the input), so it drops no parse the input admits (`gated_no_loss`), and the surviving
    frontier = the *actual* infix triggers in the input, depth-independent
    (`gated_counts_actual_infix_triggers`, `gated_at_most_one`). Prunes the `K` factor at the source.
  - **`CastDelegateMergeBound.v`** — share ONE delegate across the source cat's category-changing
    infixes, keyed by `(source_cat, position, operand)`, collapsing `K^depth → S depth` (linear:
    `merged_linear`, `merge_bounds_blowup`, `naive_unbounded`) **without losing coverage**
    (`merge_preserves_coverage`, `merged_fires_all_source_infixes`).

- **Orphaned output** — the worker-identity obstruction of §1. Resolved *by construction*: the
  dispatch-time delegate makes the worker a `d`-worker, and **`CastRehostOutputProjection.d_worker_hosts_d`**
  proves a `d`-worker hosts `d` → accepting `Proc` root. (`direct_fix_overrides_worker_identity`
  records that this is the sound completion the post-resolution path could not reach.)

**Composition (the implementation contract):** the dispatch-time gated+merged cross-cat-LHS delegate is
SOUND (`d`-worker hosts `d`), COMPLETE (lookahead-gate is no-loss), and BOUNDED (merge → linear). This
is the conjunction of `CastLookaheadGateBound` ⊕ `CastDelegateMergeBound` ⊕
`CastRehostOutputProjection.d_worker_hosts_d`. **NEXT FV step (do first, before code):** a unifying
`CastDispatchHostResolution.v` that states this composition as one theorem over the concrete dispatch
event (a cast trigger at position `p` with the input's following infix triggers), so the implementation
transcribes a single verified contract.

This also realizes the broader **pipeline state-space-control** goal (Task #21's original scope):
evidence-gated dispatch prunes the speculative frontier at the source, and cohort-merge + demand-bounded
realization bound its memory — the "pull evidence earlier + clean up the state-space at each seam"
direction, generalized beyond casts.

## 3. FV model inventory (all zero-admission, `rocq-prattail-wpda` green)

| Model | Commit | Proves |
|---|---|---|
| `CastCompareFrontierBound.v` | a26a2b54 | hosting law; `approach_a_rejects` (recognition approach unsound) |
| `CastDelegateMergeBound.v` | 629e9759 | merge `K^d → S d`, coverage-preserving |
| `CastLookaheadGateBound.v` | 95ff146b | lookahead-gate no-loss, frontier = actual triggers |
| `CastLookaheadHostSynthesis.v` | 9d853b47 | unified post-resolution synth spec (input side) |
| `CastRehostOutputProjection.v` | 32fbf254 | **worker-identity: post-resolution insufficient; `d`-worker hosts `d`** |
| `LexForkKeywordReservation.v` | 51d57c91 | the keyword-reservation fall-through (the lex-fork being modified) |
| `CastDispatchHostResolution.v` | *TODO* | **the composition: gated+merged dispatch ⇒ sound·complete·bounded** |

## 4. Mechanism map (sites, from this session's trace investigation)

- **lex-fork** `forks.rs::emit_lex_fork_at_prefix_dispatch` (`:427-430`): the `__fall_through` routes a
  cast keyword to the single cast arm. The `prefix_primary_has_dispatch_rule(state_cat, kind)` gate
  (`kind_dispatch.rs:134-199`) covers only *same-cat primary* rules, so for a cast trigger in a
  *consuming* category's state it does not fall through to that category's `CrossCatLhs` arm.
- **Pass-0 cross-cat-LHS arm** `prefix.rs::emit_unified_arm` (`:1293-1323`); buckets are keyed by
  `(token pattern, state_cat guard)`; the `CrossCatLhs{source}` descriptor for a cast trigger DOES
  exist (Pass-0 `:949-976` adds the source cat's FIRST). The lex-fork must stop bypassing it.
- **cohort (merge) machinery** in `wpda_walker.rs`: register/pause/revive at
  `allocate_uncached_push_child:14669`; resolve at `cursor_gss_pop_via_edge:15869`; revive at
  `revive_cohort_member_with_snapshot:15218`; `DispatchKey{pos, source_src_idx, inner_cur_bp,
  wrap_cat, wrap_rule}`; `pending_cohort_drain_keys`. The merge keys the delegate by
  `(source_cat, position)` and shares across `wrap_rule` (the infix), per `CastDelegateMergeBound`.
- **EOI acceptance** `is_accepting_config:5978` / `resolve_at_end_of_input:4532` — cursor-based; the
  dispatch-time `d`-worker reaches it naturally (no salvage needed).

## 5. Implementation plan (each step zero-admission + baseline-relative gauntlet)

1. **`CastDispatchHostResolution.v`** — the unifying composition theorem (§2). FV first.
2. **Lookahead-gate predicate** (codegen or runtime): at the operand frontier, the set of
   `c`-sourced category-changing infixes whose trigger is the lookahead. Transcribes `gated_*`.
3. **lex-fork → cross-cat-LHS for cast triggers**: stop bypassing the Pass-0 `CrossCatLhs` arm for
   keyword/ident-ambiguous cast triggers, *gated* by (2) so only triggered infixes dispatch.
4. **Cohort-merge the delegate**: key by `(source_cat, position)`, share across `wrap_rule`; one
   shared cast-body parse, fanned to the surviving infixes at reentry. Transcribes
   `merge_preserves_coverage`.
5. **Verify**: `cast_probe` (`int(3)==3`, `float(3)>=3.0`, `cast_error_fixed != …`, nested casts for
   no-explosion); op-suite diff vs `prattail/docs/theory/formal-verification/baseline-cf03e571-failures.txt`
   (217); `-3!` canary; prattail-lib gauntlet; `gen_calculator_op` + `gen_rhocalc_op` + `edge_case_tests`.

## 6. Open risks

- The lex-fork change is the one that historically exploded — it must land **together** with the
  gate (2) and merge (4), never alone (the falsified path). The unifying model (1) is the gate against
  re-falsification.
- The merge key `(source_cat, position)` must not over-merge cursors that differ on a load-bearing axis
  (the `CohortQuotient`/`ConfigKey` discipline); `CastDelegateMergeBound.merge_preserves_coverage` is
  the soundness obligation to transcribe faithfully.
- Recovery/prefix-trailing tests (`resolve_prefix_with_trailing`) must stay green — the dispatch-time
  fix should not perturb the no-accepting-cursor salvage path.
