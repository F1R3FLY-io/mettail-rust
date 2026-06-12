# EVIDENCE-DRIVEN EARLY PRUNING — Staged Implementation Program

> **Status:** v3 (2026-06-11) — both round-2 critics folded. Soundness round 2 (0 BLOCKER,
> 4 MAJOR): N1 semantic_root hoist STRUCK (category error); N2 whole-stack `stack_fully_modeled`
> guard; N3+N4 `repair_synthesizable_classes` over-approximation incl. SUBSTITUTE; N5
> `source_priority` hypothesis + `rule_at_pop_implies_must_consumed` lemma. Effectiveness round 2
> (1 BLOCKER fixed in-commit, 3 MAJOR): the walker-stats build break was repaired INSIDE ROOT-A
> (9fdaed68) + I6 gains a `--features walker-stats` build gate; **P2's DAG-node lattice masks are
> the CRITICAL PATH** (the cast corpus routes through `LatticeTokenSource` — a linear-only gate
> would never fire on its own target corpus); **P3 is DEMOTED to inventory + diagnostic-only**
> (entry gate predicted to fail ~5×; the weighted by-product struck as a P4 input — skeleton-model
> bound is not admissible over the real frontier); minors m-1..m-4 (stats_inc_idx!, `must`
> totality over SymbolKind, non-zero-slot printing, bench panel fit). Full record:
> `03-red-team-ledger.md`. Next: round 3 — verify the fold, hunt residue, drive to convergence;
> THEN the FV models land (model commit precedes any Rust), THEN measure-first staged
> implementation.
>
> **v1→v2 changes (by finding):** I8 rewritten (B1: insertable-classes rule replaces the inverted
> `recovery_depth==0` guard); P1 goal re-attributed (F1: the "342,699" pathology is ROOT-A's, the
> number was an unsourced placeholder — all waste gates re-baseline POST-ROOT-A) + cohort-share =
> `EquivKey` reuse only (F2⊕m2: `wrap_rule` STAYS a discriminator); P2 `must`-fixpoint restricted
> to non-nullable positions (M1) + per-DAG-NODE masks (M2) + top-`RuleAt`-frame obligations on
> `WpdaGssNode` (F4) + per-literal trigger classes (F6); P3 gains a Step-(-1) transition inventory
> with an allow-list entry gate (B2⊕F3) + the cheaper `semantic_root_accepts` hoist weighed first
> (F8) **[STRUCK in v3 per round-2 N1 — category error; replaced by `category_reaches_accepting`]**; P4 ordering proofs get a real scheduler model (M3) + the within-step demotion invariant;
> P0 provisions the missing benches + battery scoping by commit class (F5); line refs replaced by
> function anchors (F9); I4 corpus adversarially seeded per failure mode (m1).
>
> **Repo:** `/home/dylon/Workspace/f1r3fly.io/mettail-rust` (branch `feature/wfst-architecture`)
> **Foundation docs:** `00-existing-mechanisms-inventory.md`, `01-sota-survey-filtering-approaches.md`,
> `docs/design/parser-fv/{evidence-driven-early-pruning.md, evidence-gated-cross-cat-dispatch.md}`

## 0. The frame (Kalman inspiration, made exact)

The walker is a Bayes filter whose belief support is the cursor frontier (survey §0.1). The Kalman
inspiration is realized in exactly two legal forms:

1. **Zero-posterior refutation** (the only legal drop): compute a sound over-approximation `β̂ ⊇ β`
   of the backward indicator `β(x) = [∃ accepting continuation from configuration x over the
   remaining input]`; remove a cursor only when `β̂(x) = 0`. Four abstraction levels of the remaining
   input, each level sound, each subsuming the previous: `α = ⊤` (Stage A, pre*-liveness),
   `α = token-class Parikh bitmask` (Stage B), `α = regular over-approximation DFA` (Stage D),
   `α = exact` (the parse itself). The Kalman "conjugate family" is the regular configuration
   language closed under `pre*`/`post*` (BEM97/EHRS00/RSJM05) — already implemented in
   `prattail/src/wpds.rs` (`prestar` at :1073, `poststar` at :835, `build_wpds` at :425).
2. **Posterior-weight ordering** (never thresholding): forward weights and admissible completion
   bounds ORDER work (Stage C); innovation/ESS diagnose and demote, never drop (Stage E). Soundness
   is the support-homomorphism argument already proven as `EvidenceComplete.weight_is_order_only`;
   the forbidden move is already characterized as
   `EvidenceComplete.weight_drop_can_lose_valid_alternative`.

## 1. Program invariants (apply to EVERY stage; violation = stage rejected)

- **I1 (no-loss):** removal only via definite, monotone-under-continuation evidence or exact
  observational-equivalence collapse. Every gate's Rocq model proves `refute_definite`,
  `monotone_under_continuation`, `no_loss` (w.r.t. the actual input), and `frontier_shrink` or
  `set_preservation`.
- **I2 (FV-first):** the Rocq model lands as its own commit BEFORE any Rust, in
  `formal/rocq/prattail_wpda_runtime/theories/` (or `dovetail/formal/rocq/theories/` for P6a),
  registered in `_CoqProject`, Rocq 9.1 (`From Stdlib Require ...`), zero `Admitted`/`Axiom`
  confirmed by `Print Assumptions` on every exported theorem.
- **I3 (measure-first):** every stage opens with a Step-0 diagnostic commit (counters only,
  `#[cfg(feature = "walker-stats")]` + `stats_inc!`/`stats_add!` per
  `prattail/src/walker_stats.rs:2110/2124`, report block in the `Display` impl following the H13
  format at walker_stats.rs:1647 `"... — gate ≥ X% to proceed"`). Accept/stop gates are stated below
  per stage; a STOP is a recorded outcome (precedent: H13 EdgeKind 0.6% vs ≥60% → STOPPED; CD06 →
  "STOPPED at diagnostic-only", commit f7afa448).
- **I4 (shadow-mode soundness check):** every DEFINITE gate runs first in shadow mode (count
  would-refutes, refute nothing) across the full battery; the counter `*_refuted_then_accepted`
  MUST be exactly 0 everywhere (a would-refuted cursor that later participates in an accepted parse
  = soundness bug). Only then may enforcement be enabled. **Counters are PARTITIONED by
  `WpdaState`-class × `recovery_enabled`** so a single hit in a rare state is never statistically
  buried (red-team m1/B2). **The shadow corpus is ADVERSARIALLY SEEDED** with one input per known
  definite-gate failure mode: (a) missing-operator input with recovery INSERT reachable for the
  obligated class, (b) Optional-skip input whose entered path contributes the union-unique class
  absent downstream (no-else `IfElse`), (c) multi-length lex-ambiguous input (`-3` style) driving a
  refutation, not just a presence test. Shadow soundness is battery-bounded — the Rocq model, not
  I4, carries the universal claim; I4 is the transcription check.
- **I5 (flip-experiment):** every enforcement lands with an env-var kill switch (precedent
  `B2_DISABLE` in `languages/examples/b2_chain_bench.rs`); Welch protocol: N≥15 trials/arm (N=51 for
  chain panels), `/tmp/welch_ttest.py`, two-tailed p<0.05; ACCEPT iff p<0.05 AND treatment mean <
  control AND zero behavioral diffs; non-target panels (chain_50/100/200 via
  `languages/tests/trampoline_tests.rs`) must be Welch-neutral or byte-identical hot path (the R4
  guard). Record each as a pgmcp experiment.
- **I6 (battery):** every commit that can change behavior runs: `gen_ledtest_op` **220/0 (SENTINEL —
  any failure aborts the stage)**, `gen_calculator_op` 1330/0, `gen_rhocalc_op` 530/1,
  `edge_case_tests` 227/2, `rhocalc_tests` 118/8, prattail lib 3980/0, plus the `-3!` canary
  (`postfix_binds_tighter_than_unary`), the cast probe set (`int(3)==3`, `float(3)>=3.0`,
  `cast_error_fixed != 0.0`, `int(float(int(3.14)))` nested tower), and `rocq-prattail-wpda` green.
  Baselines are pinned BY COMMIT HASH at each stage start (see §8 — they shift when #307 ROOT-F
  lands).
- **I7 (reuse-first):** each stage names the existing mechanism it generalizes; net-new machinery
  requires a written justification of why no existing mechanism extends.
- **I8 (recovery composition — REWRITTEN per red-team B1; the v1 `recovery_depth == 0` guard was
  INVERTED and unsound):** depth-0 is the recovery-ELIGIBLE state (`child_recovery_depth =
  depth+1`, wpda_walker.rs `recovery fork`), and recovery INSERT *fabricates* tokens (cost 2.0,
  recovery.rs) — so an obligation class absent from the actual suffix can still be SUPPLIED by a
  future repair, and `S_{i+1} ⊆ S_i` is false across an INSERT. The sound rule: **a definite gate
  may refute on a missing obligation class ONLY IF that class cannot be fabricated by recovery**
  — formally, every definite-gate model carries
  `refute ⇒ must(x) ∩ repair_synthesizable_classes = ∅` (round-2 N3+N4 corrections):
  - **`repair_synthesizable_classes`** covers ALL class-synthesizing repairs — INSERT, SUBSTITUTE
    (reinterprets the current token as any sync token; recovery.rs:889-905), and CategorySwitch —
    not INSERT alone (the v2 "INSERT is the one repair class" sentence was FALSE; all three draw
    from `sync_tokens`).
  - It is a **conservative OVER-approximation, per-cursor-context**:
    `repair_synthesizable_classes(cursor) ⊇ ⋃ { sync_tokens(c) : c reachable-recovery category }`,
    with the safe upper bound = the union over ALL categories' untightened sync sets
    (`tightened_sync_tokens` only shrinks; scoping to the CURRENT category is UNSOUND
    mid-`CrossCatLhsReentry` where the state-category and the reachable recovery category differ).
    ∅ when recovery is disabled — gates unconditionally applicable then.
  - **Stated consequence (effectiveness honesty):** `sync_tokens` includes every grammar terminal
    of the category — operator literals (`==`, `>=`) AND structural delimiters — so under
    recovery-ON, P2 refutation on infix-trigger obligations is suppressed almost everywhere;
    **P2's measurable win is the `recovery_enabled = false` partition**, and the accept/STOP gate
    evaluates that partition.
  - DELETE/SKIP repairs only shrink the suffix (verified monotone-safe: `S[next_pos] ⊆ S[pos]`,
    masks live on the immutable shared LexDag); INSERT holds `cursor.pos` fixed while fabricating
    a phantom class — covered by the disjointness side-condition.
  Implementation: intersect the `must`-mask with the non-synthesizable complement BEFORE any
  refutation test. Shadow counters partition by `recovery_enabled` (I4).
  `resolve_prefix_with_trailing` + `recovery_integration_tests` + a missing-operator INSERT probe
  + a junk-token SUBSTITUTE probe (`int(3) X 3`) are battery members for this reason.

## 2. Stage ladder (validated and corrected from the sketch)

The pre-sketched ladder is structurally right (0 → B → A → C/E → D); three corrections from ground
truth:

- **Correction 1 (Stage 0 is partially shipped):** commit 82310a24 already landed the d1
  cross-cat-LHS fall-through + the whole-suffix trigger-presence gate
  (`prefix_crosscat_lhs_trigger_ahead`, `kind_dispatch.rs:188-213`) with zero-admission model
  `CastLexForkCrossCatLhsGap.v` (`d1_restores_hosting`, `gate_no_loss`,
  `gate_zero_overhead_when_absent`, `gate_kills_tower_blowup`, plus `d2_*` and `d1_d2_delta`
  characterizing what d1 misses). Furthermore
  `CastLookaheadGateBound.gating_subsumes_per_position_merge` proves gating subsumes the
  per-position merge — so the cohort-share half of Stage 0 is **conditional on measurement** (do not
  build the CrossCatLhs cohort merge unless duplicates are measured; the existing cohort merge
  engages only for `WpdaState::CrossCatDelegate`).
- **Correction 2 (Stage B is a generalization of shipped code, twice over):** the shipped trigger
  gate is (i) an O(n) suffix RESCAN per dispatch (kind_dispatch.rs:200-211 loops `pos+1..n` every
  call) and (ii) restricted to cross-cat-LHS triggers. Stage B replaces the rescan with one
  precomputed, monotonically-shrinking suffix-class bitmask (O(n) once per parse, O(1) per check —
  the `ContextWeight` u128-bitset style of `prattail/src/wfst.rs:249-621` reused) and widens the
  obligation set from "delegate triggers" to per-configuration `must`-classes. The 1-token/1-class
  projection theorem (`generalizes_trigger_gate`) makes the shipped gate a corollary.
- **Correction 3 (Stage C must fit the actual scheduler):** `step_fanout` (wpda_walker.rs:9950)
  steps ALL frontier members per step through the Tomita ingest/drain (:10014-10105) — there is no
  global pop-one priority heap. Stage C therefore claims only what the architecture supports: (a)
  realization order (already lex-min), (b) per-step iteration/demotion order and lazy-cohort
  scheduling, (c) admissible-bound-sharpened extraction. It does NOT restructure the walker into
  best-first-pop; that would be a separate program.

Ladder: **P0 prep → P1 (Stage 0) → P2 (Stage B) → P3 (Stage A) → P4 (Stages C+E) → P5 (Stage D,
residue-gated) → P6a dovetail / P6b eval (probe-gated)**. P2 and P3 Step-0 diagnostics can run
concurrently; enforcement is strictly sequential so each stage's measured residue attributes
correctly.

---

## P0 — Preparation (1 commit + coordination)

1. **Land the in-flight #307 ROOT-A work** (`ConsumeAtAndReplace` action + `MixfixLiteralAccounting.v`
   + forks.rs D2 sites). It touches the same files as P1/P2 (`forks.rs`, `wpda_walker.rs`,
   `engine_impl.rs`); starting before it lands guarantees conflicts. Do not begin P1 implementation
   commits until `git status` is clean on those files.
2. **Pin baselines:** record the exact battery numbers + commit hash in
   `docs/design/evidence-pruning/02-program-ledger.md` (new file, the program's running ledger,
   modeled on the Phase 5A ledger style).
3. **Shared scaffold commit:** add to `walker_stats.rs` an
   `// ── Evidence-pruning program (P-series) ──` section with the shadow-counter naming convention
   (`<stage>_shadow_would_refute_total`, `<stage>_shadow_refuted_then_accepted` — partitioned by
   `WpdaState`-class × `recovery_enabled` per I4, `<stage>_shadow_steps_after_would_refute`) and
   env-var convention (`PRATTAIL_EP_<STAGE>=off|shadow|on`, read once per walker construction).
   **Partitioned-counter mechanics (round-2 m-1):** `stats_inc!` takes a bare ident and cannot
   index — add a `stats_inc_idx!(self, field, idx)` macro (or direct indexed assignment inside
   `#[cfg(feature = "walker-stats")]` blocks, the `apply_action_variant_histogram` precedent) +
   `const WPDA_STATE_CLASS_COUNT: usize` sizing the `[u64; N]` arrays. **Display prints only
   non-zero slots** (round-2 m-3 — the report is already ~86 writeln!s; full 36-slot dumps per
   stage would be unreadable). No behavior change; battery must be identical (incl.
   `cargo build --features walker-stats` — now an I6 gate after the round-2 B-1 break).
4. **Bench provisioning (NEW per red-team F5 — the Welch gates have no panels otherwise):** create
   `languages/examples/cast_tower_bench.rs` (mirroring `b2_chain_bench.rs`: cast towers
   `int(float(int(3.14)))`[`== 3`] + the cast-then-compare probe set, `PRATTAIL_EP_*` kill-switch
   arms). `recovery_cohort_bench.rs` EXISTS (`languages/benches/`, Cargo bench table) but is
   panel-thin for P4 (round-2 m-4: 5 fixed cascading-error strings maximizing cohort-cache hits) —
   EXTEND it with zero-innovation ε/recovery-stall inputs (stall without consuming) + a
   `PRATTAIL_EP_P4_DEMOTE` kill-switch arm. Commit before P1.
5. **Battery scoping by commit class (NEW per red-team F5):** M (model) and L (ledger) commits run
   the FULL I6 battery; D (diagnostic) and I (implementation) commits run the SENTINEL
   (`gen_ledtest_op`) + the targeted panel + the `-3!` canary + the changed-surface suite, with
   the full battery deferred to the stage's L-commit. Line references in this plan are FUNCTION
   ANCHORS, not absolute line numbers (red-team F9: ROOT-A renumbers forks.rs/engine_impl.rs).

---

## P1 — Stage 0: evidence-gated + (conditionally) cohort-shared cross-cat-LHS delegates

**Goal (REWRITTEN per red-team F1):** the cast-then-infix *step-count* pathology is **owned by
ROOT-A** (mixfix part-0 literal accounting + unchecked kind=0 consume + EOI discard — fixed at
P0.1, commit pending), NOT by delegate over-spawning; the previously-cited "342,699 no-op steps"
was an unsourced session-memory placeholder and is RETIRED as a target number. P1's real, narrower
target: the **delegate FAN on cast-then-compare** (`int(3) == 3` class) — bound the number of
live CrossCatLhs delegates per (pos, source) via the gate (+ `EquivKey` merge only if duplicates
are measured), under the unified `evidence_gated_delegates` contract. ALL waste numbers and the
waste gate re-baseline on a POST-ROOT-A measurement (I3); P1's diagnostic commit produces the
first sourced numbers.

**Rocq model (commit 1):** `formal/rocq/prattail_wpda_runtime/theories/EvidenceGatedDelegates.v`
- Composes the four shipped models rather than re-proving them: parameters instantiate
  `CastLookaheadGateBound` (gate), `CastDelegateMergeBound` (merge bound),
  `CastDispatchHostResolution` (`dispatch_sound`/`dispatch_no_loss`/`merged_total_linear`),
  `CastLexForkCrossCatLhsGap` (`d1_subset_d2`, `d1_d2_delta`).
- New theorems: `gated_delegates_no_loss` (for every parse the actual input admits, the gated
  fall-through still spawns the hosting delegate — the d2 form, covering multi-token-prefix cast
  triggers d1 misses); `gated_delegates_frontier_shrink` (gated frontier ≤ number of actual
  infix-trigger occurrences in the suffix, depth-independent); `share_iff_duplicate`
  (cohort-sharing the CrossCatLhs delegate is coverage-preserving AND is the identity when the gate
  already yields ≤1 delegate per (pos, source) — the formal statement of why the merge is
  conditional); `gate_repair_disjoint` (I8).
- Soundness theorem = "never refutes a viable alternative" (`gated_delegates_no_loss`);
  effectiveness theorem = "refutes the measured waste class" (`gated_delegates_frontier_shrink` +
  `gate_kills_tower_blowup` reuse).

**Step-0 diagnostic (commit 2)** — counters in walker_stats.rs, instrumentation at the sites:
- `crosscat_lhs_fallthrough_considered`, `crosscat_lhs_fallthrough_gated_off` — at the d1 gate
  consultation, codegen site `macros/src/gen/runtime/wpda_codegen/forks.rs:412-472` (emitted gate
  calls into `kind_dispatch.rs:188`).
- `crosscat_lhs_delegates_spawned`, `crosscat_lhs_delegate_dup_at_pos_source` (the would-share
  measure: count >1 live delegate cursors at one `(pos, source_src_idx)`; instrument at
  `allocate_uncached_push_child` wpda_walker.rs:15007 and the Pass-0 push in `prefix.rs:1293-1323`).
- `cast_then_infix_steps` — `apply_action_calls` attributed to delegate-origin cursors via
  `cohort_origin` (pattern exists at step_fanout :9961-9987).
- **Probe inputs:** `int(3) == 3`, `int(3) + 3`, `int(3)`, `int(float(int(3.14)))`,
  `int(float(int(3.14))) == 3`, the `comparison_after_cast_results::*` /
  `operator_chains_after_casts::*` clusters.

**Accept/STOP gates:**
- d2 extension: implement iff the d1-vs-d2 delta is non-empty on the corpus (count fall-through
  considerations where `prefix_crosscat_lhs_has_dispatch_rule` hits only under d2's
  multi-token-prefix extension — counter `crosscat_lhs_d2_only_hits`); if 0 across the
  battery+corpus → record STOP (d1 suffices; `d1_d2_delta` stays a proven-but-unneeded reserve).
- Cohort-share: implement iff `crosscat_lhs_delegate_dup_at_pos_source` ≥ 10% of
  `crosscat_lhs_delegates_spawned` on any corpus input; else STOP (gate alone realizes the linear
  bound, per `gating_subsumes_per_position_merge`).
- Waste gate: `cast_then_infix_steps` on `int(float(int(3.14))) == 3` must drop ≥ 60% vs the pinned
  baseline when enforcement is on; if the diagnostic shows the remaining steps are NOT
  delegate-attributed, record and pass the residue to P2/P3.

**Implementation (commit 3, only for the measured-in parts — REWRITTEN per red-team F2⊕m2):**
extend the `emit_lex_fork_at_prefix_dispatch` `__fall_through` (forks.rs — function anchor, not
line numbers; ROOT-A renumbers the file) to the d2 predicate. If cohort-share passed its gate, the
ONLY admissible merge is the EXISTING `EquivKey` (`DispatchKey::equiv` = `(source_src_idx,
inner_cur_bp)`, dispatch_cohort.rs) — **`wrap_rule`/`wrap_cat` MUST remain cache-key
discriminators** (the M4 tombstone in the `DispatchKey` doc: collapsing distinct wrap rules at
`(pos, source, bp)` WAS the cast-family root cause; never re-widen). `share_iff_duplicate` is
stated over `EquivKey`-identical members only. Sites by function anchor:
`allocate_uncached_push_child` / `cursor_gss_pop_via_edge` / `revive_cohort_member_with_snapshot`.
Kill switch `PRATTAIL_EP_P1`. I7 discharge: P1 builds NO new merge machinery — gate (shipped) +
`EquivKey` (shipped) + d2 predicate (generated, already emitted) only.

**Flip experiment (commit 4 = ledger):** Welch N=15 on the cast-probe workload (a `cast_tower_bench`
example mirroring `b2_chain_bench.rs`); R4 neutrality on chain_50/100/200; full battery; record
experiment + gate decisions in the ledger.

> **★ AMENDED 2026-06-11 (user-approved via AskUserQuestion; red-team ledger Round 5).** The
> Step-0 D-commit measurements FALSIFIED commit-3's premise: `gating_subsumes_per_position_merge`
> claimed the gate alone realizes the linear bound, but with the gate correctly OPEN
> (trigger present, `gated_off=0`) the fan persists — 3,504 spawns / 3,500 duplicates on
> `int(float(int(3.14))) == 3`. The duplicates are REDUNDANT-VIABLE cursors (same valid
> sub-parse, genuinely distinct return frames): the EquivKey/ConfigKey merge cannot collapse
> them (they differ in real ConfigKey axes) and P2's zero-posterior refutation does not apply
> to viable cursors. The I7 wording ("NO new merge machinery") is therefore AMENDED for the
> trigger-present case: P1's implementation is a **cohort-style PARKING design** (parse the
> source once, park N return frames, broadcast), delivered as:
> (1) the sound SHADOW-measurement half first (observation-only full-key map + would-share
>     counters; never mutates the real cohort cache);
> (2) a NEW non-vacuous Rocq model commit (the parking/revive semantics: per-member
>     predecessor-dependent reentry as hypothesis, broadcast soundness as theorem — R5-8;
>     `EvidenceGatedDelegates.v` stays but is vacuous w.r.t. reentry fidelity);
> (3) design v2 with ALL Round-5 corrections (R5-1 dedicated member-tail revive; R5-2 wrap as
>     read-not-compared side payload; R5-3 capture-point inside `apply_pop_body_to_cursor`;
>     R5-4 attribution extended to `CrossCatLhsReentry` + full-key criteria; R5-5 singleton/
>     Fork member shapes separated; R5-6 EOI orphan design; R5-7 host-sourced wrap_cat),
>     re-red-teamed to convergence BEFORE implementation;
> (4) the flip experiment + ≥60% waste gate (commit 4) unchanged, with the R5-4-corrected
>     attribution.
> v1 of the parking design is REFUTED and fenced (04-p1-icommit-design.md; do not implement).

---

## P2 — Stage B: Parikh/suffix-obligation gate (zero-posterior refutation, token-class level)

**Goal:** refute a cursor the moment its outstanding obligations demand a token class absent from
the remaining input. Generalizes: the shipped trigger-ahead scan (1 class, rescan) → all
configurations, precomputed mask.

**Rocq model (commit 1 — CORRECTED per red-team M1, M2, F4, F6):**
`formal/rocq/prattail_wpda_runtime/theories/ParikhObligationGate.v`
- Token classes: **one distinct class per grammar-declared infix-trigger TERMINAL** (FIRST-of-infix
  granularity — `==` ≠ `>=`; red-team F6: coarser classes make the shipped-gate projection a
  strict weakening), plus coarse classes for the rest. The class alphabet size feeds the P3/P5
  byte budgets.
- `must : symbol → class-set` by the fixpoint `must(t) = {class(t)}`,
  **`must(A) = ⋂_{A→σ} ( ⋃_{s∈σ, nonnullable(s)} must(s) )`** — the union ranges over
  NON-NULLABLE RHS positions ONLY (red-team M1: `Optional` has an explicit skip path and `Sep`
  admits 0 iterations; the v1 unrestricted union over-claimed — counterexample: the skip
  derivation of `A → s₁ Optional[","s₃]` consumes no comma). `nonnullable` is the standard
  fixpoint ("every derivation of s consumes ≥1 token"), itself defined in the model.
- Obligations of a configuration: **the TOP `RuleAt` frame's `must` only** (red-team F4: the
  full-stack ⋃ requires walking the per-cursor `incoming_edge_stack` — NOT O(1) on the shared
  GSS). Theorem `top_frame_refutation_sound`: top-frame `must(x) ⊄ S[node]` already implies no
  accepting continuation (the full-stack union only ADDS classes, so the top-frame test is a
  sound weakening — refutation fires on a subset of the definite-dead set).
- Suffix masks are **per-DAG-NODE** (red-team M2: lattice positions are node-ids, `next_pos(pos,
  alt) = target_node`, NOT linear; two nodes can share a `byte_start`; orphans sit after EOF):
  `S : node → class-set` with edge-monotonicity `∀ alt: S[next_pos(node, alt)] ⊆ S[node]` — NEVER
  `nat`-successor monotonicity. New theorem `lattice_node_mask_welldefined` (the backward DP
  assigns exactly one mask per node-id; the gate reads `S[cursor.pos]` as a node-id, never a byte
  offset).
- Theorems: `must_consume_sound` (induction on derivations WITH the nonnullable hypothesis on
  each unioned position); `rule_at_pop_implies_must_consumed` (round-2 N5: every `RuleAt` pop is a
  COMPLETION that fires the rule action — verified: `emit_fire_action` on `SymbolKind::RuleAt`;
  `Unwinding`/`GroupingClosePreservingInner` pop only `Return`/`CategoryEntry` frames — the
  top-frame soundness silently depends on this, so it is a NAMED lemma); `gate_no_loss` (refute ⇒
  x is in no accepting parse of the actual suffix); `gate_monotone` (along DAG edges);
  `generalizes_trigger_gate` **as refinement ⊑** (the shipped d1 presence-gate refines into the
  1-class projection; equality only under the per-literal class assumption, which the class
  function above satisfies for trigger classes); `lattice_union_sound` (union over DAG paths sound
  for every path — Lang-1988); `lattice_node_mask_welldefined` includes the [REPAIR]-position
  clause (repairs never allocate DAG nodes; `cursor.pos` ranges over `dag.nodes` indices; INSERT
  holds pos fixed — the phantom class is covered by the I8 disjointness side-condition);
  `gate_repair_disjoint` (I8 v3 form: `refute ⇒ must ∩ repair_synthesizable_classes = ∅`).
- Soundness = `gate_no_loss` + `top_frame_refutation_sound`; effectiveness =
  `gate_refutes_absent_obligation` (refutation fires at the transition creating the obligation,
  not at EOI).
- I7 discharge (red-team F8): P2 generalizes TWO shipped mechanisms —
  `prefix_crosscat_lhs_trigger_ahead` (presence scan → mask) and
  `pos_in_absorbed_chain_interval` (the existing O(1) interval-membership refutation shape) — and
  sources classes from the existing `FirstSet`/`follow_inputs` machinery (prediction.rs), not a
  new analysis.

**Step-0 diagnostic (commit 2):**
- New module `prattail/src/suffix_classes.rs`: `SuffixClassMasks` built by one backward pass over
  the `WpdaTokenSource` (plain stream: O(n); lattice: backward DP over `LexDag` edges, union per
  node — O(|E|)). Class inventory and per-(category, rule, position) `must` masks emitted at codegen
  into `macros/src/gen/runtime/wpda_codegen/tables.rs` (alongside the existing category/rule tables)
  as `u128` consts — reusing the `ContextWeight` bit-assignment machinery (`wfst.rs:554-571`).
- Shadow counters: `parikh_shadow_would_refute_total`, `parikh_shadow_refuted_then_accepted`
  (**must be 0** — I4), `parikh_shadow_steps_after_would_refute` (steps spent on cursors after
  shadow refutation fired — the direct waste quantification), `eoi_dead_cursors_parikh_refutable`
  (of cursors dying at the premature-Accepted filter in `resolve_at_end_of_input`
  :4593/`is_accepting_config` :6039, how many were shadow-refutable earlier).
- Check sites (shadow): per-frontier, immediately after the Tomita drain in `step_fanout` where
  `node.shell` exposes `(inner_state, node, pos)` (wpda_walker.rs:10096-10105) — this pays the check
  ONCE PER MERGED CLASS (Candidate-F amortization for free); and per Fork-child at the
  `children.push` sites in `apply_action_to_cursor` (:7825+ Fork arm).

**Accept/STOP gates:** `parikh_shadow_steps_after_would_refute ≥ 20%` of `apply_action_calls` on
the pathological corpus (cast probes + ProcX root-fan inputs + post-ROOT-A rhocalc send/receive
corpus) → implement enforcement; `< 5%` → STOP (record; proceed to P3 diagnostics anyway, A and B
kill different classes). `parikh_shadow_refuted_then_accepted > 0` anywhere → hard stop, fix the
model/transcription first.

**Implementation (commit 3):** enforcement at the two shadow sites (refuted cursor →
`CursorOutcome::Drop` through `cursor_resolution_check`'s Drop path, with `stats` attribution
`cursors_dropped_via_parikh_gate`); replace the `prefix_crosscat_lhs_trigger_ahead` O(n) rescan with
an O(1) mask test (semantics: refinement per `generalizes_trigger_gate` ⊑ — separate sub-commit so
it is independently flippable). Obligation source = the cursor's TOP `RuleAt` symbol on
**`WpdaGssNode`** (gss.rs `WpdaGss` — NOT the legacy `GraphStructuredStack`/`GssNode`, which is
dead on the hot path; red-team F4): `must` of `(category_src_idx, rule_index_in_category,
position)` is a baked-table lookup — genuinely O(1), no per-frame storage, sound per
`top_frame_refutation_sound`. **`must` is TOTAL over `SymbolKind`** (round-2 m-2): the obligation
function is defined for EVERY kind — `RuleAt` gets the rule-position mask; unconstrained kinds
(`Return`, `CategoryEntry`, `InfixContinuation`, markers) get the sound default `must = ∅`
(never-refute); `top_frame_refutation_sound` is proven over all variants, not just `RuleAt`.
**Lattice masks ARE the critical path** (round-2 M-1 REVERSAL of the v2 deferral — PROVEN:
`parse_via_wpda` routes through `LatticeTokenSource` whenever `dag.has_ambiguity()`, and the cast
corpus IS lex-ambiguous (`int` keyword/ident fork), so a linear-only gate would enforce NOTHING on
the very corpus its accept gate measures): `lattice_node_mask_welldefined` ships in the model
commit, the DAG-node mask table ships in the diagnostic commit, and shadow validation runs on
lattice inputs from day one; enforcement arms on BOTH source kinds once shadow is clean. Kill
switch `PRATTAIL_EP_P2=off|shadow|on`.

**Flip experiment (commit 4):** Welch N=15 cast-probe + rhocalc corpus panels; N=51 chain panels for
R4 neutrality; battery per I6; ledger + experiment record.

---

## P3 — Stage A: pre*-saturation configuration liveness (the Boolean Kalman / exact backward indicator at α = ⊤)

> **★ DEMOTED to inventory + diagnostic-only (round-2 M-3 decision):** the Step-(-1) transition
> inventory faces ≥15 must-add classes (18 `WpdaState` variants + the CrossCatLhs/Reentry/
> Projection-wrap transients) against the bare `(category, rule_label, position)` skeleton in
> `build_wpds` — the ≤K=3 entry gate is predicted to FAIL ~5×. P3 therefore executes ONLY:
> (1) the Step-(-1) inventory commit (valuable on its own — it is the transition census every
> later modeling effort needs), (2) the recorded STOP (expected), (3) the diagnostic-only shadow
> measurement (`prestar_shadow_incremental_over_parikh` over the modeled subset) to quantify what
> a future full model would buy. NO enforcement apparatus, NO allow-list build-out, NO
> `PreStarLiveness.v` beyond the inventory unless the gate unexpectedly passes. **The weighted
> by-product is STRUCK as a P4 input** — the weighted prestar runs over the SAME skeleton model
> and inherits the SAME abstraction hole, so it is NOT a valid admissible bound over the real
> frontier; P4's `admissible_bound_exact_first` either restricts to {in-model}-state cursors or
> drops the prestar bound (lex-min realization order needs no table).

**Goal (if the entry gate unexpectedly passes):** offline (codegen-time), compute the regular set
`pre*(AcceptingConfigs)` of the grammar's WPDA; at runtime, refute any cursor whose configuration
leaves the live set — input-independent death detected at the killing transition instead of EOI.

**Reuse (I7):** `prattail/src/wpds.rs` already implements `build_wpds` (:425), `prestar` (:1073,
worklist saturation), P-automaton membership queries (`is_symbol_accepted` :335,
`reachable_symbols` :398), consumed today by `lint.rs`/`cost_benefit.rs`/`pipeline.rs` at analysis
time only. Stage A = bake + runtime-check, not new saturation code.

**Step-(-1) — TRANSITION INVENTORY + the cheaper alternative (NEW, entry gate; red-team B2⊕F3,
F8):** before the model commit, two deliverables:
1. **Transition inventory:** enumerate EVERY `WpdaStepAction`/`WpdaState` transition class the
   runtime fires (~25 `WpdaState` variants incl. `MixfixContinuation`, `MixfixLiteralRun`,
   `CollectionLoop`/`CollectionOpenParen`, `BinderRule`/`BinderListLoop`, `OptionalGroup`,
   `GroupingMarker`, `CrossCatDelegate` + `CrossCatLhs`/`CrossCatLhsReentry` edges with wrap
   injection, `Unwinding`, `Saturating`, recovery forks, lex forks) and tag each:
   {in-model, restricts-only (proof sketch required), must-add-to-model}. **Entry gate:** ≤ K
   must-add classes (K decided at inventory time, default 3) — else P3 STOPs at the model with the
   inventory as the recorded negative. Honest prediction (recorded up front): liveness over the
   bare `RuleAt` skeleton is likely `α=⊤`-vacuous on intrinsic states, predicting
   `prestar_shadow_incremental_over_parikh < 3%` → STOP.
2. **The cheaper alternative weighed FIRST (REWRITTEN per round-2 N1 — the v2 wording proposed
   hoisting `semantic_root_accepts_at_cursor`, which is a CATEGORY ERROR: that predicate operates
   on a REALIZED single-Symbol SPPF root whose span ends at the cursor; at dispatch time no root
   exists, and a mechanical adaptation would refute every spawn with an unconsumed operand — the
   inverse contract):** the dispatch-time category-viability gate, if wanted, is a DISTINCT
   predicate `category_reaches_accepting(category, top_frame)` grounded in the pre*-live set
   (P3's own apparatus) or the existing `FirstSet`/`alt_compat_with_dispatch_cat` compatibility
   filter — NOT the EOI span predicate. It goes through the full I4 shadow ladder like any
   definite gate. P3's diagnostic still measures its would-refute coverage separately
   (`category_viability_would_refute`) to decide whether the full table apparatus earns its
   residual — but there is no shipped-predicate shortcut.

**Rocq model (commit 1):** `formal/rocq/prattail_wpda_runtime/theories/PreStarLiveness.v`
- `saturation_sound` / `saturation_complete` (on the model PDS: `x ∈ pre*(F) ⟺ ∃ accepting
  continuation` — transcribing the BEM97/EHRS00 saturation rules over a finite worklist, structured
  like the existing finite models, e.g. `FiniteHarness.v`);
- `abstraction_superset` — THE load-bearing theorem: the map from runtime configurations
  (`StackSymbolV2` stacks + `WpdaState`) to model configurations (`(category, rule_label,
  position)` stacks) is an over-approximation: every runtime-acceptable configuration maps into the
  model's `pre*(F)`. **Scoped by the Step-(-1) inventory** (red-team B2⊕F3, SHARPENED by round-2
  N2: the allow-list must be WHOLE-STACK, not current-state — the abstraction maps the entire
  stack, and a cursor in an allowed current state can carry frames pushed by unmodeled
  transitions; counterexample `{ int(3) == 3 | x }`: the operand cursor sits in a normal dispatch
  state with CollectionMarker + CrossCatProjection(wrap) frames below it, whose truncated/aliased
  model image can fall outside `pre*(F)`): the theorem is proven ONLY over the inventory's
  {in-model ∪ restricts-only} classes, and **enforcement carries a runtime
  `stack_fully_modeled(cursor)` guard** — refute only when EVERY frame symbol on the cursor's
  `incoming_edge_stack` AND the current `WpdaState` are in the proven-exact sub-alphabet.
  Implementation: a monotone "carries-unmodeled-frame" sticky bit per cursor, set at push of any
  `CollectionMarker`/`MixfixMarker`/`GroupingMarker`/`CrossCatProjection`/recovery/lex-fork frame
  (O(1) maintenance, no stack walk; cleared never — monotone). Shadow counters partition by
  fully-modeled-vs-not. Most dangerous unmodeled config (recorded): the `CrossCatLhsReentry`
  "re-push source above predecessor for one infix pass" transient on `int(3) == 3` — exactly the
  parse this program exists to enable;
- `refute_definite` (`x ∉ pre*(F)` ⇒ no accepting continuation on ANY suffix),
  `frame_annotation_correct` (carrying the P-automaton state per pushed frame and updating on
  push/pop = re-running the automaton on the stack; O(1) maintenance), `monotone_under_continuation`
  (input-independent ⇒ trivial), `gate_repair_disjoint` (I8).

**Step-0 diagnostic (commit 2):**
- Codegen: emit the saturated P-automaton as tables (`tables.rs` + `engine_impl.rs`):
  `PRESTAR_TRANSITIONS: &[(state, symbol_key, state)]`, `PRESTAR_LIVE: &[bool]`. Size counters
  `prestar_table_states`, `prestar_table_bytes`; budget: ≤ 64 KB per language, else
  STOP-and-compress (class the symbols first).
- Runtime shadow (RETARGETED per red-team F4): annotate at the push sites
  (`cursor_gss_push_with_kind` + the step_fanout Substage-5 broadcast push — function anchors)
  with the P-automaton state. **Storage target: the per-cursor `incoming_edge_stack` arena entry,
  NOT the shared `WpdaGssNode`** (GSS nodes are shared across cursors with different stack
  suffixes — a per-node annotation is ill-defined; the legacy `gss.rs GssNode`/
  `GraphStructuredStack` is dead on the hot path and must not be touched). One `u16` per
  edge-stack entry behind `#[cfg(feature = "walker-stats")]` for the shadow phase — per-frame
  storage acknowledged honestly; `frame_annotation_correct` is stated over the edge-stack arena.
  Mid-micro-loop reads (a `CollectionLoop`/`MixfixLiteralRun` consumes many tokens within one
  model position) must be proven CONSERVATIVE (live ⊇ actual) or liveness is checked only at
  push/pop boundaries (red-team m3). Counters `prestar_shadow_would_refute_total`,
  `prestar_shadow_refuted_then_accepted` (**must be 0**; partitioned by `WpdaState`-class),
  `prestar_shadow_steps_after_would_refute`, and crucially
  `prestar_shadow_incremental_over_parikh` (steps shadow-refuted by A but NOT by B — the
  marginal-value measure) + `semantic_root_hoist_would_refute` (the Step-(-1) alternative's
  coverage).

**Accept/STOP gates:** `prestar_shadow_incremental_over_parikh ≥ 10%` of `apply_action_calls` on
the corpus → implement; `< 3%` → STOP (record "A subsumed by B on these grammars"; keep the tables
emitted under a feature for future grammars, since A's weighted variant still feeds P4's bounds).
Table budget gate as above. Zero `refuted_then_accepted` everywhere.

**Implementation (commit 3) — CONDITIONAL: executes ONLY if the Step-(-1) entry gate unexpectedly
passes (round-3 Finding 1: under the demotion this subsection is INERT — the live P3 deliverables
are the inventory + the diagnostic shadow measurement + the recorded STOP):** promote the frame
annotation out of the stats cfg; enforcement at the same two per-frontier/per-child sites as P2;
`cursors_dropped_via_prestar_gate` attribution. Kill switch `PRATTAIL_EP_P3`.
**Weighted by-product — STRUCK as a P4 input (round-2 M-3):** the weighted prestar runs over the
SAME skeleton model and inherits the SAME abstraction hole, so its meet-over-all-paths completion
weight is NOT an admissible bound over the real frontier. Retained here only as the
conditional-pass artifact (if the inventory gate passes AND the weighted table is proven
admissible over the modeled subset, P4 may consume it restricted to {in-model}-state cursors).

**Flip experiment (commit 4):** as P2; additionally a ProcX-root-fan panel (the 12→16-cursor inputs
from inventory gap #1: category-viability death should now fire at dispatch).

---

## P4 — Stages C+E: evidence-weighted ORDERING + innovation/ESS reporting (order-only; kills nothing by construction)

**Rocq models (commit 1 — CORRECTED per red-team M3: the v1 "extends `weight_is_order_only`"
framing was a category error; that theorem models realize-side `from_alternatives` dedup, not the
walker scheduler. P4 needs a GENUINE scheduler model):**
- `formal/rocq/prattail_wpda_runtime/theories/ForwardOrderOnly.v` — models `step_fanout`'s
  per-step frontier TRANSITION (ingest → Tomita drain → per-member step → resolution checks →
  surviving set), NOT an abstract dedup list. Theorems: `step_permutation_invariant` (the
  surviving-cursor SET after one full step is invariant under iteration-order permutation of the
  frontier, INCLUDING the budget-sentinel and merge interactions — the load-bearing new proof;
  **round-2 N5 hypothesis:** `source_priority` is NOT in the Tomita `merge_disambiguator` yet
  survives first-arrival and is the dangling-else tiebreak in `merge_equivalent_cursors` — the
  theorem must carry the lemma "`source_priority` is a function of the disambiguator on
  merge-eligible tied-weight arcs" (likely true: traced merge-eligible arcs share lex
  provenance ⇒ share priority) OR `source_priority` is added to the merge predicate);
  `ordering_preserves_accepted_set` (corollary over the run fixpoint);
  `admissible_bound_exact_first` — **REVISED per the P3 demotion (round-2 M-3): the prestar
  weighted table is NOT available as the outside bound** (skeleton-model bound is not admissible
  over the real frontier). The theorem is stated EITHER restricted to {in-model}-state cursors
  (if the P3 inventory unexpectedly passes) OR for the table-free form: lex-min realization order
  alone (already shipped) — the walker-side port of dovetail's `NBestExtraction.v` ORDER theorem;
  cite `EvidenceComplete.weight_is_order_only` only for the realize-side half.
- `formal/rocq/prattail_wpda_runtime/theories/InnovationDemotionOrderOnly.v`:
  `demotion_preserves_accepted_set` — REQUIRES and states the invariant: **demotion permutes step
  order WITHIN a single `step_fanout` pass and never removes/defers a live member from the set the
  pass drains** (red-team caveat: a member deferred to a LATER step is invisible to the
  whole-frontier progress fingerprint and `!progress_made` can exit early — the safe-as-coded
  property holds precisely because `step_fanout` steps the entire frontier per iteration);
  `every_member_stepped_before_exit` (the `run_to_end_of_input` loop steps every live member at
  least once before any `!progress_made` exit); `ess_report_no_prune` (the report path mutates no
  frontier state). Counter `demoted_member_unstepped_at_exit` (must be 0).

**Implementation (commit 2; no Step-0 needed — order-only, the measure IS the flip experiment):**
- ESS: `walker_stats.rs` fold over normalized frontier weights, `frontier_ess_x1000` recorded at
  every `AmbiguityBudget` sentinel emission (decode site `resolve_at_end_of_input` :4654 and the
  budget check in `wpda_runtime.rs::CursorBoundingMode`) and at EOI; surface in the budget error
  report so "1 winner + noise" (ESS≈1) is distinguishable from genuine k-way ambiguity (ESS≈k).
  Always-on (it is a report; gate the computation behind the budget event so the hot path pays
  nothing).
- Innovation: per-cursor `consumed_since_last_check` flag (a cursor advancing only via ε/recovery
  edges in a window is "zero-innovation"); demotion = stable-partition the post-drain iteration
  order in `step_fanout` (innovating frontiers first) and prefer innovating members in lazy-cohort
  scheduling. Counter `zero_innovation_demotions`.
- Realization order is already lex-min-first; no change.

**Accept criteria:** battery IDENTICAL (zero diffs tolerated — order-only); Welch p<0.05 improvement
on at least one pathological panel (recovery-heavy `recovery_cohort_bench` and the cast/ProcX
panels) and neutrality elsewhere; if no panel improves, keep ESS reporting (diagnostic value) and
revert demotion (record STOP for the demotion half). Kill switch `PRATTAIL_EP_P4_DEMOTE`.

---

## P5 — Stage D: regular residual over-approximation gate (residue-gated endgame)

**Entry gate (measure-first, no model until it passes):** after P1/P2 enforcement (P3 is
diagnostic-only per its demotion), define
`residual_dead_steps` = steps spent on cursors that die at EOI minus P2-real-refuted minus
{P2-shadow ∪ P3-shadow}-refuted steps, measured on the corpus. Implement Stage D **only if** `residual_dead_steps ≥ 15%`
of `apply_action_calls` (the ALL(*) lesson predicts the cheap gates already took the volume;
expected outcome: STOP).

If it passes: **Rocq model** `RegularResidualGate.v` (`overapprox_superset` via the Mohri–Nederhof
strongly-regular transformation per category, `reject_definite`, `frame_state_compositional` —
per-frame entry-state save/resume on push/pop, `monotone_under_continuation`,
`gate_repair_disjoint`); **codegen** per-category superset DFAs over token classes (size-budgeted:
≤ 32 KB/category or STOP); **runtime** residual-DFA state per merged frontier (post-P1 merge,
post-Tomita — pay per class); same shadow→enforce→flip ladder; counters `residual_dfa_shadow_*`
mirroring P2. Order-sensitive kills (`== int(3)` where the trigger is BEHIND the cursor) are its
distinctive class — include those probes.

---

## P6a — Dovetail engine (saturation + extraction): explicit stages and non-goals

Ground truth: the extractor (`dovetail/src/extract.rs`) already ships Huang–Chiang exact lazy
k-best with an **admissible 0̄-inside reachability skip** (`with_heuristic`, backed by
`compute_inside_closed`/Newton-SCC — proofs `NBestExtraction.v`, `EnumerationCompleteness.v`,
`LazyFrontierOrder.v`, `OrderPreservingFraming.v`, `ExtractionOutcome.v`, and
`InsideWeightSccClosure.v`). That IS this program's Stage-C analog, already done.
Saturation (`dovetail/src/rules.rs`) reports `Converged`, `NodeLimit`, or `IterationLimit`
explicitly (`DovetailSaturation.v`) and prunes nothing.

- **DV-0 (probe, 1 commit):** counters `enodes_added_total` vs `enodes_in_extracted_derivations`
  (mark during extraction over the rhocalc eval corpus) + saturation share of eval wall-time.
  **Gate:** untouched-share ≥ 50% AND saturation ≥ 20% of eval wall-time → DV-1; else record
  non-goal.
- **DV-1 (only on gate pass):** demand-gated rule application — the magic-sets/demand
  transformation for e-graphs: apply a rule only when its LHS root class is in the demanded set
  (backward closure from extraction roots). Model
  `dovetail/formal/rocq/theories/Saturation/SaturationDemandGate.v`: `demand_closure_complete` (every e-class
  appearing in any derivation of any demanded root is in the demanded set — extraction-equivalence,
  the query-equivalence theorem shape of BMSU86), `demand_monotone`. This is a quotient-of-work, not
  a drop: undemanded classes are never extracted, so omitting their saturation changes no observable
  result.
- **Non-goal (recorded):** WTA-extraction outside-bound A* beyond the shipped inside-skip — only
  revisit if profiling shows `kth`'s heap dominates an end-to-end workload (no current evidence).
  Lossy beam/cutoff remains forbidden.

## P6b — Eval layer (Ascent fixpoint demand): explicit stage and non-goals

Existing evidence mechanisms (inventory §8): guard dispatch, semantic_hash dedup, rewrite-to-Err,
and the seed-side category-compatibility filter (`alt_compat_with_dispatch_cat`, phase-D design).
Parse-side refutations already never reach eval (refuted cursors never realize) — the parse→eval
seam is sound today; P1-P3 shrink its volume.

- **EV-0 (probe, 1 commit):** per-relation Ascent fact counts vs facts reachable backward from
  extracted normal forms, on the post-ROOT-A rhocalc comm corpus (the newly non-vacuous tests are
  exactly where eval waste would first appear). **Gate:** undemanded-fact share ≥ 50% AND eval ≥ 20%
  of test wall-time → EV-1 (demand/magic-set transformation of the generated Ascent rules, with a
  `DemandTransformEquivalence.v` query-equivalence model); else non-goal.
- **Non-goal (recorded):** Rho-machine-side pruning. Per the amended
  `docs/design/made/rholang-target/design.md`, scheduling/GC/cost belong to f1r3node's Rho machine
  (`eval_par`, RSpace); MeTTaIL's contract is "emit Par, never fork". Evidence-based demand there is
  the cost-accounting `is_funded`/`delta_sigma` story owned by the M-RHO adapter — outside this
  program's boundary. This program's contribution to M-RHO is upstream purity: fewer spurious
  alternatives (notably ROOT-F pollution) means fewer spurious Par seeds.

---

## 7. Pipeline-wide seam map (where each mechanism fires)

| Seam | Existing (kept) | This program adds |
|---|---|---|
| lex | DAG soft-fail orphans, edge weights | P2's backward class-DP over the lex DAG (mask = union over paths) |
| lex→dispatch fork | keyword reservation (51d57c91), d1 fall-through+gate (82310a24) | P1 d2 + unified model; P2 mask replaces rescans |
| dispatch | PathMap trie, visited_dispatch, `ContextWeight::is_zero` | P2 obligation gate at spawn; P3 liveness at push *(only if the P3 entry gate passes; diagnostic-only otherwise)* |
| parse step | Tomita merge, cohort cache, progress detector | P2/P3 per-frontier refutation (post-drain, per merged class); P4 demotion |
| EOI | premature-Accepted, trailing salvage | P3 *(conditional, as above)* would make input-independent death fire at the killing transition; ESS in budget reports |
| realize | min_terminal_span, semantic_root, semantic_hash dedup, caps(report) | unchanged here — ROOT-F track owns packing-level pollution |
| eval | guards, dedup, Err-rewrites, seed filter | EV-0 probe; demand transform only on gate pass |
| dovetail | budget reports, exact k-best + 0̄-inside skip | DV-0 probe; demand-gated saturation only on gate pass |
| Rho machine | adapter boundary (M-RHO.0) | non-goal (boundary recorded) |

## 8. Sequencing vs in-flight tracks; shared substrate

- **#307 ROOT-A (lands first):** same files as P1/P2; hard ordering dependency (P0.1).
- **#307 ROOT-F (sub-multiset PPar pollution — every `{p | q}` also realizing `{p}`; 5B splice
  family):** separate track at the REALIZE seam (packing-level, `sppf_realize.rs` + the Phase 5B
  splice machinery of a95c5106). Cursor-level gates (P2/P3) cannot fix it and must not claim it.
  **Shared substrate:** (1) the no-loss proof template — ROOT-F's fix will be a packing-level
  definite gate or quotient and should instantiate the same
  `EvidenceComplete.{no_valid_alternative_dropped, evidence_only_removal}` template and the
  I3/I4/I5 ladder; (2) `walker_stats`/`PRATTAIL_WALKER_STATS` reporting; (3) **baseline coupling:**
  `rhocalc_tests` 118/8 and `edge_case` 227/2 contain ROOT-F failures — every P-stage pins its
  baseline hash, and a ROOT-F landing triggers a one-commit rebaseline of the ledger (never
  silently absorb diffs).
- **Phase 2 realizer:** no file overlap with P1-P5. **Shared substrate:** the realized-term
  ambiguity contract and the test corpora. Coordinate on rebaselines and on EV-0's corpus choice
  (run EV-0 before the realizer rewires eval, so the measurement attributes to the current engine).

## 9. Risk register (v3 — reconciled with red-team rounds 1-3)

1. **P3 `abstraction_superset` fidelity** ⇒ Step-(-1) transition inventory with ≤K-must-add entry
   gate; **P3 is DEMOTED to inventory + diagnostic-only (round-2 M-3)** — no enforcement
   apparatus; the whole-stack `stack_fully_modeled` guard (round-2 N2) + per-state shadow
   partitioning apply to the DIAGNOSTIC and to any conditional-pass revival. The v1
   "`recovery_depth == 0`-only" mitigation is DELETED (it was inverted — see I8 v2/v3).
2. **Lattice masks under lex ambiguity** (P2): per-DAG-NODE masks keyed by node-id with
   edge-monotonicity; union-over-paths direction; `lattice_node_mask_welldefined` ships in the P2
   MODEL commit and the gate ships **ARMED on BOTH source kinds, shadow-validated on lattice
   inputs first** (round-2 M-1: the cast corpus routes through `LatticeTokenSource` — a
   linear-only arming gate would enforce nothing on its own target corpus; the v2
   "until lattice-validated" deferral is DELETED).
3. **Recovery composition** (all definite gates): I8 v3 — `refute ⇒ must ∩ repair_synthesizable_classes = ∅`;
   INSERT is the suffix-growing repair; counters partitioned by `recovery_enabled`; missing-operator
   INSERT probe in the corpus (B1).
4. **Lex-fork blast radius** (P1 d2): the falsified-fall-through history (360c55ec) — d2 lands only
   WITH its gate, never alone; `extension_preserves_189_behavior`/`multilength_unaffected`
   re-verified; ledtest SENTINEL aborts on any regression.
5. **Table size blowups** (P5; P3 only if its entry gate passes): explicit byte budgets with STOP
   outcomes; per-literal trigger classes feed the alphabet-size line (F6).
6. **Measurement honesty:** all waste percentages computed on BOTH the pathological corpus and the
   neutral corpus (chains); a gate passing only on a synthetic input does not justify enforcement
   (record per-corpus numbers in the ledger). ALL waste numbers re-baselined POST-ROOT-A; the
   "342,699" figure is RETIRED as unsourced (F1).
7. **Re-conflation regression** (P1): `wrap_rule`/`wrap_cat` are LOAD-BEARING `DispatchKey`
   discriminators (M4 tombstone); the only merge key is the existing `EquivKey`; any proposal to
   widen/narrow either key requires its own model + flip experiment (F2⊕m2).
8. **Scheduler-model fidelity** (P4): order-only claims are proven against `step_fanout`'s actual
   transition (permutation-invariance incl. budget/merge), never inferred from realize-side dedup
   theorems (M3); demotion is within-step only (`demoted_member_unstepped_at_exit == 0`).

## 10. Commit-boundary summary (per stage: M=model, D=diagnostic, I=implementation, L=ledger)

- P0: 1 commit (scaffold) + ledger file.
- P1: M `EvidenceGatedDelegates.v` → D counters/probes → I (d2 and/or cohort-share, each separately
  flippable) → L (Welch + decisions).
- P2: M `ParikhObligationGate.v` → D `suffix_classes.rs` + shadow → I enforcement + rescan
  replacement (separate sub-commit) → L.
- P3 (DEMOTED): M = the Step-(-1) transition-inventory doc ONLY → D = diagnostic-only shadow
  measurement → recorded STOP (expected) → L. [`PreStarLiveness.v`, enforcement, and the weighted
  table are all conditional on the entry gate unexpectedly passing — round-2 M-3.]
- P4: M `ForwardOrderOnly.v` + `InnovationDemotionOrderOnly.v` → I ESS + demotion → L.
- P5: entry-gate measurement commit; then M `RegularResidualGate.v` → D → I → L only on gate pass.
- P6a/P6b: probe commit each; models (`SaturationDemandGate.v`, `DemandTransformEquivalence.v`)
  only on gate pass.

Every M commit: `_CoqProject` update + `rocq-prattail-wpda` green + `Print Assumptions` output in
the commit message. Every D/I commit: battery results in the commit message (ledtest SENTINEL
first). Every L commit: pgmcp experiment id + accept/STOP verdicts.
