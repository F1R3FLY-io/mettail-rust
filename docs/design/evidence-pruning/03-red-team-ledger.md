# Evidence-Pruning Program — Red-Team Ledger

> Adversarial-critic iterations on `02-staged-implementation-plan.md`, per the standing mandate:
> independent critics attack the design until convergence BEFORE any FV/implementation.
> Round 1: two critics (soundness / effectiveness), launched 2026-06-11.

## Round 1 — Critic 1 (SOUNDNESS): **NOT-CONVERGED** (2 BLOCKER, 3 MAJOR, 3 minor)

### B1 [BLOCKER] — Recovery token-INSERT inverts I8's `recovery_depth == 0` guard
- Evidence: `recovery.rs:84` INSERT fabricates a missing token (cost 2.0); `wpda_walker.rs:7589-7628`
  recovery fork — the PARENT that spawns recovery is at depth 0 (`child_recovery_depth = depth+1`,
  :7743-7754). Depth-0 is the recovery-ELIGIBLE state, not the recovery-free state.
- Counterexample: input `int(3) 3` (missing `==`) in a Bool-seeking context. P2's `must` includes
  the `==` class; the actual suffix lacks it ⇒ gate refutes at depth 0 — but recovery would INSERT
  `==` and produce a valid `[REPAIR]` parse. The monotone-under-continuation premise is violated by
  the repair transition itself (INSERT grows the suffix class set; `S_{i+1} ⊆ S_i` is false across
  an INSERT).
- **Fix:** definite-gate applicability = "obligation class ∉ insertable/sync set" (NOT
  `recovery_depth == 0`). Every definite-gate model carries `refute ⇒ must ∩ insertable_classes = ∅`.
  Partition shadow counters by `recovery_enabled`. P2/P3 enforcement is sound only with recovery
  OFF until this lands.

### B2 [BLOCKER] — `PreStarLiveness.abstraction_superset` unprovable as stated
- `build_wpds` (`wpds.rs:425-733`) models the STATIC grammar: one model position per syntax item,
  reachability from the primary category. MISSING runtime transition classes: (1) cross-cat LHS
  delegation + reentry (`gss.rs:401-450` `EdgeKind::CrossCatLhs`/`CrossCatLhsReentry` — the
  "re-push source above predecessor for one infix pass" transient); (2) cast `CrossCatProjection`
  wrap injection (`gss.rs:418-424` `(wrap_cat, wrap_rule)`); (3) micro-state machines
  (`wpda_runtime.rs:304-459` CollectionLoop/CollectionOpenParen/MixfixContinuation/
  MixfixLiteralRun/InfixChainIterative — one model Replace per item vs many runtime states).
  `wpda_walker.rs` has ZERO references to prestar/Wpds/PAutomaton today.
- A runtime config missing from the model maps OUTSIDE `pre*(F)` ⇒ unsound refutation. Most
  dangerous input: `int(3) == 3` mid-`CrossCatLhsReentry` — Stage A would refute the parse the
  program exists to enable.
- **Fix:** extend `build_wpds` with model transitions for (1)-(3) + proofs, OR restrict P3
  enforcement to an ALLOW-LIST of `WpdaState`s whose model image is proven exact — refuse to refute
  in any `CrossCat*`/`Mixfix*`/`Collection*`/`InfixChainIterative` state until modeled. Partition
  `prestar_shadow_refuted_then_accepted` by `WpdaState`.

### M1 [MAJOR] — `must`-fixpoint union unsound over nullable/Optional/Sep RHS positions
- `must(A) = ⋂_{A→σ} ⋃_{s∈σ} must(s)` over-claims: `Sep` is nullable (0 iterations), `Optional`
  has an explicit skip path (`wpds.rs:668-689`). Counterexample: `A → s₁ Optional[","s₃]` — the
  skip derivation consumes no comma, but the union puts Comma in `must(A)` ⇒ refutes a valid parse
  whenever Comma ∉ suffix. The "nullable ⇒ ∅" parenthetical only covers wholly-nullable A.
- **Fix:** `must(A) = ⋂_{A→σ} ( ⋃_{s∈σ, nonnullable(s)} must(s) )` with nullable computed as the
  standard fixpoint ("every derivation consumes ≥1 token"), proven with the nullable hypothesis on
  each unioned position. Seed the P2 corpus with Optional-skip / Sep-empty inputs (e.g. no-else
  `IfElse`).

### M2 [MAJOR] — `S_i` masks ill-defined on the lex DAG; nat-monotonicity is the wrong shape
- `LatticeTokenSource`: positions are DAG node-ids (`next_pos(pos, alt) = target_node`), NOT linear;
  `positions_are_linear_tokens() = false`; two distinct nodes can share a `byte_start`; orphan
  nodes can sit numerically after EOF. `S_{i+1} ⊆ S_i` over nat is FALSE as written.
- The shipped trigger-ahead scan is safe only because it is a PRESENCE test; the mask REFUTATION
  makes indexing load-bearing.
- **Fix:** per-DAG-NODE masks with edge-monotonicity `∀alt: S[next_pos(node,alt)] ⊆ S[node]`;
  `lattice_union_sound` quantifies over DAG paths; Rust table keyed by node-id, NEVER `byte_start`;
  add `lattice_node_mask_welldefined`. Until the model is DAG-shaped, gate P2 on
  `positions_are_linear_tokens()` and STOP on lattice sources.

### M3 [MAJOR] — P4's "extends `weight_is_order_only`" is a category error
- `EvidenceComplete.weight_is_order_only` is about realize-side `from_alternatives` dedup (abstract
  `list Alt`), NOT the walker scheduler. The accepted set is produced by `step_fanout`
  (:9950-10120) + `resolve_at_end_of_input` (:4593) + `is_accepting_config` (:6039).
- **Fix:** new model of `step_fanout`'s per-step frontier transition proving permutation-invariance
  of the surviving-cursor set (incl. budget/merge), PLUS a proof that `run_to_end_of_input` steps
  every live member before any `!progress_made` exit.

### P4 demotion × progress-detector — attack FAILED as coded, with one caveat
- Safe because `step_fanout` steps the ENTIRE frontier per iteration and the progress fingerprint
  (:4388-4415, weight deliberately dropped per H1') is whole-frontier — in-step permutation cannot
  starve a cursor.
- CAVEAT (must be a stated invariant): if demotion is ever implemented as "do not materialize this
  lazy-cohort member this step", the deferred member is invisible to the fingerprint and
  `!progress_made` can fire early. Invariant: demotion permutes WITHIN a step, never removes a live
  member from the drained set. Counter `demoted_member_unstepped_at_exit` (must be 0).

### m1 [minor] — I4 shadow soundness is battery-bounded; corpus must be adversarially seeded
- One input per definite-gate failure mode: (a) missing-operator + recovery INSERT reachable,
  (b) Optional-skip with union-unique class absent downstream, (c) multi-length lex ambiguity
  driving a refutation. Partition `refuted_then_accepted` by `WpdaState` × `recovery_enabled`.

### m2 [minor] — P1 cohort-share wording risks re-conflating what M4 un-conflated
- `DispatchKey` (`dispatch_cohort.rs:81-130`) was WIDENED with `wrap_cat`/`wrap_rule` to fix the
  cast family. "Share across `wrap_rule` only" is ambiguous. **Fix wording:** merge only members
  with IDENTICAL full `DispatchKey` (incl. `wrap_rule`); `share_iff_duplicate` carries the
  `wrap_rule` discriminator. `EquivKey` (`(source, inner_cur_bp)`, position/wrap-independent) must
  NOT be the share key.

### m3 [minor] — P3 mid-micro-loop annotation staleness
- A CollectionLoop/MixfixLiteralRun consumes many tokens within one model position; push-site
  annotation is stale mid-loop. **Fix:** prove non-push-aligned reads are CONSERVATIVE (live ⊇
  actual), or check liveness only at push/pop boundaries.

### Attacks that FAILED (convergence record)
- Union-over-lex-paths: sound — union is the over-approximation direction; `must ⊄ union ⇒ must ⊄ path`.
- ESS reporting: genuinely read-only (fold at budget-event/EOI; no frontier mutation).
- Premature-Accepted filter: preserves trailing alternates (`push_eoi_resolution_candidate`
  :4524-4558 keeps both EOI-accepting and prefix-trailing candidates).
- P1 d1 gate: one-sided by construction (presence ⇒ do-not-refute); spurious hits die by evidence.

## Round 1 — Critic 2 (EFFECTIVENESS): **NOT-CONVERGED** (2 BLOCKER, 3 MAJOR, 4 minor)

### F1 [BLOCKER] — The "342,699 no-op steps" pathology is mis-attributed; it is ROOT-A's bug, not gate-addressable
- The number appears NOWHERE in the codebase/pgmcp/test artifacts — only in the evidence-pruning
  docs; its origin is a session-memory bullet (file-history `4801cd1043000a38@v8`) whose original
  text says "(frontier quiescence missing)" and an earlier draft used the placeholder "n no-op
  walker steps". The dedicated rho15 investigation attributed the cast-then-infix/send waste to
  ROOT-A (mixfix part-0 literal accounting + unchecked kind=0 consume + `unwrap_or(pos+1)`
  fabrication + EOI discard at `push_eoi_resolution_candidate` :4524-4557) — none of which
  P1/P2/P3 touch, and ALL of which the in-flight ROOT-A commit fixes.
- **Fix:** rewrite P1's goal — the step-count pathology is OWNED BY ROOT-A (P0.1); P1's real
  target is the narrower delegate FAN on cast-then-compare. Re-pin every waste number to a
  freshly MEASURED post-ROOT-A baseline; the 60%-drop waste gate must baseline AFTER ROOT-A.

### F2 [BLOCKER] — "share across `wrap_rule` only" re-introduces the M4-reverted collapse
- `DispatchKey` doc (dispatch_cohort.rs:76-99) is an explicit tombstone: collapsing distinct wrap
  rules at `(pos, source, bp)` WAS the cast-family root cause; M4 added the wrap discriminator.
  The plan's instruction means merging delegates differing only in `wrap_rule` = exactly that
  collapse. The narrow merge the plan wants ALREADY EXISTS as `EquivKey`
  (`(source_src_idx, inner_cur_bp)`).
- **Fix:** delete the instruction; only admissible merge = existing `EquivKey`; `wrap_rule` STAYS
  a cache discriminator; cohort-share half of P1 = "reuse `EquivKey`, never re-widen", gated on
  the measured dup counter. (CONVERGES with critic 1's m2.)

### F3 [MAJOR] — `abstraction_superset` omits the entire intrinsic subsystem (~25 `WpdaState` variants)
- Model `StackSymbol = (category, rule_label, position)` vs runtime `StackSymbolV2` (cat, rule,
  bp, SymbolKind ∈ {CategoryEntry, RuleAt, InfixContinuation, Return, CollectionMarker,
  GroupingMarker, MixfixMarker, …}) + ~25 `WpdaState` variants (Mixfix*, Collection*, Binder*,
  Grouping*, CrossCatDelegate, Unwinding, Saturating, recovery, lex-fork) absent from
  `build_wpds`. (CONVERGES with critic 1's B2.)
- **Fix:** P3 Step-(-1) "transition inventory" deliverable — tag every transition class
  {in-model, restricts-only, must-add}; entry gate "≤ K must-add classes" else P3 STOPs at the
  model. Honest prediction: liveness sound only over the RuleAt skeleton ⇒ likely
  `prestar_shadow_incremental_over_parikh < 3%` → STOP.

### F4 [MAJOR] — Wrong GSS struct; O(1)/no-per-frame-storage claims fail against GSS sharing
- The walker uses `WpdaGss`/`WpdaGssNode { pos, symbol: StackSymbolV2 }` (gss.rs:362-367) — the
  plan's cited `gss.rs:97 GssNode` is the legacy `GraphStructuredStack` (dead on the hot path).
  GSS nodes are SHARED; a cursor's true stack suffix is its `incoming_edge_stack` (arena-backed)
  — full-stack obligations require walking it, not an O(1) top-frame read.
- **Fix:** retarget to `WpdaGssNode` + the `incoming_edge_stack` arena. P2's gate = `must` of the
  TOP `RuleAt` symbol only — genuinely O(1) AND sound for refutation (the full-stack union only
  ADDS classes; top-frame `must ⊄ S` already implies no accepting continuation) — but the plan
  must say so. P3 annotation lives per edge-stack entry (per-frame storage acknowledged honestly).

### F5 [MAJOR] — Welch benches don't exist; full battery per commit infeasible
- No `cast_tower_bench`, no `recovery_cohort_bench` (only `b2_chain_bench.rs` + the standard
  bench table). Full I6 battery is several minutes × ~20 commits.
- **Fix:** P0 deliverable: create both benches (mirroring b2_chain_bench, kill-switch arms).
  Scope I6 by commit class: M/L commits = full battery; D/I commits = SENTINEL + targeted panel +
  `-3!` canary + changed-surface suite.

### F6 [minor] — `generalizes_trigger_gate` equality is false unless trigger literals are per-class
- The shipped gate matches operator TEXT (`==`, `>=`, …); P2's classes may coarsen. **Fix:** map
  each grammar-declared infix-trigger terminal to a distinct class (FIRST-of-infix granularity);
  restate the theorem as refinement (⊑), or equality only under per-literal classes; carry the
  alphabet size into P3/P5 byte budgets.

### F7 — Stage-order inversion attack FAILED (convergence record)
- `d1_d2_delta` (CastLexForkCrossCatLhsGap.v:171-181) proves d2-minus-d1 = exactly
  `{(SourceCtx, IVar)}` — a lex-fork branch decision orthogonal to P2's suffix-class refutation;
  P2 provably cannot subsume d2. The existing `crosscat_lhs_d2_only_hits` STOP-gate suffices.

### F8 [minor] — Missed reuse (I7 not discharged)
- `pos_in_absorbed_chain_interval` (wpda_walker.rs:14164) = an existing O(1) interval-membership
  refutation of the same shape; `EquivKey` = the existing narrow merge; `FirstSet`/`follow_inputs`
  = the existing class source; and inventory gap #1's ProcX fan points at hoisting the existing
  `semantic_root_accepts_at_cursor` (:6188) to dispatch — potentially CHEAPER than P3's tables.
- **Fix:** discharge I7 per stage: P1→EquivKey; P2→name the two generalized mechanisms + FirstSet;
  P3→justify pre*-tables vs the semantic-root hoist (if the hoist closes the ProcX fan, P3
  enforcement may be unnecessary).

### F9 [minor] — Stale line refs post-ROOT-A
- ROOT-A renumbers forks.rs/engine_impl.rs. **Fix:** function-name anchors
  (`emit_lex_fork_at_prefix_dispatch __fall_through`) instead of absolute line ranges. No
  structural conflict (different functions, ~140 lines apart).

## Round 1 — CONVERGENT FINDINGS (both critics independently)
1. **M4/`wrap_rule` re-collapse** (c1-m2 ⊕ c2-F2): the plan's cohort-share wording would
   re-introduce the cast-family root cause. Resolution: `EquivKey` reuse only.
2. **`abstraction_superset` infidelity** (c1-B2 ⊕ c2-F3): build_wpds misses whole runtime
   subsystems. Resolution: transition inventory + WpdaState allow-list + per-state shadow
   partitioning + honest STOP prediction.

## Round 1 verdict: plan v1 REFUTED on 4 distinct BLOCKERs — v2 revision required, then round 2.

---

## Round 2 — Critic 1 (SOUNDNESS, fresh agent vs v2): **NOT-CONVERGED** (0 BLOCKER, 4 MAJOR, 1 minor) — scope narrowing

### N1 [MAJOR] — The `semantic_root_accepts` dispatch-time hoist is a CATEGORY ERROR
- `semantic_root_accepts_at_cursor` (wpda_walker.rs:6188-6221) operates on a REALIZED single-Symbol
  SPPF root whose span ends at the cursor (`root_hi == cursor_pos`); its only caller fires when
  `sppf_stack.len() == 1` ∧ Symbol. At DISPATCH time there is no root — the check returns trivial
  answers, or, mechanically adapted, REFUTES every spawn whose operand is unconsumed (no-loss
  violation). The "cheaper P3 alternative" is illusory as written.
- **Fix:** strike the hoist; a dispatch-time viability gate must be a DISTINCT predicate grounded
  in pre*/FirstSet (`category_reaches_accepting(c, top_frame)`), full I4 ladder. Remove P3's
  "table apparatus may be unnecessary" escape that rested on it.

### N2 [MAJOR] — P3 allow-list must be WHOLE-STACK, not current-state
- The abstraction maps the entire stack; a cursor in an ALLOWED current state can carry frames
  pushed by UNMODELED transitions (CollectionMarker, CrossCatProjection(wrap), MixfixMarker…).
  Counterexample: `{ int(3) == 3 | x }` — operand cursor in a normal dispatch state with
  Collection + CrossCatProjection frames below ⇒ truncated/aliased stack image may fall outside
  pre*(F) ⇒ refutes the headline parse, slipping past the current-state allow-list.
- **Fix:** `stack_fully_modeled(cursor)` guard (walk `incoming_edge_stack`, or a monotone sticky
  bit set on unmodeled-frame push); `abstraction_superset` stated over fully-modeled stacks only;
  shadow counters partitioned by fully-modeled-vs-not. Reinforces the predicted P3 STOP.

### N3 [MAJOR] — `insertable_classes` is per-(category × dispatch-context), and includes the OPERATOR LITERALS
- Ground truth: INSERT draws from `sync_tokens` = structural delimiters ∪
  `collect_terminals_for_category` — which includes EVERY operator literal (`==` IS a Bool sync
  token); `tightened_sync_tokens` makes it context-dependent. A flat per-language set scoped to
  the current category is UNSOUND mid-CrossCatLhsReentry (state-cat Int, reachable recovery Bool).
- **Consequence (must be stated):** under recovery-on, P2 refutation on infix-trigger obligations
  is suppressed almost everywhere — P2's measurable win is the `recovery_enabled = false`
  partition.
- **Fix:** conservative over-approximation `insertable_classes(cursor) ⊇ ⋃ sync_tokens(c)` over
  all reachable recovery categories (safe upper bound: union over ALL categories; tightening only
  shrinks); prove `gate_repair_disjoint` against the over-approximation.

### N4 [MAJOR] — SUBSTITUTE (and CategorySwitch) ALSO synthesize classes; "INSERT is the one" is FALSE
- SUBSTITUTE (recovery.rs:889-905) reinterprets the current token as any sync token — supplies an
  obligated class the raw suffix lacked (counterexample: `int(3) X 3`, SUBSTITUTE X→`==`).
- **Fix:** rename to `repair_synthesizable_classes` = INSERT ∪ SUBSTITUTE ∪ CategorySwitch
  sources (same `sync_tokens` set ⇒ same value, but the concept and proof must cover all three);
  drop the false sentence from I8.

### N5 [minor] — `step_permutation_invariant` must pin `source_priority`
- `source_priority` is NOT in the Tomita `merge_disambiguator` (tomita_frontier.rs:288-300) yet is
  the dangling-else tiebreak in `merge_equivalent_cursors` (wpda_walker.rs:11529-11530) — a
  first-arrival-kept field. No concrete failing parse constructed (merge-eligible arcs traced so
  far share provenance ⇒ share priority) ⇒ prove-or-pin: lemma "source_priority is a function of
  the disambiguator on tied-weight arcs" as a hypothesis, or add it to the merge predicate.
- Also: add `rule_at_pop_implies_must_consumed` lemma to ParikhObligationGate.v (top-frame
  soundness silently depends on "every RuleAt pop is a completion" — verified true:
  emit_fire_action on RuleAt; Unwinding/GroupingClose pop only Return/CategoryEntry); add the
  [REPAIR]-position clause to `lattice_node_mask_welldefined` (repairs never allocate DAG nodes;
  INSERT holds pos fixed).

### Round 2 VERIFIED-SAFE records (attacks that failed)
- DELETE/SKIP monotone-safety: both only shrink the suffix; masks over the immutable shared
  LexDag can't be corrupted by another cursor's repair.
- RuleAt abandonment: every RuleAt pop fires the completion action — top-frame `must` genuinely owed.
- Tomita ⊕-merge permutation-safety: merge requires full disambiguator + ptr-eq heavy fields +
  visited equality; only commutative weight fields mutate (modulo N5).
- [REPAIR]/orphan mask well-definedness: cursor.pos always indexes dag.nodes.
- P1 EquivKey grounding: `equiv()` drops pos+wrap; `DispatchKey::new` keeps wrap — v2 faithful to M4.
- P2 lattice arming guard mirrors the shipped `positions_are_linear_tokens()` pattern.
- recovery_cohort_bench.rs EXISTS (languages/benches/, Cargo.toml:203-205) — round-1 F5 was
  half-right (cast_tower_bench is the only missing panel).

## Round 2 — Critic 2 (EFFECTIVENESS, fresh agent vs v2): **NOT-CONVERGED** (1 BLOCKER, 3 MAJOR, 4 minor)

### B-1 [BLOCKER] — ROOT-A broke the `--features walker-stats` build (the measure-first substrate)
- Non-exhaustive `project_continuation_record_for_action` match (wpda_walker.rs:654 region) missing
  `ConsumeAtAndReplace`; PLUS bucket collision: both ConsumeAndReplace and ConsumeAtAndReplace
  mapped to `apply_action_variant_histogram` bucket 11 — conflating exactly the per-action
  attribution P-series diagnostics need.
- **RESOLVED (same session, inside the ROOT-A commit 9fdaed68):** projection arm added (record +
  size_of::<usize>, reserved slot 17 of the independent projection index space);
  `ConsumeAtAndReplace => 19` own bucket; histogram grown [u64;19]→[u64;20]; label appended;
  verified `cargo build/test -p mettail-prattail --features walker-stats` green 3980/0.
- **Plan change:** I6 battery gains a `cargo build --features walker-stats` gate (the load-bearing
  build for the program, previously untested by the battery).

### M-1 [MAJOR] — Holistic contradiction: P2 enforcement OFF on its own accept-gate corpus
- PROVEN at runtime: `parse_via_wpda` routes to `LatticeTokenSource` iff `dag.has_ambiguity()`;
  `int(3)`'s DAG IS ambiguous (`Fixed("int")`/`Ident("int")`/`Fixed("in")` fork + numeric-literal
  forks) ⇒ the ENTIRE cast/ProcX corpus takes the lattice path, where
  `positions_are_linear_tokens() = false` disarms P2's v2 lattice guard. P2 would measure a
  passing gate on inputs it cannot act on; it would enforce only on linear inputs (the chains —
  where the plan promises NEUTRALITY).
- **Fix (decided): option (a) — the DAG-node masks ARE the critical path**;
  `lattice_node_mask_welldefined` ships in the P2 model commit and the lattice gate ships ARMED
  (shadow-validated on lattice inputs first). The "until lattice-validated" deferral is deleted.

### M-2 [MAJOR] — Independent confirmation of round-2-soundness N1 (the hoist)
- `semantic_root_accepts_at_cursor` is O(span) (two linear delimiter scans) AND takes a realized
  `SppfId` that does not exist at dispatch. Confirms striking the hoist (already applied per N1).

### M-3 [MAJOR] — P3's ≤K entry gate cannot pass (K=3 vs ≥15 must-add classes); weighted table inherits the hole
- 18 `WpdaState` variants + CrossCatLhs/Reentry/Projection-wrap transients vs the bare
  `(category, rule_label, position)` skeleton in build_wpds. Honest prediction: gate FAILS ~5×.
  AND the v2 "weighted by-product feeds P4" claim is UNSOUND as stated: the weighted prestar runs
  over the SAME skeleton model ⇒ same abstraction hole ⇒ not a valid admissible bound for P4 over
  the real frontier.
- **Fix (decided): P3 DEMOTED now** — Step-(-1) inventory commit → recorded STOP (predicted) →
  P3 reduces to diagnostic-only shadow measurement; NO enforcement apparatus, NO allow-list
  build-out, and P4's `admissible_bound_exact_first` either restricts to {in-model}-state cursors
  or drops the prestar bound (keeping lex-min realization order, which needs no table).

### m-1 [minor] — `stats_inc!` takes a bare ident; partitioned counters need `stats_inc_idx!` or
  direct indexed assignment + `const WPDA_STATE_CLASS_COUNT`. (P0.3 convention corrected.)
### m-2 [minor] — `must` must be TOTAL over `SymbolKind` (InfixContinuation/MixfixMarker/Return/
  CategoryEntry tops are common): sound default `must = ∅` (never-refute) for unconstrained kinds;
  `top_frame_refutation_sound` proven over ALL SymbolKind variants.
### m-3 [minor] — partitioned counters print only non-zero slots (report-size budget).
### m-4 [minor] — recovery_cohort_bench EXISTS but is panel-thin for P4 (5 fixed strings,
  cohort-hit-maximizing): P0.4 extends it with zero-innovation ε/recovery-stall inputs + a
  PRATTAIL_EP_P4_DEMOTE kill-switch arm.

### Round-2 effectiveness attacks that FAILED (convergence record)
- EquivKey wording now unambiguous + implementable (CLOSED); F4 struct retarget verified
  (WpdaGssNode/incoming_edge_stack arena O(1) access HOLDS); I8 insertable_classes derivable from
  recovery config (CLOSED); M1/M2 mask math sound as stated (the issue was WHERE P2 runs, not the
  math); P3 reuse anchors accurate; u128 class budget holds (~40 classes/language, 88 bits spare);
  bench-absence half-resolved (recovery_cohort_bench exists; only cast_tower_bench is new).

## Round 2 verdict: 0 soundness BLOCKERs; 1 build BLOCKER (FIXED in 9fdaed68); MAJORs are
## decision-shaped (P2 lattice = critical path; P3 demoted) — folded into v3. Round 3 next.

---

## Round 3 — Convergence check (single dual-lens critic vs v3 @ 60c1a926): **NOT-CONVERGED on
## TEXT-CONSISTENCY ONLY — "no design-level residue remains"**

- **Fold verification: COMPLETE** — every round-1/round-2 resolution verified present in the BODY
  (not just the header), with line-level spot-checks. No asserted-but-missing resolution.
- **F1 [MAJOR]:** §10 commit summary + the P3 body Implementation/Weighted-by-product subsections
  still shipped the demoted apparatus (`PreStarLiveness.v` enforcement + weighted table). FIXED:
  §10 line rewritten to the demoted form; body subsections wrapped in the conditional-pass guard;
  weighted by-product restated as STRUCK-with-conditional-revival.
- **F2 [MAJOR]:** §9 risk #2 still carried the v2 "until lattice-validated" linear-only arming
  deferral that round-2 M-1 deleted. FIXED: §9 #2 restated — masks ship ARMED on both source
  kinds, shadow-validated on lattice first.
- **F3 [minor]:** P5 entry gate said "after P1-P3 enforcement". FIXED: "after P1/P2 enforcement
  (P3 diagnostic-only)"; residual_dead_steps subtraction restated as minus-P2-real minus
  {P2∪P3}-shadow.
- **F4 [minor]:** the v1→v2 changelog still advertised the struck hoist. FIXED: [STRUCK in v3]
  annotation.
- **F5 [minor]:** §9 titled "v2 — round 1". FIXED: re-versioned v3; risk #1 restated to the
  demoted form; risk #5 byte budgets scoped "(P5; P3 only if its entry gate passes)".
- **F6 [implementation-phase carry-forward]:** the `stack_fully_modeled` sticky bit is
  monotone-never-cleared while `incoming_edge_stack` supports `intern_pop` — a cursor that pops
  its last unmodeled frame stays barred from refutation. SOUND (conservative direction), moot
  under the P3 demotion; if P3 enforcement is ever revived, consider an unmodeled-frame DEPTH
  COUNTER (decrement on pop) instead of a bit — O(1), recovers refutation.
- **Residue-coherence judgment (the program survives its own demotions):** the measurable spine =
  P1 (delegate fan, measurement-gated) + P2 (recovery-off obligation refutation, ≥20%-gated,
  lattice-armed) + P4 (ESS report always-on; demotion flip-gated with STOP fallback) + P5/P6
  (entry-gated, STOP-expected). Every kill is diagnostic-gated with a recordable STOP; I1-I8
  intact.
- **Round-3 failed attacks (record):** sticky-bit cloning leak (children inherit the
  field-by-field bit); sticky-bit GSS-sharing leak (bit is per-cursor, not per-shared-node);
  repair-class union vacuity (disclosed + scoped to recovery-off); stale 342k baseline in a live
  gate (all hits are retirement statements); P4 p<0.05-from-reordering brittleness (ESS
  report-only + demotion flip-gated); eoi_dead_cursors structurally empty (premature-Accepted
  machinery proves the population plausible); F6 alphabet line orphaned (P5 still consumes it).

## Round 4 — confirmation pass on the round-3 edits: ★ **CONVERGED** ★

- All five round-3 fixes verified correctly and completely in place (F1: §10 + P3 body demoted/
  conditional; F2: §9 #2 armed-on-both-kinds; F3: P5 entry-gate phrase + shadow-set subtraction;
  F4: changelog [STRUCK] annotation; F5: §9 re-versioned + risks #1/#5 demoted/scoped).
- Full-document sweep against every established decision (P3 demoted; lattice masks critical
  path; hoist struck; EquivKey-only merge; repair_synthesizable_classes; whole-stack guard;
  within-step demotion): NO design-level residue, NO new contradiction.
- Two cosmetic minors found and FIXED in the same pass: §7 seam-map P3 rows annotated
  conditional; §9 risk #3 naming drift (`insertable_classes`→`repair_synthesizable_classes`).
- Carry-forward (implementation-phase, non-blocking): ledger F6 — if P3 enforcement is ever
  revived, prefer an unmodeled-frame DEPTH COUNTER over the monotone sticky bit.

**FINAL VERDICT (4 rounds, 5 independent critic agents): the design is CONVERGED.** Round 1
refuted v1 on 4 BLOCKERs; round 2 refuted v2 on 4 soundness MAJORs + 1 build BLOCKER + 3
effectiveness MAJORs; round 3 found text-consistency residue only ("no design-level residue
remains"); round 4 confirmed the fold and swept clean. Next: user review → FV models (model
commit precedes any Rust) → measure-first staged implementation per §10.

