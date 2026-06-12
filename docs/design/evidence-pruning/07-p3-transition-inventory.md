# EP-P3 Step-(-1) — WPDA Transition Inventory & pre*-Liveness Entry Gate

> **Stage:** P3 (Stage A — pre\*-saturation configuration liveness), **DEMOTED to inventory +
> diagnostic-only** by round-2 M-3 (plan `02-staged-implementation-plan.md` §P3).
> **This doc is deliverable 1 of 3:** the Step-(-1) transition census + the ≤K-must-add entry gate.
> Deliverable 2 = the recorded STOP (below, **the gate FAILS as predicted**). Deliverable 3 = the
> diagnostic-only shadow measurement (`prestar_shadow_incremental_over_parikh`), whose own honesty
> constraint also fires — see §6.
>
> **Branch/commit:** `feature/wfst-architecture` @ `edac0084`.
> **Authoritative source anchors** (file:line at `edac0084`): the skeleton model is
> `prattail/src/wpds.rs::build_wpds` (:425–733); the runtime state space is
> `prattail/src/wpda_runtime.rs::WpdaState` (:303–612) + `SymbolKind` (:53–97); the runtime action
> classes are `prattail/src/wpda_walker.rs::WpdaStepAction` (:508–727), fired by
> `apply_action_to_cursor`.

## 0. Why this census exists (and who else needs it)

The pre\*-liveness gate (Stage A) wants to refute, at the *killing transition* rather than at EOI,
any cursor whose configuration has left `pre*(AcceptingConfigs)` of the grammar's WPDA. That is
only sound if the runtime configuration `(WpdaState, StackSymbolV2-stack)` has a faithful image in
the **model** the saturation runs over. The model that exists today —
`build_wpds` — is the bare `(category, rule_label, position)` skeleton (Reps–Lal–Kidd 2007
context-free-process encoding, single control location `p`). This census tags **every** runtime
transition class against that skeleton so we know, per class, whether liveness over it is sound.

The census is independently valuable: it is the transition inventory **every later modeling effort
needs**, including the upcoming Dovetail work (the engine's saturation/extraction must agree with
the same runtime→model correspondence). It is written to be reconstructable from scratch.

## 1. The skeleton model (what `build_wpds` actually emits)

`build_wpds` (`prattail/src/wpds.rs:425`) maps a `LanguageSpec` to a WPDS over the stack alphabet

- **Γ = `StackSymbol { category: String, rule_label: String, position: u32 }`** (`wpds.rs:61`).
  Category entry = empty `rule_label`, `position = 0` (`StackSymbol::category_entry`, :73);
  mid-rule = `(category, rule_label, position)` (`StackSymbol::rule_position`, :82).

Rules (`WpdsRule`, `wpds.rs:104`), one control location `p`:

| Model rule | Emitted for (`build_wpds` site) |
|---|---|
| `Replace ⟨p,γ⟩↪⟨p,γ'⟩` (intraprocedural) | Terminal (:517), same-cat NonTerminal (:531), same-cat Binder (:556), same-cat Collection (:578), IdentCapture/BinderCollection (:600), Sep single-traversal (:611), Map (:639), Zip (:662), **Optional skip path** (:673), GuardExpression (:690) |
| `Push ⟨p,γ⟩↪⟨p,γ_cont γ_callee⟩` (cross-cat call) | cross-cat NonTerminal (:544), cross-cat Binder (:564), cross-cat Collection (:587), Map cross-refs (:629), Zip cross-refs (:651), **Optional enter path** (:679) |
| `Pop ⟨p,γ⟩↪⟨p,ε⟩` (completion) | Rule completion (`final_pos`, :707–710); synthetic Pop for zero-rule categories (:720–730) |

What the skeleton **does not** carry:

- **No binding power.** `bp` lives only in the runtime (`StackSymbolV2.bp`, `wpda_runtime.rs:124`,
  and inside `WpdaState`). The Pratt precedence machinery is entirely out of model.
- **No `WpdaState`.** The 18 intrinsic runtime states (+2 terminal) collapse to "a position in a
  rule" or vanish.
- **No marker frames.** Runtime `SymbolKind` adds `CollectionMarker`, `GroupingMarker`,
  `MixfixMarker`, `OptionalGroupAt`, and uses `InfixContinuation` (`wpda_runtime.rs:53–97`); the
  model alphabet has only `{CategoryEntry, RuleAt(pos), Return}`-equivalents.
- **No loop structure.** Sep/Map/Zip/Optional are **summarized to a single traversal** — the source
  is explicit: *"The Sep body may loop, but we model a single traversal"* (`wpds.rs:617`). Collection
  element iteration, mixfix operand sequencing, and binder-list loops are likewise flattened.
- **No Pratt-LHS position.** For infix/postfix rules the same-cat LHS NonTerminal is recognized
  (`skipped_pratt_lhs`, `wpds.rs:535`) but still emitted as a plain `Replace` — there is **no**
  distinct "LHS already on the builder → dispatch an operator" model position. The runtime
  `InfixLoop` configuration has no image.
- **No cross-cat wrap injection.** The `CrossCatLhs` / `CrossCatLhsReentry` "re-push the source
  above its predecessor for one infix pass" transient (live `EdgeKind`s,
  `wpda_walker.rs:7042/7145`, with `wrap_cat`/`wrap_rule` injection at the cohort jobs
  :7642/:11854/:11942) has no model rule.

## 2. Classification key

- **in-model** — the runtime configuration has an EXACT skeleton image (a `(cat, rule, pos)` frame
  the skeleton emits) and the transition is a skeleton `Replace`/`Push`/`Pop`. A liveness query over
  it is well-defined.
- **restricts-only** — the transition only *prunes* which model configurations are reachable (a bp
  floor, a peek-decided branch the model already collapsed, a frontier multiplexer). *Proof sketch
  required:* it removes configurations and never creates a reachable runtime configuration whose
  model image lies outside `pre*(F)`. A liveness query is sound (it can only refute a subset of the
  definite-dead set).
- **must-add-to-model** — the runtime configuration carries pushdown structure the skeleton has no
  symbol/rule for (an extra stack frame, an iteration counter, a wrap injection, a re-push, a
  phantom class). There is no sound model image, so a liveness query would refute *live* cursors.
  The model must be **extended** before liveness over this class is admissible.

## 3. `WpdaState` census (`wpda_runtime.rs:303–612`)

| # | `WpdaState` variant | Tag | Model image / proof sketch |
|---|---|---|---|
| 1 | `Ready { min_bp }` | restricts-only | Image `⟨cat⟩` entry. `min_bp` removes prefix rules with `l_bp < min_bp` from the reachable set; the model's `cat-entry → rule-entry` Replace set is a superset ⇒ live set only shrinks. |
| 2 | `PrefixDispatch { pos, cur_bp }` | in-model | The `cat-entry → rule-entry` Replace dispatch (`wpds.rs:497`). Image `⟨cat⟩` or `⟨cat.rule@0⟩`. `cur_bp` is a restricts-only refinement on top. |
| 3 | `InfixLoop { cur_bp }` | **must-add** | The model elides the Pratt LHS (`skipped_pratt_lhs`, `wpds.rs:535`): no "LHS-consumed → operator-dispatch" position exists, and there is no `InfixContinuation` frame. The configuration "LHS on builder, awaiting an operator of bp > `cur_bp`" has no image. |
| 4 | `InfixChainIterative { rs, ri, obp, rbp }` | **must-add** | Iterative absorption REUSES one `Return` frame across N chain iterations (alloc elision, `wpda_runtime.rs:325`); the model has one `Pop` per completion and no iteration fixpoint. The mid-chain config (reused frame, advancing `pos`) maps to no single model frame. |
| 5 | `CollectionLoop { rs, ri, es, obp, acc, slot, kv }` | **must-add** | The element-separator LOOP (N elements, `kv_phase` for HashMap) is summarized to a single traversal (`wpds.rs:611–623`). The mid-loop config (a `CollectionMarker` frame + accumulator id + `kv_phase`) has no model symbol. |
| 6 | `CollectionOpenParen { rs, ri, es, obp }` | **must-add** | Two-token open delimiter (`"list"` then `"("`); the model consumes the collection as one Replace/Push and never splits the open into a wait-for-`(` state. The `CollectionMarker` already pushed has no image. |
| 7 | `MixfixContinuation { rs, ri, cidx }` | **must-add** | Mixfix operand sequencing with a per-operand counter (`cidx`) carried on a `MixfixMarker` frame; the model has no mixfix marker and no operand counter (the body is a flat trigger-elided position sequence, like infix). |
| 8 | `MixfixLiteralRun { rs, ri, cidx, kind, sub }` | **must-add** | Walks literal sub-sequences between operands with `(kind, sub_pos)` indices; the model collapses a rule's literals into consecutive Replace positions with no sub-indexing and no marker frame. |
| 9 | `BinderRule { rs, ri, bs, obp }` | **must-add** (restricts-only only in the degenerate same-cat-body, no-scope case) | The position walk over same-cat items mirrors the model's per-item Replace chain, BUT the binder SCOPE state (`start_binder_scope` builder coupling) + the `outer_bp` carried for precedence resume + the `OptionalGroup` re-entry have no image. In practice must-add. |
| 10 | `OptionalGroup { rs, ri, gidx, sub, obp }` | **must-add** | The model has ONLY a skip-Replace + enter-Push pair (`wpds.rs:668–689`). The present-path inner-position walk (`sub_pos`), the FIRST-set peek branch, the present/absent `ActionArg`, and the `OptionalGroupAt` marker frame are all unmodeled. |
| 11 | `BinderListLoop { rs, ri, bs, obp, mp, np, sub }` | **must-add** | The `^[xs]` ident loop (N idents, separators, close) with per-iteration `sub_pos`; summarized to a single traversal in the model (no loop, no per-iteration frame). |
| 12 | `CrossCatDelegate { src, inner_bp }` | restricts-only | The cross-cat `Push` IS the model image: `Push(from rule pos, to [continuation, ⟨source⟩ entry])` (`wpds.rs:544`). The delegate's job = push `⟨source⟩` entry + sub-parse. `inner_cur_bp` is a restricts-only bp floor on the sub-parse. **CAVEAT:** holds for the plain `CrossCatProjection` delegate ONLY; the `CrossCatLhs`/`Reentry` wrap-injection transient (#19 below) is must-add. |
| 13 | `AmbiguityFanout { branches }` | restricts-only | A frontier multiplexer. The model is per-configuration; "≥2 live configs" adds no stack structure — each branch is classified on its own `inner_state`. |
| 14 | `Saturating { delta_size }` | **must-add** (by absence) | A WPDS-internal saturation-bookkeeping state, not a parse configuration and not a stack frame; it has no `(cat, rule, pos)` image. Excluded from the liveness domain (never queried), but it cannot be modeled as a config ⇒ counted must-add for the census. |
| 15 | `Unwinding` | in-model **over `Return`/`CategoryEntry` pops only** | Popping a `Return` frame fires the model `Pop` rule (`wpds.rs:710`) — that is the image. When `Unwinding` pops a MARKER (`Collection`/`Grouping`/`Mixfix`/`OptionalGroupAt`) the popped frame is must-add. The boundary is exactly round-2 N5's `rule_at_pop_implies_must_consumed` lemma. |
| 16 | `GroupingClosePreservingInner { inner }` | **must-add** | Re-pushes a `CategoryEntry` of the inner cat AFTER `)` to preserve cross-cat infix dispatch context; this re-push of an already-completed category is a synthetic frame the model (which Pops the grouping and is done) never emits. |
| 17 | `Accepted` | in-model | Terminal; the accepting configuration = `Pop` of the primary category's final position to the empty stack. This is `F` itself. |
| 18 | `Error { message }` | restricts-only | A dead configuration; already refuted; never live. |

Plus the marker frames pushed without a dedicated state:

| # | Structure | Tag | Note |
|---|---|---|---|
| 19 | `GroupingMarker` frame + `CrossCatLhs`/`CrossCatLhsReentry` wrap injection | **must-add** | The grouping marker has no model symbol (the grouping is "transparent" in the model: Push/Pop of the inner cat). The wrap-injection transient (`EdgeKind::CrossCatLhs`/`Reentry`, `wpda_walker.rs:7042/7145`; `wrap_cat`/`wrap_rule` at :7642/:11854/:11942) — the §P3-named **most-dangerous unmodeled config** on `int(3) == 3` — has no model rule. |

## 4. `SymbolKind` frame-alphabet additions (`wpda_runtime.rs:53–97`)

The model alphabet is `{CategoryEntry, RuleAt(pos), Return}`. The runtime adds **five** frame kinds.
Each is a distinct model-alphabet addition for the whole-stack abstraction (round-2 N2: the
abstraction maps the ENTIRE stack, so even if a state were modeled, its frame symbol must ALSO be in
Γ):

| Frame kind | Owning state class | Model symbol? |
|---|---|---|
| `CollectionMarker` | CollectionLoop / CollectionOpenParen | none — **must-add** |
| `GroupingMarker` | (no state; prefix arm) | none — **must-add** |
| `MixfixMarker` | MixfixContinuation / MixfixLiteralRun | none — **must-add** |
| `OptionalGroupAt(sub)` | OptionalGroup | none — **must-add** |
| `InfixContinuation` | InfixLoop | none — **must-add** (model elides the infix LHS, so "awaiting RHS" has no image) |

## 5. `WpdaStepAction` census (`wpda_walker.rs:508–727`, fired by `apply_action_to_cursor`)

| Action variant | Tag | Against the skeleton's `{Replace, Push, Pop}` |
|---|---|---|
| `Advance` / `AdvanceWithEffect` | restricts-only | Pure state move (+ optional `BuilderDelta`); no GSS change. An internal refinement of one model position; removes nothing, adds no frame. |
| `Push` / `PushWithEdgeKind` | in-model | Cross-cat call = model `Push`. `EdgeKind` is GSS-routing metadata (restricts-only on top). |
| `Pop` | in-model over `Return`; must-add over a marker | Model `Pop` when popping a `Return`; the marker-pop case inherits its frame's must-add. |
| `Replace` | in-model | Same-cat/terminal advance = model `Replace`. |
| `Consume` | in-model | Terminal `Replace` at a separator; `pos` advance, no frame. |
| `ConsumeAndReplace` / `ConsumeAtAndReplace` / `ConsumeIdentAndReplace` | in-model | Terminal/ident `Replace` + `pos` advance. `ConsumeAt*` carries the matched lattice-edge target (`next_pos`) — a restricts-only refinement over the generic `advance_cursor_pos` (the "half-fix trap"; `wpda_walker.rs:661`). |
| `ConsumeAndPush` | in-model | `Push` + atomic trigger consume. |
| `ConsumeAndPop` / `ConsumeAtAndPop` | **must-add** | The collection-close arm pops a `CollectionMarker` (frame unmodeled); it never pops a `Return`. |
| `ReplaceAndPush` | **must-add** in practice | `Replace`-then-`Push` (param-cat entry) — but the replaced symbol is a marker/RuleAt-with-bp, so the marker frame is unmodeled. |
| `IterativeChainAbsorb` | **must-add** | The alloc-elided reused-`Return` chain (see `InfixChainIterative`). |
| `Fork` | restricts-only | Multiplexes into branches (each branch action classified separately); the Fork adds no frame. `consume_trigger` is an in-model `pos` advance. The dispatch FAN is the P1 concern, not a model-structure gap. |
| `OptGroupAbsent` / `OptGroupFinalize` | **must-add** | Optional present/absent `ActionArg` + `OptionalGroupAt` marker pop; the model has only the bare skip/enter Replace/Push. |
| `ParsePredicate` | restricts-only | Inline sub-language parse; consumes a span + pushes one `ActionArg`. From the WPDS view, a single `Replace` at the guard position (`GuardExpression` is modeled intra, `wpds.rs:690`). |
| `Accept` | in-model | Transition to `F`. |
| `Error` | restricts-only | Drop; dead. |
| `Idle` | restricts-only | `NoChange`; no transition. |

## 6. Entry gate — the must-add tally and the recorded STOP

**Entry gate (plan §P3 Step-(-1)):** `K = 3` must-add classes (the plan default). Count the distinct
must-add transition classes — the structures the model would need NEW pushdown machinery for:

1. `InfixLoop` — Pratt-LHS-elided operator dispatch + `InfixContinuation` frame.
2. `InfixChainIterative` — reused-`Return` iterative-chain fixpoint.
3. `CollectionLoop` — element-separator iteration + `CollectionMarker` frame + `kv_phase`.
4. `CollectionOpenParen` — two-token open + early `CollectionMarker`.
5. `MixfixContinuation` — mixfix operand counter on `MixfixMarker`.
6. `MixfixLiteralRun` — inter-operand literal sub-walk with `(kind, sub_pos)`.
7. `OptionalGroup` — present-path inner walk + `OptionalGroupAt` marker + `sub_pos`.
8. `BinderListLoop` — `^[xs]` ident-loop iteration.
9. `GroupingClosePreservingInner` — post-`)` inner-cat re-push.
10. `Saturating` — out-of-band; no configuration image.
11. `CrossCatLhs`/`CrossCatLhsReentry` wrap injection — the `wrap_cat`/`wrap_rule` re-push transient.
12. `CollectionMarker` frame (no model symbol).
13. `GroupingMarker` frame (no model symbol).
14. `MixfixMarker` frame (no model symbol).
15. `OptionalGroupAt` frame (no model symbol).
16. `InfixContinuation` frame (no model image for the infix LHS).
17. `BinderRule` scope state (`start_binder_scope` coupling + `outer_bp` resume).

**MUST-ADD COUNT = 17 distinct classes.** A deliberately conservative floor — collapse each marker
frame (12–16) into its owning state class and count only state-level structures — still yields **11**.

```
            K (gate)   must-add   ratio
  full         3          17       5.7×
  floor        3          11       3.7×
```

**GATE RESULT: FAIL.** `17 > 3` (floor `11 > 3`). The plan's honest up-front prediction —
*"the ≤K=3 entry gate is predicted to FAIL ~5×"* and *"≥15 must-add"* — is **CONFIRMED**:
17 ≈ 5.7×K, well above the ~5× prediction; even the conservative floor is 3.7×K.

**Recorded STOP (deliverable 2):** P3 stops at this inventory. Per the §P3 demotion, there is
**no** `PreStarLiveness.v`, **no** enforcement apparatus, **no** allow-list build-out. The inventory
is the recorded negative.

### Why the result is structural, not incidental

The skeleton is a *recognizer-shape* model: a position in a rule, with cross-cat calls as Push/Pop.
The runtime is a *Pratt + mixfix + collection + binder* engine whose live configurations are
dominated by (a) operator dispatch with the LHS already reduced onto the builder (the entire
`InfixLoop`/mixfix family — elided by `skipped_pratt_lhs`), (b) iteration the model flattens
(collections, chains, binder lists), and (c) marker frames that carry parse state with no model
symbol. Liveness over the bare `RuleAt` skeleton is therefore `α=⊤`-vacuous on exactly the intrinsic
states where the runtime spends its steps — which is also why the diagnostic (§7) predicts a
near-zero incremental.

## 7. Deliverable 3 — the diagnostic-only shadow measurement, and its own honesty STOP

The third deliverable was the diagnostic-only `prestar_shadow_incremental_over_parikh`: bake the
prestar P-automaton for the skeleton WPDA, and in a `PRATTAIL_EP_P3=shadow` mode (mirroring the
`EpP2Mode` plumbing) query, at the same merged-frontier drain site P2 uses
(`wpda_walker.rs:11398`), the liveness of cursors whose configuration is in-model, counting where
prestar would-refute and P2's Parikh mask did not.

**The plan attaches an explicit honesty constraint to this sub-deliverable** (§P3 deliverable 3,
final sentence; §9 risk 1): *if baking the prestar for the runtime check requires NEW modeling
beyond the existing `wpds.rs` analysis surface (i.e., it stops being reuse), STOP that
sub-deliverable, record exactly what it would need, and let the inventory + the recorded prediction
stand — do NOT build new saturation machinery.* That constraint **fires here.** The existing analysis
surface does exactly one shape of query, and it is the wrong shape:

- `prestar(wpds, target)` (`wpds.rs:1073`) — reusable as-is.
- `build_bad_state_automaton(wpds, labels)` (`verify.rs:77`) — a reusable *template* for an
  `AcceptingConfigs` target (swap "bad" for the Pop-completable final positions / accepting roots).
- **But the membership query is ALWAYS the single-symbol start config:**
  `symbol_weight(&wpds.initial_symbol)` (`verify.rs:60`) and
  `accepts_initial_config(automaton, &wpds.initial_symbol)` (`cegar.rs:447`). The latter's own
  doc-comment states: *"For single-symbol stack configurations, we just check if q is directly a
  final state."* These answer "is `⟨p, γ₀⟩` (a ONE-element stack) backward-reachable to the target?".

A per-cursor liveness query is a different question with no existing implementation. A cursor
configuration is `(WpdaState, multi-frame StackSymbolV2-stack)`. Answering "is THIS cursor's
configuration in `pre*(F)`?" requires three pieces that do **not** exist on the analysis surface:

1. **A runtime→model stack abstraction map** `StackSymbolV2`-stack (+ `WpdaState`) →
   `StackSymbol`-stack — the `abstraction_superset` map the (un-built) §P3 model commit names. No
   such function exists; `build_wpds` constructs the model from the *spec*, never from a runtime
   stack. The bp + marker frames (§4) carry parse state with no model symbol, so the map is
   partial/lossy — the very fidelity gap this inventory quantifies.
2. **A multi-symbol P-automaton word-acceptance routine** — run the cursor's stack word
   `γ_k … γ_1` from `initial_state` along transitions to a final state. **Every** existing helper
   (`is_symbol_accepted` :335, `symbol_weight` :384, `is_symbol_in_any_configuration` :375,
   `accepts_initial_config`) is single-symbol. Writing the multi-symbol path walk is NEW machinery.
3. **The whole-stack `stack_fully_modeled(cursor)` guard substrate** (round-2 N2) — a monotone
   per-cursor "carries-unmodeled-frame" sticky bit, set at push of any marker/recovery/lex-fork
   frame. New per-cursor state.

All three are new modeling beyond `prestar`/`is_symbol_accepted`/`reachable_symbols`. Per the
constraint, **deliverable 3 STOPS at this recorded statement of what it would need.** Building the
runtime probe is forbidden here. (The shadow plumbing fields/counters are likewise NOT added — the
sub-deliverable does not reach the wiring stage.)

This is the SAME conclusion the entry gate reaches by the independent must-add argument (§6): the
skeleton is too coarse for the runtime configurations, so neither the offline model nor the runtime
probe is admissible without the ≥15 must-add extensions. **The two arguments converge.** The
predicted `prestar_shadow_incremental_over_parikh < 3%` (the recorded negative) stands by derivation:
the only obligation-bearing classes (the infix triggers) live in `InfixLoop`/`InfixContinuation`
configs that are must-add — exactly the configs a skeleton liveness query cannot soundly touch — so
a *sound* (in-model-only) prestar shadow would query an empty set on these grammars, giving an
incremental of **0%** (mechanism-derived, identical in spirit to the P2 D-commit's mechanism-derived
zero @ `edac0084`).

## 8. Forward use (the census is the deliverable)

Even with P3 stopped, this table is the durable artifact. The must-add column **is** the work-list
for any future modeling effort that wants a configuration-faithful WPDA:

- **Dovetail** (the next track): its saturation/extraction agreement needs precisely this
  runtime→model correspondence; classes 1–11 are where a naïve `(cat, rule, pos)` model and the real
  engine diverge.
- **A future P3 revival** (only on an unexpectedly passing gate for some other grammar): would
  consume rows 12–19 of §3 and §4 as the Γ-extension list, and the `restricts-only` proof sketches
  as the `abstraction_superset` obligations to discharge.
- **P4** already routes around this: `admissible_bound_exact_first` is stated table-free (lex-min
  realization order, no prestar table) precisely because, per this inventory, the weighted skeleton
  bound is not admissible over the real frontier (plan §P3 "weighted by-product STRUCK as a P4
  input").

## 9. Verdict summary

| Deliverable | Outcome |
|---|---|
| 1. Step-(-1) transition inventory | ✅ this doc (§3–§5) — 18 states + 5 frame kinds + 22 actions, each tagged |
| Entry gate (`K = 3`) | ❌ **FAIL** — must-add = **17** (floor 11), ≈ 5.7×K (prediction: ~5×, ≥15) |
| 2. Recorded STOP | ✅ §6 — no `PreStarLiveness.v`, no enforcement, no allow-list |
| 3. Diagnostic shadow `prestar_shadow_incremental_over_parikh` | ⏹ **honesty STOP** (§7) — the runtime query needs new modeling (abstraction map + multi-symbol word acceptance + `stack_fully_modeled`); the plan forbids building it. Predicted/derived incremental **0% < 3%** stands. |
| Battery (P3 `=shadow` behaviorally inert) | ✅ N/A — no shadow mode shipped; tree is doc-only + ledger (§verification in `02-program-ledger.md`) |
