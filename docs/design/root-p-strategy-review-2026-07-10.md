# ROOT-P Deep Strategy Review — 2026-07-10

**Status:** review for user decision · **Author:** Claude (Fable 5) · **Scope:** the deep-`@` parse-performance tail (ROOT-P), the canonical-GLL campaign verdicts, and the full space of alternative strategies (industry-standard, SOTA, novel, parallel).

---

## 1. Executive summary

1. **The campaign's terminal verdict — "single-level poly frontier cannot deliver arbitrary-depth readings; real mechanism limit" — is correct for the arms that were tested but does NOT transfer to canonical GLL.** Every refuted arm (bounded-k fold, coarse fan, exact fan, caller-dedup, P2CORE, recursive-pop) wrapped *classic cursors that carry semantically load-bearing state outside the descriptor key* (deep `sppf_stack`, `edge_stack`, lex triple). Scott–Johnstone-style GLL has a machine-checked-grade completeness argument precisely because a descriptor `(L, u, i, w)` carries **nothing else**: identical descriptors have identical futures, so add-once dedup can never "drop a derivation before it is built." The observed loss is the signature of **pack-at-reduce** (n-ary packings interned from the classic per-cursor stack at reduce time) instead of canonical **pack-at-advance** (binarized `getNodeP` intermediates interned at every symbol shift). This review pinpoints that discrepancy with code receipts (§4).
2. **A grammar-side strategy the campaign never tried was surfaced, probed the same day, and partially refuted.** New probes (§5) show the deep-`@` exponential axis is dominated by the ~10-rule `@`-led send *sugar family* (`POutputNil/Quoted/Short/…Empty/…Persist`) whose members build **byte-identical ASTs** on the exploding inner shapes (the repo even ships `normalize_send_sugar_canon`, a downstream canonicalizer unifying these eval-equal variants for `term_eq`/COMM — institutional confirmation the multiplicity is semantically void where it explodes). However, the executed deletion probe (§6.1) proved the family is **not removable**: the "redundant-looking" rules carry genuine coverage and Display-distinct readings on Name-shaped inners (`grp_d*` → ERR, `@(c)!(0)` loses its NParen reading, `@x!(for…)` breaks), and the residual frontier stays exponential. Grammar normalization therefore survives only in its full **FGLL-style factoring** form (shared-prefix spine + union inners + late constructor binding — a codegen feature, medium effort, delivery unproven), demoted from "cheap likely fix" to "composable follow-on."
3. **The banked coarse-fan `k=4` arm is now measured** (§6.3): reading-exact and sub-second through depth 3 (`2/2/4`, `owner=2`, `-3!=1`, `@a!(0,1)=1`), and it makes sim pass ×3 (24/94/33 s vs the 1800 s cap) — but it **hard-rejects valid input at depth ≥ 4** and on `@x!(for…)` (which sim silently skips). It is an explicitly-gated interim at best, never the fix.
4. **Recommended strategy (§8): the descriptor-pure canonical rebuild (S2) under the corrected design rules (§4.4)** — not the previously-planned node-relabeling (which would have kept classic stacks on cursors/edges and hit the same wall), and not bounded-`k` banking. It is the only option with a literature-grade guarantee covering the failure mode, and ~70 % of its substrate is already built and validated in-tree. FGLL-style factoring composes with it later as a constant-factor divider; parallelism (§7) is a constant-factor multiplier, not a fix for an exponential.

---

## 2. Problem statement and hard data

`sim_rhocalc_proptest_campaign` (50 cases of `arb_proc(3)`, ≤ 500 chars) exceeds the 1800 s CI cap stochastically — the ~0.4 % pathological tail is deep-`@` terms. The deterministic reproduction is the grouping ladder

```
gen_grp(d):  @Nil!(core_d)   where   core_0 = @Nil,   core_i = @(core_{i-1})!()
```

Measured this session (dev profile, classic = HEAD engine; arm = `CANONICAL_GLL_ENABLED=true` + `PRATTAIL_CGLL_BINARIZE=1 PRATTAIL_CGLL_RETSLOT=1`, default `k=4`):

| term | readings (GT) | classic wall | classic growth | k=4 arm wall | arm readings | arm `max_U_per_pos` |
|---|---|---|---|---|---|---|
| `grp_d1` | 2 | 1.2 s | — | 0.2 s | 2 ✓ | 4 083 |
| `grp_d2` | 2 | 14.5 s | ×12.1 | 0.2 s | 2 ✓ | 5 709 |
| `grp_d3` | 4 | 148.8 s | ×10.3 | 0.3 s | 4 ✓ | 6 328 |
| `grp_d4` | ? | **TIMEOUT > 700 s** | ~×10 | 0.3 s | **ERR** ✗ | 6 166 |
| `grp_d5` | ? | TIMEOUT (> 200 s; ledger: d≥5 also stack-overflow-prone) | — | 0.4 s | **ERR** ✗ | 6 328 |
| `@x!(for(@y<-z){Nil})` | 1 | fast | — | 0.1 s | **ERR** ✗ | 1 425 |

Two facts frame everything:

- **The failing inputs are ~35 characters.** Any textbook cubic general parser (Earley–Scott, GLL, BRNGLR) processes a 35-token input in well under a millisecond-to-seconds regardless of ambiguity *count*, because derivations are packed, not enumerated in the frontier. A 148 s parse at `n = 30` is 5–6 orders of magnitude off the complexity class the algorithm family guarantees. This is a bookkeeping-discipline gap, not intrinsic hardness.
- **The frontier explosion is ~10×/level while genuine readings grow 2 → 2 → 4.** The engine pays exponential work to keep apart states that mostly do not correspond to distinct readings.

---

## 3. What the campaign established (compressed, honest)

Validated and reusable (all live in-tree, dormant behind `const CANONICAL_GLL_ENABLED=false` @ `wpda_walker.rs:718`):

- `gss.rs` is a correct Scott–Johnstone GSS: node sharing, slot/`operand_w`-labelled edges with identity `(target, operand_w)` (gss.rs:834, 1450-1453), `gll_pop` edge fan, and the **P-set contingent-pop replay** (gss.rs:811-814, `gll_create`@1435) — the piece naïve implementations forget.
- Binarized SPPF with hash-consed `Intermediate`/`getNodeP` (`sppf.rs`, Stage E1) and packed `symbol_packings` (Tomita §6.4 / Scott–Johnstone / Goodman semiring discipline), plus `link_packing_to_symbol` with ⊕-fold weights.
- A `{R, U, P}` descriptor worklist driver (`step_canonical`) with budget, instrumentation, and a large flag matrix for A/B.
- The reduce-once/push-z pop, `SYMONLY` structural-pop deferral, the return-slot **key** discovery (fixes `-3!` = 1), and the coarse-fan `k=4` arm (exact through d3 — §6.3).

Refuted (each verified, with the *stated* reason):

| arm | verdict | stated mechanism |
|---|---|---|
| cursor-level SLOT packing (Stages 2+3) | sound but non-delivering | merge fires post-materialization; transient fanout still exponential |
| arc-level RootpSlot dedup | proven runtime no-op | ingest tier re-applies a criterion its input already satisfies |
| bounded-k fold (`cgll_retslot_key_u`) | under-covers | fixed `k` cannot cover arbitrary depth; `k ≥ depth+1` |
| caller-dedup by return-slot key | insufficient | `-3!` callers distinct at every bounded level |
| P2CORE single-level node identity | refuted | needs `k ≥ 2·depth+2`; collections over-fire |
| recursive-pop (PoC-0 + clean test) | NO-GO | "loser dropped at add-once before it reduces ⇒ its packing never built" |

The clean test's own nuance is the pivot of this review: *the readings ARE packable (they share the goal `Symbol` as 2 packings); the distinction lives in the enclosing return chain the single-level poly frontier can't preserve.* §4 shows this is exactly the state of affairs canonical GLL is designed for — and why the executable arms still lost it.

---

## 4. Central re-analysis: the "mechanism limit" is an artifact of the hybrid

### 4.1 The theory that must not be contradicted

- **GLL** (Scott & Johnstone 2010; parse-tree generation 2013) is worst-case **O(n³)** and **complete**: the SPPF contains *every* derivation. Descriptors are `(L, u, i, w)`; `U` is add-once; `P` replays pops for late edges. The 2010 paper names this engine's exact disease: with stack-carrying "elementary descriptors" *"the number of descriptors created can be exponential in the size of input"*; the cure is *"combining the stacks into a single, global graph structure, a GSS, recording only the corresponding stack top node in the descriptor."*
- **Afroozeh & Izmaylova, "Faster, Practical GLL Parsing" (CC 2015)** replace the original slot-labelled GSS nodes with **`(nonterminal, position)` nodes and return-slot + left-context-`w` on edges** (edge dedup on `(L, w, target)`) — with a semantic-equivalence argument, preserved cubic bounds, and **10× measured speedup on a highly ambiguous grammar**. This is decisive for this codebase: the campaign's recurring conclusion "GSS-by-`(pos,symbol)` is the architectural root" blames a node identity the literature proves is **not** an obstacle. The caller distinction living "only as 2 operand edges on the shared node" (gss-by-slot plan §"WHY G/O merge today") is the *correct canonical arrangement*; the pop edge-fan is where it re-materializes. CC'15 further proves the descriptor's `w` is **functionally determined by `(L, u, i)`** (the span-canonical hash-consed node), so descriptor dedup *cannot* lose derivations — new derivations of a span attach to the shared node via `getNodeP` packing even when the descriptor is a `U`-duplicate; and with the `(A,i)` GSS, *"there is at most one call to getNodeP with the same arguments."*
- **FUN-GLL / BSR** (van Binsbergen, Scott & Johnstone 2018-2020; BSR = Scott, Johnstone & van Binsbergen, SCP 2019) goes further: descriptors are **pure triples** `(slot, l, k)` with *no GSS node object and no SPPF node at all*; all derivation data lives in a global monotone binary-subtree-representation set with proven soundness/completeness. The frontier provably never needs to carry derivation state. (Johnstone's SLE 2023 "A Reference GLL Implementation" is the current executable reference in this style.)
- **BRNGLR** (Scott, Johnstone & Economopoulos 2007), with Johnson 1991/Kipps: the same lesson from the LR side — unbinarized length-`m` reduction searches enumerate `Θ(n^{m-1})` stack paths (standard GLR is O(n^{ρ+1})); binarizing the reduction search on the fly restores O(n³). This engine's per-cursor `edge_stack` replays are that path enumeration in disguise, compounded per nesting level.
- **Iguana / data-dependent GLL** (Afroozeh & Izmaylova, PEPM 2016; Yakker, POPL 2010): operator precedence enters as **finite-domain parameters on nonterminals + slot constraints checked at descriptor creation**, keeping the cubic bound. This is the sanctioned fusion of Pratt binding powers with GLL — and this engine already does it right (`WpdaState` embeds bp in the slot); it is one of the parts to *keep*.
- **Independent 2026 benchmark** (Vo et al., arXiv:2606.08465): RNGLR/BRNGLR median ×3.0 vs LR(1), GLL ×6, Earley ×10 across 22 grammars — engine *family* matters less than the sharing invariants. Fix the driver, keep the substrate.

The common design law: **anything a continuation needs must live in one of the two shared graphs (GSS for return context, SPPF for derivation content), never on the walker state; the walker state must be exactly the four canonical coordinates.** Then add-once dedup is trivially lossless: identical descriptors have identical futures.

### 4.2 Where this engine deviates (code receipts)

1. **The descriptor `w` is not span-canonical.** `cgll_descriptor_w` (wpda_walker.rs:22370) is the *owner-masked shallow ident of the single top* of the classic per-cursor `sppf_stack`. The deeper stack entries — the partial left context of the in-progress rule — are **outside the key** in every poly arm, and folded in only by the deliberately-exponential `SOUND`/`SOUND_SPPF` probe arms (22348-22357). Canonical GLL has no such unkeyed residue: the left context is one binarized `Intermediate(slot, lo, hi)` id, hash-consed, with divergent same-span partials **packed inside it at `getNodeP` time**.
2. **Packing happens at reduce, not at advance.** Reduces intern n-ary packings from the classic stack (`emit_fire_action` → `intern_packing → link_packing_to_symbol → intern_push`). Hence the clean-test observation "the loser is dropped **before it reduces** ⇒ its distinguishing packing is **never built**": under pack-at-advance that packing would already exist by the time any merge could occur. The PoC's packing-on-merge (design C) no-op'd for exactly this reason (`pack_newlinks=0`).
3. **Resume needs classic stacks.** `gll_create` snapshots `caller_sppf_stack`/`caller_edge_stack` onto edges; resumed callers restore them; per-caller re-reduce corrupts arity (`retslot_edges` refutation). In canonical GLL a resume is `(L_ret, u_caller, i, y = getNodeP(L_ret, w_edge, z))` — four coordinates, no stacks — because semantic material is recovered from the packed forest at realize time, not from live stacks.
4. **`E1` binarize exists but is a parallel shadow, not the cursor discipline.** `cgll_w` threading was even stripped (`strip_cgll_w`) in several arms; where threaded, it *coexists* with the classic stack rather than replacing it, so the unkeyed residue remains.

### 4.3 Reconciling the clean-test refutation

The clean test proved: two derivations reaching the same `(inner_state, immediate-return-node, pos, top-Symbol)` with different return-chain continuations merge, reduce once, push one `z`, and the second enclosure is unrecoverable. Under descriptor purity this state of affairs **cannot arise**:

- If the two lineages differ in *future* descents, they differ in `(L, u, i, w)` **now** — a cursor's future is a function of its descriptor alone — so they never merge. The prior arms merged them because the differing state (deep stack / return chain) was real but **unkeyed**.
- If they differ only in *past* (how the same span was derived), canonical `w` is the same id and the difference is already **packed inside** it; merging is lossless by construction.
- Enclosing-context differences are per-**edge** (`w_edge` on the GSS edge, distinct `L_ret` slots), recovered by the pop fan + P-replay — both already implemented correctly in `gss.rs`.

So the refutations compose into: *the hybrid* (canonical bookkeeping around classic stack-machine cursors) cannot be both poly and exact — true, thoroughly proven by ~25 agents, and consistent with BRNGLR's account of why stack-materializing Tomita variants degrade. Canonical GLL itself remains untested here **and carries a literature-grade guarantee**. The `⚠★` memory directive ("verify a 'limit' is MATHEMATICALLY general, not an architecture artifact") lands precisely.

### 4.4 Design rules for a descriptor-pure canonical arm (the corrected S2)

1. Descriptor = `(L, u, i, w)`, nothing else influences stepping inside the canonical arm. `L` = grammar slot **including** the Pratt context (`WpdaState` already embeds bp — data-dependent-GLL style, cf. Iguana's operator-precedence-as-parameters); `u` = GSS node (`(pos, symbol)` per A&I is fine); `w` = binarized `getNodeP` intermediate id (never a stack, never a shallow top).
2. `getNodeP`/`getNodeE` at **every** symbol advance; packings for same-`(slot, lo, hi)` join at creation. Reduce = `gll_pop` + per-edge `y = getNodeP(L_ret, w_edge, z)`; no classic-stack restore, no re-reduce.
3. Semantic actions, weights, `output_cat`, owner gates read from the **popped `z`'s packing family** (P4's "route every read through z" work item — it is not optional; it is the discipline).
4. Collections ride the `w`-axis (accumulator = intermediate spine), binders get their own slots (`is_descent` must classify scope-entry actions), lex provenance rides `Packing.weight` (⊕-fold) — all three already designed in the recpop plan and unchanged.
5. Election/enumeration only at realize (lazy); the single-result path never materializes the reading set.

Everything in rule 1–5 exists in-tree except the discipline itself: the stepping logic for the canonical arm must be derived from `L` + the two graphs (a slot-driven interpreter), not delegated to `engine.step` over classic cursors. That is the honest multi-week core of S2 — and the *only* genuinely new build.

---

## 5. The new empirical decomposition: genuine vs spurious ambiguity

Probes on the classic engine (this session):

| term | readings | Display strings | verdict |
|---|---|---|---|
| `@Nil!(@(@Nil)!())` (d1) | 2 | `@Nil!(@(@Nil)!())`, `@Nil!(@@Nil!())` | **genuine** (grouping attribution) |
| `grp_d3` | 4 | 4 distinct bracketings | **genuine**, slow growth |
| `@Nil!(@Nil!())` (`owner=2` gate) | 2 | **identical** ×2 | **spurious** (sugar-rule attribution) |
| `@c!(0)` | 2 | **identical** ×2 | **spurious**: `POutputQuoted` → `NQuote(name_pattern_to_proc(NVar c)) = NQuote(PVar c)`; `POutputShort` → `NQuote(PVar c)` — **byte-identical ASTs** |
| `@(c)!(0)` | 3 | 1 distinct + identical ×2 | mixed |
| `@1!(0)`, `@"k"!(0)`, `@Nil!!(0)` | 1 | — | only `Short` matches |

The `@`-led send family (`rhocalc.rs:138-290`: `POutputNil/PPersistOutputNil/POutputQuoted/POutputShort/PPersistOutputShort` + the five `…Empty` twins, plus `…2Plus` twins further down) was *written as ordered-choice fallback* — the comments say so explicitly ("only when that path fails … do we fall through") — but a generalized parser runs all of them in parallel at every `@`, and each nesting level multiplies. This matches the campaign's own strongest measurement: masking `@`-trigger *owner* identity collapsed the d4 frontier **397 643 → 583 (682×)** — owner identity *is* sugar-rule identity. The repo itself confirms the variants are eval-equal by design: `languages/src/rhocalc/runtime.rs` ships `normalize_send_sugar_canon` (2026-07-06), a deep canonicalizer that folds every `@`-send sugar variant to the same `POutput/PPersistOutput(NQuote(chan), payload)` target *because* "`POutputNil(q)`, `POutputShort(PZero, q)`, and `POutput(NQuoteNil, q)` all denote" the same process — i.e., the engine pays exponential frontier to keep apart states a later pass explicitly re-unifies.

Consequences:

- The exponential axis is dominated by semantically-void multiplicity. The genuine reading set (2/2/4/…) is small and slow-growing at the depths that matter.
- The `owner=2` A/B gate pins an artifact, not a semantic property. Any strategy that legitimately collapses same-AST duplicates will change such pinned counts — that is a *test expectation* change, not a semantics change (flagged for user sign-off; "never disambiguate early" is honored because nothing distinct is being merged: the ASTs are byte-identical, and where they are *not* identical the alternatives must be and are kept).

---

## 6. Strategy options

### 6.1 S1 — Grammar-side normalization of the sugar family (NEW; recommended first)

Express the ordered-choice intent so the engine never materializes the parallel same-AST lineages. Three realizations, in increasing generality:

1. **Spec-level factoring** (rhocalc only): replace the 10-rule family with a factored skeleton (`"@" inner "!"|"!!" "(" payload? ")"`) with a late-bound fold that dispatches on the inner shape (all folds already build `POutput/PPersistOutput(NQuote(…))`). Requires the spec DSL to express the inner union (`Nil`-kw | `Name` | `Proc@220`) — may need a small codegen feature.
2. **Codegen shared-prefix factoring** (generic, preferred): a spec-compilation pass that left-factors same-category rules sharing a literal prefix into one dispatch spine with late constructor binding. Benefits every bundled language; aligns with the "prefer generalized solution" standing preference. **This is published technique with measured wins: FGLL** — Scott & Johnstone, *"Structuring the GLL parsing algorithm for performance"* (SCP 125, 2016): GLL over *factorised* grammars traverses shared prefixes once, descriptors per factored slot rather than per alternative, constructors bound at packed-node-extraction time, "significant speed up" over base GLL. S1 is FGLL's transform applied at the WPDA spec-compiler level.
3. **Priority/preference pruning** (industry standard: SDF2/Spoofax `prefer`/`avoid`; Iguana's data-dependent disambiguation): keep the rules, add the *declared* ordering the comments already describe, and prune dominated same-span alternatives at the `@`-cohort dispatch. Smallest change; preserves rule identities (weights/owners); the pruning is exactly "if the preferred rule accepts this span, drop the fallback's duplicate." (Related literature: Adams & Might, OOPSLA 2017 — structure-preserving grammar⨯tree-automaton intersection; de Souza Amorim et al. 2018 — contextual deep-priority disambiguation moved to parse time at near-zero overhead.)

**PROBE EXECUTED (2026-07-10, same session — deletion variant REFUTED).** The cheapest falsifier — scratch-disabling the six provably-AST-identical-looking rules (`POutputNil`, `PPersistOutputNil`, `POutputQuoted` + the three `…Empty` twins) and re-running the battery on the classic engine (`scratchpad/zz_probes/logs_s1probe/`) — produced:

| term | baseline | S1-deletion | verdict |
|---|---|---|---|
| `@Nil!(@Nil!())` (owner) | 2 (identical ×2) | **1** | ✓ sugar-dup collapse confirmed where subsumption is real |
| `@c!(0)` | 2 (identical ×2) | **1** | ✓ same |
| `grp_d1..d3` | 2/2/4 | **ERR / ERR / ERR** | ✗ genuine readings LOST — `POutputQuoted` alone covers Name-shaped inners like `(@Nil)` (no Proc parse exists for them) |
| `grp_d1..d3` wall | 1.2/14.5/148.8 s | 0.7/8.7/83.5 s | ✗ residual frontier **still exponential** (~10×/level) — the remaining `@`-owners (Short/persist/2Plus/Name-rules) still multiply |
| `@(c)!(0)` | 3 (1 distinct + 2 dup) | **1** (ungrouped only) | ✗ the genuine NParen-preserving reading is dropped |
| `@a!(0,1)` | 1 | **2** | ✗ duplicate *gained* — lineage interplay is fragile under ad-hoc rule surgery |
| `@x!(for(@y<-z){Nil})` | 1 | **ERR** | ✗ coverage broken |

Conclusions: (a) the *diagnosis* stands — where subsumption is real the duplicates vanish with zero semantic loss; (b) rule **deletion** is refuted — the family's members carry genuine, non-obviously-overlapping coverage; (c) only full **factoring** (one shared-prefix spine, inner slot = the *union* `Nil`-kw | `Name` | `Proc@220`, constructor bound late at the divergence point — exactly FGLL's transform) can normalize the family without losing readings, and that is a codegen feature with careful semantics, not an afternoon's work; (d) even successful factoring is only *proven* to collapse the sugar axis — whether the residual (grouping-attribution chains through depth) is polynomial for the classic engine is plausible (shape-guard floor grew ~linearly: 32/244/404/616) but **unproven**. S1 is therefore demoted to a composable follow-on/companion to S2, not the primary path.

### 6.2 S2 — Descriptor-pure canonical GLL core (the corrected rewrite)

§4.4. Multi-week; the risk concentrates where the existing plans already put it (P3 collections/binders, P4 `output_cat`/eager-firing, C7 threading, FV) — but the *core mechanism risk* the campaign priced as "genuinely uncertain / shadow-mirage" is retired by the literature guarantee once descriptor purity is the design rule. Prior "single-level key" refutations do not apply: they keyed hybrids. S1 composes with S2 (smaller constants, fewer packings).

### 6.3 S3 — Bank the coarse-fan `k=4` arm (the pending option #2)

Measured this session: exact multisets and sub-second walls through d3; `-3!=1`, `@a!(0,1)=1`, `@(p)` reject preserved; `max_U_per_pos` plateaus ~6.3 k. **But**: hard `ERR` on valid `grp_d4`/`grp_d5` and on `@x!(for…)` — banking requires an explicit depth/coverage gate with a fallback story:

- fallback-to-classic for gated inputs = a dual runtime path (standing policy: avoid; fail-closed only), and re-admits the exponential for exactly the inputs that need help;
- explicit reject = a *language-level* scope-down on valid input (needs explicit user authorization by standing directive).

sim ×3 under the arm: **PASS in 24 s / 94 s / 33 s** (vs the 1800 s cap; classic times out stochastically) — the arm *would* make CI green. Interpretive caveat: the sim harness silently `continue`s on unparseable inputs, so the arm's `ERR` classes (`d ≥ 4`, `@x!(for…)`) do not fail sim — they silently shrink its effective coverage. Shipping the arm without an explicit gate is therefore precisely the "silent scope-down" the standing directives prohibit. Even gated, S3 is an interim CI-unblock, not a fix; S1 likely dominates it on every axis within days.

### 6.4 S4 — Parallelism (assessed, not a fix)

- **Descriptor-worklist parallelism** (work-stealing over `R`; lock-free/sharded `U`, `P`, SPPF interners — matches the standing non-blocking preference): sound, literature-supported, and a good fit *after* the frontier is poly; a constant-factor (≤ cores) multiplier. It cannot rescue a 10×/level exponential — parallelizing 745 k cursors at d4 buys one level (~16 cores ≈ one ×10) and loses again at d5.
- **Portfolio racing** (classic ∥ canonical, first-finisher): conflicts with the no-dual-runtime-paths policy; rejected.
- **CI-level sharding** of the proptest campaign: masks the tail; violates the no-band-aid standing directive; rejected.
- **SIMD/GPU**: the hot loop is pointer-chasing frontier bookkeeping on ~35-token inputs; no data-parallel shape. GPU CFPQ/Valiant-style matrix parsing (Azimov/Grigorev et al.) targets long inputs / graph queries where `n` dominates — here `n ≈ 35` and the grammar constant dominates; forest extraction on GPU is immature. Rejected for this problem.

### 6.5 S5 — Other surveyed-and-rejected

- **Earley–Scott + Leo as a sidecar engine**: algorithmically equivalent to S2's endpoint (Leo-style right-recursion sharing emerges from canonical GLL's GSS sharing); would be a *third* engine with the same P3/P4 integration bill — strictly worse than finishing the canonical arm.
- **Derivatives / parsing-with-zippers**: elegant, but measured constants are worse than GLL in every published comparison; nothing to gain here.
- **Memoized/packrat Pratt**: memoizing `(pos, cat, bp)` sub-parses *is* the GSS/SPPF sharing, minus ambiguity handling — a re-derivation of S2, not an alternative.
- **Relational parsing** (Herman, PLDI 2020 — memoized transition relations of atomic languages; cubic worst-case, linear on LR-regular, orders-of-magnitude wins over the best Earley/GLR/GLL in its benchmarks): the strongest post-2015 algorithmic idea in the space, noted for completeness — but it is recognition-first with a structuring layer on top, and porting the WPDA weight/collection/binder semantics onto it would be a fourth-engine bet with none of the in-tree substrate reuse S2 gets. Revisit only if S1+S2 both disappoint.

One more SOTA fact that matters to this repo specifically: **no mechanized GLL/GLR correctness proof exists in the literature** (closest: a verified *Earley* parser, ITP 2024; verified ALL(*), CPP 2021). The P5 zero-admission Rocq obligations this campaign already scaffolded (`CanonicalGllDescriptorBound.v`, `RootPSlotPackingPreservation.v`) would, if discharged against the descriptor-pure S2 core, be novel territory — and the BSR soundness/completeness properties (SCP 2019) are the natural formal spec to port.

---

## 7. What the current architecture already gets right (leverage inventory)

The review's corrections are narrow because most of the stack is already the SOTA design: correct GSS with P-replay; packed binarized SPPF with semiring weights (Goodman); demand-driven single-result driver; Pratt bp inside the state (= data-dependent-GLL slot parameters); byte-identical const-gated A/B discipline with trap-reverted flips; a reading-multiset oracle harness; and zero-admission FV scaffolding (`CanonicalGllDescriptorBound.v`, `RootPSlotPackingPreservation.v`) whose lemma statements (poly bound, exact pop, packing preservation) are exactly the right obligations for S2. S1 and S2 are completions of this architecture, not departures.

---

## 8. Recommended roadmap (updated after the same-session probes)

The hypothesis ladder was already exercised this session: the cheap S1-deletion falsifier ran and was refuted (§6.1), and the k=4 arm was measured end-to-end including sim ×3 (§6.3). What remains is the strategy with the guarantee:

1. **Primary: S2 — descriptor-pure canonical core** under §4.4's design rules, staged with the standing Plan-agent + red-team discipline:
   - **PoC (the go/no-go)**: a slot-driven stepping loop for the rhocalc send/grouping fragment where the canonical arm's cursor state is *exactly* `(L, u, i, w)` — no `sppf_stack`, no `edge_stack`, no lex triple; `getNodeP` at every advance; pop = edge fan + P-replay only. Gate: ladder `d1..d5` depth-uniform poly `|U|` **with no `k` anywhere** + exact Display-distinct multisets + CF-core/`-3!`/`@(p)`/`@a!(0,1)` unchanged. This directly tests the one thing every prior arm violated, and the CC'15 counting argument predicts it passes.
   - Then P3 (collections on the `w`-axis; binder scope-entry classified `is_descent`), P4 (`output_cat`/weights routed through the popped `z`'s packing — the known risk-dominant integration), P5 (zero-admission FV: the existing `CanonicalGllDescriptorBound.v` / `RootPSlotPackingPreservation.v` obligations, targeting the BSR soundness/completeness spec — novel territory, no mechanized GLL proof exists), then the flip gate (full reading A/B + `gen_rhocalc_prop` 123/123 + 4-language + sim < 1800 s ×3).
   - Reuses `gss.rs`/`sppf.rs`/E1-binarize/worklist as-is; retires the k-fold key, slot-union fans, and every bounded-`k` compromise.
2. **Composable follow-on: S1-as-factoring** (FGLL-style shared-prefix factoring with union inners and late constructor binding, as a *generic codegen pass*) — a constant-factor frontier divider for every engine and language, informed by the probe's coverage pitfalls (`POutputQuoted`'s Name-inner coverage must ride the union, never be dropped). Do not attempt as rule surgery.
3. **S3 (only if CI must be green before S2's PoC lands, and only with explicit authorization):** bank the k=4 arm behind an explicit depth/coverage gate (deterministic pre-scan; loud reject or classic fallback — the fallback variant conflicts with the no-dual-runtime-paths policy and would need that policy explicitly waived); document the gated domain. The sim ×3 data (24/94/33 s) proves it would work as an interim; the `@x!(for…)` gap (P3 binder classification) must be fixed first regardless.
4. **Afterwards, optional:** worklist parallelization (work-stealing over `R`, lock-free/sharded `U`/`P`/SPPF interners — matches the standing non-blocking preference) as a wall-clock multiplier; the d≥5 recursion-depth overflow is structurally fixed by S2's explicit worklist.

**Decision points for the user** (everything else proceeds autonomously per the standing grind directive): (a) commit to S2 as the primary path (multi-week core surgery, staged, gated, dormant-until-green — the honest cost of the guaranteed fix); (b) whether S3's gated interim is wanted while S2 runs, and if its fallback flavor is preferred, an explicit waiver of the no-dual-runtime-paths policy for the depth gate; (c) whether byte-identical-AST duplicate *counts* in pinned multisets are artifacts that a future S1-factoring pass may legitimately change (the Display-distinct reading set is always preserved).

---

## 9. Citations (web-verified 2026-07-10)

Core algorithms:
- E. Scott, A. Johnstone. *GLL Parsing.* LDTA 2009 / ENTCS 253(7):177-189, 2010. DOI: 10.1016/j.entcs.2010.08.041 — descriptors `(L,u,i)`; the exponential-stacks quote; `U`/`R`/`P` sets.
- E. Scott, A. Johnstone. *GLL parse-tree generation.* Sci. Comput. Program. 78(10):1828-1844, 2013. DOI: 10.1016/j.scico.2012.03.005 — `(L,u,i,w)`; left-context `w` on GSS **edges**; `getNodeP`; cubic SPPF (Thms 2-3).
- A. Afroozeh, A. Izmaylova. *Faster, Practical GLL Parsing.* CC 2015, LNCS 9031:89-108. DOI: 10.1007/978-3-662-46663-6_5 — `(A,i)` GSS, edges `(u,L,w,v)` deduped on `(L,w,target)`; `w` functionally determined by `(L,u,i)`; 10× on highly ambiguous grammars.
- E. Scott, A. Johnstone. *Structuring the GLL parsing algorithm for performance* (FGLL/RGLL). Sci. Comput. Program. 125:1-22, 2016. DOI: 10.1016/j.scico.2016.04.003 — **factorised grammars = S1's literature anchor**.
- E. Scott, A. Johnstone. *GLL syntax analysers for EBNF grammars.* Sci. Comput. Program. 166:120-145, 2018.
- E. Scott, A. Johnstone, L.T. van Binsbergen. *Derivation representation using binary subtree sets.* Sci. Comput. Program. 175:63-84, 2019. DOI: 10.1016/j.scico.2019.01.008 — BSR; soundness/completeness spec (the natural Rocq target).
- L.T. van Binsbergen, E. Scott, A. Johnstone. *Purely functional GLL parsing.* J. Comput. Lang. 58:100945, 2020. DOI: 10.1016/j.cola.2020.100945 — descriptors as pure triples; no in-flight tree plumbing.
- A. Johnstone. *A Reference GLL Implementation.* SLE 2023. DOI: 10.1145/3623476.3623521
- E. Scott, A. Johnstone, R. Economopoulos. *BRNGLR: a cubic Tomita-style GLR parsing algorithm.* Acta Informatica 44(6):427-461, 2007. DOI: 10.1007/s00236-007-0054-z — with M. Johnson, *The computational complexity of GLR parsing*, and Kipps (in Tomita ed., *Generalized LR Parsing*, Kluwer 1991): unbinarized reduction search = O(n^{ρ+1}).
- E. Scott, A. Johnstone. *Right Nulled GLR Parsers.* TOPLAS 28(4):577-618, 2006. DOI: 10.1145/1146809.1146810
- E. Scott. *SPPF-style parsing from Earley recognisers.* ENTCS 203(2):53-67, 2008. DOI: 10.1016/j.entcs.2008.03.044
- M. Tomita. *Efficient Parsing for Natural Language.* Kluwer, 1985.

Precedence / data-dependence / disambiguation:
- A. Afroozeh, A. Izmaylova. *Operator precedence for data-dependent grammars.* PEPM 2016:13-24. DOI: 10.1145/2847538.2847540 — bp as finite-domain slot parameters + constraints, cubic preserved.
- T. Jim, Y. Mandelbaum, D. Walker. *Semantics and algorithms for data-dependent grammars* (Yakker). POPL 2010:417-430. DOI: 10.1145/1706299.1706347
- A. Afroozeh, A. Izmaylova. *Iguana: a practical data-dependent parsing framework.* CC 2016. DOI: 10.1145/2892208.2892234
- M.D. Adams, M. Might. *Restricting Grammars with Tree Automata.* PACMPL 1(OOPSLA):82, 2017. DOI: 10.1145/3133906
- L.E. de Souza Amorim, M.J. Steindorfer, E. Visser. *Towards Zero-Overhead Disambiguation of Deep Priority Conflicts.* Programming J. 2(3), 2018. arXiv:1803.10215
- E. Visser. *Syntax Definition for Language Prototyping.* PhD thesis, UvA, 1997. (SDF2 `prefer`/`avoid`)

Earley line / weights / verification:
- J.M.I.M. Leo. TCS 82(1):165-176, 1991. DOI: 10.1016/0304-3975(91)90180-A — right recursion linear.
- J. Aycock, R.N. Horspool. *Practical Earley Parsing.* Comput. J. 45(6):620-630, 2002. · J. Kegler. *Marpa.* arXiv:1910.08129
- J. Goodman. *Semiring Parsing.* Comput. Linguist. 25(4):573-605, 1999. · A. Opedal et al. *Efficient Semiring-Weighted Earley Parsing.* ACL 2023. DOI: 10.18653/v1/2023.acl-long.204
- M. Rau, T. Nipkow. *A Verified Earley Parser.* ITP 2024, LIPIcs 309:31. DOI: 10.4230/LIPIcs.ITP.2024.31 — no mechanized GLL/GLR proof exists; this repo's P5 FV would be novel.

Parallel / matrix / other engines (assessed §6.4-6.5):
- G. Herman. *Faster general parsing through context-free memoization.* PLDI 2020. arXiv:1902.06591
- A. Barenghi et al. *Parallel parsing made practical* (PAPAGENO). Sci. Comput. Program. 112:195-226, 2015. — requires unambiguous operator-precedence grammars.
- J.-P. Bernardy, K. Claessen. *Efficient parallel and incremental parsing of practical context-free languages.* JFP 25, 2015. — needs sparse charts.
- R. Azimov, S. Grigorev. *Context-free path querying by matrix multiplication.* GRADES-NDA 2018. DOI: 10.1145/3210259.3210264; all-path forest extraction GRADES-NDA 2021. DOI: 10.1145/3461837.3464513 — graph-scale wins only; rejected for n≈35 strings (Lee, JACM 49(1), 2002: subcubic ⇔ fast BMM).
- P. Darragh, M.D. Adams. *Parsing with Zippers.* PACMPL 4(ICFP):108, 2020. DOI: 10.1145/3408990
- H.-S. Vo et al. *An Empirical Comparison of General Context-Free Parsers.* arXiv:2606.08465 (2026) — BRNGLR/RNGLR ×3.0 median vs LR(1); GLL ×6; Earley ×10.

Measurement logs: `scratchpad/zz_probes/logs_k4bank/` (k=4 arm + classic ladder + sim ×3), `scratchpad/zz_probes/logs_s1probe/` (S1 grammar-normalization probe).

---

## Appendix A — S2 PoC OUTCOME (Stages B0–D, same day; verdict: GO)

The recommended S2 PoC (§8.1) was planned, adversarially red-teamed (8 protocol amendments — notably: structured ret-slot synthesis from action data, D2 nodes at `i` with per-edge `z`, a corrected accept criterion, and a full boundary-cursor fill-list), and implemented the same day as this review. The descriptor-pure engine (`step_canonical_pure`, opt-in via `PRATTAIL_CGLL_PURE` inside the const-gated canonical arm; default build byte-identical, smoke 166/166 at every stage) interprets the unchanged generated WPDA tables with cursor state exactly `(L, u, i, w)` — the decisive enabler being that the generated `engine.step` never reads the GSS or the frontier node's position.

**Result: the depth-uniformity thesis is CONFIRMED on the exact ladder that refuted every hybrid arm.**

| depth | readings (pure) | oracle | `max_U_per_pos` | wall |
|---|---|---|---|---|
| d1 | 2 | classic 2 ✓ + E1-GT shape-EQ | 260 | ~0.05 s |
| d2 | 2 | classic 2 ✓ | 290 | ~0.1 s |
| d3 | 4 | classic 4 ✓ | 291 | ~0.1 s |
| d4 | 8 | E1-GT exhaustive **8/8 multiset-exact** (classic parse: >700 s timeout; k=4 arm: hard ERR) | 291 | ~0.1 s |
| d5 | 16 | **analytic** (below) — classic route machine-infeasible (>300 GB) | **291 (plateau)** | 0.19 s / 28 MB |

No `k` exists anywhere in the pure path (grep-receipted). Forest well-formedness self-checks (span partition, exact leaf coverage, root span): `issues=0` at d1/d4/d5. Full final battery 17/17 including `@a!(1+2,3)` (the pre-declared P3.b limitation — it passed exactly, 2/2), single-result election TERM-EQ 13/13, `weight_drops=0` with shape-safe lex-weight carriers. During the gate the *classic* control arm reproduced ROOT-P (single-result d3 ≈ 5 min, d4 timeout), while the pure arm held the plateau.

**Analytic d5 derivation** (replaces the infeasible ground truth; ledger §D.1): for the ladder $`T(d)`$ the reading multiset is generated by the wrapped-step doubling $`w(k) = \{S(x), E(x) : x \in w(k-1)\}`$, $`|w(1)| = 2`$, with the unwrapped outer level contributing only the $`S`$-branch — giving

```math
R(1) = 2, \qquad R(d) = 2^{d-1} \ (d \ge 2)
```

derived by full case enumeration over the nine participating rhocalc rules (with the `prefix(220)` floor eliminating all Name-shaped readings at k≥1, and the byte-identical twin families packing rather than multiplying). It reproduces the measured 2/2/4/8 and its predicted d5 **multiset** (not just the count) matches all 16 measured ASTs exactly; two residual mechanism lemmas (D-U, D-N's `l_bp` extraction) are named P5-FV obligations.

**One semantics ruling** (decision point (c), receipted in the ledger): on `@a!(0,1)`-class terms the pure arm uniformly yields the byte-identical `POutputQuoted`/`POutputShort` twin pair that classic yields on `@a!(0)`, `@x!(0)`, `@a!(1+2,3)` but *loses* on long payloads to a proven fire-elide starvation (`CLASSIC-FIRE-ELIDE` trace: the per-cursor stacks starve the channel cast). The complete-forest count is correct; the gate criterion for byte-identical twin families is dedup-set equality + elected-term identity. Any committed test pinning the starved counts surfaces at P4 for explicit sign-off.

Remaining to productionize (task-tracked): P3 full-coverage overlays (kv-maps, Class-5/empty collections, optional groups, predicates, binder-scope opcodes for `lam`/`PNew` shapes, FrameCtx delimiter classes), P4 `output_cat`/weight ⊗-order parity through the popped-`z` packing + 4-language parity, P5 zero-admission Rocq FV (BSR-spec obligations incl. the two named lemmas), then the flip gate (const ON after `gen_rhocalc_prop` 123/123 + 4-language suites + sim < 1800 s ×3).
