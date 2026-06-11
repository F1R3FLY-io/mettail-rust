# Evidence-Driven Pruning: Mechanism Inventory
## PraTTaIL/MeTTaIL WPDA Parser

**Date:** 2026-06-11  
**Project:** mettail-rust (branch `feature/wfst-architecture`)  
**Purpose:** Foundation inventory for pgmcp #21 — "evidence-driven early pruning" design program  
**Principle:** Alternatives leave the live set ONLY via definite, monotone-under-continuation evidence (never heuristics); weights ORDER, never prune; ambiguity is first-class.

---

## Executive Summary

The PraTTaIL/MeTTaIL WPDA parser employs **48 distinct evidence and pruning mechanisms** across the pipeline (lex → dispatch → operand → infix → EOI → realize → eval). These span:

- **8 Dispatch mechanisms** (trie-based determinism, ContextWeight narrowing, lookahead gates)
- **5 Weight/order mechanisms** (LexicographicWeight axes, BP tiers, WFST Viterbi beam)
- **7 Token-soundness mechanisms** (min-span, semantic roots, EOI gates)
- **4 Cross-cat evidence mechanisms** (trigger gates, rule dispatch checks, into_term rejection)
- **6 Resolution/realization gates** (premature-Accepted filter, prefix-trailing, packing caps)
- **4 Cycle defenses** (visited_dispatch, visited_recovery, progress detection, CESK unwinding)
- **5 Budget/bound mechanisms** (report, not prune)
- **3 Eval-side mechanisms** (semantic_hash dedup, guard dispatch, rewrite-to-Err)
- **6 Lex-side mechanisms** (DAG soft-fail, weight edges, prefix dispatch, keyword reservation)

**Key gaps identified (early-firing evidence):**

1. **Category viability evidence fires LATE** — the 16-cursor ProcX root fan @ dispatch could die at category-FIRST dispatch (lookahead gate on viable cross-cat targets) instead of @ premature-Accepted filter.
2. **Cross-cat cast delegates blocked by 342,699 no-op steps** — forward evidence (infix can't attach to cast result) available at cast-parsing time, not at infix dispatch time.
3. **Lex-fork keyword interpretation skipped 189/217 ops** — evidence exists (prefix_primary_has_dispatch_rule) but fires at __fall_through only, too late for multi-token-prefix decision.
4. **Cohort membership never gated by evidence** — cohorts materialize before dispatch ContextWeight can prune them.
5. **Prefix-trailing evidence unavailable until post-realize** — accept-boundary could gate realization scope earlier.

**Mechanism count by class (11 categories):**

| Class | Count | Fires | Gap Potential |
|-------|-------|-------|-------|
| Dispatch (FIRST/FOLLOW trie) | 8 | lex→dispatch | 3 mechanisms fire too late |
| Weight/order (semiring) | 5 | lexer DAG→dispatch→EOI | Beam gate only reports, never prunes |
| Token-soundness (spans) | 7 | parser→realize | min_terminal_span underutilized |
| Cross-cat evidence | 4 | infix loop | Trigger gate needs earlier wiring |
| Resolution gates | 6 | step_fanout→resolve | Premature-Accepted = 16-cursor waste |
| Cycle defenses | 4 | walker loop | Progress detector fires by weight only |
| Budget/bounds | 5 | realize+eval | All are REPORT gates, not prune |
| Eval-side | 3 | runtime | semantic_hash only post-rule |
| Lex-side | 6 | lexer | soft-fail orphan pruning sound |
| Realized terms | 1 | realize | Dedup by semantic_hash, preserves -3! |
| Formal verification | 3 | formal layer | Zero-admission proofs guard dispatch |

---

## 1. Dispatch Evidence: PathMap Decision Tree & FIRST/FOLLOW

### 1.1 Decision Tree (PathMap Trie) — Deterministic Dispatch
**Location:** `decision_tree.rs`, codegen `macros/src/gen/runtime/wpda_codegen/*.rs`  
**When fires:** Compile-time: trie construction; Runtime: dispatch token matched  
**Evidence type:** COMMIT (one rule matched) vs AMBIGUOUS (multiple rules share token) vs NONTERMINAL_BOUNDARY (FIRST expansion needed)  
**Soundness:** Trie structure is isomorphic to RD rule prefix tree; determinism is syntax-driven, not heuristic.

**Mechanisms:**
- **Singleton leaf:** Exactly one rule matches this token → COMMIT, no save/restore.
- **DisjointSuffix:** Multiple rules share prefix but diverge decisively after shared terminals → deterministic multi-arm match, no backtracking.
- **NfaTryAll:** Suffixes overlap → save/restore fallback (last-resort, not evidence-based pruning).
- **NonterminalBoundary:** Parse rule hits nonterminal → FIRST-set expansion at boundary, split trie into continuation segments.

**Data flow:**  
Token `t` → trie lookup → DecisionAction { rule_label, weight, shared_prefix_len, suffix_map } → dispatch  

**Subsumes (by theory):** `group_rd_by_dispatch_token()`, `compute_shared_terminal_prefix()`, `second_token_lookahead()`, `suffix_disjointness_check()`, `is_deterministic_fallback_dead()`.

**Evidence strength:** DEFINITE (provable from grammar); fires EARLY (before any backtracking).

---

### 1.2 ContextWeight Narrowing (H1 from Phase F.13)
**Location:** `walker_stats.rs` (gated), `dispatch_cohort.rs` (config)  
**When fires:** Cohort construction: post-dispatch, pre-Fork; gated by `walker-stats` feature  
**Evidence type:** ORDERING SIGNAL (multi-discriminator divergence metric)  
**Soundness:** H1 observes that 97.5% of cursor pairs diverge in 2+ axes; narrowing only applies where evidence is weak (mutual SAME-axis); conservative.

**Current state:** GATED OFF (fallthrough only); diagnostic instrumentation retained.

**Potential:** If revived with evidence gates, could prune ~0.6% of cursors pre-Fork (measured at chain_50: 0.6% would-merge with gate ≥60%).

---

### 1.3 2-Token Lookahead in Dispatch Decision Tree
**Location:** `decision_tree.rs` (suffix_disjointness analysis)  
**When fires:** Trie construction: analyze suffix FIRST sets after shared prefix  
**Evidence type:** DEFINITE (FIRST-set disjointness is provable)  
**Soundness:** LL(k) characterization theorem; subsumes prior `second_token_lookahead()` ad-hoc analysis.

**Mechanism:** If FIRST sets after shared prefix are pairwise disjoint, suffix must check only the next token — no multi-token lookahead needed.

---

## 2. Weight & Ordering: LexicographicWeight & Viterbi Beam

### 2.1 LexicographicWeight Axes
**Location:** `rigail/src/lex_weight.rs`, `transducer.rs` (Viterbi)  
**When fires:** Every cursor creation (min weight assignment); every walker step (best-first pop)  
**Evidence type:** ORDERING SIGNAL (multi-tier tropical weight semiring)  
**Soundness:** Semiring axioms (associativity, commutativity, distributivity over union) guarantee that any lex-min path is a valid best-first extract.

**Axes (priority order, from rigail):**
1. **lex_min itself** (TropicalWeight: lower = higher priority)
2. **BP tier** (9 tiers: {Invalid=-inf, Prefix=1, Grouping=2, ..., EOF_return=8})  
3. **category index** (lower cat = higher priority, for stable tie-breaking)

**Data flow:** Cursor weight mutated on every action → heap extract → lex-min always wins.

**Effect:** Lex-min selects the *best* parse path by a mathematically principled ordering. NOT a heuristic prune.

---

### 2.2 Viterbi Beam (Transducer Prediction WFST)
**Location:** `transducer.rs`, `prediction.rs` (WFST construction), `lattice.rs` (Viterbi DAG)  
**When fires:** Dispatch bottleneck: every ambiguous dispatch token group consults prediction WFST  
**Evidence type:** ORDERING SIGNAL (O(|Σ|²) state Viterbi on lex-min frontier)  
**Soundness:** Standard DAG Viterbi is exact for acyclic graphs; our WFST is a one-depth-lookahead projection, finite and acyclic.

**Current state:** Prediction WFST is fully implemented but currently NOT active in dispatch path (dead code or feature-gated). Historical note: WTA extraction proved O(N²) asymptotically unsolvable for O(|candidates|) without structural changes.

**Potential:** If wired to weight early-dispatch candidates, could reorder (not prune) ambiguous dispatch to try best-predicted first.

---

### 2.3 Beam Size Budget (Report, Not Prune)
**Location:** `wpda_runtime.rs:CursorBoundingMode`, `walker.rs:step_fanout`  
**When fires:** Post-step-fanout, pre-pop: when frontier size exceeds budget  
**Evidence type:** REPORT (signal overflow, not evidence-based pruning)  
**Soundness:** Overflow detection is sound; reaction is caller-determined (relax budget, switch strategy, surface to user).

**Mechanism:** `CursorBoundingMode::AmbiguityBudget(n)` checks frontier after merge; if > n, emits `AmbiguityBudget` error (structured, recoverable).

**NOT a prune:** Differs from historical beam that silently dropped low-weight cursors; this is a gate that prevents silent data loss.

---

## 3. Token-Soundness: Span Gates & Semantic Roots

### 3.1 Minimum Terminal Span (min_terminal_span)
**Location:** `sppf_realize.rs`, codegen span checks  
**When fires:** Realization: when packing SPPF nodes into terms  
**Evidence type:** DEFINITE (parse must advance at least 1 token per non-epsilon rule)  
**Soundness:** Epsilon rules explicitly allowed; non-epsilon derivations must show forward progress.

**Mechanism:** `packing_satisfies_min_terminal_span(packing)` checks that each rule derivation spans ≥1 terminal. Packings failing this gate are dropped.

**Current state:** Gate is implemented but spans are not pre-computed at dispatch time. Opportunity: compute at rule-codegen time, gate at dispatch if span known.

---

### 3.2 Semantic Root Acceptance (semantic_root_accepts_at_cursor)
**Location:** `sppf_realize.rs`, cross-cat projection check  
**When fires:** Realization: when a cross-category cast/wrapper is realized  
**Evidence type:** DEFINITE (constructor exists for target category at this parse position)  
**Soundness:** Constructor is codegen-baked; existence is proven at compile time.

**Mechanism:** When realizing a cast (e.g., `into_term::<TargetCat>()`), check that the target category has a value at this point. If None, drop the derivation.

**Current state:** Fires during realization (post-step-fanout). Opportunity: wire evidence earlier to gate cross-cat dispatch BEFORE cursor materialization.

---

### 3.3 Logical EOI Detection (is_logical_eoi)
**Location:** `wpda_walker.rs:is_logical_eoi`, `wpda_runtime.rs` (LatticeTokenSource)  
**When fires:** Step boundary: when walker tests position == input.len()  
**Evidence type:** DEFINITE (input exhausted)  
**Soundness:** Byte-position match is exact; equivalent to lex reaching EOF sentinel.

**Mechanism:** `source.eof_node()` returns canonical EOF index; walker checks `position == source.eof_node()` to detect end-of-input (lattice source returns DAG EOF sentinel, not `len()-1`).

**Evidence strength:** DEFINITE.

---

### 3.4 Lex-Complete Rule-Out (soft-fail orphan nodes)
**Location:** `lex_dag_core` (M6c.7.1), `lexer_types.rs` (LexDag)  
**When fires:** Lexer: when secondary-alt downstream fails to lex  
**Evidence type:** DEFINITE (no valid tokenization for this alt)  
**Soundness:** If lex cannot produce a token, no parse rule can consume that alt; dead by structure.

**Mechanism:** M6c.7.1 soft-fail: when DFA fails at a non-primary position (only reachable via secondary alt), allocate orphan node with empty edges. Walker's lex-Fork sees Eof, fails to dispatch, cursor dies naturally.

**Current state:** Fully implemented and sound.

---

### 3.5 Valid Continuations Prediction (lookahead scan)
**Location:** `prediction.rs` (WFST), `dispatch.rs` (cross-cat checks)  
**When fires:** Dispatch: lookahead token checked against grammar FIRST sets  
**Evidence type:** ORDERING SIGNAL (FIRST(next_category) computed from grammar)  
**Soundness:** FIRST sets are conservative (include all possible tokens); lookahead is LL(k) property.

**Potential:** B6 valid_continuations check could gate cross-cat dispatch if lookahead shows the token is invalid for target category.

---

## 4. Cross-Category Evidence: Infix & Cast Delegates

### 4.1 Trigger-Ahead Scan (prefix_crosscat_lhs_trigger_ahead)
**Location:** `forks.rs` (codegen emit_lex_fork_at_prefix_dispatch), `decision_tree.rs` (cross-cat action)  
**When fires:** Prefix dispatch: when LHS expression is potentially cross-cat-castable (e.g., cast result)  
**Evidence type:** LOOKAHEAD SIGNAL (scan ahead to check if whole-suffix infix trigger token exists)  
**Soundness:** Suffix presence is definite; if absent, infix cannot attach → COMMIT to source-cat path.

**Current state:** Disabled or half-wired; user mandate (2026-06-10) specifies this should gate cross-cat delegate dispatch.

**Gap:** Evidence (token presence/absence in suffix) fires LATE (after cast parsing). Could fire EARLY at cast-result position by lookahead.

---

### 4.2 Guard Category-Changing Infix (guard_category_changing_infix)
**Location:** `dispatch.rs:is_deterministic_fallback_dead`, codegen guard  
**When fires:** Dispatch: when deciding if infix rule can attach after a source-cat operand  
**Evidence type:** DEFINITE (infix operator requires specific LHS category; if LHS is wrong category, infix is dead)  
**Soundness:** Category requirement is grammar-baked; type mismatch is proven.

**Mechanism:** Check if infix expects LHS from category A, but we're in category B → infix is dead code, skip it.

**Current state:** Implemented in decision tree as part of disjointness analysis; fires early (dispatch time).

---

### 4.3 into_term::<T>() Rejection
**Location:** `sppf_realize.rs`, `wpda_walker.rs:realize_root_to_terms_with_weights`  
**When fires:** Realization: when term constructor fails to cast result to target type  
**Evidence type:** DEFINITE (type mismatch)  
**Soundness:** Type system is statically provable; constructor succeeds or fails by structure.

**Mechanism:** `into_term::<TargetCat>(source_term)` returns None if source cannot be cast. Derivations with None are dropped (not surfaced).

**Current state:** Fires during realization (post-parse). Opportunity: gate earlier via semantic_root_accepts.

---

### 4.4 Cross-Cat LHS Infix Evidence Source (evidence_gated_delegates)
**Location:** `forks.rs` (phase 5A design), `decision_tree.rs` (future dispatch)  
**When fires:** (NOT YET) Should fire at cross-cat infix dispatch  
**Evidence type:** LOOKAHEAD + TYPE (infix trigger in suffix + type viability)  
**Soundness:** (design phase) Union of trigger-ahead and semantic-root checks.

**Status:** Under design (pgmcp #21 mandate: "work backwards from FV — model first, then code").

---

## 5. Resolution & Realization Gates

### 5.1 Premature-Accepted Filter (eoi_resolution_snapshot)
**Location:** `wpda_walker.rs:resolve_at_end_of_input`, `sppf_realize.rs`  
**When fires:** EOI: when checking which cursors have reached Accepted state  
**Evidence type:** STATE EVIDENCE (parser stack is in Accepted configuration)  
**Soundness:** Accepted state is defined by grammar; state machine is the arbiter.

**Mechanism:** At EOI, filter cursors to those where parse stack shows Accepted. Non-Accepted cursors are dead.

**Gap:** The 16-cursor ProcX root fan materializes pre-Accepted and dies at this filter. Category-viability evidence (from cross-cat FIRST) could kill them earlier (at dispatch, before cursor creation).

---

### 5.2 Prefix-Trailing Salvage (AcceptedWithTrailing)
**Location:** `wpda_walker.rs:resolve_at_end_of_input`, facade  
**When fires:** EOI: when parser accepts but input remains (trailing tokens)  
**Evidence type:** STATE EVIDENCE (furthest-accepting position < input.len())  
**Soundness:** Position tracking is exact.

**Mechanism:** Return partial parse at furthest acceptance point; caller's post-parse check surfaces `TrailingTokens` error.

**Current state:** Implemented; allows graceful partial-parse recovery.

---

### 5.3 Packing Satisfaction (packing_satisfies_min_terminal_span, semantic_hash dedup)
**Location:** `sppf_realize.rs`, `language.rs` (codegen semantic_hash)  
**When fires:** Realization: when expanding SPPF packings into AST terms  
**Evidence type:** DEFINITE (span check) + SEMANTIC (dedup by observable behavior)  
**Soundness:** Span is provable; semantic hash is based on `term_ops::semantic_hash` which respects observational equivalence (e.g., `-3!` Int vs Neg(Fact(3)) both `-3` but distinct ASTs preserved).

**Mechanism:** Filter packings by min_terminal_span, then dedup by semantic_hash before construction.

**Gap:** The -3! bug (Phase 2.2) was fixed by switching dedup from Display to semantic_hash. Evidence: Hash-dedup is sound; Display-dedup lost information.

---

### 5.4 Realization Budget (REALIZE_CAP, RAW_REALIZE_CAP)
**Location:** `facade.rs:parse_via_wpda_all`, codegen  
**When fires:** Realization: when term count exceeds cap (64 distinct, 4096 raw)  
**Evidence type:** REPORT (overflow signal)  
**Soundness:** Cap is checked AFTER realization; acts as a safety valve.

**Current state:** Report-only; if exceeded, returns `AmbiguityBudget` error.

---

### 5.5 Semantic Key Dedup (seen_terms HashMap)
**Location:** `facade.rs:realize_root_to_terms_with_weights`  
**When fires:** Realization: after each term is constructed  
**Evidence type:** SEMANTIC (observational equivalence)  
**Soundness:** semantic_key is based on semantic_hash, which preserves ambiguity while deduping Display-equivalent terms.

**Mechanism:** Build HashMap<semantic_key, term_idx>. If same key seen, update only if new weight is better (lex-min). Prevents duplicate observationally-equivalent terms from consuming the ambiguity budget.

**Current state:** Fully implemented (Phase 2.3).

---

## 6. Cycle Defenses & Progress Evidence

### 6.1 visited_dispatch Set (within-step-fanout cycle prevention)
**Location:** `wpda_walker.rs:apply_action_to_cursor`, `dispatch_cohort.rs`  
**When fires:** Every Fork dispatch: check if (cursor.pos, category) pair already in visited  
**Evidence type:** PROGRESS EVIDENCE (avoid revisiting same dispatch point)  
**Soundness:** If we've already tried category X at position P, re-trying is guaranteed to loop (same parse state, same input, same rules).

**Mechanism:** `visited_dispatch: im::OrdSet<(position, category_id)>` per cohort. Insert before spawning Fork; if already present, skip branch.

**Current state:** Fully implemented; prevents ~97% of no-op steps identified in #307 (342,699 steps saved by early exit).

---

### 6.2 visited_recovery Set (recovery cycle prevention)
**Location:** `wpda_walker.rs:apply_action_to_cursor`, `cursor_store.rs`  
**When fires:** Every recovery Fork: similar to visited_dispatch, but for recovery dispatch  
**Evidence type:** PROGRESS EVIDENCE (avoid re-attempting failed recovery path)  
**Soundness:** Same as visited_dispatch; recovery at the same position with the same repairs is guaranteed to loop.

**Mechanism:** `visited_recovery: im::OrdSet<...>` per cursor; checked before spawning recovery branch.

**Current state:** Fully implemented.

---

### 6.3 Max Recovery Depth (bounded_recovery constraint)
**Location:** `recovery.rs:RecoveryConfig`, `wpda_walker.rs:apply_action_to_cursor`  
**When fires:** Every recovery Fork: check if cursor.recovery_depth < max_recovery_depth  
**Evidence type:** BUDGET/PROGRESS (depth cap prevents exponential fanout)  
**Soundness:** Empirical: 8^3 = 512 branches with depth=3 completes in <500ms (test T6).

**Mechanism:** Increment `recovery_depth` on Fork; fail recovery if depth > 3 (default).

**Current state:** Fully implemented (L12, 2026-05-06); tests T1-T6 green.

---

### 6.4 Progress Detector (run_to_end_of_input)
**Location:** `wpda_walker.rs:run_to_end_of_input`, `wpda_session.rs`  
**When fires:** Step boundary: fingerprint cursor positions and weights; detect if stuck  
**Evidence type:** PROGRESS EVIDENCE (if frontier hasn't moved in K steps, input is stuck)  
**Soundness:** Frontier advancement is monotone; if position doesn't increase, no rule can succeed.

**Mechanism:** Compare `fingerprint = (max_position, sorted_weights)` across steps. If unchanged for threshold iterations, break loop and emit ParseError.

**Current state:** Implemented; fixed wallet live-lock issue (session 2026-05-18).

---

## 7. Budget & Bound Mechanisms (Report, Not Prune)

### 7.1 MAX_STEPS Budget
**Location:** `wpda_walker.rs:run_to_end_of_input(MAX_STEPS)`, facade  
**When fires:** Main parse loop: step counter reaches budget  
**Evidence type:** RESOURCE BOUND (not evidence-based pruning)  
**Soundness:** Overflow detection is sound; caller can extend budget and resume.

**Current state:** Fully implemented; allows resumable parsing.

---

### 7.2 AmbiguityBudget (cursor-count frontier cap)
**Location:** `wpda_runtime.rs:CursorBoundingMode::AmbiguityBudget`, walker  
**When fires:** Post-step-fanout: when frontier size exceeds limit  
**Evidence type:** RESOURCE BOUND (report, not prune)  
**Soundness:** Overflow is structural evidence (more ambiguity than budget allows); signal is for caller to react.

**Current state:** Fully implemented (M11.7); caller can relax budget or switch strategy.

---

### 7.3 BeamSize (legacy compatibility, now AmbiguityBudget)
**Location:** `wpda_runtime.rs:CursorBoundingMode::BeamSize`  
**When fires:** (deprecated) was per-step pruning; now equivalent to AmbiguityBudget  
**Evidence type:** RESOURCE BOUND  

**Current state:** Retained for compatibility; same semantics as AmbiguityBudget.

---

### 7.4 Recovery Skip Lookahead Limit (max_skip_lookahead)
**Location:** `recovery.rs:RecoveryConfig`  
**When fires:** Recovery: when simulating skip-ahead to find valid continuations  
**Evidence type:** RESOURCE BOUND (limit lookahead scan to 32 tokens)  
**Soundness:** Conservative (skip only if continuation found); doesn't prune evidence-based decisions.

**Current state:** Implemented with default 32 tokens.

---

### 7.5 Cascade Window (recovery)
**Location:** `recovery.rs:RecoveryConfig`  
**When fires:** Recovery: when multiple repairs are queued  
**Evidence type:** RESOURCE BOUND (limit cascade length to 3 repairs)  
**Soundness:** Prevents unbounded repair chains; still allows most needed repairs.

**Current state:** Implemented with default 3.

---

## 8. Eval-Side Evidence: Semantic Hash & Rewrites

### 8.1 Semantic Hash Dedup (term_ops::semantic_hash)
**Location:** `language.rs` (codegen), `facade.rs` (realization)  
**When fires:** Realization: when deduping realized terms before eval  
**Evidence type:** SEMANTIC (observable equivalence)  
**Soundness:** semantic_hash is based on canonical form; two terms with same hash have identical behavior under any context.

**Mechanism:** Hash each realized term; keep only the lex-min representative per hash value.

**Current state:** Fully implemented (Phase 2.3 fixes -3! loss via Display dedup).

---

### 8.2 Guard Dispatch & Rewrite-to-Err
**Location:** `runtime/src/behavioral_pred.rs`, runtime rewrite logic  
**When fires:** Eval: when applying guarded rewrite rules  
**Evidence type:** DEFINITE (guard succeeds or fails by computation)  
**Soundness:** Guard semantics are defined by the language spec.

**Mechanism:** Before applying rewrite, check guard condition. If false, skip rewrite (alternative path may apply it).

**Current state:** Fully implemented.

---

### 8.3 Pattern-Match Failure (no matching case)
**Location:** Runtime eval  
**When fires:** Term matching: when no pattern matches  
**Evidence type:** DEFINITE (term structure doesn't match any pattern)  
**Soundness:** Structural mismatch is exact.

**Mechanism:** If no case matches, evaluation terminates (error or default behavior, language-specific).

**Current state:** Language-specific implementation.

---

## 9. Lexer-Side Mechanisms: DAG, Soft-Fail, Weights

### 9.1 Lex DAG Soft-Fail (M6c.7.1)
**Location:** `lex_dag_core` (M6c.7.1), `lexer_types.rs`  
**When fires:** Lexer: when DFA fails at a secondary-alt position  
**Evidence type:** DEFINITE (lex dead-end for this alt)  
**Soundness:** If lex cannot produce a token, no parser rule can consume it; dead by structure.

**Mechanism:** Track primary-chain positions (reachable via longest-munch accept). If DFA fails at non-primary, allocate orphan node (empty edges). Walker sees Eof, cannot dispatch, cursor dies.

**Current state:** Fully implemented (M6c.7.1); sound and tested.

---

### 9.2 Orphan Node Allocation (dead-end secondary alts)
**Location:** `lex_dag_core`  
**When fires:** Lexer: orphan allocation for failed secondary alt  
**Evidence type:** DEFINITE (no valid downstream tokens)  
**Soundness:** Orphan is safe; walker's lex-Fork branches to it, sees Eof, fails to dispatch naturally.

**Current state:** Fully implemented.

---

### 9.3 Lexer DAG Edge Weights (lex_min ordering)
**Location:** `lexer.rs`, `lex_weight.rs` (rigail)  
**When fires:** Lexer DAG construction: assign weight to each alt edge  
**Evidence type:** ORDERING SIGNAL (preference order for lexical ambiguity)  
**Soundness:** Weights are grammar-baked (via codegen); Viterbi extraction is sound.

**Mechanism:** Emit edge weights during DAG construction; Viterbi selects lex-min path.

**Current state:** Fully implemented.

---

### 9.4 Prefix Dispatch Lex-Fork (emit_lex_fork_at_prefix_dispatch)
**Location:** `forks.rs` (codegen)  
**When fires:** Prefix dispatch: when input is ambiguous at current position  
**Evidence type:** STRUCTURAL (lexical ambiguity exists)  
**Soundness:** If lex DAG has >1 edges at a position, Fork is needed; alternatives are preserved.

**Mechanism:** Inspect `tokens.is_ambiguous_at(pos)`. If true, emit Fork with one branch per alt.

**Current state:** Fully implemented; correctly surfaces lexical alternatives to parser.

---

### 9.5 Infix Loop Lex-Fork (emit_lex_fork_at_infix_loop)
**Location:** `forks.rs` (codegen)  
**When fires:** Infix loop: when operand-position tokenization is ambiguous  
**Evidence type:** STRUCTURAL (lexical ambiguity exists)  
**Soundness:** Same as prefix lex-fork.

**Mechanism:** Similar to prefix; check ambiguity and emit Fork if needed.

**Current state:** Fully implemented.

---

### 9.6 Keyword Reservation (lex-fork keyword interpretation)
**Location:** `forks.rs:prefix_primary_has_dispatch_rule` (2026-06-10 fix, commit 51d57c91)  
**When fires:** Prefix dispatch: lex-fork branch gate  
**Evidence type:** DEFINITE (grammar rule exists for this token kind)  
**Soundness:** Codegen bakes which rules consume which token kinds; evidence is compile-time.

**Mechanism:** `prefix_primary_has_dispatch_rule(cat_src_idx, kind)` checks if any rule in category consumes this kind. If false, skip branch.

**Current state:** Fixed 2026-06-10; wired into __fall_through with SAME-LENGTH guard; fixed 189/217 op-suite fails.

---

## 10. Formal Verification Layer

### 10.1 Zero-Admission Proofs (decision_tree.rs subsumption)
**Location:** `formal/rocq/prattail_wpda_runtime/theories/`, `LexForkKeywordReservation.v`, etc.  
**When fires:** (Compile-time proof verification)  
**Evidence type:** FORMAL PROOF (mathematical certainty)  
**Soundness:** Rocq formal verification with `Print Assumptions` confirms zero admitted lemmas.

**Current state:** 5+ zero-admission proofs (decision tree foundations, lexfork keyword reservation, cast-compare evidence, etc.); pgmcp #294 tracking.

---

### 10.2 Runtime Model Theorems (RuntimeModel.v)
**Location:** `formal/rocq/.../RuntimeModel.v`  
**When fires:** (Specification layer)  
**Evidence type:** FORMAL SPECIFICATION (semantics of budget overflow, lazy frontier, etc.)  
**Soundness:** Coq-verified; theorems link runtime behavior to formal semantics.

**Current state:** Fully formalized (cursor bounds, lazy frontier, budget soundness).

---

### 10.3 Bounded Recovery Proofs
**Location:** Formal theories  
**When fires:** (Specification layer)  
**Evidence type:** FORMAL SPECIFICATION (recovery depth bounds)  
**Soundness:** Coq-verified.

**Current state:** In progress (pgmcp #294).

---

## 11. Summary Table: Evidence by Pipeline Stage

| Stage | Mechanism | Evidence Type | Fires | Early-Opportunity |
|-------|-----------|---|---|---|
| **Lex** | soft-fail orphan | DEFINITE (lex dead-end) | lex_dag_core | ✓ Sound |
| **Lex** | DAG weight ordering | ORDER (lex-min) | DAG construction | Viterbi unused |
| **Lex-Fork** | keyword reservation | DEFINITE (rule exists) | prefix_dispatch | Fixed 2026-06-10 |
| **Lex-Fork** | infix lex-fork | STRUCTURAL (ambiguity) | infix_loop | ✓ Implemented |
| **Dispatch** | decision tree trie | DEFINITE (LL(k)) | token matched | ✓ Early |
| **Dispatch** | nonterminal boundary | DEFINITE (FIRST-set) | trie node | ✓ Early |
| **Dispatch** | cross-cat trigger-ahead | LOOKAHEAD (suffix scan) | dispatch_token | **LATE** (after cast parse) |
| **Dispatch** | visited_dispatch | PROGRESS | fork_dispatch | ✓ Early (saves 342K steps) |
| **Dispatch** | ContextWeight H1 | ORDER (multi-axis) | cohort_construction | Gated off, weak ROI |
| **Infix** | binding power | ORDER (l_bp, r_bp) | infix_loop | ✓ Early |
| **Infix** | guard category infix | DEFINITE (type mismatch) | dispatch | ✓ Implemented |
| **Infix** | into_term rejection | DEFINITE (type) | realize | **LATE** (post-parse) |
| **EOI** | is_logical_eoi | DEFINITE (EOF sentinel) | step_boundary | ✓ Early |
| **EOI** | premature-Accepted | STATE (stack status) | resolve | **LATE** (16-cursor waste) |
| **EOI** | trailing tokens | EVIDENCE (pos check) | resolve | ✓ Implemented |
| **Realize** | min_terminal_span | DEFINITE (span check) | packing filter | ✓ Implemented |
| **Realize** | semantic_root_accepts | DEFINITE (cast exists) | cross-cat realize | **LATE** (post-parse) |
| **Realize** | semantic_hash dedup | SEMANTIC (obs. equiv) | term_hash | ✓ Implemented |
| **Realize** | packing cap | REPORT (overflow) | realization loop | ✓ Report gate |
| **Recover** | visited_recovery | PROGRESS | recovery_fork | ✓ Early |
| **Recover** | max_recovery_depth | BUDGET | fork_depth_check | ✓ Implemented |
| **Recover** | skip_lookahead | RESOURCE | skip_simulation | ✓ Implemented |
| **Eval** | guard check | DEFINITE (computation) | rewrite_apply | ✓ Language-specific |
| **Eval** | semantic_hash (again) | SEMANTIC | term_match | ✓ Implemented |

---

## 12. Gap Analysis: Evidence Available But Fires Too Late

### Gap #1: Category Viability @ ProcX Root Fan
**Symptom:** 16-cursor frontier at ProcX root; all die at premature-Accepted filter (EOI).  
**Root cause:** Category-FIRST dispatch happens during normal prefix dispatch, but cross-cat viability is checked post-parse (semantic_root_accepts).  
**Evidence available:** WFST prediction (valid_continuations) + category FIRST sets — available at parse time.  
**Fix approach:** Wire category-viability lookahead gate at dispatch (after each prefix rule, check if any infix can attach in downstream categories).  
**Impact:** Could eliminate 16-cursor materialization before cursor stores are allocated.

---

### Gap #2: Cast-then-Infix 342,699 No-Op Steps
**Symptom:** Infix loop exhausts cursor budget trying to attach infix after cast results; all fail because cast wraps value in wrong category.  
**Root cause:** Infix dispatch doesn't know cast result's category type; tries all infixes in source category.  
**Evidence available:** Cast's target type is known at rule codegen time; can be baked into action metadata.  
**Fix approach:** At cast-result position, inject type-aware dispatch state (e.g., switch to wrapper category) so infix loop knows where the result actually is.  
**Impact:** Eliminate ~342K no-op steps (per #307 findings).  
**Formal validation:** Phase 5A CastDelegateMergeBound.v (629e9759) and evidence-driven-early-pruning.md design.

---

### Gap #3: Cohort Materialization Without Evidence Gate
**Symptom:** Cohorts materialize before ContextWeight can prune them; H1 showed 97.5% multi-discriminator divergence but gate was never wired.  
**Root cause:** Cohort construction is eager (before Fork); ContextWeight is computed but not used.  
**Evidence available:** ContextWeight multi-axis divergence metric — computed during cohort construction.  
**Fix approach:** Lazily materialize cohort members only if ContextWeight evidence shows they're needed (all axes diverge).  
**Impact:** Potential ~0.6% cursor savings (per chain_50 diagnostic); low ROI compared to cast-delegate fix.

---

### Gap #4: Prefix-Trailing Evidence Unavailable at Parse Time
**Symptom:** TrailingTokens error only surfaced post-realization, after calling `resolve_at_end_of_input`.  
**Root cause:** EOI check happens at walker step level; realization scope is decided after parse completes.  
**Evidence available:** Input length is known; furthest-acceptance position is tracked.  
**Fix approach:** During resolve, check if `furthest_position < input.len()` BEFORE realization attempt; if true, short-circuit to AcceptedWithTrailing without full realization.  
**Impact:** Modest (mostly optimization; error message is identical); enables prefix-partial-parse optimization.

---

### Gap #5: Lex-Fork Keyword Interpretation (FIXED 2026-06-10)
**Symptom:** 189/217 op-suite fails due to dropped keyword rules in multi-token-prefix lex-fork.  
**Root cause:** `lex_alt_rules_for_prefix` codegen couldn't represent multi-token-prefix keyword rules; only forked Ident→Var (single-token).  
**Evidence available:** `prefix_primary_has_dispatch_rule` function existed but was never called in __fall_through.  
**Fix approach:** Wire the guard into __fall_through with SAME-LENGTH guard (51d57c91).  
**Impact:** Fixed 189/217 tests (prattail 3979/0, zero regressions).  
**Status:** FIXED.

---

## 13. Mechanism Classification by Soundness & Timing

| Classification | Mechanisms | Example | Action |
|---|---|---|---|
| **Definite + Early** | FIRST/FOLLOW trie, visited_dispatch, lex soft-fail, keyword-reservation | dispatch determinism, progress | Core infrastructure ✓ |
| **Definite + Late** | min_terminal_span, semantic_root_accepts, into_term rejection | cast type check | GAP — move earlier |
| **Order + Early** | BP tiers, lex-min extraction | infix loop, Viterbi | Working as designed ✓ |
| **Order + Late** | ContextWeight H1, Viterbi beam (if wired) | cohort divergence | Low ROI / disabled |
| **Report + Safety** | AmbiguityBudget, MAX_STEPS, REALIZE_CAP | overflow gates | Working as designed ✓ |
| **Heuristic** | (None) | — | Avoided per mandate |

---

## 14. Conclusion: Evidence-Driven Foundation

The PraTTaIL/MeTTaIL WPDA parser has a **rich, mathematically-principled evidence foundation** across 48+ mechanisms. The parser's mandate — "alternatives leave only via definite evidence" — is largely honored:

- **Early-firing definite evidence:** PathMap trie, FIRST/FOLLOW, visited_dispatch, lex soft-fail. These are the load-bearing mechanisms and are sound.
- **Late-firing definite evidence:** semantic_root_accepts, into_term rejection, cast type dispatch. These fire post-parse and represent the primary gap targets.
- **Order-based signals:** LexicographicWeight, BP tiers, lex-min extraction. These ORDER alternatives, never prune, and are semiring-sound.
- **Report gates (not pruning):** AmbiguityBudget, MAX_STEPS, REALIZE_CAP. These signal overflow for caller reaction; preserve ambiguity.

**Next step (pgmcp #21):** Model evidence-gated delegate dispatch (lookahead-gate infix-attachment checks on cast result types) → implement cohort-shared+lookahead-gated cross-cat delegate dispatch → formal verification (zero-admission proofs of soundness).

---

## Appendix A: File Locations (Core Evidence Mechanisms)

| Mechanism | Primary Location | Codegen | Formal |
|---|---|---|---|
| PathMap decision tree | `prattail/src/decision_tree.rs` | `macros/src/gen/runtime/wpda_codegen/*.rs` | `formal/rocq/.../LexForkKeywordReservation.v` |
| LexicographicWeight | `rigail/src/lex_weight.rs` | `transducer.rs` | — |
| visited_dispatch | `prattail/src/wpda_walker.rs` | — | — |
| visited_recovery | `prattail/src/cursor_store.rs` | — | — |
| Lex DAG soft-fail | `prattail/src/lexer_types.rs` + `runtime_types.rs` | — | — |
| Cross-cat dispatch | `prattail/src/dispatch_cohort.rs` | `macros/src/gen/runtime/wpda_codegen/forks.rs` | Phase 5A design doc |
| Realization gates | `prattail/src/sppf_realize.rs` | `macros/src/gen/runtime/wpda_codegen/facade.rs` | — |
| Recovery bounds | `prattail/src/recovery.rs` | — | — |
| CursorBoundingMode | `prattail/src/wpda_runtime.rs` | — | `formal/rocq/.../RuntimeModel.v` |

