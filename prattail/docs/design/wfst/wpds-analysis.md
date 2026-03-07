# Weighted Pushdown System (WPDS) Analysis Layer

**Date:** 2026-03-07 (Layer Expansion; originally 2026-03-04)

## 1. Overview

PraTTaIL's trampoline parser **is** a pushdown automaton: it maintains an explicit
`Vec<Frame_Cat>` stack, uses `(category, min_bp)` as states, and consumes tokens as
input. The existing `PredictionWfst` provides finite-state analysis at compile time but
cannot reason about stack context. The WPDS layer adds **pushdown-aware** compile-time
analysis — it can determine whether a grammar rule is reachable only in stack
configurations that actually occur during parsing.

The WPDS layer comprises two logical parts:

1. **Core WPDS** (Phases 1–4): Grammar-to-WPDS construction, poststar/prestar
   saturation, stringsum analysis, and initial pipeline integration.
2. **Layer Expansion** (8 sprints): Call graph analysis (G33), recursion depth bounds
   (G34), cycle classification (G35), calling context analysis (G36), context-sensitive
   rule tables (CS-01), cross-category BP modulation (CS-04), context-aware ambiguity
   resolution (CS-05), and 6 pipeline integrations (INT-01/02/03, COMP-07/08, RT-01).

```
LanguageSpec ──→ build_wpds() ──→ Wpds<W>
                                     │
                ┌────────────────────┼────────────────────────────┐
                │                    │                            │
                ▼                    ▼                            ▼
         poststar(Boolean)   stringsum(Counting)       extract_call_graph() [G33]
         → reachability      → ambiguity counts         │
                │                    │                   ├─ compute_depth_bounds() [G34]
                │                    │                   ├─ classify_cycles() [G35]
                │                    │                   ├─ compute_calling_contexts() [G36]
                │                    │                   │
                │                    │                   ├─ build_context_rule_tables() [CS-01]
                │                    │                   ├─ analyze_cross_category_bp() [CS-04]
                │                    │                   └─ analyze_context_ambiguity() [CS-05]
                │                    │
                ▼                    ▼
         lint.rs (Tier 5)     cost_benefit.rs
         W13, D14, D15,      (A5 refinement)
         P05, W14, W16,
         COMP-08
                │
                ├─ INT-01: weight refinement
                ├─ COMP-07: trie confirmation
                ├─ INT-02: dead-rule recording
                ├─ INT-03: NFA spillover reduction
                └─ RT-01: frame pool sizing
```

**Implementation:** ~3,150 lines in `wpds.rs`, ~450 lines in `lint.rs`, ~200 lines in
`pipeline.rs`, plus trampoline/decision-tree integrations. 43 unit tests.

---

## 2. Theoretical Foundations

Three complementary formalisms underpin the implementation:

1. **Reps, Lal & Kidd (2007)** — Weighted Pushdown Systems for interprocedural
   analysis. poststar/prestar saturation produces weighted P-automata encoding all
   reachable configurations with call/return matching. This is the primary algorithm.

2. **Droste, Dziadek & Kuich (2019)** — Simple reset WPDA normal form. Three stack ops
   (push/pop/noop), no ε-transitions. Canonical algebraic system:

       X = M₀X + Σₜ M₁ₜ X M₂ₜ X + E

   mapping directly onto Pratt's infix continuation / nested subexpression / atom.

3. **Butoi et al. (2022)** — Direct WPDA stringsum algorithm. O(n³|Q|³|Γ|³)
   per input. Avoids CFG conversion, provides |Q|×|Γ| speedup over Lang (1974).

---

## 3. Grammar-to-WPDS Mapping

PraTTaIL's inter-category dispatch is interprocedural control flow:

| Program Analysis Concept | PraTTaIL Equivalent |
|---|---|
| Procedure | Grammar category (Expr, Type, Pattern, ...) |
| Call site | Cross-category reference (Expr rule invoking Type) |
| Return site | Continuation after cross-category parse completes |
| Call stack | Trampoline frame stack (`Vec<Frame_Cat>`) |
| ICFG edge | Dispatch transition (infix/prefix/RD handler) |
| Valid path | Parse path with matched category entry/exit |
| MOVP | Weight of all valid parses respecting call/return matching |

### PDS Encoding

The WPDS uses a **context-free process** encoding (single control location `p`):

- **Control locations P** = `{p}`
- **Stack alphabet Γ** = `StackSymbol(category, rule_label, position)` triples
- **Rules Δ**:
  - **Replace** (intraprocedural): `⟨p, (Cat, rule, pos)⟩ ↪ ⟨p, (Cat, rule, pos+1)⟩`
    — consuming a terminal advances position within a rule
  - **Push** (cross-category call): `⟨p, (Cat, rule, pos)⟩ ↪ ⟨p, (Callee, "", 0)(Cat, rule, pos+1)⟩`
    — enter callee category, push return address
  - **Pop** (return): `⟨p, (Cat, rule, last)⟩ ↪ ⟨p, ε⟩`
    — rule complete, pop frame

### Weight Assignment

Weights come from the `PredictionWfst`:
- If a WFST transition exists from `Cat` on `rule_label`, use its tropical weight
- Otherwise, default weight `W::one()` (unit cost)
- Cross-category Push rules carry weight `W::one()` (call cost is uniform)

---

## 4. Core Algorithms

### 4.1 poststar — Forward Reachability Saturation

The core algorithm for grammar-wide analysis. Given an initial P-automaton encoding the
start configuration `⟨p, γ₀⟩`, poststar saturates it to encode ALL reachable
configurations:

```
Input:  A₀ = P-automaton for {⟨p, [⟨StartCat⟩]⟩}
Output: A_post* encoding all configs reachable from A₀

Algorithm:
  worklist := initial transition set
  while worklist not empty:
    pick (q, γ, q') from worklist
    for each WPDS rule r matching γ:
      case Pop:    no new transition (config accepted)
      case Replace(γ'):
        add (p, γ', q') with weight f(r) ⊗ w(q,γ,q')
      case Push(γ₁, γ₂):
        add fresh state q_r
        add (p, γ₁, q_r)  with weight f(r)
        add (q_r, γ₂, q') with weight w
```

**Complexity:** O_s(|P|·|Δ|·(|Q₀|+|Δ|)·H) where H = weight domain height.

**Reachability semantics:** A stack symbol γ is reachable if it appears on ANY
transition `(q, γ, q')` where q is the initial state — not necessarily where q' is
an accepting state. This is critical for cross-category symbols that appear mid-stack.

### 4.2 prestar — Backward Reachability Saturation

Dual of poststar: computes all configurations from which a target set is reachable.
Currently implemented but not directly used in the pipeline.

### 4.3 stringsum — Per-Input Analysis

Given a specific input token sequence, computes the total weight of all accepting runs:

    stringsum(input) = ⨁_{ρ ∈ Acc(input)} weight(ρ)

Over the counting semiring, this gives the exact number of parse trees (ambiguity).
Over the tropical semiring, it gives the minimum-cost parse.

---

## 5. Call Graph Analysis (G33)

### Purpose

Extract the inter-category call structure from WPDS Push rules as a directed, weighted
graph. This enables recursion detection, fan-in/fan-out measurement, and witness trace
generation for dead-rule diagnostics.

### Data Structures

```rust
pub struct CallEdge {
    pub caller_cat: String,     // Category initiating the call
    pub callee_cat: String,     // Category being called
    pub call_sites: usize,      // Number of distinct Push rules
    pub total_weight: f64,      // Aggregated weight across call sites
}

pub struct WpdsCallGraph {
    pub edges: Vec<CallEdge>,
    pub fan_out: HashMap<String, usize>,  // Distinct callees per category
    pub fan_in: HashMap<String, usize>,   // Distinct callers per category
    pub sccs: Vec<Vec<String>>,           // Tarjan SCC decomposition
    pub categories: HashSet<String>,      // All categories in graph
}
```

### Algorithm: `extract_call_graph()`

1. **Linear scan** of all WPDS rules, filtering for `Push` variants
2. **Aggregate** `(caller, callee)` pairs into `CallEdge`s with multiplicity
3. **Compute** fan-in/fan-out from edge set
4. **Tarjan SCC** decomposition for recursion identification

```
extract_call_graph(wpds):
  edge_map := {}
  for rule in wpds.rules:
    if rule is Push:
      caller := rule.from_gamma.category
      callee := rule.to_gamma_top.category
      if caller ≠ callee:
        edge_map[(caller, callee)] += 1
  sccs := tarjan_scc(categories, edges)
  return WpdsCallGraph { edges, fan_in, fan_out, sccs, categories }
```

**Complexity:** O(|Δ| + |V| + |E|) where |V| = categories, |E| = edges.

### Worked Example

Grammar with mutual recursion: `Expr → "x" | Decl "in" Expr; Decl → "let" Expr`

```
Call Graph:
  Expr ──→ Decl (1 call site: LetIn rule, pos=0)
  Decl ──→ Expr (1 call site: LetDecl rule, pos=1)

SCCs: [{Expr, Decl}]  (mutual recursion)
Fan-out: Expr=1, Decl=1
Fan-in:  Expr=1, Decl=1
```

### Witness Traces: `shortest_path_witness()`

For D15 dead-rule diagnostics, BFS backward from the dead category on the reverse call
graph to find the shortest hypothetical Push chain from a reachable category:

```
shortest_path_witness(call_graph, reachable, target_cat):
  reverse_adj := build reverse adjacency from call_graph.edges
  BFS backward from target_cat:
    if current ∈ reachable: reconstruct path, return
  return ["no path from any reachable category"]
```

---

## 6. Recursion Depth Bounds (G34)

### Purpose

Determine per-category minimum nesting depth and whether max depth is bounded.
Used by RT-01 for frame pool pre-sizing.

### Data Structure

```rust
pub struct DepthBounds {
    pub min_depth: u32,          // 0 = top-level (primary category)
    pub max_depth: Option<u32>,  // None = unbounded (recursive)
    pub is_recursive: bool,      // SCC member or self-loop
}
```

### Algorithm: `compute_depth_bounds()`

```
compute_depth_bounds(call_graph, primary_cat):
  // BFS from primary to compute min_depth
  visited := { primary_cat → 0 }
  queue := [(primary_cat, 0)]
  while queue not empty:
    (cat, depth) := dequeue
    for callee in adj[cat]:
      if callee ∉ visited:
        visited[callee] := depth + 1
        enqueue (callee, depth + 1)

  // Classify recursive categories
  recursive_cats := { cat | cat ∈ SCC with |SCC|>1 or self-loop }

  // Assign bounds
  for cat in all_categories:
    min_depth := visited[cat] or u32::MAX
    is_recursive := cat ∈ recursive_cats
    max_depth := if is_recursive or unreachable then None else Some(min_depth)
    result[cat] := DepthBounds { min_depth, max_depth, is_recursive }
```

### RT-01 Integration

The maximum bounded depth feeds into `TrampolineConfig.frame_pool_capacity`:

    frame_pool_capacity = max(depth_bounds[cat].max_depth for cat in bounded) + 1

This enables `Vec::with_capacity(N)` instead of `Vec::new()` for the trampoline frame
pool TLS, eliminating reallocations for grammars with known nesting limits.

---

## 7. Cycle Classification (G35)

### Purpose

Classify call graph cycles as Direct (self-loop) or Mutual (multi-category), and detect
left-recursion within cycles.

### Data Structures

```rust
pub enum CycleKind {
    Direct,   // |SCC| = 1 with self-edge
    Mutual,   // |SCC| > 1
}

pub struct CycleInfo {
    pub categories: Vec<String>,
    pub kind: CycleKind,
    pub is_left_recursive: bool,
}
```

### Algorithm: `classify_cycles()`

```
classify_cycles(call_graph, wpds):
  cycles := []
  for scc in call_graph.sccs:
    if |scc| > 1:
      is_lr := any(has_left_recursion(cat, wpds) for cat in scc)
      cycles.push(CycleInfo { scc, Mutual, is_lr })
    elif |scc| = 1 and has_self_edge(scc[0]):
      is_lr := has_left_recursion(scc[0], wpds)
      cycles.push(CycleInfo { scc, Direct, is_lr })
  return cycles
```

### Left-Recursion Detection: `has_left_recursion()`

A category is left-recursive if a Replace-only path exists from a rule's position-0
back to the category entry without consuming input:

```
has_left_recursion(category, wpds):
  entry := StackSymbol::category_entry(category)
  for Replace rule from entry to (category, rule, 0):
    if has_replace_path_to_entry(wpds, (category, rule, 0), entry):
      return true
  return false

has_replace_path_to_entry(wpds, start, target):
  BFS from start following only Replace rules:
    if current == target: return true
  return false
```

---

## 8. Calling Context Analysis (G36)

### Purpose

Determine "who calls each category" by scanning WPDS Push rules. Each calling context
records the caller category, rule label, position, and weight.

### Data Structure

```rust
pub struct CallingContext {
    pub caller_category: String,
    pub caller_rule: String,
    pub caller_position: u32,
    pub weight: f64,
}
```

### Algorithm: `compute_calling_contexts()`

```
compute_calling_contexts(wpds):
  contexts := {}
  for rule in wpds.rules:
    if rule is Push:
      callee := rule.to_gamma_top.category
      contexts[callee].push(CallingContext {
        caller_category: rule.from_gamma.category,
        caller_rule: rule.from_gamma.rule_label,
        caller_position: rule.from_gamma.position,
        weight: if rule.weight.is_zero() then 0.0 else 1.0
      })
  return contexts
```

---

## 9. Context-Sensitive Rule Tables (CS-01)

### Purpose

Build per-category tables mapping calling contexts to valid rule sets. When different
contexts yield different rule sets, context-sensitive dispatch can eliminate unnecessary
rule attempts.

### Data Structures

```rust
pub struct ContextEntry {
    pub context_tag: String,       // Caller category name or "top-level"
    pub valid_rules: Vec<String>,  // Rule labels valid in this context
}

pub struct ContextRuleTable {
    pub category: String,
    pub entries: Vec<ContextEntry>,
    pub is_nontrivial: bool,       // At least one context has reduced rules
    pub singleton_contexts: usize, // Contexts with exactly 1 valid rule
}
```

### Algorithm: `build_context_rule_tables()`

For each category with calling contexts:
1. Group calling contexts by caller category
2. For each unique caller, determine which rules are reachable
3. Add a "top-level" entry for the primary category (called directly)
4. Mark table as nontrivial if any context has a reduced rule set
5. Count singleton contexts (direct dispatch without try-all)

---

## 10. Cross-Category BP Modulation (CS-04)

### Purpose

Record per-call-site binding power hints from WPDS Push rules. Position 0 calls are
prefix contexts (BP typically 0), while position > 0 calls may be infix contexts
(BP > 0). When different callers use different BP values, CS-04 can thread
caller-specific BP through cross-category dispatch.

### Algorithm: `analyze_cross_category_bp()`

```
analyze_cross_category_bp(wpds):
  bp_map := {}
  for Push rule in wpds.rules:
    caller := rule.from_gamma.category
    callee := rule.to_gamma_top.category
    bp_hint := if rule.from_gamma.position == 0 then 0 else 1
    bp_map[(caller, callee)].push(bp_hint)
  deduplicate and sort each bp_map entry
  return bp_map
```

---

## 11. Context-Aware Ambiguity Resolution (CS-05)

### Purpose

A category is "context-unambiguous" if it has at most one unique calling context.
For such categories, NFA try-all can commit to the first success (skip save/restore).

### Algorithm: `analyze_context_ambiguity()`

```
analyze_context_ambiguity(calling_contexts, reachable_categories):
  result := {}
  for cat in reachable_categories:
    unique_callers := |{ ctx.caller_category for ctx in calling_contexts[cat] }|
    result[cat] := (unique_callers ≤ 1)
  return result
```

---

## 12. Pipeline Integrations

### INT-01: WPDS PredictionWfst Weight Refinement

For rules with equal WFST weights sharing a dispatch token, use WPDS poststar weights
as tiebreaker. Lower WPDS weight → lower WFST weight (0.001 offset per rank).

### COMP-07: WPDS × Trie Dead-Rule Confirmation

Cross-reference WPDS-unreachable rules with decision tree presence. Rules present in
the PathMap trie but WPDS-unreachable are "phantom entries" — confirmed dead across
both analysis layers.

### INT-02: Dead-Rule Recording for Codegen

Record WPDS-dead rules in a `HashSet<String>` for downstream codegen suppression.
Ambiguous candidates that are WPDS-unreachable can be skipped during code generation.

### INT-03: NFA Spillover Reduction

Remove WPDS-unreachable rules from NFA spillover groups. If a category's spillover
is eliminated (all ambiguous groups become singletons), remove it from
`nfa_spillover_categories`.

### RT-01: Frame Pool Pre-Sizing

Use G34 depth bounds to set `TrampolineConfig.frame_pool_capacity`:

```rust
pub frame_pool_capacity: Option<usize>,
// When Some(n), TLS pool uses Vec::with_capacity(n) instead of Vec::new()
```

### Pipeline Sequence

```
  generate_parser_code()
  ╷
  ├─ Steps 5a–5g (existing WFST pipeline)
  │
  ├─ 5h. build_wpds() + poststar() + analyze_wpds()    [wpds.rs]
  │       P05: wall-clock timing
  │
  ├─ 5i. INT-01: wpds_refine_prediction_weights()       [pipeline.rs]
  │       Tiebreak equal-weight rules via WPDS rank
  │
  ├─ 5j. COMP-07: wpds_confirm_trie_dead_rules()        [pipeline.rs]
  │       Cross-reference WPDS-unreachable with PathMap trie
  │
  ├─ 5k. INT-02: dead-rule recording for codegen        [pipeline.rs]
  │       HashSet<String> of WPDS-dead rule labels
  │
  ├─ 5l. INT-03: NFA spillover reduction                [pipeline.rs]
  │       Remove WPDS-dead rules from spillover groups
  │
  ├─ Lint layer (includes W13, D14, D15, P05, W14, W16, COMP-08)
  ╵
```

---

## 13. Expanded Lint Diagnostics

The WPDS layer expansion introduces 6 new diagnostics:

| ID | Name | Severity | Source |
|---|---|---|---|
| W13 | wpds-unreachable | Warning | Stack-aware dead-rule detection via poststar |
| D14 | wpds-complexity-report | Info | |Γ|, |Δ|, SCCs, call edges, depth bounds |
| D15 | wpds-witness-trace | Info | BFS shortest path on G33 call graph (sub-diagnostic of W13) |
| P05 | wpds-pipeline-cost | Info | Wall-clock timing and analysis sizes |
| W14 | wpds-confirmed-ambiguity | Warning/Note | WPDS confirms/denies pushdown ambiguity |
| W16 | wpds-weight-inversion | Warning | WFST vs WPDS weight order disagreement |
| COMP-08 | wpds-refactoring-suggestion | Note | Hub splitting, inlining, cycle-breaking |

See the [per-lint documentation](../../diagnostics/) for trigger conditions, examples,
and resolution strategies.

---

## 14. WpdsAnalysis Struct

The `WpdsAnalysis` struct aggregates all WPDS analysis results for consumption by
downstream pipeline stages and lints:

```rust
pub struct WpdsAnalysis {
    // ── Core (Phase 1–4) ──
    pub grammar_name: String,
    pub num_symbols: usize,               // |Γ| — stack alphabet size
    pub num_rules: usize,                 // |Δ| — PDS rule count
    pub reachable_categories: HashSet<String>,
    pub unreachable_rules: Vec<WpdsUnreachableRule>,
    pub category_weights: HashMap<String, f64>,  // TropicalWeight per category

    // ── G33: Call Graph ──
    pub call_graph: WpdsCallGraph,

    // ── G34: Depth Bounds ──
    pub depth_bounds: HashMap<String, DepthBounds>,

    // ── G35: Cycles ──
    pub cycles: Vec<CycleInfo>,

    // ── G36: Calling Contexts ──
    pub calling_contexts: HashMap<String, Vec<CallingContext>>,

    // ── CS-01: Context Rule Tables ──
    pub context_rule_tables: HashMap<String, ContextRuleTable>,

    // ── CS-04: Cross-Category BP ──
    pub cross_category_bp: HashMap<(String, String), Vec<u8>>,

    // ── CS-05: Context Ambiguity ──
    pub context_unambiguous: HashMap<String, bool>,
}
```

---

## 15. Pipeline Integration (Gate)

### G25 WpdsReachabilityCheck (cost_benefit.rs)

Optimization gate controlling WPDS analysis:
- **Speedup:** 0.4 (moderate — improves dead-rule precision)
- **Cost:** 0.3 (moderate — WPDS construction + saturation)
- **Applicable:** When `category_count >= 2` (cross-category calls exist)
- **Type:** Diagnostic (not Auto — opt-in)

---

## 16. What WPDS Does NOT Do

- **Runtime parsing** — Pratt is O(n), WPDA stringsum is O(n³). The WPDS layer is
  strictly compile-time.
- **Replace the WFST** — The PredictionWfst remains the primary dispatch ordering
  mechanism. WPDS augments it with pushdown-aware analysis.
- **Lexing** — The lexer is purely regular (NFA → DFA → minimized DFA). No pushdown
  power needed.
- **Real-time dispatch** — WPDS results are precomputed, not evaluated on the hot path.

---

## 17. Semiring Compatibility

| Semiring | Butoi/Droste | Reps (idempotent) | Use Case |
|---|---|---|---|
| TropicalWeight | Yes | Yes | Shortest-path dispatch |
| BooleanWeight | Yes | Yes | Reachability |
| CountingWeight | Yes | Safe approx | Ambiguity counting |
| LogWeight | Yes | Safe approx | EM training, entropy |
| EditWeight | Yes | Yes | Error recovery costs |
| ProductWeight | Yes | (components) | Compound analyses |
| ArcticWeight | Yes | Yes | Critical-path |
| FuzzyWeight | Yes | Yes | Soft constraints |

---

## 18. Files

| File | Role |
|---|---|
| `prattail/src/wpds.rs` | Core implementation (~3,150 lines + 43 tests) |
| `prattail/src/cost_benefit.rs` | G25 optimization gate |
| `prattail/src/lint.rs` | W13, D14, D15, P05, W14, W16, COMP-08 lint diagnostics |
| `prattail/src/pipeline.rs` | WPDS analysis block, INT-01/02/03, COMP-07 |
| `prattail/src/trampoline.rs` | RT-01 frame pool pre-sizing |
| `prattail/src/decision_tree.rs` | COMP-07 trie confirmation support |
| `prattail/src/lib.rs` | Module registration |

---

## 19. Future Work (Phase 5 — Deferred)

- **EWPDS merging functions** — Cross-category composition with BP transformation tracking
- **Bar-Hillel intersection** — WPDA intersection with WFSA for tab completion and repair ranking
- **Relational weight domain** — Track binding power transformations across category boundaries
- **Corpus-trained weights** — Forward-backward on WPDA with LogWeight semiring

Note: CS-01/04/05 provide structural frameworks that can be further refined with
per-rule-per-context poststar reachability data in a future sprint.

---

## 20. References

- Reps, T., Lal, A., & Kidd, N. (2007). *Program Analysis Using Weighted Pushdown
  Systems.* In: FSTTCS 2007. LNCS 4855, Springer.

- Droste, M., Dziadek, S., & Kuich, W. (2019). *Weighted simple reset pushdown
  automata.* Theoretical Computer Science, 777, 252–271.

- Butoi, S., Fasanya, T., Cotterell, R., & Vieira, T. (2022). *Algorithms for Weighted
  Pushdown Automata.* EMNLP 2022.

- Tarjan, R. E. (1972). *Depth-first search and linear graph algorithms.*
  SIAM Journal on Computing, 1(2), 146–160.

---

## Cross-References

- [WPDS Layer Expansion Design](wpds-expansion/README.md) — Hub document for
  the 8-sprint expansion
- [Five-Tier Dead-Rule Detection](dead-rule-detection.md) — Tier 5 WPDS-based detection
- [Diagnostic Reference](../../diagnostics/README.md) — All lint diagnostics
- [Pipeline Integration](../../architecture/wfst/pipeline-integration.md) — Data flow
