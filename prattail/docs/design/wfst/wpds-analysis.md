# Weighted Pushdown System (WPDS) Analysis Layer

## Overview

PraTTaIL's trampoline parser **is** a pushdown automaton: it maintains an explicit
`Vec<Frame_Cat>` stack, uses `(category, min_bp)` as states, and consumes tokens as
input. The existing `PredictionWfst` provides finite-state analysis at compile time but
cannot reason about stack context. The WPDS layer adds **pushdown-aware** compile-time
analysis — it can determine whether a grammar rule is reachable only in stack
configurations that actually occur during parsing.

```
LanguageSpec ──→ build_wpds() ──→ Wpds<W>
                                     │
                ┌────────────────────┤
                │                    │
                ▼                    ▼
         poststar(BooleanWeight)   stringsum(CountingWeight)
         → stack-aware reachability → exact ambiguity counts
                │                    │
                ▼                    ▼
         lint.rs (W13)         cost_benefit.rs (G25)
```

## Theoretical Foundations

Three complementary formalisms underpin the implementation:

1. **Reps, Lal & Kidd (2007)** — Weighted Pushdown Systems for interprocedural
   analysis. poststar/prestar saturation produces weighted P-automata encoding all
   reachable configurations with call/return matching. This is the primary algorithm.

2. **Droste, Dziadek & Kuich (2019)** — Simple reset WPDA normal form. Three stack ops
   (push/pop/noop), no epsilon-transitions. Canonical algebraic system:
   `X = M_0 X + Sum_t M_{1,t} X M_{2,t} X + E`
   mapping directly onto Pratt's infix continuation / nested subexpression / atom.

3. **Butoi et al. (2022)** — Direct WPDA stringsum algorithm. O(n^3 |Q|^3 |Gamma|^3)
   per input. Avoids CFG conversion, provides |Q| * |Gamma| speedup over Lang (1974).

## Grammar-to-WPDS Mapping

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
- **Stack alphabet Gamma** = `StackSymbol(category, rule_label, position)` triples
- **Rules Delta**:
  - **Replace** (intraprocedural): `<p, (Cat, rule, pos)> -> <p, (Cat, rule, pos+1)>`
    — consuming a terminal advances position within a rule
  - **Push** (cross-category call): `<p, (Cat, rule, pos)> -> <p, (Callee, "", 0)(Cat, rule, pos+1)>`
    — enter callee category, push return address
  - **Pop** (return): `<p, (Cat, rule, last)> -> <p, epsilon>`
    — rule complete, pop frame

### Weight Assignment

Weights come from the `PredictionWfst`:
- If a WFST transition exists from `Cat` on `rule_label`, use its tropical weight
- Otherwise, default weight `TropicalWeight(1.0)` (unit cost)
- Cross-category rules: weight = weight of the rule in the calling category

## Algorithms

### poststar — Forward Reachability Saturation

The core algorithm for grammar-wide analysis. Given an initial P-automaton encoding the
start configuration (start category, empty stack), poststar saturates it to encode ALL
reachable configurations:

```
Input:  A_0 = P-automaton for initial configs {(p, [<StartCat, "", 0>])}
Output: A_post* = P-automaton encoding all configs reachable from A_0

Algorithm:
  worklist := initial transition set
  while worklist not empty:
    pick (q, gamma, q') from worklist
    for each WPDS rule r matching gamma:
      case Pop:  add (p, gamma, q_accept) with weight f(r) * w(q,gamma,q')
      case Replace(gamma'): add (p, gamma', q') with weight f(r) * w(q,gamma,q')
      case Push(gamma1, gamma2):
        add fresh state q_r
        add (p, gamma1, q_r) with weight f(r)
        add (q_r, gamma2, q') with weight 1
```

**Complexity:** O_s(|P| |Delta| (|Q_0| + |Delta|) H) where H = weight domain height.

**Reachability semantics:** A stack symbol `gamma` is reachable if it appears on ANY
transition `(q, gamma, q')` where `q` is the initial state — not necessarily where `q'`
is an accepting state. This is critical for cross-category symbols that appear mid-stack.

### prestar — Backward Reachability Saturation

Dual of poststar: computes all configurations from which a target set is reachable.
Currently implemented but not used in the pipeline.

### stringsum — Per-Input Analysis

Given a specific input token sequence, computes the total weight of all accepting runs:

```
stringsum(input) = bigoplus_{rho in Acc(input)} weight(rho)
```

Over the counting semiring, this gives the exact number of parse trees (ambiguity).
Over the tropical semiring, it gives the minimum-cost parse.

## Pipeline Integration

### G25 WpdsReachabilityCheck (cost_benefit.rs)

Optimization gate controlling WPDS analysis:
- **Speedup:** 0.4 (moderate — improves dead-rule precision)
- **Cost:** 0.3 (moderate — WPDS construction + saturation)
- **Applicable:** When `category_count >= 2` (cross-category calls exist)
- **Type:** Diagnostic (not Auto — opt-in)

### W13 WpdsUnreachable (lint.rs)

New lint that reports rules unreachable under full pushdown analysis:

```
warning[W13]: rule 'OrphanRule' in category 'Orphan' is unreachable under WPDS analysis
  --> grammar definition
  = note: this rule cannot be reached from the start category via any valid call/return sequence
  = note: missing caller context: no category dispatches to 'Orphan'
```

Severity: Warning. Iterates `WpdsAnalysis.unreachable_rules`.

### Pipeline Block (pipeline.rs)

Conditionally runs WPDS analysis before the unified lint layer:

```rust
if optimization_gates.wpds_reachability && bundle.categories.len() >= 2 {
    let cat_infos = /* build WpdsCategoryInfo from bundle */;
    let analysis = analyze_wpds_from_bundle(&cat_infos, &bundle.wfst, start_category);
    // Pass to LintContext
}
```

Uses `analyze_wpds_from_bundle()` which reconstructs a minimal LanguageSpec from
ParserBundle data, avoiding changes to the pipeline function signature.

## What WPDS Does NOT Do

- **Runtime parsing** — Pratt is O(n), WPDA stringsum is O(n^3). The WPDS layer is
  strictly compile-time.
- **Replace the WFST** — The PredictionWfst remains the primary dispatch ordering
  mechanism. WPDS augments it with pushdown-aware analysis.
- **Lexing** — The lexer is purely regular (NFA -> DFA -> minimized DFA). No pushdown
  power needed.
- **Real-time dispatch** — WPDS results are precomputed, not evaluated on the hot path.

## Semiring Compatibility

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

## Files

| File | Role |
|---|---|
| `prattail/src/wpds.rs` | Core implementation (~1400 lines + 17 tests) |
| `prattail/src/cost_benefit.rs` | G25 optimization gate |
| `prattail/src/lint.rs` | W13 lint diagnostic |
| `prattail/src/pipeline.rs` | Conditional WPDS analysis block |
| `prattail/src/lib.rs` | Module registration |

## Future Work (Phase 5 — Optional)

- **EWPDS merging functions** — Cross-category composition with BP transformation tracking
- **Bar-Hillel intersection** — WPDA intersection with WFSA for tab completion and repair ranking
- **Relational weight domain** — Track binding power transformations across category boundaries
- **Corpus-trained weights** — Forward-backward on WPDA with LogWeight semiring
