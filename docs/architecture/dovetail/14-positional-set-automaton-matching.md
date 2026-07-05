# Positional Set-Automaton Matching

> Status: current (2026-07-05). Covers `dovetail/src/set_automaton.rs` and the
> `CompiledRuleSet` reuse surface in `dovetail/src/rules.rs`.

## 1. Why This Document Exists

Dovetail's default matcher walks each rule's left-hand-side pattern against every
candidate e-class recursively (see [Rules and Saturation §Search And
Instantiation](04-rules-and-saturation.md#search-and-instantiation)). The
**positional set automaton** is a shared matching substrate that compiles a whole
set of left-hand-side patterns **once** and dispatches, at each subject root, only
the candidate patterns whose root symbol and arity can match — the reusable
matching layer the Rho-native runtime plan builds on
([13 — Knotted-Topoi Operational Invariants](../rho-native-integration/13-knotted-topoi-operational-invariants.md)
cites it as the compile-time matcher whose result the σ-injection consumes).

This document defines the algorithm, its associative-commutative (AC) exclusion
boundary, and the compiled-rule-set reuse property, and maps each to the code, the
oracle test, and the mechanized proof.

## 2. The Data Model

| Term | Meaning | Rust |
|---|---|---|
| `Pattern::Var(name)` | a pattern variable — matches any e-node, binds `name` in σ | `rules.rs` `Pattern` |
| `Pattern::App { op, args }` | a **positional** application — a fixed symbol `op` over ordered child patterns | `rules.rs` `Pattern` |
| `Pattern::AcApp { op, args, rest }` | an **associative-commutative** application — order-insensitive, with an optional `rest` complement | `rules.rs` `Pattern` |
| `PatternId(usize)` | a caller-assigned stable id for a compiled pattern | `set_automaton.rs:19` |
| `SetAutomatonMatch { pattern, root, subst }` | one match: which pattern, at which root e-class, under which σ | `set_automaton.rs:23` |

The subject is the saturated e-graph; a **root** is a canonical e-class considered
as a potential redex head.

## 3. The Algorithm

```text
  compile_structural(patterns)                          scan(egraph)
  ─────────────────────────────                         ────────────
  for (id, p) in patterns:                              for each canonical root class c:
    if contains_ac(p):            ┌── AC boundary ──┐     for each e-node n in c:
        unsupported.push(id)  ────┤ AcApp rejected  │       key = (n.op, n.arity)
    else:                         │ → lazy e-graph  │       candidates =
        key = (p.op, p.arity)     │   path (§4)      │         variable_roots            (Var: match any root)
        index[key].push(id)       └─────────────────┘         ∪ index[key]               (App: op+arity agree)
        compile p's state tree                                for id in candidates:
  ↓                                                             σ = recursive_match(pattern[id], n)   (positional, cached)
  Ok(CompiledRuleSet)  ──reused across many e-graphs──►         if σ: emit SetAutomatonMatch{id, c, σ}
```

Three ideas do the work:

1. **Root indexing.** Every structural pattern is keyed by its **root symbol and
   arity** `(op, arity)`. Scanning an e-node `n` only dispatches the patterns under
   key `(n.op, n.arity)` (plus the variable patterns, which match any root). The
   recursive positional match then runs *only* on those candidates. This is the
   candidate-pruning the set automaton exists for (`SetAutomatonStats.candidate_evaluations`,
   `set_automaton.rs:37`).
2. **State caching.** Compiled pattern states are interned (`StateId`) and their
   substitution results cached per canonical e-class, so repeated sub-pattern work
   across the scan is memoized (`state_cache_hits` / `state_evaluations`).
3. **Compile once, scan many.** `CompiledRuleSet` (`rules.rs:361`) hoists the
   positional automaton out of the per-graph loop: one compilation is applied to
   every e-graph in a saturation run.

## 4. The Associative-Commutative Boundary

Positional matching assumes **ordered, fixed-arity** children. AC patterns
(`Pattern::AcApp`) are order-insensitive and may bind a `rest` complement whose
materialization is **budget-gated** (it can enumerate sub-multisets — see
[Rules and Saturation §Associative-Commutative Matching](04-rules-and-saturation.md#associative-commutative-matching)).
Compiling them positionally would be unsound. Therefore:

- `contains_ac` (`set_automaton.rs:334`) flags any pattern containing an `AcApp`
  anywhere, and `compile_structural` (`:160`) returns those `PatternId`s in
  `SetAutomatonError::unsupported` rather than compiling them.
- After that rejection an `AcApp` is `unreachable!` inside the compiler (`:126`,
  `:184`) — AC patterns never enter the positional state machine.
- They remain complete on the **existing lazy AC e-graph path** (the recursive
  matcher with the budgeted `rest` complement), so no matches are lost — only the
  matching *locus* differs.

This is a clean separation: the positional automaton is an **exact, deterministic**
accelerator for the structural fragment; the AC fragment keeps its
budget-accounted lazy semantics.

## 5. Correctness — What Is Guaranteed

| Property | Statement | Evidence |
|---|---|---|
| **Index soundness** | A structural pattern that matches an e-node has an agreeing root `op` + `arity`, so the `(op, arity)` index **never drops a real match**; the automaton's match set equals the recursive oracle's. | oracle test `prop_set_automaton_matches_recursive_positional_oracle` (`dovetail/tests/properties.rs`); proof `index_never_drops_match` + `app_match_requires_root_agreement` |
| **AC separation** | The compiler admits **exactly** the AC-free patterns; an `AcApp` is never dispatched by the positional automaton. | proof `ac_pattern_not_compilable` / `structural_pattern_compilable` / `ac_root_not_dispatched`; unit test `rejects_ac_patterns_without_partial_compilation` (`set_automaton.rs:370`) |
| **Reuse** | The dispatched set is a pure function of `(patterns, node)`, so compiling once and reusing across e-graphs preserves per-node results. | proof `reuse_is_per_node_deterministic`; regression test `compiled_rule_set_reuses_positional_automata_across_graphs` (`rules.rs:1754`) |

All three proofs are mechanized **zero-admission** in
`formal/rocq/advanced_automata/theories/PositionalSetAutomatonSound.v`
(`Print Assumptions` → "Closed under the global context"; built under
`make -C formal check-capped`). See
[07 — Formal Verification and Tests](07-formal-verification-and-tests.md) for the
suite-wide gate.

## 6. Observability

`SetAutomatonStats` (`set_automaton.rs:31`) exposes, per scan: `root_classes`,
`root_nodes`, `candidate_evaluations` (checks after symbol/arity indexing),
`state_evaluations` (cache misses), and `state_cache_hits`. These feed the RhoNet
cost model and the Epic 9 matching-efficiency benchmarks (candidate-evaluation and
recursion-depth reductions).

## 7. References

- Implementation: `dovetail/src/set_automaton.rs`, `dovetail/src/rules.rs`
  (`CompiledRuleSet`, `contains_ac`).
- Tests: `dovetail/tests/properties.rs` (positional oracle equivalence),
  `dovetail/src/rules.rs` (`compiled_rule_set_reuses_positional_automata_across_graphs`).
- Proof: `formal/rocq/advanced_automata/theories/PositionalSetAutomatonSound.v`.
- Set-automaton term rewriting: M. Bouwman and R. Erkens, *Term rewriting based on
  set automaton matching* (`SET-AUTOMATON-MATCHING-2022`, see
  [rho-native references](../rho-native-integration/references.md)).
- Related: [04 — Rules and Saturation](04-rules-and-saturation.md#associative-commutative-matching),
  [13 — Knotted-Topoi Operational Invariants](../rho-native-integration/13-knotted-topoi-operational-invariants.md).
