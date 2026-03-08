# Concurrency Analysis Diagnostics (N-Category)

**Source:** `prattail/src/lint.rs` (emission), `prattail/src/petri.rs` (N01/N02),
`prattail/src/nominal.rs` (N03/N04), `prattail/src/alternating.rs` (N05)

## Overview

The N-category lints report on the concurrency, scoping, and behavioral
equivalence properties of the grammar, as discovered by three complementary
analysis engines: Petri net coverability (deadlock and resource analysis),
nominal automata (name-binding scope analysis), and alternating automata
(bisimulation equivalence). These diagnostics help grammar authors understand
the concurrent behavior of grammars that model process calculi, concurrent
languages, or any formalism with parallel composition and name binding.

The analysis pipeline:

```
  ┌───────────────────────────────────────────────────────────────┐
  │                     Grammar Specification                     │
  └────────┬──────────────────┬─────────────────┬─────────────────┘
           │                  │                 │
           v                  v                 v
  ┌──────────────────┐ ┌─────────────────┐ ┌────────────────────┐
  │   Petri Net      │ │    Nominal      │ │   Alternating      │
  │  (petri.rs)      │ │  (nominal.rs)   │ │ (alternating.rs)   │
  │                  │ │                 │ │                    │
  │  Places ←── cats │ │  Names ←── ids  │ │  States ←── cats   │
  │  Trans ←── rules │ │  Orbits ←── eq │ │  Trans ←── rules   │
  │  Tokens ←── toks │ │  Support ←── s │ │  Game ←── product  │
  └────┬────────┬────┘ └────┬──────┬────┘ └────────┬───────────┘
       │        │           │      │               │
       v        v           v      v               v
  ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐
  │  N01   │ │  N02   │ │  N03   │ │  N04   │ │  N05   │
  │deadlock│ │unbound │ │ scope  │ │ scope  │ │non-bis │
  │  risk  │ │channel │ │violate │ │narrow  │ │imilar  │
  └────────┘ └────────┘ └────────┘ └────────┘ └────────┘
```

## Lint Index

| ID | Name | Severity | Feature Gate | Description |
|----|------|----------|--------------|-------------|
| [N01](N01-deadlock-risk.md) | deadlock-risk | Warning | `petri` | Petri net coverability detects potential deadlock |
| [N02](N02-unbounded-channel.md) | unbounded-channel | Warning | `petri` | Place has unbounded token capacity |
| [N03](N03-scope-violation.md) | scope-violation | Warning | `nominal` | Name used outside its binding scope |
| [N04](N04-scope-narrowing.md) | scope-narrowing | Note | `nominal` | Binder scope can be tightened |
| [N05](N05-non-bisimilar.md) | non-bisimilar | Warning | `alternating` | Categories are not bisimilar (attacker wins game) |

## Severity Distribution

- **Warning (4):** N01, N02, N03, N05 -- require grammar author review.
- **Note (1):** N04 -- informational suggestion for scope refinement.

## Feature Gates

All five N-category lints are feature-gated. None are always-on. This reflects
the fact that concurrency analysis is only meaningful for grammars that model
concurrent or name-binding constructs.

| Feature | Lints | Analysis Engine | Description |
|---------|-------|-----------------|-------------|
| `petri` | N01, N02 | Petri net coverability | Deadlock and resource boundedness |
| `nominal` | N03, N04 | Nominal automata | Name-binding scope analysis |
| `alternating` | N05 | Alternating automata | Bisimulation equivalence |

## Theoretical Background

### Petri nets (N01, N02)

A Petri net is a bipartite directed graph N = (P, T, F, W, M_0) where:
- P is a finite set of *places* (parser states, token buffers).
- T is a finite set of *transitions* (rule applications).
- F subset (P x T) union (T x P) is the *flow relation*.
- W: F --> N is the *weight function* (arc multiplicities).
- M_0: P --> N is the *initial marking* (initial token distribution).

A transition t is *enabled* at marking M if forall p in pre(t), M(p) >= W(p, t).
A *dead marking* is one where no transition is enabled (deadlock). The
*Karp-Miller coverability tree* extends the reachability tree with omega markers
for unbounded places, enabling decidable analysis of boundedness and coverability.

### Nominal automata (N03, N04)

A nominal automaton operates over an infinite alphabet of *names* (atoms).
States carry a *support* -- the finite set of names they depend on. Transitions
are equivariant: they commute with name permutations. The key concepts are:
- **Orbit:** An equivalence class of configurations under name permutation.
- **Binder:** A syntactic construct that introduces a fresh name into scope.
- **Scope:** The syntactic region where a bound name is valid.
- **Alpha-equivalence:** Two terms are alpha-equivalent if they differ only in
  the choice of bound names.

### Alternating automata and bisimulation (N05)

An alternating automaton generalizes nondeterministic automata by allowing
transitions to branch both existentially (there exists a successor) and
universally (all successors must satisfy). Bisimulation is checked via a
two-player game:
- **Attacker** (existential player): chooses transitions to expose differences.
- **Defender** (universal player): must match every Attacker move.

Two states are bisimilar if the Defender has a winning strategy for the
infinite-round game starting from those states. The game is decided by
a fixed-point computation over the product state space.

## Interaction Between Analyses

The three analysis engines are independent but their results can interact:

- **N01 + N02:** Adding capacity bounds to unbounded places (resolving N02)
  may introduce new deadlocks (triggering N01), and vice versa.

- **N03 + N04:** Scope violations (N03) and scope narrowing (N04) are
  complementary: N03 detects names that escape their scope, while N04
  detects scopes that are wider than necessary. Both inform the same
  nominal model.

- **N03 + N05:** Scope violations can cause non-bisimilarity. If two categories
  differ in which names are in scope, the Attacker can exploit this as a
  distinguishing move.

- **N01 + N05:** Non-bisimilar categories used in parallel composition may
  contribute to deadlock if their behavioral differences create blocking
  dependencies.

## Related Diagnostic Categories

- **S (Safety):** S01-S06 -- safety verification and structural analysis via WPDS
- **W (WFST-Specific):** W01, W13 -- dead-rule detection complements concurrency analysis
- **G (Grammar Structure):** G07 -- identical rules; a precondition for bisimilarity
- **D (Decision Tree):** D14-D15 -- WPDS complexity and witness traces
