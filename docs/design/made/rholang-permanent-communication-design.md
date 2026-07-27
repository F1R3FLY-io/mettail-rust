# Rholang Permanent Send/Receive and COMM Normalization Design

**Status:** Implemented  
**Primary areas:** `languages/src/rholang.rs`, `languages/src/rholang/runtime.rs`, `languages/src/rholang/receive.rs`

---

## 1. Goal

This design defines durable communication semantics in Rholang and stabilizes COMM behavior around send/receive sugar.

The core product goals are:

- Add permanent receive syntax and runtime behavior (`<=`) that keeps the listener after a successful COMM.
- Add permanent send syntax and runtime behavior (`!!`) that keeps the sender after a successful COMM.
- Support polyadic receive/send sugar without introducing arity bugs in COMM.
- Keep empty bind semantics explicit and deterministic.
- Preserve existing ephemeral receive behavior (`<-`) and compatibility with current normal-form exploration.

---

## 2. Scope

Implemented behavior includes:

- Permanent single receives and join receives.
- Permanent sends and their interaction with ephemeral/permanent receives.
- Guarded receives (`where`) across permanent and ephemeral variants.
- Empty bind receives (`for(<= c){...}`) with strict payload-shape matching.
- Canonicalization of send payloads and receive patterns for arity-stable COMM.

Out of scope:

- New public API surface in external crates.
- Changes to evaluator architecture outside receive/normalization path.

---

## 3. Problem Statement

Before this work, communication behavior was primarily tuned for ephemeral COMM and had multiple sugar entry points that could produce shape mismatches:

- Polyadic sugar (`x!(a,b,c)`, `for(a,b,c <- x){...}`) could reach COMM in non-canonical forms.
- Empty-send / empty-bind cases required explicit handling to avoid false-positive reductions.
- Permanent send/receive semantics needed precise consume/retain policy across all communication combinations.

The architecture needed one deterministic COMM contract:

1. normalize syntax sugar into canonical internal forms,
2. match using arity-safe and guard-aware logic,
3. apply substitutions,
4. remove/reinsert terms based only on permanence flags.

---

## 4. Design Decisions

### 4.1 Canonical COMM input shape

All relevant send/receive sugar is normalized before COMM, so matching logic operates on one payload representation.

Decision:

- Model polyadic payloads as list-shaped unary payloads internally.
- Canonicalize both payload and pattern shape in runtime normalization + receive helpers.

Why:

- Reduces branch complexity in COMM matching.
- Prevents divergence between parser sugar variants and runtime semantics.
- Keeps arity mismatch behavior testable and deterministic.

### 4.2 Permanent send/receive as consume policy, not separate COMM engine

Decision:

- Reuse the same COMM pipeline for permanent and ephemeral communication terms.
- Drive post-match term retention from `(permanent_recv, permanent_send)` classification.

Why:

- Avoids duplicated matching/substitution logic.
- Keeps behavioral matrix explicit:
  - ephemeral recv + ephemeral send: consume both
  - ephemeral recv + permanent send: consume recv only
  - permanent recv + ephemeral send: consume send only
  - permanent recv + permanent send: consume neither

### 4.3 Empty bind as explicit predicate

Decision:

- Keep empty bind handling (`for(<- c){...}`, `for(<= c){...}`) as first-class logic via dedicated checks.

Why:

- Empty bind should only fire on empty payload shape.
- Enforcing this at match time prevents accidental reductions on non-empty payloads.

### 4.4 Guard semantics are pre-commit checks

Decision:

- Evaluate `where` guard before committing the reduction result.
- Block reduction on non-`true` outcomes.

Why:

- Aligns with receive-as-filter interpretation.
- Prevents invalid substitutions from being committed when guard fails.

### 4.5 Small-struct context for single receive path

Decision:

- Consolidate single receive matching inputs into a context struct (`SingleReceiveCtx`) instead of passing many independent parameters.

Why:

- Keeps `finish_single_comm` cohesive and less error-prone.
- Centralizes receive-mode flags (`permanent_recv`, `empty_bind`) with bound pattern and continuation.
- Improves maintainability without changing semantics.

---

## 5. Architecture

### 5.1 Parser/surface syntax

Rholang adds/uses:

- Permanent binds: `<=` (single and join rows).
- Permanent sends: `!!`.
- Polyadic sugar for send and receive.
- Query and empty variants that are desugared/normalized before final COMM matching.

### 5.2 Runtime normalization boundary

Normalization ensures COMM sees canonical terms:

- Empty send sugar becomes list payload form.
- Polyadic sends become unary send with list payload.
- Receive rows are desugared into stable internal bind structures.
- Parallel shape is normalized for reliable COMM entry.

### 5.3 COMM evaluation path

High-level flow:

1. Candidate receive row selected.
2. Candidate output(s) searched in parallel bag.
3. Payload/pattern compatibility checked (including empty bind and arity).
4. Optional guard (`where`) evaluated.
5. Continuation term produced via substitution or guarded COMM wrapper.
6. Bag updated according to permanent/ephemeral policy.

### 5.4 REPL normal-form selection

A companion behavior update in REPL progression prefers reachable rewrite progress from the initial term.  
This aligns UX with the new larger rewrite spaces introduced by permanent behavior and keeps user-visible progression intuitive.

---

## 6. Testing Strategy

Integration tests in `languages/tests/rholang_tests.rs` cover:

- Permanent receive + ephemeral send.
- Permanent receive + permanent send.
- Ephemeral receive + permanent send.
- Join receives with mixed permanence.
- `where` true/false behavior on permanent rows.
- Empty permanent receive behavior.
- Polyadic matching success and arity mismatch blocking.
- Semicolon row behavior with permanent first rows.
- REPL-facing reachable normal-form expectations.

Design intent of tests:

- Verify consume/retain matrix directly.
- Ensure sugar-normalized and canonical forms are semantically equivalent.
- Prevent regressions in matching edge cases (empty payload and arity).

---

## 7. Trade-offs and Alternatives

### Alternative A: separate permanent COMM implementation

Rejected.  
Would duplicate matching and substitution logic and increase bug surface.

### Alternative B: preserve sugar forms deeper into COMM

Rejected.  
Creates many representational branches and weaker guarantees around arity/shape.

### Alternative C: lenient empty bind matching

Rejected.  
Would make reductions less predictable and break explicit empty-pattern semantics.

---

## 8. Risks and Mitigations

- **Risk:** rewrite-space growth from permanent terms may affect usability.  
  **Mitigation:** reachable normal-form selection behavior in REPL and focused tests.

- **Risk:** subtle regressions in mixed permanence + join rows.  
  **Mitigation:** dedicated matrix-like tests across single/join and guard/no-guard.

- **Risk:** sugar-path divergence over time.  
  **Mitigation:** canonicalization boundary before COMM; tests assert sugar equivalence.

---

## 9. Outcome

Rholang communication semantics use a more explicit and canonical architecture:

- permanent send/receive are implemented as policy, not forked runtime logic,
- COMM works on normalized internal forms,
- edge cases (empty bind, guard, arity) are deterministic,
- test coverage tracks the new behavior surface.

This keeps the implementation simple, composable, and aligned with the existing pipeline-style interpreter design.

---

## 10. Canonical COMM Examples

The following one-step examples capture the permanence matrix and expected post-COMM shape.

### 10.1 Ephemeral receive + ephemeral send

Input:

```
{for(x <- c){*x} | c!(p)}
```

One COMM step:

```
p
```

Expected effect: receive and send are both consumed.

### 10.2 Ephemeral receive + permanent send

Input:

```
{for(x <- c){*x} | c!!(p)}
```

One COMM step:

```
{p | c!!(p)}
```

Expected effect: receive is consumed; permanent send remains.

### 10.3 Permanent receive + ephemeral send

Input:

```
{for(x <= c){*x} | c!(p)}
```

One COMM step:

```
{p | for(x <= c){*x}}
```

Expected effect: send is consumed; permanent receive remains.

### 10.4 Permanent receive + permanent send

Input:

```
{for(x <= c){*x} | c!!(p)}
```

One COMM step:

```
{p | for(x <= c){*x} | c!!(p)}
```

Expected effect: neither communication endpoint is consumed.
