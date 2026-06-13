# Rho-Native Dataflow Lowering

Last updated: 2026-06-13

This document explains how Dovetail rewrite semantics are compiled into a
Rho-native dataflow network. The generated execution artifact is normalized
Rholang AST (`models::rhoapi::Par`) that feeds directly into the Rho interpreter;
Rholang source snippets appear here only as reader annotations. The design uses
Rholang and RSpace as intended: communication is the scheduling mechanism.

The lowering is grounded in Rholang's reflective process model
([RHO-2005](references.md#rho-2005)), RSpace's tuple-space API
([RSPACE-DOCS](references.md#rspace-docs)), and Rholang's syntax and
concurrency rules ([RHOLANG-DOCS](references.md#rholang-docs)).

All symbols used here are defined in
[Concepts and Glossary](01-concepts-and-glossary.md).

## Core Correspondence

| Dovetail concept | Rho-native representation |
|---|---|
| fact | RSpace message |
| delta fact | message on a delta channel |
| rewrite rule | persistent Rholang contract |
| premise | receive pattern |
| multi-premise rule | atomic RSpace join |
| guard | RSpace `where` predicate or native guard handler |
| derived fact | send from rule continuation |
| exact key | canonical channel or payload identity |
| ambiguity | explicit candidate facts |
| normal form | observed output fact after quiescence |

The guiding equation is:

`lower(derive(F, Δ)) = comm_step(lower(F), lower(Δ))`

In words: one Dovetail derivation step lowers to one or more RSpace
communications that emit the same observable fact.

## RhoNet Intermediate Calculus

RhoNet is a proof-oriented intermediate representation. It is deliberately
smaller than full Rholang.

### Syntax

| Form | Meaning |
|---|---|
| `Fact(ch, payload)` | A message is present on channel `ch`. |
| `Contract(name, binds, guard, body)` | A persistent receive that fires for every matching message tuple. |
| `Join(binds)` | An atomic multi-channel receive. |
| `Send(ch, payload)` | Emit a fact. |
| `New(names, body)` | Create private names for an evaluation. |
| `Par(p, q)` | Run two subprocesses concurrently. |
| `Observe(ch)` | Declare an observable output channel. |

### Operational Step

The central RhoNet transition is COMM:

`Fact(c₁, a₁) | ... | Fact(cₙ, aₙ) | Contract(k, binds, guard, body) → body[σ]`

provided:

`match(binds, (c₁, a₁), ..., (cₙ, aₙ)) = σ`

and:

`guard(σ) = true`

If `guard(σ) = false`, no fact is consumed and no body is emitted.

## Lowering Shape

![Dovetail rule to RhoNet and Rholang dataflow lowering](figures/04-rho-native-dataflow-lowering.svg)

PlantUML source:
[figures/04-rho-native-dataflow-lowering.puml](figures/04-rho-native-dataflow-lowering.puml).

```plantuml
@startuml
title Dovetail Rule to RhoNet / Rholang Dataflow

skinparam backgroundColor #FEFEFE
skinparam shadowing false
skinparam activity {
  BorderColor #1F2937
  FontColor #111827
  ArrowColor #374151
}

start
:Dovetail rule\n`p₁ ∧ ... ∧ pₙ ∧ g ⇒ q`;
:Compute exact keys\nfor premise channels; <<#DBEAFE>>
:Create RhoNet join\nfor `p₁ ... pₙ`; <<#DCFCE7>>
if (guard class?) then (same-bind pure)
  :Lower to RSpace\n`where` guard; <<#FEF3C7>>
elseif (cross-bind or external)
  :Lower to native\nguard handler; <<#FDE68A>>
else (none)
  :Use `true`; <<#E5E7EB>>
endif
:Emit persistent contract AST; <<#FCE7F3>>
:Attach Rholang-text\nreader annotation; <<#FBCFE8>>
:Inject normalized `Par`\ninto RhoRuntime; <<#EDE9FE>>
stop

legend right
  <#DBEAFE> key/channel selection
  <#DCFCE7> RhoNet construction
  <#FEF3C7> direct RSpace guard
  <#FDE68A> native handler guard
  <#FCE7F3> Rholang AST surface
  <#EDE9FE> host Rho execution
endlegend
@enduml
```

## Example: Unary Rewrite

Source rule:

`Neg(Neg(x)) → x`

Dovetail form:

`Term(Neg(Neg(x))) ⇒ Rw(Neg(Neg(x)), x)`

RhoNet form:

`Contract("rule:double-neg", bind Fact("delta:Proc", Neg(Neg(x))), true, Send("delta:Proc", x))`

Rholang sketch:

```rholang
contract @"mtl:rule:double-neg"(@term) = {
  match term {
    ["Neg", ["Neg", x]] => { @"mtl:delta:Proc"!(x) }
    _ => { Nil }
  }
}
```

The sketch is illustrative. The implementation constructs the equivalent
normalized `Par` value directly. Text like the sketch may be stored as an
annotation for logs and documents, but it is not parsed as the execution path.

## Example: Multi-Premise Rewrite as Join

Consider a rule with two premises:

`A(x) ∧ B(x, y) ⇒ C(y)`

RhoNet lowers this to one atomic join:

`for (@a <- ch_A & @b <- ch_B where compatible(a, b)) { ch_C!(project_y(b)) }`

The atomicity matters. If `A(x)` is available but no compatible `B(x, y)` is
available, RSpace does not consume `A(x)`. This matches the logical reading of
conjunction:

`A(x) ∧ B(x, y)` is available only when both conjuncts are available.

## Example: rhocalc COMM

Source term:

```text
{ (c?x).{*(x)} | c!(p) }
```

Source rewrite:

`{ (c?x).{*(x)} | c!(p) } → p`

Rho-native lowering, rendered here as text for readability:

```rholang
new out in {
  for (@x <- @"mtl:c") { @"mtl#out"!(x) } |
  @"mtl:c"!(p)
}
```

RSpace performs the communication when both sides are present. This is not a
simulation of COMM; it is COMM delegated to the host Rho machine.

## Semi-Naive Channels

The Rho backend uses two fact families:

| Family | Meaning |
|---|---|
| `fact` | Stable facts already accepted into the known set. |
| `delta` | Newly discovered facts that should trigger rule work. |

The logical equations are:

`Fᵢ₊₁ = Fᵢ ∪ Δᵢ₊₁`

`Δᵢ₊₁ = derive(Fᵢ, Δᵢ) ∖ Fᵢ`

The Rho-native network realizes these equations with contracts:

- delta facts trigger rule contracts;
- derived candidates ask the dedup service whether the exact key is new;
- new facts are emitted to both stable and next-delta channels.

## Literate Algorithm: Lower a Rewrite Rule

The following is pseudocode, not executable code.

```pseudocode
Algorithm: Lower a Dovetail rewrite rule to RhoNet

Given:
  rule r
  premise patterns P = [p₁, ..., pₙ]
  guard g
  right-hand side builder q
  category metadata M

Produce:
  RhoNet contract C

Steps:
  1. Assign a canonical channel to each premise.
     The channel is determined by the premise category, relation kind, and
     exact key fields that are known before matching.

  2. Convert each premise pattern into a RhoNet bind pattern.
     The bind pattern extracts the values needed by the substitution `σ`.

  3. Classify the guard.
     If the guard depends only on variables from one bind and can be rendered
     as a pure Rholang boolean, mark it as an RSpace where-guard.
     Otherwise mark it as a native guard-handler call.

  4. Build an atomic join over all premise channels.
     The join has one body and commits only when all binds and the guard hold.

  5. In the body, construct `q(σ)`.
     Compute its exact output key.

  6. Send the candidate fact to the dedup service.
     If the key is new, emit it as stable fact and delta fact.

  7. Wrap the join body in a persistent contract.
     The contract remains available for subsequent arriving facts.
```

### Invariant

Every contract firing corresponds to a substitution satisfying the source rule:

`fires(Cᵣ, σ) ⇒ patternᵣ(σ) ∧ premisesᵣ(σ) ∧ guardᵣ(σ)`

## Literate Algorithm: Deduplicate and Emit a Fact

The following algorithm is the Rho-native analogue of exact-key insertion.

```pseudocode
Algorithm: Deduplicate and emit a Rho fact

Given:
  candidate fact f
  exact key k
  fact channel fact_ch
  delta channel delta_ch
  seen channel seen_ch

Produce:
  zero or more emitted RSpace messages

Steps:
  1. Ask the seen service whether k is already present.

  2. If k is present:
       emit no stable fact and no delta fact.
       The candidate has already been represented.

  3. If k is absent:
       record k on seen_ch.
       emit f on fact_ch.
       emit f on delta_ch.

  4. If k collides with a non-equivalent existing fact:
       emit an exact-key violation diagnostic and stop the run.
```

### Invariant

The emitted Rho fact set is key-equivalent to the Dovetail fact set:

`keys(resting_facts) = keys(F)`

## Ambiguity as Explicit Data

Rholang scheduling is nondeterministic where several communications are enabled.
That nondeterminism must not become semantic pruning.

Bad lowering:

`select candidate₁ or candidate₂`

Correct lowering:

`candidate(candidate₁) | candidate(candidate₂)`

The first representation chooses one. The second represents both. Therefore the
Rho backend represents ambiguity as explicit facts on candidate channels.

## Name and Capability Discipline

Every evaluation receives a private namespace:

`New(eval_id, body)`

Within that namespace:

- internal fact channels are private;
- output is routed through `@"mtl#out"`;
- source names are grounded with a disjoint prefix;
- bundles may restrict read/write access when the rendered Rholang can express
  the restriction cleanly.

The safety condition is:

`internal_channel ∉ free_names(user_program)`

and:

`sentinel_channel ∉ image(ground_source_name)`

## Why RhoNet Before Rholang?

RhoNet gives the proof a small target:

`Dovetail → RhoNet → Rholang/RSpace`

The first arrow proves semantic preservation from facts/rules to dataflow. The
second arrow proves that the emitted Rholang uses host primitives in the intended
way.

This avoids proving correctness directly over the full host AST format while
still making the runtime artifact explicit. The second proof/engineering layer
checks that generated `Par` values satisfy the host representation invariants
that source parsing used to hide.
