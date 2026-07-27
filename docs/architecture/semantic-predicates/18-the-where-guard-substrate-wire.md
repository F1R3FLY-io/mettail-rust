# The `where`-Guard Substrate Wire

Last updated: 2026-07-26

All symbols are defined in [Concepts and Glossary](01-concepts-and-glossary.md).
This document specifies the mechanism by which a source-level `where` clause reaches
the semantic-predicate substrate. It is the *implementation* counterpart of
[06 — Guard Syntax and Extensions](06-guard-syntax-and-extensions.md) (what an author
may write), [07 — Language-to-Rholang Integration](07-language-to-rholang-integration.md)
(how obligations are induced), and [08 — Runtime COMM Enforcement](08-runtime-comm-enforcement.md)
(what enforces the surviving predicate). The algebras it dispatches to are specified in
[02](02-effective-boolean-algebra.md)–[05](05-algebra-pyramid-and-decidability.md).

![The `where`-guard wire](figures/18-where-guard-wire.svg)

PlantUML source: [figures/18-where-guard-wire.puml](figures/18-where-guard-wire.puml).

## 0. The governing rule

The rule is a statement about **syntactic position**, not about the shape of the expression:

| syntactic position | evaluator |
|---|---|
| a `where` clause on a guarded receive | the **semantic-predicate substrate** — at compile time where the guard is statically decidable, at run time otherwise |
| an `if` condition | the **Rholang interpreter** |

The same expression `x == 5` is therefore decided by the substrate in a `where` and by the
interpreter in an `if`. There is no partition of expressions into "really predicates" and
"not really predicates"; the clause it sits in settles the question.

### 0.1 Why this document exists

Before the wire, **zero** of Rholang's `where`-guard forms reached the substrate. Not partially:
the substrate was not connected to the `where` surface at all. Two independent gaps produced that:

1. **No obligation was induced.** `collect_guard_obligations` emitted a guard obligation only for
   a `?name:Guard` term parameter. Rholang's guard parameter is `cond:Proc`, an ordinary
   category-typed parameter, which the collector explicitly skipped (§4).
2. **No decision procedure was reached.** The compile-time decision re-used `rho_pure_eval` — the
   Rholang interpreter's own evaluator, run at compile time — and the run-time decision was a
   hand-written walk over the surface AST. Neither is the substrate (§2, §3).

## 1. Concepts introduced here

| Term | Definition | Canonical anchor |
|---|---|---|
| **guard formula** | The substrate image of a `where` guard: a Boolean combination of *sorted atoms*, each dispatched to the algebra that owns its sort. | `enum GuardFormula` (`prattail/src/guard_formula.rs`) |
| **guard var map** | The receive's binder ⇄ substrate-variable-index map. Fixes one order, used by both the formula and every assignment. | `struct GuardVarMap` |
| **static leg** | The compile-time decision: *is the guard true under **every** assignment to the receive's binders?* | `fn static_verdict` |
| **ground leg** | The run-time decision: *does the guard hold under **this** payload?* | `fn ground_verdict_with` |
| **opaque atom** | A guard fragment the substrate deliberately has no procedure for. Decidable only through a caller-supplied resolver. | `struct GuardAtom`, `enum GuardAtomKind` |
| **the fence** | The concrete-semantics evaluator whose agreement is required before a static verdict may change the emitted artifact. | `fn machine_verdict` (`rholang-runtime/src/guard_discharge.rs`) |
| **consensus budget** | The one substrate configuration every node decides `where`-guards with. | `const CONSENSUS_SUBSTRATE_CONFIG` |
| **declared guard slot** | An author's declaration that a category-typed term parameter is a semantic predicate. | `guards { guard_slots { … } }` |

## 2. One vocabulary, two encoders

A `where` guard is decided twice in a program's life, and the two sites hold it in two
different representations:

| site | representation | question |
|---|---|---|
| lowering | the lowered `rhoapi::Par` | can it be settled before any payload exists? |
| COMM | the surface `Proc`, already substituted with the arrived payload | does it hold for *this* payload? |

Each therefore needs its own **encoder**. What they must not have is their own **decider**: two
deciders of one surface guard language is precisely the divergence shape this suite exists to
prevent. Both encoders target a single intermediate vocabulary, `GuardFormula`, and both then
call the same procedures. A disagreement between the compile-time and run-time answers becomes a
statement about one data type rather than about two unrelated code paths.

```math
\mathsf{Proc} \xrightarrow{\ \mathsf{encode}_{\mathrm{surface}}\ } \mathsf{GuardFormula} \xleftarrow{\ \mathsf{encode}_{\mathrm{lowered}}\ } \mathsf{Par}
```

### 2.1 The formula

`GuardFormula` is a Boolean combination — `And`, `Or`, `Not`, `Implies`, and the two constants —
over five atom forms:

| atom | sort | decided by |
|---|---|---|
| `Linear(PresburgerPred)` | integer | Presburger arithmetic, decided by the remainder-based NFA construction |
| `Prop(BooleanTest)` | propositional | the KAT Boolean algebra ([02](02-effective-boolean-algebra.md)) |
| `Scalar { var, pred: AnyPred }` | any non-integer scalar | that sort's effective Boolean algebra |
| `ScalarRel { op, left, right }` | any scalar | exactly, at run time — see §2.3 |
| `Atom(GuardAtom)` | — | **never here**; only a caller's resolver — see §5 |

Integers go to Presburger rather than to the interval algebra because Presburger is strictly
stronger: it relates *several* variables through linear constraints, where an interval predicate
constrains one variable against constants. A comparison of two linear forms
`Σ aᵢxᵢ + c` and `Σ bᵢxᵢ + d` normalizes to `LinearConstraint`'s canonical `Σ eᵢxᵢ ≤ f` shape:

```math
\sum_i a_i x_i + c \;\bowtie\; \sum_i b_i x_i + d
\qquad\Longleftrightarrow\qquad
\sum_i (a_i - b_i)\, x_i \;\bowtie\; d - c
```

with `≠` expanding to a disjunction of two strict inequalities and `=` to a conjunction of two
non-strict ones, exactly as `LinearConstraint::from_neq` and `from_eq` do.

### 2.2 The propositional sort is natively n-ary

`AnyDomain::Bool` is a *truth assignment* keyed by proposition name, not a bare `bool`, and
`KatBooleanAlgebra` ranges over those assignments. A boolean-sorted binder therefore needs no
positional index: it becomes `BooleanTest::Atom(name)`, and an arbitrary number of boolean
binders share one `Prop` atom. This is why `Prop` is a distinct variant rather than a `Scalar`
with a `Bool` leaf.

### 2.3 Why `ScalarRel` exists

`AnyPred` is a **unary** predicate — a set of elements — so it cannot express a relation between
two positions. Two cases therefore have no symbolic encoding and are recorded as relations
instead of being fabricated:

* **variable versus variable**, for any sort;
* an **ordered** comparison on a sort whose algebra carries no order predicate. `StrPred` is a
  *language*, not an order, so lexicographic `<` on strings has no encoding; the arbitrary-precision
  and floating sorts likewise have no bounded-automaton encoding.

Both are *statically undecided and exactly decidable at run time*, which is the split the rule
prescribes rather than a shortfall.

## 3. The three legs

### 3.1 The static leg

`static_verdict` answers one of four things: `Valid`, `Unsatisfiable`, `Contingent`, or
`Undecided`. It is built from a single satisfiability procedure called twice, since

```math
\varphi \text{ is valid} \iff \lnot\varphi \text{ is unsatisfiable},
\qquad
\varphi \text{ is contingent} \iff \varphi \text{ and } \lnot\varphi \text{ are both satisfiable}.
```

`Contingent` is therefore a *proof* that the guard depends on the payload — a positive statement
that the guard belongs to the run-time leg — and is distinguished from `Undecided`, which is a
statement about coverage.

#### 3.1.1 The decidable fragment, and why combination needs care

Satisfiability of a Boolean combination of atoms drawn from *different* theories is a theory-
combination problem. The wire implements the fragment where combination is sound and complete
without a solver, and answers `Undecided` everywhere else — which is always safe, because the
consumer falls back to the run-time leg.

| shape | procedure | exact? |
|---|---|---|
| every atom integer-sorted | fold the whole Boolean structure into one `PresburgerPred` (Presburger is closed under `∧`, `∨`, `¬`), decide by NFA emptiness | yes, over the configured domain |
| every atom propositional | fold into one `BooleanTest`, decide in `KatBooleanAlgebra` | yes |
| every atom a `Scalar` on **one** variable | fold into one `AnyPred`, decide in that sort's algebra | yes |
| a **conjunction** whose conjuncts each fall in one of the above | regroup by theory, conjoin *inside* each theory, combine the per-theory answers with `Sat3::and` | yes |
| anything else | `Undecided(FragmentNotCovered)` | — |

The fourth row's *regrouping* is load-bearing and was got wrong on the first implementation.
`Sat3::and` combines two **independent** satisfiability answers, and independence holds *across*
theories — a binder has exactly one sort, so an integer binder and a boolean binder are different
binders, and two scalar groups are keyed by distinct variables — but emphatically **not within**
one. Concretely:

```math
\mathrm{sat}(x = 1) = \mathsf{Sat}, \quad \mathrm{sat}(x = 2) = \mathsf{Sat}, \quad
\mathrm{sat}\bigl(x = 1 \land x = 2\bigr) = \mathsf{Unsat}.
```

Folding those two conjuncts with `Sat3::and` answers `Sat` for an unsatisfiable formula — unsound
in the direction that matters. Conjuncts are therefore partitioned by theory and conjoined inside
each theory's own decision procedure, and only the per-theory answers are combined. Since `Unsat`
annihilates a conjunction, a proven-unsatisfiable group settles the whole formula even alongside a
conjunct outside the covered fragment.

#### 3.1.2 ⚠ The bounded-domain caveat

Presburger's decision procedure here runs over a **bounded** integer domain, `[-2^{w-1}, 2^{w-1})`
for a bit width `w`. Over a bounded domain, neither implication holds:

```math
\mathrm{valid}_{2^w}(\varphi) \;\not\Rightarrow\; \mathrm{valid}_{\mathbb{Z}}(\varphi),
\qquad
\mathrm{unsat}_{2^w}(\varphi) \;\not\Rightarrow\; \mathrm{unsat}_{\mathbb{Z}}(\varphi).
```

Witnesses, at `w = 16`: `x < 40000` is valid over the bounded domain and not over `ℤ`, and
`x > 40000` is unsatisfiable over the bounded domain and satisfiable over `ℤ`.

A `StaticVerdict` is therefore a statement **about the domain it was decided over**, and the type
carries that domain (`StaticVerdict::domain`) so a consumer cannot misread it by accident. A
verdict alone may **not** license an artifact change; §3.3 is how that is enforced.

The ground leg has no such caveat: it evaluates concretely on `i64`, so it is exact.

### 3.2 The ground leg

`ground_verdict_with` evaluates the formula under a `GuardAssignment` — a possibly *partial* map
from binder index to concrete value. Partiality is deliberate: at COMM time some binders may hold
a payload that is not scalar, and a guard mentioning one of those is undecidable by the scalar
legs. A missing binder yields `DontKnow`.

> **A defect this prevents.** `IntAssignment::get` defaults an out-of-range index to `0`. Reading
> an assignment through it without an explicit coverage check turns an *unbound* `x` in `x == 0`
> into a confident `Sat`. `GuardAssignment` requires coverage and answers `DontKnow` otherwise.

#### 3.2.1 ★ The connectives are left-strict, not Kleene

The connectives evaluate the **left** operand always and the **right** operand only when the left
did not settle the result. An undecided left operand therefore propagates as undecided even where
Kleene's strong three-valued tables would answer:

| formula | Kleene | here |
|---|---|---|
| `? ∨ ⊤` | `⊤` | `?` |
| `? ∧ ⊥` | `⊥` | `?` |
| `⊥ ∧ ?` | `⊥` | `⊥` |
| `⊤ ∨ ?` | `⊤` | `⊤` |
| `⊥ ⇒ ?` | `⊤` | `⊤` |

This is a **soundness** property, not a simplification. The reducer evaluates *both* operands of
`EAnd`/`EOr` unconditionally, and its guard check maps any evaluation error or non-boolean result
to `false`. A full-Kleene `∨` that answered `⊤` from the right operand alone would therefore fire
host-side while the reducer does not fire — unsoundness in the **firing** direction, which is the
unrecoverable one (§6.2).

The discipline constrains the formula *constructors* as well as the evaluator. The classical
absorptions `φ ∨ ⊤ = ⊤` and `φ ∧ ⊥ = ⊥` are valid and are **withheld**, because applying them at
construction time smuggles a decision past the discipline. Exactly three simplifications survive
on each side, and each is the discipline's own behaviour written out:

| kept | why it is safe |
|---|---|
| `⊤ ∧ φ = φ` | a decided-true left means "evaluate the right", which is `φ` |
| `⊥ ∧ φ = ⊥` | a decided-false left short-circuits, exactly as the discipline does |
| `φ ∧ ⊤ = φ` | evaluating `⊤` on the right returns the left's own verdict, unchanged |

and dually for `∨`. One constructor serves both legs, so the static leg pays a small
**completeness** cost: `Atom ∨ ⊤` is classically valid but reaches `static_verdict` with its
opaque atom intact and is answered `Undecided`. That is recorded rather than fixed, because the
obvious fix — simplifying classically before the static leg — would make *"statically valid"* stop
implying *"grounds to `Sat`"*, and that implication is what lets the two legs be reasoned about
together.

### 3.3 The fence

The compile-time consumer is `guard_discharge::classify`, whose only artifact-affecting outcome is
`Discharged`: the lowering declines to populate `Receive.condition`, and the reducer's
`check_commit` short-circuits a missing guard to `true`.

```text
  Discharged ⟸ substrate_verdict(⟦φ⟧) == Some(true)  ∧ machine_verdict(⟦φ⟧) == Some(true)
  Refuted    ⟸ substrate_verdict(⟦φ⟧) == Some(false) ∧ machine_verdict(⟦φ⟧) == Some(false)
  otherwise  ⟹ Residual                    (and a DISAGREEMENT emits a hard diagnostic)
```

The substrate is the **authority**: it is asked first, and a `None` from it is `Residual` whatever
any other leg says. `machine_verdict` is the **fence**, and it is required for *soundness* rather
than as a redundancy check: by §3.1.2 a bounded-domain verdict cannot on its own license omitting
a condition, and `machine_verdict` evaluates the very `Par` the artifact would carry, with `i64`
semantics, through the reducer's own evaluator. Requiring agreement makes the discharge set exactly
the intersection, which is sound by construction.

#### 3.3.1 What the fence costs, stated

The substrate's reach genuinely exceeds the fence's. It settles **open** guards — guards that
mention a binder — which `rho_pure_eval` cannot touch at all, because evaluating a condition with
free variables under the empty environment is unsound and the discharge path therefore requires
binder-closure:

| open guard | substrate |
|---|---|
| `x < x + 1` | `Valid` |
| `x == 1 and x == 2` | `Unsatisfiable` |

Neither is acted upon. An open guard has no concrete-semantics witness, so acting on it would be
exactly the unsound widening the fence exists to prevent; the verdict is emitted as a diagnostic
and the guard is left `Residual`. Widening the discharge set on the strength of a bounded-domain
verdict is a separate decision, and it needs either an unbounded decision procedure or a soundness
argument bridging the two domains.

## 4. Making the obligation exist

[07 §4.1](07-language-to-rholang-integration.md) induces the obligation set from the
`LanguageDef`. A term parameter is a semantic-predicate slot in two ways, and both induce the
same obligation id, `term:<Label>:guard:<param>`, with kind `BehavioralPredicate`:

| surface | recognized by |
|---|---|
| `?param:Guard` | its **type** — a `GuardBody` term parameter |
| `param:SomeCategory` plus `guards { guard_slots { Label(param); } }` | the author's **declaration** |

### 4.1 Why the typed slot alone is not enough

`?param:Guard` switches the parser into the predicate sublanguage, whose runtime predicate type
is `RelationQuery | Quantified | AcMatch | And | Or | Not | Implies | Top`, with arguments drawn
from `Var | IntLit | StringLit`. That grammar has **no comparison operators, no arithmetic, and no
nesting inside arguments**. For a language whose guard sublanguage *is* its own expression
language, retyping the slot is not a neutral change:

| Rholang `where` | as a behavioral predicate |
|---|---|
| `where x == 42` | only as a flat relation query |
| `where x + y < 10` | not expressible |
| `where t matches {P \| Q}` | not expressible |

Retyping would not make the guard a semantic predicate; it would delete most of the guard
language. The declaration states the same fact — *this parameter is a semantic predicate* —
without the loss, and the guard stays a full expression that the encoder maps into the substrate.

### 4.2 Declaration, never inference

Nothing in the collector reads the rule's syntax form. The literal `"where"` is not special (a
point [06 §1](06-guard-syntax-and-extensions.md) already makes about the typed slot), and no
parameter *name* is load-bearing. Recognition by spelling is the drift this tree forbids, and the
rule is stated in the code it governs: *"Recognition is by CONSTRUCTOR, never by spelling."*

### 4.3 The declaration survives into `LanguageDef`

This matters for two standing requirements — that backends need only the *specification* and not
the Rust macro front end, and that specifications are moving into Rholang as data. A guard
mechanism that lived only in the macro would have to be redesigned when specs move.

It does not. The measured round trip is
`definition_source() → reconstruct_language_def → LanguageDef`, and the obligations induced from
the reconstructed definition are exactly the declared ones
(`languages/tests/rholang_guard_slot_obligations.rs`, which reads the *generated* language value
rather than the macro input). The declaration is therefore spec-level data, as is the
`?name:Guard` slot itself (`TermParam::GuardBody`, in the `ast` crate).

### 4.4 Coverage evidence must be derived, not asserted

The obligation set is only half the story: the admission gate ([07 §5](07-language-to-rholang-integration.md))
requires a *disposition* for each obligation, and the caller supplies it. A caller that asserts
"this language induces no guard obligations" is making a claim about the language which becomes
false the moment the language declares a slot — and the gate then fails at a call site with no
local explanation.

`guard_quality::substrate_guard_coverage(def)` makes the evidence a function of the definition:
each induced obligation gets the substrate's own default disposition for its kind, which is
gate-compatible by construction. A language that induces no obligations yields an empty
collection, so the derived form subsumes the asserted one rather than replacing it.

> **Measured.** Declaring Rholang's two `where` slots while the four production planner sites
> still asserted "no obligations" broke every consumer of the production language registry — the
> flip gate failed coverage, and about eighty tests across five suites fell over at once. The
> derived form is what makes the declaration composable with the gate.

## 5. The structural leg is delegated, never re-implemented

`t matches {φ | ψ}` — the **separating conjunction** — has associative-commutative-with-remainder
semantics: the target must split into two disjoint parts satisfying `φ` and `ψ` respectively. That
is the reducer's matcher's question, and building a second one is exactly the divergence the guard
design exists to avoid.

The substrate therefore has **no procedure** for it, and this is structural rather than a
convention: a spatial fragment becomes an opaque `Atom`, `prattail` never sees a surface term, and
the only way an `Atom` is ever decided is through a resolver the caller supplies to
`ground_verdict_with`. The surface encoder's resolver hands the original fragment to the deciders
that already exist:

| atom kind | resolver |
|---|---|
| `Spatial` | the host `matches` verdict, which itself declines the separating conjunction and leaves it to the reducer |
| `StructuralEquality` | the existing exact collection comparator |
| `NonLinear`, `ProcessShaped`, `Uncovered` | none — fails closed |

**Static** discharge of a separating conjunction would require associative-commutative tree
automata — a theory extension, not wiring. The rule permits routing it to run time, and that is
what the wire does. At a guard site the target is ground by the time the guard is evaluated, so
the run-time case is concrete matching, which the existing matcher performs.

## 6. Consensus

### 6.1 The budget is a consensus parameter

`Sat3::DontKnow` is documented as *"undecided within the available budget / procedure"*. The
budget half is the hazard: a budget-dependent `DontKnow` that decided whether a COMM fires would
let two nodes with different budgets disagree about whether a COMM **happened** — a fork, not a
performance difference.

The resolution is to fix the budget network-wide (`CONSENSUS_SUBSTRATE_CONFIG`). That converts the
dangerous half into the benign one: with one budget, `DontKnow` is a deterministic function of the
guard, every node computes the same verdict, and COMM firing is deterministic.

Consequences, which are the point of naming it:

* It is **not per-node tunable.** A node that raises it to "decide more guards" changes which
  COMMs fire and forks itself off the network.
* Changing it is a **protocol change**: a guard that answered `DontKnow` under the old budget may
  answer `Sat` under a larger one, so a COMM that never fired starts firing.
* It is **not** a general analysis budget. Non-guard uses of the substrate — lints, offline
  analysis, tooling — are free to choose their own; only the guard path is bound to this one.

### 6.2 What a `DontKnow` means

With the budget fixed, the remaining question is semantic rather than safety-critical, and the
answer is that the guard does not pass. Two independent reasons:

* **It agrees with every decider already in the tree.** The host disposition's *declines* yields
  no rewrite, and the reducer's guard check maps error, non-boolean and `false` alike to "do not
  commit". Any other answer would put the substrate in disagreement with the reducer.
* **The failure modes are asymmetric.** A COMM that does not fire leaves a *resting, observable*
  continuation — it is in the normal form, in the state hash, and in storage, and a later step can
  still consume it. A COMM that fires wrongly consumes a datum and runs a continuation, and nothing
  undoes that.

### 6.3 The discharge consequence, unchanged

Discharging omits one condition evaluation per receive-eval, so a program's cost depends on the
compiler version that produced its artifact. This remains sound for consensus because the artifact
is fixed: every validator replays the same bytes and therefore charges the same amount. It is
recorded because it is an observable delta, not because it is a hazard.

## 7. Reconciliation with [08 — Runtime COMM Enforcement](08-runtime-comm-enforcement.md)

[08](08-runtime-comm-enforcement.md) states that the substrate is *classify-only* and that at run
time the surviving predicate is enforced by structural matching, a host boolean guard, or a native
join — *"the EBA/SFT is never re-evaluated"*. That description was accurate for the pre-wire
architecture and is now **partially superseded**:

| lane | who decides a residual guard at COMM time | status |
|---|---|---|
| the in-tree eager-COMM (fold) lane | **the substrate**, through the ground leg | changed by the wire |
| every **mettail** RSpace (`run`, `step`, `speculation`, the benches) | **the substrate**, through `SubstrateGuardMatcher::check_commit` | changed by the run-time leg |
| the **f1r3node consensus** lane (`runtime_manager`, `node/setup`, the REPL gRPC service) | f1r3node's `Matcher::check_commit`, i.e. `rho_pure_eval` | unchanged — see below |

> ⚠ **CORRECTED (2026-07-27).** This section previously read: *"The reducer lane is unchanged
> because the artifact is a `Par` and `rhoapi` has no node that names an external decision
> procedure … Bringing the reducer lane under the rule therefore requires either a host-side hook
> or a lowering that carries the guard to a native process, and both are protocol-level designs
> rather than wiring."*
>
> The premise is true — `rhoapi` still has no such node — and **the conclusion drawn from it was
> wrong.** The run-time leg shipped in `80b9d9f8` the day after this paragraph was last touched,
> and this section survived a relocation refactor (`25716a0a`) without being re-affirmed against
> it. The paragraph then generated a standing work item asserting the missing node *blocks* the
> run-time half. It does not.

**Why the wire has no role here.** The decision procedure is not named by the *term*; it is named
by the *runtime construction*. `check_commit` is a method on
`Arc<Box<dyn Match<BindPattern, ListParWithRandom, TaggedContinuation>>>`, which is a **parameter**
of `RSpace::create` / `create_with_replay`. Swapping deciders is three constructor arguments, and
this tree has already done it: `SubstrateGuardMatcher` (`rholang-runtime/src/guard_par_substrate.rs`)
delegates `get` to f1r3node's `Matcher` verbatim and overrides only `check_commit`, installed at
every mettail RSpace site — with **zero** f1r3node lines changed.

★ **And a wire field would be actively harmful, not merely unnecessary.** A node saying *"decide me
with procedure X"* makes the decider **deploy-author-selectable**, promoting a host-local
capability — which procedures a validator has, at which version, under which budget — into
consensus-visible bytes. Today the invariant is the opposite and is what makes replay sound:
`create_with_replay` takes **one** `Match` object and hands it to both the play and the replay
space, so play and replay structurally cannot disagree about who decided.

`rhoapi` already carries the cautionary precedent. `TaggedContinuation.scala_body_ref` *does* name
external procedures, and its vocabulary includes genuinely non-deterministic services, which the
reducer must special-case on replay (*"if the trace shows a failed non-deterministic process, we
cannot replay it"*). The only discipline that makes even that survivable is that the vocabulary is
**closed and host-defined**, reachable solely through `New.uri` — never by naming an arbitrary
procedure.

**What remains genuinely open is a different thing, correctly scoped.** f1r3node's three production
construction sites still hard-code `Matcher`, so the **consensus lane** is not yet under the
USER rule. That is a **decider swap at three call sites** — wire-compatible, no proto change, no
re-encoding of stored `Par`s — which is consensus-affecting (it changes which COMMs fire wherever
the two deciders disagree) and therefore needs validator agreement and an activation height. It is
not a protocol-format change, and conflating the two is what the superseded paragraph did.

Until that swap, the wire establishes the compile-time half of the rule in full on the consensus
lane: `guard_discharge::classify` discharges a guard only where the substrate **and** the machine
verdict agree, so a replayed artifact's omitted guards were called true by both. That is an
under-approximation of the rule, never an unsound one.

## 8. On GuardedRho

`languages/tests/definitions/guarded_rho.rs` is a **prototype** — the smallest language that proved the
`?guard:Guard` mechanism works — and not a reference implementation. Its fixed relation
vocabulary (`logic { relation halts(Proc); relation safe(Proc); }`) is the shape a spike takes,
not a design to generalize from: a *finite, declared* set of named relations cannot serve a guard
language that must be expressive, because the predicates a guard wants are not enumerable in
advance.

Nothing in this document derives from it. The wire is derived from the rule (§0) and from the
substrate's own structure (§2), and it neither preserves nor breaks the prototype: GuardedRho's
typed slot still induces its obligation, still parses through the predicate sublanguage, and is
used here only as the *comparison* that shows a declared slot and a typed slot induce the same
obligation shape (§4).

## 9. Evidence

| property | where it is checked |
|---|---|
| every guard form is decided by the wire; the symbolic shortfall is exactly `matches`, `/`, `%` | `languages/tests/rholang_guard_substrate_wire.rs` |
| the substrate-derived COMM decider agrees with the prior decider on the whole corpus | same file, the differential |
| the constructors withhold the classical absorptions | `prattail/src/guard_formula.rs`, unit tests |
| an unbound variable is `DontKnow`, never a default | same |
| a spatial atom is decidable only through the resolver | same |
| the consensus budget is fixed, and a different budget really does change verdicts | same |
| both `where` surfaces induce a `BehavioralPredicate` obligation, indistinguishable in shape from a typed slot's | `languages/tests/rholang_guard_slot_obligations.rs` |
| no undeclared rule induces a term-guard obligation | same |
| a static verdict carries the domain it was decided over | `prattail/src/guard_formula.rs`, unit tests |

## References

The decision procedures this wire dispatches to are specified and cited in
[02](02-effective-boolean-algebra.md)–[05](05-algebra-pyramid-and-decidability.md) and
[13](13-constraint-theory-engine.md); the consolidated bibliography is
[references.md](references.md). The three works the Presburger leg rests on directly:

- Büchi, J. R. (1960). "Weak second-order arithmetic and finite automata."
  *Zeitschrift für Mathematische Logik und Grundlagen der Mathematik*, 6(1–6), 66–92.
  [doi:10.1002/malq.19600060105](https://doi.org/10.1002/malq.19600060105) — Presburger-definable
  sets are exactly those recognizable by finite automata over positional encodings of integers,
  which is what makes the static leg an automata construction.
- Wolper, P., & Boigelot, B. (1995). "An automata-theoretic approach to Presburger arithmetic
  constraints." In *Static Analysis (SAS 1995)*, LNCS 983, 21–32.
  [doi:10.1007/3-540-60360-3_30](https://doi.org/10.1007/3-540-60360-3_30) — the automata
  representation used for Boolean combination and existential projection.
- Bartzis, C., & Bultan, T. (2003). "Efficient symbolic representations for arithmetic constraints
  in verification." *International Journal of Foundations of Computer Science*, 14(4), 605–624.
  [doi:10.1142/S0129054103001911](https://doi.org/10.1142/S0129054103001911) — the remainder-based
  construction whose state space is bounded by the coefficients, which is what keeps the static
  leg tractable on guard-sized formulas.
