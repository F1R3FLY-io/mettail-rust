# Language-to-Rholang Integration

Last updated: 2026-06-22

All symbols are defined in [Concepts and Glossary](01-concepts-and-glossary.md).
This document traces the end-to-end spine: how a guard declared in a `language!`
specification becomes a parsed predicate, a classified obligation, a disposition
with a quality grade, and finally a **fail-closed flip decision** that admits (or
refuses) the language on the Rho backend. The run-time enforcement of the surviving
guard is the subject of [08](08-runtime-comm-enforcement.md); this document stops
at the admission boundary.

The single most important architectural fact, stated up front and proven through
the rest of the document: **the symbolic-predicate substrate runs at compile time
and is classify-only.** It emits *evidence + a quality tag* per obligation. It does
**not** emit an EBA, SFA, or SFT structure into the generated Rholang.

![End-to-end: a language! guard becomes a fail-closed flip decision](figures/07-end-to-end-sequence.svg)

PlantUML source: [figures/07-end-to-end-sequence.puml](figures/07-end-to-end-sequence.puml).

## 1. The spine in one line

`guards{} / ?guard:Guard  →  GuardConfig / BehavioralPred (AST)  →  PredicateParser (prattail)  →  EBA/SFT/tree classification  →  obligation + disposition + quality  →  fail-closed flip gate  →  {lower | reject}`

Each arrow is an ownership boundary. The five sections below walk them in order.

## 2. Declaration — two surfaces in `language!`

A language author declares guards in two places, both parsed into the `ast` crate
(`mettail_ast`):

1. **The `?guard:Guard` term slot.** A grammar rule may carry a guard-body
   parameter, e.g. GuardedRho's
   `PGuardedInput . n:Name, ?guard:Guard, ^x.p:[Name → Proc] ⊢ "for" "(" x "<-" n "where" guard ")" "{" p "}" : Proc`.
   The `?guard:Guard` slot parses to `TermParam::GuardBody { name }`
   (`ast/src/grammar.rs`).
2. **The `guards { }` block.** A language-generic configuration parsed by
   `parse_guards` (`ast/src/language/parse.rs`) into `GuardConfig`
   (`ast/src/language/model.rs`), held at `LanguageDef.guard_config`. Its
   sub-blocks are:
   - `builtin_predicates` — the closed set of named predicates the guard
     sublanguage may use;
   - `connectives` — the keywords for the logical connectives (`ConnectiveDecl`);
   - `theories` — `TheoryRegistration`s naming a Rust type that implements
     `BooleanAlgebra`/`ConstraintTheory` plus the categories it handles;
   - `channels` — `channel <Cat>;` and `join <Label>(p: Cat);` declarations.

The predicate itself is the `BehavioralPred` AST (`ast/src/language/model.rs`):
`RelationQuery { relation_name, args, negated }`, `Quantified { quantifier, var,
domain, bound, body }`, `And`/`Or`/`Not`/`Implies`, the structural `AcMatch { bag,
elements, rest }`, and `Top`. It is carried as a rule premise
(`Premise::BehavioralGuard`) or rewrite condition (`Condition::BehavioralGuard`).

## 3. Compilation — into the prattail predicate sublanguage

The macro lowers the declared configuration into the prattail parser
specification. `lower_guard_config`
(`macros/src/gen/syntax/parser/prattail_bridge.rs`) turns each `?guard:Guard` slot
into a `SyntaxItemSpec::GuardExpression { param_name }`. At parse time the
generated prattail parser, on reaching a `GuardExpression` item, switches to the
**predicate sublanguage parser** (`PredicateParser`), which produces a runtime
`BehavioralPred` directly from the user's source tokens.

> **A correction worth stating, because the obvious file is the wrong one.**
> `macros/src/gen/runtime/guard_codegen.rs` is **vestigial**: its
> `generate_guard_codegen` emits only the `TriState` type, and the tier→codegen
> table in its module documentation is descriptive, not emitted. Behavioral
> predicates are *not* compiled into per-guard wrapper functions. The live compile
> path is `prattail_bridge.rs` → `PredicateParser`; the live *classification* path
> is `backend.rs` + `guard_quality.rs` (next sections). A reader tracing the
> integration should follow those, not `guard_codegen.rs`.

## 4. Classification — the substrate's "left half"

This is where the symbolic algebra of [02](02-effective-boolean-algebra.md)–[05](05-algebra-pyramid-and-decidability.md)
does its work, and where the classify-only boundary is enforced. The substrate
(`prattail/src/{symbolic,sft,sym_tree,algebra_tower,any_algebra,…}.rs`) takes the
parsed predicate and produces, for each guard obligation, an **evidence** that it
is covered by some effective theory and a **quality** grade for that evidence. It
emits no runtime structure.

> **`any-algebra-substrate.md §8`, made precise.** The substrate is the *left half*
> of the boundary with the Dovetail/Rho backend:
>
> ```
> language! → LanguageDef → guard obligations          [collect_guard_obligations — backend.rs]
>    → [SUBSTRATE]  EBA / SFT / tree / behavioral evidence  +  quality tag
>    → RhoGuardDisposition { kind, quality }              ──fills──▶ RhoGuardCoverageEvidence (fail-closed)
>    → [DOVETAIL] guarded rewrite rules + reports → [RHO] AST backend (rhoapi::Par)
> ```

### 4.1 Obligations

`collect_guard_obligations(def)` (`rholang-codegen/src/backend.rs`) walks the
`LanguageDef` and induces the exact obligation set, each tagged with a
`RhoGuardObligationKind`:

| Source in `language!` | Obligation id | `RhoGuardObligationKind` |
|---|---|---|
| `guards{}` builtins | `predicate:<name>` (or `predicate:standard-builtins`) | `BehavioralPredicate` |
| `theories{}` entry | `theory:<name>` | `TheoryRegistration` |
| `channels{}` / `join` | `channel:<Cat>` / `join:<Label>` | `RhoNativeJoin` |
| `?guard:Guard` slot | `term:<Label>:guard:<name>` | `BehavioralPredicate` |
| `BehavioralGuard` premise | `…:guard:<idx>` | `StructuralPattern` if it has an `AcMatch` component, else `BehavioralPredicate` |

The structural-vs-behavioral split is decided by `guard_pred_obligation_kind` via
`pred_has_structural_component` (an `AcMatch` component is structural; a `RelationQuery`/`Top`
is behavioral).

### 4.2 Dispositions and the compatibility matrix

A `RhoGuardDispositionKind` is the *mechanism* chosen to cover an obligation:

| Disposition | Covers | Realized by |
|---|---|---|
| `DovetailCoreStructural` | structural patterns | Dovetail exact-key / AC matching |
| `EffectiveBooleanAlgebra` | decidable value/theory predicates | an EBA instance ([02](02-effective-boolean-algebra.md)) |
| `SymbolicFiniteTransducer` | predicates needing input→output analysis | an SFT ([04](04-symbolic-transducers-sft-stft.md)) |
| `RhoNativeJoin` | channels, joins, external-relation behavioral guards | a host native join ([08](08-runtime-comm-enforcement.md)) |
| `NativeHandler` | host-specific computations | a native handler |
| `ExternalContract` | obligations met by an external contract | an out-of-band guarantee |

`guard_disposition_covers(obligation_kind, disposition_kind)`
(`rholang-codegen/src/backend.rs`) is the **compatibility matrix**: it answers
"may this disposition cover this obligation?" It is the falsifiable core of the
gate — an incompatible pairing is rejected.

![Obligation, disposition, quality, and the flip verdict](figures/07-disposition-decision.svg)

PlantUML source: [figures/07-disposition-decision.puml](figures/07-disposition-decision.puml).

### 4.3 Quality

Orthogonal to *which* mechanism covers an obligation is *how good* the evidence is.
`guard_quality.rs` derives a `RhoGuardQuality` — the 7-value vocabulary, ordered so
`Unknown` sorts highest (most restrictive):

| Quality | Meaning | Typical source |
|---|---|---|
| `ExactDecidable` | decided exactly | structural (Dovetail-core) or T1/T2 EBA |
| `BoundedDecidable` | decided up to a bound | T3 (bounded reachability) |
| `RejectSafeApprox` | reject-safe over-approximation | a behavioral leg (Heyting / `RejectSafeProduct`) |
| `TrustedNativeGuard` | trusted host computation | `NativeHandler` / `ExternalContract` / T4 |
| `MachineCheckedModel` | backed by a mechanized proof | a verified disposition |
| `RuntimeObservation` | observed at run time | `RhoNativeJoin` |
| `Unknown` | no evidence | nothing classified — **fail-closed** |

`classify_quality` applies the precedence *runtime-observed ▷ machine-checked ▷
reject-safe*, else the mechanism and tier drive the tag (T1/T2 → `ExactDecidable`,
T3 → `BoundedDecidable`, T4 → `TrustedNativeGuard`). `default_classification` gives
the conservative default per obligation kind: structural to Dovetail-core exact;
theory to EBA exact; **behavioral to EBA with `reject_safe`** (the Heyting leg —
sound: may reject, never wrongly admits); `RhoNativeJoin` → runtime-observed.
`derive_guard_qualities(def)` is the per-language entry point that emits a
`RhoGuardDispositionQuality` for every obligation. Only `Unknown` returns `true`
from `refuses_production_default`.

## 5. Admission — the fail-closed flip gate

This document's earlier sections define the three pipeline stages the gate consumes,
so the theorems below use only defined terms. To restate them compactly: an
**obligation** is a unit of guard work induced from the `LanguageDef` (§4.1, each
tagged with a `RhoGuardObligationKind`); a **disposition** is the mechanism chosen to
cover an obligation (§4.2, a `RhoGuardDispositionKind`), admissible only when the
compatibility matrix `guard_disposition_covers` permits the pairing; a **quality** is
the grade of the covering evidence (§4.3, a `RhoGuardQuality`, with `Unknown` the
fail-closed bottom). The gate is the conjunction that admits a language onto the Rho
backend exactly when its `obligation → disposition → quality` pipeline is fully and
soundly discharged.

A language adopts the Rho backend as its production default only when the planner
`plan_rho_default_backend` and the flip gate `decide_rho_flip`
(`rholang-codegen/src/flip.rs`) agree. The executable flip predicate is:

`Flip(L) = Coverage(L) ∧ ArtifactValidation(L) ∧ NoNewDeadlocks(L)`

- **Coverage** is `RhoGuardCoverageEvidence::exactly_covers`: every obligation has
  a compatible disposition, with no uncovered, extraneous, or invalid obligation.
- **Quality** folds in via `guard_quality_blockers_for`: any obligation whose
  quality `refuses_production_default()` (i.e. `Unknown`) yields a
  `RhoFlipBlocker::GuardQuality` and blocks the flip.
- **ArtifactValidation** and **NoNewDeadlocks** are the Rho-backend artifact and
  deadlock checks documented in
  [Rho-Native Integration](../rho-native-integration/04-rho-native-dataflow-lowering.md).

The gate is **fail-closed**: absent positive coverage evidence with non-`Unknown`
quality, the default backend selection refuses rather than falling through. This is
mechanized as `RhoBackendFlipGate.v` (which composes with `RhoGuardedCommSoundness.v`)
and surfaced in [10 — Formal Verification](10-formal-verification-and-tests.md).

This document is the **proof-home** of the flip gate. The results of §5.1–§5.2 are
stated and proved here as ordinary mathematical Theorems, each closed with `∎`; the
Coq objects that mechanize them are named only as parenthetical citations, so a reader
who never opens `RhoBackendFlipGate.v` can still follow every step. The run-time
soundness the gate licenses is §5.3.

### 5.1 The gate is the conjunction of three independent gates

Model the gate's three inputs as the Booleans `coverage_passed(g)`,
`artifact_validated(g)`, `no_new_deadlocks(g)` of a gate state `g`, and define the
flip decision as their conjunction `can_flip_to_rho(g) = coverage_passed(g) ∧ artifact_validated(g) ∧ no_new_deadlocks(g)`.

**Theorem 5.1 (the flip gate is the conjunction of three gates).** The flip decision
`can_flip_to_rho(g) = true` holds **iff** all three input gates pass — that is, iff
`coverage_passed(g) = true` and `artifact_validated(g) = true` and `no_new_deadlocks(g) = true`.

*Proof.* Write the gate as `b₁ ∧ b₂ ∧ b₃` with `b₁ = coverage_passed(g)`,
`b₂ = artifact_validated(g)`, `b₃ = no_new_deadlocks(g)`. Boolean conjunction over `{true, false}` satisfies `b ∧ c = true ⟺ (b = true ∧ c = true)` (the truth table of `∧`: the meet is `true` exactly when both arguments are `true`). Apply this equivalence to the outer conjunction `(b₁ ∧ b₂) ∧ b₃` to split off `b₃`, then again to the inner `b₁ ∧ b₂` to split `b₁` from `b₂`. The two applications give `(b₁ ∧ b₂) ∧ b₃ = true ⟺ b₁ = true ∧ b₂ = true ∧ b₃ = true`, which is the claim. `∎` (Mechanized as `can_flip_iff_all_gates`; the two splits are two rewrites by `andb_true_iff`.)

**Theorem 5.2 (each gate is necessary).** If any one of `coverage_passed(g)`,
`artifact_validated(g)`, `no_new_deadlocks(g)` is `false`, then `can_flip_to_rho(g) = false`.

*Proof.* A `false` factor short-circuits the conjunction: for Booleans,
`false ∧ c = false`, `b ∧ false = false`, and these compose, so any `false` argument
of `b₁ ∧ b₂ ∧ b₃` forces the whole expression to `false` regardless of the other two.
Taking each factor `false` in turn discharges the three cases. `∎` (Mechanized as the
three theorems `missing_coverage_blocks_flip`, `missing_artifact_validation_blocks_flip`,
and `missing_deadlock_gate_blocks_flip`, one per failing input.) Theorem 5.1 already
yields this as its contrapositive; the three named witnesses make the per-gate
necessity individually citable, which is what the gate's `RhoFlipBlocker` reporting
needs.

The contrapositive reading of Theorems 5.1–5.2 is the architectural claim: **no single
green light admits the flip** — coverage without a validated artifact, or a validated
artifact with a fresh deadlock, each leaves the gate `false`. The gate is therefore a
true `AND`, not a weighted score with a passing threshold.

### 5.2 Unknown quality is fail-closed

The quality axis of §4.3 enters the gate as an additional, additive family of
blockers. Let `qs` be the covered obligations paired with their qualities; the planner
derives one `RhoFlipBlocker::GuardQuality` per obligation whose quality
`refuses_production_default()`, and only `Unknown` does so (§4.3). Write
`can_flip_with_qualities(g, qs)` for the full gate: the Boolean gate of §5.1 **and**
the absence of any quality blocker, i.e. `can_flip_with_qualities(g, qs) = can_flip_to_rho(g) ∧ (blocker-count(qs) = 0)`, where `blocker-count(qs)` is the number of obligations in `qs` whose quality refuses the production default.

**Theorem 5.3 (Unknown quality is fail-closed).** If any covered guard obligation in
`qs` carries quality `Unknown`, the flip is blocked: `can_flip_with_qualities(g, qs) = false`.

*Proof.* Suppose some obligation `q ∈ qs` has quality `Unknown`. Because exactly
`Unknown` satisfies `refuses_production_default` (§4.3), `q` is counted by
`blocker-count`, so `blocker-count(qs) ≥ 1`, hence `blocker-count(qs) ≠ 0` and the
conjunct `(blocker-count(qs) = 0)` is `false`. The full gate is the conjunction
`can_flip_to_rho(g) ∧ (blocker-count(qs) = 0)`; a `false` second conjunct zeroes the
whole conjunction (`b ∧ false = false`, Theorem 5.2's short-circuit) independently of
the Boolean gate `can_flip_to_rho(g)`. Therefore `can_flip_with_qualities(g, qs) = false`. `∎` (Mechanized as `unknown_guard_quality_blocks_flip`, resting on
`refuses_production_default_iff_unknown` — that only `Unknown` refuses — and
`unknown_quality_contributes_blocker` — that an `Unknown` obligation makes the blocker
count non-zero.)

This is the precise content of "**fail-closed**": an obligation the substrate could
not classify (quality `Unknown` — *no evidence*, §4.3) is not silently admitted; it
is converted into a hard blocker. The complementary positive fact — that a gate with
no quality blocker is licensed exactly when the Boolean gate passes — is mechanized as
`can_flip_with_qualities_iff`, and the genuinely-gated nature of the licensing (an
`Unknown` obligation denies it outright) as `unknown_guard_quality_denies_licensing`.

### 5.3 What the gate licenses: a sound guarded COMM

Passing the gate is the compile-time *permission* to lower the surviving guard to a
run-time enforcement mechanism (§5's closing note; the mechanisms themselves are
[08](08-runtime-comm-enforcement.md)). The soundness of that run-time step is the
companion result, mechanized in `RhoGuardedCommSoundness.v` and proved here for the
firing factorization and the soundness of the product evaluation; the asymmetric
reject-safety it pairs with is cross-referenced to its proof-home rather than
re-proved.

Model a guarded receive by a substitution `s` carrying the match. Three Booleans
decide on it: `name_match(s)` (the channel names unify), `structural_eval(s)` (the
classical structural leg, decided exactly), and `behavioral_eval(s)` (the reject-safe
behavioral leg — a *sound under-approximation* of the true behavioral property
`behavioral_true(s)`, so `behavioral_eval(s) = true ⟹ behavioral_true(s) = true`, the
Heyting/`Sat3::DontKnow` boundary of [12](12-heyting-behavioral-logic.md)). The
**product guard's run-time evaluation** is `product_eval(s) = structural_eval(s) ∧ behavioral_eval(s)`, the **true product property** is `product_true(s) = structural_eval(s) ∧ behavioral_true(s)`, and a guarded COMM **fires** iff `comm_fires(s) = name_match(s) ∧ product_eval(s)`.

**Theorem 5.4 (a guarded COMM fires iff names match and the product guard holds).**
For every `s`, `comm_fires(s) = true` **iff** `name_match(s) = true` and `product_eval(s) = true`.

*Proof.* By definition `comm_fires(s) = name_match(s) ∧ product_eval(s)`. Boolean
conjunction satisfies `b ∧ c = true ⟺ (b = true ∧ c = true)`; applied to the two
factors `name_match(s)` and `product_eval(s)` this is exactly the claim. `∎`
(Mechanized as `comm_fires_iff`, a single application of `andb_true_iff`.)

**Theorem 5.5 (the run-time product evaluation is sound).** For every `s`,
`product_eval(s) = true ⟹ product_true(s) = true`: a firing product guard soundly
certifies the true product property.

*Proof.* Assume `product_eval(s) = true`, i.e. `structural_eval(s) ∧ behavioral_eval(s) = true`. By `b ∧ c = true ⟺ (b = true ∧ c = true)`, both `structural_eval(s) = true` and `behavioral_eval(s) = true`. The structural leg is **exact**, so its contribution to `product_true(s)` is the same `structural_eval(s) = true`. The behavioral leg is **reject-safe**, the soundness hypothesis `behavioral_eval(s) = true ⟹ behavioral_true(s) = true`; from `behavioral_eval(s) = true` it gives `behavioral_true(s) = true`. Hence both conjuncts of `product_true(s) = structural_eval(s) ∧ behavioral_true(s)` are `true`, so `product_true(s) = true`. `∎` (Mechanized as `product_eval_sound`; the behavioral step discharges the `behavioral_sound` hypothesis of `RhoGuardedCommSoundness.v`. Soundness is one-directional: the converse can fail, because the reject-safe leg may report `false` on a state where `behavioral_true` holds — it never wrongly admits, only conservatively rejects.)

Theorems 5.4 and 5.5 compose into the firing-soundness statement *a fired COMM
satisfies the true guard* (`name_match(s) ∧ product_true(s)`, mechanized as
`comm_fires_implies_true_guard`): unfold the firing equivalence (Theorem 5.4), then
upgrade the product evaluation to the true property (Theorem 5.5). The asymmetric
counterpart — that the **complement** guard `¬(structural ∧ behavioral)`, lowered in
its padded double-`⊤` De Morgan form, never fires on a satisfiable product (so a
`DontKnow` can never commit a COMM) — is **Theorem 6.1 of [12 — Heyting Algebras for
Behavioral Constraints](12-heyting-behavioral-logic.md#6-how-heyting-completes-boolean-for-structural-behavioral-types)**;
its run-time mirror is `RhoGuardedCommSoundness.v`'s `mixed_negation_soundness` and
`rho_complement_no_commit`. We cross-reference it rather than restate its proof.

Finally, the two halves join: a flip-eligible (`Unknown`-free, Boolean-passing) plan
*licenses* the production-default lowering, and exactly under that license the
firing-soundness of Theorem 5.5 applies — mechanized as `licensed_flip_is_guard_sound`,
which consumes the flip-eligibility premise via `can_flip_with_qualities_iff` and then
instantiates `comm_fires_implies_true_guard`. The gate and the guard are sound
together: the gate admits no un-evidenced guard, and an admitted guard never fires a
COMM it does not truly satisfy.

> **Lowering target follows the disposition.** Once a language passes the gate, the
> *surviving* guard is lowered to one of three run-time enforcement mechanisms
> depending on its disposition — RSpace structural matching, a host `where`
> boolean guard, or a host-routed native join. The choice and its run-time
> semantics are [08 — Runtime COMM Enforcement](08-runtime-comm-enforcement.md);
> the funding axis it composes with is
> [09 — Funding Composition](09-funding-composition.md).

## 6. The comprehension contract

Every page of this suite preserves the same left-to-right story, and this document
is its spine:

`predicate over language data → effective Boolean algebra element → decided + classified at compile time → fail-closed coverage evidence → host enforcement of the survivor`

If a page mentions an EBA, SFA, SFT, or the tower, it is *before* the coverage
boundary — compile-time classification. If a page mentions RSpace, `where`, COMM,
or `RhoNativeJoin`, it is *after* the boundary — host run-time enforcement. The two
never cross: **the substrate classifies; the host enforces.**
