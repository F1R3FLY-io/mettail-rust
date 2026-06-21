# Concepts and Glossary

This page defines Dovetail terms before they appear in formulas or algorithms.

## Core Terms

| Term | Definition |
|---|---|
| MeTTaIL | A language modeling system that defines syntax and rewrite semantics for object languages. |
| `language!` | The MeTTaIL specification macro that declares categories, constructors, syntax, rewrites, native hooks, and metadata for a modeled language. |
| Dovetail | The standalone MeTTaIL rewrite engine crate at `dovetail/`. |
| rewrite rule | A `RewriteRule<L>` data value: a left-hand `Pattern`, a right-hand `Pattern`, and an optional `label`. It has **no** guard or evidence field — a rule that reaches saturation is unconditional (see *guard*). |
| guard | A predicate that conditions a language's rewrite. Guards are **discharged upstream** of Dovetail (in `rholang-codegen`): a structural guard is folded into the LHS pattern shape, a behavioral guard routes the rule to the host (`RhoNativeJoin`) or a native handler, and an unclassifiable guard fails the flip closed. Dovetail's rule data therefore carries no guard to evaluate; the law `guard(σ)=false ⇒ no derived fact` is realized by *not lowering* the rule, not by an inline predicate call. |
| disposition | The upstream classification of a rejected/guarded rule into how it is covered: `NativeHandler` (native fold), `RhoNativeJoin`/`RhoAstContract` (host RSpace), `DovetailCoreStructural` (e-graph congruence), in-engine `AcStructuralApply` (AC rewrite), or `ExternalContract` (evidence outside the generated contract). The flip gate is fail-closed: an `Unknown` disposition leaves a language un-flipped. |
| AC (associative-commutative) operator | An operator whose children form an unordered multiset and nest flatly — parallel composition `\|`, a bag collection. `op⟦P,Q⟧ ≡ op⟦Q,P⟧` (commutative) and `op⟦P, op⟦Q,R⟧⟧ ≡ op⟦P,Q,R⟧` (associative). |
| op-bag | An e-node whose label is an AC operator; its children are the multiset members. |
| sub-multiset selection | A size-`k` multiset `s⋆ ⊆ b⋆` chosen from an op-bag `b⋆`; enumerated lazily by `lazy_ac_select` (one `k`-combination at a time, never all `C(m,k)` at once). |
| rest complement | In `AcApp{op, fixed, rest}`, the multiset `b⋆ ⊖ s⋆` of unselected children; `rest` binds to a **fresh canonical** op-node over it (the only e-graph mutation AC matching makes, budget-gated). |
| associative flattening | On instantiation, splicing any op-bag member into its parent op-bag so a result is one flat bag, not a bag-of-bags (`add_flattened_bag`). |
| binder | A constructor that introduces a bound name with lexical scope — Ambient's `new(x, P)` binds `x` in `P`. Represented with the `moniker` crate's `Scope`/`Binder`/`FreeVar`. |
| de-Bruijn index | A nameless representation of a bound variable as the count of binders between its use and its binder, making α-equivalent terms *identical* (de Bruijn 1972). The binder-congruence handler keys on de-Bruijn body shape. |
| α-equivalence | Equality up to consistent renaming of bound names: `new(x, x[0]) ≈α new(y, y[0])`. |
| capture-avoidance | Renaming a bound name so it cannot be accidentally captured when a term moves under another binder; realized here by `moniker` `unbind` (which freshens the bound name) before re-closing with `Scope::new`. |
| freshness `x # t` | "`x` does not occur free in `t`" (Pitts' nominal-logic relation): the side condition under which a binder may float past a term. |
| NativeHandler | A disposition (and the Ambient binder mechanism): a deterministic, capture-safe in-Rust transform — here, float `new`s outward then AC-reduce — installed as a language's `try_direct_eval`. |
| binder-congruence handler | Ambient's `NativeHandler`: floats every `new` to the top (capture-safe), leaving a binder-free soup the AC rules reduce. Documented in [Binder-Congruence Handler](11-binder-congruence-handler.md). |
| fold rule | A term-constructor rule (`eval_mode = Fold`) whose RHS is a *native-computed* Rust body `![{ … }]` run on its reduced children, not a `Pattern → Pattern` rewrite — e.g. RhoCalc `int(a,w):Proc`, Calculator `concat(a,b):List`. A **non-native-output** fold returns an object/collection category (`Proc`/`List`/`Map`/`Bag`); these reduced nowhere after the Ascent retirement (the *cast-eval gap*). Documented in [Native-Fold Reduction](12-native-fold-reduction.md). |
| typed op-enum `L` | The generated per-language `<Lang>DovetailOp` the e-graph carries on the fold path: one variant per `(category, constructor)` with literal/var payloads **inline** (lossless, so reconstruction is total), replacing the lossy `EGraph<String>` `{:?}` leaves. Its `SemanticHash` frames a discriminant then `Eq`-agreeing payload bytes (Map/Bag via sorted `Display`). |
| native-computed rewrite | A rewrite whose RHS is computed by a trusted Rust function — a `NativeRule<L>` + a `NativeOpId` tag run by the one compiled-in **dispatcher** `Fn(NativeOpId, &mut EGraph<L>, &Subst) → Option<EClassId>`. Folds lower to these and reduce inside `saturate_with_native`. |
| fold-readiness guard | The three-way classifier the dispatcher applies to a fold's child class: a **value op** fires, a **fold-redex op** defers (the child must fold first), and a **`Var`** defers. Realized by `class_is_fold_value` (a no-extraction e-node scan); it is what makes a fold sound under unordered saturation (no spurious `Err` from firing on an unfolded child). |
| `NativeFoldLowered` | The generated-rule disposition for a native fold (the fourth, beside `LoweredAsDovetailRule` / `SuppliedByEGraphCongruence` / `RejectedByGeneratedCompiler`): its single requirement is the exact content key `ReqExactContentKey` (the computed result is added through the exact-key path). |
| predicated type | A type-like language constraint expressed as a guard over values or patterns. Dovetail consumes predicated types as guarded rules and coverage obligations from generated inventory. |
| structural predicated type | A guard whose truth is determined by constructor shape, exact keys, binding layout, AC decomposition, or other pattern structure. |
| behavioral predicated type | A guard whose truth depends on a relation, theory, host operation, channel compatibility, or other behavior beyond immediate shape. |
| equality saturation | Iterative growth of an equality graph until no new equalities are found or a bound stops the run. |
| e-graph | A graph of equivalence classes and expression nodes. |
| e-class | An equivalence class of terms, identified by `EClassId`. |
| e-node | A labeled operator with zero or more child e-classes. |
| congruence closure | The rule that if children are equal, parent expressions with the same operator are equal. |
| exact key | A byte-stream identity where equality is byte equality, represented by `ContentKey`. |
| semantic hash | Dovetail's name for exact content serialization; despite the name, it is not a finite hash. |
| weight | A semiring value used to order derivations. |
| semiring | Algebra with `⊕`, `⊗`, `0̄`, and `1̄`. |
| weighted tree automaton | A tree automaton whose transitions carry weights. |
| effective Boolean algebra | A decidable Boolean algebra over a predicate domain; it is external evidence for behavioral guard analysis, not a Dovetail extraction weight. |
| symbolic finite-state transducer | A symbolic transducer used to prove guard-preserving transformations, pre-images, post-images, or normalizations. |
| WFST | Weighted finite-state transducer; useful for weighted language/transduction analyses and selectivity evidence, distinct from Dovetail's weighted tree automaton extraction model. |
| DFTA | Deterministic finite tree automaton; Dovetail views e-classes as states and e-nodes as transitions. |
| inside weight | The aggregate weight of all derivations rooted at an e-class. |
| SCC | Strongly connected component in the e-class dependency graph. |
| extraction | Enumeration of derivation trees from an e-class. |
| derivation | A chosen e-node plus one derivation for each child e-class. |
| report | A typed, proof-preserving artifact that carries checked facts across a Dovetail phase boundary. |
| `SatReport` | The saturation report carrying terminal outcome and statistics. |
| `Extraction<T>` | The extraction report envelope carrying a value and terminal completeness. |
| `DovetailRunReport` | The runtime-facing report built from checked extraction output. |
| report consumer | An adapter or oracle that reads a report without depending on Dovetail internals. |
| term record | A unique derivation node recorded once in a report under its exact `ContentKey`. |
| derivation edge | A report edge from parent key to child key, preserving child order and repeated child uses. |
| cycle cut | A recursion guard that prevents infinite enumeration through a back-edge. |
| completeness | Terminal metadata saying whether extracted output is exhaustive or bounded by a cycle cut. |
| tuple-space seam | Generic `TupleSpace` and `Match` traits used to model rendezvous without depending on RSpace. |

## Report Terms

Dovetail uses "report" in the API-contract sense, not the prose-document
sense. A report is a typed handoff artifact that another subsystem may consume
without depending on Dovetail's internal e-graph and extractor structures.

| Artifact | Boundary | Main obligation |
|---|---|---|
| `SatReport` | saturation | inspect `Converged`, `NodeLimit`, or `IterationLimit` before claiming saturation success |
| `Extraction<T>` | extraction | preserve the extracted value and the terminal `Complete` or `BoundedByCycleCut` status together |
| `DovetailRunReport` | runtime/tool handoff | preserve exact root keys, term records, ordered derivation edges, and completeness |
| runtime observation | backend execution | keep it separate from Dovetail reports because it is produced after a backend consumes an artifact |

A Dovetail report is therefore closer to a small certificate than to a log:

`report = semantic payload + exact identity + boundary status`

The common source of confusion is treating a report as an evaluator's final
display value. In Dovetail, the display value is a possible downstream
presentation. The report is the checked handoff object that says which exact
rewrite alternatives exist, how they are supported, and whether the finite
handoff is exhaustive.

The word does not introduce a separate reporting subsystem. It names values
that already sit on Dovetail's critical execution path:

`saturate → SatReport`

`extract → Extraction<T>`

`report_from_extraction → DovetailRunReport`

Those values exist because a rewrite engine has to preserve more than one
pretty-printed answer. It must also preserve exact identity, ambiguity,
derivation support, ordering, budget status, and cyclic boundedness.

The detailed contract is
[Runtime-Facing Reports](10-runtime-facing-reports.md).

## Symbols

| Symbol | Meaning |
|---|---|
| `q` | An e-class, treated as a WTA state. |
| `n` | An e-node, treated as a WTA transition. |
| `children(n)` | Ordered child e-classes of e-node `n`. |
| `weight(n)` | Local semiring weight of e-node `n`. |
| `inside(q)` | Aggregate weight for all derivations rooted at e-class `q`. |
| `⊕` | Semiring addition, used to aggregate alternatives. |
| `⊗` | Semiring multiplication, used to compose a parent with child weights. |
| `0̄` | Semiring zero; Dovetail treats composed `0̄` derivations as refuted. |
| `1̄` | Semiring one; identity for composition. |
| `key(x)` | Exact content key of value `x`. |
| `D(q)` | Set of derivations rooted at e-class `q`. |
| `σ` | A substitution `variableName ↦ EClassId` (a match's bindings). |
| `b⋆` | A multiset (bag) of e-class children, e.g. `⟦c₁, c₂, c₂⟧` — duplicates count, order does not. |
| `s⋆ ⊆ b⋆` | `s⋆` is a sub-multiset of `b⋆`. |
| `⊎`, `⊖` | Multiset union and difference. |
| `x # t` | Freshness: name `x` does not occur free in term `t`. |
| `≈α` | α-equivalence (equality up to renaming of bound names). |
| `λ`-free / de-Bruijn body | A binder's body with bound names replaced by de-Bruijn indices, so α-equivalent bodies are byte-identical. |

The WTA recurrence is:

`inside(q) = ⊕_{n ∈ nodes(q)} weight(n) ⊗ ⊗_{c ∈ children(n)} inside(c)`

The derivation completeness contract is:

`Complete(q) ⇒ emitted(q) = { d ∈ D(q) | weight(d) ≠ 0̄ }`

The bounded cyclic contract is:

`BoundedByCycleCut(q) ⇒ emitted(q) ⊆ { d ∈ D(q) | weight(d) ≠ 0̄ }`

The report completeness contract is:

`ReportComplete(r) ⇔ completeness(r) = Complete`

## Naming Boundaries

| Name | Boundary |
|---|---|
| `language!` | Source-of-truth language declarations and generated semantic inventory. |
| Dovetail | Rewrite semantics and extraction. |
| Rho backend | Lowering and execution bridge from Dovetail semantics to RhoRuntime. |
| Rho machine | Host process-calculus runtime in F1r3node/Rholang. |
| Ascent | Legacy generated Datalog rewrite backend and oracle path. |
| WPDA | Active parser/recognizer architecture upstream of Dovetail. |

## Safety Terms

`unsafe trait SemanticHash` is unsafe because implementors must uphold a
semantic contract that Rust cannot check:

`write_content(x) = write_content(y) ⇔ x ≈ y`

Here `x ≈ y` means observational equality for the value being serialized. If an
implementation violates this, exact-key deduplication can become unsound.
