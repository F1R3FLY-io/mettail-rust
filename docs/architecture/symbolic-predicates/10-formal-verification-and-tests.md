# Formal Verification and Tests

Last updated: 2026-06-22

All symbols are defined in [Concepts and Glossary](01-concepts-and-glossary.md).
This document is the **evidence ledger** for the semantic-predicate substrate. It
answers the reviewer's question — *which claim is checked by which artifact, and
how strong is that artifact?* — by laying out three concrete evidence layers, a
mechanized-proof matrix keyed to the actual Rocq theory files, the zero-admission
gate that keeps those proofs honest, the runtime tests that exercise the live host
behavior, and the exact capped build commands a reviewer runs to reproduce every
green check.

Nothing here is aspirational: every theorem name in the matrices below was read
out of the `.v` source, and every build target below exists in `formal/Makefile`.

## 1. The three evidence layers

The substrate's correctness rests on three independent kinds of evidence, each
answering a different question and each reproducible by a single command.

| Layer | Artifact kind | Question it answers | Strength | Reproduce with |
|---|---|---|---|---|
| **Mechanized proofs** | Rocq theories in `formal/rocq/` and `dovetail/formal/rocq/` | "Is the *algebra* sound — do the Boolean laws, closure, composition, functionality, and bridge soundness hold for *all* inputs?" | machine-checked over arbitrary inputs, **zero-admission** | `make -C formal check-capped FORMAL_CAPPED_TARGET=<target>` |
| **Runtime tests** | Rust integration tests in `rholang-runtime/tests/` and `languages/tests/` | "Does the *live host* behave as the proofs require — does a failed guard rest its data, and does a real guarded language plan end-to-end with usable quality?" | concrete executions against f1r3node's `RhoRuntime` and the real codegen path | `cargo test -p <crate> --test <name>` |
| **Zero-admission gate** | `formal/scripts/check_rocq_zero_admission.py` | "Are the proofs *complete* — no `Axiom`, `Conjecture`, `Parameter`, `Admitted.`, or `admit.` hiding a hole?" | a syntactic scanner with its own `--self-test`, run on the four critical trees | `make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-critical-zero-admission` |

The layers are **complementary, not redundant**. A proof shows the algebra is
sound for every input but says nothing about whether f1r3node actually rests a
guard-failing datum; the runtime oracle shows exactly that but only for the
sampled programs. The zero-admission gate is the meta-check that the first layer
contains no escape hatch. A claim is "covered" only when the algebra is proven,
the gate passes, and — where the claim is about run-time enforcement — the oracle
agrees.

> **Two Rocq trees.** The proofs live in *two* workspaces. The substrate's own
> algebra/transducer/bridge proofs are under the workspace tree
> `formal/rocq/` (subtrees `symbolic_algebra/`, `sft/`, `presburger/`,
> `predicate_dispatch/`, `rho_bridge/`). The Dovetail saturation/extraction
> proofs are under the companion tree `dovetail/formal/rocq/theories/`. Both are
> in the zero-admission gate's `DEFAULT_ROOTS`; this document covers the
> substrate tree in detail and references the Dovetail tree where the bridge
> proofs depend on it.

## 2. Mechanized-proof matrix

Each row pairs a substrate claim with the `.v` file that mechanizes it, the
key theorem name(s) you can grep for, and the capped build target that compiles
it. Names are exact (read from source). Rows are grouped by theory tree.

### 2.1 `symbolic_algebra` — target `rocq-symbolic-algebra`

Directory: `formal/rocq/symbolic_algebra/theories/`.

| Claim | File | Key theorem(s) / record(s) | Target |
|---|---|---|---|
| An EBA satisfies the Boolean laws *up to denotation* — `≈ 28` derived identities (commutativity, associativity, idempotence, absorption, distributivity, `a ∧ ¬a ≈ ⊥`, `a ∨ ¬a ≈ ⊤`, double-negation, De Morgan), plus the decision-procedure correctness of `implies`/`is_tautology`/`overlaps`/`equivalent`. | `EffectiveBooleanAlgebra.v` | records `EBA`, `EBA_Laws`, `RejectSafeLaws`; `conj_comm`, `disj_comm`, `conj_assoc`, `absorb_conj_disj`, `excluded_middle`, `non_contradiction`, `double_neg`, `de_morgan_conj`, `de_morgan_disj`, `implies_correct`, `tautology_correct`, `overlaps_correct`, `equivalent_correct` | `rocq-symbolic-algebra` |
| The reject-safe tier is the strict weakening of the EBA: every classical EBA is reject-safe (drops `sat_complete` and the involutive `eval_neg`). | `EffectiveBooleanAlgebra.v` | `eba_implies_reject_safe` | `rocq-symbolic-algebra` |
| EBAs are **closed under independent-domain product**; complement is De Morgan over a DNF of rectangles. | `ProductAlgebraClosure.v` | `product_eba_laws` (via `pdnf_neg_eval`, `pdnf_sat_sound`/`pdnf_sat_complete`, `pdnf_wit_sound`/`pdnf_wit_total`) | `rocq-symbolic-algebra` |
| EBAs are **closed under disjoint sum**; the left/right projections are exact. | `SumAlgebraClosure.v` | `sum_eba_laws`; `project_L_correct`, `project_R_correct` | `rocq-symbolic-algebra` |
| The **collection (bag) algebra** over occupancy minterms is an EBA with exact satisfiability and witness. | `CollectionAlgebraClosure.v` | `collection_eba_laws`; `csat_sound`/`csat_complete`, `cwit_sound`/`cwit_total` | `rocq-symbolic-algebra` |
| The **ranked-tree constructor closure** is an EBA; emptiness is decidable by a bounded-chain saturation that provably stabilizes. | `TreeAlgebraClosure.v` | `tree_eba` (record `DFTA`; `teval_tconj`/`teval_tdisj`/`teval_tneg`; `Fstep_mono`/`Fstep_bounded`/`present_closed`; `stabilizes`) | `rocq-symbolic-algebra` |
| Two decidable theories **combine** via a joint search — the Nelson-Oppen base case — yielding an EBA with sound/complete satisfiability. | `TheoryCombination.v` | `combined_eba_laws`; `csat_sound`/`csat_complete`, `cwit_sound`/`cwit_total` | `rocq-symbolic-algebra` |
| The Heyting tier models behavioral negation: triple-negation collapse `¬¬¬a = ¬a`, `¬¬a = ⊥ ⇒ a = ⊥`, the regular-element subalgebra, and `¬¬a = a` *only on regulars*. | `HeytingAlgebra.v` | `dneg_idempotent`, `dneg_eq_bot_implies_bot`, `regular_meet`, `excluded_middle_reg`, `neg_involutive_on_regular` | `rocq-symbolic-algebra` |
| The decidability-tier lattice is a **join-semilattice** that is a **homomorphism under theory combination**, and tier maps to regularity. | `GuardTierCertificate.v` | `tier_le` (total order: `tier_le_refl`/`tier_le_antisym`/`tier_le_trans`/`tier_le_total`); `tier_max_comm`/`tier_max_idem`/`tier_max_assoc`/`tier_max_ub_l`/`tier_max_ub_r`/`tier_max_least`; `tier_max_sound_hom`/`tier_max_complete_hom`/`tier_max_exact`; `tier_regularity_reg`/`tier_regularity_boundary`/`tier_regularity_closed` | `rocq-symbolic-algebra` |
| The **mixed structural `×` behavioral complement is a reject-safe over-approximation** that never fires falsely; the concrete 3-valued model proves classical complement is genuinely unavailable there. | `BehavioralNegation.v` | `mixed_negation_soundness`, `mixed_guard_no_false_fire`, `weak_dneg`; module `TriModel`: `tri_neg_sound`, `excluded_middle_fails`, `no_classical_complement` | `rocq-symbolic-algebra` |

### 2.2 `sft` — target `rocq-sft`

Directory: `formal/rocq/sft/theories/`.

| Claim | File | Key theorem(s) | Target |
|---|---|---|---|
| The transducer **output term** forms a monoid (under `Concat`) and a category (under `then`), so composition is an exact algebraic operation rather than an opaque closure. | `OutputTermAlgebra.v` | `oconcat_assoc`, `oconcat_eps_l`, `oconcat_eps_r`; `othen_correct` (the β-law), `othen_id_l`, `othen_id_r`, `othen_assoc`, `othen_eps_l` | `rocq-sft` |
| SFT **composition** has left/right identities and is associative. | `SftComposition.v` | `sft_compose_left_identity`, `sft_compose_right_identity`, `sft_compose_assoc` | `rocq-sft` |
| SFT **functionality** (single-valuedness) is preserved by composition and characterized by per-input output length `≤ 1`. | `SftFunctionality.v` | `identity_functional`, `constant_functional`, `epsilon_functional`, `compose_preserves_functional`, `domain_characterization`, `functional_iff_all_le1` | `rocq-sft` |
| The **tree-transducer** relabeling homomorphism composes associatively and counts are preserved by fusion. | `StftComposition.v` | `thom_id`, `thom_fusion`, `thom_compose_assoc`, `tcount_thom`; `ft_compose_left_identity`/`ft_compose_right_identity`/`ft_compose_assoc` | `rocq-sft` |
| Tree-transducer **functionality** is preserved by composition and the relabeling preserves the tree node count. | `StftFunctionality.v` | `identity_functional`, `compose_preserves_functional`, `thom_preserves_tcount`, `functional_output_le1` | `rocq-sft` |

### 2.3 `presburger` — target `rocq-presburger`

Directory: `formal/rocq/presburger/theories/`.

| Claim | File | Key theorem(s) | Target |
|---|---|---|---|
| Presburger-NFA-definable integer sets are a **Boolean algebra** (commutativity, De Morgan, double-negation) realized by NFA intersection/union/complement — automata-theoretic, not SMT. | `PresburgerBooleanAlgebra.v` | `and_comm`, `or_comm`, `de_morgan_and`, `de_morgan_or`, `double_negation`, `nfa_intersect_correct`, `nfa_union_correct`, `nfa_complement_correct` | `rocq-presburger` |

The integer decision procedure is the binary-encoded remainder NFA of
[Büchi, 1960](references.md#buchi-1960) and
[Bartzis & Bultan, 2003](references.md#bartzis-bultan-2003); see
[02 §5](02-effective-boolean-algebra.md) for why automata rather than a solver.

### 2.4 `predicate_dispatch` — target `rocq-predicate-dispatch`

Directory: `formal/rocq/predicate_dispatch/theories/`.

| Claim | File | Key theorem(s) | Target |
|---|---|---|---|
| The predicate-feature dispatch is **complete** (every nonzero signature is accepted), **never rejects a covered feature set**, and its signature union is a commutative/associative/idempotent monoid (the `∨` of guard feature-sets). | `DispatchCompleteness.v` | `dispatch_completeness`, `dispatch_zero_rejected`, `sig_union_comm`, `sig_union_assoc`, `sig_union_idempotent`; supporting `base_invariant_m1`/`base_invariant_m10`, `extract_features_always_accepted` | `rocq-predicate-dispatch` |

### 2.5 `rho_bridge` — algebra-to-COMM soundness, target `rocq-rho-bridge`

Directory: `formal/rocq/rho_bridge/theories/`. These are the bridges that carry
the algebra's verdict across the classify-only boundary to a live COMM, and
compose it with OSLF funding and the fail-closed flip gate.

| Claim | File | Key theorem(s) | Target |
|---|---|---|---|
| A guarded COMM **fires iff the product guard is satisfied**; the product evaluation is sound; a complemented guard never commits and a true guard does — the run-time reflection of `mixed_negation_soundness`. | `RhoGuardedCommSoundness.v` | `comm_fires_iff`, `product_eval_sound`, `comm_fires_implies_true_guard`, `mixed_negation_soundness`, `rho_complement_no_commit`, `rho_guard_true_commits` | `rocq-rho-bridge` |
| Guard **atomicity at the host boundary**: a failed guard consumes nothing and emits nothing, a missing premise never commits, no output is fabricated, and a true enabled guard adds exactly its output. | `GuardedCommSoundness.v` | `failed_guard_no_commit`, `missing_premise_no_commit`, `guarded_attempt_no_fabrication`, `true_guard_enabled_adds_output` | `rocq-rho-bridge` |
| The Rho backend's **flip gate is fail-closed**: a language becomes a production default iff `coverage ∧ artifact-validation ∧ no-new-deadlocks` all hold, and any `Unknown`-quality obligation blocks it. | `RhoBackendFlipGate.v` | `can_flip_iff_all_gates`, `default_backend_gate_iff_all_requirements`, `refuses_production_default_iff_unknown`, `unknown_guard_quality_blocks_flip`, `licensed_flip_is_guard_sound` | `rocq-rho-bridge` |
| OSLF funding obeys the **four resource laws** (sound, reject-underfunded, supply-monotone, decidable) and the capstone identifies the resource logic as OSLF-sound — the second axis of the guarded-COMM verdict (08). | `MettaOslfLawsConformance.v` | `law_sound`, `law_reject_underfunded`, `law_supply_monotone`, `law_decidable`, `metta_resource_logic_is_oslf_sound` | `rocq-rho-bridge` |
| The GSLT presentation of a language's decompositions is **sound, complete, and characterizing** — Dovetail's saturation is its reduction relation. | `MettaGsltPresentation.v` | `decompositions_sound`, `decompositions_complete`, `decompositions_characterization` | `rocq-rho-bridge` |

> **How the bridges compose.** `RhoGuardedCommSoundness.comm_fires_iff` is the
> logic axis (`guard-satisfied`); `MettaOslfLawsConformance.law_sound` is the
> resource axis (`funded`); the run-time verdict
> `COMM fires ⟺ guard-satisfied ∧ funded` is exactly the two-axis composition
> documented in [09 — OSLF Composition](09-oslf-composition.md).
> `RhoBackendFlipGate` then
> guarantees no language reaches a live COMM at all unless every obligation is
> covered with non-`Unknown` quality.

## 3. The zero-admission gate

> ## ⚠ Callout — `Sat3` and `Esakia` are **not** Coq objects
>
> The three-valued/Esakia-trichotomy story is implemented in **Rust**, not Rocq.
> `Sat3` is a Rust enum (`prattail/src/algebra_tower.rs`), and there is no
> `Sat3` or `Esakia` lemma in any `.v` file. When you need the mechanized basis
> for "behavioral negation is genuinely non-classical / three-valued," cite these
> instead:
>
> | Story you want to support | Cite (Coq) |
> |---|---|
> | "Excluded middle genuinely fails; there is no classical complement here." | `BehavioralNegation.v` — `excluded_middle_fails`, `no_classical_complement`, `tri_neg_sound` |
> | "Classical reasoning is sound only on the *regular* sublattice." | `HeytingAlgebra.v` — `neg_involutive_on_regular`, `excluded_middle_reg`, `regular_meet` |
> | "Tier ↔ regularity boundary is exactly the structural/behavioral split." | `GuardTierCertificate.v` — `tier_regularity_reg`, `tier_regularity_boundary`, `tier_regularity_closed` |
>
> Do **not** attribute a Rocq lemma to `Sat3` or to an "Esakia" theorem — those
> are the Rust tower's vocabulary (see the glossary entry for `Sat3`), validated
> by the Rust tests, while the *proof* that the behavior they encode is sound is
> carried by the three files above.

A mechanized proof is only as strong as its weakest unproven leg, so a green
`Qed` is necessary but not sufficient — a file could still smuggle a hole through
`Axiom`, `Conjecture`, `Parameter`, an `Admitted.` theorem, or an `admit.`
tactic. The gate `formal/scripts/check_rocq_zero_admission.py` rules those out
syntactically:

1. It **strips nested comments** first (so a banned token inside an explanatory
   `(* … *)` comment is *not* a false positive), handling the nested-comment
   grammar of Rocq.
2. It then bans, on live source lines: `Axiom`, `Conjecture`, `Parameter`/
   `Parameters` (allowing the usual `Local`/`Global`/`Polymorphic`/`Monomorphic`
   modifiers), a bare `Admitted.`, and the `admit.` tactic (guarded so it does
   not trip on identifiers that merely *contain* the substring, e.g. an
   `admit_force` definition).
3. It carries a `--self-test` that asserts a clean fixture passes and that an
   `Axiom`/`Conjecture`/`Parameter`/`Admitted.`/`admit.` fixture each fails — so
   the scanner's own correctness is checked before it scans the repository.

Its `DEFAULT_ROOTS` are the **four critical trees**:

```text
dovetail/formal/rocq/theories
formal/rocq/rho_bridge/theories
formal/rocq/symbolic_algebra/theories
formal/rocq/sft/theories
```

Every tree in the matrices of §2.1, §2.2, and §2.5 is inside `DEFAULT_ROOTS`
and passes the gate with exit `0`; the substrate ships with no `Admitted.` and
no `Axiom` in those trees. The aggregate target runs the self-test, then the
scanner:

```text
rocq-critical-zero-admission:
    python3 scripts/check_rocq_zero_admission.py --self-test
    python3 scripts/check_rocq_zero_admission.py
```

The `presburger` and `predicate_dispatch` trees are compiled and `Qed`-checked
by their own targets (§2.3, §2.4); the four-tree `DEFAULT_ROOTS` set is the
*critical-path* gate that blocks a release on any admission in the algebra,
transducer, bridge, or Dovetail proofs.

## 4. Runtime-test matrix

The proofs say a failed guard must not commit and a covered language must plan;
these tests check that the **live host and the real codegen path** actually do
so. There are two anchors.

| Test file | What it exercises | The proof it operationalizes | Key cases |
|---|---|---|---|
| `rholang-runtime/tests/rho_guard_oracle.rs` | Real Rholang `where`-guard receives run through f1r3node's host `RhoRuntime`, observing both the output channel and the data channel. | `GuardedCommSoundness.v` — `failed_guard_no_commit`, `true_guard_enabled_adds_output` | `false_single_bind_guard_leaves_data_and_emits_no_output` (a `where x > 0` guard on `@"c"!(-3)` emits nothing and leaves `-3` resting); `guard_filters_multiple_messages_without_consuming_failed_candidate` (later `7` fires, earlier `-1` stays); `false_cross_bind_guard_leaves_all_join_inputs` and `cross_bind_guard_can_commit_later_without_consuming_failed_pair` (the join analog: `x + y > 10` rests both inputs, then a later satisfying pair commits while the earlier failing datum remains) |
| `languages/tests/guarded_rho_rho_backend.rs` | End-to-end Rho-default backend **planning** for the real `GuardedRho` language under the live `guard_quality` wiring, reconstructing the augmented `LanguageDef` from `definition_source()` exactly as the production installer does. | `RhoBackendFlipGate.v` — `refuses_production_default_iff_unknown`, `unknown_guard_quality_blocks_flip`, `default_backend_gate_iff_all_requirements` | `guarded_rho_induces_guard_obligations_with_non_unknown_qualities` (its channel/join/`?guard` slots induce `RhoNativeJoin` + behavioral obligations, every derived quality non-`Unknown`, behavioral legs land on `RejectSafeApprox`); `guarded_rho_plans_end_to_end_with_all_qualities_non_unknown` (without coverage the audit blocks; with exact rejected-rule + four guard dispositions it plans, carrying `RuntimeObservation` for the two join surfaces and `RejectSafeApprox` for the two predicate legs — never `Unknown`) |

The oracle proves the *atomicity* clause of the algebra-to-COMM bridge on real
f1r3node executions: a failed `where`-guard is observationally a no-op on the
tuple space (the rejected datum is still readable), and a strictly later
satisfying datum still commits — precisely the "rest, then commit" guarantee the
glossary's **guard atomicity** entry names. The planning test proves the
*fail-closed* clause end-to-end: the gate is genuinely engaged (it blocks without
coverage) and a fully-covered real guarded language passes it with every
substrate quality usable, so `RhoFlipBlocker::GuardQuality` never fires for a
legitimately covered language.

Run them with:

```text
cargo test -p mettail-rholang-runtime --test rho_guard_oracle
cargo test -p mettail-languages --test guarded_rho_rho_backend --features guarded-rho,rho-codegen
```

## 5. Canonical capped build commands

All formal targets run under a **32 GiB RSS hard cap** via `systemd-run`
(`FORMAL_MEMORY_MAX_BYTES = 34359738368` bytes); `formal/Makefile` *refuses* an
uncapped or direct target so a runaway proof can never destabilize the machine.
Invoke each target through `check-capped`, selecting it with
`FORMAL_CAPPED_TARGET`:

```text
# Substrate algebra: EBA laws, closure family, Heyting, tier lattice, behavioral negation
make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-symbolic-algebra

# Symbolic transducers: SFT/STFT composition + functionality + output-term algebra
make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-sft

# Presburger integer Boolean algebra (NFA intersection/union/complement)
make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-presburger

# Predicate-feature dispatch completeness + signature-union monoid
make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-predicate-dispatch

# Algebra-to-COMM bridges: guarded-COMM soundness, flip gate, OSLF laws, GSLT
make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-rho-bridge

# The zero-admission gate over the four critical trees (self-test, then scan)
make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-critical-zero-admission
```

Each command runs `make -j1` inside the capped scope (`-j1` for the
memory-intensive modular proofs, per the project's resource-limiting discipline)
and exits `0` on success. A reviewer reproducing the whole substrate ledger runs
the five proof targets plus the gate; a CI run gates the release on
`rocq-critical-zero-admission` together with the per-tree targets.

## 6. References cross-link

- The EBA definition and the automata-not-SMT decision procedure:
  [02 — Effective Boolean Algebra](02-effective-boolean-algebra.md);
  [D'Antoni & Veanes, 2017](references.md#dantoni-veanes-2017).
- The integer decision procedure's NFA encoding:
  [Büchi, 1960](references.md#buchi-1960);
  [Bartzis & Bultan, 2003](references.md#bartzis-bultan-2003).
- The algebra tower, reject-safety, Heyting regulars, and the `Sat3` Rust enum
  the §3 callout warns about:
  [05 — Algebra Pyramid and Decidability](05-algebra-pyramid-and-decidability.md);
  the glossary entries for `Sat3`, `RejectSafeAlgebra`, `HeytingAlgebra`, and
  **Regular element** in [01 — Concepts and Glossary](01-concepts-and-glossary.md).
- The classify-only boundary the runtime tests sit downstream of, and the
  `where`-guard / `RhoNativeJoin` enforcement mechanisms:
  [08 — Runtime COMM Enforcement](08-runtime-comm-enforcement.md).
- The two-axis `guard-satisfied ∧ funded` composition the `rho_bridge` proofs
  mechanize: [09 — OSLF Composition](09-oslf-composition.md);
  [Stay & Meredith, 2016](references.md#stay-meredith-2016).
- Where each documentation requirement is satisfied:
  [00 — Requirements Traceability](00-requirements-traceability.md).
- The full bibliography, source-file index, and proof catalog:
  [References](references.md).
