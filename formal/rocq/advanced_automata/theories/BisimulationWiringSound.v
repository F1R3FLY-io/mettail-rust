(*
 * BisimulationWiringSound: soundness of WIRING the partition-refinement
 * bisimulation (prattail/src/bisimulation.rs::Lts) into the analysis layer
 * (OSLF Phase 4 wiring lemma).
 *
 * The Rust `Lts::bisimulation` computes a partition by signature refinement and
 * `Lts::is_bisimulation` CERTIFIES the result (the runtime `assert` in
 * `bisimulation::analyze_from_bundle`). This file proves that certificate is
 * SOUND for its live use — category dedup / N06-ISO merge: a certified
 * partition relates ONLY genuinely-bisimilar states, so merging same-block
 * categories never identifies behaviorally-distinct ones.
 *
 * Reuses the shipped M8.2 proof `RegisterEquivalence.v` (the exact
 * `is_bisimulation` / `bisimilar` definitions the Rust `Lts::is_bisimulation`
 * mirrors). For a single transition system the two transition relations of
 * `is_bisimulation`/`bisimilar` coincide (`trans trans`).
 *
 * Theorems:
 *   - certified_partition_relates_only_bisimilar : a relation certified a
 *       bisimulation is contained in bisimilarity — so two states the certified
 *       partition relates are genuinely bisimilar (merging them is sound).
 *   - bisimilar_refl : every state is bisimilar to itself (the partition
 *       diagonal is always a valid merge — identity is a bisimulation).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From AdvancedAutomata Require Import RegisterEquivalence.

(* The wiring soundness: the Rust `Lts::is_bisimulation` certificate (asserted in
   `analyze_from_bundle`) guarantees that every pair the returned partition
   relates is bisimilar — so deduping / merging same-block categories (N06-ISO)
   never conflates behaviorally-distinct ones. Immediate from the definition of
   `bisimilar` (an existential over bisimulations), witnessed by R itself. *)
Theorem certified_partition_relates_only_bisimilar :
  forall (R : ConfigRel) (trans : TransRel) (c1 c2 : Config),
    is_bisimulation R trans trans ->
    R c1 c2 ->
    bisimilar trans trans c1 c2.
Proof.
  intros R trans c1 c2 Hbis Hr.
  exists R. split; [exact Hbis | exact Hr].
Qed.

(* The partition diagonal is always sound: a state is bisimilar to itself, since
   the identity relation is a bisimulation. So a block never wrongly excludes
   reflexivity, and self-merge is always valid. *)
Theorem bisimilar_refl :
  forall (trans : TransRel) (c : Config), bisimilar trans trans c c.
Proof.
  intros trans c. exists (@eq Config). split.
  - unfold is_bisimulation. split.
    + intros c1 c2 a c' Heq Ht. subst c2. exists c'. split.
      * exact Ht.
      * reflexivity.
    + intros c1 c2 a c' Heq Ht. subst c2. exists c'. split.
      * exact Ht.
      * reflexivity.
  - reflexivity.
Qed.

Print Assumptions certified_partition_relates_only_bisimilar.
Print Assumptions bisimilar_refl.
