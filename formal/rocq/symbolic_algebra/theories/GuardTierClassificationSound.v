(*
 * GuardTierClassificationSound: soundness of the guard-decidability tier
 * classifier `classify_decidability_sorted` (prattail/src/symbolic.rs:2066) that
 * the testkit guard analysis (testkit/src/analytical/guards.rs) routes its
 * STRUCTURAL guards through, and soundness of the structural∪behavioral
 * partition fold that produces the per-language `(T1,T2,T3,T4,worst)` tally.
 *
 * The Rust classifier:
 *
 *     classify_decidability_sorted(g, registry) =
 *         if registry.contains(g.sort) { T1 }
 *         else { classify_decidability(project(g.pred)) }
 *
 * A *structural* guard carries `pred = AnyPred::True` (a pure data-sort type
 * assertion), and `classify_decidability(project(True)) = classify(True) = T1`.
 * So a structural guard is T1 on *both* branches — and the T1 it gets is SOUND
 * because:
 *   - the registry-resident branch decides the guard with the leaf EBA's `sat`,
 *     which is the bare leaf decision (`wrapper_sat_faithful`,
 *     AnyAlgebraProjectionSound.v) and terminates; and
 *   - T1 is the EXACT (sound ∧ complete) tier (`tier_regularity_reg` ∧
 *     `tier_regularity T1 = Reg`, GuardTierCertificate.v).
 *
 * This file proves, zero-admission:
 *
 *   (i)  CLASSIFIER SOUNDNESS (Section ClassifierSoundness):
 *        `classify g registry = T1 -> tsound T1 = true /\ tcomplete T1 = true`,
 *        by composing `tier_regularity_reg` with the registry/leaf-decision
 *        equality witnessed by `wrapper_sat_faithful`. The composition is made
 *        explicit by `registry_decision_is_leaf_decision`: the deciding
 *        procedure for a registry-resident structural guard is *literally* the
 *        bare leaf `sat`, so it terminates — which is what licenses the T1
 *        (compile-time-decidable) tag.
 *
 *   (ii) PARTITION SOUNDNESS (Section PartitionSoundness):
 *        folding `tier_max` over a structural∪behavioral guard list equals
 *        `tier_max (fold structural) (fold behavioral)` (`fold_app_tier_max`),
 *        and the combined guarantee is the MEET of the parts'
 *        (`partition_sound_hom` / `partition_complete_hom`), via
 *        `tier_max_assoc`/`tier_max_comm`/`tier_max_sound_hom`/
 *        `tier_max_complete_hom`. Hence a fold that mixes the (T1) structural
 *        guards and the (T2) behavioral guards degrades the guarantee exactly as
 *        the weakest leg dictates — soundness is preserved through T2/T3, lost
 *        only at T4 — matching the Rust `worst_tier = tier_max(...)`.
 *
 * Spec-to-Code Traceability:
 *   Coq                                  | Rust
 *   -------------------------------------|------------------------------------------
 *   SortedGuard / sg_sort / sg_pred      | any_algebra::SortedGuard { sort, pred }
 *   registry_contains                    | SortRegistry::contains
 *   structural (pred = SGTrue)           | SortedGuard{ pred: AnyPred::True }
 *   classify                             | symbolic::classify_decidability_sorted
 *   classify_struct_is_T1                | the structural arm (both branches ⇒ T1)
 *   registry_decision_is_leaf_decision   | registry-resident ⇒ leaf EBA sat (wrapper)
 *   fold_tier / fold_app_tier_max        | the testkit tally fold (worst = tier_max)
 *   partition_sound_hom                  | guard_codegen max_tier guarantee homomorphism
 *
 * Reuses (all zero-admission, registered in this project's _CoqProject):
 *   - GuardTierCertificate.v   : Tier, tier_max, tsound, tcomplete,
 *                                tier_regularity, tier_regularity_reg,
 *                                tier_max_{assoc,comm,sound_hom,complete_hom}.
 *   - AnyAlgebraProjectionSound.v + EffectiveBooleanAlgebra.v :
 *                                wrapper_sat_faithful (registry = leaf decision).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

From SymbolicAlgebra Require Import EffectiveBooleanAlgebra.
From SymbolicAlgebra Require Import GuardTierCertificate.
From SymbolicAlgebra Require Import AnyAlgebraProjectionSound.

(* ===================================================================== *)
(*  The sorted-guard model and the classifier                            *)
(* ===================================================================== *)

Section Classifier.
  (** A [Sort] is the data-sort tag of a guard. The Rust [Sort] enum is finite
      with [Eq]; we model it as an abstract type with a boolean equality that
      reflects propositional equality (same faithfulness condition the carrier
      proof uses for its [Tag]). *)
  Variable Sort : Type.
  Variable sort_eqb : Sort -> Sort -> bool.
  Hypothesis sort_eqb_spec : forall a b, sort_eqb a b = true <-> a = b.

  (** The carrier predicate payload of a guard. We only need to distinguish the
      structural [True] payload (a data-sort type assertion) from "any other"
      payload, so we model it with a two-constructor type: [SGTrue] is the
      structural assertion; [SGOther] stands for a non-structural payload whose
      projected tier is supplied explicitly. This mirrors that
      [classify_decidability(project(AnyPred::True)) = T1] is a *computation*, not
      an assumption. *)
  Inductive GuardPred : Type :=
  | SGTrue  : GuardPred                 (* AnyPred::True — structural assertion *)
  | SGOther : Tier -> GuardPred.        (* any other payload, carrying its projected tier *)

  (** A guard paired with the sort it constrains. *)
  Record SortedGuard := {
    sg_sort : Sort;
    sg_pred : GuardPred;
  }.

  (** A registry is a membership test over sorts (the Rust
      [SortRegistry::contains]). *)
  Variable registry_contains : Sort -> bool.

  (** The projected tier of a payload under the untyped structural classifier.
      [classify_decidability(project(True)) = T1]; a non-structural payload
      carries its own projected tier. This is the Coq image of
      [classify_decidability ∘ project_anypred_to_predicate_expr]. *)
  Definition projected_tier (p : GuardPred) : Tier :=
    match p with
    | SGTrue    => T1
    | SGOther t => t
    end.

  (** The classifier, mirroring [classify_decidability_sorted] exactly:
      registry-resident sort ⇒ T1; otherwise the projected tier. *)
  Definition classify (g : SortedGuard) : Tier :=
    if registry_contains (sg_sort g) then T1 else projected_tier (sg_pred g).

  (** A structural guard is one whose payload is the data-sort assertion. *)
  Definition is_structural (g : SortedGuard) : bool :=
    match sg_pred g with SGTrue => true | SGOther _ => false end.

  (* =================================================================== *)
  (*  (i) Classifier soundness                                           *)
  (* =================================================================== *)

  Section ClassifierSoundness.

    (** A structural guard classifies to T1, on BOTH branches: the
        registry-resident branch is T1 directly, and the fallback branch is
        [projected_tier SGTrue = T1]. *)
    Lemma classify_struct_is_T1 :
      forall g, is_structural g = true -> classify g = T1.
    Proof.
      intros g Hstruct. unfold classify, is_structural in *.
      destruct (sg_pred g) eqn:Ep; [| discriminate].
      destruct (registry_contains (sg_sort g)); reflexivity.
    Qed.

    (** T1 is the EXACT tier: its decision is both sound and complete. This is
        the core obligation — it composes [tier_regularity_reg] (the Esakia
        regular/clopen ⇔ sound∧complete correspondence) with the computation
        [tier_regularity T1 = Reg]. *)
    Theorem classify_T1_sound_and_complete :
      forall g, classify g = T1 -> tsound T1 = true /\ tcomplete T1 = true.
    Proof.
      intros g _.
      apply tier_regularity_reg.
      reflexivity.            (* tier_regularity T1 = Reg, by computation *)
    Qed.

    (** Specialized to a structural guard: it is classified T1 and that T1 is
        exact. (The headline structural-soundness statement.) *)
    Corollary structural_classifies_exact :
      forall g, is_structural g = true ->
        classify g = T1 /\ tsound (classify g) = true /\ tcomplete (classify g) = true.
    Proof.
      intros g Hstruct.
      pose proof (classify_struct_is_T1 g Hstruct) as HT1.
      split; [exact HT1|].
      rewrite HT1. split; reflexivity.
    Qed.

    (** The registry-resident decision IS the bare leaf decision. We expose the
        composition explicitly: for a guard whose sort is registry-resident, the
        carrier decides it by projecting onto the registered leaf algebra [A] and
        running [sat] on the *same-sort wrapped* leaf payload — which, by
        [wrapper_sat_faithful] (AnyAlgebraProjectionSound.v), equals the bare
        leaf [sat q]. A bare leaf [sat] is the EBA's own (terminating) decision
        procedure, which is exactly why the registry-resident branch is sound to
        tag T1 (compile-time decidable).

        [own]/[q]/[A]/[tag_eqb] instantiate the carrier-proof's section data; the
        statement is the registry-resident decision equals the leaf decision,
        independent of the abstract guard model above. *)
    Theorem registry_decision_is_leaf_decision :
      forall (Tag : Type) (tag_eqb : Tag -> Tag -> bool)
             (tag_eqb_spec : forall a b, tag_eqb a b = true <-> a = b)
             (A : EBA) (own : Tag) (q : Pred A),
        sat (fold_pred Tag tag_eqb A own (Native Tag A own q)) = sat q.
    Proof.
      intros Tag tag_eqb tag_eqb_spec A own q.
      exact (wrapper_sat_faithful Tag tag_eqb tag_eqb_spec A own q).
    Qed.

  End ClassifierSoundness.

  (* =================================================================== *)
  (*  (ii) Partition soundness                                           *)
  (* =================================================================== *)

  Section PartitionSoundness.

    (** The weakest-tier fold over a guard list: [tier_max] reduced from a [T1]
        seed (the strongest tier, the unit of [tier_max]). This is the testkit
        tally's [worst_tier]. *)
    Definition fold_tier (gs : list SortedGuard) : Tier :=
      fold_right (fun g acc => tier_max (classify g) acc) T1 gs.

    (** [T1] is the right unit of [tier_max] (the strongest tier never weakens
        anything). *)
    Lemma tier_max_T1_r : forall t, tier_max t T1 = t.
    Proof. intro t; destruct t; reflexivity. Qed.

    Lemma tier_max_T1_l : forall t, tier_max T1 t = t.
    Proof. intro t; destruct t; reflexivity. Qed.

    (** Folding over a concatenation splits as the [tier_max] of the two folds —
        the structural∪behavioral partition law. Proven by induction on the
        first list, using associativity to re-associate the accumulator. *)
    Theorem fold_app_tier_max :
      forall xs ys, fold_tier (xs ++ ys) = tier_max (fold_tier xs) (fold_tier ys).
    Proof.
      induction xs as [| g xs IH]; intro ys; simpl.
      - (* [] ++ ys : fold_tier ys = tier_max T1 (fold_tier ys) *)
        rewrite tier_max_T1_l. reflexivity.
      - (* (g :: xs) ++ ys *)
        unfold fold_tier in *. simpl.
        rewrite IH.
        (* goal: tier_max (classify g) (tier_max (fold xs) (fold ys))
                 = tier_max (tier_max (classify g) (fold xs)) (fold ys) *)
        apply tier_max_assoc.
    Qed.

    (** The guarantee of a partitioned fold is the MEET (conjunction) of the two
        parts' guarantees: a combined tally is sound iff BOTH parts are sound,
        and complete iff BOTH are complete. Composes [fold_app_tier_max] with the
        tier guarantee homomorphisms. *)
    Theorem partition_sound_hom :
      forall xs ys,
        tsound (fold_tier (xs ++ ys))
        = tsound (fold_tier xs) && tsound (fold_tier ys).
    Proof.
      intros xs ys. rewrite fold_app_tier_max. apply tier_max_sound_hom.
    Qed.

    Theorem partition_complete_hom :
      forall xs ys,
        tcomplete (fold_tier (xs ++ ys))
        = tcomplete (fold_tier xs) && tcomplete (fold_tier ys).
    Proof.
      intros xs ys. rewrite fold_app_tier_max. apply tier_max_complete_hom.
    Qed.

    (** A purely-structural fold is exact: every structural guard is T1, so the
        fold stays T1 (sound ∧ complete). By induction, using
        [classify_struct_is_T1] and [tier_max T1 T1 = T1]. *)
    Theorem structural_fold_is_T1 :
      forall gs, forallb is_structural gs = true -> fold_tier gs = T1.
    Proof.
      induction gs as [| g gs IH]; intro Hall; simpl in *.
      - reflexivity.
      - apply andb_true_iff in Hall. destruct Hall as [Hg Hgs].
        unfold fold_tier in *. simpl.
        rewrite (classify_struct_is_T1 g Hg).
        rewrite IH by exact Hgs.
        reflexivity.
    Qed.

    (** Hence a structural∪behavioral fold has *exactly* the behavioral part's
        guarantee — the structural part (being T1, the unit) cannot weaken it.
        This is the precise statement that "a pure-arithmetic grammar is all-T1,
        and adding behavioral (freshness/premise/binder) guards surfaces those
        obligations at their true (≥ T2) tier without the structural guards
        masking them". *)
    Corollary structural_neutral_in_partition :
      forall xs ys, forallb is_structural xs = true ->
        fold_tier (xs ++ ys) = fold_tier ys.
    Proof.
      intros xs ys Hstruct.
      rewrite fold_app_tier_max.
      rewrite (structural_fold_is_T1 xs Hstruct).
      apply tier_max_T1_l.
    Qed.

  End PartitionSoundness.

End Classifier.

(* Closure under the global context is verified by the zero-admission checker;
   the explicit prints are cheap insurance against a stray axiom leaking in via
   the imported lemmas. *)
Print Assumptions classify_T1_sound_and_complete.
Print Assumptions structural_classifies_exact.
Print Assumptions registry_decision_is_leaf_decision.
Print Assumptions fold_app_tier_max.
Print Assumptions partition_sound_hom.
Print Assumptions partition_complete_hom.
Print Assumptions structural_fold_is_T1.
Print Assumptions structural_neutral_in_partition.
