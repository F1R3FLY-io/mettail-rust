(*
 * BehavioralNegation: soundness of the ASYMMETRIC De Morgan negation in a mixed
 * structural × behavioral product guard, and the failure of excluded middle on
 * the behavioral leg.
 *
 * The unified guard is `ProductAlgebra<S : BooleanAlgebra, B : RejectSafeAlgebra>`
 * (symbolic.rs): the structural leg S has CLASSICAL (two-valued, involutive)
 * negation, the behavioral leg B has only REJECT-SAFE negation — a SOUND
 * under-approximation of the classical complement, never complete (the
 * Sat3::DontKnow boundary). De Morgan over such a product is asymmetric:
 *   ¬(ps ∧ pb) = (¬ps ∧ ⊤) ∨ (⊤ ∧ ¬pb)
 * with ¬ps classical and ¬pb reject-safe. This file proves, zero-admission:
 *
 *   - `mixed_negation_soundness` : the mixed complement is a reject-safe
 *     over-approximation of the true complement — whenever it accepts, the
 *     product genuinely REJECTS. Hence a guarded receive built from it never
 *     wrongly *admits* (fires) a Comm — the load-bearing safety property
 *     (`RhoGuardedCommSoundness`, GuardedCommSoundness).
 *   - `weak_dneg` : the reject-safe leg gives only weak double negation.
 *   - `excluded_middle_fails` (concrete Tri model) : there is a reject-safe
 *     algebra and a predicate p with neither p nor ¬p satisfied — so the
 *     behavioral leg is genuinely non-classical (the DontKnow region is
 *     inhabited), confirming it must implement HeytingAlgebra, never classical
 *     BooleanAlgebra. The model also discharges the abstract hypotheses,
 *     proving them consistent.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.

(* ===================================================================== *)
(*  Abstract mixed product: classical structural × reject-safe behavioral *)
(* ===================================================================== *)

Section MixedNegation.
  (* Structural leg: classical, two-valued, involutive negation. *)
  Variable DS PS : Type.
  Variable evalS : PS -> DS -> bool.
  Variable negS  : PS -> PS.
  Variable topS  : PS.
  Hypothesis evalS_negS : forall p d, evalS (negS p) d = negb (evalS p d).
  Hypothesis evalS_topS : forall d, evalS topS d = true.

  (* Behavioral leg: reject-safe negation — a SOUND under-approximation of the
     classical complement (no completeness law). *)
  Variable DB PB : Type.
  Variable evalB : PB -> DB -> bool.
  Variable negB  : PB -> PB.
  Variable topB  : PB.
  Hypothesis evalB_negB_sound : forall p d, evalB (negB p) d = true -> evalB p d = false.
  Hypothesis evalB_topB : forall d, evalB topB d = true.

  (* The mixed product predicate evaluation (∧ over the independent legs). *)
  Definition mprod_eval (ps : PS) (pb : PB) (ds : DS) (db : DB) : bool :=
    evalS ps ds && evalB pb db.

  (* The asymmetric De Morgan complement, as a 2-rectangle DNF. *)
  Definition mneg_eval (ps : PS) (pb : PB) (ds : DS) (db : DB) : bool :=
    (evalS (negS ps) ds && evalB topB db) || (evalS topS ds && evalB (negB pb) db).

  (* MAIN: the mixed complement is a reject-safe over-approximation — accepting
     it certifies the product rejects. *)
  Theorem mixed_negation_soundness : forall ps pb ds db,
    mneg_eval ps pb ds db = true -> mprod_eval ps pb ds db = false.
  Proof.
    intros ps pb ds db H. unfold mneg_eval in H. unfold mprod_eval.
    rewrite (evalB_topB db), (evalS_topS ds), (evalS_negS ps ds) in H.
    rewrite andb_true_r, andb_true_l in H.
    apply orb_true_iff in H. destruct H as [H | H].
    - apply negb_true_iff in H. rewrite H. reflexivity.
    - apply evalB_negB_sound in H. rewrite H. apply andb_false_r.
  Qed.

  (* The guard interpretation: if the mixed complement fires, the product guard
     does NOT fire — so no Comm is wrongly admitted. *)
  Corollary mixed_guard_no_false_fire : forall ps pb ds db,
    mneg_eval ps pb ds db = true -> mprod_eval ps pb ds db <> true.
  Proof.
    intros ps pb ds db H Hfire.
    rewrite (mixed_negation_soundness ps pb ds db H) in Hfire. discriminate.
  Qed.

  (* Reject-safe double negation is weak: ¬¬ accepting certifies ¬ rejects. *)
  Theorem weak_dneg : forall pb d,
    evalB (negB (negB pb)) d = true -> evalB (negB pb) d = false.
  Proof. intros pb d H. apply evalB_negB_sound. exact H. Qed.

End MixedNegation.

(* ===================================================================== *)
(*  Concrete reject-safe model: excluded middle fails                    *)
(* ===================================================================== *)

Module TriModel.
  (* A three-valued behavioral predicate over a one-point domain: definitely
     satisfiable, definitely unsatisfiable, or undecided (DontKnow). *)
  Inductive Tri := TSat | TUnsat | TUnknown.

  Definition tri_eval (p : Tri) (_ : unit) : bool :=
    match p with TSat => true | TUnsat => false | TUnknown => false end.

  (* Reject-safe negation: it flips the decided cases but leaves DontKnow
     undecided — it never *claims* membership in the complement of an undecided
     predicate. *)
  Definition tri_neg (p : Tri) : Tri :=
    match p with TSat => TUnsat | TUnsat => TSat | TUnknown => TUnknown end.

  (* The model satisfies the reject-safe soundness law (so the abstract
     hypotheses above are consistent). *)
  Theorem tri_neg_sound : forall p d, tri_eval (tri_neg p) d = true -> tri_eval p d = false.
  Proof. intros [] []; simpl; intro H; try discriminate; reflexivity. Qed.

  (* But excluded middle FAILS: TUnknown satisfies neither itself nor its
     negation — the DontKnow region is inhabited. *)
  Theorem excluded_middle_fails :
    exists (p : Tri) (d : unit),
      tri_eval p d = false /\ tri_eval (tri_neg p) d = false.
  Proof. exists TUnknown, tt. split; reflexivity. Qed.

  (* Equivalently: there is no `p ∨ ¬p = ⊤` law here — the join of TUnknown and
     its negation is not everywhere-true. *)
  Theorem no_classical_complement :
    exists (p : Tri) (d : unit),
      (tri_eval p d || tri_eval (tri_neg p) d) = false.
  Proof. exists TUnknown, tt. reflexivity. Qed.

End TriModel.

Print Assumptions mixed_negation_soundness.
Print Assumptions TriModel.excluded_middle_fails.
Print Assumptions TriModel.tri_neg_sound.
