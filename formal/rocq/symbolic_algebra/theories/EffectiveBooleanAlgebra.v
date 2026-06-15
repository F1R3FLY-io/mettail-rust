(*
 * EffectiveBooleanAlgebra: the abstract effective Boolean algebra (EBA) that the
 * Rust `BooleanAlgebra` trait (prattail/src/symbolic.rs) realizes, with its laws
 * and the derived Boolean-algebra identities (proven up to semantic
 * equivalence, since the Rust `and`/`or`/`not` are *syntactic* predicate
 * constructors that are lawful only up to `equivalent`).
 *
 * An EBA bundles a (possibly infinite) domain `Dom`, a predicate syntax `Pred`,
 * the Boolean constructors, and the three decision procedures EVAL/SAT/WIT.
 * `EBA_Laws` fixes their meaning: EVAL is a Boolean homomorphism, SAT is sound
 * and complete w.r.t. EVAL, and WIT produces a satisfying element exactly when
 * one exists. Everything else (commutativity, associativity, absorption,
 * distributivity, excluded middle, De Morgan, double negation, and the derived
 * operators implies/equivalent/is_tautology/overlaps) is *derived* and proven.
 *
 * Spec-to-Code Traceability:
 *   Coq                         | Rust (prattail/src/symbolic.rs)
 *   ----------------------------|------------------------------------------
 *   EBA.top / bot / conj / disj | BooleanAlgebra::true_pred/false_pred/and/or
 *   EBA.neg / eval / sat / wit  | BooleanAlgebra::not/evaluate/is_satisfiable/witness
 *   decides_implies / overlaps  | BooleanAlgebra::implies/overlaps (default methods)
 *   is_tautology / equivalent   | BooleanAlgebra::is_tautology/equivalent
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import Setoid.

(* ===================================================================== *)
(*  The EBA record and its laws                                          *)
(* ===================================================================== *)

Record EBA := {
  Dom  : Type;
  Pred : Type;
  top  : Pred;
  bot  : Pred;
  conj : Pred -> Pred -> Pred;
  disj : Pred -> Pred -> Pred;
  neg  : Pred -> Pred;
  eval : Pred -> Dom -> bool;
  sat  : Pred -> bool;
  wit  : Pred -> option Dom;
}.

Arguments top {_}.
Arguments bot {_}.
Arguments conj {_} _ _.
Arguments disj {_} _ _.
Arguments neg {_} _.
Arguments eval {_} _ _.
Arguments sat {_} _.
Arguments wit {_} _.

(** The laws an EBA must satisfy. EVAL is the *semantics*; SAT and WIT are
    decision procedures sound and complete w.r.t. it. *)
Record EBA_Laws (A : EBA) : Prop := {
  eval_top  : forall d : Dom A, eval (@top A) d = true;
  eval_bot  : forall d : Dom A, eval (@bot A) d = false;
  eval_conj : forall (p q : Pred A) (d : Dom A),
    eval (conj p q) d = andb (eval p d) (eval q d);
  eval_disj : forall (p q : Pred A) (d : Dom A),
    eval (disj p q) d = orb (eval p d) (eval q d);
  eval_neg  : forall (p : Pred A) (d : Dom A), eval (neg p) d = negb (eval p d);
  sat_sound    : forall p : Pred A, sat p = true -> exists d : Dom A, eval p d = true;
  sat_complete : forall (p : Pred A) (d : Dom A), eval p d = true -> sat p = true;
  wit_sound : forall (p : Pred A) (d : Dom A), wit p = Some d -> eval p d = true;
  wit_total : forall p : Pred A, sat p = true -> exists d : Dom A, wit p = Some d;
}.

(* ===================================================================== *)
(*  Reject-safe laws: the WEAK contract for semi-decidable algebras       *)
(* ===================================================================== *)

(** The weak law contract that the behavioral / Heyting leg satisfies. It
    deliberately drops [sat_complete], the classical involutive [eval_neg], and
    excluded middle. In their place, negation is only required to be a *sound
    under-approximation* of the classical complement: whenever the (possibly
    incomplete) complement accepts an element, that element is genuinely outside
    the predicate. The converse may fail — that gap is precisely the
    [Sat3::DontKnow] boundary of a semi-decidable predicate.

    This record is what prevents a downstream proof from ever assuming classical
    complement on a semi-decidable leg (the Dovetail session's caution,
    discharged structurally): SFA/SFT machinery and the mixed
    [ProductAlgebra<Structural, Behavioral>] are written against [RejectSafeLaws],
    while operations needing classical complement demand the full [EBA_Laws].
    It is the Coq mirror of the Rust trait [RejectSafeAlgebra] at the base of the
    tower [BooleanAlgebra : HeytingAlgebra : RejectSafeAlgebra]. *)
Record RejectSafeLaws (A : EBA) : Prop := {
  rs_eval_conj : forall (p q : Pred A) (d : Dom A),
    eval (conj p q) d = andb (eval p d) (eval q d);
  rs_eval_disj : forall (p q : Pred A) (d : Dom A),
    eval (disj p q) d = orb (eval p d) (eval q d);
  rs_eval_neg_sound : forall (p : Pred A) (d : Dom A),
    eval (neg p) d = true -> eval p d = false;
  rs_sat_sound : forall p : Pred A, sat p = true -> exists d : Dom A, eval p d = true;
  rs_wit_sound : forall (p : Pred A) (d : Dom A), wit p = Some d -> eval p d = true;
}.

(** Every classical EBA is reject-safe: the strong contract implies the weak one.
    This is the base edge of the trait tower — a [BooleanAlgebra] is a fortiori a
    [RejectSafeAlgebra], so existing decidable algebras drop straight into the
    reject-safe-bounded machinery with no proof obligation of their own. *)
Lemma eba_implies_reject_safe : forall (A : EBA), EBA_Laws A -> RejectSafeLaws A.
Proof.
  intros A L. constructor.
  - exact (eval_conj A L).
  - exact (eval_disj A L).
  - intros p d Hneg. rewrite (eval_neg A L) in Hneg.
    apply negb_true_iff in Hneg. exact Hneg.
  - exact (sat_sound A L).
  - exact (wit_sound A L).
Qed.

(** An unsatisfiable predicate has no witness — the contrapositive of
    wit_sound composed with sat_complete. Reused by the closure family's
    [wit_total] proofs (sum/collection/tree) to discharge the "fall through to
    the next component" case. *)
Lemma wit_none_of_unsat :
  forall (A : EBA), EBA_Laws A -> forall p : Pred A, sat p = false -> wit p = None.
Proof.
  intros A L p H. destruct (wit p) as [d|] eqn:W; [|reflexivity].
  apply (wit_sound A L) in W. apply (sat_complete A L) in W.
  rewrite W in H. discriminate.
Qed.

(** Semantic equivalence: two predicates denote the same set of domain elements.
    This is the relation the Boolean-algebra laws hold up to. *)
Definition equiv (A : EBA) (p q : Pred A) : Prop :=
  forall d, eval p d = eval q d.

Notation "p ≈[ A ] q" := (equiv A p q) (at level 70).

Section Laws.
  Variable A : EBA.
  Variable L : EBA_Laws A.

  Let Etop  := eval_top A L.
  Let Ebot  := eval_bot A L.
  Let Econj := eval_conj A L.
  Let Edisj := eval_disj A L.
  Let Eneg  := eval_neg A L.

  (* ===================================================================== *)
  (*  ≈ is an equivalence relation                                         *)
  (* ===================================================================== *)

  Lemma equiv_refl : forall p, equiv A p p.
  Proof. intros p d. reflexivity. Qed.

  Lemma equiv_sym : forall p q, equiv A p q -> equiv A q p.
  Proof. intros p q H d. symmetry. apply H. Qed.

  Lemma equiv_trans : forall p q r, equiv A p q -> equiv A q r -> equiv A p r.
  Proof. intros p q r H1 H2 d. rewrite H1. apply H2. Qed.

  (* ===================================================================== *)
  (*  Boolean-algebra axioms (up to ≈)                                     *)
  (* ===================================================================== *)

  Lemma conj_comm : forall p q, equiv A (conj p q) (conj q p).
  Proof. intros p q d. rewrite !Econj. apply andb_comm. Qed.

  Lemma disj_comm : forall p q, equiv A (disj p q) (disj q p).
  Proof. intros p q d. rewrite !Edisj. apply orb_comm. Qed.

  Lemma conj_assoc : forall p q r, equiv A (conj p (conj q r)) (conj (conj p q) r).
  Proof.
    intros p q r d. rewrite !Econj.
    destruct (eval p d), (eval q d), (eval r d); reflexivity.
  Qed.

  Lemma disj_assoc : forall p q r, equiv A (disj p (disj q r)) (disj (disj p q) r).
  Proof.
    intros p q r d. rewrite !Edisj.
    destruct (eval p d), (eval q d), (eval r d); reflexivity.
  Qed.

  Lemma conj_idem : forall p, equiv A (conj p p) p.
  Proof. intros p d. rewrite Econj. apply andb_diag. Qed.

  Lemma disj_idem : forall p, equiv A (disj p p) p.
  Proof. intros p d. rewrite Edisj. apply orb_diag. Qed.

  Lemma absorb_conj_disj : forall p q, equiv A (conj p (disj p q)) p.
  Proof.
    intros p q d. rewrite Econj, Edisj.
    destruct (eval p d), (eval q d); reflexivity.
  Qed.

  Lemma absorb_disj_conj : forall p q, equiv A (disj p (conj p q)) p.
  Proof.
    intros p q d. rewrite Edisj, Econj.
    destruct (eval p d), (eval q d); reflexivity.
  Qed.

  Lemma distrib_conj_disj :
    forall p q r, equiv A (conj p (disj q r)) (disj (conj p q) (conj p r)).
  Proof.
    intros p q r d. rewrite !Econj, !Edisj, !Econj.
    destruct (eval p d), (eval q d), (eval r d); reflexivity.
  Qed.

  Lemma distrib_disj_conj :
    forall p q r, equiv A (disj p (conj q r)) (conj (disj p q) (disj p r)).
  Proof.
    intros p q r d. rewrite !Edisj, !Econj, !Edisj.
    destruct (eval p d), (eval q d), (eval r d); reflexivity.
  Qed.

  Lemma conj_top : forall p, equiv A (conj p top) p.
  Proof. intros p d. rewrite Econj, Etop. apply andb_true_r. Qed.

  Lemma disj_bot : forall p, equiv A (disj p bot) p.
  Proof. intros p d. rewrite Edisj, Ebot. apply orb_false_r. Qed.

  Lemma conj_bot : forall p, equiv A (conj p bot) bot.
  Proof. intros p d. rewrite Econj, Ebot. apply andb_false_r. Qed.

  Lemma disj_top : forall p, equiv A (disj p top) top.
  Proof. intros p d. rewrite Edisj, Etop. apply orb_true_r. Qed.

  Lemma excluded_middle : forall p, equiv A (disj p (neg p)) top.
  Proof.
    intros p d. rewrite Edisj, Eneg, Etop.
    destruct (eval p d); reflexivity.
  Qed.

  Lemma non_contradiction : forall p, equiv A (conj p (neg p)) bot.
  Proof.
    intros p d. rewrite Econj, Eneg, Ebot.
    destruct (eval p d); reflexivity.
  Qed.

  Lemma double_neg : forall p, equiv A (neg (neg p)) p.
  Proof. intros p d. rewrite !Eneg. apply negb_involutive. Qed.

  Lemma de_morgan_conj :
    forall p q, equiv A (neg (conj p q)) (disj (neg p) (neg q)).
  Proof.
    intros p q d. rewrite Eneg, Econj, Edisj, !Eneg.
    destruct (eval p d), (eval q d); reflexivity.
  Qed.

  Lemma de_morgan_disj :
    forall p q, equiv A (neg (disj p q)) (conj (neg p) (neg q)).
  Proof.
    intros p q d. rewrite Eneg, Edisj, Econj, !Eneg.
    destruct (eval p d), (eval q d); reflexivity.
  Qed.

  (* ===================================================================== *)
  (*  Satisfiability characterizations                                     *)
  (* ===================================================================== *)

  (** SAT is false exactly when the predicate denotes the empty set. *)
  Lemma sat_false_iff_empty :
    forall (p : Pred A), sat p = false <-> (forall d, eval p d = false).
  Proof.
    intros p. split.
    - intros Hsat d. destruct (eval p d) eqn:E; [| reflexivity].
      apply (sat_complete A L) in E. rewrite E in Hsat. discriminate.
    - intros Hempty. destruct (sat p) eqn:E; [| reflexivity].
      apply (sat_sound A L) in E. destruct E as [d Hd].
      rewrite Hempty in Hd. discriminate.
  Qed.

  (** SAT is true exactly when the predicate is inhabited. *)
  Lemma sat_true_iff_inhabited :
    forall (p : Pred A), sat p = true <-> (exists d, eval p d = true).
  Proof.
    intros p. split.
    - apply (sat_sound A L).
    - intros [d Hd]. apply (sat_complete A L) with (d := d). exact Hd.
  Qed.

  (* ===================================================================== *)
  (*  Derived operators (mirroring the Rust default methods)               *)
  (* ===================================================================== *)

  (** `implies p q` decides "every element satisfying p satisfies q". *)
  Definition decides_implies (p q : Pred A) : bool :=
    negb (sat (conj p (neg q))).

  Lemma implies_correct :
    forall p q,
      decides_implies p q = true <->
      (forall d, eval p d = true -> eval q d = true).
  Proof.
    intros p q. unfold decides_implies.
    rewrite negb_true_iff. rewrite sat_false_iff_empty.
    split.
    - intros Hempty d Hp. specialize (Hempty d).
      rewrite Econj, Eneg in Hempty.
      rewrite Hp in Hempty. simpl in Hempty.
      destruct (eval q d); [reflexivity | discriminate].
    - intros Himp d. rewrite Econj, Eneg.
      destruct (eval p d) eqn:Ep; simpl; [| reflexivity].
      rewrite (Himp d Ep). reflexivity.
  Qed.

  (** `is_tautology p` decides "every element satisfies p". *)
  Definition decides_tautology (p : Pred A) : bool := negb (sat (neg p)).

  Lemma tautology_correct :
    forall p, decides_tautology p = true <-> (forall d, eval p d = true).
  Proof.
    intros p. unfold decides_tautology.
    rewrite negb_true_iff. rewrite sat_false_iff_empty.
    split.
    - intros H d. specialize (H d). rewrite Eneg in H.
      destruct (eval p d); [reflexivity | discriminate].
    - intros H d. rewrite Eneg. rewrite H. reflexivity.
  Qed.

  (** `overlaps p q` decides "some element satisfies both". *)
  Definition decides_overlaps (p q : Pred A) : bool := sat (conj p q).

  Lemma overlaps_correct :
    forall p q,
      decides_overlaps p q = true <-> (exists d, eval p d = true /\ eval q d = true).
  Proof.
    intros p q. unfold decides_overlaps.
    rewrite sat_true_iff_inhabited. split.
    - intros [d Hd]. exists d. rewrite Econj in Hd.
      apply andb_prop in Hd. exact Hd.
    - intros [d [Hp Hq]]. exists d. rewrite Econj, Hp, Hq. reflexivity.
  Qed.

  (** `equivalent p q` decides semantic equivalence. *)
  Definition decides_equivalent (p q : Pred A) : bool :=
    andb (decides_implies p q) (decides_implies q p).

  Lemma equivalent_correct :
    forall p q, decides_equivalent p q = true <-> equiv A p q.
  Proof.
    intros p q. unfold decides_equivalent, equiv.
    rewrite andb_true_iff, !implies_correct.
    split.
    - intros [H1 H2] d.
      destruct (eval p d) eqn:Ep, (eval q d) eqn:Eq; try reflexivity.
      + rewrite (H1 d Ep) in Eq. discriminate.
      + rewrite (H2 d Eq) in Ep. discriminate.
    - intros H. split; intros d Hx.
      + rewrite <- H. exact Hx.
      + rewrite H. exact Hx.
  Qed.

End Laws.

(* Closure under the global context is verified by the (extended) zero-admission
   checker; an explicit assumption print is kept as cheap insurance. *)
Print Assumptions equivalent_correct.
Print Assumptions eba_implies_reject_safe.
