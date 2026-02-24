(*
 * TotalOrder: Opt 4 — OrdVar Total Order and Scope Total Preorder.
 *
 * Two separate sections with different guarantees:
 *
 * OrdVar (Total Order, under hash injectivity on u32 UniqueId):
 *   - Model: Var := Free uid | Bound scope binder
 *   - Comparison: variant discriminant, then hash(uid) for Free or
 *     (scope, binder) lexicographic for Bound
 *   - Theorems: O1a reflexivity, O1b antisymmetry, O1c transitivity, O1d totality
 *   - O3: Hash-Ord consistency (cmp_var (Free a) (Free b) = Eq <-> a = b)
 *
 * Scope (Total Preorder, hash collisions on patterns break antisymmetry):
 *   - Model: cmp_scope (p1,b1) (p2,b2) :=
 *       Z.compare(hash p1)(hash p2) then cmp_body b1 b2
 *   - Theorems: O2a reflexivity, O2b transitivity, O2c totality
 *   - O4: eq_scope s1 s2 -> cmp_scope s1 s2 = Eq (but NOT converse)
 *   - Rust BTree collections only require total preorder, not strict total order.
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition          | Rust / Ascent Code                | Location
 *   -------------------------|-----------------------------------|--------------------------
 *   cmp_var                  | OrdVar::cmp                       | binding.rs:266-289
 *   cmp_scope                | Scope::cmp                        | binding.rs:111-134
 *   hash_uid                 | hash_uid closure in OrdVar::cmp   | binding.rs:279-283
 *   hash_pat                 | hash_pat closure in Scope::cmp    | binding.rs:127-130
 *   Free / Bound             | Var::Free / Var::Bound            | moniker crate
 *   OrdVar                   | pub struct OrdVar(pub Var<String>) | binding.rs:256-258
 *   Scope                    | pub struct Scope<P, T> { inner }  | binding.rs:87-89
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Bool.

From AscentOptimizations Require Import Prelude.

Import ListNotations.

(* We use Stdlib's comparison type: Lt, Eq, Gt from CompOpp *)

(* ===================================================================== *)
(*  Comparison combinators using Stdlib comparison                        *)
(* ===================================================================== *)

Definition cmp_then (c1 c2 : comparison) : comparison :=
  match c1 with
  | Eq => c2
  | _ => c1
  end.

(* ===================================================================== *)
(*  Properties of Z.compare                                               *)
(* ===================================================================== *)

Lemma z_compare_refl : forall a, Z.compare a a = Eq.
Proof. intros a. apply Z.compare_refl. Qed.

Lemma z_compare_eq : forall a b, Z.compare a b = Eq -> a = b.
Proof. intros a b H. apply Z.compare_eq. exact H. Qed.

Lemma z_compare_lt_trans : forall a b c,
  Z.compare a b = Lt -> Z.compare b c = Lt -> Z.compare a c = Lt.
Proof.
  intros a b c Hab Hbc.
  apply Z.compare_lt_iff.
  apply Z.compare_lt_iff in Hab.
  apply Z.compare_lt_iff in Hbc.
  exact (Z.lt_trans _ _ _ Hab Hbc).
Qed.

Lemma z_compare_antisym : forall a b, Z.compare a b = CompOpp (Z.compare b a).
Proof. intros a b. apply Z.compare_antisym. Qed.

Lemma z_compare_total : forall a b,
  Z.compare a b = Lt \/ Z.compare a b = Eq \/ Z.compare a b = Gt.
Proof.
  intros a b.
  destruct (Z.compare a b); auto.
Qed.

(* ===================================================================== *)
(*  Properties of Nat.compare                                             *)
(* ===================================================================== *)

Lemma nat_compare_refl : forall a, Nat.compare a a = Eq.
Proof. intros a. apply Nat.compare_refl. Qed.

Lemma nat_compare_eq : forall a b, Nat.compare a b = Eq -> a = b.
Proof. intros a b H. apply Nat.compare_eq. exact H. Qed.

Lemma nat_compare_lt_trans : forall a b c,
  Nat.compare a b = Lt -> Nat.compare b c = Lt -> Nat.compare a c = Lt.
Proof.
  intros a b c Hab Hbc.
  apply Nat.compare_lt_iff in Hab.
  apply Nat.compare_lt_iff in Hbc.
  apply Nat.compare_lt_iff. lia.
Qed.

(* ===================================================================== *)
(*  Properties of cmp_then                                                *)
(* ===================================================================== *)

Lemma cmp_then_refl : forall c, cmp_then Eq c = c.
Proof. reflexivity. Qed.

Lemma cmp_then_eq : forall c1 c2, cmp_then c1 c2 = Eq -> c1 = Eq /\ c2 = Eq.
Proof.
  intros c1 c2 H. destruct c1; simpl in H; try discriminate.
  split; [reflexivity | exact H].
Qed.

Lemma cmp_then_lt_left : forall c, cmp_then Lt c = Lt.
Proof. reflexivity. Qed.

Lemma cmp_then_gt_left : forall c, cmp_then Gt c = Gt.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  SECTION 1: OrdVar — Total Order                                       *)
(* ===================================================================== *)

Section OrdVarOrder.

  (* Abstract unique ID type *)
  Variable UID : Type.
  Variable hash_uid : UID -> Z.
  Hypothesis hash_uid_injective : forall a b : UID, hash_uid a = hash_uid b -> a = b.

  (* Bound variable components *)
  Variable ScopeId : Type.
  Variable BinderId : Type.
  Variable cmp_scope_id : ScopeId -> ScopeId -> comparison.
  Variable cmp_binder_id : BinderId -> BinderId -> comparison.

  (* Scope/Binder comparison properties *)
  Hypothesis cmp_scope_id_refl : forall s, cmp_scope_id s s = Eq.
  Hypothesis cmp_scope_id_eq : forall s1 s2, cmp_scope_id s1 s2 = Eq -> s1 = s2.
  Hypothesis cmp_scope_id_trans_lt : forall a b c,
    cmp_scope_id a b = Lt -> cmp_scope_id b c = Lt -> cmp_scope_id a c = Lt.
  Hypothesis cmp_scope_id_antisym : forall a b,
    cmp_scope_id a b = CompOpp (cmp_scope_id b a).

  Hypothesis cmp_binder_id_refl : forall b, cmp_binder_id b b = Eq.
  Hypothesis cmp_binder_id_eq : forall b1 b2, cmp_binder_id b1 b2 = Eq -> b1 = b2.
  Hypothesis cmp_binder_id_trans_lt : forall a b c,
    cmp_binder_id a b = Lt -> cmp_binder_id b c = Lt -> cmp_binder_id a c = Lt.
  Hypothesis cmp_binder_id_antisym : forall a b,
    cmp_binder_id a b = CompOpp (cmp_binder_id b a).

  (* Var type: mirrors Rust's moniker::Var *)
  Inductive Var : Type :=
    | Free : UID -> Var
    | Bound : ScopeId -> BinderId -> Var.

  (* OrdVar comparison: mirrors binding.rs:266-289 *)
  Definition cmp_var (v1 v2 : Var) : comparison :=
    match v1, v2 with
    | Free _, Bound _ _ => Lt          (* Free < Bound by variant discriminant *)
    | Bound _ _, Free _ => Gt          (* Bound > Free by variant discriminant *)
    | Free a, Free b =>
        Z.compare (hash_uid a) (hash_uid b)  (* Compare by hash of UniqueId *)
    | Bound s1 b1, Bound s2 b2 =>
        cmp_then (cmp_scope_id s1 s2)         (* Lexicographic: scope first *)
                 (cmp_binder_id b1 b2)        (* then binder *)
    end.

  (* ----------------------------------------------------------------- *)
  (*  O1a: Reflexivity                                                   *)
  (* ----------------------------------------------------------------- *)
  Theorem O1a_cmp_var_refl : forall v, cmp_var v v = Eq.
  Proof.
    intros v. destruct v as [uid | s b].
    - (* Free uid *)
      simpl. apply z_compare_refl.
    - (* Bound s b *)
      simpl. rewrite cmp_scope_id_refl. simpl. apply cmp_binder_id_refl.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  O1b: Antisymmetry (cmp_var v1 v2 = Eq -> v1 = v2)                *)
  (* ----------------------------------------------------------------- *)
  Theorem O1b_cmp_var_antisym : forall v1 v2,
    cmp_var v1 v2 = Eq -> v1 = v2.
  Proof.
    intros v1 v2 H.
    destruct v1 as [a | s1 b1]; destruct v2 as [b | s2 b2]; simpl in H;
      try discriminate.
    - (* Free a, Free b *)
      apply z_compare_eq in H. apply hash_uid_injective in H. subst. reflexivity.
    - (* Bound s1 b1, Bound s2 b2 *)
      apply cmp_then_eq in H. destruct H as [Hs Hb].
      apply cmp_scope_id_eq in Hs. apply cmp_binder_id_eq in Hb.
      subst. reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Helper: cmp_var flip                                              *)
  (* ----------------------------------------------------------------- *)
  Lemma cmp_var_flip : forall v1 v2, cmp_var v1 v2 = CompOpp (cmp_var v2 v1).
  Proof.
    intros v1 v2.
    destruct v1 as [a | s1 b1]; destruct v2 as [b | s2 b2]; simpl.
    - (* Free, Free *)
      apply z_compare_antisym.
    - (* Free, Bound *) reflexivity.
    - (* Bound, Free *) reflexivity.
    - (* Bound, Bound *)
      rewrite cmp_scope_id_antisym with (a := s1).
      rewrite cmp_binder_id_antisym with (a := b1).
      destruct (cmp_scope_id s2 s1) eqn:Hs; simpl;
        try reflexivity;
        destruct (cmp_binder_id b2 b1) eqn:Hb; simpl; reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  O1c: Transitivity                                                  *)
  (* ----------------------------------------------------------------- *)

  (* Helper for Bound-Bound-Bound transitivity with cmp_then *)
  Lemma cmp_then_trans_lt_lt :
    forall s1 s2 s3 b1 b2 b3,
      cmp_then (cmp_scope_id s1 s2) (cmp_binder_id b1 b2) = Lt ->
      cmp_then (cmp_scope_id s2 s3) (cmp_binder_id b2 b3) = Lt ->
      cmp_then (cmp_scope_id s1 s3) (cmp_binder_id b1 b3) = Lt.
  Proof.
    intros s1 s2 s3 b1 b2 b3 H12 H23.
    unfold cmp_then in *.
    destruct (cmp_scope_id s1 s2) eqn:Hs12; try discriminate;
    destruct (cmp_scope_id s2 s3) eqn:Hs23; try discriminate.
    - (* Eq, Eq -> scope s1=s3, binders: b1<b2, b2<b3 *)
      apply cmp_scope_id_eq in Hs12. apply cmp_scope_id_eq in Hs23. subst.
      rewrite cmp_scope_id_refl.
      exact (cmp_binder_id_trans_lt b1 b2 b3 H12 H23).
    - (* Eq, Lt -> s1=s2, s2<s3 -> s1<s3 *)
      apply cmp_scope_id_eq in Hs12. subst. rewrite Hs23. reflexivity.
    - (* Lt, Eq -> s1<s2, s2=s3 -> s1<s3 *)
      apply cmp_scope_id_eq in Hs23. subst. rewrite Hs12. reflexivity.
    - (* Lt, Lt -> s1<s3 *)
      rewrite (cmp_scope_id_trans_lt s1 s2 s3 Hs12 Hs23). reflexivity.
  Qed.

  Theorem O1c_cmp_var_trans : forall v1 v2 v3,
    cmp_var v1 v2 = Lt -> cmp_var v2 v3 = Lt -> cmp_var v1 v3 = Lt.
  Proof.
    intros v1 v2 v3 H12 H23.
    destruct v1 as [a | s1 b1];
    destruct v2 as [b | s2 b2];
    destruct v3 as [c | s3 b3];
    simpl in *; try discriminate; try reflexivity.
    - (* Free, Free, Free *)
      exact (z_compare_lt_trans _ _ _ H12 H23).
    - (* Bound, Bound, Bound *)
      exact (cmp_then_trans_lt_lt s1 s2 s3 b1 b2 b3 H12 H23).
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  O1d: Totality                                                      *)
  (* ----------------------------------------------------------------- *)
  Theorem O1d_cmp_var_total : forall v1 v2,
    cmp_var v1 v2 = Lt \/ cmp_var v1 v2 = Eq \/ cmp_var v1 v2 = Gt.
  Proof.
    intros v1 v2.
    destruct v1; destruct v2; simpl;
      try (left; reflexivity); try (right; right; reflexivity).
    - (* Free, Free *)
      apply z_compare_total.
    - (* Bound, Bound *)
      destruct (cmp_scope_id s s0) eqn:Hs; simpl.
      + (* Eq: passes through to binder *)
        destruct (cmp_binder_id b b0) eqn:Hb; auto.
      + (* Lt *)
        left. reflexivity.
      + (* Gt *)
        right. right. reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  O3: Hash-Ord consistency for Free variables                        *)
  (* ----------------------------------------------------------------- *)
  Theorem O3_hash_ord_consistency : forall a b,
    cmp_var (Free a) (Free b) = Eq <-> a = b.
  Proof.
    intros a b. split.
    - intros H. simpl in H. apply z_compare_eq in H.
      apply hash_uid_injective. exact H.
    - intros H. subst. apply O1a_cmp_var_refl.
  Qed.

End OrdVarOrder.

(* ===================================================================== *)
(*  SECTION 2: Scope — Total Preorder                                     *)
(* ===================================================================== *)

Section ScopeOrder.

  (* Pattern and body types *)
  Variable P : Type.
  Variable T : Type.

  (* Hash on patterns (may have collisions — patterns are complex types) *)
  Variable hash_pat : P -> Z.

  (* Body comparison (assumed to be a total order on T) *)
  Variable cmp_body : T -> T -> comparison.
  Hypothesis cmp_body_refl : forall t, cmp_body t t = Eq.
  Hypothesis cmp_body_trans_lt : forall a b c,
    cmp_body a b = Lt -> cmp_body b c = Lt -> cmp_body a c = Lt.
  Hypothesis cmp_body_eq_implies_eq : forall a b, cmp_body a b = Eq -> a = b.
  Hypothesis cmp_body_antisym : forall a b, cmp_body a b = CompOpp (cmp_body b a).

  (* Structural equality on patterns *)
  Variable eq_pat : P -> P -> Prop.
  Hypothesis eq_pat_dec : forall p1 p2, {eq_pat p1 p2} + {~ eq_pat p1 p2}.

  (* Scope = (pattern, body) pair — mirrors binding.rs:87-89 *)
  Record Scope_t := mkScope {
    scope_pattern : P;
    scope_body : T;
  }.

  (* Scope comparison: mirrors binding.rs:111-134 *)
  Definition cmp_scope (s1 s2 : Scope_t) : comparison :=
    cmp_then
      (Z.compare (hash_pat (scope_pattern s1)) (hash_pat (scope_pattern s2)))
      (cmp_body (scope_body s1) (scope_body s2)).

  (* Scope structural equality *)
  Definition scope_eq (s1 s2 : Scope_t) : Prop :=
    eq_pat (scope_pattern s1) (scope_pattern s2) /\
    scope_body s1 = scope_body s2.

  (* ----------------------------------------------------------------- *)
  (*  O2a: Reflexivity                                                   *)
  (* ----------------------------------------------------------------- *)
  Theorem O2a_cmp_scope_refl : forall s, cmp_scope s s = Eq.
  Proof.
    intros s. unfold cmp_scope.
    rewrite z_compare_refl. simpl. apply cmp_body_refl.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  O2b: Transitivity                                                  *)
  (* ----------------------------------------------------------------- *)
  Theorem O2b_cmp_scope_trans : forall s1 s2 s3,
    cmp_scope s1 s2 = Lt -> cmp_scope s2 s3 = Lt -> cmp_scope s1 s3 = Lt.
  Proof.
    intros s1 s2 s3 H12 H23.
    unfold cmp_scope, cmp_then in *.
    destruct (Z.compare (hash_pat (scope_pattern s1))
                        (hash_pat (scope_pattern s2))) eqn:Hz12; try discriminate;
    destruct (Z.compare (hash_pat (scope_pattern s2))
                        (hash_pat (scope_pattern s3))) eqn:Hz23; try discriminate.
    - (* Eq, Eq: hash s1 = hash s2 = hash s3 *)
      apply Z.compare_eq in Hz12. apply Z.compare_eq in Hz23.
      rewrite Hz12. rewrite Hz23. rewrite Z.compare_refl.
      exact (cmp_body_trans_lt _ _ _ H12 H23).
    - (* Eq, Lt: hash s1 = hash s2, hash s2 < hash s3 *)
      apply Z.compare_eq in Hz12. rewrite Hz12. rewrite Hz23. reflexivity.
    - (* Lt, Eq: hash s1 < hash s2, hash s2 = hash s3 *)
      apply Z.compare_eq in Hz23. rewrite <- Hz23. rewrite Hz12. reflexivity.
    - (* Lt, Lt: hash s1 < hash s3 *)
      rewrite (z_compare_lt_trans _ _ _ Hz12 Hz23). reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  O2c: Totality                                                      *)
  (* ----------------------------------------------------------------- *)
  Theorem O2c_cmp_scope_total : forall s1 s2,
    cmp_scope s1 s2 = Lt \/ cmp_scope s1 s2 = Eq \/ cmp_scope s1 s2 = Gt.
  Proof.
    intros s1 s2. unfold cmp_scope, cmp_then.
    destruct (Z.compare (hash_pat (scope_pattern s1)) (hash_pat (scope_pattern s2))) eqn:Hz.
    - (* Eq: passes through to cmp_body *)
      destruct (cmp_body (scope_body s1) (scope_body s2)) eqn:Hb; auto.
    - (* Lt *)
      left. reflexivity.
    - (* Gt *)
      right. right. reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  O4: PartialEq implies Ord-Eq (requires hash compatibility)        *)
  (* ----------------------------------------------------------------- *)

  (* Additional hypothesis: structural pattern equality implies hash equality *)
  Hypothesis hash_pat_compat : forall p1 p2, eq_pat p1 p2 -> hash_pat p1 = hash_pat p2.

  Theorem O4_eq_implies_cmp_eq : forall s1 s2,
    scope_eq s1 s2 -> cmp_scope s1 s2 = Eq.
  Proof.
    intros s1 s2 [Hpat Hbody].
    unfold cmp_scope.
    rewrite (hash_pat_compat _ _ Hpat).
    rewrite z_compare_refl. simpl.
    rewrite Hbody. apply cmp_body_refl.
  Qed.

  (* Demonstrate that the converse does NOT hold (hash collisions break it).
     We state this as a negative result: there is no proof of the converse
     without hash injectivity on patterns. *)
  Remark O4_converse_not_provable :
    (* If hash_pat is not injective on patterns, then
       cmp_scope s1 s2 = Eq does NOT imply scope_eq s1 s2.
       This is a documentation remark, not a formal theorem. *)
    True.
  Proof. exact I. Qed.

  (* ----------------------------------------------------------------- *)
  (*  NOT antisymmetric: Total Preorder, not Total Order                 *)
  (* ----------------------------------------------------------------- *)
  (* Scope comparison is a total preorder because hash collisions on
     patterns can cause cmp_scope s1 s2 = Eq even when s1 <> s2.
     This is acceptable: Rust's BTree only requires total preorder.

     Antisymmetry would require:
       cmp_scope s1 s2 = Eq /\ cmp_scope s2 s1 = Eq -> s1 = s2
     which fails when hash_pat p1 = hash_pat p2 but p1 <> p2. *)

End ScopeOrder.
