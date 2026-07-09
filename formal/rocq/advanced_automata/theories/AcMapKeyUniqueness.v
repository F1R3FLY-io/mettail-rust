(*
 * AcMapKeyUniqueness: FV (AC-map) for Stage AC's in-Rho AC matching of Map (EMap) operands.
 *
 * A Map (rho `EMap` / host `ParMap`) is a key-unique association: at most one value per key
 * (the sorted-dedup `ParMap` invariant). When an AC-map pattern `{k_1:v_1, …, ...rest}` is
 * matched, the native matcher removes the fixed (key,value) entries and binds `rest` to the
 * remainder map. This theory proves the load-bearing MapAc invariant: KEY-UNIQUENESS IS
 * PRESERVED ACROSS THE SPLIT — the remainder is still key-unique, and the removed key no
 * longer appears in it (so re-inserting the fixed entries cannot collide). Without this, the
 * `rest` binding could smuggle a duplicate key past the split and violate the `ParMap`
 * invariant the decoder relies on.
 *
 * Self-contained over `Stdlib.List.NoDup` (keys as nat identities). Zero-admission.
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.

Import ListNotations.

Section AcMapKeyUniqueness.

  Variable V : Type.
  Definition Entry : Type := (nat * V)%type.
  Definition Map : Type := list Entry.
  Definition keys (m : Map) : list nat := map fst m.

  (* Key-uniqueness = the keys have no duplicates (the ParMap sorted-dedup invariant). *)
  Definition key_unique (m : Map) : Prop := NoDup (keys m).

  (* Remove the first entry with key k (given key-uniqueness there is at most one). *)
  Fixpoint remove_key (k : nat) (m : Map) : Map :=
    match m with
    | [] => []
    | (k', v) :: t => if Nat.eqb k' k then t else (k', v) :: remove_key k t
    end.

  (* Removal never introduces a key: every remainder key was already a key of the map. *)
  Lemma remove_key_keys_incl : forall k m x,
    In x (keys (remove_key k m)) -> In x (keys m).
  Proof.
    intros k m x. induction m as [| [k' v] t IH]; simpl; [ tauto |].
    destruct (Nat.eqb k' k) eqn:He.
    - intro Hin. right. exact Hin.
    - simpl. intros [Heq | Hin].
      + left. exact Heq.
      + right. apply IH. exact Hin.
  Qed.

  (* (AC-map.1) KEY-UNIQUENESS PRESERVED: the remainder after removing a key is still
     key-unique — the AC-map split cannot create a duplicate key. *)
  Theorem remove_key_preserves_uniqueness : forall k m,
    key_unique m -> key_unique (remove_key k m).
  Proof.
    intros k m. unfold key_unique. induction m as [| [k' v] t IH]; simpl; [ intro; constructor |].
    destruct (Nat.eqb k' k) eqn:He.
    - intro Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [_ Hnd]. exact Hnd.
    - simpl. intro Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
      apply NoDup_cons_iff. split.
      + intro Hin. apply Hnotin. apply remove_key_keys_incl in Hin. exact Hin.
      + apply IH. exact Hnd.
  Qed.

  (* (AC-map.2) THE REMOVED KEY IS GONE: after removing key k from a key-unique map, k no
     longer occurs — so re-inserting a fixed entry with key k cannot collide with the rest. *)
  Theorem remove_key_drops_key : forall k m,
    key_unique m -> ~ In k (keys (remove_key k m)).
  Proof.
    intros k m. unfold key_unique. induction m as [| [k' v] t IH]; simpl.
    - intros _ [].
    - destruct (Nat.eqb k' k) eqn:He.
      + apply Nat.eqb_eq in He. subst k'.
        intro Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin _]. exact Hnotin.
      + apply Nat.eqb_neq in He. simpl. intro Hnd.
        apply NoDup_cons_iff in Hnd. destruct Hnd as [_ Hnd].
        intros [Heq | Hin].
        * apply He. exact Heq.
        * apply (IH Hnd). exact Hin.
  Qed.

  (* (AC-map.3) A DISTINCT KEY SURVIVES: removing key k leaves any OTHER present key in place
     — the split loses only the matched key, correlating the fixed/rest partition with the map
     (no unrelated entry is dropped). *)
  Theorem remove_key_keeps_other : forall k j m,
    j <> k -> In j (keys m) -> In j (keys (remove_key k m)).
  Proof.
    intros k j m Hne. induction m as [| [k' v] t IH]; simpl; [ intros [] |].
    destruct (Nat.eqb k' k) eqn:He.
    - apply Nat.eqb_eq in He. subst k'. intros [Heq | Hin].
      + exfalso. apply Hne. symmetry. exact Heq.
      + exact Hin.
    - simpl. intros [Heq | Hin].
      + left. exact Heq.
      + right. apply IH. exact Hin.
  Qed.

  (* ------------------------------------------------------------------------------------------- *)
  (* AC4 — key-uniqueness survives the ENTIRE reflect -> match -> RHS split.                       *)
  (*                                                                                             *)
  (* The AC4-map path is: (reflect) the subject map is reflected to the native EMap carrier, which  *)
  (* rides `ParMap` — sorted + key-deduped, so the located map is a PERMUTATION of the subject map; *)
  (* (match) the native `list_match_single_` removes the matched key entries + binds the residual   *)
  (* map to the remainder; (RHS) the receiver body reconstructs a map by re-inserting the fixed     *)
  (* entries. This block proves KEY-UNIQUENESS is an invariant of EACH step, so the `ParMap`         *)
  (* invariant the decoder relies on holds end to end.                                             *)

  (* keys is a permutation congruence: a permuted map has permuted keys. *)
  Lemma keys_perm : forall m1 m2, Permutation m1 m2 -> Permutation (keys m1) (keys m2).
  Proof. intros m1 m2 Hperm. unfold keys. apply Permutation_map. exact Hperm. Qed.

  (* (AC4-map REFLECT) key-uniqueness is PERMUTATION-INVARIANT: the located map (a permutation of the
     subject map — the ParSet/ParMap re-sourcing) is key-unique iff the subject map is. So reflecting
     the operand map to the EMap carrier neither adds nor drops a key collision. *)
  Theorem key_unique_perm : forall m1 m2,
    Permutation m1 m2 -> key_unique m1 -> key_unique m2.
  Proof.
    intros m1 m2 Hperm Hku. unfold key_unique in *.
    apply (Permutation_NoDup (keys_perm m1 m2 Hperm)). exact Hku.
  Qed.

  (* (AC4-map RHS) re-inserting a fixed entry with key k into the residual (which the match dropped k
     from) yields a key-unique map — the RHS reconstruction cannot smuggle a duplicate key. Uses
     `remove_key_drops_key` (k is gone from the residual) + `remove_key_preserves_uniqueness`. *)
  Theorem reinsert_preserves_uniqueness : forall k v m,
    key_unique m -> key_unique ((k, v) :: remove_key k m).
  Proof.
    intros k v m Hku. unfold key_unique. simpl.
    apply NoDup_cons_iff. split.
    - exact (remove_key_drops_key k m Hku).
    - exact (remove_key_preserves_uniqueness k m Hku).
  Qed.

  (* (AC4-map END-TO-END) KEY-UNIQUENESS SURVIVES THE SPLIT: given a key-unique SUBJECT map and its
     located reflection (a permutation), removing a matched key then re-inserting a fixed entry with
     that key yields a key-unique map. This is the composed reflect -> match -> RHS obligation: the
     map keys stay unique through the whole in-Rho AC-map firing. *)
  Theorem map_split_preserves_uniqueness : forall k v subject_map located_map,
    Permutation located_map subject_map ->
    key_unique subject_map ->
    key_unique ((k, v) :: remove_key k located_map).
  Proof.
    intros k v subject_map located_map Hperm Hku.
    apply reinsert_preserves_uniqueness.
    apply (key_unique_perm subject_map located_map (Permutation_sym Hperm)). exact Hku.
  Qed.

End AcMapKeyUniqueness.

(* ============================================================================================= *)
(* AC4-zip — the CORRELATION (a shared component across two picked elements) is preserved by the   *)
(* reflect -> match split. A `ZipAc` receiver picks two structured set elements CORRELATED by a     *)
(* shared component (the `Receive.condition` `EEq(a_0, a_1)`); the located set is a permutation of   *)
(* the subject set, so a correlated pair of located elements is exactly a correlated pair of subject *)
(* elements — the correlation the reducer enforces is the SUBJECT's, not an artifact of the spread.  *)
(* ============================================================================================= *)

Section AcZipCorrelation.

  Variable A B : Type.
  Definition ZipElem : Type := (A * B)%type.

  (* Two elements are CORRELATED when they share their first component (the `Pair(a, _)` key). *)
  Definition correlated (e1 e2 : ZipElem) : Prop := fst e1 = fst e2.

  (* (AC4-zip) CORRELATION PRESERVED: a correlated pair drawn from the LOCATED set is exactly a
     correlated pair drawn from the SUBJECT set, because `In` is permutation-invariant and the
     correlation is a property of the two elements themselves. So the paired match the reducer
     commits under the guard ranges over the subject's pairs, for any spread ordering. *)
  Theorem correlation_perm_invariant : forall (located subject : list ZipElem) e1 e2,
    Permutation located subject ->
    ((In e1 located /\ In e2 located /\ correlated e1 e2) <->
     (In e1 subject /\ In e2 subject /\ correlated e1 e2)).
  Proof.
    intros located subject e1 e2 Hperm. split.
    - intros [H1 [H2 Hc]]. split; [| split ].
      + apply (Permutation_in e1 Hperm). exact H1.
      + apply (Permutation_in e2 Hperm). exact H2.
      + exact Hc.
    - intros [H1 [H2 Hc]]. split; [| split ].
      + apply (Permutation_in e1 (Permutation_sym Hperm)). exact H1.
      + apply (Permutation_in e2 (Permutation_sym Hperm)). exact H2.
      + exact Hc.
  Qed.

End AcZipCorrelation.

Print Assumptions remove_key_preserves_uniqueness.
Print Assumptions remove_key_drops_key.
Print Assumptions remove_key_keeps_other.
Print Assumptions key_unique_perm.
Print Assumptions reinsert_preserves_uniqueness.
Print Assumptions map_split_preserves_uniqueness.
Print Assumptions correlation_perm_invariant.
