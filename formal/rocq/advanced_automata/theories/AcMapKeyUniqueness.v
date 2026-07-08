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

End AcMapKeyUniqueness.

Print Assumptions remove_key_preserves_uniqueness.
Print Assumptions remove_key_drops_key.
Print Assumptions remove_key_keeps_other.
