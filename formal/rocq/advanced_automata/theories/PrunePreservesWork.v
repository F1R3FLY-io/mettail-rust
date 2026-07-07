(*
 * PrunePreservesWork: obligation O2 of the in-Rho matching verification plan
 * (docs 16). The P2 config-tree `prune(ct, p)` — removing the matched positions
 * at/below p after an inner rewrite fires — preserves the OUTER matching work: it
 * never adds a position, positions strictly outside p survive, positions at/below p
 * are removed, and the surviving for-receives stay distinct/valid. This is the
 * cross-rewrite-step optimization (P2 Lemma 1, `[optimal]` Thm 5.2 = `thm:prune-
 * preserves`) transported to the in-Rho location-channel scheme.
 *
 * Model boundary (plan 16 section 0, consistent with Phase A): prune is modeled
 * structurally over the surface `positions` / `chan` map of SymbolOnceInjective —
 * "no for-receive outside p is added or invalidated" — not over an operational Rho
 * frame. An operational O2 (persistence across an actual COMM) belongs beside (iii)
 * in Phase C.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool PeanoNat List.
Import ListNotations.
From AdvancedAutomata Require Import PositionalSetAutomatonSound.
From AdvancedAutomata Require Import SymbolOnceInjective.

(* p is a Dewey prefix of q (p at-or-above q in the term tree). *)
Fixpoint prefix (p q : Position) : bool :=
  match p, q with
  | [], _ => true
  | _ :: _, [] => false
  | a :: p', b :: q' => Nat.eqb a b && prefix p' q'
  end.

(* Prune the config-tree at p: drop every position at/below p (the inner redex's
   own matching work), keep the rest (the outer work still to do). *)
Definition prune (P : list Position) (p : Position) : list Position :=
  filter (fun q => negb (prefix p q)) P.

(* A self-contained "injective map preserves NoDup under a filter" (a filtered
   sublist of a NoDup image is NoDup). *)
Lemma nodup_map_filter {A B} (f : A -> B) (g : A -> bool) (l : list A) :
  NoDup (map f l) -> NoDup (map f (filter g l)).
Proof.
  induction l as [| x l' IH]; simpl; intro H.
  - constructor.
  - inversion H as [| h t Hnotin Hnd Heq]; subst.
    destruct (g x) eqn:Hg; simpl.
    + constructor.
      * intro Hin. apply Hnotin.
        apply in_map_iff in Hin. destruct Hin as [y [Hfy Hiny]].
        apply filter_In in Hiny. destruct Hiny as [Hiny _].
        apply in_map_iff. exists y. split; [exact Hfy | exact Hiny].
      * apply IH. exact Hnd.
    + apply IH. exact Hnd.
Qed.

(* ---- prune never ADDS a position (prune ct <= ct) ---- *)
Theorem prune_subset : forall P p, incl (prune P p) P.
Proof.
  intros P p x Hin. unfold prune in Hin. apply filter_In in Hin. destruct Hin as [Hin _]. exact Hin.
Qed.

(* ---- positions strictly OUTSIDE p survive (outer for-receives stay live) ---- *)
Theorem prune_preserves_outside : forall P p q,
  In q P -> prefix p q = false -> In q (prune P p).
Proof.
  intros P p q Hin Hpre. unfold prune. apply filter_In. split.
  - exact Hin.
  - rewrite Hpre. reflexivity.
Qed.

(* ---- positions at/below p are removed (the inner redex's own work) ---- *)
Theorem prune_removes_below : forall P p q,
  prefix p q = true -> ~ In q (prune P p).
Proof.
  intros P p q Hpre Hin. unfold prune in Hin. apply filter_In in Hin.
  destruct Hin as [_ Hf]. rewrite Hpre in Hf. discriminate Hf.
Qed.

(* ---- the surviving for-receives remain distinct/valid (O1 preserved) ---- *)
Theorem prune_preserves_receives : forall op args site p,
  NoDup (map (chan site op) (prune (positions (PApp op args)) p)).
Proof.
  intros op args site p. unfold prune.
  apply nodup_map_filter. apply chan_injective_on_positions.
Qed.

Print Assumptions prune_subset.
Print Assumptions prune_preserves_outside.
Print Assumptions prune_removes_below.
Print Assumptions prune_preserves_receives.
