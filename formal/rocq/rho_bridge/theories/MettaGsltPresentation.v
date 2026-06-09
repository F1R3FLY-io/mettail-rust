(*
 * MettaGsltPresentation: the MeTTaIL GSLT presentation (`MettaGslt` / `MettaSig`,
 * mettail-rho-adapter) re-presents f1r3node-rust's deploy-signature lane algebra
 * FAITHFULLY — its `split_join_decompositions` (delegated to the host `Sig`'s)
 * enumerates EXACTLY the split/join (⊗) decompositions of the signature: every
 * decomposition it emits is a real `And`-node decomposition (SOUND), and every
 * `And` subterm's decomposition is emitted (COMPLETE). No decomposition is
 * fabricated and none is missed — the lane structure the OSLF funding analysis
 * relies on is preserved by the MeTTaIL re-presentation.
 *
 * Model: the host `Sig` is a binary tree of `Ground` leaves and `And` (split/join,
 * ⊗) nodes (f1r3node-rust rholang/.../accounting/mod.rs:1260; the
 * `ResourceSignature::split_join_decompositions` impl, resource_logic.rs:89-99,
 * recurses on `Sig::And`). `MettaSig` wraps `Sig` and delegates `key` and
 * `split_join_decompositions` to it (mettail-rho-adapter `gslt.rs`), so the host's
 * decomposition algebra IS MeTTaIL's — this file proves that algebra
 * sound+complete (and structurally terminating, as a Coq `Fixpoint`).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
Import ListNotations.

Section MettaGsltPresentation.

  (* A deploy signature: Ground leaves carrying a lane key, And (⊗) split/join. *)
  Inductive Sig : Type :=
    | Ground : nat -> Sig
    | And    : Sig -> Sig -> Sig.

  (* The lane key (modelling `Sig::key`/`lane_hash`: distinct shapes ⇒ distinct
     keys; here a structural key suffices to state soundness/completeness). *)
  Fixpoint sig_key (s : Sig) : nat :=
    match s with
    | Ground k => k
    | And l r  => 1 + sig_key l + sig_key r
    end.

  (* `split_join_decompositions`: for each `And` node, emit its (compound, left,
     right) lane-key decomposition, then recurse into both operands — exactly the
     host impl (resource_logic.rs:89-99), which `MettaSig` delegates to. *)
  Fixpoint decompositions (s : Sig) : list (nat * nat * nat) :=
    match s with
    | Ground _ => []
    | And l r  =>
        (sig_key (And l r), sig_key l, sig_key r)
          :: (decompositions l ++ decompositions r)
    end.

  (* `x` occurs as a subterm of `s`. *)
  Inductive subterm : Sig -> Sig -> Prop :=
    | sub_refl : forall s, subterm s s
    | sub_l    : forall x l r, subterm x l -> subterm x (And l r)
    | sub_r    : forall x l r, subterm x r -> subterm x (And l r).

  (* SOUNDNESS: every emitted decomposition is a real `And` subterm's split — no
     decomposition is fabricated. *)
  Theorem decompositions_sound : forall s c a b,
    In (c, a, b) (decompositions s) ->
    exists l r,
      subterm (And l r) s
      /\ c = sig_key (And l r) /\ a = sig_key l /\ b = sig_key r.
  Proof.
    induction s as [k | x IHx y IHy]; intros c a b H.
    - simpl in H. contradiction.
    - simpl in H. destruct H as [Heq | Hin].
      + (* the head: this very `And x y` *)
        inversion Heq; subst. exists x, y.
        split; [apply sub_refl | repeat split].
      + apply in_app_or in Hin. destruct Hin as [Hl | Hr].
        * destruct (IHx c a b Hl) as [l [r [Hsub [Hc [Ha Hb]]]]].
          exists l, r. split; [apply sub_l; exact Hsub | repeat split; assumption].
        * destruct (IHy c a b Hr) as [l [r [Hsub [Hc [Ha Hb]]]]].
          exists l, r. split; [apply sub_r; exact Hsub | repeat split; assumption].
  Qed.

  (* COMPLETENESS: every `And` subterm's decomposition is emitted — none is
     missed. *)
  Theorem decompositions_complete : forall s l r,
    subterm (And l r) s ->
    In (sig_key (And l r), sig_key l, sig_key r) (decompositions s).
  Proof.
    induction s as [k | x IHx y IHy]; intros l r H.
    - exfalso. inversion H.
    - inversion H; subst.
      + (* sub_refl: And l r = And x y *) simpl. left. reflexivity.
      + (* sub_l: subterm (And l r) x *) simpl. right. apply in_or_app. left.
        apply IHx. assumption.
      + (* sub_r: subterm (And l r) y *) simpl. right. apply in_or_app. right.
        apply IHy. assumption.
  Qed.

  (* The two together: the emitted decomposition set is EXACTLY the set of
     `And`-subterm decompositions — faithful re-presentation of the lane algebra. *)
  Theorem decompositions_characterization : forall s c a b,
    In (c, a, b) (decompositions s)
    <-> (exists l r,
           subterm (And l r) s
           /\ c = sig_key (And l r) /\ a = sig_key l /\ b = sig_key r).
  Proof.
    intros s c a b. split.
    - apply decompositions_sound.
    - intros [l [r [Hsub [Hc [Ha Hb]]]]]. subst.
      apply decompositions_complete. exact Hsub.
  Qed.

End MettaGsltPresentation.
