(*
 * StftWiringSound: soundness of WIRING the symbolic tree transducer
 * (prattail/src/sym_tree_transducer.rs) into the backward-type-reasoning
 * analysis layer (OSLF Phase 4 wiring lemma).
 *
 * The functional transducer model mirrors the shipped composition proof
 * `StftComposition.v` (formal/rocq/sft): a transducer is `X -> list Y` and
 * composition is `ft_compose f g := fun t => flat_map g (f t)`
 * (StftComposition.v:22,277) = the Rust `compose_transduce()`
 * (StftComposition.v:50). `StftComposition.v` proves the OUTPUT-level laws
 * (left/right identity, associativity). This file adds the DOMAIN-level wiring
 * theorem backward typing needs: the pre-image (`domain_sta()` / `is_total`,
 * sym_tree_transducer.rs:206,224) of a COMPOSED cast factors through the
 * intermediate domain — so computing a cast's pre-image and composing casts is
 * sound backward type reasoning over a rewrite `r : src -> tgt`.
 *
 * Theorems:
 *   - ft_compose_left_id / right_id : identity-cast laws (mirror StftComposition).
 *   - ft_compose_assoc       : cast chaining is associative (mirror StftComposition).
 *   - cast_preimage_factors  : `t` reaches the final target through `compose f g`
 *       iff `t` produces some intermediate `u` (∈ f t) that is itself in `g`'s
 *       domain (reaches the target) — the backward-typing soundness of
 *       pre-image composition (NEW; StftComposition proves only output laws).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
Import ListNotations.

Section StftWiring.
  (* Trees / payloads are opaque: the composition + domain laws never inspect
     their structure (mirrors StftComposition's parametric `Tree X`). *)

  Definition ft (A B : Type) := A -> list B.
  Definition ft_apply {A B} (f : ft A B) (t : A) : list B := f t.
  Definition ft_compose {A B C} (f : ft A B) (g : ft B C) : ft A C :=
    fun t => flat_map g (f t).
  Definition ft_identity {A} : ft A A := fun t => [t].

  (* A source term is in a transducer's DOMAIN iff it produces some output — the
     Rust `domain_sta()` accept-set / `is_total` predicate. *)
  Definition in_domain {A B} (f : ft A B) (t : A) : Prop := f t <> [].

  Lemma nonempty_iff_exists_In {A} (l : list A) : l <> [] <-> exists y, In y l.
  Proof.
    destruct l as [| a l'].
    - split; [intro H; exfalso; apply H; reflexivity | intros [y Hy]; inversion Hy].
    - split; [intros _; exists a; left; reflexivity | intros _; discriminate].
  Qed.

  Theorem ft_compose_left_id {A B} (g : ft A B) (t : A) :
    ft_apply (ft_compose ft_identity g) t = ft_apply g t.
  Proof.
    unfold ft_apply, ft_compose, ft_identity. simpl. rewrite app_nil_r. reflexivity.
  Qed.

  Theorem ft_compose_right_id {A B} (f : ft A B) (t : A) :
    ft_apply (ft_compose f (fun x : B => [x])) t = ft_apply f t.
  Proof.
    unfold ft_apply, ft_compose. induction (f t) as [| x xs IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Theorem ft_compose_assoc {A B C D}
    (f : ft A B) (g : ft B C) (h : ft C D) (t : A) :
    ft_apply (ft_compose (ft_compose f g) h) t
    = ft_apply (ft_compose f (ft_compose g h)) t.
  Proof.
    unfold ft_apply, ft_compose. induction (f t) as [| x xs IH].
    - reflexivity.
    - simpl. rewrite flat_map_app. rewrite IH. reflexivity.
  Qed.

  (* THE wiring soundness: backward typing via pre-image composition. `t` reaches
     the final target through `compose f g` iff `t` produces some intermediate
     `u` that is itself in `g`'s domain. Reuses stdlib `in_flat_map`. *)
  Theorem cast_preimage_factors {A B C} (f : ft A B) (g : ft B C) (t : A) :
    in_domain (ft_compose f g) t
    <-> exists u, In u (f t) /\ in_domain g u.
  Proof.
    unfold in_domain, ft_compose.
    rewrite nonempty_iff_exists_In.
    split.
    - intros [y Hy]. apply in_flat_map in Hy. destruct Hy as [u [Hu Hyu]].
      exists u. split; [exact Hu |]. rewrite nonempty_iff_exists_In. exists y. exact Hyu.
    - intros [u [Hu Hdom]]. rewrite nonempty_iff_exists_In in Hdom.
      destruct Hdom as [y Hy]. exists y. apply in_flat_map. exists u. split; [exact Hu | exact Hy].
  Qed.

  Print Assumptions ft_compose_assoc.
  Print Assumptions cast_preimage_factors.

End StftWiring.
