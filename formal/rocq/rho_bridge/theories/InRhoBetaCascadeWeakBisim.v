(*
 * InRhoBetaCascadeWeakBisim: the object-level beta reduction realized by the in-Rho
 * subst cascade (Stage 4 S-binder SLICE 2b) is WEAKLY BISIMILAR to abstract beta.
 *
 * ---------------------------------------------------------------------------------
 * THE STATEMENT (blueprint v2 section 6d)
 * ---------------------------------------------------------------------------------
 *
 * Object-beta `(lam b) a  ~>  b[a/0]` is the single VISIBLE label.  On the reducer the
 * beta redex fires as ONE COMM: the installed `Beta` sigma-receiver captures `(b, a)`
 * and SENDS the seed `^subst(Z, a, b, out)` on the reserved channel (this send is the
 * observable beta-fire).  The five reserved receivers then self-drive the substitution
 * cascade; every `^subst` / `^shift` / `^shiftk` / `^cmp` / `^pred` COMM is INTERNAL
 * (tau).  We prove the two systems are weakly bisimilar:
 *
 *   weak_bisim_beta_cascade_vs_abstract_beta
 *      : is_weak_bisimulation R (awvis) (cwvis)      with   R o c := norm c = o
 *
 * where the abstract system (`awvis`, on `Obj`) takes one visible beta step to
 * `odbeta a b = b[a/0]`, and the concrete system (`cwvis`, on `Tm`) takes tau* (reflect
 * the redex), one visible COMM (`cbeta`, the seed send), then tau* (the cascade).  The
 * bisimulation relation `R o c := norm c = o` identifies a concrete term with the
 * abstract object it evaluates to; it is preserved because the tau-cascade PRESERVES
 * `norm` (`step_preserves_norm`) and the visible seed's `norm` is exactly `odbeta a b`
 * (`subst_normal_form_is_debruijn_beta`).
 *
 * ---------------------------------------------------------------------------------
 * WHY THIS IS A GENUINE REDUCTION BISIMULATION (and not the vacuous tau-erasure trap)
 * ---------------------------------------------------------------------------------
 *
 * `advanced_automata/InRhoSameCLTSWeakBisim.v` proves channel-SCHEME independence: its
 * tau backbone ERASES arbitrary tau prefixes to `[]`, so an inert step re-proves the
 * bisimulation VACUOUSLY (it never inspects what the tau steps compute).  This file is
 * modeled instead on `CommReductionCorrespondence.v`: the tau steps here ARE the real
 * TRS reductions `step`, and the up-to-tau target is pinned down by
 * `DeBruijnSubstTRS.v`'s STRONG NORMALIZATION + CONFLUENCE: the cascade from the seed
 * reaches the UNIQUE normal form `embed (b[a/0])` (`cascade_target_well_defined`).
 * `beta_cascade_is_nonvacuous` exhibits a concrete redex whose cascade takes real steps
 * and lands on the correct reduct, so the matching is not vacuously satisfiable.
 *
 * Rocq 9.1 compatible.  No Admitted, no Axioms, no Assumptions, no Parameters.
 *)

From Stdlib Require Import List.
From RhoBridge Require Import DeBruijnSubstTRS.

Import ListNotations.

Section InRhoBetaCascadeWeakBisim.

  (* =============================================================================
     1.  The two labelled transition systems.
     ============================================================================= *)

  (* ABSTRACT beta on object terms: `(lam b) a  ~>  b[a/0]`, at an application node
     `oNode op [oLam b; a]` (the reserved App op id `op` is the visible label). *)
  Inductive abeta (op : nat) : Obj -> Obj -> Prop :=
    | abeta_fire : forall b a,
        abeta op (oNode op [oLam b; a]) (odbeta a b).

  (* CONCRETE: the ONE visible COMM of the in-Rho beta fire.  The `Beta` sigma-receiver,
     given the reflected redex `App(^lambda(b), a) = tNode op [tLam b'; a']` (with
     `b' = embed b`, `a' = embed a`), SENDS the seed `^subst(Z, a, b, out)` -- modeled as
     the transition to `tSubst 0 (embed a) (embed b)`.  This is the single observable
     action; everything after is the tau-cascade `step`. *)
  Inductive cbeta (op : nat) : Tm -> Tm -> Prop :=
    | cbeta_fire : forall b a,
        cbeta op (tNode op [tLam (embed b); embed a]) (tSubst 0 (embed a) (embed b)).

  (* The concrete WEAK visible transition: tau* (reflect / locate the redex), one visible
     COMM, then tau* (the substitution cascade). *)
  Definition cwvis (op : nat) (c c' : Tm) : Prop :=
    exists c1 c2, star c c1 /\ cbeta op c1 c2 /\ star c2 c'.

  (* The abstract system has no internal action, so its weak visible transition IS the
     strong one (kept as a definition for symmetry with `cwvis`). *)
  Definition awvis (op : nat) (o o' : Obj) : Prop := abeta op o o'.

  (* The two-clause weak bisimulation, in the shape of
     advanced_automata/RegisterEquivalence's `is_bisimulation` / InRhoSameCLTSWeakBisim's
     `is_weak_bisimulation`, but with the CONCRETE reduction transitions above. *)
  Definition is_weak_bisimulation
      (R : Obj -> Tm -> Prop)
      (t1 : nat -> Obj -> Obj -> Prop) (t2 : nat -> Tm -> Tm -> Prop) : Prop :=
    (forall o c op o', R o c -> t1 op o o' ->
        exists c', t2 op c c' /\ R o' c')
    /\ (forall o c op c', R o c -> t2 op c c' ->
        exists o', t1 op o o' /\ R o' c').

  (* The bisimulation relation: a concrete term REPRESENTS the abstract object it
     evaluates to (`norm c` collapses the whole cascade). *)
  Definition represents (o : Obj) (c : Tm) : Prop := norm c = o.

  (* =============================================================================
     2.  Reflection of the redex (the tau prefix) and the cascade (the tau suffix).
     ============================================================================= *)

  (* `embed` of an application node is the reflected App-over-lambda redex. *)
  Lemma embed_app_lam : forall op b a,
    embed (oNode op [oLam b; a]) = tNode op [tLam (embed b); embed a].
  Proof. reflexivity. Qed.

  (* A concrete term representing an application object tau*-reduces to the reflected
     redex (via `reduces_to_norm`) -- the tau PREFIX that locates / reflects the redex
     the sigma-receiver then fires on. *)
  Lemma reduces_to_reflected_redex : forall op b a c,
    represents (oNode op [oLam b; a]) c ->
    star c (tNode op [tLam (embed b); embed a]).
  Proof.
    intros op b a c Hrep. unfold represents in Hrep.
    pose proof (reduces_to_norm c) as Hred.
    rewrite Hrep in Hred. rewrite embed_app_lam in Hred. exact Hred.
  Qed.

  (* The seed's `norm` is exactly the de-Bruijn beta reduct (the tau SUFFIX collapses to
     `b[a/0]`); a restatement of `subst_normal_form_is_debruijn_beta`. *)
  Lemma seed_norm_is_beta : forall a b,
    norm (tSubst 0 (embed a) (embed b)) = odbeta a b.
  Proof. intros a b. apply subst_normal_form_is_debruijn_beta. Qed.

  (* =============================================================================
     3.  The weak bisimulation.
     ============================================================================= *)

  (* FORWARD (abstract simulated by concrete): an abstract beta step is matched by the
     in-Rho weak visible transition -- reflect the redex (tau-star), fire the seed COMM,
     and the seed represents the abstract reduct. *)
  Lemma forward_simulation : forall o c op o',
    represents o c -> awvis op o o' ->
    exists c', cwvis op c c' /\ represents o' c'.
  Proof.
    intros o c op o' Hrep Hstep. unfold awvis in Hstep.
    inversion Hstep as [b a Hlhs Hrhs]. subst o o'.
    exists (tSubst 0 (embed a) (embed b)). split.
    - (* cwvis: tau* to the reflected redex, then the one visible COMM, then no tau *)
      exists (tNode op [tLam (embed b); embed a]), (tSubst 0 (embed a) (embed b)).
      split; [| split].
      + apply reduces_to_reflected_redex. exact Hrep.
      + apply cbeta_fire.
      + apply star_refl.
    - (* the seed represents the abstract reduct b[a/0] *)
      unfold represents. apply seed_norm_is_beta.
  Qed.

  (* BACKWARD (concrete simulated by abstract): an in-Rho weak visible transition is
     matched by an abstract beta step.  The tau-prefix cannot change `norm`, so the fired
     redex has `norm = oNode op [oLam b; a]`; the tau-suffix preserves `norm`, so the
     result represents `b[a/0]`. *)
  Lemma backward_simulation : forall o c op c',
    represents o c -> cwvis op c c' ->
    exists o', awvis op o o' /\ represents o' c'.
  Proof.
    intros o c op c' Hrep Hcwvis.
    destruct Hcwvis as [c1 [c2 [Hpre [Hcomm Hpost]]]].
    inversion Hcomm as [b a Hc1 Hc2]. subst c1 c2.
    exists (odbeta a b). split.
    - (* the abstract system fires beta at the same App node *)
      unfold awvis.
      assert (Ho : o = oNode op [oLam b; a]).
      { unfold represents in Hrep. rewrite <- Hrep.
        rewrite (star_preserves_norm c (tNode op [tLam (embed b); embed a]) Hpre).
        simpl. rewrite !norm_embed. reflexivity. }
      rewrite Ho. apply abeta_fire.
    - (* the tau-suffix preserves norm; the seed's norm is b[a/0] *)
      unfold represents.
      rewrite <- (star_preserves_norm _ c' Hpost).
      apply seed_norm_is_beta.
  Qed.

  (* THE WEAK BISIMULATION: `represents` (norm-equality) is a weak bisimulation between
     abstract beta and the in-Rho beta-with-subst-cascade. *)
  Theorem weak_bisim_beta_cascade_vs_abstract_beta :
    is_weak_bisimulation represents awvis cwvis.
  Proof.
    split.
    - exact forward_simulation.
    - exact backward_simulation.
  Qed.

  (* =============================================================================
     4.  The up-to-tau target is well defined (SN + CR) and the matching non-vacuous.
     ============================================================================= *)

  (* THE UP-TO-TAU TARGET IS WELL DEFINED (blueprint section 6d): from the seed
     `subst(0, a, b)`, EVERY normal form the cascade can reach -- under ANY RSpace
     interleaving of the tau-COMMs -- is the UNIQUE `embed (b[a/0])`.  Directly from
     `DeBruijnSubstTRS`'s confluence + termination (`subst_trs_unique_nf`). *)
  Theorem cascade_target_well_defined : forall a b u,
    star (tSubst 0 (embed a) (embed b)) u -> is_obj u = true ->
    u = embed (odbeta a b).
  Proof.
    intros a b u Hstar Hobj.
    apply (beta_seed_unique_nf_is_debruijn_beta a b u Hstar Hobj).
  Qed.

  (* The whole visible-then-tau path reaches exactly the reflected beta reduct: the
     concrete weak visible transition from the reflected redex to `embed (b[a/0])`. *)
  Theorem beta_fire_then_cascade_reaches_reduct : forall op a b,
    cwvis op (tNode op [tLam (embed b); embed a]) (embed (odbeta a b)).
  Proof.
    intros op a b.
    exists (tNode op [tLam (embed b); embed a]), (tSubst 0 (embed a) (embed b)).
    split; [| split].
    - apply star_refl.
    - apply cbeta_fire.
    - apply beta_cascade_reaches_debruijn_nf.
  Qed.

  (* NON-VACUITY (the trap `InRhoSameCLTSWeakBisim` cannot rule out): a concrete beta
     redex whose tau-cascade does REAL work.  `(lam. ^bound 0) (^free A)` fires to the
     seed, which takes >= 1 genuine `step` and normalizes to `^free A` -- so the tau
     backbone is NOT inert and the bisimulation is not vacuously satisfied. *)
  Definition witness_redex (op x : nat) : Tm :=
    tNode op [tLam (tBound 0); tFree x].

  Theorem beta_cascade_is_nonvacuous : forall op x,
    (* the visible fire produces the seed *)
    cbeta op (witness_redex op x) (tSubst 0 (tFree x) (tBound 0))
    (* the seed takes a real (non-reflexive) tau step ... *)
    /\ (exists u, tSubst 0 (tFree x) (tBound 0) <> u
                  /\ step (tSubst 0 (tFree x) (tBound 0)) u)
    (* ... and the whole cascade lands on the beta reduct ^free x *)
    /\ star (tSubst 0 (tFree x) (tBound 0)) (tFree x).
  Proof.
    intros op x. split; [| split].
    - (* cbeta on the witness: embed (oBound 0) = tBound 0, embed (oFree x) = tFree x *)
      exact (cbeta_fire op (oBound 0) (oFree x)).
    - (* subst(0, free x, bound 0) -> shiftk 0 (free x) (a real step, n = j = 0 => Eq) *)
      exists (tShiftk 0 (tFree x)). split.
      + discriminate.
      + apply s_head.
        assert (Hs := h_subst_bound 0 (tFree x) 0). simpl in Hs. exact Hs.
    - (* the cascade: subst -> shiftk 0 (free x) -> free x *)
      eapply star_cons.
      + apply s_head.
        assert (Hs := h_subst_bound 0 (tFree x) 0). simpl in Hs. exact Hs.
      + apply star_one. apply s_head. apply h_shiftk_zero.
  Qed.

End InRhoBetaCascadeWeakBisim.

(* Zero-admission confirmation. *)
Print Assumptions weak_bisim_beta_cascade_vs_abstract_beta.
Print Assumptions cascade_target_well_defined.
Print Assumptions beta_fire_then_cascade_reaches_reduct.
Print Assumptions beta_cascade_is_nonvacuous.
