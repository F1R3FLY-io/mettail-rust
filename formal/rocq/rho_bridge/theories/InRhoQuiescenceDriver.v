(*
 * InRhoQuiescenceDriver: the A-S5.2 in-Rho self-re-spreading QUIESCENCE DRIVER (the
 * generated `^drive` receiver family, Lambda core, PS value carrier) modeled as a
 * big-step LTS over the reflected object fragment — soundness, per-trace quiescence,
 * typed fuel exhaustion, and the ITERATED beta weak bisimulation.
 *
 * ---------------------------------------------------------------------------------
 * WHAT IS MODELED (and at what level)
 * ---------------------------------------------------------------------------------
 *
 * The driver (rholang-codegen/src/rho_net_drive.rs) is ONE persistent receiver
 * `^drive(t, fuel, ret)` whose Match arms realize, per driven node:
 *
 *   1. the REDEX arm (Lambda: `App(^lambda(b), a)`), fuel-gated (ground 0 case FIRST),
 *      firing through the sigma ABI — the installed beta SEED + subst TRS compute the
 *      contractum, which is RE-DRIVEN with `fuel - 1`;
 *   2. the CONGRUENCE-DESCENT arm: concurrent child drives (fuel COPIED, not
 *      decremented — per-path semantics), an atomic join, and the inline POST-JOIN
 *      RE-CHECK of the reassembled node against the redex arms only;
 *   3. the BINDER arm: drive the body, rewrap (NO post-rewrap re-check for Lambda —
 *      no compiled entry root is the binder tag; see
 *      `binder_rewrap_needs_no_recheck` below for the discharged emission rule);
 *   4. leaf / `^free` / `^bound` passthroughs; a typed `^drive-err` wildcard.
 *
 * Following the task mandate, the driver is modeled as an LTS over the ABSTRACT term
 * fragment (`Obj`/`Tm` of DeBruijnSubstTRS), NOT the emitted `Par`: the big-step
 * relation `drives op fuel t r` (mutually with `recheck`, the post-join re-check)
 * mirrors the arm structure exactly — one constructor per arm disposition, the fuel
 * decrement ONLY on firing, descent copying fuel, and the result type `dres`
 * separating the quiescent value (`DDone`, the OUT datum) from the typed fuel
 * exhaustion (`DFuel`, the `^drive-fuel` datum). The `^drive-err` wildcard is modeled
 * by PARTIALITY: an out-of-fragment term has no `drives` derivation, exactly as the
 * real arm publishes no OUT value.
 *
 * The FIRING clause's contractum is `odbeta a b` — justified by the SN + CONFLUENCE
 * instantiation of `DeBruijnSubstTRS.v` exactly as
 * `InRhoBetaCascadeWeakBisim.cascade_target_well_defined` consumes it: from the seed
 * `subst(0, a, b)` EVERY normal form the in-Rho cascade can reach under ANY RSpace
 * interleaving is the UNIQUE `embed (b[a/0])`, so the model's firing result is the
 * only value the real cascade can deliver to the fresh return.
 *
 * ---------------------------------------------------------------------------------
 * THE THEOREMS
 * ---------------------------------------------------------------------------------
 *
 *   drive_steps_sound          : a DDone drive is an iterated object-level beta
 *                                reduction (each firing = a genuine beta step at the
 *                                fired position; contextual closure `obeta`).
 *   quiescence_sound           : PER-TRACE (decision (3)): EVERY derivation ending in
 *                                `DDone v` yields a beta-NORMAL `v` (the host NF-scan
 *                                mirror `lam_nf`), by the structural induction whose
 *                                join RE-CHECK case carries the children-normal
 *                                hypothesis — the F14-confirmed induction.
 *   fuel_exhaustion_never_wrong: a `DFuel u` trace surfaces the STUCK REDEX itself —
 *                                typed, never mistakable for a normal form
 *                                (`exhaustion_datum_is_not_nf`), and constructor-
 *                                disjoint from any NF claim.
 *   drive_weak_bisim           : the ITERATED beta weak bisimulation — `represents`
 *                                is a weak bisimulation between iterated abstract
 *                                beta chains (`aiter`) and iterated in-Rho
 *                                fire-plus-cascade chains (`citer`), in the SAME
 *                                two-clause `is_weak_bisimulation` shape as
 *                                InRhoBetaCascadeWeakBisim (whose single-fire clauses
 *                                — resting on the SN+CR-unique cascade target — are
 *                                lifted pointwise). This is the single-step → iterated
 *                                upgrade the WholeGsltInRhoOpCorrespondence premises
 *                                consume in A-S5.7.
 *   drive_two_firing_nonvacuous: the TWO-firing witness `(lam.0) ((lam.0) x^)`: a
 *                                fuel-2 model derivation to `DDone (oFree x)` AND the
 *                                matching two-step iterated concrete transition —
 *                                the model's firing chain and the in-Rho weak
 *                                transitions land on the same represented NF (and the
 *                                final leaf drive at fuel 0 witnesses that
 *                                descent/leaves never consult fuel).
 *
 * Rocq 9.1 compatible.  No Admitted, no Axioms, no Assumptions, no Parameters.
 *)

From Stdlib Require Import List.
From RhoBridge Require Import DeBruijnSubstTRS InRhoBetaCascadeWeakBisim.

Import ListNotations.

(* The drive RESULT: the quiescent value (the OUT datum) or the typed fuel-exhaustion
   datum (the `^drive-fuel` payload).  Constructor disjointness IS the "typed label,
   never a visible NF claim" separation: no derivation can confuse the two. *)
Inductive dres : Type :=
  | DDone : Obj -> dres
  | DFuel : Obj -> dres.

Section DriverModel.

  (* The one entry-root op of the Lambda fragment (the reflected `App` tag). *)
  Variable op : nat.

  (* `v` is NOT a beta redex at this node (the wildcard side of the redex Match arm —
     the driver's arm ORDER: the redex pattern is tried first, so descent/re-check
     default arms carry exactly this negative premise). *)
  Definition not_beta_redex (v : Obj) : Prop :=
    forall b a, v <> oNode op [oLam b; a].

  (* The host NF-scan mirror (plan v2 section 4.7): beta-normal forms of the driven
     Lambda fragment — no `App(^lambda(_), _)` node present.  `nf_app`'s third premise
     is the scan's redex test at the node. *)
  Inductive lam_nf : Obj -> Prop :=
    | nf_free  : forall x, lam_nf (oFree x)
    | nf_bound : forall n, lam_nf (oBound n)
    | nf_lam   : forall b, lam_nf b -> lam_nf (oLam b)
    | nf_app   : forall t1 t2,
        lam_nf t1 -> lam_nf t2 -> (forall b, t1 <> oLam b) ->
        lam_nf (oNode op [t1; t2]).

  (* Object-level ONE-STEP beta at any driver-reachable position: the contextual
     closure of the root fire over the binary-App / lambda fragment.  Each `drives`
     firing is one of these (drive_steps_sound). *)
  Inductive obeta : Obj -> Obj -> Prop :=
    | ob_fire : forall b a, obeta (oNode op [oLam b; a]) (odbeta a b)
    | ob_appl : forall t1 t1' t2,
        obeta t1 t1' -> obeta (oNode op [t1; t2]) (oNode op [t1'; t2])
    | ob_appr : forall t1 t2 t2',
        obeta t2 t2' -> obeta (oNode op [t1; t2]) (oNode op [t1; t2'])
    | ob_lam : forall b b', obeta b b' -> obeta (oLam b) (oLam b').

  Inductive ostar : Obj -> Obj -> Prop :=
    | ostar_refl : forall t, ostar t t
    | ostar_cons : forall t u v, obeta t u -> ostar u v -> ostar t v.

  Lemma ostar_trans : forall t u v, ostar t u -> ostar u v -> ostar t v.
  Proof.
    intros t u v Htu Huv. induction Htu as [t | t w u Hstep Htu IH].
    - exact Huv.
    - eapply ostar_cons; [exact Hstep | apply IH; exact Huv].
  Qed.

  Lemma ostar_appl : forall t1 t1' t2,
    ostar t1 t1' -> ostar (oNode op [t1; t2]) (oNode op [t1'; t2]).
  Proof.
    intros t1 t1' t2 H. induction H as [t | t w u Hstep H IH].
    - apply ostar_refl.
    - eapply ostar_cons; [apply ob_appl; exact Hstep | exact IH].
  Qed.

  Lemma ostar_appr : forall t1 t2 t2',
    ostar t2 t2' -> ostar (oNode op [t1; t2]) (oNode op [t1; t2']).
  Proof.
    intros t1 t2 t2' H. induction H as [t | t w u Hstep H IH].
    - apply ostar_refl.
    - eapply ostar_cons; [apply ob_appr; exact Hstep | exact IH].
  Qed.

  Lemma ostar_lam : forall b b', ostar b b' -> ostar (oLam b) (oLam b').
  Proof.
    intros b b' H. induction H as [t | t w u Hstep H IH].
    - apply ostar_refl.
    - eapply ostar_cons; [apply ob_lam; exact Hstep | exact IH].
  Qed.

  (* =============================================================================
     The driver big-step model: `drives fuel t r` mutually with the post-join
     `recheck` — ONE constructor per generated arm disposition (see the header for
     the arm-by-arm correspondence).
     ============================================================================= *)

  Inductive drives : nat -> Obj -> dres -> Prop :=
    (* leaf / reserved passthrough arms: inert, fuel NOT consulted. *)
    | d_free : forall fuel x, drives fuel (oFree x) (DDone (oFree x))
    | d_bound : forall fuel n, drives fuel (oBound n) (DDone (oBound n))
    (* the binder arm: drive the body, rewrap; NO post-rewrap re-check (no compiled
       entry root is the binder tag — the emission rule, discharged for this fragment
       by `binder_rewrap_needs_no_recheck`).  A body exhaustion propagates the typed
       datum (the join never fires, OUT never lands). *)
    | d_lam_done : forall fuel b v,
        drives fuel b (DDone v) -> drives fuel (oLam b) (DDone (oLam v))
    | d_lam_fuel : forall fuel b u,
        drives fuel b (DFuel u) -> drives fuel (oLam b) (DFuel u)
    (* the redex arm, fuel-gated: ground 0 FIRST (the typed exhaustion datum is the
       stuck redex node itself — the `rebuild_from_pattern` datum), else FIRE (the
       cascade's SN+CR-unique value `odbeta a b`) and RE-DRIVE with `fuel - 1`. *)
    | d_redex_fuel0 : forall b a,
        drives 0 (oNode op [oLam b; a]) (DFuel (oNode op [oLam b; a]))
    | d_redex_fire : forall f b a r,
        drives f (odbeta a b) r -> drives (S f) (oNode op [oLam b; a]) r
    (* the congruence-descent arm (redex arm did NOT match): concurrent child drives
       with the SAME fuel (per-path — descent never decrements), the atomic join, then
       the inline post-join re-check of the reassembled node. *)
    | d_descend_done : forall fuel t1 t2 v1 v2 r,
        not_beta_redex (oNode op [t1; t2]) ->
        drives fuel t1 (DDone v1) ->
        drives fuel t2 (DDone v2) ->
        recheck fuel (oNode op [v1; v2]) r ->
        drives fuel (oNode op [t1; t2]) r
    (* a child exhaustion: the join never fires; the trace ends with the child's typed
       datum (OUT never lands). *)
    | d_descend_fuel_l : forall fuel t1 t2 u,
        not_beta_redex (oNode op [t1; t2]) ->
        drives fuel t1 (DFuel u) ->
        drives fuel (oNode op [t1; t2]) (DFuel u)
    | d_descend_fuel_r : forall fuel t1 t2 u,
        not_beta_redex (oNode op [t1; t2]) ->
        drives fuel t2 (DFuel u) ->
        drives fuel (oNode op [t1; t2]) (DFuel u)

  (* The post-join RE-CHECK: the reassembled node against the REDEX ARMS ONLY —
     its children are already normal, so descent would be redundant; the default
     (wildcard) arm publishes the node as this subtree's NF. *)
  with recheck : nat -> Obj -> dres -> Prop :=
    | rc_fire0 : forall b a,
        recheck 0 (oNode op [oLam b; a]) (DFuel (oNode op [oLam b; a]))
    | rc_fire : forall f b a r,
        drives f (odbeta a b) r -> recheck (S f) (oNode op [oLam b; a]) r
    | rc_done : forall fuel t1 t2,
        not_beta_redex (oNode op [t1; t2]) ->
        recheck fuel (oNode op [t1; t2]) (DDone (oNode op [t1; t2])).

  Scheme drives_mut := Minimality for drives Sort Prop
    with recheck_mut := Minimality for recheck Sort Prop.
  Combined Scheme drives_recheck_mut from drives_mut, recheck_mut.

  (* The binder-arm re-check emission rule, discharged for this fragment: a rewrapped
     binder node is normal whenever its driven body is — a lambda is never a redex
     ROOT here (every compiled entry root is the App op), so the post-rewrap re-check
     the codegen would emit for a binder-rooted entry is correctly SKIPPED. *)
  Lemma binder_rewrap_needs_no_recheck : forall v, lam_nf v -> lam_nf (oLam v).
  Proof. intros v Hv. apply nf_lam. exact Hv. Qed.

  (* =============================================================================
     drive_steps_sound: a DDone drive is an iterated genuine object beta reduction.
     ============================================================================= *)

  Lemma drive_steps_sound_mut :
    (forall fuel t r, drives fuel t r -> forall v, r = DDone v -> ostar t v)
    /\ (forall fuel t r, recheck fuel t r -> forall v, r = DDone v -> ostar t v).
  Proof.
    apply (drives_recheck_mut
      (fun fuel t r => forall v, r = DDone v -> ostar t v)
      (fun fuel t r => forall v, r = DDone v -> ostar t v)).
    - (* d_free *) intros fuel x v Heq. injection Heq as <-. apply ostar_refl.
    - (* d_bound *) intros fuel n v Heq. injection Heq as <-. apply ostar_refl.
    - (* d_lam_done *)
      intros fuel b v Hb IH v0 Heq. injection Heq as <-.
      apply ostar_lam. apply (IH v eq_refl).
    - (* d_lam_fuel *) intros fuel b u Hb IH v Heq. discriminate Heq.
    - (* d_redex_fuel0 *) intros b a v Heq. discriminate Heq.
    - (* d_redex_fire *)
      intros f b a r Hr IH v Heq.
      eapply ostar_cons; [apply ob_fire | apply (IH v Heq)].
    - (* d_descend_done *)
      intros fuel t1 t2 v1 v2 r Hnr Ht1 IH1 Ht2 IH2 Hrc IH0 v Heq.
      eapply ostar_trans; [apply ostar_appl; apply (IH1 v1 eq_refl) |].
      eapply ostar_trans; [apply ostar_appr; apply (IH2 v2 eq_refl) |].
      apply (IH0 v Heq).
    - (* d_descend_fuel_l *) intros fuel t1 t2 u Hnr Ht IH v Heq. discriminate Heq.
    - (* d_descend_fuel_r *) intros fuel t1 t2 u Hnr Ht IH v Heq. discriminate Heq.
    - (* rc_fire0 *) intros b a v Heq. discriminate Heq.
    - (* rc_fire *)
      intros f b a r Hr IH v Heq.
      eapply ostar_cons; [apply ob_fire | apply (IH v Heq)].
    - (* rc_done *) intros fuel t1 t2 Hnr v Heq. injection Heq as <-. apply ostar_refl.
  Qed.

  Theorem drive_steps_sound : forall fuel t v,
    drives fuel t (DDone v) -> ostar t v.
  Proof.
    intros fuel t v H. exact (proj1 drive_steps_sound_mut fuel t (DDone v) H v eq_refl).
  Qed.

  (* =============================================================================
     quiescence_sound (PER-TRACE): every DDone trace rests a beta-normal form.  The
     mutual induction's re-check motive carries the children-normal hypothesis — the
     join case of the F14-confirmed structural induction.
     ============================================================================= *)

  Lemma quiescence_sound_mut :
    (forall fuel t r, drives fuel t r -> forall v, r = DDone v -> lam_nf v)
    /\ (forall fuel t r, recheck fuel t r ->
          (forall t1 t2, t = oNode op [t1; t2] -> lam_nf t1 /\ lam_nf t2) ->
          forall v, r = DDone v -> lam_nf v).
  Proof.
    apply (drives_recheck_mut
      (fun fuel t r => forall v, r = DDone v -> lam_nf v)
      (fun fuel t r =>
        (forall t1 t2, t = oNode op [t1; t2] -> lam_nf t1 /\ lam_nf t2) ->
        forall v, r = DDone v -> lam_nf v)).
    - (* d_free *) intros fuel x v Heq. injection Heq as <-. apply nf_free.
    - (* d_bound *) intros fuel n v Heq. injection Heq as <-. apply nf_bound.
    - (* d_lam_done *)
      intros fuel b v Hb IH v0 Heq. injection Heq as <-.
      apply nf_lam. apply (IH v eq_refl).
    - (* d_lam_fuel *) intros fuel b u Hb IH v Heq. discriminate Heq.
    - (* d_redex_fuel0 *) intros b a v Heq. discriminate Heq.
    - (* d_redex_fire *) intros f b a r Hr IH v Heq. apply (IH v Heq).
    - (* d_descend_done — the join case: the re-check receives the children-normal
         facts from the two child-drive inductive hypotheses. *)
      intros fuel t1 t2 v1 v2 r Hnr Ht1 IH1 Ht2 IH2 Hrc IH0 v Heq.
      apply IH0; [| exact Heq].
      intros t1' t2' Hnode. injection Hnode as <- <-.
      split; [apply (IH1 v1 eq_refl) | apply (IH2 v2 eq_refl)].
    - (* d_descend_fuel_l *) intros fuel t1 t2 u Hnr Ht IH v Heq. discriminate Heq.
    - (* d_descend_fuel_r *) intros fuel t1 t2 u Hnr Ht IH v Heq. discriminate Heq.
    - (* rc_fire0 *) intros b a Hch v Heq. discriminate Heq.
    - (* rc_fire — the re-check FIRED: the result is a full re-drive of the
         contractum, so the drives motive applies directly (no children hypothesis
         needed). *)
      intros f b a r Hr IH Hch v Heq. apply (IH v Heq).
    - (* rc_done — the wildcard default: the reassembled node is normal because its
         children are (the join hypotheses) and the redex arm did not match. *)
      intros fuel t1 t2 Hnr Hch v Heq. injection Heq as <-.
      destruct (Hch t1 t2 eq_refl) as [H1 H2].
      apply nf_app; [exact H1 | exact H2 |].
      intros b Heqlam. apply (Hnr b t2). rewrite Heqlam. reflexivity.
  Qed.

  Theorem quiescence_sound : forall fuel t v,
    drives fuel t (DDone v) -> lam_nf v.
  Proof.
    intros fuel t v H. exact (proj1 quiescence_sound_mut fuel t (DDone v) H v eq_refl).
  Qed.

  (* =============================================================================
     fuel_exhaustion_never_wrong: an exhausted trace surfaces the STUCK REDEX itself
     as the typed datum — never a normal form, never a DDone claim (the result
     constructors are disjoint by the `dres` type).
     ============================================================================= *)

  Lemma fuel_exhaustion_mut :
    (forall fuel t r, drives fuel t r ->
       forall u, r = DFuel u -> exists b a, u = oNode op [oLam b; a])
    /\ (forall fuel t r, recheck fuel t r ->
       forall u, r = DFuel u -> exists b a, u = oNode op [oLam b; a]).
  Proof.
    apply (drives_recheck_mut
      (fun fuel t r => forall u, r = DFuel u -> exists b a, u = oNode op [oLam b; a])
      (fun fuel t r => forall u, r = DFuel u -> exists b a, u = oNode op [oLam b; a])).
    - intros fuel x u Heq. discriminate Heq.
    - intros fuel n u Heq. discriminate Heq.
    - intros fuel b v Hb IH u Heq. discriminate Heq.
    - intros fuel b u Hb IH u0 Heq. apply (IH u0 Heq).
    - intros b a u Heq. injection Heq as <-. exists b, a. reflexivity.
    - intros f b a r Hr IH u Heq. apply (IH u Heq).
    - intros fuel t1 t2 v1 v2 r Hnr Ht1 IH1 Ht2 IH2 Hrc IH0 u Heq. apply (IH0 u Heq).
    - intros fuel t1 t2 u Hnr Ht IH u0 Heq. apply (IH u0 Heq).
    - intros fuel t1 t2 u Hnr Ht IH u0 Heq. apply (IH u0 Heq).
    - intros b a u Heq. injection Heq as <-. exists b, a. reflexivity.
    - intros f b a r Hr IH u Heq. apply (IH u Heq).
    - intros fuel t1 t2 Hnr u Heq. discriminate Heq.
  Qed.

  Theorem fuel_exhaustion_never_wrong : forall fuel t u,
    drives fuel t (DFuel u) -> exists b a, u = oNode op [oLam b; a].
  Proof.
    intros fuel t u H. exact (proj1 fuel_exhaustion_mut fuel t (DFuel u) H u eq_refl).
  Qed.

  (* The typed datum can NEVER be mistaken for a normal form: the exhaustion payload
     is a redex, and no redex is `lam_nf`. *)
  Corollary exhaustion_datum_is_not_nf : forall fuel t u,
    drives fuel t (DFuel u) -> ~ lam_nf u.
  Proof.
    intros fuel t u H Hnf.
    destruct (fuel_exhaustion_never_wrong fuel t u H) as [b [a ->]].
    inversion Hnf as [| | | t1 t2 H1 H2 Hnotlam Heq]. subst.
    exact (Hnotlam b eq_refl).
  Qed.

End DriverModel.

(* =================================================================================
   drive_weak_bisim: the ITERATED beta weak bisimulation — `represents` lifted from
   the single-fire clauses of InRhoBetaCascadeWeakBisim (whose cascade legs rest on
   DeBruijnSubstTRS SN + confluence) to firing CHAINS, in the same two-clause
   `is_weak_bisimulation` shape.  This is the driver's iterated-driving upgrade of the
   single-step premises (plan v2 section 7.1/7.4).
   ================================================================================= *)

(* Iterated ABSTRACT beta: a chain of visible root fires. *)
Inductive aiter (op : nat) : Obj -> Obj -> Prop :=
  | aiter_refl : forall o, aiter op o o
  | aiter_cons : forall o o' o'',
      awvis op o o' -> aiter op o' o'' -> aiter op o o''.

(* Iterated CONCRETE weak visible transitions: a chain of tau* ; fire-COMM ; tau*
   (each `cwvis` link's tau suffix is the subst cascade, SN+CR-collapsed). *)
Inductive citer (op : nat) : Tm -> Tm -> Prop :=
  | citer_refl : forall c, citer op c c
  | citer_cons : forall c c' c'',
      cwvis op c c' -> citer op c' c'' -> citer op c c''.

Theorem drive_weak_bisim : is_weak_bisimulation represents aiter citer.
Proof.
  split.
  - (* FORWARD: an abstract firing chain is matched by an in-Rho weak chain. *)
    intros o c op o' Hrep Hiter. revert c Hrep.
    induction Hiter as [o | o o1 o2 Hstep Hiter IH]; intros c Hrep.
    + exists c. split; [apply citer_refl | exact Hrep].
    + destruct (forward_simulation o c op o1 Hrep Hstep) as [c1 [Hc1 Hrep1]].
      destruct (IH c1 Hrep1) as [c2 [Hc2 Hrep2]].
      exists c2. split; [eapply citer_cons; [exact Hc1 | exact Hc2] | exact Hrep2].
  - (* BACKWARD: an in-Rho weak chain is matched by an abstract firing chain. *)
    intros o c op c' Hrep Hiter. revert o Hrep.
    induction Hiter as [c | c c1 c2 Hstep Hiter IH]; intros o Hrep.
    + exists o. split; [apply aiter_refl | exact Hrep].
    + destruct (backward_simulation o c op c1 Hrep Hstep) as [o1 [Ho1 Hrep1]].
      destruct (IH o1 Hrep1) as [o2 [Ho2 Hrep2]].
      exists o2. split; [eapply aiter_cons; [exact Ho1 | exact Ho2] | exact Hrep2].
Qed.

(* =================================================================================
   NON-VACUITY: the TWO-firing witness (the InRhoBetaCascadeWeakBisim witness
   pattern, iterated) — `(lam.0) ((lam.0) x^)` drives to `oFree x` with fuel 2 in the
   model (two redex fires; the final leaf drive at fuel 0 also witnesses that leaves
   never consult fuel), AND the concrete iterated weak transition takes the same two
   fire-plus-cascade steps to the represented normal form.
   ================================================================================= *)

Definition two_chain (op x : nat) : Obj :=
  oNode op [oLam (oBound 0); oNode op [oLam (oBound 0); oFree x]].

Theorem drive_two_firing_nonvacuous : forall op x,
  drives op 2 (two_chain op x) (DDone (oFree x))
  /\ citer op (embed (two_chain op x)) (embed (oFree x))
  /\ represents (oFree x) (embed (oFree x)).
Proof.
  intros op x. split; [| split].
  - (* the model derivation: fire (fuel 2 -> 1), fire (fuel 1 -> 0), leaf at fuel 0. *)
    unfold two_chain.
    apply d_redex_fire. cbn.
    apply d_redex_fire. cbn.
    apply d_free.
  - (* the concrete chain: two fire-then-cascade weak steps, each the SN+CR-unique
       cascade target (beta_fire_then_cascade_reaches_reduct). *)
    unfold two_chain.
    eapply citer_cons.
    + exact (beta_fire_then_cascade_reaches_reduct
               op (oNode op [oLam (oBound 0); oFree x]) (oBound 0)).
    + eapply citer_cons.
      * exact (beta_fire_then_cascade_reaches_reduct op (oFree x) (oBound 0)).
      * apply citer_refl.
  - unfold represents. apply norm_embed.
Qed.

(* Zero-admission confirmation. *)
Print Assumptions drive_steps_sound.
Print Assumptions quiescence_sound.
Print Assumptions fuel_exhaustion_never_wrong.
Print Assumptions exhaustion_datum_is_not_nf.
Print Assumptions binder_rewrap_needs_no_recheck.
Print Assumptions drive_weak_bisim.
Print Assumptions drive_two_firing_nonvacuous.
