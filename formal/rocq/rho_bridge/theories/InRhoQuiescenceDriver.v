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

(* =================================================================================
   A-S5.5: the BAG DRIVER model — the AC-family arms' peel/join/three-case-splice
   reassembly (rho_net_drive.rs `bag_fragment_dispatch` + the bag arm + the carrier's
   contractum entry) modeled as a big-step LTS over an ABSTRACT bag-value fragment,
   with the FLATTENING agreement lemma (plan v2 section 7.2).

   Conservative extension (the task mandate): the Lambda `Obj` fragment above carries no
   AC bag, and adding a bag constructor to `Obj`/`Tm` (DeBruijnSubstTRS) would disturb
   every landed theorem.  So the bag arm is modeled in its OWN self-contained fragment
   `bval` — a tree of op-bags over never-driven leaf atoms — exactly the shape the driver
   sees: a HashBag `Par` soup whose elements are either same-op sub-bags (spliced) or
   opaque values (wrapped).  Nothing above is touched; every landed Lambda theorem and
   its proof is intact.

   WHAT IS MODELED.  The driver's bag arm peels one element, drives it, drives the
   remainder, and splices the driven element's fragment back via the AM-3 THREE-CASE
   dispatch (Nil / same-op soup / wrap) before the post-join re-check.  The host's
   value-level `add_flattened_bag` (dovetail/src/rules.rs:707) splices any member that is
   itself an op-bag, multiplicity-preserving, on tree-shaped values (no cycle case).  The
   theorems:

     driver_flatten_agrees_with_add_flattened_bag : the driver's one-level-per-reassembly
                                                     splice (`bdrive`) computes the SAME
                                                     value as the host flatten (`bflatten`).
     bag_flatness_sound      : a driven bag is FLAT (no nested-bag element) — the AM-2
                               flatness obligation that makes the top-level NF-scan
                               complete (a nested `{{A,B},C}` would hide sibling redexes).
     bag_atoms_preserved     : the driven bag's leaf-atom multiset EQUALS the subject's
                               (`bflatten` only re-associates; multiplicity-preserving).
     bag_quiescence_sound    : PER-TRACE — EVERY `bdrives` derivation rests a FLAT bag
                               (the F14 join hypothesis, `Forall2 bdrives`, carries each
                               driven element's flatness; the AM-3 splice preserves it).
     bdrives_computes_bflatten / bdrives_deterministic : the relation computes exactly the
                               host flatten (per-trace determinism of the descent).

   The AC-FIRING fuel discipline (the redex arms consulting `MatchCase.guard` + the ground
   `GInt 0` case) is the SHARED `dres`/`DFuel` mechanism proven in DriverModel above:
   `fuel_exhaustion_never_wrong` / `exhaustion_datum_is_not_nf` bind the AC arms verbatim
   (an AC arm's `DFuel` datum is its subject soup — a redex — never an NF claim).  This
   section adds only the reassembly/flattening content the bag arm introduces.
   ================================================================================= *)

Section BagDriverModel.

  (* ── generic list helpers (uniquely prefixed to avoid any Stdlib name clash) ── *)

  (* Forall over an append. *)
  Lemma bag_Forall_app {A} (P : A -> Prop) (a b : list A) :
    Forall P a -> Forall P b -> Forall P (a ++ b).
  Proof.
    intros Ha Hb. induction Ha as [| x l0 Hx Hl0 IH]; simpl.
    - exact Hb.
    - apply Forall_cons; [exact Hx | exact IH].
  Qed.

  (* Forall distributes over flat_map when each image is Forall. *)
  Lemma bag_Forall_flat_map {A B} (P : B -> Prop) (f : A -> list B) (l : list A) :
    Forall (fun x => Forall P (f x)) l -> Forall P (flat_map f l).
  Proof.
    intro H. induction H as [| x l0 Hx Hl0 IH]; simpl.
    - apply Forall_nil.
    - apply bag_Forall_app; [exact Hx | exact IH].
  Qed.

  (* Pointwise-equal functions give equal flat_map (unconditional). *)
  Lemma bag_flat_map_ext {A B} (f g : A -> list B) (l : list A) :
    (forall x, f x = g x) -> flat_map f l = flat_map g l.
  Proof.
    intro Hext. induction l as [| a l0 IH]; simpl.
    - reflexivity.
    - rewrite Hext, IH. reflexivity.
  Qed.

  (* Forall-conditioned flat_map extensionality (the per-element IH form). *)
  Lemma bag_flat_map_ext_forall {A B} (f g : A -> list B) (l : list A) :
    Forall (fun x => f x = g x) l -> flat_map f l = flat_map g l.
  Proof.
    intro H. induction H as [| x l0 Hx Hl0 IH]; simpl.
    - reflexivity.
    - rewrite Hx, IH. reflexivity.
  Qed.

  (* flat_map fusion. *)
  Lemma bag_flat_map_flat_map {A B C} (f : B -> list C) (g : A -> list B) (l : list A) :
    flat_map f (flat_map g l) = flat_map (fun x => flat_map f (g x)) l.
  Proof.
    induction l as [| a l0 IH]; simpl.
    - reflexivity.
    - rewrite flat_map_app, IH. reflexivity.
  Qed.

  (* ── the abstract bag fragment ── *)

  (* An abstract bag value: an op-bag of children, or a never-driven leaf atom (a
     capability continuation / opaque value the driver wraps).  `nat` identifies atoms so
     the multiplicity argument has a concrete carrier. *)
  Inductive bval : Type :=
    | BAtom : nat -> bval
    | BBag  : list bval -> bval.

  (* The list-aware induction principle (the default `bval_ind` gives no hypothesis for
     the `list bval` children).  Proved by an inner fix over the children list; `REC` is
     applied only to `c`, a subterm of `l` hence of `BBag l` — guarded. *)
  Lemma bval_ind2 : forall (P : bval -> Prop),
    (forall n, P (BAtom n)) ->
    (forall l, Forall P l -> P (BBag l)) ->
    forall v, P v.
  Proof.
    intros P Hatom Hbag. fix REC 1.
    intro v; destruct v as [n | l].
    - apply Hatom.
    - apply Hbag. induction l as [| c cs IH].
      + apply Forall_nil.
      + apply Forall_cons; [apply REC | exact IH].
  Qed.

  (* The leaf-atom multiset of a bag value (order-preserving list), for multiplicity. *)
  Fixpoint atoms (v : bval) : list nat :=
    match v with
    | BAtom n => n :: nil
    | BBag l => flat_map atoms l
    end.

  (* The host `add_flattened_bag` mirror: flatten a value, splicing any member that is
     itself an op-bag.  `frag` is the one-member fragment (a sub-bag's elements, or the
     singleton wrap).  Structurally recursive: `bflatten c` on children `c` of `l`. *)
  Definition frag (w : bval) : list bval :=
    match w with
    | BBag cs => cs
    | BAtom n => BAtom n :: nil
    end.

  Fixpoint bflatten (v : bval) : bval :=
    match v with
    | BAtom n => BAtom n
    | BBag l => BBag (flat_map (fun c => frag (bflatten c)) l)
    end.

  (* The driver's AM-3 THREE-CASE splice (rho_net_drive.rs `bag_fragment_dispatch`): the
     DRIVEN element's fragment contributed to the accumulator — Nil (empty bag) splices
     NOTHING, a same-op soup splices its elements, anything else wraps as one element. *)
  Definition splice_fragment (driven : bval) (acc : list bval) : list bval :=
    match driven with
    | BBag nil          => acc                    (* Nil: splice-as-nothing *)
    | BBag (c :: cs)    => (c :: cs) ++ acc        (* same-op soup: splice its sends *)
    | BAtom n           => BAtom n :: acc          (* wrap one element send *)
    end.

  (* The driver's bag drive: fold the three-case splice over the DRIVEN elements (each
     `bdrive e` already flattened by the recursion — the AM-3(b) drive induction). *)
  Fixpoint bdrive (v : bval) : bval :=
    match v with
    | BAtom n => BAtom n
    | BBag l => BBag (fold_right (fun e acc => splice_fragment (bdrive e) acc) nil l)
    end.

  (* The three-case splice equals prepending the host fragment: the AM-3 dispatch is
     exactly the `add_flattened_bag` member splice (the Nil case = the empty prefix). *)
  Lemma splice_fragment_is_frag_app : forall w acc,
    splice_fragment w acc = frag w ++ acc.
  Proof.
    intros w acc. destruct w as [n | l].
    - reflexivity.
    - destruct l as [| c cs]; reflexivity.
  Qed.

  (* The bag arm's fold IS the host flatten's flat_map, once the splice is the fragment
     append. *)
  Lemma fold_right_frag_is_flat_map :
    forall (f : bval -> bval) (l : list bval),
      fold_right (fun e acc => splice_fragment (f e) acc) nil l
        = flat_map (fun c => frag (f c)) l.
  Proof.
    intros f l. induction l as [| c cs IH]; simpl.
    - reflexivity.
    - rewrite splice_fragment_is_frag_app, IH. reflexivity.
  Qed.

  (* ★ THE AGREEMENT LEMMA (plan v2 section 7.2): the driver's one-level-per-reassembly
     three-case splice computes the SAME value as the host's value-level flatten on
     tree-shaped values. *)
  Theorem driver_flatten_agrees_with_add_flattened_bag :
    forall v, bdrive v = bflatten v.
  Proof.
    intro v; induction v as [n | l IHl] using bval_ind2.
    - reflexivity.
    - cbn [bdrive bflatten]. rewrite (fold_right_frag_is_flat_map bdrive l). f_equal.
      apply bag_flat_map_ext_forall.
      eapply Forall_impl; [| exact IHl]. intros c Hc. rewrite Hc. reflexivity.
  Qed.

  (* Flatness: a value is flat iff every bag element is an atom (no nested bag). *)
  Definition atom_elem (c : bval) : Prop := exists n, c = BAtom n.
  Definition is_flat (v : bval) : Prop :=
    match v with
    | BAtom _ => True
    | BBag l => Forall atom_elem l
    end.

  (* `frag` of a FLAT value is a list of atoms (so prepending it keeps an all-atoms
     accumulator all-atoms). *)
  Lemma frag_of_flat_is_atoms : forall w,
    is_flat w -> Forall atom_elem (frag w).
  Proof.
    intros w Hflat. destruct w as [n | l]; simpl in *.
    - apply Forall_cons; [exists n; reflexivity | apply Forall_nil].
    - exact Hflat.
  Qed.

  (* ★ FLATNESS SOUNDNESS (the AM-2 obligation): a driven bag is flat. *)
  Theorem bag_flatness_sound : forall v, is_flat (bdrive v).
  Proof.
    intro v; induction v as [n | l IHl] using bval_ind2.
    - exact I.
    - cbn [bdrive]. rewrite (fold_right_frag_is_flat_map bdrive l). cbn [is_flat].
      apply bag_Forall_flat_map.
      eapply Forall_impl; [| exact IHl]. intros c Hc. apply frag_of_flat_is_atoms. exact Hc.
  Qed.

  (* `flat_map atoms (frag w) = atoms w` for ANY w — the fragment of a value re-exposes
     exactly its leaves. *)
  Lemma flat_map_atoms_frag : forall w,
    flat_map atoms (frag w) = atoms w.
  Proof.
    intro w. destruct w as [n | l]; reflexivity.
  Qed.

  (* ★ MULTIPLICITY PRESERVATION: the driven bag's leaf-atom multiset EQUALS the
     subject's (`bflatten` only re-associates the nesting, left-to-right — so even the
     ORDER is preserved, hence list equality, a fortiori multiset equality). *)
  Theorem bag_atoms_preserved : forall v, atoms (bflatten v) = atoms v.
  Proof.
    intro v; induction v as [n | l IHl] using bval_ind2.
    - reflexivity.
    - cbn [bflatten atoms].
      rewrite (bag_flat_map_flat_map atoms (fun c => frag (bflatten c)) l).
      transitivity (flat_map (fun c => atoms (bflatten c)) l).
      + apply bag_flat_map_ext. intro x. apply flat_map_atoms_frag.
      + apply bag_flat_map_ext_forall. exact IHl.
  Qed.

  (* The bag arm as a big-step LTS: a leaf is inert; a bag drives EVERY element (the F14
     concurrent child drives), then splices the driven elements (the AM-3 reassembly).
     `Forall2 bdrives l ws` is the atomic JOIN — the reassembly sees only fully-driven
     children. *)
  Inductive bdrives : bval -> bval -> Prop :=
    | bd_atom : forall n, bdrives (BAtom n) (BAtom n)
    | bd_bag  : forall l ws,
        Forall2 bdrives l ws ->
        bdrives (BBag l) (BBag (fold_right (fun w acc => splice_fragment w acc) nil ws)).

  (* fold over `map bdrive l` = fold over `l` with the splice pre-composed with bdrive. *)
  Lemma fold_right_splice_map : forall l,
    fold_right (fun w acc => splice_fragment w acc) nil (map bdrive l)
      = fold_right (fun e acc => splice_fragment (bdrive e) acc) nil l.
  Proof.
    induction l as [| c cs IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  (* The relation computes exactly the driver's `bdrive` function. *)
  Lemma bdrives_computes_bdrive : forall v, bdrives v (bdrive v).
  Proof.
    intro v; induction v as [n | l IHl] using bval_ind2.
    - apply bd_atom.
    - cbn [bdrive]. rewrite <- fold_right_splice_map. apply bd_bag.
      induction IHl as [| c cs Hc Hcs IH]; simpl.
      + apply Forall2_nil.
      + apply Forall2_cons; [exact Hc | exact IH].
  Qed.

  (* From the per-element determinism (the structural IH) + the Forall2 join, the driven
     children are exactly `map bdrive l`. *)
  Lemma forall2_bdrives_map : forall l ws,
    Forall (fun c => forall w, bdrives c w -> w = bdrive c) l ->
    Forall2 bdrives l ws ->
    ws = map bdrive l.
  Proof.
    intros l ws HF H2. generalize dependent ws.
    induction HF as [| c cs Hc Hcs IH]; intros ws H2.
    - inversion H2; subst; reflexivity.
    - inversion H2; subst; simpl. f_equal.
      + apply Hc. assumption.
      + apply IH. assumption.
  Qed.

  (* Per-trace determinism of the descent (there is no schedule choice in the pure
     flattening reassembly). *)
  Lemma bdrives_deterministic : forall v w, bdrives v w -> w = bdrive v.
  Proof.
    intro v; induction v as [n | l IHl] using bval_ind2; intros w H.
    - inversion H; subst; reflexivity.
    - inversion H; subst; cbn [bdrive]; f_equal.
      match goal with
      | [ HF : Forall2 bdrives l ?ws |- _ ] =>
          rewrite (forall2_bdrives_map l ws IHl HF)
      end.
      apply fold_right_splice_map.
  Qed.

  (* ★ PER-TRACE QUIESCENCE (the F14 join + AM-3 splice induction): EVERY `bdrives`
     derivation rests a FLAT bag — the reassembly's `Forall2 bdrives` hypothesis carries
     each driven child's flatness (through determinism), and the three-case splice
     preserves it, so no nested bag hides a sibling redex from the top-level scan. *)
  Theorem bag_quiescence_sound : forall v w, bdrives v w -> is_flat w.
  Proof.
    intros v w H. rewrite (bdrives_deterministic v w H). apply bag_flatness_sound.
  Qed.

End BagDriverModel.

(* Zero-admission confirmation. *)
Print Assumptions drive_steps_sound.
Print Assumptions quiescence_sound.
Print Assumptions fuel_exhaustion_never_wrong.
Print Assumptions exhaustion_datum_is_not_nf.
Print Assumptions binder_rewrap_needs_no_recheck.
Print Assumptions drive_weak_bisim.
Print Assumptions drive_two_firing_nonvacuous.
(* A-S5.5 bag-driver additions. *)
Print Assumptions driver_flatten_agrees_with_add_flattened_bag.
Print Assumptions bag_flatness_sound.
Print Assumptions bag_atoms_preserved.
Print Assumptions bag_quiescence_sound.
Print Assumptions bdrives_computes_bdrive.
Print Assumptions bdrives_deterministic.
