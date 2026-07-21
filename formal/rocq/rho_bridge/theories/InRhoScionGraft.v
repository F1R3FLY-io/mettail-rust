(*
 * InRhoScionGraft: the E-1 DEMAND-DRIVEN SLOT-SCION for the in-Rho quiescence
 * driver's FiringEmission seam (rholang-codegen/src/rho_net_drive.rs `ScionBundle`),
 * modeled as a big-step LTS over the SAME reflected object fragment `Obj` used by the
 * landed driver (DeBruijnSubstTRS `Obj`), with the FIRED-MULTISET carried in the result
 * so control-vs-treatment agreement is a genuine "same normal form AND same fired
 * multiset" statement (the runtime gate, scion_grafting.rs).
 *
 * ---------------------------------------------------------------------------------
 * R-10 RESOLUTION (the plan's core structural claim, de-risked in STEP 0)
 * ---------------------------------------------------------------------------------
 *
 * This file is ADDITIVE over the shared `Obj` of DeBruijnSubstTRS.  It touches NOTHING
 * in InRhoQuiescenceDriver.v — it MIRRORS that file's style (a `drives`/`recheck`
 * big-step, a `dres` result split, mutual `Scheme`s, an `ostar`/`obeta` soundness
 * pattern) rather than editing it.  The scion ladder lives NATIVELY in the existing
 * arity-general constructor node `oNode : nat -> list Obj -> Obj`
 * (DeBruijnSubstTRS.v:96):
 *
 *     End       = oNode c_end  []
 *     Step u    = oNode c_step [u]
 *     Wrap u    = oNode c_wrap [u]
 *     D1 u      = oNode c_d1   [u]        (a known-RHS "scion node")
 *     C(t1,t2)  = oNode c      [t1; t2]   (any arity — the model is arity-general)
 *
 * so NO new term constructor and NO edit to the driver is needed.  (The design's
 * alternative (a) — a beta-fragment port — is vacuous: SubstRewrite (beta) arms are
 * definitionally `ContractumRedrive`, they carry no scion; see e1_scion_design_v1.md
 * section 2.2.)
 *
 * ---------------------------------------------------------------------------------
 * WHAT IS MODELED
 * ---------------------------------------------------------------------------------
 *
 * A finite, deeply-embedded rule table `R : list rule` of linear constructor patterns
 * `pat` and constructor-tree right-hand sides `rhs` over slot indices.  From it we
 * derive (all decidable bool `Fixpoint`s):
 *
 *   could_unify p s      : might pattern `p` match SOME instantiation of rhs-subtree `s`?
 *   mark s               : = scion_position_is_recheck (rho_net_drive.rs:2179) — does
 *                          any rule LHS could_unify with the rhs-position `s`?  false =
 *                          SKIP (the codegen savings), true = RECHECK.
 *   is_ever_redex_root c : = redex_root_ctors (rho_net_drive.rs:2453) — is `c` any
 *                          rule's LHS root constructor?
 *   graft_safe           : the FOLD-1 GUARD (scion_emit_point :2401) — every SKIP
 *                          constructor sitting ABOVE a RECHECK is never a redex root.
 *   root_stable          : the section-4.2 side condition (no constructor demanded at
 *                          LHS depth >= 1 is any rule's LHS root).
 *
 * TWO big-step relations over `Obj`, carrying the fired-rule multiset (`list nat` of
 * rule indices) in the result:
 *
 *   gdrives  — the CONTRACTUM-REDRIVE reference (the landed driver, generalized to the
 *              rule table and to arity-general `oNode`): on firing, the WHOLE contractum
 *              is re-driven; descent drives every child at the SAME fuel, joins, and
 *              re-checks the reassembled node.
 *   sdrives  — the SCION: on firing, the RHS skeleton is GRAFTED (known constructors are
 *              rebuilt inert, `mark=false` SKIP positions), only `mark=true` RECHECK
 *              positions RESUBMIT their raw subtree by re-entering `gdrives` at fuel-1,
 *              and slot occurrences are driven at fuel-1.  `gdrives` is defined FIRST and
 *              `sdrives`/`sgraft` reference it (gdrives never mentions sdrives), so the
 *              blocks type-check cleanly with strict positivity.
 *
 * fuel is decremented ONLY on firing (descent copies it — per-path semantics, exactly
 * the driver's discipline); the result type `dres` separates the quiescent value
 * (`Done v fired`) from the typed fuel-exhaustion datum (`Fuel u`, the stuck redex).
 *
 * Rocq 9.1 compatible.  No Admitted, no Axioms, no Assumptions, no Parameters (the rule
 * table `R` is a `Section` `Variable`, discharged to a universally-quantified hypothesis
 * before the `Print Assumptions` gate — never an axiom).
 *)

From Stdlib Require Import List PeanoNat Permutation Lia Bool.
From RhoBridge Require Import DeBruijnSubstTRS InRhoBetaCascadeWeakBisim.

Import ListNotations.

(* =================================================================================
   1.  The result type: value + FIRED MULTISET, or the typed fuel-exhaustion datum.

   `Done v fired` is the quiescent OUT value together with the multiset (order-carrying
   list) of rule indices that fired to reach it — the SM-10 fired-multiset carry that
   makes control-vs-treatment agreement a genuine "same NF AND same fired bag"
   statement.  `Fuel u` is the `^drive-fuel` datum (the stuck redex `u`).  Distinct from
   the landed `InRhoQuiescenceDriver.dres` (this file does NOT import the driver), so no
   name clash across files.
   ================================================================================= *)

Inductive dres : Type :=
  | Done : Obj -> list nat -> dres
  | Fuel : Obj -> dres.

(* Prepend a batch of child-fired labels to a result (the join's label accumulation). *)
Definition rlabels_prepend (fs : list nat) (r : dres) : dres :=
  match r with
  | Done v gs => Done v (fs ++ gs)
  | Fuel u => Fuel u
  end.

(* Cons one firing label onto a result (a single fire's label). *)
Definition rlabel_cons (i : nat) (r : dres) : dres :=
  match r with
  | Done v gs => Done v (i :: gs)
  | Fuel u => Fuel u
  end.

(* The list-drive result: all children driven to values (with concatenated labels), or
   some child exhausted fuel. *)
Inductive dres_list : Type :=
  | DoneL : list Obj -> list nat -> dres_list
  | FuelL : Obj -> dres_list.

(* =================================================================================
   2.  The deeply-embedded rule table: linear constructor patterns and constructor-tree
       RHSs over slot indices.  Constructors are `nat` tags (the reflected `^C` op
       numerals); slots are `nat` variable indices.
   ================================================================================= *)

Inductive pat : Type :=
  | PVar : nat -> pat
  | PApp : nat -> list pat -> pat.

Inductive rhs : Type :=
  | RVar : nat -> rhs
  | RApp : nat -> list rhs -> rhs.

Definition rule : Type := (pat * rhs)%type.

(* Nested induction principles (the auto-generated ones give no hypothesis for the list
   children), mirroring DeBruijnSubstTRS.Obj_ind'. *)
Definition pat_ind' (P : pat -> Prop)
  (Hv : forall i, P (PVar i))
  (Ha : forall c args, Forall P args -> P (PApp c args))
  : forall p, P p :=
  fix F (p : pat) : P p :=
    match p with
    | PVar i => Hv i
    | PApp c args =>
        Ha c args
           ((fix G (l : list pat) : Forall P l :=
               match l with
               | [] => Forall_nil P
               | x :: xs => Forall_cons x (F x) (G xs)
               end) args)
    end.

Definition rhs_ind' (P : rhs -> Prop)
  (Hv : forall i, P (RVar i))
  (Ha : forall c args, Forall P args -> P (RApp c args))
  : forall r, P r :=
  fix F (r : rhs) : P r :=
    match r with
    | RVar i => Hv i
    | RApp c args =>
        Ha c args
           ((fix G (l : list rhs) : Forall P l :=
               match l with
               | [] => Forall_nil P
               | x :: xs => Forall_cons x (F x) (G xs)
               end) args)
    end.

(* =================================================================================
   3.  Matching and instantiation (total Fixpoints; linear patterns keep them
       decidable).  Bindings are an association list slot-index -> matched Obj.
   ================================================================================= *)

Fixpoint lookup (i : nat) (b : list (nat * Obj)) : option Obj :=
  match b with
  | [] => None
  | (j, o) :: b' => if Nat.eqb i j then Some o else lookup i b'
  end.

(* pat_match p o = Some binds iff p matches o, collecting the left-to-right slot
   bindings.  PApp only matches an oNode of the same tag and arity; a variable pattern
   matches anything.  NAMED mutual list helper `pat_match_list` (rather than an anonymous
   inner fix) so the skip-soundness / agreement inductions reason about it cleanly. *)
Fixpoint pat_match (p : pat) (o : Obj) : option (list (nat * Obj)) :=
  match p with
  | PVar i => Some [(i, o)]
  | PApp c ps =>
      match o with
      | oNode c' os =>
          if andb (Nat.eqb c c') (Nat.eqb (length ps) (length os))
          then (fix go (ps0 : list pat) (os0 : list Obj) : option (list (nat * Obj)) :=
                  match ps0, os0 with
                  | [], [] => Some []
                  | p0 :: ps', o0 :: os' =>
                      match pat_match p0 o0, go ps' os' with
                      | Some b1, Some b2 => Some (b1 ++ b2)
                      | _, _ => None
                      end
                  | _, _ => None
                  end) ps os
          else None
      | _ => None
      end
  end.

(* The list matcher as a STANDALONE fixpoint (calls the completed `pat_match`), so the
   skip-soundness / agreement inductions have a NAMED handle.  `pat_match_app` below
   proves the `PApp`/`oNode` unfolding routes through it (the anonymous inner fix and
   this share the same recurrence). *)
Fixpoint pat_match_list (ps : list pat) (os : list Obj) : option (list (nat * Obj)) :=
  match ps, os with
  | [], [] => Some []
  | p0 :: ps', o0 :: os' =>
      match pat_match p0 o0, pat_match_list ps' os' with
      | Some b1, Some b2 => Some (b1 ++ b2)
      | _, _ => None
      end
  | _, _ => None
  end.

(* The inner fix of `pat_match` on a `PApp`/`oNode` pair equals `pat_match_list`. *)
Lemma pat_match_app : forall c ps c' os,
  pat_match (PApp c ps) (oNode c' os)
    = if andb (Nat.eqb c c') (Nat.eqb (length ps) (length os))
      then pat_match_list ps os else None.
Proof.
  (* the anonymous inner fix of `pat_match` and `pat_match_list` have identical bodies,
     so they are alpha-convertible — conversion closes it. *)
  intros c ps c' os. reflexivity.
Qed.

(* Instantiate an RHS skeleton with a slot binding.  An unbound RHS variable defaults to
   `oFree 0` (never happens for well-formed rules — every RHS var is a pattern var). *)
Fixpoint inst (r : rhs) (b : list (nat * Obj)) : Obj :=
  match r with
  | RVar i => match lookup i b with Some o => o | None => oFree 0 end
  | RApp c rs => oNode c (map (fun r0 => inst r0 b) rs)
  end.

(* =================================================================================
   4.  could_unify: might pattern `p` match SOME slot-instantiation of rhs-subtree `s`?
       A variable pattern matches anything (true); an rhs variable can be instantiated
       to anything, so any pattern MIGHT match it (true); two constructor nodes could
       unify iff same tag, same arity, and children pairwise could_unify.
   ================================================================================= *)

Fixpoint could_unify (p : pat) (s : rhs) : bool :=
  match p, s with
  | PVar _, _ => true
  | _, RVar _ => true
  | PApp c1 ps, RApp c2 rs =>
      andb (andb (Nat.eqb c1 c2) (Nat.eqb (length ps) (length rs)))
           ((fix go (ps0 : list pat) (rs0 : list rhs) : bool :=
               match ps0, rs0 with
               | [], [] => true
               | p0 :: ps', r0 :: rs' => andb (could_unify p0 r0) (go ps' rs')
               | _, _ => false
               end) ps rs)
  end.

(* The list could-unify as a STANDALONE fixpoint, with the unfolding lemma. *)
Fixpoint could_unify_list (ps : list pat) (rs : list rhs) : bool :=
  match ps, rs with
  | [], [] => true
  | p0 :: ps', r0 :: rs' => andb (could_unify p0 r0) (could_unify_list ps' rs')
  | _, _ => false
  end.

Lemma could_unify_app : forall c1 ps c2 rs,
  could_unify (PApp c1 ps) (RApp c2 rs)
    = andb (andb (Nat.eqb c1 c2) (Nat.eqb (length ps) (length rs)))
           (could_unify_list ps rs).
Proof.
  intros c1 ps c2 rs. reflexivity.
Qed.

Definition root_ctor (p : pat) : option nat :=
  match p with PApp c _ => Some c | PVar _ => None end.

(* =================================================================================
   L3.1 — SCION SKIP SOUNDNESS (the Lemma 6.2.3 analogue, the load-bearing NEW content).

   An UNMARKED rhs-position — one where `could_unify p s = false` for a pattern `p` — can
   NEVER be matched by `p` under ANY slot instantiation `binds`.  So the codegen's SKIP
   verdict (no re-check emitted there) loses nothing: no rule can fire at a position the
   mark analysis pruned.  This is what licenses the scion's inert graft of SKIP
   constructors.  R-free (depends only on the syntactic could_unify / pat_match / inst),
   so it is proved OUTSIDE the section.
   ================================================================================= *)

(* The list form (the PApp/RApp recursive step), carrying the per-child skip-soundness
   IH from `pat_ind'`. *)
Lemma pat_match_list_skip_none :
  forall ps rs,
    Forall (fun p => forall s, could_unify p s = false ->
                    forall binds, pat_match p (inst s binds) = None) ps ->
    length ps = length rs ->
    could_unify_list ps rs = false ->
    forall binds, pat_match_list ps (map (fun r0 => inst r0 binds) rs) = None.
Proof.
  induction ps as [| p ps IH]; intros rs HF Hlen Hcul binds.
  - destruct rs; simpl in *; [discriminate Hcul | discriminate Hlen].
  - destruct rs as [| r rs]; simpl in Hlen; [discriminate |].
    injection Hlen as Hlen.
    inversion HF as [| p0 ps0 Hp Hps]; subst.
    simpl. cbn [could_unify_list] in Hcul.
    destruct (could_unify p r) eqn:Ecu.
    + (* head could_unify: the FALSE must come from the tail *)
      simpl in Hcul.
      rewrite (IH rs Hps Hlen Hcul binds).
      destruct (pat_match p (inst r binds)); reflexivity.
    + (* head is a proven skip: pat_match p (inst r binds) = None *)
      rewrite (Hp r Ecu binds). reflexivity.
Qed.

Lemma scion_skip_sound :
  forall p s, could_unify p s = false ->
  forall binds, pat_match p (inst s binds) = None.
Proof.
  intro p. induction p as [i | c1 ps IHps] using pat_ind'; intros s Hcu binds.
  - destruct s; simpl in Hcu; discriminate.
  - destruct s as [j | c2 rs].
    + simpl in Hcu; discriminate.
    + cbn [inst]. rewrite pat_match_app, length_map.
      rewrite could_unify_app in Hcu.
      destruct (Nat.eqb c1 c2) eqn:Ec; cbn [andb] in Hcu |- *; [| reflexivity].
      destruct (Nat.eqb (length ps) (length rs)) eqn:El; cbn [andb] in Hcu |- *; [| reflexivity].
      apply Nat.eqb_eq in El.
      exact (pat_match_list_skip_none ps rs IHps El Hcu binds).
Qed.

(* =================================================================================
   5.  The rule table `R` as a Section Variable (discharged before Print Assumptions —
       a universally-quantified hypothesis, NOT an axiom).  Everything R-dependent lives
       inside.
   ================================================================================= *)

Section ScionModel.

  Variable R : list rule.

  (* Rule `i` fires at the ROOT of `t`, producing contractum `u`. *)
  Definition fires (i : nat) (t u : Obj) : Prop :=
    exists p r binds,
      nth_error R i = Some (p, r) /\ pat_match p t = Some binds /\ u = inst r binds.

  (* No rule matches at the root of `t` (the wildcard side of every redex Match arm —
     the descent/re-check arms carry exactly this negative premise). *)
  Definition no_root_redex (t : Obj) : Prop := forall i u, ~ fires i t u.

  (* mark: is the rhs-position `s` a RECHECK (some LHS could_unify) or a SKIP (none)? *)
  Definition mark (s : rhs) : bool := existsb (fun rl => could_unify (fst rl) s) R.

  (* is `c` ever a rule LHS root constructor? *)
  Definition is_ever_redex_root (c : nat) : bool :=
    existsb (fun rl => match root_ctor (fst rl) with
                       | Some c' => Nat.eqb c c'
                       | None => false
                       end) R.

  (* Rules are CONSTRUCTOR-rooted (every LHS is a `PApp`, not a bare `PVar`) — the
     structural-rewrite discipline (a `PVar`-rooted rule would rewrite EVERY term and is
     not a structural rule).  A decidable well-formedness side condition of the whole
     model; every scion rule table (ladder, RTrig, and the runtime's structural arms)
     satisfies it. *)
  Definition rules_constructor_rooted : bool :=
    forallb (fun rl => match fst rl with PApp _ _ => true | PVar _ => false end) R.

  (* graft_safe over ONE rhs skeleton: every SKIP node (mark=false) has a constructor
     that is NEVER a redex root.

     THE FOLD-1 GUARD, in its clean sufficient form.  The runtime's Fold-1 guard
     (scion_emit_point, rho_net_drive.rs:2401) forbids a SKIP constructor that sits ABOVE
     a RECHECK from being a redex root — because driving the RECHECK below it can change a
     child's root and thereby expose a fresh redex at the SKIP constructor that the inert
     graft would miss (this is exactly the NEGATIVE TEST below).  On every SLOT-BEARING
     skeleton the two forms COINCIDE: a slot occurrence is ALWAYS a recheck
     (could_unify _ (RVar _) = true, so mark (RVar _) = true), so a SKIP constructor
     dominating any slot is "above a recheck", and the only skeletons where the strong
     form is stricter are pure-GROUND skips with a redex-root constructor and an arity/tag
     mismatch — provably still safe (driving a redex-free ground term is the identity) but
     irrelevant to every scion rule (all carry slots) and to both witnesses.  We prove
     agreement under this clean form; the coincidence is documented, the gap flagged. *)
  Fixpoint rhs_graft_safe (s : rhs) : bool :=
    match s with
    | RVar _ => true
    | RApp c rs =>
        andb (if mark s then true else negb (is_ever_redex_root c))
             (forallb rhs_graft_safe rs)
    end.

  Definition graft_safe : bool := forallb (fun rl => rhs_graft_safe (snd rl)) R.

  (* root_stable (section-4.2): no constructor demanded at LHS depth >= 1 is any rule's
     LHS root.  Used only for the optional full <-> direction of agreement. *)
  Fixpoint pat_ctors_incl (p : pat) : list nat :=
    match p with
    | PVar _ => []
    | PApp c args =>
        c :: (fix fl (l : list pat) : list nat :=
                match l with [] => [] | x :: xs => pat_ctors_incl x ++ fl xs end) args
    end.

  Definition pat_ctors_below_root (p : pat) : list nat :=
    match p with PVar _ => [] | PApp _ args => flat_map pat_ctors_incl args end.

  Definition root_stable : bool :=
    forallb (fun rl => forallb (fun c => negb (is_ever_redex_root c))
                               (pat_ctors_below_root (fst rl))) R.

  (* ===============================================================================
     6.  BLOCK 1 — gdrives (the CONTRACTUM-REDRIVE reference), arity-general and
         table-driven, mutually with the child-list drive and the post-join re-check.
         One constructor per generated arm disposition.
     =============================================================================== *)

  Inductive gdrives : nat -> Obj -> dres -> Prop :=
    (* leaf / reserved passthrough arms: inert, fuel NOT consulted. *)
    | g_free  : forall f x, gdrives f (oFree x) (Done (oFree x) [])
    | g_bound : forall f n, gdrives f (oBound n) (Done (oBound n) [])
    (* binder arm (oLam is unused by the scion fragment, but kept total). *)
    | g_lam   : forall f b v gs, gdrives f b (Done v gs) -> gdrives f (oLam b) (Done (oLam v) gs)
    | g_lam_fuel : forall f b u, gdrives f b (Fuel u) -> gdrives f (oLam b) (Fuel u)
    (* redex arm, fuel-gated: ground 0 FIRST (typed exhaustion = the stuck redex node),
       else FIRE (re-drive the WHOLE contractum) with fuel-1. *)
    | g_fuel0 : forall i t u, fires i t u -> gdrives 0 t (Fuel t)
    | g_fire  : forall f i t u r,
        fires i t u -> gdrives f u r -> gdrives (S f) t (rlabel_cons i r)
    (* congruence-descent arm (no root redex): concurrent child drives at the SAME fuel,
       the atomic join, then the inline post-join re-check of the reassembled node. *)
    | g_descend : forall f op ts vs fss r,
        no_root_redex (oNode op ts) ->
        gdrives_list f ts (DoneL vs fss) ->
        grecheck f (oNode op vs) r ->
        gdrives f (oNode op ts) (rlabels_prepend fss r)
    | g_descend_fuel : forall f op ts u,
        no_root_redex (oNode op ts) ->
        gdrives_list f ts (FuelL u) ->
        gdrives f (oNode op ts) (Fuel u)

  with gdrives_list : nat -> list Obj -> dres_list -> Prop :=
    | gdl_nil : forall f, gdrives_list f [] (DoneL [] [])
    | gdl_cons : forall f t ts v gs vs fss,
        gdrives f t (Done v gs) ->
        gdrives_list f ts (DoneL vs fss) ->
        gdrives_list f (t :: ts) (DoneL (v :: vs) (gs ++ fss))
    | gdl_cons_fuel_head : forall f t ts u,
        gdrives f t (Fuel u) -> gdrives_list f (t :: ts) (FuelL u)
    | gdl_cons_fuel_tail : forall f t ts v gs u,
        gdrives f t (Done v gs) -> gdrives_list f ts (FuelL u) ->
        gdrives_list f (t :: ts) (FuelL u)

  (* post-join re-check: the reassembled node against the REDEX ARMS ONLY (children
     already normal); the wildcard default publishes the node as this subtree's NF. *)
  with grecheck : nat -> Obj -> dres -> Prop :=
    | grc_fuel0 : forall i t u, fires i t u -> grecheck 0 t (Fuel t)
    | grc_fire  : forall f i t u r,
        fires i t u -> gdrives f u r -> grecheck (S f) t (rlabel_cons i r)
    | grc_done  : forall f t, no_root_redex t -> grecheck f t (Done t []).

  (* ===============================================================================
     7.  BLOCK 2 — sgraft (the scion RHS-skeleton graft), referencing gdrives (block 1)
         for slot drives and RECHECK resubmits.  gdrives never mentions sgraft, so this
         is a clean second block.
     =============================================================================== *)

  Inductive sgraft : nat -> rhs -> list (nat * Obj) -> dres -> Prop :=
    (* a SLOT: drive the bound value via gdrives at the (already decremented) fuel. *)
    | sg_var : forall f j binds o r,
        lookup j binds = Some o -> gdrives f o r -> sgraft f (RVar j) binds r
    (* a RECHECK node (mark=true): RESUBMIT the RAW instantiated subtree to gdrives. *)
    | sg_recheck : forall f c rs binds r,
        mark (RApp c rs) = true ->
        gdrives f (inst (RApp c rs) binds) r ->
        sgraft f (RApp c rs) binds r
    (* a SKIP node (mark=false): graft the known constructor inert, recursing into
       children (slots driven, sub-rechecks resubmitted, sub-skips grafted). *)
    | sg_skip : forall f c rs binds vs fss,
        mark (RApp c rs) = false ->
        sgraft_list f rs binds (DoneL vs fss) ->
        sgraft f (RApp c rs) binds (Done (oNode c vs) fss)
    | sg_skip_fuel : forall f c rs binds u,
        mark (RApp c rs) = false ->
        sgraft_list f rs binds (FuelL u) ->
        sgraft f (RApp c rs) binds (Fuel u)

  with sgraft_list : nat -> list rhs -> list (nat * Obj) -> dres_list -> Prop :=
    | sgl_nil : forall f binds, sgraft_list f [] binds (DoneL [] [])
    | sgl_cons : forall f r rs binds v gs vs fss,
        sgraft f r binds (Done v gs) ->
        sgraft_list f rs binds (DoneL vs fss) ->
        sgraft_list f (r :: rs) binds (DoneL (v :: vs) (gs ++ fss))
    | sgl_cons_fuel_head : forall f r rs binds u,
        sgraft f r binds (Fuel u) -> sgraft_list f (r :: rs) binds (FuelL u)
    | sgl_cons_fuel_tail : forall f r rs binds v gs u,
        sgraft f r binds (Done v gs) -> sgraft_list f rs binds (FuelL u) ->
        sgraft_list f (r :: rs) binds (FuelL u).

  (* ===============================================================================
     8.  BLOCK 3 — sdrives (the scion driver).  On a ROOT redex it fires ONE scion
         graft (`sgraft` of the RHS skeleton, fuel-1); a non-redex node descends exactly
         as gdrives (the scion and the redrive share their descent — the optimization is
         only at firing), so it delegates to gdrives there; leaves are inert.  sdrives
         references sgraft + gdrives; nothing references sdrives.
     =============================================================================== *)

  Inductive sdrives : nat -> Obj -> dres -> Prop :=
    | s_free  : forall f x, sdrives f (oFree x) (Done (oFree x) [])
    | s_bound : forall f n, sdrives f (oBound n) (Done (oBound n) [])
    (* a ROOT redex at fuel 0: typed exhaustion (the stuck redex itself). *)
    | s_fuel0 : forall i t u, fires i t u -> sdrives 0 t (Fuel t)
    (* a ROOT redex at fuel S f: fire rule i, GRAFT the RHS skeleton at fuel f, cons the
       firing label. *)
    | s_fire  : forall f i t p rr binds r,
        nth_error R i = Some (p, rr) ->
        pat_match p t = Some binds ->
        sgraft f rr binds r ->
        sdrives (S f) t (rlabel_cons i r)
    (* a non-redex node: the scion descends exactly as the redrive (identical descent). *)
    | s_nonredex : forall f op ts r,
        no_root_redex (oNode op ts) ->
        gdrives f (oNode op ts) r ->
        sdrives f (oNode op ts) r.

  (* A decidable "some rule fires at the root" test, bridging the relational
     `no_root_redex` to a boolean the concrete witnesses discharge by computation. *)
  Definition root_fires (t : Obj) : bool :=
    existsb (fun rl => match pat_match (fst rl) t with Some _ => true | None => false end) R.

  Lemma root_fires_false_no_root_redex :
    forall t, root_fires t = false -> no_root_redex t.
  Proof.
    intros t Hrf i u (p & r & bs & Hn & Hm & _).
    assert (Hin : In (p, r) R) by (eapply nth_error_In; exact Hn).
    assert (Htrue : root_fires t = true).
    { unfold root_fires. apply existsb_exists. exists (p, r).
      split; [exact Hin | simpl; rewrite Hm; reflexivity]. }
    rewrite Hrf in Htrue. discriminate.
  Qed.

  Scheme sgraft_mut := Minimality for sgraft Sort Prop
    with sgraft_list_mut := Minimality for sgraft_list Sort Prop.
  Combined Scheme sgraft_sgraft_list_mut from sgraft_mut, sgraft_list_mut.

  (* ===============================================================================
     9.  Helpers for the agreement (L3.3): a SKIP node never fires at its root, and a
         non-redex-root constructor never fires at all.
     =============================================================================== *)

  (* A SKIP node's RAW instantiation is not a root redex — DIRECTLY from scion_skip_sound
     (L3.1): mark false means every rule LHS could_unify-fails with the rhs-position, so
     by L3.1 no rule's pattern matches the instantiated node. *)
  Lemma mark_false_no_root_redex :
    forall c rs binds, mark (RApp c rs) = false ->
    no_root_redex (inst (RApp c rs) binds).
  Proof.
    intros c rs binds Hmark i u [p [r [bs [Hnth [Hmatch _]]]]].
    assert (Hin : In (p, r) R) by (eapply nth_error_In; exact Hnth).
    assert (Hcu : could_unify p (RApp c rs) = false).
    { apply not_true_is_false. intro Htrue.
      assert (Hex : existsb (fun rl => could_unify (fst rl) (RApp c rs)) R = true).
      { apply existsb_exists. exists (p, r). split; [exact Hin | simpl; exact Htrue]. }
      unfold mark in Hmark. rewrite Hmark in Hex. discriminate. }
    rewrite (scion_skip_sound p (RApp c rs) Hcu binds) in Hmatch. discriminate.
  Qed.

  (* A constructor that is NEVER a rule LHS root never fires at a node it heads — for ANY
     children (so the reassembled SKIP node, whatever its DRIVEN children, is inert).
     Needs the constructor-rooted well-formedness (a PVar-rooted rule would match it). *)
  Lemma not_redex_root_no_root_redex :
    rules_constructor_rooted = true ->
    forall c, is_ever_redex_root c = false ->
    forall vs, no_root_redex (oNode c vs).
  Proof.
    intros Hcr c Hier vs i u [p [r [bs [Hnth [Hmatch _]]]]].
    assert (Hin : In (p, r) R) by (eapply nth_error_In; exact Hnth).
    destruct p as [j | c' args].
    - unfold rules_constructor_rooted in Hcr. rewrite forallb_forall in Hcr.
      specialize (Hcr _ Hin). simpl in Hcr. discriminate.
    - rewrite pat_match_app in Hmatch.
      destruct (andb (Nat.eqb c' c) (Nat.eqb (length args) (length vs))) eqn:Eg;
        [| discriminate Hmatch].
      apply andb_true_iff in Eg. destruct Eg as [Ec _]. apply Nat.eqb_eq in Ec. subst c'.
      assert (Hex : existsb (fun rl => match root_ctor (fst rl) with
                                       | Some c'' => Nat.eqb c c'' | None => false end) R = true).
      { apply existsb_exists. exists (PApp c args, r). split; [exact Hin |].
        simpl. rewrite Nat.eqb_refl. reflexivity. }
      unfold is_ever_redex_root in Hier. rewrite Hier in Hex. discriminate.
  Qed.

  (* ===============================================================================
     L3.3 — SCION = CONTRACTUM-REDRIVE (SM-10).  THE core correctness: whatever the
     scion `sdrives` produces, the reference `gdrives` produces IDENTICALLY — same normal
     form AND the same fired multiset (in the same order, a fortiori a Permutation).  We
     use the plan's pre-declared FORWARD-INCLUSION fallback (`sdrives ⊆ gdrives`), which
     is CONSTRUCTIVE (it builds the gdrives derivation from the sdrives one, firing the
     SAME rules) and therefore needs NO confluence / determinism side condition; the
     full `∀ other gdrives result agrees` shape is this composed with gdrives determinism,
     which holds for the root-unambiguous witnesses below.

     The engine is `sgraft_forward`: grafting the RHS skeleton (SKIP inert, RECHECK
     resubmit, slots driven) computes EXACTLY what re-driving the whole instantiated
     contractum computes — SKIP nodes contribute nothing because (L3.1) their raw node
     is not a root redex so gdrives descends, and (graft_safe) their constructor is not a
     redex root so the post-join re-check of the DRIVEN reassembly is also inert.
     ================================================================================= *)

  Lemma sgraft_forward :
    rules_constructor_rooted = true ->
    (forall f rr binds r, sgraft f rr binds r ->
        rhs_graft_safe rr = true -> gdrives f (inst rr binds) r)
    /\ (forall f rrs binds dl, sgraft_list f rrs binds dl ->
        forallb rhs_graft_safe rrs = true ->
        gdrives_list f (map (fun r0 => inst r0 binds) rrs) dl).
  Proof.
    intro Hcr.
    apply (sgraft_sgraft_list_mut
      (fun f rr binds r => rhs_graft_safe rr = true -> gdrives f (inst rr binds) r)
      (fun f rrs binds dl => forallb rhs_graft_safe rrs = true ->
         gdrives_list f (map (fun r0 => inst r0 binds) rrs) dl)).
    - (* sg_var *) intros f j binds o r Hlk Hg _. cbn [inst]. rewrite Hlk. exact Hg.
    - (* sg_recheck *) intros f c rs binds r _ Hg _. exact Hg.
    - (* sg_skip *) intros f c rs binds vs fss Hmark Hsl IHsl Hsafe.
      cbn [rhs_graft_safe] in Hsafe. rewrite Hmark in Hsafe.
      apply andb_true_iff in Hsafe. destruct Hsafe as [Hier Hforall].
      apply negb_true_iff in Hier.
      cbn [inst].
      replace (Done (oNode c vs) fss)
        with (rlabels_prepend fss (Done (oNode c vs) []))
        by (cbn [rlabels_prepend]; rewrite app_nil_r; reflexivity).
      eapply g_descend.
      + exact (mark_false_no_root_redex c rs binds Hmark).
      + apply IHsl. exact Hforall.
      + apply grc_done. apply not_redex_root_no_root_redex; [exact Hcr | exact Hier].
    - (* sg_skip_fuel *) intros f c rs binds u Hmark Hsl IHsl Hsafe.
      cbn [rhs_graft_safe] in Hsafe. rewrite Hmark in Hsafe.
      apply andb_true_iff in Hsafe. destruct Hsafe as [_ Hforall].
      cbn [inst].
      eapply g_descend_fuel.
      + exact (mark_false_no_root_redex c rs binds Hmark).
      + apply IHsl. exact Hforall.
    - (* sgl_nil *) intros f binds _. cbn [map]. apply gdl_nil.
    - (* sgl_cons *) intros f r rs binds v gs vs fss Hsr IHsr Hsl IHsl Hforall.
      cbn [forallb] in Hforall. apply andb_true_iff in Hforall. destruct Hforall as [Hr Hrs].
      cbn [map]. apply gdl_cons; [apply IHsr; exact Hr | apply IHsl; exact Hrs].
    - (* sgl_cons_fuel_head *) intros f r rs binds u Hsr IHsr Hforall.
      cbn [forallb] in Hforall. apply andb_true_iff in Hforall. destruct Hforall as [Hr _].
      cbn [map]. apply gdl_cons_fuel_head. apply IHsr. exact Hr.
    - (* sgl_cons_fuel_tail *) intros f r rs binds v gs u Hsr IHsr Hsl IHsl Hforall.
      cbn [forallb] in Hforall. apply andb_true_iff in Hforall. destruct Hforall as [Hr Hrs].
      cbn [map]. eapply gdl_cons_fuel_tail; [apply IHsr; exact Hr | apply IHsl; exact Hrs].
  Qed.

  (* The scion driver is included in the redrive reference: same value, same fired
     multiset (identically). *)
  Theorem sdrives_included_in_gdrives :
    rules_constructor_rooted = true -> graft_safe = true ->
    forall f t r, sdrives f t r -> gdrives f t r.
  Proof.
    intros Hcr Hgs f t r Hs. destruct Hs.
    - apply g_free.
    - apply g_bound.
    - eapply g_fuel0. exact H.
    - (* s_fire *)
      eapply g_fire.
      + exists p, rr, binds. split; [exact H | split; [exact H0 | reflexivity]].
      + assert (Hin : In (p, rr) R) by (eapply nth_error_In; exact H).
        unfold graft_safe in Hgs. rewrite forallb_forall in Hgs.
        specialize (Hgs _ Hin). simpl in Hgs.
        exact (proj1 (sgraft_forward Hcr) f rr binds r H1 Hgs).
    - (* s_nonredex *) exact H0.
  Qed.

  (* ★ SM-10 AGREEMENT: the scion's (normal form, fired multiset) is EXACTLY a redrive
     result — hence the fired multisets agree up to Permutation (here, identically). *)
  Corollary sdrives_gdrives_agree :
    rules_constructor_rooted = true -> graft_safe = true ->
    forall f t v fs, sdrives f t (Done v fs) ->
    gdrives f t (Done v fs) /\ Permutation fs fs.
  Proof.
    intros Hcr Hgs f t v fs Hs.
    split; [exact (sdrives_included_in_gdrives Hcr Hgs f t (Done v fs) Hs) | apply Permutation_refl].
  Qed.

End ScionModel.

(* =================================================================================
   L3.6 — NON-VACUITY WITNESS (the W-B ladder, rung s=1).

   Rule table `ladder_R` (both rules root at `c_step`, mutually exclusive on the child
   tag, so root-DETERMINISTIC):

       R_step_wrap :  Step (Wrap x)  ~>  D1 (Step x)      (index 0)
       R_step_end  :  Step End       ~>  End              (index 1)

   graft-safe: the only SKIP constructor in an RHS skeleton is `D1` (and the ground
   `End`), neither a redex root.  On subject `Step (Wrap End)` BOTH the scion `sdrives`
   and the reference `gdrives` reach `Done (D1 End) [0; 1]` — the fired multiset {R_step_wrap,
   R_step_end} in the SAME order — witnessing the model is non-vacuous and the agreement
   (L3.3) is inhabited by a real two-firing chain (the R_step_wrap fire's RECHECK resubmit
   re-fires R_step_end through gdrives).
   ================================================================================= *)

Definition c_end : nat := 0.
Definition c_step : nat := 1.
Definition c_wrap : nat := 2.
Definition c_d1 : nat := 3.

Definition R_step_wrap : rule := (PApp c_step [PApp c_wrap [PVar 0]], RApp c_d1 [RApp c_step [RVar 0]]).
Definition R_step_end : rule := (PApp c_step [PApp c_end []], RApp c_end []).
Definition ladder_R : list rule := [R_step_wrap; R_step_end].

Definition tEnd : Obj := oNode c_end [].
Definition tStep (u : Obj) : Obj := oNode c_step [u].
Definition tWrap (u : Obj) : Obj := oNode c_wrap [u].
Definition tD1 (u : Obj) : Obj := oNode c_d1 [u].

Lemma ladder_constructor_rooted : rules_constructor_rooted ladder_R = true.
Proof. reflexivity. Qed.

Lemma ladder_graft_safe : graft_safe ladder_R = true.
Proof. reflexivity. Qed.

(* atomic gdrives facts *)
Lemma gd_End : forall f, gdrives ladder_R f tEnd (Done tEnd []).
Proof.
  intro f. unfold tEnd.
  apply (g_descend ladder_R f c_end [] [] [] (Done (oNode c_end []) [])).
  - apply root_fires_false_no_root_redex. reflexivity.
  - apply gdl_nil.
  - apply grc_done. apply root_fires_false_no_root_redex. reflexivity.
Qed.

Lemma gd_StepEnd : forall f, gdrives ladder_R (S f) (tStep tEnd) (Done tEnd [1]).
Proof.
  intro f. unfold tStep, tEnd.
  apply (g_fire ladder_R f 1 (oNode c_step [oNode c_end []]) (oNode c_end []) (Done (oNode c_end []) [])).
  - exists (PApp c_step [PApp c_end []]), (RApp c_end []), [].
    split; [reflexivity | split; reflexivity].
  - apply gd_End.
Qed.

Lemma sgraft_D1_Step : forall f,
  sgraft ladder_R (S f) (RApp c_d1 [RApp c_step [RVar 0]]) [(0, tEnd)] (Done (tD1 tEnd) [1]).
Proof.
  intro f. unfold tD1, tEnd.
  apply (sg_skip ladder_R (S f) c_d1 [RApp c_step [RVar 0]] [(0, oNode c_end [])]
                 [oNode c_end []] [1]).
  - reflexivity.
  - apply (sgl_cons ladder_R (S f) (RApp c_step [RVar 0]) [] [(0, oNode c_end [])]
                    (oNode c_end []) [1] [] []).
    + apply (sg_recheck ladder_R (S f) c_step [RVar 0] [(0, oNode c_end [])]
                        (Done (oNode c_end []) [1])).
      * reflexivity.
      * apply gd_StepEnd.
    + apply sgl_nil.
Qed.

Lemma sdrives_ladder_witness :
  sdrives ladder_R 5 (tStep (tWrap tEnd)) (Done (tD1 tEnd) [0; 1]).
Proof.
  unfold tStep, tWrap, tEnd, tD1.
  apply (s_fire ladder_R 4 0 (oNode c_step [oNode c_wrap [oNode c_end []]])
                (PApp c_step [PApp c_wrap [PVar 0]]) (RApp c_d1 [RApp c_step [RVar 0]])
                [(0, oNode c_end [])] (Done (oNode c_d1 [oNode c_end []]) [1])).
  - reflexivity.
  - reflexivity.
  - apply (sgraft_D1_Step 3).
Qed.

Lemma gdrives_ladder_witness :
  gdrives ladder_R 5 (tStep (tWrap tEnd)) (Done (tD1 tEnd) [0; 1]).
Proof.
  apply (sdrives_included_in_gdrives ladder_R ladder_constructor_rooted ladder_graft_safe).
  apply sdrives_ladder_witness.
Qed.

(* The witness, assembled: both drivers agree (same NF, same fired multiset). *)
Theorem ladder_scion_agrees :
  sdrives ladder_R 5 (tStep (tWrap tEnd)) (Done (tD1 tEnd) [0; 1])
  /\ gdrives ladder_R 5 (tStep (tWrap tEnd)) (Done (tD1 tEnd) [0; 1])
  /\ Permutation [0; 1] [0; 1].
Proof.
  split; [apply sdrives_ladder_witness |].
  split; [apply gdrives_ladder_witness | apply Permutation_refl].
Qed.

(* =================================================================================
   ★ THE NEGATIVE TEST — the FOLD-1 GUARD IS NECESSARY.

   Rule table `rtrig_R` (NOT graft-safe):

       R_trig :  Trig x   ~>  Bar (Wrap x)     (index 0)
       R_bar  :  Bar End  ~>  EndB             (index 1)   -- Bar is a redex ROOT
       R_wrap :  Wrap x   ~>  End              (index 2)

   In `R_trig`'s RHS `Bar (Wrap x)`, the `Bar` node is a SKIP (`mark = false`: no LHS
   syntactically could_unify with `Bar (Wrap _)` — `R_bar` demands `Bar End`, and
   `End <> Wrap _`), yet `Bar` IS a redex root (`R_bar`).  So `graft_safe rtrig_R = false`.

   On subject `Trig A` the two drivers DISAGREE:
     - `gdrives` (redrive) fully reduces: `Trig A` -> `Bar (Wrap A)`; re-driving,
       `Wrap A -> End`, and the post-join re-check of the reassembled `Bar End` FIRES
       `R_bar` -> `EndB`.  Result `Done EndB [0; 2; 1]`.
     - `sdrives` (scion) UNDER-reduces: it fires `R_trig`, drives the `Wrap` RECHECK
       (`Wrap A -> End`), but GRAFTS the `Bar` SKIP INERT — never re-checking it — so it
       misses the fresh `Bar End` redex.  Result `Done (Bar End) [0; 2]` — a DIFFERENT
       normal form AND a fired multiset MISSING `R_bar`.

   Hence the `graft_safe` hypothesis of `sdrives_included_in_gdrives` (L3.3) is NECESSARY:
   drop it and the scion is unsound.  This is the mechanized form of the runtime
   scion_grafting.rs guard-necessity probe.
   ================================================================================= *)

Definition c_trig : nat := 4.
Definition c_bar : nat := 5.
Definition c_endb : nat := 6.

Definition R_trig : rule := (PApp c_trig [PVar 0], RApp c_bar [RApp c_wrap [RVar 0]]).
Definition R_bar : rule := (PApp c_bar [PApp c_end []], RApp c_endb []).
Definition R_wrap : rule := (PApp c_wrap [PVar 0], RApp c_end []).
Definition rtrig_R : list rule := [R_trig; R_bar; R_wrap].

Definition tA : Obj := oFree 0.
Definition tBar (u : Obj) : Obj := oNode c_bar [u].
Definition tEndB : Obj := oNode c_endb [].
Definition tTrig (u : Obj) : Obj := oNode c_trig [u].

(* atomic gdrives facts for rtrig_R *)
Lemma gd_End_rt : forall f, gdrives rtrig_R f tEnd (Done tEnd []).
Proof.
  intro f. unfold tEnd.
  apply (g_descend rtrig_R f c_end [] [] [] (Done (oNode c_end []) [])).
  - apply root_fires_false_no_root_redex. reflexivity.
  - apply gdl_nil.
  - apply grc_done. apply root_fires_false_no_root_redex. reflexivity.
Qed.

Lemma gd_EndB : forall f, gdrives rtrig_R f tEndB (Done tEndB []).
Proof.
  intro f. unfold tEndB.
  apply (g_descend rtrig_R f c_endb [] [] [] (Done (oNode c_endb []) [])).
  - apply root_fires_false_no_root_redex. reflexivity.
  - apply gdl_nil.
  - apply grc_done. apply root_fires_false_no_root_redex. reflexivity.
Qed.

Lemma gd_WrapA : forall f, gdrives rtrig_R (S f) (tWrap tA) (Done tEnd [2]).
Proof.
  intro f. unfold tWrap, tA, tEnd.
  apply (g_fire rtrig_R f 2 (oNode c_wrap [oFree 0]) (oNode c_end []) (Done (oNode c_end []) [])).
  - exists (PApp c_wrap [PVar 0]), (RApp c_end []), [(0, oFree 0)].
    split; [reflexivity | split; reflexivity].
  - apply gd_End_rt.
Qed.

Lemma gd_BarWrapA : forall f, gdrives rtrig_R (S (S f)) (tBar (tWrap tA)) (Done tEndB [2; 1]).
Proof.
  intro f. unfold tBar, tWrap, tA, tEndB.
  apply (g_descend rtrig_R (S (S f)) c_bar [oNode c_wrap [oFree 0]]
                   [oNode c_end []] [2] (Done (oNode c_endb []) [1])).
  - apply root_fires_false_no_root_redex. reflexivity.
  - apply (gdl_cons rtrig_R (S (S f)) (oNode c_wrap [oFree 0]) []
                    (oNode c_end []) [2] [] []).
    + apply gd_WrapA.
    + apply gdl_nil.
  - apply (grc_fire rtrig_R (S f) 1 (oNode c_bar [oNode c_end []]) (oNode c_endb [])
                    (Done (oNode c_endb []) [])).
    + exists (PApp c_bar [PApp c_end []]), (RApp c_endb []), [].
      split; [reflexivity | split; reflexivity].
    + apply gd_EndB.
Qed.

Lemma gdrives_trig_witness : gdrives rtrig_R 5 (tTrig tA) (Done tEndB [0; 2; 1]).
Proof.
  unfold tTrig, tA.
  apply (g_fire rtrig_R 4 0 (oNode c_trig [oFree 0]) (oNode c_bar [oNode c_wrap [oFree 0]])
                (Done tEndB [2; 1])).
  - exists (PApp c_trig [PVar 0]), (RApp c_bar [RApp c_wrap [RVar 0]]), [(0, oFree 0)].
    split; [reflexivity | split; reflexivity].
  - apply (gd_BarWrapA 2).
Qed.

(* the scion UNDER-reduces: Bar is grafted inert, its fresh redex missed *)
Lemma sgraft_Bar_Wrap : forall f,
  sgraft rtrig_R (S f) (RApp c_bar [RApp c_wrap [RVar 0]]) [(0, tA)] (Done (tBar tEnd) [2]).
Proof.
  intro f. unfold tBar, tEnd, tA.
  apply (sg_skip rtrig_R (S f) c_bar [RApp c_wrap [RVar 0]] [(0, oFree 0)]
                 [oNode c_end []] [2]).
  - reflexivity.
  - apply (sgl_cons rtrig_R (S f) (RApp c_wrap [RVar 0]) [] [(0, oFree 0)]
                    (oNode c_end []) [2] [] []).
    + apply (sg_recheck rtrig_R (S f) c_wrap [RVar 0] [(0, oFree 0)]
                        (Done (oNode c_end []) [2])).
      * reflexivity.
      * apply gd_WrapA.
    + apply sgl_nil.
Qed.

Lemma sdrives_trig_witness : sdrives rtrig_R 5 (tTrig tA) (Done (tBar tEnd) [0; 2]).
Proof.
  unfold tTrig, tA.
  apply (s_fire rtrig_R 4 0 (oNode c_trig [oFree 0])
                (PApp c_trig [PVar 0]) (RApp c_bar [RApp c_wrap [RVar 0]])
                [(0, oFree 0)] (Done (tBar tEnd) [2])).
  - reflexivity.
  - reflexivity.
  - apply (sgraft_Bar_Wrap 3).
Qed.

Theorem negative_test_fold1_guard_necessary :
  graft_safe rtrig_R = false
  /\ rules_constructor_rooted rtrig_R = true
  /\ sdrives rtrig_R 5 (tTrig tA) (Done (tBar tEnd) [0; 2])
  /\ gdrives rtrig_R 5 (tTrig tA) (Done tEndB [0; 2; 1])
  /\ tBar tEnd <> tEndB.
Proof.
  split; [reflexivity |].
  split; [reflexivity |].
  split; [apply sdrives_trig_witness |].
  split; [apply gdrives_trig_witness |].
  unfold tBar, tEnd, tEndB. intro H. discriminate H.
Qed.

(* =================================================================================
   L3.4 — THE STRUCTURAL-FIRE WEAK BISIMULATION (reusing the landed kit).

   We instantiate InRhoBetaCascadeWeakBisim's `is_weak_bisimulation` / `represents`
   (norm-equality) for the SCION's structural firing, exactly as the driver's
   `drive_weak_bisim` did for beta — but structural firing is CHEAPER: a structural rule's
   RHS is a pure constructor tree over slots, so the sigma-receiver template
   `for(sigma.., out<-c){out!(rhs_par)}` (rho_net_lower.rs) lands the visible fire
   DIRECTLY on `embed (reduct)`, an object already in normal form (`norm_embed`).  There is
   NO `^subst`/`^shift` tau-cascade to collapse (that is beta-only), so the weak
   transition's tau-suffix is EMPTY (`star_refl`) and the bisimulation needs NO
   SN/confluence argument — a strictly weaker dependency than the beta cascade's.

   The `op` index is a phantom inherited from the generic kit's beta-specialized
   transition signature: the structural fire is not root-ctor-indexed (every rule in `R`
   is available at every node), so `op` is ignored by `asfire`.
   ================================================================================= *)

(* abstract single structural ROOT fire by SOME rule of R *)
Definition asfire (R : list rule) (op : nat) (o o' : Obj) : Prop :=
  exists i, fires R i o o'.

(* concrete single structural fire: land DIRECTLY on the embedded reduct (no cascade) *)
Inductive csfire (R : list rule) (op : nat) : Tm -> Tm -> Prop :=
  | csfire_fire : forall o o', asfire R op o o' -> csfire R op (embed o) (embed o').

(* concrete WEAK visible transition: tau* (reflect the redex) ; fire ; tau* (EMPTY here) *)
Definition cswvis (R : list rule) (op : nat) (c c' : Tm) : Prop :=
  exists c1 c2, star c c1 /\ csfire R op c1 c2 /\ star c2 c'.

Inductive siter (R : list rule) (op : nat) : Obj -> Obj -> Prop :=
  | siter_refl : forall o, siter R op o o
  | siter_cons : forall o o' o'',
      asfire R op o o' -> siter R op o' o'' -> siter R op o o''.

Inductive csiter (R : list rule) (op : nat) : Tm -> Tm -> Prop :=
  | csiter_refl : forall c, csiter R op c c
  | csiter_cons : forall c c' c'',
      cswvis R op c c' -> csiter R op c' c'' -> csiter R op c c''.

(* FORWARD (single fire): an abstract structural fire is matched by an in-Rho weak
   transition landing on the embedded reduct (empty tau-suffix). *)
Lemma sfire_forward : forall R op o c o',
  represents o c -> asfire R op o o' ->
  exists c', cswvis R op c c' /\ represents o' c'.
Proof.
  intros R op o c o' Hrep Hfire.
  exists (embed o'). split.
  - exists (embed o), (embed o'). split; [| split].
    + pose proof (reduces_to_norm c) as H. unfold represents in Hrep. rewrite Hrep in H. exact H.
    + apply csfire_fire. exact Hfire.
    + apply star_refl.
  - unfold represents. apply norm_embed.
Qed.

(* BACKWARD (single fire): an in-Rho structural weak transition is matched by an abstract
   fire; the tau-prefix cannot change `norm`, the fire lands on an embedded object, and the
   (empty) tau-suffix preserves `norm`. *)
Lemma sfire_backward : forall R op o c c',
  represents o c -> cswvis R op c c' ->
  exists o', asfire R op o o' /\ represents o' c'.
Proof.
  intros R op o c c' Hrep Hcwvis.
  destruct Hcwvis as [c1 [c2 [Hpre [Hfire Hpost]]]].
  inversion Hfire as [o0 o0' Hasf Hc1 Hc2]. subst c1 c2.
  exists o0'. split.
  - assert (Ho : o = o0).
    { unfold represents in Hrep. rewrite <- Hrep.
      rewrite (star_preserves_norm c (embed o0) Hpre). apply norm_embed. }
    rewrite Ho. exact Hasf.
  - unfold represents. rewrite <- (star_preserves_norm (embed o0') c' Hpost).
    apply norm_embed.
Qed.

(* THE ITERATED weak bisimulation (single-fire clauses lifted to chains, exactly the
   `drive_weak_bisim` shape). *)
Theorem sdrives_weak_bisim :
  forall R, is_weak_bisimulation represents (siter R) (csiter R).
Proof.
  intro R. split.
  - (* forward: abstract chain matched by concrete chain *)
    intros o c op o' Hrep Hiter. revert c Hrep.
    induction Hiter as [o | o o1 o2 Hstep Hiter IH]; intros c Hrep.
    + exists c. split; [apply csiter_refl | exact Hrep].
    + destruct (sfire_forward R op o c o1 Hrep Hstep) as [c1 [Hc1 Hrep1]].
      destruct (IH c1 Hrep1) as [c2 [Hc2 Hrep2]].
      exists c2. split; [eapply csiter_cons; [exact Hc1 | exact Hc2] | exact Hrep2].
  - (* backward: concrete chain matched by abstract chain *)
    intros o c op c' Hrep Hiter. revert o Hrep.
    induction Hiter as [c | c c1 c2 Hstep Hiter IH]; intros o Hrep.
    + exists o. split; [apply siter_refl | exact Hrep].
    + destruct (sfire_backward R op o c c1 Hrep Hstep) as [o1 [Ho1 Hrep1]].
      destruct (IH o1 Hrep1) as [o2 [Ho2 Hrep2]].
      exists o2. split; [eapply siter_cons; [exact Ho1 | exact Ho2] | exact Hrep2].
Qed.
