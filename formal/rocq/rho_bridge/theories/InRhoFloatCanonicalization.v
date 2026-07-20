(*
 * InRhoFloatCanonicalization: FV (A-S5.8) — the generated in-Rho `^float` receiver
 * family (rholang-codegen/src/rho_net_float.rs: the dispatcher, the equation-derived
 * `^float-hoist:{C}` / `^float-merge:{op}` satellites, and the `^shift` soup/Nil arms)
 * modeled over the NAMELESS (de Bruijn) reflected ABI in the RUN-LENGTH configuration
 * representation, with the theorems the design (a_s5_8_float_design_v1.md section 6,
 * amendments F8-AM-3/F8-AM-4) names:
 *
 *   hoist_side_condition_by_shift_image / fstep_side_condition :
 *       the C-G side condition `x not in fn(P)` of every (Struct Res Par) /
 *       (Struct Res Amb) / capability-extension instance the float takes is discharged
 *       BY THE SHIFT-IMAGE ARGUMENT — a shift's image never references the extruded
 *       binder window, so NO alpha-freshening (gensym) is needed in-Rho.
 *   float_step_sound (= fstep_side_condition + float_reachable) :
 *       every float step (`fstep`, the one-member run extrusion the merge/hoist
 *       satellites realize) is a C-G-subset composite whose shifted siblings satisfy
 *       that side condition, and the float FUNCTION is reached by exactly these steps.
 *   float_functional_up_to_NewComm (the F8-AM-4 split, first half) :
 *       the float is a RELATION through the peel choice — processing the members in ANY
 *       order yields the same run length and bodies related by exactly a
 *       run-permutation-induced index renaming with an explicit two-sided inverse (the
 *       NewComm class; schedule confluence — the Q-NC record: the family has NO reorder
 *       arm, so the run order is the float's only schedule-visible degree of freedom).
 *   float_identity_on_canonical (the F8-AM-4 split, second half) :
 *       on an already-canonical configuration the float is the EXACT identity (the
 *       model's list body already quotients the Par send-order / bag-multiset degrees
 *       the in-Rho value adds).
 *   float_preserves_bag_flatness :
 *       the merge base's THREE-CASE dispatch (Nil / same-op-soup-splice / wrap —
 *       `bag_fragment_dispatch`) preserves bag flatness — the AM-2 obligation IN-RHO
 *       (BinderFloatCanonicalization.v Part 2 is the HOST `insert_into` mirror; this is
 *       the in-Rho splice's one-level form under the AM-3(b) drive induction: the
 *       recursion delivers already-floated — hence flat — fragments).
 *   float_exposes_redexes_{in,open,out} :
 *       over the extrusion + bag-permutation equivalence (`dequiv` — the float's OWN
 *       moves), a redex exists modulo the equivalence IFF it is syntactically present
 *       in the float normal form.
 *   redex_invariant_under_run_permutation (F8-AM-3) :
 *       the redex predicates are closed under the injective index renaming a NewComm
 *       run permutation induces — the NEW de Bruijn lemma.
 *       BinderFloatCanonicalization.v:381-397's in/open/out_redex_perm cover
 *       BAG-permutation invariance ONLY (they permute the member list); permuting a de
 *       Bruijn RUN reindexes the body, which those lemmas do not touch.  Redex shapes
 *       need only SAME-NAME equality between member positions, preserved AND reflected
 *       by any injective renaming.
 *
 * ---------------------------------------------------------------------------------------
 * THE MODEL (and its faithfulness boundary)
 * ---------------------------------------------------------------------------------------
 *
 * Names are de Bruijn: `NB n` references the n-th enclosing nu binder (innermost = 0),
 * `NF x` is free — the reflected `^bound(peano n)` / `^free(x)` ABI.  A configuration
 * is a RUN LENGTH (the top `^lambda` run the float assembles) over a bag of members,
 * each a run-length prefix over a depth-2 core (ambient-with-inner-capabilities /
 * capability / opaque — the fragment the Ambient rewrite patterns inspect, with inner
 * nu runs ALREADY hoisted to the member prefix: the `^float-hoist:{C}` satellites
 * perform exactly that inner hoist, one binder per step, and
 * `hoist_side_condition_by_shift_image` is the per-wrapper discharge).  Extruding one
 * member's prefix into the configuration run (`fstep`) shifts every OTHER member by the
 * extruded length ABOVE its own binders (`bump j k` — the `^shift` satellite calls the
 * merge emits, composed), and the extruded member's own references are untouched (its
 * binders move with it).  The float FUNCTION (`dfloat`) extrudes members left-to-right
 * — the merge's u-first deterministic order (the first-processed member's binders end
 * OUTERMOST); the real dispatcher's peel choice is the processing ORDER, modeled as a
 * `Permutation` of the member list (`float_functional_up_to_NewComm`).  The OutRule
 * exposure is stated for a FREE cross-level name (every renaming in play fixes `NF x`);
 * a bound cross-level name transports along the same renamings, as
 * `redex_invariant_under_run_permutation`'s out clause makes precise.
 *
 * Rocq 9.1 compatible.  No Admitted, no Axioms, no Assumptions, no Parameters.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.

Import ListNotations.

(* The window-arithmetic workhorse: interleave simplification with `Nat.leb`/`Nat.ltb`
   condition splitting (each split may expose further reducible shifts), then discharge
   index equalities/absurdities with lia. *)
Ltac window :=
  repeat (simpl in *;
    match goal with
    | [ H : Nat.leb _ _ = true |- _ ] => apply Nat.leb_le in H
    | [ H : Nat.leb _ _ = false |- _ ] => apply Nat.leb_gt in H
    | [ H : Nat.ltb _ _ = true |- _ ] => apply Nat.ltb_lt in H
    | [ H : Nat.ltb _ _ = false |- _ ] => apply Nat.ltb_ge in H
    (* simpl unfolds `Nat.leb (S k) n` one step into a match on `n`; split the
       scrutinee so the inner `leb` pattern resurfaces. *)
    | [ |- context [match ?n with 0 => false | S m => Nat.leb _ m end] ] =>
        destruct n eqn:?
    | [ |- context [Nat.leb ?a ?b] ] => destruct (Nat.leb a b) eqn:?
    | [ |- context [Nat.ltb ?a ?b] ] => destruct (Nat.ltb a b) eqn:?
    end);
  simpl in *;
  try reflexivity; try (f_equal; lia); try lia.

(* =====================================================================================
   Part 1 — de Bruijn names, the shift (`bump`), the renaming, and THE SHIFT-IMAGE
   ARGUMENT (the discharged C-G side condition).
   ===================================================================================== *)

Inductive dname : Type :=
  | NB : nat -> dname     (* ^bound(n) — the n-th enclosing binder, innermost = 0 *)
  | NF : nat -> dname.    (* ^free(x) — inert under shift and float *)

(* `bump c k`: add `k` to every bound index at or above the cutoff `c` — `k` composed
   applications of the in-Rho `^shift(c, .)` receiver (each adds exactly 1 at `c`). *)
Definition bump (c k : nat) (N : dname) : dname :=
  match N with
  | NB n => if Nat.leb c n then NB (n + k) else NB n
  | NF x => NF x
  end.

(* An index renaming applied to bound references (free names inert) — the form a NewComm
   run permutation induces on a body under the run (F8-AM-3). *)
Definition drename (rho : nat -> nat) (N : dname) : dname :=
  match N with
  | NB n => NB (rho n)
  | NF x => NF x
  end.

Lemma bump_zero : forall c N, bump c 0 N = N.
Proof. intros c [n | x]; simpl; window. Qed.

(* Composing two bumps at ONE cutoff adds the amounts — the chained `^shift(Z, .)`
   calls of the F8-AM-1c sigma-slot rule and of the reach induction below. *)
Lemma bump_compose : forall c j k N, bump c j (bump c k N) = bump c (k + j) N.
Proof. intros c j k [n | x]; simpl; window. Qed.

(* THE SHIFT-IMAGE WINDOW: a bump's image never lands INSIDE the window `[c, c + k)` —
   the freshly-extruded binder positions. *)
Theorem bump_image_avoids_window : forall c k n p,
  bump c k (NB n) = NB p -> p < c \/ c + k <= p.
Proof.
  intros c k n p H. simpl in H.
  destruct (Nat.leb c n) eqn:Hcn; injection H as <-; window.
Qed.

(* ** THE DISCHARGED SIDE CONDITION (design section 1, "THE CAPTURE-SAFETY ANSWER"):
   floating a binder run of length `k` past sibling material shifted at cutoff 0 leaves
   the extruded binders UNREFERENCED by that material — the C-G freshness premise
   `x not in fn(P)` of (Struct Res Par) / (Struct Res Amb) / the capability extensions
   holds BY CONSTRUCTION of the shift, with NO gensym. *)
Theorem hoist_side_condition_by_shift_image : forall k N i,
  i < k -> bump 0 k N <> NB i.
Proof.
  intros k N i Hik H.
  destruct N as [n | x]; simpl in H; [| discriminate H].
  injection H as <-. lia.
Qed.

(* =====================================================================================
   Part 2 — the depth-2 fragment over de Bruijn names, the renaming functor, and the
   redex predicates (the de Bruijn guard = same-name equality between member positions,
   the reflected `N == N` MatchCase.guard).
   ===================================================================================== *)

Inductive Cap : Type := CIn | COut | COpen.

(* A depth-2 member core: an ambient over inner capability prefixes (continuations
   opaque — the MA strengthening: rewrite LHSs bind them as variables), a bare
   capability, or opaque material.  Inner nu runs are ALREADY member-hoisted. *)
Inductive bcore : Type :=
  | BAmb : dname -> list (Cap * dname) -> bcore
  | BCap : Cap -> dname -> bcore
  | BOpq : nat -> bcore.

Definition map_inner (f : dname -> dname) (i : Cap * dname) : Cap * dname :=
  (fst i, f (snd i)).

Definition map_bname (f : dname -> dname) (b : bcore) : bcore :=
  match b with
  | BAmb N inner => BAmb (f N) (map (map_inner f) inner)
  | BCap c N => BCap c (f N)
  | BOpq a => BOpq a
  end.

Lemma map_inner_ext : forall f g i, (forall N, f N = g N) -> map_inner f i = map_inner g i.
Proof. intros f g [c N] H. unfold map_inner. simpl. rewrite H. reflexivity. Qed.

Lemma map_bname_ext : forall f g b, (forall N, f N = g N) -> map_bname f b = map_bname g b.
Proof.
  intros f g [N inner | c N | a] H; simpl.
  - rewrite H. f_equal. apply map_ext. intro i. apply map_inner_ext. exact H.
  - rewrite H. reflexivity.
  - reflexivity.
Qed.

Lemma map_bname_compose : forall f g b,
  map_bname f (map_bname g b) = map_bname (fun N => f (g N)) b.
Proof.
  intros f g [N inner | c N | a]; simpl; try reflexivity.
  f_equal. rewrite map_map. apply map_ext. intros [c N']. reflexivity.
Qed.

Lemma map_bname_id : forall f b, (forall N, f N = N) -> map_bname f b = b.
Proof.
  intros f [N inner | c N | a] H; simpl.
  - rewrite H. f_equal. induction inner as [| [c N'] rest IH]; simpl; [reflexivity |].
    unfold map_inner at 1. simpl. rewrite H, IH. reflexivity.
  - rewrite H. reflexivity.
  - reflexivity.
Qed.

(* A member: a run-length nu prefix over a core.  A configuration: the top run over the
   member bag. *)
Definition OM : Type := (nat * bcore)%type.
Record DCfg : Type := mkDC { dc_run : nat; dc_body : list OM }.

Definition bump_om (k : nat) (m : OM) : OM :=
  (fst m, map_bname (bump (fst m) k) (snd m)).

Definition rename_om (rho : nat -> nat) (m : OM) : OM :=
  (fst m, map_bname (drename rho) (snd m)).

Lemma rename_om_compose : forall r1 r2 m,
  rename_om r2 (rename_om r1 m) = rename_om (fun i => r2 (r1 i)) m.
Proof.
  intros r1 r2 [r d]. unfold rename_om. simpl. f_equal.
  rewrite map_bname_compose. apply map_bname_ext.
  intros [n | x]; reflexivity.
Qed.

Lemma rename_om_id : forall rho m, (forall i, rho i = i) -> rename_om rho m = m.
Proof.
  intros rho [r d] H. unfold rename_om. simpl. f_equal.
  apply map_bname_id. intros [n | x]; simpl; [rewrite H |]; reflexivity.
Qed.

(* ------------------------------------------------------------------------------------
   The syntactic redexes: prefix-free (run-0) members whose de Bruijn GUARD is
   same-name equality between the two member positions.
   ------------------------------------------------------------------------------------ *)

Definition in_redex (body : list OM) : Prop :=
  exists n m i1 i2 rest,
    Permutation body ((0, BAmb n i1) :: (0, BAmb m i2) :: rest)
    /\ In (CIn, m) i1.

Definition open_redex (body : list OM) : Prop :=
  exists n inner rest,
    Permutation body ((0, BCap COpen n) :: (0, BAmb n inner) :: rest).

Definition out_redex (m : dname) (body : list OM) : Prop :=
  exists n inner rest,
    Permutation body ((0, BAmb n inner) :: rest)
    /\ In (COut, m) inner.

(* Bag-permutation invariance — the SAME content as BinderFloatCanonicalization.v's
   in/open/out_redex_perm (:381-397), re-established over the de Bruijn shapes.  (That
   file is cited for the bag-permutation invariance ONLY; the run-permutation content is
   Part 4's NEW lemma.) *)
Lemma in_redex_perm : forall body body',
  Permutation body body' -> in_redex body -> in_redex body'.
Proof.
  intros body body' Hperm (n & m & i1 & i2 & rest & Hp & Hin).
  exists n, m, i1, i2, rest. split; [| exact Hin].
  eapply Permutation_trans; [apply Permutation_sym; exact Hperm | exact Hp].
Qed.

Lemma open_redex_perm : forall body body',
  Permutation body body' -> open_redex body -> open_redex body'.
Proof.
  intros body body' Hperm (n & inner & rest & Hp).
  exists n, inner, rest.
  eapply Permutation_trans; [apply Permutation_sym; exact Hperm | exact Hp].
Qed.

Lemma out_redex_perm : forall m body body',
  Permutation body body' -> out_redex m body -> out_redex m body'.
Proof.
  intros m body body' Hperm (n & inner & rest & Hp & Hin).
  exists n, inner, rest. split; [| exact Hin].
  eapply Permutation_trans; [apply Permutation_sym; exact Hperm | exact Hp].
Qed.

(* =====================================================================================
   Part 3 — the float: run sums, the one-member extrusion step (`fstep`) with its side
   condition, the float function (tail-parameterized closed form), reachability, and
   float_identity_on_canonical.
   ===================================================================================== *)

Fixpoint run_sum (body : list OM) : nat :=
  match body with
  | [] => 0
  | m :: rest => fst m + run_sum rest
  end.

Lemma run_sum_app : forall a b, run_sum (a ++ b) = run_sum a + run_sum b.
Proof. induction a as [| m a IH]; intro b; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma run_sum_map_bump : forall k body, run_sum (map (bump_om k) body) = run_sum body.
Proof.
  induction body as [| [j d] rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma run_sum_perm : forall a b, Permutation a b -> run_sum a = run_sum b.
Proof. intros a b H. induction H; simpl; lia. Qed.

(* ONE FLOAT STEP (the merge/hoist satellites' composed action): extrude one member's
   whole run `k >= 1` to the BOTTOM of the configuration run; every OTHER member's
   names bump by `k` above its own binders (`bump j k` — the `^shift` calls); the
   extruded member's own references are untouched (its binders move with it).

   C-G reading (float_step_sound): the composite of `k` (Struct Res Par) instances at
   the bag seam, each side condition discharged by the shift image
   (`fstep_side_condition` below; `hoist_side_condition_by_shift_image` for the
   per-wrapper hoists that pre-assembled the member run). *)
Inductive fstep : DCfg -> DCfg -> Prop :=
  | fs_extrude : forall R pre k c post,
      1 <= k ->
      fstep (mkDC R (pre ++ (k, c) :: post))
            (mkDC (R + k)
                  (map (bump_om k) pre ++ (0, c) :: map (bump_om k) post)).

(* Name occurrence in a core. *)
Definition name_in_core (N : dname) (b : bcore) : Prop :=
  match b with
  | BAmb M inner => N = M \/ In N (map snd inner)
  | BCap _ M => N = M
  | BOpq _ => False
  end.

Lemma name_in_map_bname : forall f N b,
  name_in_core N (map_bname f b) -> exists N', N = f N' /\ name_in_core N' b.
Proof.
  intros f N [M inner | c M | a] H; simpl in H.
  - destruct H as [-> | H].
    + exists M. split; [reflexivity | left; reflexivity].
    + rewrite map_map in H. apply in_map_iff in H.
      destruct H as [[c' M'] [HN Hin]]. simpl in HN. subst N.
      exists M'. split; [reflexivity | right].
      apply in_map_iff. exists (c', M'). split; [reflexivity | exact Hin].
  - subst N. exists M. split; reflexivity.
  - contradiction.
Qed.

(* ** float_step_sound, side-condition half: in a step's result, NO shifted sibling
   references the freshly-extruded window — its names sit below its own binders or
   above the extruded block.  This IS the C-G freshness premise `x not in fn(P)`, held
   by the shift image, never by gensym. *)
Theorem fstep_side_condition : forall k j d n,
  name_in_core (NB n) (map_bname (bump j k) d) -> n < j \/ j + k <= n.
Proof.
  intros k j d n H.
  apply name_in_map_bname in H. destruct H as [N' [HN _]].
  symmetry in HN.
  destruct N' as [n' | x']; simpl in HN; [| discriminate HN].
  eapply bump_image_avoids_window. exact HN.
Qed.

(* The per-member float renaming: own references (`n < k`, bound by the member's run)
   land above the LATER-extruded blocks (`+ S`); outer references (`n >= k`) land above
   the whole new block (`+ O`, with `O = total - k` in the closed instantiation). *)
Definition mem_float_map (k S O : nat) (N : dname) : dname :=
  match N with
  | NB n => if Nat.ltb n k then NB (n + S) else NB (n + O)
  | NF x => NF x
  end.

(* The float body, TAIL-parameterized: `total` is the whole extruded block (all members
   of the top-level call), `tail` the run mass of members BEYOND this sublist (0 at the
   top).  Member `(k, c)`'s later-mass is `run_sum rest + tail`. *)
Fixpoint dfm (total tail : nat) (body : list OM) : list OM :=
  match body with
  | [] => []
  | (k, c) :: rest =>
      (0, map_bname (mem_float_map k (run_sum rest + tail) (total - k)) c)
        :: dfm total tail rest
  end.

Definition dfloat (cfg : DCfg) : DCfg :=
  mkDC (dc_run cfg + run_sum (dc_body cfg))
       (dfm (run_sum (dc_body cfg)) 0 (dc_body cfg)).

Lemma dfm_app : forall a b total tail,
  dfm total tail (a ++ b) = dfm total (run_sum b + tail) a ++ dfm total tail b.
Proof.
  induction a as [| [k c] a IH]; intros b total tail; simpl; [reflexivity |].
  rewrite IH. rewrite run_sum_app. rewrite <- Nat.add_assoc. reflexivity.
Qed.

(* ------------------------------------------------------------------------------------
   float_canonicalizes + float_identity_on_canonical (the F8-AM-4 second half).
   ------------------------------------------------------------------------------------ *)

Definition canonical_body (body : list OM) : Prop :=
  Forall (fun m : OM => fst m = 0) body.

Lemma dfm_canonical : forall body total tail, canonical_body (dfm total tail body).
Proof.
  induction body as [| [k c] rest IH]; intros total tail; simpl.
  - apply Forall_nil.
  - apply Forall_cons; [reflexivity | apply IH].
Qed.

Theorem float_canonicalizes : forall cfg, canonical_body (dc_body (dfloat cfg)).
Proof. intros [R body]. apply dfm_canonical. Qed.

Lemma canonical_run_sum : forall body, canonical_body body -> run_sum body = 0.
Proof.
  induction body as [| [k c] rest IH]; intro H; simpl; [reflexivity |].
  inversion H as [| ? ? Hk Hrest]; subst. simpl in Hk. subst k.
  rewrite (IH Hrest). reflexivity.
Qed.

(* ** float_identity_on_canonical (F8-AM-4): on an already-canonical configuration the
   float is the EXACT identity — a second pass strips nothing, the merges hit their
   base cases, the run rewraps in place, never re-permuted.  (The model's list body
   already quotients the Par send-order / bag-multiset degrees the in-Rho value adds,
   so the statement's "up to Par send-order / bag multiset" is exact equality here.) *)
Theorem float_identity_on_canonical : forall cfg,
  canonical_body (dc_body cfg) -> dfloat cfg = cfg.
Proof.
  intros [R body] Hcanon. unfold dfloat. simpl in *.
  rewrite (canonical_run_sum body Hcanon). rewrite Nat.add_0_r. f_equal.
  induction body as [| [k c] rest IH]; simpl; [reflexivity |].
  inversion Hcanon as [| ? ? Hk Hrest]; subst. simpl in Hk. subst k.
  rewrite IH by exact Hrest.
  rewrite (canonical_run_sum rest Hrest).
  rewrite map_bname_id; [reflexivity |].
  intros [n | x]; simpl; window.
Qed.

(* ------------------------------------------------------------------------------------
   float_reachable (the reachability half of float_step_sound).
   ------------------------------------------------------------------------------------ *)

Inductive fsteps : DCfg -> DCfg -> Prop :=
  | fsteps_refl : forall cfg, fsteps cfg cfg
  | fsteps_cons : forall a b c, fstep a b -> fsteps b c -> fsteps a c.

Lemma fsteps_trans : forall a b c, fsteps a b -> fsteps b c -> fsteps a c.
Proof.
  intros a b c Hab. revert c. induction Hab as [a | a x b Hs Hab IH]; intros c Hbc.
  - exact Hbc.
  - eapply fsteps_cons; [exact Hs | apply IH; exact Hbc].
Qed.

Lemma bump_om_compose : forall j k m, bump_om j (bump_om k m) = bump_om (k + j) m.
Proof.
  intros j k [r d]. unfold bump_om. simpl. f_equal.
  rewrite map_bname_compose. apply map_bname_ext.
  intro N. apply bump_compose.
Qed.

Lemma map_bump_om_compose : forall j k body,
  map (bump_om j) (map (bump_om k) body) = map (bump_om (k + j)) body.
Proof.
  intros j k body. rewrite map_map. apply map_ext. intro m. apply bump_om_compose.
Qed.

Lemma map_bump_om_zero : forall body, map (bump_om 0) body = body.
Proof.
  induction body as [| [r d] rest IH]; simpl; [reflexivity |].
  unfold bump_om at 1. simpl.
  rewrite map_bname_id by (intro N; apply bump_zero).
  rewrite IH. reflexivity.
Qed.

(* Bump-then-float equals float-at-the-larger-total — the pointwise account of one
   extrusion's effect on the members still awaiting theirs.  (`run_sum body <= total`
   holds at every use: a member's run is a summand of the floated list's total.) *)
Lemma dfm_of_bumped : forall body total tail k,
  run_sum body <= total ->
  dfm total tail (map (bump_om k) body) = dfm (total + k) tail body.
Proof.
  induction body as [| [j d] rest IH]; intros total tail k Hle; simpl; [reflexivity |].
  simpl in Hle.
  rewrite run_sum_map_bump.
  rewrite IH by lia.
  f_equal.
  unfold bump_om. simpl. f_equal.
  rewrite map_bname_compose.
  apply map_bname_ext. intros [n | x]; simpl; [| reflexivity].
  window.
Qed.

(* The generalized reach: the members still awaiting extrusion carry the composed
   PENDING bump `k0` of the extrusions already performed (the ancestors of this
   recursion), and `done` members are extruded up to the remaining mass. *)
Lemma float_reach_general : forall body R done k0,
  fsteps (mkDC R (done ++ map (bump_om k0) body))
         (mkDC (R + run_sum body)
               (map (bump_om (run_sum body)) done ++ dfm (run_sum body + k0) 0 body)).
Proof.
  induction body as [| [k c] rest IH]; intros R done k0; simpl.
  - rewrite Nat.add_0_r. rewrite map_bump_om_zero. rewrite app_nil_r.
    apply fsteps_refl.
  - destruct k as [| k'].
    + (* run-0 member: no extrusion step — it joins the done side (its pending bump at
         cutoff 0 IS the closed form's all-references branch). *)
      simpl.
      specialize (IH R (done ++ [bump_om k0 (0, c)]) k0).
      rewrite map_app in IH. rewrite <- !app_assoc in IH. simpl in IH.
      eapply fsteps_trans; [exact IH |].
      match goal with
      | [ |- fsteps (mkDC ?RA ?BA) (mkDC ?RB ?BB) ] =>
          replace BB with BA; [apply fsteps_refl |]
      end.
      f_equal.
      f_equal.
      rewrite bump_om_compose.
      unfold bump_om. simpl.
      f_equal.
      apply map_bname_ext. intros [n | x]; simpl; window.
    + (* k >= 1: extrude the (pre-bumped) head, then the IH with the composed pending
         bump on the remainder. *)
      eapply fsteps_cons.
      * apply (fs_extrude R done (S k') (map_bname (bump (S k') k0) c)
                 (map (bump_om k0) rest)).
        lia.
      * rewrite map_bump_om_compose.
        specialize (IH (R + S k')
                       (map (bump_om (S k')) done
                          ++ [(0, map_bname (bump (S k') k0) c)])
                       (k0 + S k')).
        rewrite map_app in IH. rewrite <- !app_assoc in IH. simpl in IH.
        eapply fsteps_trans; [exact IH |].
        match goal with
        | [ |- fsteps (mkDC ?RA ?BA) (mkDC ?RB ?BB) ] =>
            replace RB with RA by lia;
            replace BB with BA; [apply fsteps_refl |]
        end.
        rewrite map_bump_om_compose.
        f_equal.
        f_equal.
        -- unfold bump_om. simpl. f_equal.
           rewrite map_bname_compose.
           apply map_bname_ext. intros [n | x]; simpl; window.
        -- f_equal. lia.
Qed.

(* ** float_step_sound, reachability half: the float function is an `fstep` chain —
   the in-Rho `^float` computation takes exactly these documented C-G composites, each
   with the `fstep_side_condition` discharge. *)
Theorem float_reachable : forall cfg, fsteps cfg (dfloat cfg).
Proof.
  intros [R body].
  pose proof (float_reach_general body R [] 0) as H.
  rewrite map_bump_om_zero in H. simpl in H.
  rewrite Nat.add_0_r in H.
  exact H.
Qed.

(* =====================================================================================
   Part 4 — F8-AM-3: redex invariance under the RUN-PERMUTATION-induced injective index
   renaming (NEW — BinderFloatCanonicalization.v:381-397 cover bag permutation only).
   ===================================================================================== *)

Definition injective (rho : nat -> nat) : Prop :=
  forall a b, rho a = rho b -> a = b.

Lemma drename_injective : forall rho, injective rho ->
  forall N M, drename rho N = drename rho M -> N = M.
Proof.
  intros rho Hinj [n | x] [m | y] H; simpl in H; try discriminate H;
    injection H as H; subst; try reflexivity.
  f_equal. apply Hinj. exact H.
Qed.

Lemma in_inner_rename : forall rho c m inner,
  In (c, m) (map (map_inner (drename rho)) inner) ->
  exists m', m = drename rho m' /\ In (c, m') inner.
Proof.
  intros rho c m inner H. apply in_map_iff in H.
  destruct H as [[c' m'] [Heq Hin]]. unfold map_inner in Heq. simpl in Heq.
  injection Heq as Hc Hm. subst c'. subst m.
  exists m'. split; [reflexivity | exact Hin].
Qed.

(* ** THE F8-AM-3 LEMMA: every redex predicate is closed (both directions) under the
   injective index renaming a run permutation induces — a redex shape needs only
   SAME-NAME equality between member positions, and an injective renaming preserves AND
   reflects equality. *)
Theorem redex_invariant_under_run_permutation : forall rho, injective rho ->
  forall body,
    (in_redex (map (rename_om rho) body) <-> in_redex body)
    /\ (open_redex (map (rename_om rho) body) <-> open_redex body)
    /\ (forall m,
          out_redex (drename rho m) (map (rename_om rho) body) <-> out_redex m body).
Proof.
  intros rho Hinj body.
  split; [| split].
  - split.
    + intros (n & m & i1 & i2 & rest & Hp & Hin).
      apply Permutation_sym in Hp.
      apply Permutation_map_inv in Hp.
      destruct Hp as [pre [Heq Hperm]].
      destruct pre as [| [r1 d1] pre]; [discriminate Heq |].
      destruct pre as [| [r2 d2] pre]; [discriminate Heq |].
      simpl in Heq.
      injection Heq as Hr1 Hd1 Hr2 Hd2 Hrest.
      destruct d1 as [N1 I1 | | ]; simpl in Hd1; try discriminate Hd1.
      destruct d2 as [N2 I2 | | ]; simpl in Hd2; try discriminate Hd2.
      injection Hd1 as HN1 HI1. injection Hd2 as HN2 HI2.
      subst r1 r2.
      rewrite HI1 in Hin.
      apply in_inner_rename in Hin. destruct Hin as [m' [Hm' Hin']].
      rewrite HN2 in Hm'.
      apply (drename_injective rho Hinj) in Hm'. subst m'.
      exists N1, N2, I1, I2, pre. split.
      * exact Hperm.
      * exact Hin'.
    + intros (n & m & i1 & i2 & rest & Hp & Hin).
      exists (drename rho n), (drename rho m),
             (map (map_inner (drename rho)) i1), (map (map_inner (drename rho)) i2),
             (map (rename_om rho) rest).
      split.
      * assert (E : (0, BAmb (drename rho n) (map (map_inner (drename rho)) i1))
                      :: (0, BAmb (drename rho m) (map (map_inner (drename rho)) i2))
                      :: map (rename_om rho) rest
                    = map (rename_om rho)
                          ((0, BAmb n i1) :: (0, BAmb m i2) :: rest))
          by reflexivity.
        rewrite E.
        apply Permutation_map. exact Hp.
      * change (CIn, drename rho m) with (map_inner (drename rho) (CIn, m)).
        apply in_map. exact Hin.
  - split.
    + intros (n & inner & rest & Hp).
      apply Permutation_sym in Hp.
      apply Permutation_map_inv in Hp.
      destruct Hp as [pre [Heq Hperm]].
      destruct pre as [| [r1 d1] pre]; [discriminate Heq |].
      destruct pre as [| [r2 d2] pre]; [discriminate Heq |].
      simpl in Heq.
      injection Heq as Hr1 Hd1 Hr2 Hd2 Hrest.
      destruct d1 as [| c1 N1 |]; simpl in Hd1; try discriminate Hd1.
      destruct d2 as [N2 I2 | |]; simpl in Hd2; try discriminate Hd2.
      injection Hd1 as Hc1 HN1. injection Hd2 as HN2 HI2.
      subst r1 r2 c1.
      assert (HN : N1 = N2).
      { eapply drename_injective; [exact Hinj |]. rewrite <- HN1, <- HN2. reflexivity. }
      subst N1.
      exists N2, I2, pre.
      exact Hperm.
    + intros (n & inner & rest & Hp).
      exists (drename rho n), (map (map_inner (drename rho)) inner),
             (map (rename_om rho) rest).
      assert (E : (0, BCap COpen (drename rho n))
                    :: (0, BAmb (drename rho n) (map (map_inner (drename rho)) inner))
                    :: map (rename_om rho) rest
                  = map (rename_om rho)
                        ((0, BCap COpen n) :: (0, BAmb n inner) :: rest))
        by reflexivity.
      rewrite E.
      apply Permutation_map. exact Hp.
  - intro m. split.
    + intros (n & inner & rest & Hp & Hin).
      apply Permutation_sym in Hp.
      apply Permutation_map_inv in Hp.
      destruct Hp as [pre [Heq Hperm]].
      destruct pre as [| [r1 d1] pre]; [discriminate Heq |].
      simpl in Heq.
      injection Heq as Hr1 Hd1 Hrest.
      destruct d1 as [N1 I1 | |]; simpl in Hd1; try discriminate Hd1.
      injection Hd1 as HN1 HI1.
      subst r1.
      rewrite HI1 in Hin.
      apply in_inner_rename in Hin. destruct Hin as [m' [Hm' Hin']].
      apply (drename_injective rho Hinj) in Hm'. subst m'.
      exists N1, I1, pre. split.
      * exact Hperm.
      * exact Hin'.
    + intros (n & inner & rest & Hp & Hin).
      exists (drename rho n), (map (map_inner (drename rho)) inner),
             (map (rename_om rho) rest).
      split.
      * assert (E : (0, BAmb (drename rho n) (map (map_inner (drename rho)) inner))
                      :: map (rename_om rho) rest
                    = map (rename_om rho) ((0, BAmb n inner) :: rest))
          by reflexivity.
        rewrite E.
        apply Permutation_map. exact Hp.
      * change (COut, drename rho m) with (map_inner (drename rho) (COut, m)).
        apply in_map. exact Hin.
Qed.

(* =====================================================================================
   Part 5 — F8-AM-4 (first half): float_functional_up_to_NewComm.
   ===================================================================================== *)

(* A renaming with an explicit two-sided inverse (every schedule difference is a BLOCK
   permutation — blocks swap wholesale, they never tear — so the inverse is
   constructive; injectivity for F8-AM-3 follows). *)
Definition inverse_pair (rho rho' : nat -> nat) : Prop :=
  (forall i, rho' (rho i) = i) /\ (forall i, rho (rho' i) = i).

Lemma inverse_pair_injective : forall rho rho', inverse_pair rho rho' -> injective rho.
Proof.
  intros rho rho' [Hl _] a b Hab.
  rewrite <- (Hl a), <- (Hl b), Hab. reflexivity.
Qed.

Definition id_outside (lo hi : nat) (rho : nat -> nat) : Prop :=
  forall i, i < lo \/ hi <= i -> rho i = i.

(* The two-block swap at base `S`: `[S, S + ky)` shifts up by `kx`; `[S + ky,
   S + ky + kx)` shifts down by `ky`; identity elsewhere.  Its inverse swaps the
   roles. *)
Definition block_swap (S kx ky : nat) (i : nat) : nat :=
  if andb (Nat.leb S i) (Nat.ltb i (S + ky)) then i + kx
  else if andb (Nat.leb (S + ky) i) (Nat.ltb i (S + ky + kx)) then i - ky
  else i.

Lemma block_swap_inverse : forall S kx ky,
  inverse_pair (block_swap S kx ky) (block_swap S ky kx).
Proof.
  intros S kx ky. unfold inverse_pair, block_swap.
  split; intro i; window.
Qed.

Lemma block_swap_id_outside : forall S kx ky,
  id_outside S (S + kx + ky) (block_swap S kx ky).
Proof.
  intros S kx ky i Hout. unfold block_swap. window.
Qed.

(* One float-head member is FIXED by any renaming that is the identity at/above `hi`
   when both its image offsets sit at/above `hi` — the skip case's head-fix and every
   tail-fix reduce to this. *)
Lemma rename_fixes_float_head : forall rho lo hi k S O c,
  id_outside lo hi rho -> hi <= S -> hi <= O ->
  rename_om rho (0, map_bname (mem_float_map k S O) c)
  = (0, map_bname (mem_float_map k S O) c).
Proof.
  intros rho lo hi k S O c Hid HS HO.
  unfold rename_om. simpl. f_equal.
  rewrite map_bname_compose.
  apply map_bname_ext. intros [n | x]; simpl; [| reflexivity].
  destruct (Nat.ltb n k) eqn:Hn; simpl; rewrite Hid by lia; reflexivity.
Qed.

(* Members whose float images sit strictly below `lo` (own) or at/above `hi` (outer)
   are fixed listwise. *)
Lemma rename_fixes_dfm : forall rho lo hi total tail body,
  id_outside lo hi rho ->
  run_sum body + tail <= lo ->
  hi <= total ->
  lo <= hi ->
  map (rename_om rho) (dfm total tail body) = dfm total tail body.
Proof.
  intros rho lo hi total tail body Hid Hlo Hhi Hlh.
  induction body as [| [k c] rest IH]; simpl; [reflexivity |].
  simpl in Hlo.
  rewrite IH by lia.
  f_equal.
  unfold rename_om. simpl. f_equal.
  rewrite map_bname_compose.
  apply map_bname_ext. intros [n | x]; simpl; [| reflexivity].
  destruct (Nat.ltb n k) eqn:Hn; simpl; window;
    rewrite Hid by lia; reflexivity.
Qed.

(* ** THE F8-AM-4 FIRST HALF (generalized over the ambient total/tail; the top-level
   corollary instantiates `tail := 0`, `total := run_sum body`): ANY processing order
   of the member bag floats to the same run mass with bodies related by a
   run-permutation renaming carrying an explicit two-sided inverse, confined to the
   extruded block `[tail, tail + run_sum body)`. *)
Lemma float_functional_up_to_NewComm_general : forall body body',
  Permutation body body' ->
  forall total tail,
  run_sum body + tail <= total ->
  exists rho rho',
    inverse_pair rho rho'
    /\ id_outside tail (tail + run_sum body) rho
    /\ Permutation (dfm total tail body') (map (rename_om rho) (dfm total tail body)).
Proof.
  intros body body' Hperm.
  induction Hperm as [ | x l l' Hp IH | x y l | l1 l2 l3 H12 IH12 H23 IH23];
    intros total tail Hle.
  - (* nil *)
    exists (fun i => i), (fun i => i).
    split; [split; intro i; reflexivity |].
    split; [intros i _; reflexivity |].
    simpl. apply Permutation_refl.
  - (* skip: the shared head floats identically on both sides; the IH renaming fixes
       its images (they land at or above tail + run_sum l). *)
    destruct x as [k c]. simpl in Hle. simpl.
    destruct (IH total tail ltac:(lia)) as [rho [rho' [Hinv [Hid Hbody]]]].
    exists rho, rho'.
    split; [exact Hinv |].
    split.
    + intros i Hout. apply Hid. simpl in Hout. lia.
    + rewrite <- (run_sum_perm l l' Hp).
      assert (Hfix : rename_om rho
                       (0, map_bname (mem_float_map k (run_sum l + tail) (total - k)) c)
                     = (0, map_bname (mem_float_map k (run_sum l + tail) (total - k)) c)).
      { apply (rename_fixes_float_head rho tail (tail + run_sum l)); [exact Hid | lia | lia]. }
      simpl. rewrite Hfix.
      apply perm_skip. exact Hbody.
  - (* swap: body = y :: x :: l, body' = x :: y :: l — the two-block renaming. *)
    destruct x as [kx cx]. destruct y as [ky cy].
    simpl in Hle. simpl.
    exists (block_swap (run_sum l + tail) ky kx),
           (block_swap (run_sum l + tail) kx ky).
    split; [apply block_swap_inverse |].
    split.
    + intros i Hout.
      apply (block_swap_id_outside (run_sum l + tail) ky kx). lia.
    + (* rename the two heads blockwise; the tail is fixed. *)
      assert (Hy : map_bname (drename (block_swap (run_sum l + tail) ky kx))
                     (map_bname (mem_float_map ky (kx + run_sum l + tail) (total - ky)) cy)
                   = map_bname (mem_float_map ky (run_sum l + tail) (total - ky)) cy).
      { rewrite map_bname_compose. apply map_bname_ext.
        intros [n | xn]; simpl; [| reflexivity].
        destruct (Nat.ltb n ky) eqn:Hn; simpl; unfold block_swap; window. }
      assert (Hx : map_bname (drename (block_swap (run_sum l + tail) ky kx))
                     (map_bname (mem_float_map kx (run_sum l + tail) (total - kx)) cx)
                   = map_bname (mem_float_map kx (ky + run_sum l + tail) (total - kx)) cx).
      { rewrite map_bname_compose. apply map_bname_ext.
        intros [n | xn]; simpl; [| reflexivity].
        destruct (Nat.ltb n kx) eqn:Hn; simpl; unfold block_swap; window. }
      assert (Htail : map (rename_om (block_swap (run_sum l + tail) ky kx))
                        (dfm total tail l)
                      = dfm total tail l).
      { apply (rename_fixes_dfm _ (run_sum l + tail)
                 (run_sum l + tail + ky + kx) total tail).
        - intros i Hout.
          apply (block_swap_id_outside (run_sum l + tail) ky kx). lia.
        - lia.
        - lia.
        - lia. }
      simpl. unfold rename_om at 1 2. simpl.
      rewrite Hy, Hx, Htail.
      (* goal: Permutation (xh' :: yh' :: T) (yh' :: xh' :: T) *)
      apply perm_swap.
  - (* trans: compose. *)
    assert (Hsum : run_sum l1 = run_sum l2) by (apply run_sum_perm; exact H12).
    destruct (IH12 total tail Hle) as [r1 [r1' [Hinv1 [Hid1 Hb1]]]].
    destruct (IH23 total tail ltac:(lia)) as [r2 [r2' [Hinv2 [Hid2 Hb2]]]].
    exists (fun i => r2 (r1 i)), (fun i => r1' (r2' i)).
    split.
    { destruct Hinv1 as [Hl1 Hr1]. destruct Hinv2 as [Hl2 Hr2].
      split; intro i; [rewrite Hl2; apply Hl1 | rewrite Hr1; apply Hr2]. }
    split.
    { intros i Hout.
      rewrite Hid1 by lia. apply Hid2. rewrite <- Hsum. exact Hout. }
    eapply Permutation_trans; [exact Hb2 |].
    eapply Permutation_trans; [apply Permutation_map; exact Hb1 |].
    rewrite map_map.
    match goal with
    | [ |- Permutation (map ?f ?L) (map ?g ?L) ] =>
        replace (map f L) with (map g L); [apply Permutation_refl |]
    end.
    apply map_ext. intro m. rewrite rename_om_compose. reflexivity.
Qed.

(* ** float_functional_up_to_NewComm (the design-named theorem): two peel orders of the
   SAME configuration float to the same run length with bodies related by exactly a
   NewComm run-permutation renaming. *)
Theorem float_functional_up_to_NewComm : forall R body body',
  Permutation body body' ->
  dc_run (dfloat (mkDC R body')) = dc_run (dfloat (mkDC R body))
  /\ exists rho rho',
       inverse_pair rho rho'
       /\ id_outside 0 (run_sum body) rho
       /\ Permutation (dc_body (dfloat (mkDC R body')))
                      (map (rename_om rho) (dc_body (dfloat (mkDC R body)))).
Proof.
  intros R body body' Hperm.
  assert (Hsum : run_sum body = run_sum body') by (apply run_sum_perm; exact Hperm).
  split.
  - unfold dfloat. simpl. rewrite Hsum. reflexivity.
  - destruct (float_functional_up_to_NewComm_general body body' Hperm
                (run_sum body) 0 ltac:(lia))
      as [rho [rho' [Hinv [Hid Hbody]]]].
    exists rho, rho'.
    split; [exact Hinv |].
    split; [intros i Hout; apply Hid; lia |].
    unfold dfloat. simpl. rewrite <- Hsum. exact Hbody.
Qed.

(* =====================================================================================
   Part 6 — float_preserves_bag_flatness: the merge base's THREE-CASE dispatch (the
   in-Rho `bag_fragment_dispatch`) preserves flatness — the AM-2 obligation.  The AM-3(b)
   drive induction supplies the hypothesis: the dispatched value is itself an
   already-floated fragment, so a soup value carries FLAT members (one splice level per
   reassembly suffices; deeper nesting was dissolved by the recursion that floated it).
   ===================================================================================== *)

Inductive fragval : Type :=
  | FVAtom : nat -> fragval
  | FVSoup : list fragval -> fragval.

(* The three-case dispatch: Nil (the empty soup) contributes NOTHING; a same-op soup
   contributes its members (the splice); anything else wraps as one member. *)
Definition three_case_fragment (v : fragval) : list fragval :=
  match v with
  | FVSoup ms => ms
  | FVAtom n => [FVAtom n]
  end.

Definition merge_base (u : fragval) (vms : list fragval) : list fragval :=
  three_case_fragment u ++ vms.

Definition atom_member (m : fragval) : Prop := exists n, m = FVAtom n.
Definition flat_members (l : list fragval) : Prop := Forall atom_member l.

(* ** THE AM-2 OBLIGATION, in-Rho: the merge base's splice preserves bag flatness. *)
Theorem float_preserves_bag_flatness : forall u vms,
  (forall ms, u = FVSoup ms -> flat_members ms) ->
  flat_members vms ->
  flat_members (merge_base u vms).
Proof.
  intros u vms Hu Hv. unfold merge_base, three_case_fragment.
  destruct u as [n | ms].
  - apply Forall_cons; [exists n; reflexivity | exact Hv].
  - apply Forall_app. split; [apply Hu; reflexivity | exact Hv].
Qed.

(* The Nil leg contributes nothing — no spurious empty-bag member (the AM-3 defect the
   three-case dispatch exists to prevent). *)
Example nil_fragment_contributes_nothing : forall vms,
  merge_base (FVSoup []) vms = vms.
Proof. reflexivity. Qed.

(* =====================================================================================
   Part 7 — float_exposes_redexes: over the float's own equivalence (extrusion +
   bag permutation — NO run reorder, the Q-NC record), a redex exists modulo the
   equivalence IFF it is syntactically present in the float normal form.
   ===================================================================================== *)

Inductive dequiv : DCfg -> DCfg -> Prop :=
  | de_refl : forall a, dequiv a a
  | de_step : forall a b c, fstep a b -> dequiv b c -> dequiv a c
  | de_back : forall a b c, fstep b a -> dequiv b c -> dequiv a c
  | de_perm : forall R body body' c,
      Permutation body body' -> dequiv (mkDC R body') c -> dequiv (mkDC R body) c.

Lemma dequiv_trans : forall a b c, dequiv a b -> dequiv b c -> dequiv a c.
Proof.
  intros a b c Hab. revert c.
  induction Hab as [a | a x b Hs Hab IH | a x b Hs Hab IH | R bo bo' b Hp Hab IH];
    intros c Hbc.
  - exact Hbc.
  - eapply de_step; [exact Hs | apply IH; exact Hbc].
  - eapply de_back; [exact Hs | apply IH; exact Hbc].
  - eapply de_perm; [exact Hp | apply IH; exact Hbc].
Qed.

Lemma fsteps_dequiv : forall a b, fsteps a b -> dequiv a b.
Proof.
  intros a b H. induction H as [a | a x b Hs H IH].
  - apply de_refl.
  - eapply de_step; [exact Hs | exact IH].
Qed.

Definition float_body (cfg : DCfg) : list OM := dc_body (dfloat cfg).

(* The float-relatedness bridge: two dequiv-related configurations float to
   rename-related bodies (with a two-sided-inverse renaming). *)
Definition frel (a b : DCfg) : Prop :=
  exists rho rho',
    inverse_pair rho rho'
    /\ Permutation (float_body b) (map (rename_om rho) (float_body a)).

Lemma frel_refl : forall a, frel a a.
Proof.
  intro a. exists (fun i => i), (fun i => i).
  split; [split; intro i; reflexivity |].
  match goal with
  | [ |- Permutation ?L (map ?f ?L) ] =>
      replace (map f L) with L; [apply Permutation_refl |]
  end.
  symmetry. rewrite <- map_id. apply map_ext. intro m.
  apply rename_om_id. intro i. reflexivity.
Qed.

Lemma frel_sym : forall a b, frel a b -> frel b a.
Proof.
  intros a b (rho & rho' & Hinv & Hp).
  exists rho', rho.
  split; [split; apply Hinv |].
  destruct Hinv as [Hl Hr].
  apply (Permutation_map (rename_om rho')) in Hp.
  rewrite map_map in Hp.
  match goal with
  | [ Hp : Permutation (map (rename_om rho') ?FB) (map ?f ?FA) |- _ ] =>
      replace (map f FA) with FA in Hp
  end.
  - apply Permutation_sym. exact Hp.
  - symmetry. rewrite <- map_id. apply map_ext. intro m.
    rewrite rename_om_compose. apply rename_om_id. intro i. apply Hl.
Qed.

Lemma frel_trans : forall a b c, frel a b -> frel b c -> frel a c.
Proof.
  intros a b c (r1 & r1' & Hinv1 & Hp1) (r2 & r2' & Hinv2 & Hp2).
  exists (fun i => r2 (r1 i)), (fun i => r1' (r2' i)).
  split.
  { destruct Hinv1 as [Hl1 Hr1]. destruct Hinv2 as [Hl2 Hr2].
    split; intro i; [rewrite Hl2; apply Hl1 | rewrite Hr1; apply Hr2]. }
  eapply Permutation_trans; [exact Hp2 |].
  eapply Permutation_trans; [apply Permutation_map; exact Hp1 |].
  rewrite map_map.
  match goal with
  | [ |- Permutation (map ?f ?L) (map ?g ?L) ] =>
      replace (map f L) with (map g L); [apply Permutation_refl |]
  end.
  apply map_ext. intro m. rewrite rename_om_compose. reflexivity.
Qed.

(* The extrusion bridge: one fstep's target floats to the SAME body as the source with
   the extruded member's processing order moved to the front — a Permutation of the
   member list — so `float_functional_up_to_NewComm` supplies the renaming. *)
Lemma fstep_frel : forall a b, fstep a b -> frel a b.
Proof.
  intros a b Hs. destruct Hs as [R pre k c post Hk].
  set (Sa := run_sum (pre ++ (k, c) :: post)).
  assert (HSa : Sa = run_sum pre + k + run_sum post).
  { unfold Sa. rewrite run_sum_app. simpl. lia. }
  (* the float of the STEPPED body equals the float of the SOURCE with the extruded
     member processed first (pointwise per member), up to the position move. *)
  assert (Hbody :
    Permutation
      (float_body (mkDC (R + k)
                        (map (bump_om k) pre ++ (0, c) :: map (bump_om k) post)))
      (dfm Sa 0 ((k, c) :: pre ++ post))).
  { unfold float_body, dfloat. simpl.
    rewrite run_sum_app. simpl.
    rewrite run_sum_map_bump. rewrite run_sum_map_bump.
    rewrite dfm_app.
    simpl. rewrite run_sum_map_bump.
    rewrite dfm_of_bumped by lia.
    rewrite dfm_of_bumped by lia.
    rewrite dfm_app.
    (* align the two head maps and the two totals pointwise *)
    replace (run_sum pre + run_sum post + k)
      with Sa by lia.
    replace (map_bname
               (mem_float_map 0 (run_sum post + 0)
                  (run_sum pre + run_sum post - 0)) c)
      with (map_bname (mem_float_map k (run_sum (pre ++ post) + 0) (Sa - k)) c).
    2:{ apply map_bname_ext. intros [n | x]; simpl; [| reflexivity].
        rewrite run_sum_app. window. }
    replace (run_sum post + 0) with (run_sum post) by lia.
    (* both sides are now the same three segments; move the head across *)
    apply Permutation_sym.
    replace (dfm Sa 0 ((k, c) :: pre ++ post))
      with ((0, map_bname (mem_float_map k (run_sum (pre ++ post) + 0) (Sa - k)) c)
              :: dfm Sa (run_sum post + 0) pre ++ dfm Sa 0 post).
    2:{ simpl. rewrite dfm_app. reflexivity. }
    replace (run_sum post + 0) with (run_sum post) by lia.
    apply Permutation_middle. }
  (* the order move is a Permutation of the source body *)
  destruct (float_functional_up_to_NewComm_general
              (pre ++ (k, c) :: post) ((k, c) :: pre ++ post)
              (Permutation_sym (Permutation_middle pre post (k, c)))
              Sa 0 ltac:(unfold Sa; lia))
    as [rho [rho' [Hinv [_ Hmoved]]]].
  exists rho, rho'.
  split; [exact Hinv |].
  eapply Permutation_trans; [exact Hbody |].
  unfold float_body, dfloat. simpl.
  exact Hmoved.
Qed.

Lemma dequiv_frel : forall a b, dequiv a b -> frel a b.
Proof.
  intros a b H.
  induction H as [a | a x b Hs H IH | a x b Hs H IH | R bo bo' b Hp H IH].
  - apply frel_refl.
  - eapply frel_trans; [apply fstep_frel; exact Hs | exact IH].
  - eapply frel_trans; [apply frel_sym; apply fstep_frel; exact Hs | exact IH].
  - eapply frel_trans; [| exact IH].
    destruct (float_functional_up_to_NewComm R bo bo' Hp) as [_ [rho [rho' [Hinv [_ Hb]]]]].
    exists rho, rho'. split; [exact Hinv | exact Hb].
Qed.

(* Redex transport across frel. *)
Lemma frel_in_redex : forall a b, frel a b ->
  (in_redex (float_body a) <-> in_redex (float_body b)).
Proof.
  intros a b (rho & rho' & Hinv & Hp).
  pose proof (inverse_pair_injective rho rho' Hinv) as Hinj.
  destruct (redex_invariant_under_run_permutation rho Hinj (float_body a))
    as [Hin _].
  split.
  - intro H. eapply in_redex_perm; [apply Permutation_sym; exact Hp |].
    apply Hin. exact H.
  - intro H. apply Hin. eapply in_redex_perm; [exact Hp | exact H].
Qed.

Lemma frel_open_redex : forall a b, frel a b ->
  (open_redex (float_body a) <-> open_redex (float_body b)).
Proof.
  intros a b (rho & rho' & Hinv & Hp).
  pose proof (inverse_pair_injective rho rho' Hinv) as Hinj.
  destruct (redex_invariant_under_run_permutation rho Hinj (float_body a))
    as [_ [Hopen _]].
  split.
  - intro H. eapply open_redex_perm; [apply Permutation_sym; exact Hp |].
    apply Hopen. exact H.
  - intro H. apply Hopen. eapply open_redex_perm; [exact Hp | exact H].
Qed.

Lemma frel_out_redex_free : forall a b x, frel a b ->
  (out_redex (NF x) (float_body a) <-> out_redex (NF x) (float_body b)).
Proof.
  intros a b x (rho & rho' & Hinv & Hp).
  pose proof (inverse_pair_injective rho rho' Hinv) as Hinj.
  destruct (redex_invariant_under_run_permutation rho Hinj (float_body a))
    as [_ [_ Hout]].
  specialize (Hout (NF x)). simpl in Hout.
  split.
  - intro H. eapply out_redex_perm; [apply Permutation_sym; exact Hp |].
    apply Hout. exact H.
  - intro H. apply Hout. eapply out_redex_perm; [exact Hp | exact H].
Qed.

(* Monotone exposure: a SYNTACTIC redex survives the float — the run-0 witness members
   all rename by the SAME uniform shift (+ run mass), so the guard equality survives. *)
Lemma mem_float_map_runzero : forall S O c,
  map_bname (mem_float_map 0 S O) c = map_bname (drename (fun i => i + O)) c.
Proof.
  intros S O c. apply map_bname_ext. intros [n | x]; simpl; window.
Qed.

Lemma float_monotone_in : forall R body,
  in_redex body -> in_redex (float_body (mkDC R body)).
Proof.
  intros R body (n & m & i1 & i2 & rest & Hp & Hin).
  unfold float_body, dfloat. simpl.
  destruct (float_functional_up_to_NewComm_general body
              ((0, BAmb n i1) :: (0, BAmb m i2) :: rest) Hp
              (run_sum body) 0 ltac:(lia))
    as [rho [rho' [Hinv [_ Hfl]]]].
  pose proof (inverse_pair_injective rho rho' Hinv) as Hinj.
  destruct (redex_invariant_under_run_permutation rho Hinj
              (dfm (run_sum body) 0 body)) as [Hiff _].
  apply Hiff.
  eapply in_redex_perm; [exact Hfl |].
  cbn [dfm].
  rewrite !mem_float_map_runzero.
  exists (drename (fun i => i + (run_sum body - 0)) n),
         (drename (fun i => i + (run_sum body - 0)) m),
         (map (map_inner (drename (fun i => i + (run_sum body - 0)))) i1),
         (map (map_inner (drename (fun i => i + (run_sum body - 0)))) i2),
         (dfm (run_sum body) 0 rest).
  split.
  - apply Permutation_refl.
  - change (CIn, drename (fun i => i + (run_sum body - 0)) m)
      with (map_inner (drename (fun i => i + (run_sum body - 0))) (CIn, m)).
    apply in_map. exact Hin.
Qed.

Lemma float_monotone_open : forall R body,
  open_redex body -> open_redex (float_body (mkDC R body)).
Proof.
  intros R body (n & inner & rest & Hp).
  unfold float_body, dfloat. simpl.
  destruct (float_functional_up_to_NewComm_general body
              ((0, BCap COpen n) :: (0, BAmb n inner) :: rest) Hp
              (run_sum body) 0 ltac:(lia))
    as [rho [rho' [Hinv [_ Hfl]]]].
  pose proof (inverse_pair_injective rho rho' Hinv) as Hinj.
  destruct (redex_invariant_under_run_permutation rho Hinj
              (dfm (run_sum body) 0 body)) as [_ [Hiff _]].
  apply Hiff.
  eapply open_redex_perm; [exact Hfl |].
  cbn [dfm].
  rewrite !mem_float_map_runzero.
  exists (drename (fun i => i + (run_sum body - 0)) n),
         (map (map_inner (drename (fun i => i + (run_sum body - 0)))) inner),
         (dfm (run_sum body) 0 rest).
  apply Permutation_refl.
Qed.

Lemma float_monotone_out_free : forall R body x,
  out_redex (NF x) body -> out_redex (NF x) (float_body (mkDC R body)).
Proof.
  intros R body x (n & inner & rest & Hp & Hin).
  unfold float_body, dfloat. simpl.
  destruct (float_functional_up_to_NewComm_general body
              ((0, BAmb n inner) :: rest) Hp
              (run_sum body) 0 ltac:(lia))
    as [rho [rho' [Hinv [_ Hfl]]]].
  pose proof (inverse_pair_injective rho rho' Hinv) as Hinj.
  destruct (redex_invariant_under_run_permutation rho Hinj
              (dfm (run_sum body) 0 body)) as [_ [_ Hiff]].
  specialize (Hiff (NF x)). simpl in Hiff.
  apply Hiff.
  eapply out_redex_perm; [exact Hfl |].
  cbn [dfm].
  rewrite !mem_float_map_runzero.
  exists (drename (fun i => i + (run_sum body - 0)) n),
         (map (map_inner (drename (fun i => i + (run_sum body - 0)))) inner),
         (dfm (run_sum body) 0 rest).
  split.
  - apply Permutation_refl.
  - change (COut, NF x)
      with (map_inner (drename (fun i => i + (run_sum body - 0))) (COut, NF x)).
    apply in_map. exact Hin.
Qed.

(* ** THE EXPOSURE THEOREMS: a redex exists modulo the float's own equivalence IFF it
   is syntactically present in the float normal form. *)
Theorem float_exposes_redexes_in : forall cfg,
  (exists cfg', dequiv cfg cfg' /\ in_redex (dc_body cfg'))
  <-> in_redex (dc_body (dfloat cfg)).
Proof.
  intro cfg. split.
  - intros (cfg' & Hdq & Hred).
    apply (frel_in_redex cfg cfg' (dequiv_frel cfg cfg' Hdq)).
    destruct cfg' as [R' body'].
    apply (float_monotone_in R' body'). exact Hred.
  - intro Hred. exists (dfloat cfg).
    split; [apply fsteps_dequiv; apply float_reachable | exact Hred].
Qed.

Theorem float_exposes_redexes_open : forall cfg,
  (exists cfg', dequiv cfg cfg' /\ open_redex (dc_body cfg'))
  <-> open_redex (dc_body (dfloat cfg)).
Proof.
  intro cfg. split.
  - intros (cfg' & Hdq & Hred).
    apply (frel_open_redex cfg cfg' (dequiv_frel cfg cfg' Hdq)).
    destruct cfg' as [R' body'].
    apply (float_monotone_open R' body'). exact Hred.
  - intro Hred. exists (dfloat cfg).
    split; [apply fsteps_dequiv; apply float_reachable | exact Hred].
Qed.

(* The Out exposure, for a FREE cross-level name (every renaming in play fixes `NF x`;
   a bound cross-level name transports along the run renaming, as
   `redex_invariant_under_run_permutation`'s out clause states). *)
Theorem float_exposes_redexes_out : forall x cfg,
  (exists cfg', dequiv cfg cfg' /\ out_redex (NF x) (dc_body cfg'))
  <-> out_redex (NF x) (dc_body (dfloat cfg)).
Proof.
  intros x cfg. split.
  - intros (cfg' & Hdq & Hred).
    apply (frel_out_redex_free cfg cfg' x (dequiv_frel cfg cfg' Hdq)).
    destruct cfg' as [R' body'].
    apply (float_monotone_out_free R' body' x). exact Hred.
  - intro Hred. exists (dfloat cfg).
    split; [apply fsteps_dequiv; apply float_reachable | exact Hred].
Qed.

(* =====================================================================================
   Non-vacuity witnesses.
   ===================================================================================== *)

(* The F1-shaped subject: `{ nu(n[{in m . -}]) | m[{out q . -}] }` — the nu hides the
   In-redex (member 0 carries a run), and the float exposes it (free names inert). *)
Definition f1_dcfg : DCfg :=
  mkDC 0 [ (1, BAmb (NF 1) [(CIn, NF 2)]) ; (0, BAmb (NF 2) [(COut, NF 9)]) ].

Example f1_dcfg_exposes_in_redex_after_float :
  in_redex (dc_body (dfloat f1_dcfg)).
Proof.
  unfold f1_dcfg, dfloat. simpl.
  exists (NF 1), (NF 2), [(CIn, NF 2)], [(COut, NF 9)], [].
  split.
  - apply Permutation_refl.
  - left. reflexivity.
Qed.

(* The two-binder schedule trace (the delta red-team's independent confirmation): the
   two peel orders of a two-member bag differ by exactly the block-swap run
   permutation. *)
Example two_binder_schedules_differ_by_the_block_swap :
  forall (ka kb : nat) (ca cb : bcore),
  exists rho rho',
    inverse_pair rho rho'
    /\ Permutation
         (dfm (run_sum [(ka, ca); (kb, cb)]) 0 [(kb, cb); (ka, ca)])
         (map (rename_om rho) (dfm (run_sum [(ka, ca); (kb, cb)]) 0 [(ka, ca); (kb, cb)])).
Proof.
  intros ka kb ca cb.
  destruct (float_functional_up_to_NewComm_general
              [(ka, ca); (kb, cb)] [(kb, cb); (ka, ca)]
              (perm_swap (kb, cb) (ka, ca) [])
              (run_sum [(ka, ca); (kb, cb)]) 0 ltac:(simpl; lia))
    as [rho [rho' [Hinv [_ Hp]]]].
  exists rho, rho'. split; [exact Hinv | exact Hp].
Qed.

(* Zero-admission confirmation. *)
Print Assumptions hoist_side_condition_by_shift_image.
Print Assumptions fstep_side_condition.
Print Assumptions float_reachable.
Print Assumptions float_canonicalizes.
Print Assumptions float_identity_on_canonical.
Print Assumptions float_functional_up_to_NewComm.
Print Assumptions redex_invariant_under_run_permutation.
Print Assumptions float_preserves_bag_flatness.
Print Assumptions float_exposes_redexes_in.
Print Assumptions float_exposes_redexes_open.
Print Assumptions float_exposes_redexes_out.
Print Assumptions f1_dcfg_exposes_in_redex_after_float.
Print Assumptions two_binder_schedules_differ_by_the_block_swap.
