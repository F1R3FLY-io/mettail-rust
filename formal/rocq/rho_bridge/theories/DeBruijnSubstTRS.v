(*
 * DeBruijnSubstTRS: the in-Rho de-Bruijn substitution/shift term-rewriting system
 * (TRS) that Stage 4 S-binder SLICE 2 installs as five persistent reserved receivers
 * (`rholang-codegen/src/rho_net_subst_trs.rs`) is STRONGLY NORMALIZING, CONFLUENT,
 * and computes exactly the capture-avoiding de-Bruijn beta substitution `b[a/0]`.
 *
 * ---------------------------------------------------------------------------------
 * WHAT THIS FILE PROVES (the three load-bearing theorems the bisimulation rests on)
 * ---------------------------------------------------------------------------------
 *
 *   subst_trs_terminating          -- SN: the rewrite relation `step` is well founded
 *                                     (no infinite reduction from any term), via the
 *                                     `val(k)`-weighted measure `mu` (Section MEASURE).
 *   subst_trs_confluent            -- CR: any two reducts of a term have a common
 *                                     reduct, established by the normalizing
 *                                     interpretation `norm` (an orthogonality-free
 *                                     Church-Rosser proof; see below).
 *   subst_normal_form_is_debruijn_beta
 *                                  -- NF: the normal form of the seed `subst(0,a,b)`
 *                                     is `b[a/0]`, the capture-avoiding de-Bruijn
 *                                     beta reduct.
 *   subst_trs_unique_nf            -- SN + CR combined: EVERY normal form reachable
 *                                     from a term is THE unique one `embed (norm t)`.
 *                                     This is what `InRhoBetaCascadeWeakBisim.v`
 *                                     consumes ("the tau-cascade collapses to the
 *                                     UNIQUE NF = b[a/0]").
 *
 * ---------------------------------------------------------------------------------
 * THE MODEL (blueprint v2 sections 3.1 / 6b) and the ONE explicit abstraction
 * ---------------------------------------------------------------------------------
 *
 * The reflected terms are a de-Bruijn term algebra: `oBound n` (a `^bound(peano n)`
 * leaf), `oFree x` (`^free x`), `oLam b` (`^lambda b`), `oNode op ts` (an object
 * constructor `C(t...)`).  The reduction machinery is `tShift c t` (`^shift`),
 * `tShiftk k a` (`^shiftk`) and `tSubst j a t` (`^subst`), operating on the augmented
 * algebra `Tm`.  The C1 rules of section 3.1 are the constructors of `head_step`; the
 * C2 object congruence is `h_subst_node` / `h_shift_node` (one `MatchCase` per
 * non-reserved constructor); `step` is `head_step` closed under every one-hole
 * context (congruence-anywhere), so it over-approximates ANY RSpace interleaving of
 * the cascade's tau-COMMs -- confluence over `step` is exactly the scheduler-order
 * independence the receivers need.
 *
 * ABSTRACTION (documented, not a weakening of the three theorems): the numeral
 * dispatch `^cmp` / `^pred` / `^sb` / `^shb` (section 3.1) is a bounded, deterministic,
 * obviously-terminating sub-cascade over Peano NUMERALS -- it computes `Nat.compare`
 * and `Nat.pred` on the de-Bruijn indices.  We model the indices `j`, `c`, `k`, `n`
 * as Coq `nat` and fold that numeral dispatch into the `if n <? c` / `match n ?= j`
 * conditionals of the `shift` / `subst` head rules.  This is a SOUND ABSTRACTION of
 * the receivers (representing numeral arithmetic as `nat` arithmetic is faithful and,
 * if anything, MORE rigorous than embedding Peano numerals as reducible subterms,
 * which would force a non-monotone `min`-interpretation for the `^cmp` cutoff).  The
 * SN / CR / NF theorems are about the `subst` / `shift` structure -- the genuine
 * lambda-sigma sigma-fragment content (Curien-Hardin-Levy / Zantema) -- which the
 * abstraction leaves intact.
 *
 * ---------------------------------------------------------------------------------
 * WHY CONFLUENCE VIA `norm` (and not a from-scratch orthogonality library)
 * ---------------------------------------------------------------------------------
 *
 * The system is orthogonal: left-linear, and exactly ONE rule fires per
 * `(subst|shift, head)` redex -- `head_step_deterministic` proves the contractum is a
 * FUNCTION of the redex, and `object_binder_disjoint` records the C2 guard (a binder
 * `tLam` is a DISTINCT constructor from an object `tNode`, so it never falls into the
 * generic congruence arm and always takes the depth-incrementing `h_subst_lam`).
 * Rather than formalize Rosen's orthogonality->confluence theorem, we use the
 * equivalent (and lighter) NORMALIZING INTERPRETATION method: `norm : Tm -> Obj`
 * evaluates every term to its intended normal form; we prove `step` PRESERVES `norm`
 * (`step_preserves_norm`) and every term REDUCES to (the embedding of) its `norm`
 * (`reduces_to_norm`).  Together these give Church-Rosser directly, with the common
 * reduct exhibited as `embed (norm t)` -- no critical-pair analysis.
 *
 * Rocq 9.1 compatible.  No Admitted, no Axioms, no Assumptions, no Parameters.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.Wf_nat.

Import ListNotations.

Section DeBruijnSubstTRS.

  (* =============================================================================
     1.  Object terms and the capture-avoiding de-Bruijn beta substitution (the SPEC).
     ============================================================================= *)

  (* Reflected de-Bruijn terms -- the NORMAL FORMS of the cascade.  `oBound n` is the
     reserved `^bound(peano n)` leaf, `oFree x` the `^free x` leaf, `oLam b` the
     `^lambda b` binder node (its bound variable de-Bruijn-implicit), `oNode op ts` a
     non-reserved object constructor `C(t...)`. *)
  Inductive Obj : Type :=
    | oBound : nat -> Obj
    | oFree  : nat -> Obj
    | oLam   : Obj -> Obj
    | oNode  : nat -> list Obj -> Obj.

  (* The auto-generated `Obj_ind` gives no hypothesis for the `oNode` children; this
     is the standard nested induction principle that does. *)
  Definition Obj_ind' (P : Obj -> Prop)
    (Hb : forall n, P (oBound n))
    (Hf : forall x, P (oFree x))
    (Hl : forall b, P b -> P (oLam b))
    (Hn : forall op ts, Forall P ts -> P (oNode op ts))
    : forall t, P t :=
    fix F (t : Obj) : P t :=
      match t with
      | oBound n => Hb n
      | oFree x => Hf x
      | oLam b => Hl b (F b)
      | oNode op ts =>
          Hn op ts
             ((fix G (l : list Obj) : Forall P l :=
                 match l with
                 | [] => Forall_nil P
                 | x :: xs => Forall_cons x (F x) (G xs)
                 end) ts)
      end.

  (* de-Bruijn SHIFT: lift every free index `>= c` by one (the free-variable shift
     under a binder).  `oLam` increments the cutoff `c` -- this is capture-avoidance. *)
  Fixpoint oshift (c : nat) (t : Obj) : Obj :=
    match t with
    | oBound n => oBound (if n <? c then n else S n)
    | oFree x => oFree x
    | oLam b => oLam (oshift (S c) b)
    | oNode op ts => oNode op (map (oshift c) ts)
    end.

  (* Iterated shift: `k` successive `oshift 0` passes (the `^shiftk` fixed receiver). *)
  Fixpoint oshiftk (k : nat) (a : Obj) : Obj :=
    match k with
    | O => a
    | S k' => oshift 0 (oshiftk k' a)
    end.

  (* The native shift contract's single-pass specification.  `oshift_by c k t` traverses
     `t` once and adds `k` to every index free at cutoff `c`; under a binder the cutoff
     increments exactly as in `oshift`.  The executable implementation is an explicit-stack
     PDA over the reflected Par (including HashBag soup children). *)
  Fixpoint oshift_by (c k : nat) (t : Obj) : Obj :=
    match t with
    | oBound n => oBound (if n <? c then n else n + k)
    | oFree x => oFree x
    | oLam b => oLam (oshift_by (S c) k b)
    | oNode op ts => oNode op (map (oshift_by c k) ts)
    end.

  Lemma oshift_by_zero : forall t c, oshift_by c 0 t = t.
  Proof.
    intro t. induction t as [n | x | b IH | op ts IH] using Obj_ind'; intro c; simpl.
    - destruct (n <? c); f_equal; lia.
    - reflexivity.
    - rewrite IH. reflexivity.
    - f_equal. replace ts with (map (fun child => child) ts) at 2 by apply map_id.
      apply map_ext_in. intros child Hin.
      apply Forall_forall with (x := child) in IH; auto.
  Qed.

  (* One ordinary shift after a `k`-amount pass is the `(k+1)`-amount pass.  This is
     the algebraic fusion law that removes the repeated whole-tree traversal. *)
  Lemma oshift_after_oshift_by : forall t c k,
    oshift c (oshift_by c k t) = oshift_by c (S k) t.
  Proof.
    intro t. induction t as [n | x | b IH | op ts IH] using Obj_ind'; intros c k; simpl.
    - destruct (n <? c) eqn:Hlt; simpl.
      + rewrite Hlt. reflexivity.
      + apply Nat.ltb_ge in Hlt.
        assert (Hshifted : (n + k <? c) = false) by (apply Nat.ltb_ge; lia).
        rewrite Hshifted. f_equal. lia.
    - reflexivity.
    - rewrite IH. reflexivity.
    - f_equal. rewrite map_map. apply map_ext_in. intros child Hin.
      apply Forall_forall with (x := child) in IH; auto.
  Qed.

  (* The native one-pass result is extensionally identical to the recursive `^shiftk`
     implementation it replaces.  Thus the generated program/COMM shape changes, but the
     reflected contractum does not. *)
  Theorem oshift_by_is_oshiftk : forall k t,
    oshift_by 0 k t = oshiftk k t.
  Proof.
    intro k. induction k as [| k IH]; intro t.
    - simpl. apply oshift_by_zero.
    - simpl. rewrite <- IH. symmetry. apply oshift_after_oshift_by.
  Qed.

  (* de-Bruijn single SUBSTITUTION `t[a/j]`.  On a bound index `n`: if `n = j` replace
     with `a` lifted past the `j` binders it now sits under (`oshiftk j a` -- CAPTURE
     AVOIDANCE); if `n > j` decrement (the binder `j` is being removed); if `n < j`
     leave it.  Under `oLam`, `j` INCREMENTS (depth). *)
  Fixpoint osubst (j : nat) (a : Obj) (t : Obj) : Obj :=
    match t with
    | oBound n =>
        match n ?= j with
        | Eq => oshiftk j a
        | Gt => oBound (Nat.pred n)
        | Lt => oBound n
        end
    | oFree x => oFree x
    | oLam b => oLam (osubst (S j) a b)
    | oNode op ts => oNode op (map (osubst j a) ts)
    end.

  (* The de-Bruijn beta reduct `b[a/0]`. *)
  Definition odbeta (a b : Obj) : Obj := osubst 0 a b.

  (* Capture-avoidance, made explicit as named rewrite lemmas (both hold by
     definition; stated so the discipline is auditable): the depth INCREMENTS under a
     binder, and the matched variable is shifted past the intervening binders. *)
  Lemma osubst_under_binder : forall j a b,
    osubst j a (oLam b) = oLam (osubst (S j) a b).
  Proof. reflexivity. Qed.

  Lemma osubst_matched_var_is_shifted : forall j a,
    osubst j a (oBound j) = oshiftk j a.
  Proof.
    intros j a. simpl. rewrite Nat.compare_refl. reflexivity.
  Qed.

  (* =============================================================================
     2.  The TRS term algebra `Tm` and the small-step rewrite relation `step`.
     ============================================================================= *)

  (* `Tm` = object terms plus the three reduction-machinery nodes.  The index
     arguments (`n`, `c`, `k`, `j`) are `nat` (the abstraction of the numeral
     dispatch; see the header). *)
  Inductive Tm : Type :=
    | tBound  : nat -> Tm
    | tFree   : nat -> Tm
    | tLam    : Tm -> Tm
    | tNode   : nat -> list Tm -> Tm
    | tShift  : nat -> Tm -> Tm
    | tShiftk : nat -> Tm -> Tm
    | tSubst  : nat -> Tm -> Tm -> Tm.

  Definition Tm_ind' (P : Tm -> Prop)
    (Hb : forall n, P (tBound n))
    (Hf : forall x, P (tFree x))
    (Hl : forall b, P b -> P (tLam b))
    (Hn : forall op ts, Forall P ts -> P (tNode op ts))
    (Hsh : forall c t, P t -> P (tShift c t))
    (Hsk : forall k a, P a -> P (tShiftk k a))
    (Hsu : forall j a t, P a -> P t -> P (tSubst j a t))
    : forall t, P t :=
    fix F (t : Tm) : P t :=
      match t with
      | tBound n => Hb n
      | tFree x => Hf x
      | tLam b => Hl b (F b)
      | tNode op ts =>
          Hn op ts
             ((fix G (l : list Tm) : Forall P l :=
                 match l with
                 | [] => Forall_nil P
                 | x :: xs => Forall_cons x (F x) (G xs)
                 end) ts)
      | tShift c t => Hsh c t (F t)
      | tShiftk k a => Hsk k a (F a)
      | tSubst j a t => Hsu j a t (F a) (F t)
      end.

  (* Embed an object term as a (machinery-free) `Tm` -- the reflected-term ABI flows a
     captured object straight into a `^subst` seed with no re-encoding. *)
  Fixpoint embed (o : Obj) : Tm :=
    match o with
    | oBound n => tBound n
    | oFree x => tFree x
    | oLam b => tLam (embed b)
    | oNode op ts => tNode op (map embed ts)
    end.

  (* A `Tm` is an OBJECT (a normal form: no machinery node anywhere). *)
  Fixpoint is_obj (t : Tm) : bool :=
    match t with
    | tBound _ | tFree _ => true
    | tLam b => is_obj b
    | tNode _ ts => forallb is_obj ts
    | tShift _ _ | tShiftk _ _ | tSubst _ _ _ => false
    end.

  (* The C1 head rules (blueprint section 3.1).  The numeral dispatch `^cmp`/`^pred`/
     `^sb`/`^shb` is folded into the `if n <? c` / `match n ?= j` conditionals. *)
  Inductive head_step : Tm -> Tm -> Prop :=
    | h_shift_bound : forall c n,
        head_step (tShift c (tBound n)) (tBound (if n <? c then n else S n))
    | h_shift_lam : forall c b,
        head_step (tShift c (tLam b)) (tLam (tShift (S c) b))
    | h_shift_free : forall c x,
        head_step (tShift c (tFree x)) (tFree x)
    | h_shift_node : forall c op ts,
        head_step (tShift c (tNode op ts)) (tNode op (map (tShift c) ts))
    | h_shiftk_zero : forall a,
        head_step (tShiftk 0 a) a
    | h_shiftk_succ : forall k a,
        head_step (tShiftk (S k) a) (tShift 0 (tShiftk k a))
    | h_subst_bound : forall j a n,
        head_step (tSubst j a (tBound n))
                  (match n ?= j with
                   | Eq => tShiftk j a
                   | Gt => tBound (Nat.pred n)
                   | Lt => tBound n
                   end)
    | h_subst_lam : forall j a b,
        head_step (tSubst j a (tLam b)) (tLam (tSubst (S j) a b))
    | h_subst_free : forall j a x,
        head_step (tSubst j a (tFree x)) (tFree x)
    | h_subst_node : forall j a op ts,
        head_step (tSubst j a (tNode op ts)) (tNode op (map (tSubst j a) ts)).

  (* `step` = `head_step` under every one-hole context (congruence-anywhere).  The
     `tNode` congruence reduces ONE child (`l ++ t :: r`); no rule reduces inside an
     index argument (those are `nat`). *)
  Inductive step : Tm -> Tm -> Prop :=
    | s_head : forall t u, head_step t u -> step t u
    | s_lam : forall b b', step b b' -> step (tLam b) (tLam b')
    | s_node : forall op l t t' r,
        step t t' -> step (tNode op (l ++ t :: r)) (tNode op (l ++ t' :: r))
    | s_shift : forall c t t', step t t' -> step (tShift c t) (tShift c t')
    | s_shiftk : forall k a a', step a a' -> step (tShiftk k a) (tShiftk k a')
    | s_subst_a : forall j a a' t, step a a' -> step (tSubst j a t) (tSubst j a' t)
    | s_subst_t : forall j a t t', step t t' -> step (tSubst j a t) (tSubst j a t').

  (* Reflexive-transitive closure. *)
  Inductive star : Tm -> Tm -> Prop :=
    | star_refl : forall t, star t t
    | star_cons : forall t u v, step t u -> star u v -> star t v.

  Lemma star_one : forall t u, step t u -> star t u.
  Proof. intros t u H. eapply star_cons; [exact H | apply star_refl]. Qed.

  Lemma star_trans : forall t u v, star t u -> star u v -> star t v.
  Proof.
    intros t u v Htu. induction Htu as [t | t u1 u Hs Hstar IH]; intro Huv.
    - exact Huv.
    - eapply star_cons; [exact Hs | apply IH; exact Huv].
  Qed.

  (* =============================================================================
     3.  Orthogonality: the contractum is a function of the redex; the C2 guard.
     ============================================================================= *)

  (* ORTHOGONALITY (left-linear + exactly one rule per `(subst|shift, head)`): the
     head contraction is DETERMINISTIC -- the contractum is a function of the redex.
     Distinct reserved heads and distinct object-argument constructors mean no two
     head rules share a left-hand side (no critical pairs). *)
  Theorem head_step_deterministic : forall t u1 u2,
    head_step t u1 -> head_step t u2 -> u1 = u2.
  Proof.
    intros t u1 u2 H1 H2.
    destruct H1; inversion H2; subst; reflexivity.
  Qed.

  (* The C2 GUARD (blueprint section 3.2): an object node is a DISTINCT constructor
     from a binder, so the depth-incrementing `h_subst_lam` and the generic object
     congruence `h_subst_node` never overlap -- a binder can never take the generic
     arm (which would lose the `S j` increment and cause capture). *)
  Theorem object_binder_disjoint : forall b op ts, tLam b <> tNode op ts.
  Proof. intros b op ts H. discriminate H. Qed.

  (* `reserved_disjoint_from_object` (the C2 codegen assertion, formalized): the
     object constructors are disjoint from the reserved machinery constructors -- an
     object term is never a `^subst`/`^shift`/`^shiftk` node, so the object congruence
     arms are the only rules that touch it. *)
  Definition is_reserved_head (t : Tm) : bool :=
    match t with
    | tShift _ _ | tShiftk _ _ | tSubst _ _ _ => true
    | _ => false
    end.
  Definition is_object_head (t : Tm) : bool :=
    match t with
    | tBound _ | tFree _ | tLam _ | tNode _ _ => true
    | _ => false
    end.

  Theorem reserved_disjoint_from_object : forall t,
    is_object_head t = true -> is_reserved_head t = false.
  Proof. intros t H. destruct t; try reflexivity; discriminate H. Qed.

  (* A reducible term is never an object; hence a genuine normal form is irreducible. *)
  Lemma step_implies_not_obj : forall t u, step t u -> is_obj t = false.
  Proof.
    intros t u H.
    induction H as [t u Hh | b b' Hs IH | op l t t' r Hs IH
                   | c t t' Hs IH | k a a' Hs IH | j a a' t Hs IH | j a t t' Hs IH].
    - (* s_head *) inversion Hh; reflexivity.
    - (* s_lam *) simpl. exact IH.
    - (* s_node *) simpl. rewrite forallb_app. simpl. rewrite IH.
      destruct (forallb is_obj l); reflexivity.
    - (* s_shift *) reflexivity.
    - (* s_shiftk *) reflexivity.
    - (* s_subst_a *) reflexivity.
    - (* s_subst_t *) reflexivity.
  Qed.

  Theorem is_obj_irreducible : forall t, is_obj t = true -> forall u, ~ step t u.
  Proof.
    intros t Hobj u Hstep. apply step_implies_not_obj in Hstep.
    rewrite Hobj in Hstep. discriminate Hstep.
  Qed.

  (* =============================================================================
     4.  The normalizing interpretation `norm` and Church-Rosser via `norm`.
     ============================================================================= *)

  (* `norm t` : evaluate every machinery node to its object result -- the intended
     normal form of `t`.  This is the semantic yardstick for confluence. *)
  Fixpoint norm (t : Tm) : Obj :=
    match t with
    | tBound n => oBound n
    | tFree x => oFree x
    | tLam b => oLam (norm b)
    | tNode op ts => oNode op (map norm ts)
    | tShift c t => oshift c (norm t)
    | tShiftk k a => oshiftk k (norm a)
    | tSubst j a t => osubst j (norm a) (norm t)
    end.

  (* Embedding then normalizing is the identity (embed produces a machinery-free
     term). *)
  Lemma norm_embed : forall o, norm (embed o) = o.
  Proof.
    intro o. induction o as [n | x | b IH | op ts IH] using Obj_ind'.
    - reflexivity.
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
    - simpl. f_equal. rewrite map_map.
      induction ts as [| t ts' IHts]; [reflexivity |].
      inversion IH as [| ? ? Ht Hts]; subst. simpl. rewrite Ht. f_equal.
      apply IHts. exact Hts.
  Qed.

  (* Each head contraction PRESERVES `norm` (a per-rule computation). *)
  Lemma head_preserves_norm : forall t u, head_step t u -> norm t = norm u.
  Proof.
    intros t u H. destruct H; simpl.
    - (* h_shift_bound *) reflexivity.
    - (* h_shift_lam *) reflexivity.
    - (* h_shift_free *) reflexivity.
    - (* h_shift_node *) f_equal. rewrite map_map, map_map. apply map_ext.
      intro t. reflexivity.
    - (* h_shiftk_zero *) reflexivity.
    - (* h_shiftk_succ *) reflexivity.
    - (* h_subst_bound *) destruct (n ?= j); reflexivity.
    - (* h_subst_lam *) reflexivity.
    - (* h_subst_free *) reflexivity.
    - (* h_subst_node *) f_equal. rewrite map_map, map_map. apply map_ext.
      intro t. reflexivity.
  Qed.

  (* Hence every `step` (head or congruence) preserves `norm`. *)
  Lemma step_preserves_norm : forall t u, step t u -> norm t = norm u.
  Proof.
    intros t u H.
    induction H as [t u Hh | b b' Hs IH | op l t t' r Hs IH
                   | c t t' Hs IH | k a a' Hs IH | j a a' t Hs IH | j a t t' Hs IH].
    - apply head_preserves_norm. exact Hh.
    - simpl. rewrite IH. reflexivity.
    - simpl. f_equal. rewrite map_app, map_app. simpl. rewrite IH. reflexivity.
    - simpl. rewrite IH. reflexivity.
    - simpl. rewrite IH. reflexivity.
    - simpl. rewrite IH. reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Lemma star_preserves_norm : forall t u, star t u -> norm t = norm u.
  Proof.
    intros t u H. induction H as [t | t u1 u Hs Hstar IH].
    - reflexivity.
    - rewrite (step_preserves_norm t u1 Hs). exact IH.
  Qed.

  (* ---- star congruence lifts (one per one-hole context) ---- *)

  Lemma star_lam : forall b b', star b b' -> star (tLam b) (tLam b').
  Proof.
    intros b b' H. induction H as [b | b u b' Hs Hstar IH].
    - apply star_refl.
    - eapply star_cons; [apply s_lam; exact Hs | exact IH].
  Qed.

  Lemma star_shift : forall c t t', star t t' -> star (tShift c t) (tShift c t').
  Proof.
    intros c t t' H. induction H as [t | t u t' Hs Hstar IH].
    - apply star_refl.
    - eapply star_cons; [apply s_shift; exact Hs | exact IH].
  Qed.

  Lemma star_shiftk : forall k a a', star a a' -> star (tShiftk k a) (tShiftk k a').
  Proof.
    intros k a a' H. induction H as [a | a u a' Hs Hstar IH].
    - apply star_refl.
    - eapply star_cons; [apply s_shiftk; exact Hs | exact IH].
  Qed.

  Lemma star_subst_a : forall j a a' t, star a a' -> star (tSubst j a t) (tSubst j a' t).
  Proof.
    intros j a a' t H. induction H as [a | a u a' Hs Hstar IH].
    - apply star_refl.
    - eapply star_cons; [apply s_subst_a; exact Hs | exact IH].
  Qed.

  Lemma star_subst_t : forall j a t t', star t t' -> star (tSubst j a t) (tSubst j a t').
  Proof.
    intros j a t t' H. induction H as [t | t u t' Hs Hstar IH].
    - apply star_refl.
    - eapply star_cons; [apply s_subst_t; exact Hs | exact IH].
  Qed.

  Lemma star_node_one : forall op l t t' r,
    star t t' -> star (tNode op (l ++ t :: r)) (tNode op (l ++ t' :: r)).
  Proof.
    intros op l t t' r H. induction H as [t | t u t' Hs Hstar IH].
    - apply star_refl.
    - eapply star_cons; [apply s_node; exact Hs | exact IH].
  Qed.

  (* Reduce EVERY child of a node pointwise (an accumulator carries the prefix already
     rewritten to `g`).  Polymorphic in the source index type `A` (the children are
     produced by `f`/`g : A -> Tm`; `A` is `Obj` for the embed lemmas, `Tm` for the
     identity-source node case of `reduces_to_norm`). *)
  Lemma star_node_map_app : forall (A : Type) op (f g : A -> Tm) pre ts,
    Forall (fun o => star (f o) (g o)) ts ->
    star (tNode op (pre ++ map f ts)) (tNode op (pre ++ map g ts)).
  Proof.
    intros A op f g pre ts. revert pre.
    induction ts as [| o ts' IH]; intros pre H.
    - simpl. rewrite !app_nil_r. apply star_refl.
    - inversion H as [| ? ? Ho Hts]; subst. simpl.
      eapply star_trans.
      + apply (star_node_one op pre (f o) (g o) (map f ts')). exact Ho.
      + specialize (IH (pre ++ [g o]) Hts).
        rewrite <- !app_assoc in IH. simpl in IH. exact IH.
  Qed.

  Lemma star_node_map : forall (A : Type) op (f g : A -> Tm) ts,
    Forall (fun o => star (f o) (g o)) ts ->
    star (tNode op (map f ts)) (tNode op (map g ts)).
  Proof.
    intros A op f g ts H. apply (star_node_map_app A op f g [] ts H).
  Qed.

  (* Specialize a universally-quantified `Forall` pointwise (to feed `star_node_map`
     from the nested induction hypotheses, whose per-child claim is `forall c ...`). *)
  Lemma Forall_at : forall (P : Obj -> nat -> Prop) c ts,
    Forall (fun o => forall d, P o d) ts -> Forall (fun o => P o c) ts.
  Proof.
    intros P c ts H. induction H as [| o ts' Ho Hts IH]; constructor.
    - apply Ho.
    - exact IH.
  Qed.

  Lemma Forall_at2 : forall (P : Obj -> nat -> Obj -> Prop) j oa ts,
    Forall (fun o => forall d ob, P o d ob) ts -> Forall (fun o => P o j oa) ts.
  Proof.
    intros P j oa ts H. induction H as [| o ts' Ho Hts IH]; constructor.
    - apply Ho.
    - exact IH.
  Qed.

  (* ---- the machinery reduces an EMBEDDED object to its evaluated object ---- *)

  (* `^shift` of an embedded object reduces to the embedded shifted object. *)
  Lemma shift_embed_reduces : forall o c,
    star (tShift c (embed o)) (embed (oshift c o)).
  Proof.
    intro o. induction o as [n | x | b IH | op ts IH] using Obj_ind'; intro c.
    - apply star_one. apply s_head. apply h_shift_bound.
    - apply star_one. apply s_head. apply h_shift_free.
    - simpl. eapply star_cons.
      + apply s_head. apply h_shift_lam.
      + apply star_lam. apply IH.
    - simpl. eapply star_cons.
      + apply s_head. apply h_shift_node.
      + rewrite map_map, map_map.
        apply (star_node_map Obj op (fun o => tShift c (embed o))
                                    (fun o => embed (oshift c o)) ts).
        apply (Forall_at (fun o d => star (tShift d (embed o)) (embed (oshift d o))) c ts).
        exact IH.
  Qed.

  (* `^shiftk` of an embedded object reduces to the embedded iterated-shifted object. *)
  Lemma shiftk_embed_reduces : forall k o,
    star (tShiftk k (embed o)) (embed (oshiftk k o)).
  Proof.
    induction k as [| k IHk]; intro o.
    - apply star_one. apply s_head. apply h_shiftk_zero.
    - simpl. eapply star_cons.
      + apply s_head. apply h_shiftk_succ.
      + eapply star_trans.
        * apply star_shift. apply IHk.
        * apply shift_embed_reduces.
  Qed.

  (* `^subst` of embedded objects reduces to the embedded de-Bruijn substitution. *)
  Lemma subst_embed_reduces : forall o j oa,
    star (tSubst j (embed oa) (embed o)) (embed (osubst j oa o)).
  Proof.
    intro o. induction o as [n | x | b IH | op ts IH] using Obj_ind'; intros j oa.
    - (* oBound n *)
      simpl.
      assert (Hstep : head_step (tSubst j (embed oa) (tBound n))
                        (match n ?= j with
                         | Eq => tShiftk j (embed oa)
                         | Gt => tBound (Nat.pred n)
                         | Lt => tBound n
                         end))
        by apply h_subst_bound.
      destruct (n ?= j) eqn:E.
      + (* Eq: matched var -> shiftk *)
        eapply star_cons; [apply s_head; exact Hstep |].
        apply shiftk_embed_reduces.
      + (* Lt *)
        apply star_one. apply s_head. exact Hstep.
      + (* Gt *)
        apply star_one. apply s_head. exact Hstep.
    - (* oFree x *)
      apply star_one. apply s_head. apply h_subst_free.
    - (* oLam b *)
      simpl. eapply star_cons.
      + apply s_head. apply h_subst_lam.
      + apply star_lam. apply IH.
    - (* oNode op ts *)
      simpl. eapply star_cons.
      + apply s_head. apply h_subst_node.
      + rewrite map_map, map_map.
        apply (star_node_map Obj op (fun o => tSubst j (embed oa) (embed o))
                                    (fun o => embed (osubst j oa o)) ts).
        apply (Forall_at2 (fun o d ob => star (tSubst d (embed ob) (embed o))
                                              (embed (osubst d ob o))) j oa ts).
        exact IH.
  Qed.

  (* NORMALIZATION TO THE INTERPRETATION: every term reduces to (the embedding of) its
     `norm`.  Half of the Church-Rosser proof. *)
  Theorem reduces_to_norm : forall t, star t (embed (norm t)).
  Proof.
    intro t.
    induction t as [n | x | b IH | op ts IH | c t IH | k a IH | j a t IHa IHt]
      using Tm_ind'.
    - apply star_refl.
    - apply star_refl.
    - simpl. apply star_lam. exact IH.
    - simpl. rewrite map_map.
      replace ts with (map (fun x => x) ts) at 1 by apply map_id.
      apply (star_node_map Tm op (fun x => x) (fun x => embed (norm x)) ts). exact IH.
    - simpl. eapply star_trans.
      + apply star_shift. exact IH.
      + apply shift_embed_reduces.
    - simpl. eapply star_trans.
      + apply star_shiftk. exact IH.
      + apply shiftk_embed_reduces.
    - simpl. eapply star_trans.
      + apply star_subst_a. exact IHa.
      + eapply star_trans.
        * apply star_subst_t. exact IHt.
        * apply subst_embed_reduces.
  Qed.

  (* CONFLUENCE (Church-Rosser): any two reducts share a common reduct -- exhibited as
     `embed (norm t)`.  No critical-pair analysis: `step` preserves `norm`, and every
     term reduces to its `norm`. *)
  Theorem subst_trs_confluent : forall t u1 u2,
    star t u1 -> star t u2 ->
    exists v, star u1 v /\ star u2 v.
  Proof.
    intros t u1 u2 H1 H2. exists (embed (norm t)). split.
    - rewrite (star_preserves_norm t u1 H1). apply reduces_to_norm.
    - rewrite (star_preserves_norm t u2 H2). apply reduces_to_norm.
  Qed.

  (* =============================================================================
     5.  Strong normalization via the `val(k)`-weighted measure `mu`.
     ============================================================================= *)

  (* The naive <#nodes, size> measure is NON-MONOTONE: `tShiftk (S k) a` spawns a
     `tShift` node.  The measure below PRE-PAYS the `val(k) = k` shift passes by the
     factor `3 ^ k` (a `^shiftk` weight) and `4 ^ (mu t)` (a `^subst` weight), a
     monotone interpretation that strictly decreases on every rule.  `tShift` is
     size-preserving (factor 2, index-independent so descending a binder does not grow
     it); `tSubst` beats its `S j` depth increment because `4 > 3`. *)
  Fixpoint mu (t : Tm) : nat :=
    match t with
    | tBound _ => 1
    | tFree _ => 1
    | tLam b => S (mu b)
    | tNode _ ts => S (list_sum (map mu ts))
    | tShift _ t => 2 * mu t
    | tShiftk k a => (mu a + 2) * 3 ^ k
    | tSubst j a t => (mu a + 2) * 3 ^ j * 4 ^ (mu t)
    end.

  Lemma pow_pos : forall b n, 1 <= b -> 1 <= b ^ n.
  Proof.
    intros b n Hb. induction n as [| n IH]; simpl.
    - lia.
    - nia.
  Qed.

  (* Two arithmetic facts, proved on plain variables so `nia` finds the certificate;
     the call sites supply `4 ^ (.)` powers as the (opaque) arguments (keeping the
     exponents symbolic so `nia` treats the powers atomically). *)
  Lemma exp_step : forall P Q s, 4 <= P -> 1 <= Q -> s < 4 * Q -> P + s < 4 * (P * Q).
  Proof. intros P Q s HP HQ Hs. nia. Qed.

  Lemma succ_mul_lt : forall d x q, 2 <= d -> x < q -> S (d * x) < d * q.
  Proof. intros d x q Hd Hx. nia. Qed.

  (* Strict monotonicity of a degree-three monomial in its first / last factor (the
     `^subst` congruence cases; `nia` alone does not reach the degree-three product, so
     these route through the positive-factor cancellation lemmas). *)
  Lemma mul3_mono_first : forall x y P Q,
    x < y -> 1 <= P -> 1 <= Q -> (x + 2) * P * Q < (y + 2) * P * Q.
  Proof.
    intros x y P Q Hxy HP HQ.
    assert (HK : 0 < P * Q) by nia.
    rewrite <- !Nat.mul_assoc.
    apply (proj1 (Nat.mul_lt_mono_pos_r (P * Q) (x + 2) (y + 2) HK)). lia.
  Qed.

  Lemma mul3_mono_last : forall M P u v,
    1 <= M -> 1 <= P -> u < v -> M * P * u < M * P * v.
  Proof.
    intros M P u v HM HP Huv.
    assert (HK : 0 < M * P) by nia.
    apply (proj1 (Nat.mul_lt_mono_pos_l (M * P) u v HK)). exact Huv.
  Qed.

  Lemma mu_pos : forall t, 1 <= mu t.
  Proof.
    intro t. induction t as [n | x | b IH | op ts IH | c t IH | k a IH | j a t IHa IHt]
      using Tm_ind'; simpl; try lia.
    - (* tShiftk *) assert (1 <= 3 ^ k) by (apply pow_pos; lia). nia.
    - (* tSubst *)
      assert (1 <= 3 ^ j) by (apply pow_pos; lia).
      assert (1 <= 4 ^ (mu t)) by (apply pow_pos; lia). nia.
  Qed.

  (* The one non-trivial arithmetic fact (the `h_subst_node` head case): the sum of
     the children's `4 ^ (mu .)` weights is dominated by the parent's. *)
  Lemma exp_sum_lt : forall ts,
    list_sum (map (fun t => 4 ^ (mu t)) ts) < 4 ^ (S (list_sum (map mu ts))).
  Proof.
    induction ts as [| t ts' IH]; simpl.
    - lia.
    - (* after simpl the goal is:  4^(mu t) + S' < 4 * 4^(mu t + X) *)
      assert (HA : 4 <= 4 ^ (mu t)).
      { rewrite <- (Nat.pow_1_r 4) at 1. apply Nat.pow_le_mono_r; [lia | apply mu_pos]. }
      assert (HQ : 1 <= 4 ^ (list_sum (map mu ts'))) by (apply pow_pos; lia).
      (* IH : S' < 4^(S X) = 4 * 4^X *)
      rewrite (Nat.pow_succ_r 4 (list_sum (map mu ts'))) in IH by lia.
      rewrite Nat.pow_add_r.
      apply exp_step; assumption.
  Qed.

  (* A scaling helper for the linear `tShift` node case. *)
  Lemma list_sum_map_scale : forall (k : nat) (f : Tm -> nat) l,
    list_sum (map (fun t => k * f t) l) = k * list_sum (map f l).
  Proof.
    intros k f l. induction l as [| t l' IH]; simpl.
    - lia.
    - rewrite IH. lia.
  Qed.

  (* The `mu` of the `^shift` object-congruence reduct: shifting every child scales the
     child-sum by exactly `2` (the `tShift` factor). *)
  Lemma list_sum_mu_shift : forall c ts,
    list_sum (map mu (map (tShift c) ts)) = 2 * list_sum (map mu ts).
  Proof.
    intros c ts. induction ts as [| t ts' IH]; simpl.
    - reflexivity.
    - rewrite IH. lia.
  Qed.

  (* The `mu` of the `^subst` object-congruence reduct: substituting in every child
     scales the child-sum by the constant `^subst` weight `(mu a + 2) * 3 ^ j`. *)
  Lemma list_sum_mu_subst : forall j a ts,
    list_sum (map mu (map (tSubst j a) ts))
    = (mu a + 2) * 3 ^ j * list_sum (map (fun t => 4 ^ (mu t)) ts).
  Proof.
    intros j a ts. induction ts as [| t ts' IH]; simpl.
    - nia.
    - rewrite IH. nia.
  Qed.

  (* Each head contraction STRICTLY decreases `mu`. *)
  Lemma head_decreases_mu : forall t u, head_step t u -> mu u < mu t.
  Proof.
    intros t u H. destruct H.
    - (* h_shift_bound *) simpl. lia.
    - (* h_shift_lam *) simpl. lia.
    - (* h_shift_free *) simpl. lia.
    - (* h_shift_node *)
      assert (E1 : mu (tShift c (tNode op ts)) = 2 * S (list_sum (map mu ts)))
        by reflexivity.
      assert (E2 : mu (tNode op (map (tShift c) ts))
                   = S (2 * list_sum (map mu ts))).
      { simpl. f_equal. apply list_sum_mu_shift. }
      rewrite E1, E2. lia.
    - (* h_shiftk_zero *) simpl.
      assert (Ha : 1 <= mu a) by apply mu_pos. nia.
    - (* h_shiftk_succ *) simpl.
      assert (H3 : 1 <= 3 ^ k) by (apply pow_pos; lia).
      assert (Ha : 1 <= mu a) by apply mu_pos. nia.
    - (* h_subst_bound *)
      assert (H3 : 1 <= 3 ^ j) by (apply pow_pos; lia).
      assert (Ha : 1 <= mu a) by apply mu_pos.
      destruct (n ?= j); simpl; nia.
    - (* h_subst_lam *) simpl.
      assert (H3 : 1 <= 3 ^ j) by (apply pow_pos; lia).
      assert (H4 : 1 <= 4 ^ (mu b)) by (apply pow_pos; lia).
      assert (Ha : 1 <= mu a) by apply mu_pos.
      nia.
    - (* h_subst_free *) simpl.
      assert (H3 : 1 <= 3 ^ j) by (apply pow_pos; lia).
      assert (Ha : 1 <= mu a) by apply mu_pos.
      nia.
    - (* h_subst_node *)
      assert (Hsum := exp_sum_lt ts).
      assert (H3 : 1 <= 3 ^ j) by (apply pow_pos; lia).
      assert (Ha : 1 <= mu a) by apply mu_pos.
      set (D := (mu a + 2) * 3 ^ j) in *.
      assert (HD : 2 <= D) by (unfold D; nia).
      assert (E1 : mu (tSubst j a (tNode op ts))
                   = D * 4 ^ (S (list_sum (map mu ts)))) by reflexivity.
      assert (E2 : mu (tNode op (map (tSubst j a) ts))
                   = S (D * list_sum (map (fun t => 4 ^ (mu t)) ts))).
      { simpl. f_equal. apply list_sum_mu_subst. }
      rewrite E1, E2. apply succ_mul_lt; assumption.
  Qed.

  (* Hence every `step` strictly decreases `mu` (congruence via monotonicity of `mu`
     in each subterm). *)
  Lemma step_decreases_mu : forall t u, step t u -> mu u < mu t.
  Proof.
    intros t u H.
    induction H as [t u Hh | b b' Hs IH | op l t t' r Hs IH
                   | c t t' Hs IH | k a a' Hs IH | j a a' t Hs IH | j a t t' Hs IH].
    - apply head_decreases_mu. exact Hh.
    - (* s_lam *) simpl. lia.
    - (* s_node *) simpl. rewrite !map_app. simpl. rewrite !list_sum_app. simpl. lia.
    - (* s_shift *) simpl. lia.
    - (* s_shiftk *) simpl.
      assert (1 <= 3 ^ k) by (apply pow_pos; lia). nia.
    - (* s_subst_a *) simpl.
      apply mul3_mono_first; [ exact IH | apply pow_pos; lia | apply pow_pos; lia ].
    - (* s_subst_t *) simpl.
      apply mul3_mono_last.
      + lia.
      + apply pow_pos; lia.
      + apply Nat.pow_lt_mono_r; [ lia | exact IH ].
  Qed.

  (* STRONG NORMALIZATION: `step` is well founded -- no infinite reduction sequence. *)
  Theorem subst_trs_terminating : well_founded (fun u t => step t u).
  Proof.
    apply (well_founded_lt_compat Tm mu (fun u t => step t u)).
    intros u t Hstep. apply step_decreases_mu. exact Hstep.
  Qed.

  (* =============================================================================
     6.  The normal form is the de-Bruijn beta reduct; unique-NF for the bisimulation.
     ============================================================================= *)

  (* THE NF THEOREM: the normal form of the seed `subst(0, a, b)` is `b[a/0]`, the
     capture-avoiding de-Bruijn beta reduct. *)
  Theorem subst_normal_form_is_debruijn_beta : forall a b,
    norm (tSubst 0 (embed a) (embed b)) = odbeta a b.
  Proof.
    intros a b. simpl. rewrite !norm_embed. reflexivity.
  Qed.

  (* And the cascade actually REACHES it: the seed reduces to the embedded beta reduct. *)
  Theorem beta_cascade_reaches_debruijn_nf : forall a b,
    star (tSubst 0 (embed a) (embed b)) (embed (odbeta a b)).
  Proof.
    intros a b. unfold odbeta. apply subst_embed_reduces.
  Qed.

  (* A genuine normal form is its own `norm`-embedding. *)
  Lemma is_obj_embed_norm : forall t, is_obj t = true -> t = embed (norm t).
  Proof.
    intro t. induction t as [n | x | b IH | op ts IH | c t IH | k a IH | j a t IHa IHt]
      using Tm_ind'; intro Hobj; simpl in *.
    - reflexivity.
    - reflexivity.
    - rewrite <- IH by exact Hobj. reflexivity.
    - f_equal. rewrite map_map.
      revert Hobj. induction ts as [| t ts' IHts]; intro Hobj; [reflexivity |].
      inversion IH as [| ? ? Ht Hts]; subst.
      simpl in Hobj. apply andb_prop in Hobj. destruct Hobj as [Ht0 Hts0].
      simpl. rewrite <- (Ht Ht0). f_equal. apply IHts; assumption.
    - discriminate Hobj.
    - discriminate Hobj.
    - discriminate Hobj.
  Qed.

  (* SN + CR combined -- the property `InRhoBetaCascadeWeakBisim.v` consumes: EVERY
     normal form reachable from `t` is THE unique one, `embed (norm t)`.  (Existence of
     that normal form is `subst_trs_terminating` + `reduces_to_norm`; this is
     uniqueness.) *)
  Theorem subst_trs_unique_nf : forall t u,
    star t u -> is_obj u = true -> u = embed (norm t).
  Proof.
    intros t u Hstar Hobj.
    rewrite (is_obj_embed_norm u Hobj).
    rewrite (star_preserves_norm t u Hstar). reflexivity.
  Qed.

  (* The seed's unique normal form is the de-Bruijn beta reduct (capture-avoiding):
     ANY object term the cascade can reach from `subst(0,a,b)` IS `b[a/0]`.  This is
     the end-to-end statement the weak bisimulation's up-to-tau target rests on. *)
  Theorem beta_seed_unique_nf_is_debruijn_beta : forall a b u,
    star (tSubst 0 (embed a) (embed b)) u -> is_obj u = true ->
    u = embed (odbeta a b).
  Proof.
    intros a b u Hstar Hobj.
    rewrite (subst_trs_unique_nf _ u Hstar Hobj).
    rewrite subst_normal_form_is_debruijn_beta. reflexivity.
  Qed.

End DeBruijnSubstTRS.

(* Zero-admission confirmation. *)
Print Assumptions osubst_under_binder.
Print Assumptions osubst_matched_var_is_shifted.
Print Assumptions head_step_deterministic.
Print Assumptions object_binder_disjoint.
Print Assumptions reserved_disjoint_from_object.
Print Assumptions is_obj_irreducible.
Print Assumptions step_preserves_norm.
Print Assumptions reduces_to_norm.
Print Assumptions subst_trs_confluent.
Print Assumptions subst_trs_terminating.
Print Assumptions subst_normal_form_is_debruijn_beta.
Print Assumptions beta_cascade_reaches_debruijn_nf.
Print Assumptions subst_trs_unique_nf.
Print Assumptions beta_seed_unique_nf_is_debruijn_beta.
