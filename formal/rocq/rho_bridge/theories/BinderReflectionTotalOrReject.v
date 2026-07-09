(*
 * BinderReflectionTotalOrReject: the Stage 3c binder/β-substitution codegen is
 * well-defined and injective.
 *
 * The Rust lowering (`rholang-codegen/src/rho_net_lower.rs`) compiles a binder
 * rewrite `App(Lam(^x. b), a) ~> subst(b, x := a)` to a flat σ-receiver. Two pieces
 * carry correctness:
 *
 *   (1) the De Bruijn LHS σ-variable extraction (`collect_lhs_vars_term`): a binder
 *       brought into scope by a `Lambda`/`MultiLambda` node is EXCLUDED from the
 *       σ-slots, while the body's FREE variables are preserved. This file models it
 *       as `free_in` and proves:
 *         - `binder_excluded`: the binder is never a free σ-slot;
 *         - `free_lam_char`: `x` is a free σ-slot of `Lam b body` iff `x <> b`
 *           (binder excluded) AND `x` is a free σ-slot of `body` (free vars
 *           preserved) — the exact well-definedness statement.
 *
 *   (2) the RHS reflection (`reflect_term_par_env`): a `Lambda` node reflects to a
 *       tagged binder node with a bound-variable leaf for its binder, a bound
 *       occurrence in the body reflects to a bound-var leaf (NOT a σ-slot), and a
 *       free variable to its σ-slot index. This file models it as `reflect` and
 *       proves:
 *         - collision-freedom (`reflect_lam_shape` / `reflect_app_shape` /
 *           `reflect_var_shape`): a binder node, an application node, a bound-var
 *           leaf, and a σ-slot are pairwise-distinct reflected shapes — so the
 *           reserved binder tag never collides with an Apply node or a σ-slot;
 *         - injectivity (`reflect_inj`): distinct reflectable terms reflect to
 *           distinct values (under a `NoDup` σ-variable order, which
 *           `lower_lhs_vars` guarantees by first-occurrence de-duplication).
 *
 * Beta is a BASE rewrite, so it inherits the proven base-rewrite correspondence
 * (LinearCommCorrespondence.v) and the install boundary
 * (RhoLoweringTotalOrRejects.v); this file discharges the ADDED binder-specific
 * well-definedness + injectivity obligation.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
(* Stage 4 S-binder SLICE 3b: the reflected-occurrence guard bridges to the proven report firing. *)
From RhoBridge Require Import GuardedCommSoundness.
From RhoBridge Require Import NonLinearEqConsistency.
From RhoBridge Require Import AcNonLinearConsistency.
From RhoBridge Require Import AmbientOpenFiring.

Import ListNotations.

Section BinderReflectionTotalOrReject.

  (* A pattern term: a metavariable (identified by a [nat]), a binary constructor
     application (an operator id and two arguments — enough to model the App /
     constructor arm's structure; the β-LHS [App(Lam(fun), arg)] is
     [PApp op (PLam b body) (PVar arg)]), or a binder (binder id + body). *)
  Inductive PTerm : Type :=
    | PVar : nat -> PTerm
    | PApp : nat -> PTerm -> PTerm -> PTerm
    | PLam : nat -> PTerm -> PTerm.

  (* ---------------------------------------------------------------------------
     (1) The De Bruijn LHS free-variable extraction.
     --------------------------------------------------------------------------- *)

  (* [free_in env t] = the free σ-slots of [t] with [env] the in-scope binders (the
     De Bruijn environment [collect_lhs_vars_term] threads): a variable is a free
     σ-slot iff it is NOT an in-scope binder; a binder pushes its name over its body
     (excluding it from the body's σ-slots). *)
  Fixpoint free_in (env : list nat) (t : PTerm) : list nat :=
    match t with
    | PVar x => if existsb (Nat.eqb x) env then [] else [x]
    | PApp _ f a => free_in env f ++ free_in env a
    | PLam b body => free_in (b :: env) body
    end.

  (* [In]-membership of the [existsb (Nat.eqb ·) ·] test. *)
  Lemma existsb_eqb_In : forall x env,
    existsb (Nat.eqb x) env = true <-> In x env.
  Proof.
    intros x env. rewrite existsb_exists. split.
    - intros [y [Hin Heq]]. apply Nat.eqb_eq in Heq. subst y. exact Hin.
    - intros Hin. exists x. split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  Lemma existsb_eqb_not_In : forall x env,
    existsb (Nat.eqb x) env = false <-> ~ In x env.
  Proof.
    intros x env. split.
    - intros Hfalse Hin. apply existsb_eqb_In in Hin.
      rewrite Hin in Hfalse. discriminate Hfalse.
    - intros Hnot. destruct (existsb (Nat.eqb x) env) eqn:Hb.
      + exfalso. apply Hnot. apply existsb_eqb_In. exact Hb.
      + reflexivity.
  Qed.

  (* Membership of a variable in the free σ-slots of a single variable node. *)
  Lemma free_in_var : forall env z x,
    In x (free_in env (PVar z)) <-> (~ In z env /\ x = z).
  Proof.
    intros env z x. simpl. destruct (existsb (Nat.eqb z) env) eqn:Hb.
    - apply existsb_eqb_In in Hb. split.
      + intros [].
      + intros [Hnot _]. contradiction.
    - apply existsb_eqb_not_In in Hb. split.
      + intros Hin. simpl in Hin. destruct Hin as [Heq | Hf].
        * split; [ exact Hb | symmetry; exact Heq ].
        * destruct Hf.
      + intros [_ Heq]. simpl. left. symmetry. exact Heq.
  Qed.

  (* [free_in] depends on the environment only through its membership (as a set), so
     reordering / re-associating the bound binders is invisible. *)
  Lemma free_in_env_iff : forall t env1 env2 x,
    (forall z, In z env1 <-> In z env2) ->
    (In x (free_in env1 t) <-> In x (free_in env2 t)).
  Proof.
    induction t as [z | op f IHf a IHa | b body IHbody]; intros env1 env2 x Hperm.
    - rewrite !free_in_var. split.
      + intros [Hnot Heq]. split; [ | exact Heq ].
        intro Hin. apply Hnot. apply (proj2 (Hperm z)). exact Hin.
      + intros [Hnot Heq]. split; [ | exact Heq ].
        intro Hin. apply Hnot. apply (proj1 (Hperm z)). exact Hin.
    - simpl. rewrite !in_app_iff.
      rewrite (IHf env1 env2 x Hperm), (IHa env1 env2 x Hperm). reflexivity.
    - simpl. apply IHbody. intro w. simpl. split.
      + intros [Hb | Hin]; [ left; exact Hb | right; apply (proj1 (Hperm w)); exact Hin ].
      + intros [Hb | Hin]; [ left; exact Hb | right; apply (proj2 (Hperm w)); exact Hin ].
  Qed.

  (* An in-scope binder is never a free σ-slot of ANY term under that environment. *)
  Lemma free_not_in_bound : forall t env x,
    In x env -> ~ In x (free_in env t).
  Proof.
    induction t as [y | op f IHf a IHa | b body IHbody]; intros env x Hin.
    - simpl. destruct (existsb (Nat.eqb y) env) eqn:Hb.
      + simpl. auto.
      + simpl. intros [Heq | []]. subst y.
        apply existsb_eqb_not_In in Hb. contradiction.
    - simpl. intro Hcat. apply in_app_or in Hcat. destruct Hcat as [Hf | Ha].
      + apply (IHf env x Hin Hf).
      + apply (IHa env x Hin Ha).
    - simpl. apply IHbody. right. exact Hin.
  Qed.

  (* THE BINDER IS EXCLUDED: the binder is never a free σ-slot of its own lambda. *)
  Theorem binder_excluded : forall b body env,
    ~ In b (free_in env (PLam b body)).
  Proof.
    intros b body env. simpl. apply free_not_in_bound. left. reflexivity.
  Qed.

  (* Adding one binder [y] to the environment changes membership only for [y]
     itself: for any OTHER variable [x], being a free σ-slot is preserved. This is
     the "free vars preserved" half. *)
  Lemma free_in_cons_iff : forall t x y env,
    x <> y ->
    (In x (free_in (y :: env) t) <-> In x (free_in env t)).
  Proof.
    induction t as [z | op f IHf a IHa | b body IHbody]; intros x y env Hxy.
    - (* PVar z *)
      rewrite !free_in_var. split.
      + intros [Hnot Heq]. split; [ | exact Heq ].
        intro Hin. apply Hnot. right. exact Hin.
      + intros [Hnot Heq]. split; [ | exact Heq ].
        intro Hin. simpl in Hin. destruct Hin as [Hyz | Hin'].
        * apply Hxy. transitivity z; [ exact Heq | symmetry; exact Hyz ].
        * apply Hnot. exact Hin'.
    - (* PApp *)
      simpl. rewrite !in_app_iff.
      rewrite (IHf x y env Hxy), (IHa x y env Hxy). reflexivity.
    - (* PLam b body : reorder [b :: y :: env] to [y :: b :: env], then the IH on
         [b :: env] discharges the added binder [y]. *)
      simpl.
      assert (Hswap : In x (free_in (b :: y :: env) body)
                      <-> In x (free_in (y :: b :: env) body)).
      { apply free_in_env_iff. intro w. simpl. tauto. }
      rewrite Hswap. exact (IHbody x y (b :: env) Hxy).
  Qed.

  (* THE CHARACTERIZATION (well-definedness): [x] is a free σ-slot of [Lam b body]
     iff [x] is not the binder AND [x] is a free σ-slot of the body — the binder is
     excluded and the body's free variables are preserved, exactly. *)
  Theorem free_lam_char : forall x b body env,
    In x (free_in env (PLam b body)) <-> (x <> b /\ In x (free_in env body)).
  Proof.
    intros x b body env. simpl. split.
    - intros Hin.
      assert (Hxb : x <> b).
      { intro Heq. subst x.
        apply (free_not_in_bound body (b :: env) b); [ left; reflexivity | exact Hin ]. }
      split; [ exact Hxb | ].
      apply (proj1 (free_in_cons_iff body x b env Hxb)). exact Hin.
    - intros [Hxb Hbody].
      apply (proj2 (free_in_cons_iff body x b env Hxb)). exact Hbody.
  Qed.

  (* ---------------------------------------------------------------------------
     (2) The RHS reflection: collision-freedom + injectivity.
     --------------------------------------------------------------------------- *)

  (* The reflected image: a σ-slot [RSlot i] (a De Bruijn [BoundVar]), a bound-var
     leaf [RBound n] (the reserved [^bound] leaf), an application node [RApp op _ _]
     (the constructor's tag), or a binder node [RLam b _] (the reserved [^lambda]
     tag). The FOUR constructors are pairwise distinct, so the binder node collides
     with neither an Apply node nor a σ-slot. *)
  Inductive RTerm : Type :=
    | RSlot : nat -> RTerm
    | RBound : nat -> RTerm
    | RApp : nat -> RTerm -> RTerm -> RTerm
    | RLam : nat -> RTerm -> RTerm.

  (* First-occurrence index of [x] in [l] (the σ-slot the reflection assigns). *)
  Fixpoint index_of (x : nat) (l : list nat) : option nat :=
    match l with
    | [] => None
    | y :: ys => if Nat.eqb x y then Some 0 else option_map S (index_of x ys)
    end.

  (* The RHS reflection with a binder environment [env] and the σ-variable order
     [vars]: a bound occurrence reflects to a bound-var leaf; a free variable to its
     σ-slot (or fails, [None], if it is neither — a dangling RHS variable); an
     application reflects its op-tagged children; a binder reflects to a binder node
     with its binder pushed onto [env]. *)
  Fixpoint reflect (env vars : list nat) (t : PTerm) : option RTerm :=
    match t with
    | PVar x =>
        if existsb (Nat.eqb x) env then Some (RBound x)
        else match index_of x vars with
             | Some i => Some (RSlot i)
             | None => None
             end
    | PApp op f a =>
        match reflect env vars f, reflect env vars a with
        | Some rf, Some ra => Some (RApp op rf ra)
        | _, _ => None
        end
    | PLam b body =>
        match reflect (b :: env) vars body with
        | Some rb => Some (RLam b rb)
        | None => None
        end
    end.

  (* COLLISION-FREEDOM: each source kind reflects to its OWN [RTerm] head. *)
  Lemma reflect_var_shape : forall env vars x r,
    reflect env vars (PVar x) = Some r ->
    r = RBound x \/ (exists i, r = RSlot i).
  Proof.
    intros env vars x r Hr. simpl in Hr.
    destruct (existsb (Nat.eqb x) env).
    - left. injection Hr as Hr. symmetry. exact Hr.
    - destruct (index_of x vars) as [i |] eqn:Hidx.
      + right. exists i. injection Hr as Hr. symmetry. exact Hr.
      + discriminate Hr.
  Qed.

  Lemma reflect_app_shape : forall env vars op f a r,
    reflect env vars (PApp op f a) = Some r ->
    exists rf ra, r = RApp op rf ra
                  /\ reflect env vars f = Some rf
                  /\ reflect env vars a = Some ra.
  Proof.
    intros env vars op f a r Hr. simpl in Hr.
    destruct (reflect env vars f) as [rf |] eqn:Hf; [ | discriminate Hr ].
    destruct (reflect env vars a) as [ra |] eqn:Ha; [ | discriminate Hr ].
    exists rf, ra. injection Hr as Hr. subst r. auto.
  Qed.

  Lemma reflect_lam_shape : forall env vars b body r,
    reflect env vars (PLam b body) = Some r ->
    exists rb, r = RLam b rb /\ reflect (b :: env) vars body = Some rb.
  Proof.
    intros env vars b body r Hr. simpl in Hr.
    destruct (reflect (b :: env) vars body) as [rb |] eqn:Hb; [ | discriminate Hr ].
    exists rb. injection Hr as Hr. subst r. auto.
  Qed.

  (* index_of points at the first occurrence: [nth_error l i] recovers [x]. *)
  Lemma index_of_nth : forall l x i,
    index_of x l = Some i -> nth_error l i = Some x.
  Proof.
    induction l as [| y ys IH]; intros x i Hidx.
    - simpl in Hidx. discriminate Hidx.
    - simpl in Hidx. destruct (Nat.eqb x y) eqn:Hxy.
      + apply Nat.eqb_eq in Hxy. subst y. injection Hidx as Hidx. subst i.
        reflexivity.
      + destruct (index_of x ys) as [j |] eqn:Hj; simpl in Hidx;
          [ | discriminate Hidx ].
        injection Hidx as Hidx. subst i. simpl. apply IH. exact Hj.
  Qed.

  (* Two variables that share a σ-slot index are equal (index_of is injective on the
     σ-variable order). *)
  Lemma index_of_inj : forall l x y i,
    index_of x l = Some i -> index_of y l = Some i -> x = y.
  Proof.
    intros l x y i Hx Hy.
    apply index_of_nth in Hx. apply index_of_nth in Hy.
    rewrite Hx in Hy. injection Hy as Hy. exact Hy.
  Qed.

  (* INJECTIVITY: distinct reflectable terms reflect to distinct values. Collision-
     freedom (the shape lemmas) forces matching kinds; the σ-slot case uses
     index_of injectivity. *)
  Theorem reflect_inj : forall t1 t2 env vars r,
    reflect env vars t1 = Some r ->
    reflect env vars t2 = Some r ->
    t1 = t2.
  Proof.
    induction t1 as [x1 | op1 f1 IHf1 a1 IHa1 | b1 body1 IHbody1];
      intros t2 env vars r H1 H2.
    - (* t1 = PVar x1 *)
      pose proof (reflect_var_shape _ _ _ _ H1) as Hshape1.
      destruct t2 as [x2 | op2 f2 a2 | b2 body2].
      + (* PVar x2 *)
        simpl in H1, H2.
        destruct (existsb (Nat.eqb x1) env) eqn:He1;
          destruct (existsb (Nat.eqb x2) env) eqn:He2.
        * (* both bound : RBound x1 = RBound x2 *)
          injection H1 as H1. injection H2 as H2. subst r.
          injection H2 as H2. subst x2. reflexivity.
        * (* x1 bound, x2 free *)
          injection H1 as H1. subst r.
          destruct (index_of x2 vars); discriminate H2.
        * (* x1 free, x2 bound *)
          injection H2 as H2. subst r.
          destruct (index_of x1 vars); discriminate H1.
        * (* both free : RSlot i1 = RSlot i2, index_of injective *)
          destruct (index_of x1 vars) as [i1 |] eqn:Hi1; [ | discriminate H1 ].
          destruct (index_of x2 vars) as [i2 |] eqn:Hi2; [ | discriminate H2 ].
          injection H1 as H1. injection H2 as H2. subst r.
          injection H2 as H2. subst i2.
          f_equal. apply (index_of_inj vars x1 x2 i1 Hi1 Hi2).
      + (* PApp : contradicts the Var shape *)
        pose proof (reflect_app_shape _ _ _ _ _ _ H2) as [rf [ra [Hr _]]].
        subst r. destruct Hshape1 as [HB | [i HS]]; discriminate.
      + (* PLam : contradicts the Var shape *)
        pose proof (reflect_lam_shape _ _ _ _ _ H2) as [rb [Hr _]].
        subst r. destruct Hshape1 as [HB | [i HS]]; discriminate.
    - (* t1 = PApp op1 f1 a1 *)
      pose proof (reflect_app_shape _ _ _ _ _ _ H1) as [rf1 [ra1 [Hr1 [Hf1 Ha1]]]].
      destruct t2 as [x2 | op2 f2 a2 | b2 body2].
      + (* PVar : contradicts the App shape *)
        pose proof (reflect_var_shape _ _ _ _ H2) as Hshape2.
        subst r. destruct Hshape2 as [HB | [i HS]]; discriminate.
      + (* PApp op2 f2 a2 *)
        pose proof (reflect_app_shape _ _ _ _ _ _ H2) as [rf2 [ra2 [Hr2 [Hf2 Ha2]]]].
        subst r. injection Hr2 as Hop Hrf Hra. subst op2 rf2 ra2.
        assert (Hfeq : f1 = f2) by (apply (IHf1 f2 env vars rf1); assumption).
        assert (Haeq : a1 = a2) by (apply (IHa1 a2 env vars ra1); assumption).
        subst f2 a2. reflexivity.
      + (* PLam : contradicts the App shape *)
        pose proof (reflect_lam_shape _ _ _ _ _ H2) as [rb [Hr _]].
        subst r. discriminate Hr.
    - (* t1 = PLam b1 body1 *)
      pose proof (reflect_lam_shape _ _ _ _ _ H1) as [rb1 [Hr1 Hbody1]].
      destruct t2 as [x2 | op2 f2 a2 | b2 body2].
      + (* PVar : contradicts the Lam shape *)
        pose proof (reflect_var_shape _ _ _ _ H2) as Hshape2.
        subst r. destruct Hshape2 as [HB | [i HS]]; discriminate.
      + (* PApp : contradicts the Lam shape *)
        pose proof (reflect_app_shape _ _ _ _ _ _ H2) as [rf [ra [Hr _]]].
        subst r. discriminate Hr.
      + (* PLam b2 body2 *)
        pose proof (reflect_lam_shape _ _ _ _ _ H2) as [rb2 [Hr2 Hbody2]].
        subst r. injection Hr2 as Hb Hrb. subst b2 rb2.
        assert (Hbodyeq : body1 = body2)
          by (apply (IHbody1 body2 (b1 :: env) vars rb1); assumption).
        subst body2. reflexivity.
  Qed.

  (* COLLISION-FREEDOM: a binder node's reflection is distinct from BOTH any
     application node's AND any variable's (a bound-var leaf or a σ-slot) — the
     reserved `^lambda` tag never collides with an `Apply` node or a σ-slot
     `BoundVar`. *)
  Theorem reflect_binder_node_collision_free :
    forall env vars b body r,
      reflect env vars (PLam b body) = Some r ->
      (forall op f a, reflect env vars (PApp op f a) <> Some r)
      /\ (forall x, reflect env vars (PVar x) <> Some r).
  Proof.
    intros env vars b body r HL.
    pose proof (reflect_lam_shape _ _ _ _ _ HL) as [rb [HrL _]]. subst r.
    split.
    - (* No application node reflects to a binder node. *)
      intros op f a Hcontra.
      pose proof (reflect_app_shape _ _ _ _ _ _ Hcontra) as [rf [ra [Hr _]]].
      discriminate Hr.
    - (* No variable (bound-var leaf or σ-slot) reflects to a binder node. *)
      intros x Hcontra.
      pose proof (reflect_var_shape _ _ _ _ Hcontra) as [HB | [i HS]]; discriminate.
  Qed.

End BinderReflectionTotalOrReject.

(* ===========================================================================
   STAGE 4 S-binder (slice 1): the INDEXED-PEANO MATCH-side reflection.

   The section above models the RHS *pattern* reflection (`reflect_term_par_env`) — NAMED binders,
   host-computed σ-slots. The Stage-4 S-binder MATCH path instead reflects the RUNTIME SUBJECT term
   (the macro `reflect_category_fn`, `macros/src/gen/runtime/rho_invocation.rs`), which is ALREADY
   de-Bruijn (moniker). So a BOUND occurrence `Var::Bound{scope=n}` reflects to `^bound(peano n)`
   (the reserved `^bound` tag over a Peano numeral `S(S(…Z))` of the scope offset), a FREE
   occurrence to `^free name`, a single binder `Lam(^x. body)` to `^lambda([⟦body⟧])` (ONE child,
   the binder De Bruijn-IMPLICIT), and a structural constructor node to its op-tagged image.

   This is a TOTAL subject reflection (every runtime term has a ground image — no σ-slot failure).
   The added obligation this slice discharges: it is INJECTIVE (distinct runtime terms → distinct
   ground images), with the reserved `^`-tags collision-free vs the structural nodes, so the
   set-automaton's `App(^lambda(body), arg)` entry matches the reflected β-redex UNAMBIGUOUSLY. The
   REDUCT (the capture-avoiding substitution turning the captured `(body, arg)` into `b[a/0]`) is
   S-binder SLICE 2's in-Rho TRS — NOT modeled here (this slice MATCHES + captures).

   Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
   =========================================================================== *)

Section MatchSideIndexedPeanoReflection.

  (* Peano numeral for a De Bruijn scope offset: `^bound(peano n)` reflects a runtime
     `Var::Bound{scope=n}` to the reserved `^bound` tag over `S(S(…(Z)))` with n `S`s. (Constructor
     names carry an `M`/`MR` prefix — the RHS-pattern section above already defines global
     `RTerm`/`PTerm` constructors; Inductives are NOT section-discharged, so the prefixes avoid the
     collision.) *)
  Inductive MPeano : Type :=
    | MPZ : MPeano
    | MPS : MPeano -> MPeano.

  Fixpoint mpeano (n : nat) : MPeano :=
    match n with
    | O => MPZ
    | S m => MPS (mpeano m)
    end.

  (* mpeano is INJECTIVE: distinct scope offsets give distinct numerals (hence distinct `^bound`
     leaves) — the numeric core of the binder-node injectivity. *)
  Lemma mpeano_inj : forall m n, mpeano m = mpeano n -> m = n.
  Proof.
    induction m as [| m IH]; intros [| n] H; simpl in H; try discriminate H.
    - reflexivity.
    - injection H as H. f_equal. apply IH. exact H.
  Qed.

  (* A runtime term, already de-Bruijn (the MATCH-side subject the M-reflect walk reads): a BOUND
     occurrence at scope [n] (`Var::Bound{scope=n}`), a FREE occurrence [x] (`Var::Free`), a
     structural constructor node (nullary `A` / unary `F(·)` / binary `App(·,·)` — the LambdaDemo
     β-redex shapes, exactly as the existing [PApp] models the App arm binary), or a single binder
     [MLam body] (`Lam(^x. body)`). *)
  Inductive MTerm : Type :=
    | MBound : nat -> MTerm
    | MFree  : nat -> MTerm
    | MNode0 : nat -> MTerm
    | MNode1 : nat -> MTerm -> MTerm
    | MNode2 : nat -> MTerm -> MTerm -> MTerm
    | MLam   : MTerm -> MTerm.

  (* The reflected GROUND image (a `GroundTerm`): the reserved `^bound(mpeano n)` leaf, the reserved
     `^free x` leaf, an op-tagged structural node (`MRNode·`, SAME arity as the source), or the
     reserved `^lambda([body])` binder node (ONE child, the binder De Bruijn-IMPLICIT). The three
     reserved kinds ([MRBound]/[MRFree]/[MRLam]) are pairwise distinct from each other AND from every
     structural node — the `^`-prefixed tags are unforgeable. *)
  Inductive MImg : Type :=
    | MRBound : MPeano -> MImg
    | MRFree  : nat -> MImg
    | MRNode0 : nat -> MImg
    | MRNode1 : nat -> MImg -> MImg
    | MRNode2 : nat -> MImg -> MImg -> MImg
    | MRLam   : MImg -> MImg.

  (* The MATCH-side reflection: TOTAL (a subject always has a ground image, unlike the RHS pattern
     reflection which can fail on a dangling σ-slot). A bound var → `^bound(mpeano scope)`; a free
     var → `^free name`; a structural node → its op-tagged image; a binder → `^lambda([⟦body⟧])`. *)
  Fixpoint mreflect (t : MTerm) : MImg :=
    match t with
    | MBound n => MRBound (mpeano n)
    | MFree x => MRFree x
    | MNode0 op => MRNode0 op
    | MNode1 op a => MRNode1 op (mreflect a)
    | MNode2 op a b => MRNode2 op (mreflect a) (mreflect b)
    | MLam body => MRLam (mreflect body)
    end.

  (* COLLISION-FREEDOM (the reserved `^lambda` tag never collides): whatever reflects to a binder
     node IS a binder — no structural node and no variable reflects to it. *)
  Theorem mreflect_lambda_collision_free : forall body t,
    mreflect (MLam body) = mreflect t -> exists b, t = MLam b.
  Proof.
    intros body t H. destruct t; simpl in H; try discriminate H.
    exists t. reflexivity.
  Qed.

  (* COLLISION-FREEDOM (the reserved `^bound` tag never collides): whatever reflects to a `^bound`
     leaf IS a bound occurrence — no structural node, no free var, no binder reflects to it. *)
  Theorem mreflect_bound_collision_free : forall n t,
    mreflect (MBound n) = mreflect t -> exists m, t = MBound m.
  Proof.
    intros n t H. destruct t; simpl in H; try discriminate H.
    exists n0. reflexivity.
  Qed.

  (* COLLISION-FREEDOM (the reserved `^free` tag never collides). *)
  Theorem mreflect_free_collision_free : forall x t,
    mreflect (MFree x) = mreflect t -> exists y, t = MFree y.
  Proof.
    intros x t H. destruct t; simpl in H; try discriminate H.
    exists n. reflexivity.
  Qed.

  (* INJECTIVITY: distinct runtime terms reflect to distinct ground images — the MATCH reflection
     loses no information. The `^bound` case reduces to [mpeano_inj]; every other case is structural.
     So the reflected β-redex `App(^lambda(F(^bound Z)), A)` is an UNAMBIGUOUS automaton subject. *)
  Theorem mreflect_inj : forall t1 t2, mreflect t1 = mreflect t2 -> t1 = t2.
  Proof.
    induction t1 as [n1 | x1 | op1 | op1 a1 IHa1 | op1 a1 IHa1 b1 IHb1 | body1 IHbody1];
      intros t2 H; destruct t2 as [n2 | x2 | op2 | op2 a2 | op2 a2 b2 | body2];
      simpl in H; try discriminate H.
    - injection H as H. apply mpeano_inj in H. subst n2. reflexivity.
    - injection H as H. subst x2. reflexivity.
    - injection H as H. subst op2. reflexivity.
    - injection H as Hop Ha. subst op2. f_equal. apply IHa1. exact Ha.
    - injection H as Hop Ha Hb. subst op2. f_equal.
      + apply IHa1. exact Ha.
      + apply IHb1. exact Hb.
    - injection H as Hb. f_equal. apply IHbody1. exact Hb.
  Qed.

End MatchSideIndexedPeanoReflection.

(* ===========================================================================
   STAGE 4 S-binder (slice 2b): the ^subst / ^shift reflection is INJECTIVE, and the
   FIVE reserved-tagged shapes (^lambda / ^bound(peano) / ^free / ^subst / ^shift) are
   pairwise distinct.

   Slice 2a lands the in-Rho subst cascade: the Beta sigma-receiver SENDS a reserved
   `^subst(Z, a, b, out)` node, and the five reserved receivers spread `^shift(...)`
   nodes as the cascade runs (`rholang-codegen/src/rho_net_subst_trs.rs`,
   `reserved_subst_trs_labels`).  For the cascade to be UNAMBIGUOUS on the reducer, the
   two NEW reserved tags `^subst` / `^shift` must be reflected injectively and must not
   collide with the slice-1 subject tags `^lambda` / `^bound` / `^free` (nor with each
   other) -- the `^`-prefixed tags are unforgeable vs a user constructor, and the
   depth-indexed Peano arguments (`j` in `^subst`, `c` in `^shift`) reflect through the
   same injective `mpeano` the slice-1 `^bound` leaf uses.

   This section extends the slice-1 `MatchSideIndexedPeanoReflection` with a term algebra
   carrying the two reserved reduction tags and proves (a) the reflection is injective
   (`sbreflect_inj`, reusing `mpeano_inj` for every Peano index) and (b) the five reserved
   shapes are pairwise distinct (`subst_five_shapes_distinct` / the collision-free
   lemmas).  Rocq 9.1 compatible.  No Admitted, no Axioms, no Assumptions.
   =========================================================================== *)

Section SubstShiftReflectionInjective.

  (* A reflected term carrying the two reduction tags on top of the slice-1 subject
     shapes: `^bound(peano n)`, `^free x`, `^lambda b`, `^subst(j, a, t)`, `^shift(c, t)`
     (`j` / `c` are de-Bruijn depths -- reflected as Peano numerals, as in the runtime
     ABI).  These are the FIVE reserved shapes of the cascade. *)
  Inductive SbTerm : Type :=
    | SbBound : nat -> SbTerm
    | SbFree  : nat -> SbTerm
    | SbLam   : SbTerm -> SbTerm
    | SbSubst : nat -> SbTerm -> SbTerm -> SbTerm
    | SbShift : nat -> SbTerm -> SbTerm.

  (* The reflected image: the reserved tag over the Peano-indexed / structural children.
     The FIVE constructors are pairwise distinct, so the reserved `^subst` / `^shift`
     tags never collide with `^lambda` / `^bound` / `^free` nor with each other. *)
  Inductive SbImg : Type :=
    | SbRBound : MPeano -> SbImg
    | SbRFree  : nat -> SbImg
    | SbRLam   : SbImg -> SbImg
    | SbRSubst : MPeano -> SbImg -> SbImg -> SbImg
    | SbRShift : MPeano -> SbImg -> SbImg.

  (* The reflection: every de-Bruijn index / depth goes through the injective `mpeano`
     (slice 1); the structure is preserved. *)
  Fixpoint sbreflect (t : SbTerm) : SbImg :=
    match t with
    | SbBound n => SbRBound (mpeano n)
    | SbFree x => SbRFree x
    | SbLam b => SbRLam (sbreflect b)
    | SbSubst j a t => SbRSubst (mpeano j) (sbreflect a) (sbreflect t)
    | SbShift c t => SbRShift (mpeano c) (sbreflect t)
    end.

  (* COLLISION-FREEDOM (the reserved `^subst` tag never collides): whatever reflects to a
     `^subst` node IS a `^subst` -- no `^lambda` / `^bound` / `^free` / `^shift` does. *)
  Theorem sbreflect_subst_collision_free : forall j a t s,
    sbreflect (SbSubst j a t) = sbreflect s ->
    exists j' a' t', s = SbSubst j' a' t'.
  Proof.
    intros j a t s H. destruct s; simpl in H; try discriminate H.
    exists n, s1, s2. reflexivity.
  Qed.

  (* COLLISION-FREEDOM (the reserved `^shift` tag never collides). *)
  Theorem sbreflect_shift_collision_free : forall c t s,
    sbreflect (SbShift c t) = sbreflect s ->
    exists c' t', s = SbShift c' t'.
  Proof.
    intros c t s H. destruct s; simpl in H; try discriminate H.
    exists n, s. reflexivity.
  Qed.

  (* THE FIVE SHAPES ARE PAIRWISE DISTINCT: the reserved `^subst` image differs from each
     of the other four reflected shapes (the analogous facts for the remaining pairs are
     immediate by constructor distinctness -- `^subst` is the new load-bearing tag the
     Beta seed sends, so it is stated explicitly). *)
  Theorem subst_five_shapes_distinct : forall j a t,
    (forall n, sbreflect (SbSubst j a t) <> sbreflect (SbBound n))
    /\ (forall x, sbreflect (SbSubst j a t) <> sbreflect (SbFree x))
    /\ (forall b, sbreflect (SbSubst j a t) <> sbreflect (SbLam b))
    /\ (forall c t', sbreflect (SbSubst j a t) <> sbreflect (SbShift c t')).
  Proof.
    intros j a t. repeat split; intros; simpl; discriminate.
  Qed.

  (* INJECTIVITY: distinct reserved terms reflect to distinct images -- the `^bound`,
     `^subst` and `^shift` Peano indices reduce to `mpeano_inj`; the rest is structural.
     So a `^subst(Z, a, b)` seed and every `^shift(c, .)` the cascade spreads is an
     UNAMBIGUOUS reflected subject. *)
  Theorem sbreflect_inj : forall t1 t2, sbreflect t1 = sbreflect t2 -> t1 = t2.
  Proof.
    induction t1 as [n1 | x1 | b1 IHb1 | j1 a1 IHa1 tt1 IHtt1 | c1 tt1 IHtt1];
      intros t2 H; destruct t2 as [n2 | x2 | b2 | j2 a2 tt2 | c2 tt2];
      simpl in H; try discriminate H.
    - injection H as H. apply mpeano_inj in H. subst n2. reflexivity.
    - injection H as H. subst x2. reflexivity.
    - injection H as H. f_equal. apply IHb1. exact H.
    - injection H as Hj Ha Ht. apply mpeano_inj in Hj. subst j2.
      f_equal; [ apply IHa1; exact Ha | apply IHtt1; exact Ht ].
    - injection H as Hc Ht. apply mpeano_inj in Hc. subst c2.
      f_equal. apply IHtt1. exact Ht.
  Qed.

End SubstShiftReflectionInjective.

(* ===========================================================================
   STAGE 4 S-binder (SLICE 3b): the STRUCTURAL-AC non-linear guard `EEq(N_i, N_j)` on the
   reflected ambient-name occurrences ⟺ the report's `N ≡ N` e-class equality — the LOAD-BEARING
   binder piece that makes the distinct-`new` veto SOUND.

   The Ambient `OpenRule` `{POpen N P, PAmb N Q, ...rest} ~> {P, Q, ...rest}` fires only when the
   OPEN capability's ambient name and the AMBIENT's name are the SAME name. The in-Rho MATCH receiver
   (`rho_net_lower.rs::structural_ac_match_receiver_par`) enforces this with a `Receive.condition`
   `EEq(N_0, N_1)` over the two elements' REFLECTED channel occurrences; the host report enforces the
   e-graph e-class equality `N ≡ N`. Both compare the SAME de-Bruijn name occurrences: a runtime
   `Var::Bound{scope=d}` reflects to the reserved `^bound(peano d)` leaf (the slice-1 indexed-Peano
   reflection, `mreflect` on `MBound`), a `Var::Free name` to `^free name`. Because DE-BRUIJN quotients
   α (α-equivalent occurrences are SYNTACTICALLY identical), and the reflection is INJECTIVE
   (`mpeano_inj` at the depth, constructor-distinctness across bound/free), the reducer's `EEq` on the
   reflected leaves is EXACTLY α-equivalence of the ambient names — hence exactly the report's e-class
   check. Two names bound at the same depth reflect equal; two names bound at DIFFERENT depths (by
   DIFFERENT `new`s — `^bound(peano d1)` vs `^bound(peano d2)`, `d1 ≠ d2`) reflect UNEQUAL, so the
   guard FAILS and the reducer never commits the COMM: `open` cannot dissolve an ambient bound by a
   different binder (the `ambnewdemo_distinct_binders_veto_the_open` reject).

   HONEST MODELING NOTE. The reducer's `EEq` returns a `bool`; here `guard_holds` is the PROP
   "the two reflected name images are equal", i.e. `EEq` evaluated true. This is faithful — NOT a
   weakening: `EEq` on the reserved GROUND `^bound`/`^free` leaves IS structural equality of those
   leaves (they carry no free variables to evaluate), and the report's `Fact` identity of a name
   occurrence (`name_fact`, keyed on bound depth / free name with disjoint parities) is an INJECTIVE
   naming precisely because de-Bruijn quotients α. So the reflected-occurrence guard, the report's
   `open_guard` over the name Facts (`AmbientOpenFiring`), and α-equivalence coincide. This section
   proves that coincidence and composes it with the PROVEN report firing (`AmbientOpenFiring.
   open_commits_when_names_agree` / `open_disagree_no_commit`) — so the OpenRule fires in Rho EXACTLY
   when the reflected names are α-equal, delivering `{P, Q, ...rest}`, and is reject-safe otherwise.
   Reuses `mpeano`/`mpeano_inj`/`MImg` (this file, slice 1) + `open_guard_iff_names_agree` /
   `open_commits_when_names_agree` / `open_disagree_no_commit` / `struct_attempt` / `insert_all`
   (AmbientOpenFiring). Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
   =========================================================================== *)

Section StructuralAcBinderGuard.

  (* An ambient NAME occurrence, already de-Bruijn (the MATCH-side subject the M-reflect walk reads):
     bound at scope depth [d] (`Var::Bound{scope=d}` → `^bound(peano d)`) or free with name [x]
     (`Var::Free` → `^free x`). Two occurrences are α-EQUIVALENT iff they are the SAME de-Bruijn
     occurrence — equal as `AmbName`. *)
  Inductive AmbName : Type :=
    | ANBound : nat -> AmbName
    | ANFree  : nat -> AmbName.

  (* The reserved-tagged GROUND reflection of a name occurrence (the SAME indexed-Peano reflection the
     subject walk uses on `MBound`/`MFree`: `^bound(mpeano d)` / `^free x`). Reuses `MImg`/`mpeano`
     from `MatchSideIndexedPeanoReflection` — so the guard compares EXACTLY the reflected channel
     images. *)
  Definition reflect_name (n : AmbName) : MImg :=
    match n with
    | ANBound d => MRBound (mpeano d)
    | ANFree x => MRFree x
    end.

  (* The receiver's `Receive.condition` `EEq(N_i, N_j)` HOLDS iff the two reflected name images are
     structurally equal — the reducer's `EEq` on the reserved ground leaves. *)
  Definition guard_holds (n1 n2 : AmbName) : Prop := reflect_name n1 = reflect_name n2.

  (* (S-guard.1) THE α-EQUIVALENCE CHARACTERIZATION: the reflected-occurrence `EEq` guard holds IFF
     the two ambient names are the SAME de-Bruijn occurrence — α-equivalence. Same depth ⟹ same
     `^bound(peano d)` (`mpeano_inj`); same free name ⟹ same `^free x`; bound vs free never collide
     (constructor-distinct `MImg`). So reducer `EEq` ≡ α-equivalence of the ambient names. *)
  Theorem guard_holds_iff_alpha_equiv : forall n1 n2,
    guard_holds n1 n2 <-> n1 = n2.
  Proof.
    intros n1 n2. unfold guard_holds. split.
    - destruct n1 as [d1 | x1]; destruct n2 as [d2 | x2]; simpl; intro H.
      + injection H as H. apply mpeano_inj in H. subst d2. reflexivity.
      + discriminate H.
      + discriminate H.
      + injection H as H. subst x2. reflexivity.
    - intro H. subst n2. reflexivity.
  Qed.

  (* (S-guard.2) THE DISTINCT-BINDER VETO IS SOUND: an open name bound at depth [d1] and an ambient
     name bound at depth [d2] ≠ [d1] (bound by DIFFERENT `new`s) reflect to DIFFERENT `^bound` depths,
     so the guard FAILS — `open` cannot dissolve an ambient bound by a different binder. The exact
     `ambnewdemo_distinct_binders_veto_the_open` reject, made decidable in Rho by the depth-tagging. *)
  Theorem distinct_binder_depth_vetoes : forall d1 d2,
    d1 <> d2 -> ~ guard_holds (ANBound d1) (ANBound d2).
  Proof.
    intros d1 d2 Hne Hg. apply Hne.
    apply (proj1 (guard_holds_iff_alpha_equiv (ANBound d1) (ANBound d2))) in Hg.
    injection Hg as Hg. exact Hg.
  Qed.

  (* The report's `Fact` identity of a name occurrence (`find_sigma` reads the de-Bruijn subterm): a
     bound occurrence at depth [d] ↦ the EVEN tag [2*d], a free name [x] ↦ the ODD tag [S (2*x)] — an
     INJECTIVE naming (disjoint parities; de-Bruijn quotients α, so equal `Fact` ⟺ α-equivalent). This
     is the `Fact` the `AmbientOpenFiring` report model keys `open_guard` on. *)
  Definition name_fact (n : AmbName) : Fact :=
    match n with
    | ANBound d => 2 * d
    | ANFree x => S (2 * x)
    end.

  Lemma name_fact_inj : forall n1 n2, name_fact n1 = name_fact n2 -> n1 = n2.
  Proof.
    intros [d1 | x1] [d2 | x2]; simpl; intro H.
    - f_equal. lia.
    - exfalso. lia.
    - exfalso. lia.
    - f_equal. lia.
  Qed.

  (* (S-guard.3) THE GUARD ⟺ THE REPORT e-class CHECK: the reflected-occurrence `EEq` guard holds IFF
     the report's `open_guard` over the name Facts holds (`AmbientOpenFiring`) — both certify `N ≡ N`.
     Composes `open_guard_iff_names_agree` (report) with `name_fact` injectivity + the α-equivalence
     characterization (spread). *)
  Theorem spread_guard_iff_report_open_guard : forall n1 n2,
    guard_holds n1 n2 <-> open_guard (name_fact n1) (name_fact n2) = true.
  Proof.
    intros n1 n2. rewrite guard_holds_iff_alpha_equiv.
    rewrite open_guard_iff_names_agree. split.
    - intro H. subst n2. reflexivity.
    - intro H. apply name_fact_inj. exact H.
  Qed.

  (* (S-guard.4 CAPSTONE) THE OpenRule FIRES IN RHO EXACTLY WHEN THE REFLECTED NAMES ARE α-EQUIVALENT,
     delivering `{P, Q, ...rest}`: when the two reflected ambient-name occurrences are α-equal (guard
     holds), the PROVEN report firing model commits BOTH structural reducts P, Q spliced with rest
     (`AmbientOpenFiring.open_commits_when_names_agree` — `insert_all [p;q] facts`); when they are
     DISTINCT (e.g. different `^bound` depths, different `new`s), the guard FAILS and the consume
     commits NOTHING (`open_disagree_no_commit`) — reject-safe. Ties the spread guard (Part 3) to the
     proven report firing (Stage 3d `AmbientOpenFiring`). *)
  Theorem open_fires_iff_alpha_equiv :
    forall facts premises n1 n2 p q,
      all_present facts premises ->
      ( guard_holds n1 n2 ->
        struct_attempt facts (open_rule premises (name_fact n1) (name_fact n2) p q)
          (insert_all [p; q] facts) )
      /\ ( ~ guard_holds n1 n2 ->
           forall next,
             struct_attempt facts (open_rule premises (name_fact n1) (name_fact n2) p q) next ->
             next = facts ).
  Proof.
    intros facts premises n1 n2 p q Hpres. split.
    - intro Hg.
      apply spread_guard_iff_report_open_guard in Hg.
      apply open_guard_iff_names_agree in Hg.
      apply open_commits_when_names_agree; [ exact Hpres | exact Hg ].
    - intros Hng next Hatt.
      apply (open_disagree_no_commit facts premises (name_fact n1) (name_fact n2) p q next);
        [ | exact Hatt ].
      intro Heq. apply Hng.
      apply (proj2 (spread_guard_iff_report_open_guard n1 n2)).
      apply (proj2 (open_guard_iff_names_agree (name_fact n1) (name_fact n2))).
      exact Heq.
  Qed.

  (* Concrete POSITIVE witness (`new(x, {open(x, A) | x[B]})`): both ambient names bound by the ONE
     enclosing `new`, so both reflect to `^bound(peano 0)` and the guard HOLDS. *)
  Theorem same_new_binder_guard_holds :
    guard_holds (ANBound 0) (ANBound 0).
  Proof. apply guard_holds_iff_alpha_equiv. reflexivity. Qed.

  (* Concrete NEGATIVE witness (`new(x, new(y, {open(x, A) | y[B]}))`): the open name `x` bound by the
     OUTER `new` (depth 1 inside the inner scope), the ambient name `y` by the INNER `new` (depth 0) —
     DIFFERENT depths, so the guard FAILS and the OpenRule cannot fire. *)
  Theorem distinct_new_binders_veto_witness :
    ~ guard_holds (ANBound 1) (ANBound 0).
  Proof. apply distinct_binder_depth_vetoes. discriminate. Qed.

End StructuralAcBinderGuard.

(* Zero-admission confirmation. *)
Print Assumptions binder_excluded.
Print Assumptions free_lam_char.
Print Assumptions reflect_inj.
Print Assumptions reflect_binder_node_collision_free.
Print Assumptions mpeano_inj.
Print Assumptions mreflect_lambda_collision_free.
Print Assumptions mreflect_bound_collision_free.
Print Assumptions mreflect_free_collision_free.
Print Assumptions mreflect_inj.

(* ---- Stage 4 S-binder (slice 2b): ^subst / ^shift reflection injectivity ---- *)
Print Assumptions sbreflect_subst_collision_free.
Print Assumptions sbreflect_shift_collision_free.
Print Assumptions subst_five_shapes_distinct.
Print Assumptions sbreflect_inj.

(* ---- Stage 4 S-binder (SLICE 3b): the reflected-occurrence guard ⟺ α-equivalence ---- *)
Print Assumptions guard_holds_iff_alpha_equiv.
Print Assumptions distinct_binder_depth_vetoes.
Print Assumptions name_fact_inj.
Print Assumptions spread_guard_iff_report_open_guard.
Print Assumptions open_fires_iff_alpha_equiv.
Print Assumptions same_new_binder_guard_holds.
Print Assumptions distinct_new_binders_veto_witness.
