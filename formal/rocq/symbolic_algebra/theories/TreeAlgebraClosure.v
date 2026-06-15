(*
 * TreeAlgebraClosure: the effective Boolean algebras are closed under the
 * ranked-tree constructor. Given an EBA A whose domain elements ("payloads") are
 * partitioned into a finite set of satisfiable minterm classes `Sigma`, the
 * trees with payloads drawn from A form an EBA `tree_eba` over the recursive
 * domain `DTree`. This is the structural-recursion core of the Rust
 * `SymbolicTreeAutomaton<A>` / `TreePred<P>` / `TreeAlgebra<A>`
 * (prattail/src/sym_tree.rs): a tree predicate is a *deterministic, complete,
 * bottom-up tree automaton* over the payload classes, evaluated by a single
 * bottom-up run; Boolean closure is the tree-automaton product (conj/disj) and
 * the (state-final) flip (neg); SAT is bottom-up emptiness by saturation, and
 * WIT is the minimal accepted term that saturation materializes per state.
 *
 * Determinism + completeness of the carried automaton are what make the Boolean
 * closure clean: the product of two deterministic complete automata is again
 * deterministic and complete, so `conj`/`disj` are exact, and complementation is
 * the pointwise negation of the (single) final predicate — NO determinization is
 * needed (contrast the Rust `determinize_with`, which determinizes a
 * nondeterministic compiled automaton; here every predicate is *born*
 * deterministic, so the Coq model captures the post-determinization invariant
 * that the Rust complement relies upon).
 *
 * The payload alphabet is abstracted by a FINITE partition `Sigma` of `Dom A`
 * into minterm classes, with `letter : Dom A -> Sigma` total (the partition is
 * complete) and a witness payload `pick : Sigma -> option (Dom A)` for the
 * inhabited (satisfiable) classes. This is exactly the per-constructor payload
 * minterm set the Rust automaton computes via
 * `crate::collection_algebra::minterms` (sym_tree.rs:376), whose realizability
 * and inhabitation are already verified in CollectionAlgebraClosure.v; we take
 * that finite, complete, inhabited partition as the abstract interface here so
 * the present file proves only the *structural* tree-automaton content (product,
 * complement, saturation emptiness, witness). The structural automaton is fully
 * proved — no axioms, no admits — over that documented payload-partition
 * abstraction.
 *
 * Binary ranked trees are the canonical ranked-tree case (`DLeaf`/`DNode`);
 * higher arity encodes into binary in the usual way (right-spine of `DNode`s),
 * which the bottom-up product/saturation arguments are insensitive to.
 *
 * Main result: `tree_eba_laws : EBA_Laws tree_eba`.
 *
 * Spec-to-Code Traceability:
 *   Coq                         | Rust (prattail/src/sym_tree.rs)
 *   ----------------------------|------------------------------------------
 *   DTree                       | SymTerm<A::Domain> (DLeaf=leaf, DNode=binary node)
 *   DFTA / run / teval          | SymbolicTreeAutomaton / run / accepts
 *   tconj / tdisj (product)     | SymbolicTreeAutomaton::intersect / union (det.)
 *   tneg (final flip)           | SymbolicTreeAutomaton::complement (det.+complete)
 *   sat_pairs (saturation)      | productive_states / witness (bottom-up fixpoint)
 *   tsat (existsb final)        | SymbolicTreeAutomaton::is_empty (negated)
 *   twit (find final)           | SymbolicTreeAutomaton::witness (minimal term)
 *   Sigma / letter / pick       | constructor_minterms / minterms (verified in
 *                               |   CollectionAlgebraClosure.v)
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
Import ListNotations.
From SymbolicAlgebra Require Import EffectiveBooleanAlgebra.

(* ===================================================================== *)
(*  Generic helpers                                                       *)
(* ===================================================================== *)

(* existsb succeeds iff find returns a satisfying element (reused style from
   CollectionAlgebraClosure.v). *)
Lemma existsb_find_some {X} (f : X -> bool) (l : list X) :
  existsb f l = true -> exists x, find f l = Some x /\ f x = true.
Proof.
  induction l as [|a l IH]; simpl; [discriminate|].
  destruct (f a) eqn:E.
  - intros _. exists a. split; [reflexivity | exact E].
  - simpl. exact IH.
Qed.

(* map distributes over flat_map (proved here to avoid fragile stdlib names). *)
Lemma map_flat_map {X Y Z} (f : Y -> Z) (g : X -> list Y) (l : list X) :
  map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof.
  induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite map_app, IH. reflexivity.
Qed.

(* n-fold iteration of an endofunction. *)
Fixpoint iter {X} (f : X -> X) (n : nat) (x : X) : X :=
  match n with
  | 0 => x
  | S k => f (iter f k x)
  end.

(* A bounded forall over a decidable predicate either holds, or fails at some
   witnessing point ≤ n. Decidable choice over a finite range — no classical
   axiom. *)
Lemma bounded_dec (P : nat -> Prop) (Pdec : forall k, {P k} + {~ P k}) :
  forall n, (forall k, k <= n -> P k) \/ (exists k, k <= n /\ ~ P k).
Proof.
  induction n as [|n IH].
  - destruct (Pdec 0) as [H|H].
    + left. intros k Hk. apply Nat.le_0_r in Hk. subst k. exact H.
    + right. exists 0. split; [apply Nat.le_refl | exact H].
  - destruct IH as [Hall | Hex].
    + destruct (Pdec (S n)) as [H|H].
      * left. intros k Hk.
        (* Hk : k <= S n ; split on whether k = S n or k <= n *)
        destruct (Nat.eq_dec k (S n)) as [->|Hne].
        -- exact H.
        -- apply Hall. apply Nat.lt_succ_r. apply Nat.le_neq. split; [exact Hk | exact Hne].
      * right. exists (S n). split; [apply Nat.le_refl | exact H].
    + destruct Hex as [k [Hk Hnk]]. right. exists k.
      split; [apply Nat.le_le_succ_r; exact Hk | exact Hnk].
Qed.

(* ===================================================================== *)
(*  Generic bounded-chain stabilization (the saturation fixpoint)         *)
(*                                                                        *)
(*  An extensive, incl-monotone operator on subsets of a finite universe  *)
(*  reaches a fixpoint within |universe| iterations from the empty set.    *)
(*  This is the decidable-emptiness core: the reachable-state sets form an *)
(*  increasing chain of subsets of the (finite) state enumeration, so they *)
(*  stabilize within `length q_enum` steps.                                *)
(* ===================================================================== *)

Section Stabilization.
  Variable Q : Type.
  Variable q_eqdec : forall x y : Q, {x = y} + {x <> y}.

  Definition card (l : list Q) : nat := length (nodup q_eqdec l).

  Lemma incl_nodup_self (l : list Q) : incl (nodup q_eqdec l) l.
  Proof. intros x Hx. apply nodup_In in Hx. exact Hx. Qed.

  Lemma incl_self_nodup (l : list Q) : incl l (nodup q_eqdec l).
  Proof. intros x Hx. apply nodup_In. exact Hx. Qed.

  Lemma incl_nodup_mono (a b : list Q) :
    incl a b -> incl (nodup q_eqdec a) (nodup q_eqdec b).
  Proof.
    intros H x Hx. apply nodup_In. apply nodup_In in Hx. apply H. exact Hx.
  Qed.

  Lemma card_incl_le (a b : list Q) : incl a b -> card a <= card b.
  Proof.
    intros H. unfold card.
    apply NoDup_incl_length; [apply NoDup_nodup | apply incl_nodup_mono; exact H].
  Qed.

  Lemma card_le_length (l : list Q) : card l <= length l.
  Proof.
    unfold card. apply NoDup_incl_length; [apply NoDup_nodup | apply incl_nodup_self].
  Qed.

  (* The strict-growth lemma: a strict superset has strictly larger card. *)
  Lemma card_strict (a b : list Q) :
    incl a b -> ~ incl b a -> card a < card b.
  Proof.
    intros Hab Hnba.
    assert (Hle : card a <= card b) by (apply card_incl_le; exact Hab).
    apply Nat.le_neq. split; [exact Hle|].
    intro Heq. apply Hnba.
    assert (Hback : incl (nodup q_eqdec b) (nodup q_eqdec a)).
    { apply NoDup_length_incl.
      - apply NoDup_nodup.
      - unfold card in Heq. rewrite Heq. apply Nat.le_refl.
      - apply incl_nodup_mono; exact Hab. }
    intros x Hx. apply (incl_nodup_self a). apply Hback. apply incl_self_nodup. exact Hx.
  Qed.

  (* Equal cards under one-directional inclusion force the reverse inclusion. *)
  Lemma card_eq_incl (a b : list Q) :
    incl a b -> card a = card b -> incl b a.
  Proof.
    intros Hab Heq.
    assert (Hback : incl (nodup q_eqdec b) (nodup q_eqdec a)).
    { apply NoDup_length_incl.
      - apply NoDup_nodup.
      - unfold card in Heq. rewrite Heq. apply Nat.le_refl.
      - apply incl_nodup_mono; exact Hab. }
    intros x Hx. apply (incl_nodup_self a). apply Hback. apply incl_self_nodup. exact Hx.
  Qed.

  Variable F : list Q -> list Q.
  Variable U : list Q.
  Hypothesis F_extensive : forall P, incl P (F P).
  Hypothesis F_mono : forall P P', incl P P' -> incl (F P) (F P').
  Hypothesis F_bounded : forall P, incl (F P) U.

  Definition chain (k : nat) : list Q := iter F k [].

  Lemma chain_succ (k : nat) : chain (S k) = F (chain k).
  Proof. reflexivity. Qed.

  Lemma chain_extensive (k : nat) : incl (chain k) (chain (S k)).
  Proof. rewrite chain_succ. apply F_extensive. Qed.

  Lemma chain_in_U (k : nat) : incl (chain k) U.
  Proof.
    destruct k as [|k]; [apply incl_nil_l | rewrite chain_succ; apply F_bounded].
  Qed.

  (* A "stall" (the reverse inclusion holds) propagates forward forever. *)
  Lemma stall_propagates (k : nat) :
    incl (chain (S k)) (chain k) ->
    forall m, incl (chain (S (k + m))) (chain (k + m)).
  Proof.
    intros Hstall m. induction m as [|m IH].
    - rewrite Nat.add_0_r. exact Hstall.
    - rewrite Nat.add_succ_r.
      rewrite (chain_succ (S (k + m))), (chain_succ (k + m)).
      apply F_mono. exact IH.
  Qed.

  (* If card strictly grows on every step ≤ n, then card (chain n) ≥ n. *)
  Lemma card_grows (n : nat) :
    (forall j, j < n -> card (chain j) < card (chain (S j))) ->
    n <= card (chain n).
  Proof.
    induction n as [|n IH]; intro Hgrow.
    - apply Nat.le_0_l.
    - assert (Hn : n <= card (chain n)).
      { apply IH. intros j Hj. apply Hgrow. apply Nat.lt_lt_succ_r. exact Hj. }
      assert (Hstrict : card (chain n) < card (chain (S n))).
      { apply Hgrow. apply Nat.lt_succ_diag_r. }
      apply Nat.le_succ_l.
      apply Nat.le_lt_trans with (m := card (chain n)); [exact Hn | exact Hstrict].
  Qed.

  (* The fixpoint lands by step (length U): F (chain (length U)) ⊆ chain (length U). *)
  Theorem stabilizes :
    incl (F (chain (length U))) (chain (length U)).
  Proof.
    set (N := length U).
    change (incl (chain (S N)) (chain N)).
    (* Either every step ≤ N strictly grows card, or there is a stall at some k ≤ N. *)
    destruct (bounded_dec
                (fun k => card (chain k) < card (chain (S k)))
                (fun k => lt_dec (card (chain k)) (card (chain (S k))))
                N) as [Hall | Hex].
    - (* every step grows ⇒ card (chain (S N)) ≥ S N > N ≥ card U ≥ card (chain (S N)) *)
      exfalso.
      assert (HSN : S N <= card (chain (S N))).
      { apply card_grows. intros j Hj. apply Hall.
        apply (proj1 (Nat.lt_succ_r j N)). exact Hj. }
      assert (Hub : card (chain (S N)) <= N).
      { apply Nat.le_trans with (m := card U).
        - apply card_incl_le. apply chain_in_U.
        - apply card_le_length. }
      apply (Nat.lt_irrefl N).
      apply Nat.lt_le_trans with (m := card (chain (S N))); [| exact Hub].
      apply Nat.le_succ_l. exact HSN.
    - (* a stall at some k ≤ N: card (chain k) = card (chain (S k)) ⇒ reverse incl ⇒ propagate *)
      destruct Hex as [k [Hk Hnk]].
      assert (Heq : card (chain k) = card (chain (S k))).
      { apply Nat.le_antisymm.
        - apply card_incl_le. apply chain_extensive.
        - (* ~ (card (chain k) < card (chain (S k))) ⇒ card (chain (S k)) <= card (chain k) *)
          apply Nat.nlt_ge. exact Hnk. }
      assert (Hstall : incl (chain (S k)) (chain k)).
      { apply card_eq_incl; [apply chain_extensive | exact Heq]. }
      replace N with (k + (N - k)).
      + apply stall_propagates. exact Hstall.
      + rewrite Nat.add_comm. apply Nat.sub_add. exact Hk.
  Qed.

End Stabilization.

(* map distributes over flat_map on the *argument* list (the dual push-through). *)
Lemma flat_map_map {X Y Z} (g : Y -> list Z) (f : X -> Y) (l : list X) :
  flat_map g (map f l) = flat_map (fun x => g (f x)) l.
Proof.
  induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(* ===================================================================== *)
(*  The tree EBA over a payload algebra A with a finite minterm partition *)
(* ===================================================================== *)

Section Tree.
  Variable A : EBA.
  Variable LA : EBA_Laws A.

  (* The finite payload-class (minterm) partition of Dom A.  These are the
     per-constructor payload minterms the Rust automaton computes with
     `crate::collection_algebra::minterms` (sym_tree.rs:376); the partition's
     completeness (every payload has a class) and inhabitation (every class used
     has a witness payload) are verified in CollectionAlgebraClosure.v. *)
  Variable Sigma : Type.
  Variable sig_enum : list Sigma.
  Variable sig_all : forall s : Sigma, In s sig_enum.
  Variable sig_eqdec : forall x y : Sigma, {x = y} + {x <> y}.
  Variable letter : Dom A -> Sigma.          (* total ⇒ the partition is complete *)
  Variable pick : Sigma -> option (Dom A).    (* a witness payload of each class *)
  Hypothesis pick_letter : forall s d, pick s = Some d -> letter d = s.
  Hypothesis pick_total : forall s, In s sig_enum -> exists d, pick s = Some d.

  (* Binary ranked trees over payloads (the canonical ranked-tree case). *)
  Inductive DTree : Type :=
  | DLeaf : Dom A -> DTree
  | DNode : Dom A -> DTree -> DTree -> DTree.

  (* A deterministic, complete, bottom-up tree automaton.  The state type [Q]
     varies under product, so it is carried in the record (no nat re-indexing). *)
  Record DFTA := {
    Qst     : Type;
    q_enum  : list Qst;
    q_all   : forall q : Qst, In q q_enum;
    q_eqdec : forall x y : Qst, {x = y} + {x <> y};
    dleaf   : Sigma -> Qst;
    dbin    : Sigma -> Qst -> Qst -> Qst;
    final   : Qst -> bool;
  }.

  Fixpoint run (M : DFTA) (t : DTree) : Qst M :=
    match t with
    | DLeaf p => dleaf M (letter p)
    | DNode p l r => dbin M (letter p) (run M l) (run M r)
    end.

  Definition teval (M : DFTA) (t : DTree) : bool := final M (run M t).

  (* --------------------------------------------------------------------- *)
  (*  top / bot                                                            *)
  (* --------------------------------------------------------------------- *)

  Definition ttop : DFTA := {|
    Qst := unit;
    q_enum := [tt];
    q_all := fun q => match q with tt => or_introl eq_refl end;
    q_eqdec := fun x y => match x, y with tt, tt => left eq_refl end;
    dleaf := fun _ => tt;
    dbin := fun _ _ _ => tt;
    final := fun _ => true;
  |}.

  Definition tbot : DFTA := {|
    Qst := unit;
    q_enum := [tt];
    q_all := fun q => match q with tt => or_introl eq_refl end;
    q_eqdec := fun x y => match x, y with tt, tt => left eq_refl end;
    dleaf := fun _ => tt;
    dbin := fun _ _ _ => tt;
    final := fun _ => false;
  |}.

  (* --------------------------------------------------------------------- *)
  (*  Product (for conj / disj) and complement (for neg)                   *)
  (* --------------------------------------------------------------------- *)

  Definition prod_eqdec (M N : DFTA)
    : forall x y : (Qst M * Qst N)%type, {x = y} + {x <> y}.
  Proof.
    intros x y. decide equality; [apply (q_eqdec N) | apply (q_eqdec M)].
  Defined.

  Lemma prod_q_all (M N : DFTA) :
    forall q : (Qst M * Qst N)%type, In q (list_prod (q_enum M) (q_enum N)).
  Proof.
    intros [a b]. apply in_prod; [apply (q_all M) | apply (q_all N)].
  Qed.

  (* The product automaton with a configurable final combiner. *)
  Definition tprod (fin : bool -> bool -> bool) (M N : DFTA) : DFTA := {|
    Qst := (Qst M * Qst N)%type;
    q_enum := list_prod (q_enum M) (q_enum N);
    q_all := prod_q_all M N;
    q_eqdec := prod_eqdec M N;
    dleaf := fun s => (dleaf M s, dleaf N s);
    dbin := fun s p q => (dbin M s (fst p) (fst q), dbin N s (snd p) (snd q));
    final := fun p => fin (final M (fst p)) (final N (snd p));
  |}.

  Definition tconj (M N : DFTA) : DFTA := tprod andb M N.
  Definition tdisj (M N : DFTA) : DFTA := tprod orb M N.

  Definition tneg (M : DFTA) : DFTA := {|
    Qst := Qst M;
    q_enum := q_enum M;
    q_all := q_all M;
    q_eqdec := q_eqdec M;
    dleaf := dleaf M;
    dbin := dbin M;
    final := fun q => negb (final M q);
  |}.

  (* The product runs to the pair of component runs (determinism ⇒ exactness). *)
  Lemma run_tprod (fin : bool -> bool -> bool) (M N : DFTA) :
    forall t, run (tprod fin M N) t = (run M t, run N t).
  Proof.
    induction t as [p | p l IHl r IHr]; simpl.
    - reflexivity.
    - rewrite IHl, IHr. simpl. reflexivity.
  Qed.

  Lemma teval_tconj (M N : DFTA) :
    forall t, teval (tconj M N) t = andb (teval M t) (teval N t).
  Proof.
    intro t. unfold teval, tconj. rewrite run_tprod. reflexivity.
  Qed.

  Lemma teval_tdisj (M N : DFTA) :
    forall t, teval (tdisj M N) t = orb (teval M t) (teval N t).
  Proof.
    intro t. unfold teval, tdisj. rewrite run_tprod. reflexivity.
  Qed.

  Lemma run_tneg (M : DFTA) : forall t, run (tneg M) t = run M t.
  Proof.
    induction t as [p | p l IHl r IHr]; simpl; [reflexivity|].
    rewrite IHl, IHr. reflexivity.
  Qed.

  Lemma teval_tneg (M : DFTA) : forall t, teval (tneg M) t = negb (teval M t).
  Proof.
    intro t. unfold teval. rewrite run_tneg. reflexivity.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  Saturation carrying a witness tree per reachable state               *)
  (* --------------------------------------------------------------------- *)

  (* Leaf entries: for each inhabited class, the pair (state, witness leaf). *)
  Definition leaf_entries (M : DFTA) : list (Qst M * DTree) :=
    flat_map (fun s => match pick s with
                       | Some d => [(dleaf M (letter d), DLeaf d)]
                       | None => []
                       end) sig_enum.

  (* Binary entries: combine present (state, tree) pairs by every inhabited
     class, building the node state and its witness tree. *)
  Definition bin_entries (M : DFTA) (acc : list (Qst M * DTree))
    : list (Qst M * DTree) :=
    flat_map (fun s => match pick s with
                       | Some d =>
                           flat_map (fun qt1 =>
                             map (fun qt2 =>
                               (dbin M (letter d) (fst qt1) (fst qt2),
                                DNode d (snd qt1) (snd qt2))) acc) acc
                       | None => []
                       end) sig_enum.

  Definition tstep (M : DFTA) (acc : list (Qst M * DTree))
    : list (Qst M * DTree) :=
    acc ++ leaf_entries M ++ bin_entries M acc.

  Definition sat_pairs (M : DFTA) : list (Qst M * DTree) :=
    iter (tstep M) (length (q_enum M)) [].

  (* Present states: the fst-projection. *)
  Definition leaf_states (M : DFTA) : list (Qst M) :=
    flat_map (fun s => match pick s with
                       | Some d => [dleaf M (letter d)]
                       | None => []
                       end) sig_enum.

  Definition bin_states (M : DFTA) (P : list (Qst M)) : list (Qst M) :=
    flat_map (fun s => match pick s with
                       | Some d => flat_map (fun q1 =>
                                     map (fun q2 => dbin M (letter d) q1 q2) P) P
                       | None => []
                       end) sig_enum.

  Definition Fstep (M : DFTA) (P : list (Qst M)) : list (Qst M) :=
    P ++ leaf_states M ++ bin_states M P.

  (* --------------------------------------------------------------------- *)
  (*  Bridge: the projection of tstep is Fstep on the projection           *)
  (* --------------------------------------------------------------------- *)

  Lemma map_fst_leaf_entries (M : DFTA) :
    map fst (leaf_entries M) = leaf_states M.
  Proof.
    unfold leaf_entries, leaf_states. rewrite map_flat_map.
    apply flat_map_ext. intro s. destruct (pick s) as [d|]; reflexivity.
  Qed.

  (* The per-class inner equality, isolated so we can rewrite under no binder. *)
  Lemma bin_inner (M : DFTA) (d : Dom A) (acc : list (Qst M * DTree)) :
    map fst (flat_map (fun qt1 =>
               map (fun qt2 =>
                 (dbin M (letter d) (fst qt1) (fst qt2),
                  DNode d (snd qt1) (snd qt2))) acc) acc)
    = flat_map (fun q1 => map (fun q2 => dbin M (letter d) q1 q2) (map fst acc))
               (map fst acc).
  Proof.
    rewrite map_flat_map.
    rewrite flat_map_map.
    apply flat_map_ext. intro qt1.
    rewrite map_map. rewrite map_map. apply map_ext. intro qt2. reflexivity.
  Qed.

  Lemma map_fst_bin_entries (M : DFTA) (acc : list (Qst M * DTree)) :
    map fst (bin_entries M acc) = bin_states M (map fst acc).
  Proof.
    unfold bin_entries, bin_states. rewrite map_flat_map.
    apply flat_map_ext. intro s.
    destruct (pick s) as [d|]; [apply bin_inner | reflexivity].
  Qed.

  Lemma map_fst_tstep (M : DFTA) (acc : list (Qst M * DTree)) :
    map fst (tstep M acc) = Fstep M (map fst acc).
  Proof.
    unfold tstep, Fstep. rewrite map_app, map_app.
    rewrite map_fst_leaf_entries, map_fst_bin_entries. reflexivity.
  Qed.

  Lemma map_fst_iter_tstep (M : DFTA) (k : nat) :
    map fst (iter (tstep M) k []) = iter (Fstep M) k [].
  Proof.
    induction k as [|k IH]; simpl; [reflexivity|].
    rewrite map_fst_tstep, IH. reflexivity.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  Saturation invariant: every carried pair (q,t) has run M t = q        *)
  (* --------------------------------------------------------------------- *)

  Definition PairInv (M : DFTA) (l : list (Qst M * DTree)) : Prop :=
    forall q t, In (q, t) l -> run M t = q.

  Lemma leaf_entries_inv (M : DFTA) : PairInv M (leaf_entries M).
  Proof.
    intros q t Hin. unfold leaf_entries in Hin. apply in_flat_map in Hin.
    destruct Hin as [s [_ Hs]]. destruct (pick s) as [d|] eqn:Hps; simpl in Hs.
    - destruct Hs as [Heq | []]. injection Heq as <- <-. simpl. reflexivity.
    - destruct Hs.
  Qed.

  Lemma bin_entries_inv (M : DFTA) (acc : list (Qst M * DTree)) :
    PairInv M acc -> PairInv M (bin_entries M acc).
  Proof.
    intros Hacc q t Hin. unfold bin_entries in Hin. apply in_flat_map in Hin.
    destruct Hin as [s [_ Hs]]. destruct (pick s) as [d|] eqn:Hps; [|destruct Hs].
    apply in_flat_map in Hs. destruct Hs as [qt1 [Hin1 Hs]].
    apply in_map_iff in Hs. destruct Hs as [qt2 [Heq Hin2]].
    injection Heq as <- <-. simpl.
    rewrite (Hacc (fst qt1) (snd qt1)); [| destruct qt1; exact Hin1].
    rewrite (Hacc (fst qt2) (snd qt2)); [| destruct qt2; exact Hin2].
    reflexivity.
  Qed.

  Lemma tstep_inv (M : DFTA) (acc : list (Qst M * DTree)) :
    PairInv M acc -> PairInv M (tstep M acc).
  Proof.
    intros Hacc q t Hin. unfold tstep in Hin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    - apply Hacc; exact Hin.
    - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      + apply (leaf_entries_inv M); exact Hin.
      + apply (bin_entries_inv M acc Hacc); exact Hin.
  Qed.

  Lemma sat_pairs_inv (M : DFTA) : PairInv M (sat_pairs M).
  Proof.
    unfold sat_pairs. generalize (length (q_enum M)) as n. intro n.
    induction n as [|n IH]; simpl.
    - intros q t [].
    - apply tstep_inv. exact IH.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  Fstep is extensive / monotone / bounded ⇒ the saturation is closed   *)
  (* --------------------------------------------------------------------- *)

  Lemma incl_leaf_states (M : DFTA) (P : list (Qst M)) :
    incl (leaf_states M) (Fstep M P).
  Proof.
    unfold Fstep. apply incl_appr. apply incl_appl. apply incl_refl.
  Qed.

  Lemma incl_bin_states (M : DFTA) (P : list (Qst M)) :
    incl (bin_states M P) (Fstep M P).
  Proof.
    unfold Fstep. apply incl_appr. apply incl_appr. apply incl_refl.
  Qed.

  Lemma leaf_in_Fstep (M : DFTA) (s : Sigma) (d : Dom A) (P : list (Qst M)) :
    In s sig_enum -> pick s = Some d -> In (dleaf M (letter d)) (Fstep M P).
  Proof.
    intros Hs Hpd. apply incl_leaf_states. unfold leaf_states.
    apply in_flat_map. exists s. split; [exact Hs|]. rewrite Hpd. left; reflexivity.
  Qed.

  Lemma bin_in_Fstep (M : DFTA) (s : Sigma) (d : Dom A) (P : list (Qst M))
                     (q1 q2 : Qst M) :
    In s sig_enum -> pick s = Some d -> In q1 P -> In q2 P ->
    In (dbin M (letter d) q1 q2) (Fstep M P).
  Proof.
    intros Hs Hpd Hq1 Hq2. apply incl_bin_states. unfold bin_states.
    apply in_flat_map. exists s. split; [exact Hs|]. rewrite Hpd.
    apply in_flat_map. exists q1. split; [exact Hq1|].
    apply in_map_iff. exists q2. split; [reflexivity | exact Hq2].
  Qed.

  Lemma Fstep_extensive (M : DFTA) (P : list (Qst M)) : incl P (Fstep M P).
  Proof. unfold Fstep. apply incl_appl. apply incl_refl. Qed.

  Lemma bin_states_mono (M : DFTA) (P P' : list (Qst M)) :
    incl P P' -> incl (bin_states M P) (bin_states M P').
  Proof.
    intros H x Hx. unfold bin_states in *.
    apply in_flat_map in Hx. destruct Hx as [s [Hs Hin]].
    apply in_flat_map. exists s. split; [exact Hs|].
    destruct (pick s) as [d|]; [|exact Hin].
    apply in_flat_map in Hin. destruct Hin as [q1 [Hq1 Hin]].
    apply in_map_iff in Hin. destruct Hin as [q2 [Heq Hq2]].
    apply in_flat_map. exists q1. split; [apply H; exact Hq1|].
    apply in_map_iff. exists q2. split; [exact Heq | apply H; exact Hq2].
  Qed.

  Lemma Fstep_mono (M : DFTA) (P P' : list (Qst M)) :
    incl P P' -> incl (Fstep M P) (Fstep M P').
  Proof.
    intros H. unfold Fstep. apply incl_app.
    - apply incl_tran with (m := P'); [exact H | apply incl_appl; apply incl_refl].
    - apply incl_app.
      + apply incl_appr. apply incl_appl. apply incl_refl.
      + apply incl_appr. apply incl_appr. apply bin_states_mono. exact H.
  Qed.

  Lemma Fstep_bounded (M : DFTA) (P : list (Qst M)) : incl (Fstep M P) (q_enum M).
  Proof. intros x _. apply q_all. Qed.

  (* The saturation's present-state set is closed under one Fstep — the
     decidable-emptiness fixpoint, instantiated from the generic stabilization. *)
  Lemma present_closed (M : DFTA) :
    incl (Fstep M (map fst (sat_pairs M))) (map fst (sat_pairs M)).
  Proof.
    unfold sat_pairs. rewrite map_fst_iter_tstep.
    (* iter (Fstep M) (length (q_enum M)) [] = chain ... at U := q_enum M *)
    pose proof (stabilizes (Qst M) (q_eqdec M) (Fstep M) (q_enum M)
                  (Fstep_extensive M) (Fstep_mono M) (Fstep_bounded M)) as Hstab.
    unfold chain in Hstab. exact Hstab.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  Completeness: every tree's run-state is present (with a witness tree) *)
  (* --------------------------------------------------------------------- *)

  Lemma present_complete (M : DFTA) :
    forall t, In (run M t) (map fst (sat_pairs M)).
  Proof.
    induction t as [p | p l IHl r IHr]; simpl.
    - (* DLeaf p : state dleaf M (letter p) *)
      destruct (pick_total (letter p) (sig_all (letter p))) as [d0 Hd0].
      assert (Hle : letter d0 = letter p) by (apply pick_letter; exact Hd0).
      apply present_closed.
      replace (dleaf M (letter p)) with (dleaf M (letter d0)) by (rewrite Hle; reflexivity).
      apply (leaf_in_Fstep M (letter p) d0); [apply sig_all | exact Hd0].
    - (* DNode p l r : state dbin M (letter p) (run M l) (run M r) *)
      destruct (pick_total (letter p) (sig_all (letter p))) as [d0 Hd0].
      assert (Hle : letter d0 = letter p) by (apply pick_letter; exact Hd0).
      apply present_closed.
      replace (dbin M (letter p) (run M l) (run M r))
        with (dbin M (letter d0) (run M l) (run M r)) by (rewrite Hle; reflexivity).
      apply (bin_in_Fstep M (letter p) d0); [apply sig_all | exact Hd0 | exact IHl | exact IHr].
  Qed.

  Lemma pairs_complete (M : DFTA) :
    forall t, exists t', In (run M t, t') (sat_pairs M).
  Proof.
    intro t. pose proof (present_complete M t) as Hin.
    apply in_map_iff in Hin. destruct Hin as [[q t'] [Hfst Hpair]].
    simpl in Hfst. subst q. exists t'. exact Hpair.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  SAT / WIT and their soundness + completeness                          *)
  (* --------------------------------------------------------------------- *)

  Definition tsat (M : DFTA) : bool :=
    existsb (fun qt => final M (fst qt)) (sat_pairs M).

  Definition twit (M : DFTA) : option DTree :=
    match find (fun qt => final M (fst qt)) (sat_pairs M) with
    | Some qt => Some (snd qt)
    | None => None
    end.

  Lemma tsat_sound (M : DFTA) : tsat M = true -> exists t, teval M t = true.
  Proof.
    intro H. unfold tsat in H. apply existsb_exists in H.
    destruct H as [qt [Hin Hfin]].
    exists (snd qt). unfold teval.
    rewrite (sat_pairs_inv M (fst qt) (snd qt)); [exact Hfin | destruct qt; exact Hin].
  Qed.

  Lemma tsat_complete (M : DFTA) : forall t, teval M t = true -> tsat M = true.
  Proof.
    intros t Hev. unfold tsat. apply existsb_exists.
    destruct (pairs_complete M t) as [t' Hpair].
    exists (run M t, t'). split; [exact Hpair|]. simpl. unfold teval in Hev. exact Hev.
  Qed.

  Lemma twit_sound (M : DFTA) : forall t, twit M = Some t -> teval M t = true.
  Proof.
    intros t H. unfold twit in H.
    destruct (find (fun qt => final M (fst qt)) (sat_pairs M)) as [qt|] eqn:Hf;
      [|discriminate].
    injection H as <-. apply find_some in Hf. destruct Hf as [Hin Hfin].
    unfold teval.
    rewrite (sat_pairs_inv M (fst qt) (snd qt)); [exact Hfin | destruct qt; exact Hin].
  Qed.

  Lemma twit_total (M : DFTA) : tsat M = true -> exists t, twit M = Some t.
  Proof.
    intro H. unfold tsat in H. apply existsb_find_some in H.
    destruct H as [qt [Hfind _]]. exists (snd qt). unfold twit. rewrite Hfind. reflexivity.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  Closure: the trees over A form an EBA                                  *)
  (* --------------------------------------------------------------------- *)

  Definition tree_eba : EBA := {|
    Dom  := DTree;
    Pred := DFTA;
    top  := ttop;
    bot  := tbot;
    conj := tconj;
    disj := tdisj;
    neg  := tneg;
    eval := teval;
    sat  := tsat;
    wit  := twit;
  |}.

  Theorem tree_eba_laws : EBA_Laws tree_eba.
  Proof.
    constructor.
    - (* eval_top *) intro t. unfold eval, top, tree_eba, teval. reflexivity.
    - (* eval_bot *) intro t. unfold eval, bot, tree_eba, teval. reflexivity.
    - (* eval_conj *) intros p q t. apply teval_tconj.
    - (* eval_disj *) intros p q t. apply teval_tdisj.
    - (* eval_neg *) intros p t. apply teval_tneg.
    - (* sat_sound *) intro p. apply tsat_sound.
    - (* sat_complete *) intros p t. apply tsat_complete.
    - (* wit_sound *) intros p t. apply twit_sound.
    - (* wit_total *) intro p. apply twit_total.
  Qed.

End Tree.

Print Assumptions tree_eba_laws.
