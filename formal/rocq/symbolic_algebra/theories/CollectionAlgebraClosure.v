(*
 * CollectionAlgebraClosure: the effective Boolean algebras are closed under the
 * (order-insensitive) collection constructor. Given an EBA A and a finite basis
 * of element classes `classes : list (Pred A)`, the collection EBA over domain
 * `list (Dom A)` (a bag, represented as a list since the predicates only count
 * occupancy) has predicates given by the Boolean closure of *occupancy atoms*
 * `CFAtom i` = "some element satisfies classes[i]". This is the De-Morgan-dual
 * ∀/∃ core of the Rust BagAlgebra<A>/BagPred<P> (prattail/src/
 * collection_algebra.rs:67): the Rust `any_elem p` is `CFAtom`, `all p` is
 * `¬CFAtom(¬p)`, and the full [lo,hi] cardinality atoms are the counting
 * extension built over the same minterm idea.
 *
 * SAT is decided exactly by the Rust strategy specialised to occupancy: a bag is
 * characterised, w.r.t. the basis, by which classes it occupies (its support),
 * and a support `a : list bool` is realizable iff every occupied class is
 * jointly satisfiable with the negations of the unoccupied classes — i.e. there
 * is an element witnessing `classes[i] ∧ ⋀_{a[j]=false} ¬classes[j]`. SAT
 * enumerates the finitely many supports (`all_bvecs (length classes)`); WIT
 * materializes a bag from a realizable, formula-satisfying support.
 *
 * Main result: `collection_eba_laws : EBA_Laws collection_eba`.
 *
 * Spec-to-Code Traceability:
 *   Coq                     | Rust (prattail/src/collection_algebra.rs)
 *   ------------------------|------------------------------------------
 *   CFAtom / ceval          | BagPred::Count{_,1,None} / BagAlgebra::evaluate
 *   support / realizable    | per-minterm occupancy / minterm satisfiability
 *   csat (enum supports)    | BagAlgebra::is_satisfiable (bounded feasibility)
 *   cwit (materialize bag)  | BagAlgebra::witness
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

Lemma existsb_find_some {X} (f : X -> bool) (l : list X) :
  existsb f l = true -> exists x, find f l = Some x /\ f x = true.
Proof.
  induction l as [|a l IH]; simpl; [discriminate|].
  destruct (f a) eqn:E.
  - intros _. exists a. split; [reflexivity | exact E].
  - simpl. exact IH.
Qed.

Lemma nth_map_nth_error {X Y} (g : X -> Y) (l : list X) (i : nat) (dy : Y) :
  nth i (map g l) dy = match nth_error l i with
                       | Some x => g x
                       | None => dy
                       end.
Proof.
  revert i. induction l as [|x l IH]; intro i; simpl.
  - destruct i; reflexivity.
  - destruct i; simpl; [reflexivity | apply IH].
Qed.

(* combine (map g l) l pairs each (g x, x) positionally. *)
Lemma in_combine_map_self {X Y} (g : X -> Y) (l : list X) (b : Y) (p : X) :
  In (b, p) (combine (map g l) l) -> b = g p.
Proof.
  induction l as [|x l IH]; simpl; [intros []|].
  intros [Heq | Hin]; [injection Heq as <- <-; reflexivity | apply IH; exact Hin].
Qed.

(* the i-th positional pair is in the zip, when both lists agree in length. *)
Lemma in_combine_nth_gen {X Y} (l : list X) (l' : list Y) (i : nat) (dx : X) (dy : Y) :
  i < length l -> length l = length l' ->
  In (nth i l dx, nth i l' dy) (combine l l').
Proof.
  revert l' i. induction l as [|x l IH]; intros l' i Hi Hlen; simpl in Hi.
  - exfalso. apply (Nat.nlt_0_r i Hi).
  - destruct l' as [|y l']; simpl in Hlen; [discriminate|].
    destruct i; simpl.
    + left; reflexivity.
    + right. apply IH; [apply Nat.succ_lt_mono; exact Hi | injection Hlen; intro; assumption].
Qed.

Lemma nth_error_to_nth {X} (l : list X) (i : nat) (d x : X) :
  nth_error l i = Some x -> nth i l d = x.
Proof.
  revert i. induction l as [|y l IH]; intros [|i]; simpl; try discriminate.
  - intro H; injection H as <-; reflexivity.
  - apply IH.
Qed.

Fixpoint all_bvecs (n : nat) : list (list bool) :=
  match n with
  | 0 => [ [] ]
  | S k => flat_map (fun a => [false :: a ; true :: a]) (all_bvecs k)
  end.

Lemma all_bvecs_length : forall n a, In a (all_bvecs n) -> length a = n.
Proof.
  induction n as [|k IH]; intros a Hin; simpl in Hin.
  - destruct Hin as [<-|[]]; reflexivity.
  - apply in_flat_map in Hin. destruct Hin as [a' [Hin' Hcons]].
    simpl in Hcons. destruct Hcons as [<-|[<-|[]]]; simpl; rewrite (IH a' Hin'); reflexivity.
Qed.

Lemma all_bvecs_complete : forall a, In a (all_bvecs (length a)).
Proof.
  induction a as [|b a IH]; simpl.
  - left; reflexivity.
  - apply in_flat_map. exists a. split; [exact IH|].
    destruct b; simpl; [right; left; reflexivity | left; reflexivity].
Qed.

(* ===================================================================== *)
(*  The collection EBA construction over a fixed element-class basis      *)
(* ===================================================================== *)

Section Collection.
  Variable A : EBA.
  Variable LA : EBA_Laws A.
  Variable classes : list (Pred A).

  (* Boolean formulas over positional occupancy atoms. *)
  Inductive CF : Type :=
  | CFTrue  : CF
  | CFFalse : CF
  | CFAtom  : nat -> CF
  | CFAnd   : CF -> CF -> CF
  | CFOr    : CF -> CF -> CF
  | CFNot   : CF -> CF.

  Definition Bag : Type := list (Dom A).

  Definition present (p : Pred A) (bag : Bag) : bool :=
    existsb (fun e => eval p e) bag.

  (* Evaluate a formula against an actual bag. *)
  Fixpoint ceval (f : CF) (bag : Bag) : bool :=
    match f with
    | CFTrue  => true
    | CFFalse => false
    | CFAtom i => match nth_error classes i with
                  | Some p => present p bag
                  | None => false
                  end
    | CFAnd x y => ceval x bag && ceval y bag
    | CFOr  x y => ceval x bag || ceval y bag
    | CFNot x   => negb (ceval x bag)
    end.

  (* Evaluate a formula under an abstract support assignment. *)
  Fixpoint funder (f : CF) (a : list bool) : bool :=
    match f with
    | CFTrue  => true
    | CFFalse => false
    | CFAtom i => nth i a false
    | CFAnd x y => funder x a && funder y a
    | CFOr  x y => funder x a || funder y a
    | CFNot x   => negb (funder x a)
    end.

  (* The support of a bag: which basis classes it occupies. *)
  Definition support (bag : Bag) : list bool := map (fun p => present p bag) classes.

  (* Conjunction of the negations of the unoccupied classes under support a. *)
  Definition neg_constraint (a : list bool) : Pred A :=
    fold_right (fun (bp : bool * Pred A) acc =>
                  if fst bp then acc else conj (neg (snd bp)) acc)
               top (combine a classes).

  Definition realizable (a : list bool) : bool :=
    forallb (fun (bp : bool * Pred A) =>
               if fst bp then sat (conj (snd bp) (neg_constraint a)) else true)
            (combine a classes).

  Definition opt_elem (o : option (Dom A)) : Bag :=
    match o with Some e => [e] | None => [] end.

  Definition wit_bag (a : list bool) : Bag :=
    flat_map (fun (bp : bool * Pred A) =>
                if fst bp
                then opt_elem (wit (conj (snd bp) (neg_constraint a)))
                else []) (combine a classes).

  Definition csat (f : CF) : bool :=
    existsb (fun a => realizable a && funder f a) (all_bvecs (length classes)).

  Definition cwit (f : CF) : option Bag :=
    match find (fun a => realizable a && funder f a) (all_bvecs (length classes)) with
    | Some a => Some (wit_bag a)
    | None => None
    end.

  Definition collection_eba : EBA := {|
    Dom  := Bag;
    Pred := CF;
    top  := CFTrue;
    bot  := CFFalse;
    conj := CFAnd;
    disj := CFOr;
    neg  := CFNot;
    eval := ceval;
    sat  := csat;
    wit  := cwit;
  |}.

  (* --------------------------------------------------------------------- *)
  (*  Bridge: ceval over a bag = funder over its support                   *)
  (* --------------------------------------------------------------------- *)

  Lemma ceval_funder_support : forall f bag, ceval f bag = funder f (support bag).
  Proof.
    induction f; intro bag; simpl.
    - reflexivity.
    - reflexivity.
    - unfold support. rewrite nth_map_nth_error. reflexivity.
    - rewrite IHf1, IHf2; reflexivity.
    - rewrite IHf1, IHf2; reflexivity.
    - rewrite IHf; reflexivity.
  Qed.

  Lemma funder_ext : forall f a a', a = a' -> funder f a = funder f a'.
  Proof. intros f a a' ->. reflexivity. Qed.

  (* --------------------------------------------------------------------- *)
  (*  neg_constraint characterization                                      *)
  (* --------------------------------------------------------------------- *)

  Lemma neg_constraint_sound : forall a e,
    eval (neg_constraint a) e = true ->
    forall p, In (false, p) (combine a classes) -> eval p e = false.
  Proof.
    intros a e. unfold neg_constraint.
    induction (combine a classes) as [|bp L IH]; simpl; intros Hev p Hin.
    - destruct Hin.
    - destruct bp as [b q]; simpl in *.
      destruct b.
      + (* occupied: factor skipped; recurse *)
        destruct Hin as [Heq | Hin]; [discriminate Heq | apply (IH Hev p Hin)].
      + rewrite (eval_conj A LA) in Hev. apply andb_true_iff in Hev.
        destruct Hev as [Hneg Hrest].
        rewrite (eval_neg A LA) in Hneg. apply negb_true_iff in Hneg.
        destruct Hin as [Heq | Hin].
        * injection Heq as <-. exact Hneg.
        * apply (IH Hrest p Hin).
  Qed.

  Lemma neg_constraint_complete : forall a e,
    (forall p, In (false, p) (combine a classes) -> eval p e = false) ->
    eval (neg_constraint a) e = true.
  Proof.
    intros a e. unfold neg_constraint.
    induction (combine a classes) as [|bp L IH]; simpl; intro Hfalse.
    - apply (eval_top A LA).
    - destruct bp as [b q]; simpl in *.
      destruct b.
      + apply IH. intros p Hin. apply Hfalse. right. exact Hin.
      + rewrite (eval_conj A LA), (eval_neg A LA). apply andb_true_iff. split.
        * apply negb_true_iff. apply Hfalse. left. reflexivity.
        * apply IH. intros p Hin. apply Hfalse. right. exact Hin.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  wit_bag membership                                                   *)
  (* --------------------------------------------------------------------- *)

  Lemma wit_bag_mem : forall a e,
    In e (wit_bag a) ->
    exists p, In (true, p) (combine a classes) /\
              wit (conj p (neg_constraint a)) = Some e.
  Proof.
    intros a e Hin. unfold wit_bag in Hin. apply in_flat_map in Hin.
    destruct Hin as [bp [Hin Hbp]]. destruct bp as [b q]; simpl in Hbp.
    destruct b.
    - unfold opt_elem in Hbp. destruct (wit (conj q (neg_constraint a))) as [e'|] eqn:W.
      + destruct Hbp as [<-|[]]. exists q. split; [exact Hin | exact W].
      + destruct Hbp.
    - destruct Hbp.
  Qed.

  Lemma wit_bag_sat_neg : forall a e,
    In e (wit_bag a) -> eval (neg_constraint a) e = true.
  Proof.
    intros a e Hin. apply wit_bag_mem in Hin. destruct Hin as [p [_ W]].
    apply (wit_sound A LA) in W. rewrite (eval_conj A LA) in W.
    apply andb_true_iff in W. destruct W as [_ Hneg]. exact Hneg.
  Qed.

  Lemma wit_bag_occupies : forall a p,
    realizable a = true ->
    In (true, p) (combine a classes) ->
    exists e, In e (wit_bag a) /\ eval p e = true.
  Proof.
    intros a p Hreal Hin. unfold realizable in Hreal.
    rewrite forallb_forall in Hreal.
    specialize (Hreal (true, p) Hin). simpl in Hreal.
    apply (wit_total A LA) in Hreal. destruct Hreal as [e He].
    exists e. split.
    - unfold wit_bag. apply in_flat_map. exists (true, p). split; [exact Hin|].
      simpl. rewrite He. simpl. left; reflexivity.
    - apply (wit_sound A LA) in He. rewrite (eval_conj A LA) in He.
      apply andb_true_iff in He. destruct He as [Hp _]. exact Hp.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  The decisive lemma: a realizable support is realized by wit_bag      *)
  (* --------------------------------------------------------------------- *)

  Lemma support_wit_bag : forall a,
    realizable a = true -> length a = length classes ->
    support (wit_bag a) = a.
  Proof.
    intros a Hreal Hlen. unfold support.
    apply nth_ext with (d := false) (d' := false).
    - rewrite length_map. rewrite Hlen. reflexivity.
    - intros i Hi. rewrite length_map in Hi.
      rewrite (nth_map_nth_error (fun p => present p (wit_bag a)) classes i false).
      destruct (nth_error classes i) as [p|] eqn:Hni.
      + (* classes[i] = p; combine entry i is (nth i a false, p) *)
        assert (Hcomb : In (nth i a false, p) (combine a classes)).
        { pose proof (in_combine_nth_gen a classes i false top
                        ltac:(rewrite Hlen; exact Hi) Hlen) as Hg.
          rewrite (nth_error_to_nth classes i top p Hni) in Hg. exact Hg. }
        destruct (nth i a false) eqn:Hai.
        * (* occupied: wit_bag has a witness of p *)
          destruct (wit_bag_occupies a p Hreal Hcomb) as [e [Hein Hpe]].
          unfold present. apply existsb_exists. exists e. split; [exact Hein | exact Hpe].
        * (* unoccupied: no witness satisfies p *)
          unfold present. destruct (existsb (fun e => eval p e) (wit_bag a)) eqn:Hex;
            [|reflexivity].
          apply existsb_exists in Hex. destruct Hex as [e [Hein Hpe]].
          apply wit_bag_sat_neg in Hein.
          rewrite (neg_constraint_sound a e Hein p Hcomb) in Hpe. discriminate.
      + (* i out of range, impossible since i < length classes *)
        apply nth_error_None in Hni. exfalso. apply (Nat.lt_irrefl i).
        apply Nat.lt_le_trans with (m := length classes); [exact Hi | exact Hni].
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  A real bag's support is realizable                                   *)
  (* --------------------------------------------------------------------- *)

  Lemma realizable_support : forall bag, realizable (support bag) = true.
  Proof.
    intro bag. unfold realizable. rewrite forallb_forall.
    intros bp Hin. destruct bp as [b p]. simpl. destruct b; [|reflexivity].
    (* (true, p) in combine (support bag) classes ⇒ present p bag = true *)
    unfold support in Hin.
    pose proof (in_combine_map_self (fun p => present p bag) classes true p Hin) as Hp.
    symmetry in Hp. unfold present in Hp.
    apply existsb_exists in Hp. destruct Hp as [e [Hein Hpe]].
    apply (sat_complete A LA) with (d := e).
    rewrite (eval_conj A LA). apply andb_true_iff. split.
    - exact Hpe.
    - apply neg_constraint_complete. intros q Hq.
      (* (false, q) in combine (support bag) classes ⇒ present q bag = false *)
      unfold support in Hq.
      pose proof (in_combine_map_self (fun p => present p bag) classes false q Hq) as Hqf.
      symmetry in Hqf. unfold present in Hqf.
      destruct (eval q e) eqn:Hqe; [|reflexivity].
      exfalso.
      assert (Htrue : existsb (fun e0 => eval q e0) bag = true).
      { apply existsb_exists. exists e. split; [exact Hein | exact Hqe]. }
      rewrite Hqf in Htrue. discriminate.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  SAT / WIT soundness and completeness                                 *)
  (* --------------------------------------------------------------------- *)

  Lemma csat_sound : forall f, csat f = true -> exists bag, ceval f bag = true.
  Proof.
    intros f Hsat. unfold csat in Hsat. apply existsb_exists in Hsat.
    destruct Hsat as [a [Hin Hand]]. apply andb_true_iff in Hand.
    destruct Hand as [Hreal Hfun].
    pose proof (all_bvecs_length _ _ Hin) as Hlen.
    exists (wit_bag a). rewrite ceval_funder_support.
    rewrite (support_wit_bag a Hreal Hlen). exact Hfun.
  Qed.

  Lemma csat_complete : forall f bag, ceval f bag = true -> csat f = true.
  Proof.
    intros f bag Hev. unfold csat. apply existsb_exists.
    exists (support bag). split.
    - assert (Hl : length (support bag) = length classes).
      { unfold support. apply length_map. }
      rewrite <- Hl. apply all_bvecs_complete.
    - apply andb_true_iff. split.
      + apply realizable_support.
      + rewrite <- ceval_funder_support. exact Hev.
  Qed.

  Lemma cwit_sound : forall f bag, cwit f = Some bag -> ceval f bag = true.
  Proof.
    intros f bag Hwit. unfold cwit in Hwit.
    destruct (find (fun a => realizable a && funder f a) (all_bvecs (length classes)))
      as [a|] eqn:Hfind; [|discriminate].
    injection Hwit as <-.
    apply find_some in Hfind. destruct Hfind as [Hin Hand].
    apply andb_true_iff in Hand. destruct Hand as [Hreal Hfun].
    pose proof (all_bvecs_length _ _ Hin) as Hlen.
    rewrite ceval_funder_support, (support_wit_bag a Hreal Hlen). exact Hfun.
  Qed.

  Lemma cwit_total : forall f, csat f = true -> exists bag, cwit f = Some bag.
  Proof.
    intros f Hsat. unfold csat in Hsat. apply existsb_find_some in Hsat.
    destruct Hsat as [a [Hfind _]]. exists (wit_bag a). unfold cwit.
    rewrite Hfind. reflexivity.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  Closure: the collection is an EBA                                     *)
  (* --------------------------------------------------------------------- *)

  Theorem collection_eba_laws : EBA_Laws collection_eba.
  Proof.
    constructor.
    - intros d; reflexivity.
    - intros d; reflexivity.
    - intros p q d; reflexivity.
    - intros p q d; reflexivity.
    - intros p d; reflexivity.
    - intros p. apply csat_sound.
    - intros p d. apply csat_complete.
    - intros p d. apply cwit_sound.
    - intros p. apply cwit_total.
  Qed.

End Collection.

Print Assumptions collection_eba_laws.
