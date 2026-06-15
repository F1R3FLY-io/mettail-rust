(*
 * ProductAlgebraClosure: the effective Boolean algebras are closed under the
 * binary (independent-domain) product. Given EBAs A and B, the product EBA over
 * domain `Dom A * Dom B` has predicates represented as a DNF — a disjunction of
 * "rectangles", each an independent conjunction (pa /\ pb) over the two factor
 * predicate syntaxes. This is the Coq model of the Rust `ProductAlgebra<A,B>`
 * / `ProductPred` (prattail/src/symbolic.rs:1965) with its `to_dnf` /
 * `negate_pred` operations; the N-ary generalization (`NaryProductAlgebra`,
 * product_nary.rs) iterates this binary closure.
 *
 * Main result: `product_eba_laws : EBA_Laws A -> EBA_Laws B -> EBA_Laws
 * product_eba` — the product of two classical EBAs is again a classical EBA, so
 * intersection/union/complement/SAT/witness all lift component-wise. The crux is
 * `pdnf_neg_eval` (De Morgan on the DNF: complement = cross-product of negated
 * rectangles) and `pdnf_conj_eval` (distribution of conjunction over the two
 * disjunctions).
 *
 * Spec-to-Code Traceability:
 *   Coq                  | Rust (prattail/src/symbolic.rs, product_nary.rs)
 *   ---------------------|------------------------------------------------
 *   PDnf / Rect          | ProductPred (DNF of independent rectangles)
 *   pdnf_conj (flat_map) | ProductAlgebra::and (cross-product to_dnf)
 *   pdnf_disj (++)       | ProductAlgebra::or (DNF append)
 *   pdnf_neg (De Morgan) | ProductAlgebra::not / negate_pred
 *   pdnf_sat / pdnf_wit  | ProductAlgebra::is_satisfiable / witness
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.
From SymbolicAlgebra Require Import EffectiveBooleanAlgebra.

(* ===================================================================== *)
(*  Generic existsb helpers (boolean disjunction over lists)             *)
(* ===================================================================== *)

Lemma existsb_ext {X} (f g : X -> bool) (l : list X) :
  (forall x, f x = g x) -> existsb f l = existsb g l.
Proof.
  intros H. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite H, IH. reflexivity.
Qed.

Lemma existsb_map {X Y} (f : Y -> bool) (g : X -> Y) (l : list X) :
  existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma existsb_flat_map {X Y} (f : Y -> bool) (g : X -> list Y) (l : list X) :
  existsb f (flat_map g l) = existsb (fun x => existsb f (g x)) l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite existsb_app, IH. reflexivity.
Qed.

Lemma existsb_andb_const_l {X} (c : bool) (f : X -> bool) (l : list X) :
  existsb (fun x => c && f x) l = c && existsb f l.
Proof.
  induction l as [|a l IH]; simpl.
  - rewrite andb_false_r. reflexivity.
  - rewrite IH. destruct c, (f a), (existsb f l); reflexivity.
Qed.

Lemma existsb_andb_const_r {X} (c : bool) (f : X -> bool) (l : list X) :
  existsb (fun x => f x && c) l = existsb f l && c.
Proof.
  induction l as [|a l IH]; simpl.
  - reflexivity.
  - rewrite IH. destruct c, (f a), (existsb f l); reflexivity.
Qed.

Lemma existsb_find_some {X} (f : X -> bool) (l : list X) :
  existsb f l = true -> exists x, find f l = Some x /\ f x = true.
Proof.
  induction l as [|a l IH]; simpl; [discriminate|].
  destruct (f a) eqn:E.
  - intros _. exists a. split; [reflexivity | exact E].
  - simpl. exact IH.
Qed.

(* ===================================================================== *)
(*  The product EBA construction                                          *)
(* ===================================================================== *)

Section Product.
  Variables A B : EBA.

  Definition Rect : Type := (Pred A * Pred B)%type.
  Definition PDnf : Type := list Rect.

  Definition rect_eval (r : Rect) (d : Dom A * Dom B) : bool :=
    eval (fst r) (fst d) && eval (snd r) (snd d).

  Definition pdnf_eval (L : PDnf) (d : Dom A * Dom B) : bool :=
    existsb (fun r => rect_eval r d) L.

  Definition pdnf_top : PDnf := [ (top, top) ].
  Definition pdnf_bot : PDnf := [].
  Definition pdnf_disj (L1 L2 : PDnf) : PDnf := L1 ++ L2.

  Definition rect_conj (r1 r2 : Rect) : Rect :=
    (conj (fst r1) (fst r2), conj (snd r1) (snd r2)).

  Definition pdnf_conj (L1 L2 : PDnf) : PDnf :=
    flat_map (fun r1 => map (fun r2 => rect_conj r1 r2) L2) L1.

  (* De Morgan: each rectangle's complement is a 2-rectangle DNF; the whole
     complement is the conjunction (cross-product) of those. *)
  Definition rect_neg (r : Rect) : PDnf :=
    [ (neg (fst r), top) ; (top, neg (snd r)) ].

  Definition pdnf_neg (L : PDnf) : PDnf :=
    fold_right (fun r acc => pdnf_conj (rect_neg r) acc) pdnf_top L.

  Definition pdnf_sat (L : PDnf) : bool :=
    existsb (fun r => sat (fst r) && sat (snd r)) L.

  Definition pdnf_wit (L : PDnf) : option (Dom A * Dom B) :=
    match find (fun r => sat (fst r) && sat (snd r)) L with
    | Some r =>
        match wit (fst r), wit (snd r) with
        | Some da, Some db => Some (da, db)
        | _, _ => None
        end
    | None => None
    end.

  Definition product_eba : EBA := {|
    Dom  := Dom A * Dom B;
    Pred := PDnf;
    top  := pdnf_top;
    bot  := pdnf_bot;
    conj := pdnf_conj;
    disj := pdnf_disj;
    neg  := pdnf_neg;
    eval := pdnf_eval;
    sat  := pdnf_sat;
    wit  := pdnf_wit;
  |}.

  (* --------------------------------------------------------------------- *)
  (*  EVAL homomorphism                                                    *)
  (* --------------------------------------------------------------------- *)

  Lemma pdnf_disj_eval : forall L1 L2 d,
    pdnf_eval (pdnf_disj L1 L2) d = pdnf_eval L1 d || pdnf_eval L2 d.
  Proof.
    intros L1 L2 d. unfold pdnf_eval, pdnf_disj. rewrite existsb_app. reflexivity.
  Qed.

  Lemma pdnf_conj_eval :
    EBA_Laws A -> EBA_Laws B ->
    forall L1 L2 d, pdnf_eval (pdnf_conj L1 L2) d = pdnf_eval L1 d && pdnf_eval L2 d.
  Proof.
    intros LA LB L1 L2 d. unfold pdnf_eval, pdnf_conj.
    rewrite existsb_flat_map.
    rewrite (existsb_ext _ (fun r1 => rect_eval r1 d && existsb (fun r => rect_eval r d) L2)).
    - apply existsb_andb_const_r.
    - intro r1. rewrite existsb_map.
      rewrite (existsb_ext _ (fun r2 => rect_eval r1 d && rect_eval r2 d)).
      + apply existsb_andb_const_l.
      + intro r2. unfold rect_conj, rect_eval; simpl.
        rewrite (eval_conj A LA), (eval_conj B LB).
        destruct (eval (fst r1) (fst d)), (eval (fst r2) (fst d)),
                 (eval (snd r1) (snd d)), (eval (snd r2) (snd d)); reflexivity.
  Qed.

  Lemma rect_neg_eval :
    EBA_Laws A -> EBA_Laws B ->
    forall r d, pdnf_eval (rect_neg r) d = negb (rect_eval r d).
  Proof.
    intros LA LB r d. unfold rect_neg, pdnf_eval, rect_eval; simpl.
    rewrite (eval_neg A LA), (eval_neg B LB), (eval_top A LA), (eval_top B LB).
    destruct (eval (fst r) (fst d)), (eval (snd r) (snd d)); reflexivity.
  Qed.

  Lemma pdnf_neg_eval :
    EBA_Laws A -> EBA_Laws B ->
    forall L d, pdnf_eval (pdnf_neg L) d = negb (pdnf_eval L d).
  Proof.
    intros LA LB. induction L as [|r L IH]; intro d.
    - change (pdnf_neg []) with pdnf_top.
      unfold pdnf_top, pdnf_eval, rect_eval; simpl.
      rewrite (eval_top A LA), (eval_top B LB). reflexivity.
    - change (pdnf_neg (r :: L)) with (pdnf_conj (rect_neg r) (pdnf_neg L)).
      rewrite (pdnf_conj_eval LA LB).
      rewrite (rect_neg_eval LA LB), IH.
      (* pdnf_eval (r::L) d = rect_eval r d || pdnf_eval L d *)
      change (pdnf_eval (r :: L) d) with (rect_eval r d || pdnf_eval L d).
      destruct (rect_eval r d), (pdnf_eval L d); reflexivity.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  SAT / WIT soundness and completeness                                 *)
  (* --------------------------------------------------------------------- *)

  Lemma pdnf_sat_sound :
    EBA_Laws A -> EBA_Laws B ->
    forall L, pdnf_sat L = true -> exists d, pdnf_eval L d = true.
  Proof.
    intros LA LB L Hsat. unfold pdnf_sat in Hsat.
    apply existsb_exists in Hsat. destruct Hsat as [r [Hin Hr]].
    apply andb_true_iff in Hr. destruct Hr as [Hra Hrb].
    apply (sat_sound A LA) in Hra. destruct Hra as [da Hda].
    apply (sat_sound B LB) in Hrb. destruct Hrb as [db Hdb].
    exists (da, db). unfold pdnf_eval. apply existsb_exists.
    exists r. split; [exact Hin|]. unfold rect_eval; simpl.
    rewrite Hda, Hdb. reflexivity.
  Qed.

  Lemma pdnf_sat_complete :
    EBA_Laws A -> EBA_Laws B ->
    forall L d, pdnf_eval L d = true -> pdnf_sat L = true.
  Proof.
    intros LA LB L d Hev. unfold pdnf_eval in Hev.
    apply existsb_exists in Hev. destruct Hev as [r [Hin Hr]].
    unfold rect_eval in Hr. apply andb_true_iff in Hr. destruct Hr as [Hra Hrb].
    unfold pdnf_sat. apply existsb_exists. exists r. split; [exact Hin|].
    apply andb_true_iff. split.
    - apply (sat_complete A LA) with (d := fst d). exact Hra.
    - apply (sat_complete B LB) with (d := snd d). exact Hrb.
  Qed.

  Lemma pdnf_wit_sound :
    EBA_Laws A -> EBA_Laws B ->
    forall L d, pdnf_wit L = Some d -> pdnf_eval L d = true.
  Proof.
    intros LA LB L d Hwit. unfold pdnf_wit in Hwit.
    destruct (find (fun r => sat (fst r) && sat (snd r)) L) as [r|] eqn:Hfind;
      [|discriminate].
    apply find_some in Hfind. destruct Hfind as [Hin _].
    destruct (wit (fst r)) as [da|] eqn:Wa; [|discriminate].
    destruct (wit (snd r)) as [db|] eqn:Wb; [|discriminate].
    injection Hwit as <-.
    unfold pdnf_eval. apply existsb_exists. exists r. split; [exact Hin|].
    unfold rect_eval; simpl.
    rewrite (wit_sound A LA (fst r) da Wa), (wit_sound B LB (snd r) db Wb).
    reflexivity.
  Qed.

  Lemma pdnf_wit_total :
    EBA_Laws A -> EBA_Laws B ->
    forall L, pdnf_sat L = true -> exists d, pdnf_wit L = Some d.
  Proof.
    intros LA LB L Hsat. unfold pdnf_sat in Hsat.
    apply existsb_find_some in Hsat. destruct Hsat as [r [Hfind Hr]].
    apply andb_true_iff in Hr. destruct Hr as [Hra Hrb].
    apply (wit_total A LA) in Hra. destruct Hra as [da Hda].
    apply (wit_total B LB) in Hrb. destruct Hrb as [db Hdb].
    exists (da, db). unfold pdnf_wit. rewrite Hfind, Hda, Hdb. reflexivity.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  Closure: the product is an EBA                                       *)
  (* --------------------------------------------------------------------- *)

  Theorem product_eba_laws :
    EBA_Laws A -> EBA_Laws B -> EBA_Laws product_eba.
  Proof.
    intros LA LB. constructor.
    - (* eval_top *) intros [da db]. unfold product_eba; simpl.
      unfold pdnf_top, pdnf_eval, rect_eval; simpl.
      rewrite (eval_top A LA), (eval_top B LB). reflexivity.
    - (* eval_bot *) intros d. reflexivity.
    - (* eval_conj *) intros p q d. apply (pdnf_conj_eval LA LB).
    - (* eval_disj *) intros p q d. apply pdnf_disj_eval.
    - (* eval_neg *) intros p d. apply (pdnf_neg_eval LA LB).
    - (* sat_sound *) intros p. apply (pdnf_sat_sound LA LB).
    - (* sat_complete *) intros p d. apply (pdnf_sat_complete LA LB).
    - (* wit_sound *) intros p d. apply (pdnf_wit_sound LA LB).
    - (* wit_total *) intros p. apply (pdnf_wit_total LA LB).
  Qed.

End Product.

Print Assumptions product_eba_laws.
