(*
 * SumAlgebraClosure: the effective Boolean algebras are closed under the tagged
 * union (coproduct). Given EBAs A and B, the sum EBA over domain `Dom A + Dom B`
 * has predicates given by the recursive `SumPred` syntax (True/False/InL/InR/
 * TagL/TagR + And/Or/Not), evaluated by case on the variant tag. This is the
 * binary core of the Rust `SumAlgebra<A>` / `SumPred<P>` (prattail/src/
 * product_nary.rs:270): the Rust N-ary homogeneous tagged union iterates this
 * binary coproduct, exactly as `NaryProductAlgebra` iterates the binary product.
 *
 * SAT and WIT follow the Rust `project`-per-tag strategy: a sum predicate is
 * projected onto each variant (`project_L`/`project_R`, mirroring
 * SumAlgebra::project), and is satisfiable iff some projection is. The crux is
 * `project_L_correct`/`project_R_correct` — projection commutes with evaluation
 * on the corresponding injection — which makes SAT/WIT soundness and
 * completeness fall out of the factor algebras' own laws.
 *
 * Main result: `sum_eba_laws : EBA_Laws A -> EBA_Laws B -> EBA_Laws sum_eba`.
 *
 * Spec-to-Code Traceability:
 *   Coq                       | Rust (prattail/src/product_nary.rs)
 *   --------------------------|--------------------------------------------
 *   SumPred / sp_eval         | SumPred<P> / SumAlgebra::evaluate
 *   project_L / project_R     | SumAlgebra::project (per-tag fold)
 *   sp_sat (|| over projs)    | SumAlgebra::is_satisfiable (any over tags)
 *   sp_wit (first witnessing) | SumAlgebra::witness (first tag with a witness)
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From SymbolicAlgebra Require Import EffectiveBooleanAlgebra.

Section Sum.
  Variables A B : EBA.

  (* The recursive sum-predicate syntax (binary core of SumPred<P>). *)
  Inductive SumPred : Type :=
  | SPTrue  : SumPred
  | SPFalse : SumPred
  | SPInL   : Pred A -> SumPred          (* InVariant 0 with payload guard *)
  | SPInR   : Pred B -> SumPred          (* InVariant 1 with payload guard *)
  | SPTagL  : SumPred                     (* TagIs 0 *)
  | SPTagR  : SumPred                     (* TagIs 1 *)
  | SPAnd   : SumPred -> SumPred -> SumPred
  | SPOr    : SumPred -> SumPred -> SumPred
  | SPNot   : SumPred -> SumPred.

  Definition SumDom : Type := (Dom A + Dom B)%type.

  Fixpoint sp_eval (p : SumPred) (d : SumDom) : bool :=
    match p with
    | SPTrue  => true
    | SPFalse => false
    | SPInL pa => match d with inl da => eval pa da | inr _ => false end
    | SPInR pb => match d with inr db => eval pb db | inl _ => false end
    | SPTagL => match d with inl _ => true  | inr _ => false end
    | SPTagR => match d with inl _ => false | inr _ => true  end
    | SPAnd x y => sp_eval x d && sp_eval y d
    | SPOr  x y => sp_eval x d || sp_eval y d
    | SPNot x   => negb (sp_eval x d)
    end.

  (* Projection onto the left variant: an inner predicate for A. *)
  Fixpoint project_L (p : SumPred) : Pred A :=
    match p with
    | SPTrue  => top
    | SPFalse => bot
    | SPInL pa => pa
    | SPInR _  => bot
    | SPTagL => top
    | SPTagR => bot
    | SPAnd x y => conj (project_L x) (project_L y)
    | SPOr  x y => disj (project_L x) (project_L y)
    | SPNot x   => neg  (project_L x)
    end.

  Fixpoint project_R (p : SumPred) : Pred B :=
    match p with
    | SPTrue  => top
    | SPFalse => bot
    | SPInL _  => bot
    | SPInR pb => pb
    | SPTagL => bot
    | SPTagR => top
    | SPAnd x y => conj (project_R x) (project_R y)
    | SPOr  x y => disj (project_R x) (project_R y)
    | SPNot x   => neg  (project_R x)
    end.

  Definition sp_sat (p : SumPred) : bool := sat (project_L p) || sat (project_R p).

  Definition sp_wit (p : SumPred) : option SumDom :=
    match wit (project_L p) with
    | Some da => Some (inl da)
    | None => match wit (project_R p) with
              | Some db => Some (inr db)
              | None => None
              end
    end.

  Definition sum_eba : EBA := {|
    Dom  := SumDom;
    Pred := SumPred;
    top  := SPTrue;
    bot  := SPFalse;
    conj := SPAnd;
    disj := SPOr;
    neg  := SPNot;
    eval := sp_eval;
    sat  := sp_sat;
    wit  := sp_wit;
  |}.

  (* --------------------------------------------------------------------- *)
  (*  Projection commutes with evaluation on the matching injection        *)
  (* --------------------------------------------------------------------- *)

  Lemma project_L_correct :
    EBA_Laws A ->
    forall p da, sp_eval p (inl da) = eval (project_L p) da.
  Proof.
    intros LA. induction p; intro da; simpl.
    - rewrite (eval_top A LA); reflexivity.
    - rewrite (eval_bot A LA); reflexivity.
    - reflexivity.
    - rewrite (eval_bot A LA); reflexivity.
    - rewrite (eval_top A LA); reflexivity.
    - rewrite (eval_bot A LA); reflexivity.
    - rewrite (eval_conj A LA), IHp1, IHp2; reflexivity.
    - rewrite (eval_disj A LA), IHp1, IHp2; reflexivity.
    - rewrite (eval_neg A LA), IHp; reflexivity.
  Qed.

  Lemma project_R_correct :
    EBA_Laws B ->
    forall p db, sp_eval p (inr db) = eval (project_R p) db.
  Proof.
    intros LB. induction p; intro db; simpl.
    - rewrite (eval_top B LB); reflexivity.
    - rewrite (eval_bot B LB); reflexivity.
    - rewrite (eval_bot B LB); reflexivity.
    - reflexivity.
    - rewrite (eval_bot B LB); reflexivity.
    - rewrite (eval_top B LB); reflexivity.
    - rewrite (eval_conj B LB), IHp1, IHp2; reflexivity.
    - rewrite (eval_disj B LB), IHp1, IHp2; reflexivity.
    - rewrite (eval_neg B LB), IHp; reflexivity.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  SAT / WIT soundness and completeness                                 *)
  (* --------------------------------------------------------------------- *)

  Lemma sp_sat_sound :
    EBA_Laws A -> EBA_Laws B ->
    forall p, sp_sat p = true -> exists d, sp_eval p d = true.
  Proof.
    intros LA LB p Hsat. unfold sp_sat in Hsat.
    apply orb_true_iff in Hsat. destruct Hsat as [HL | HR].
    - apply (sat_sound A LA) in HL. destruct HL as [da Hda].
      exists (inl da). rewrite (project_L_correct LA). exact Hda.
    - apply (sat_sound B LB) in HR. destruct HR as [db Hdb].
      exists (inr db). rewrite (project_R_correct LB). exact Hdb.
  Qed.

  Lemma sp_sat_complete :
    EBA_Laws A -> EBA_Laws B ->
    forall p d, sp_eval p d = true -> sp_sat p = true.
  Proof.
    intros LA LB p d Hev. unfold sp_sat. apply orb_true_iff.
    destruct d as [da | db].
    - left. apply (sat_complete A LA) with (d := da).
      rewrite <- (project_L_correct LA). exact Hev.
    - right. apply (sat_complete B LB) with (d := db).
      rewrite <- (project_R_correct LB). exact Hev.
  Qed.

  Lemma sp_wit_sound :
    EBA_Laws A -> EBA_Laws B ->
    forall p d, sp_wit p = Some d -> sp_eval p d = true.
  Proof.
    intros LA LB p d Hwit. unfold sp_wit in Hwit.
    destruct (wit (project_L p)) as [da|] eqn:WL.
    - injection Hwit as <-. rewrite (project_L_correct LA).
      apply (wit_sound A LA). exact WL.
    - destruct (wit (project_R p)) as [db|] eqn:WR; [|discriminate].
      injection Hwit as <-. rewrite (project_R_correct LB).
      apply (wit_sound B LB). exact WR.
  Qed.

  Lemma sp_wit_total :
    EBA_Laws A -> EBA_Laws B ->
    forall p, sp_sat p = true -> exists d, sp_wit p = Some d.
  Proof.
    intros LA LB p Hsat. unfold sp_sat in Hsat. unfold sp_wit.
    destruct (sat (project_L p)) eqn:SL.
    - apply (wit_total A LA) in SL. destruct SL as [da Hda].
      rewrite Hda. exists (inl da). reflexivity.
    - simpl in Hsat.
      rewrite (wit_none_of_unsat A LA (project_L p) SL).
      apply (wit_total B LB) in Hsat. destruct Hsat as [db Hdb].
      rewrite Hdb. exists (inr db). reflexivity.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  Closure: the sum is an EBA                                            *)
  (* --------------------------------------------------------------------- *)

  Theorem sum_eba_laws :
    EBA_Laws A -> EBA_Laws B -> EBA_Laws sum_eba.
  Proof.
    intros LA LB. constructor.
    - (* eval_top *) intros d. reflexivity.
    - (* eval_bot *) intros d. reflexivity.
    - (* eval_conj *) intros p q d. reflexivity.
    - (* eval_disj *) intros p q d. reflexivity.
    - (* eval_neg *) intros p d. reflexivity.
    - (* sat_sound *) intros p. apply (sp_sat_sound LA LB).
    - (* sat_complete *) intros p d. apply (sp_sat_complete LA LB).
    - (* wit_sound *) intros p d. apply (sp_wit_sound LA LB).
    - (* wit_total *) intros p. apply (sp_wit_total LA LB).
  Qed.

End Sum.

Print Assumptions sum_eba_laws.
