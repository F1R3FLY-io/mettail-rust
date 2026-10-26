(*
 * RholangAstLowering: proof model for the AST-first rholang Proc/Name
 * lowerer in `rholang-runtime::rholang_ast`.
 *
 * Rust image:
 *   - rholang source is parsed by MeTTaIL/WPDA.
 *   - `lower_rholang_proc` maps the supported transport-pure process subset
 *     directly to normalized `rhoapi::Par`.
 *   - generated artifacts are AST values, never Rholang source text.
 *   - `PInputs` becomes one host RSpace receive; multiple input channels are
 *     one atomic join.
 *   - the body uses the same de Bruijn convention as f1r3node:
 *       formal i in an n-bind receive maps to bound index n - 1 - i.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Section RholangAstLowering.

  Definition Channel : Type := nat.
  Definition Value : Type := nat.

  Inductive Proc : Type :=
    | PZero : Proc
    | PDrop : Name -> Proc
    | PPar : Proc -> Proc -> Proc
    | POutput : Name -> Proc -> Proc
    | PInput1 : Name -> Proc -> Proc
    | PInput2 : Name -> Name -> Proc -> Proc
    | PString : Value -> Proc
    | PList : ProcList -> Proc
    | PMap : ProcPairList -> Proc
    | PBag : ProcBagList -> Proc
    | PBoundProc : nat -> Proc
  with Name : Type :=
    | NQuote : Proc -> Name
    | NFree : Channel -> Name
    | NBound : nat -> Name
    | NParen : Name -> Name
  with ProcList : Type :=
    | ProcNil : ProcList
    | ProcCons : Proc -> ProcList -> ProcList
  with ProcPairList : Type :=
    | ProcPairNil : ProcPairList
    | ProcPairCons : Proc -> Proc -> ProcPairList -> ProcPairList
  with ProcBagList : Type :=
    | ProcBagNil : ProcBagList
    | ProcBagCons : Proc -> nat -> ProcBagList -> ProcBagList.

  Scheme Proc_ind' := Induction for Proc Sort Prop
  with Name_ind' := Induction for Name Sort Prop
  with ProcList_ind' := Induction for ProcList Sort Prop
  with ProcPairList_ind' := Induction for ProcPairList Sort Prop
  with ProcBagList_ind' := Induction for ProcBagList Sort Prop.

  Combined Scheme proc_name_list_pair_ind
    from Proc_ind', Name_ind', ProcList_ind', ProcPairList_ind', ProcBagList_ind'.

  Inductive Ast : Type :=
    | ANil : Ast
    | AValue : Value -> Ast
    | AChan : Channel -> Ast
    | ABound : nat -> Ast
    | ASend : Ast -> Ast -> Ast
    | AReceive : list Ast -> Ast -> Ast
    | ANew : nat -> Ast -> Ast
    | AList : list Ast -> Ast
    | AMap : list (Ast * Ast) -> Ast
    | ABag : list (Ast * nat) -> Ast
    | APar : Ast -> Ast -> Ast.

  Inductive Artifact : Type :=
    | AstArtifact : Ast -> Artifact
    | SourceTextArtifact : list nat -> Artifact.

  Inductive LowerResult : Type :=
    | Lowered : Ast -> LowerResult
    | Rejected : LowerResult.

  Definition is_source_text_artifact (artifact : Artifact) : bool :=
    match artifact with
    | SourceTextArtifact _ => true
    | AstArtifact _ => false
    end.

  Definition bind_index (bind_count formal_index : nat) : nat :=
    bind_count - S formal_index.

  Definition lower_result_pair
      (key_result value_result : LowerResult) : option (Ast * Ast) :=
    match key_result, value_result with
    | Lowered key_ast, Lowered value_ast => Some (key_ast, value_ast)
    | _, _ => None
    end.

  Fixpoint lookup_ast (index : nat) (env : list Ast) : Ast :=
    match index, env with
    | 0, value :: _ => value
    | S index', _ :: rest => lookup_ast index' rest
    | _, [] => ANil
    end.

  Fixpoint subst_ast (env : list Ast) (ast : Ast) : Ast :=
    match ast with
    | ANil => ANil
    | AValue value => AValue value
    | AChan channel => AChan channel
    | ABound index => lookup_ast index env
    | ASend channel payload =>
        ASend (subst_ast env channel) (subst_ast env payload)
    | AReceive channels body =>
        AReceive (map (subst_ast env) channels) body
    | ANew count body => ANew count body
    | AList items => AList (map (subst_ast env) items)
    | AMap pairs =>
        AMap (map (fun '(key, value) => (subst_ast env key, subst_ast env value)) pairs)
    | ABag pairs =>
        ABag (map (fun '(item, count) => (subst_ast env item, count)) pairs)
    | APar lhs rhs => APar (subst_ast env lhs) (subst_ast env rhs)
    end.

  Fixpoint lower_proc (proc : Proc) : LowerResult :=
    match proc with
    | PZero => Lowered ANil
    | PDrop name => lower_name name
    | PPar lhs rhs =>
        match lower_proc lhs, lower_proc rhs with
        | Lowered lhs_ast, Lowered rhs_ast => Lowered (APar lhs_ast rhs_ast)
        | _, _ => Rejected
        end
    | POutput channel payload =>
        match lower_name channel, lower_proc payload with
        | Lowered channel_ast, Lowered payload_ast =>
            Lowered (ASend channel_ast payload_ast)
        | _, _ => Rejected
        end
    | PInput1 channel body =>
        match lower_name channel, lower_proc body with
        | Lowered channel_ast, Lowered body_ast =>
            Lowered (AReceive [channel_ast] body_ast)
        | _, _ => Rejected
        end
    | PInput2 lhs rhs body =>
        match lower_name lhs, lower_name rhs, lower_proc body with
        | Lowered lhs_ast, Lowered rhs_ast, Lowered body_ast =>
            Lowered (AReceive [lhs_ast; rhs_ast] body_ast)
        | _, _, _ => Rejected
        end
    | PString value => Lowered (AValue value)
    | PList items =>
        match lower_proc_list items with
        | Some asts => Lowered (AList asts)
        | None => Rejected
        end
    | PMap pairs =>
        match lower_proc_pairs pairs with
        | Some asts => Lowered (AMap asts)
        | None => Rejected
        end
    | PBag entries =>
        match lower_proc_bag entries with
        | Some asts => Lowered (ABag asts)
        | None => Rejected
        end
    | PBoundProc index => Lowered (ABound index)
    end
  with lower_name (name : Name) : LowerResult :=
    match name with
    | NQuote body => lower_proc body
    | NFree channel => Lowered (AChan channel)
    | NBound index => Lowered (ABound index)
    | NParen inner => lower_name inner
    end
  with lower_proc_list (items : ProcList) : option (list Ast) :=
    match items with
    | ProcNil => Some []
    | ProcCons item rest =>
        match lower_proc item, lower_proc_list rest with
        | Lowered item_ast, Some rest_ast => Some (item_ast :: rest_ast)
        | _, _ => None
        end
    end
  with lower_proc_pairs (pairs : ProcPairList) : option (list (Ast * Ast)) :=
    match pairs with
    | ProcPairNil => Some []
    | ProcPairCons key value rest =>
        match lower_result_pair (lower_proc key) (lower_proc value),
              lower_proc_pairs rest with
        | Some pair_ast, Some rest_ast => Some (pair_ast :: rest_ast)
        | _, _ => None
        end
    end
  with lower_proc_bag (entries : ProcBagList) : option (list (Ast * nat)) :=
    match entries with
    | ProcBagNil => Some []
    | ProcBagCons item count rest =>
        match lower_proc item, lower_proc_bag rest with
        | Lowered item_ast, Some rest_ast => Some ((item_ast, count) :: rest_ast)
        | _, _ => None
        end
    end.

  Definition lower_artifact (proc : Proc) : option Artifact :=
    match lower_proc proc with
    | Lowered ast => Some (AstArtifact ast)
    | Rejected => None
    end.

  Fixpoint append_proc_branches (procs : list Proc) : LowerResult :=
    match procs with
    | [] => Rejected
    | [proc] => lower_proc proc
    | proc :: rest =>
        match lower_proc proc, append_proc_branches rest with
        | Lowered branch_ast, Lowered rest_ast => Lowered (APar branch_ast rest_ast)
        | _, _ => Rejected
        end
    end.

  Inductive HostCommStep : Ast -> Ast -> Prop :=
    | Comm1 : forall channel payload body,
        HostCommStep
          (APar (AReceive [channel] body) (ASend channel payload))
          (subst_ast [payload] body)
    | Comm2 : forall lhs rhs payload_left payload_right body,
        HostCommStep
          (APar
             (AReceive [lhs; rhs] body)
             (APar (ASend lhs payload_left) (ASend rhs payload_right)))
          (subst_ast [payload_right; payload_left] body).

  Theorem accepted_rholang_lowering_is_ast_not_source_text :
    forall proc artifact,
      lower_artifact proc = Some artifact ->
      is_source_text_artifact artifact = false.
  Proof.
    intros proc artifact Hlower.
    unfold lower_artifact in Hlower.
    destruct (lower_proc proc) as [ast |] eqn:Hproc; inversion Hlower; reflexivity.
  Qed.

  Theorem append_two_proc_lowerings_preserves_both_branches :
    forall lhs rhs lhs_ast rhs_ast,
      lower_proc lhs = Lowered lhs_ast ->
      lower_proc rhs = Lowered rhs_ast ->
      append_proc_branches [lhs; rhs] = Lowered (APar lhs_ast rhs_ast).
  Proof.
    intros lhs rhs lhs_ast rhs_ast Hlhs Hrhs.
    simpl. rewrite Hlhs, Hrhs. reflexivity.
  Qed.

  Theorem quote_drop_lowering_preserves_body :
    forall proc ast,
      lower_proc proc = Lowered ast ->
      lower_proc (PDrop (NQuote proc)) = Lowered ast.
  Proof.
    intros proc ast Hlower.
    simpl. exact Hlower.
  Qed.

  Theorem list_literal_lowering_preserves_order :
    forall lhs rhs lhs_ast rhs_ast,
      lower_proc lhs = Lowered lhs_ast ->
      lower_proc rhs = Lowered rhs_ast ->
      lower_proc (PList (ProcCons lhs (ProcCons rhs ProcNil))) =
        Lowered (AList [lhs_ast; rhs_ast]).
  Proof.
    intros lhs rhs lhs_ast rhs_ast Hlhs Hrhs.
    simpl. rewrite Hlhs, Hrhs. reflexivity.
  Qed.

  Theorem map_literal_lowering_preserves_key_value_pairs :
    forall key value key_ast value_ast,
      lower_proc key = Lowered key_ast ->
      lower_proc value = Lowered value_ast ->
      lower_proc (PMap (ProcPairCons key value ProcPairNil)) =
        Lowered (AMap [(key_ast, value_ast)]).
  Proof.
    intros key value key_ast value_ast Hkey Hvalue.
    simpl. rewrite Hkey, Hvalue. reflexivity.
  Qed.

  Theorem bag_literal_lowering_preserves_multiplicity :
    forall item item_ast count,
      lower_proc item = Lowered item_ast ->
      lower_proc (PBag (ProcBagCons item count ProcBagNil)) =
        Lowered (ABag [(item_ast, count)]).
  Proof.
    intros item item_ast count Hitem.
    simpl. rewrite Hitem. reflexivity.
  Qed.

  Theorem one_input_comm_lowering_fires_payload :
    forall channel payload payload_ast,
      lower_proc payload = Lowered payload_ast ->
      HostCommStep
        (APar
          (match lower_proc (PInput1 (NFree channel) (PBoundProc 0)) with
           | Lowered ast => ast
           | Rejected => ANil
           end)
          (match lower_proc (POutput (NFree channel) payload) with
           | Lowered ast => ast
           | Rejected => ANil
           end))
        payload_ast.
  Proof.
    intros channel payload payload_ast Hpayload.
    simpl. rewrite Hpayload. constructor.
  Qed.

  Theorem two_formal_indices_match_runtime_push_order :
    bind_index 2 0 = 1 /\ bind_index 2 1 = 0.
  Proof. split; reflexivity. Qed.

  Theorem two_input_comm_lowering_preserves_syntactic_binder_order :
    forall lhs rhs payload_left payload_right left_ast right_ast,
      lower_proc payload_left = Lowered left_ast ->
      lower_proc payload_right = Lowered right_ast ->
      HostCommStep
        (APar
          (match
             lower_proc
                  (PInput2
                  (NFree lhs)
                  (NFree rhs)
                  (PPar (PBoundProc (bind_index 2 0))
                        (PBoundProc (bind_index 2 1))))
           with
           | Lowered ast => ast
           | Rejected => ANil
           end)
          (APar
            (match lower_proc (POutput (NFree lhs) payload_left) with
             | Lowered ast => ast
             | Rejected => ANil
             end)
            (match lower_proc (POutput (NFree rhs) payload_right) with
             | Lowered ast => ast
             | Rejected => ANil
             end)))
        (APar left_ast right_ast).
  Proof.
    intros lhs rhs payload_left payload_right left_ast right_ast Hleft Hright.
    simpl. rewrite Hleft, Hright. constructor.
  Qed.

  Fixpoint filter_adjust (bind_count : nat) (bits : list bool) : list bool :=
    match bind_count, bits with
    | 0, bits => bits
    | S count', [] => []
    | S count', _ :: rest => filter_adjust count' rest
    end.

  Theorem filter_adjust_removes_single_bound_bit :
    forall rest,
      filter_adjust 1 (true :: rest) = rest.
  Proof. intros rest. reflexivity. Qed.

  Theorem filter_adjust_removes_two_bound_bits :
    forall b0 b1 rest,
      filter_adjust 2 (b0 :: b1 :: rest) = rest.
  Proof. intros b0 b1 rest. reflexivity. Qed.

End RholangAstLowering.

Module AlternativeLowering.

Fixpoint select_keys (seen : list nat) (alternatives : list (nat * Proc)) : list Proc :=
  match alternatives with
  | [] => []
  | (key, body) :: rest =>
      if existsb (Nat.eqb key) seen then select_keys seen rest
      else body :: select_keys (key :: seen) rest
  end.

Fixpoint lower_selected (alternatives : list Proc) : option (list Ast) :=
  match alternatives with
  | [] => Some []
  | body :: rest =>
      match lower_proc body, lower_selected rest with
      | Lowered ast, Some asts => Some (ast :: asts)
      | _, _ => None
      end
  end.

Fixpoint keep_first (eqb : Ast -> Ast -> bool) (acc terms : list Ast) : list Ast :=
  match terms with
  | [] => rev acc
  | term :: rest =>
      if existsb (eqb term) acc then keep_first eqb acc rest
      else keep_first eqb (term :: acc) rest
  end.

Definition assemble (terms : list Ast) : LowerResult :=
  match terms with
  | [] => Rejected
  | first :: rest => Lowered (fold_left APar rest first)
  end.

Definition lower_proc_branches (eqb : Ast -> Ast -> bool)
    (alternatives : list (nat * Proc)) : LowerResult :=
  match lower_selected (select_keys [] alternatives) with
  | Some asts => assemble (keep_first eqb [] asts)
  | None => Rejected
  end.

Section ExactEquality.
Variable eqb : Ast -> Ast -> bool.
Hypothesis eqb_exact : forall a b, eqb a b = true <-> a = b.

Lemma exists_ast_exact : forall term acc,
  existsb (eqb term) acc = true <-> In term acc.
Proof.
  intros. rewrite existsb_exists. split.
  - intros [x [Hx E]]. apply eqb_exact in E. now subst x.
  - intros H. exists term. split; [exact H|]. apply eqb_exact. reflexivity.
Qed.

Theorem keep_first_membership : forall terms acc term,
  In term (keep_first eqb acc terms) <-> In term acc \/ In term terms.
Proof.
  induction terms as [|first rest IH]; intros; simpl.
  - rewrite <- in_rev. tauto.
  - destruct (existsb (eqb first) acc) eqn:E.
    + rewrite IH. apply exists_ast_exact in E. split.
      * tauto.
      * intros [H|[H|H]]; try tauto. subst term. tauto.
    + rewrite IH. simpl. tauto.
Qed.

Theorem keep_first_has_no_duplicates : forall terms acc,
  NoDup acc -> NoDup (keep_first eqb acc terms).
Proof.
  induction terms as [|first rest IH]; intros; simpl.
  - now apply NoDup_rev.
  - destruct (existsb (eqb first) acc) eqn:E; apply IH; [exact H|].
    constructor; [|exact H]. intros Hin. apply exists_ast_exact in Hin. congruence.
Qed.

Theorem deduplication_preserves_exact_program_membership : forall terms term,
  In term (keep_first eqb [] terms) <-> In term terms.
Proof. intros. rewrite keep_first_membership. simpl. tauto. Qed.

Theorem distinct_alternatives_are_preserved : forall left right left_ast right_ast,
  lower_proc left = Lowered left_ast -> lower_proc right = Lowered right_ast ->
  left_ast <> right_ast ->
  lower_proc_branches eqb [(0, left); (1, right)] = Lowered (APar left_ast right_ast).
Proof.
  intros. unfold lower_proc_branches. cbn [select_keys existsb Nat.eqb lower_selected].
  rewrite H. cbn [lower_selected orb]. rewrite H0. cbn [keep_first existsb].
  destruct (eqb right_ast left_ast) eqn:E.
  - apply eqb_exact in E. congruence.
  - reflexivity.
Qed.

Definition twin_alternatives :=
  [(0, PDrop (NQuote (POutput (NFree 1) (PString 7))));
   (1, PDrop (NParen (NQuote (POutput (NFree 1) (PString 7)))))].

Theorem old_lowering_emits_twins :
  lower_selected (select_keys [] twin_alternatives) =
    Some [ASend (AChan 1) (AValue 7); ASend (AChan 1) (AValue 7)].
Proof. reflexivity. Qed.

Theorem corrected_lowering_emits_one_twin :
  lower_proc_branches eqb twin_alternatives = Lowered (ASend (AChan 1) (AValue 7)).
Proof.
  unfold lower_proc_branches. rewrite old_lowering_emits_twins.
  cbn [keep_first existsb].
  assert (eqb (ASend (AChan 1) (AValue 7)) (ASend (AChan 1) (AValue 7)) = true)
    as E by (apply eqb_exact; reflexivity).
  now rewrite E.
Qed.

Theorem parallel_duplicates_inside_one_alternative_survive : forall body ast,
  lower_proc body = Lowered ast ->
  lower_proc_branches eqb [(0, PPar body body)] = Lowered (APar ast ast).
Proof.
  intros. unfold lower_proc_branches.
  cbn [select_keys existsb lower_selected lower_proc]. rewrite H. reflexivity.
Qed.

Theorem failed_lowering_is_rejected : forall alternatives,
  lower_selected (select_keys [] alternatives) = None ->
  lower_proc_branches eqb alternatives = Rejected.
Proof. intros. unfold lower_proc_branches. now rewrite H. Qed.

End ExactEquality.

Section CanonicalComparison.
Variable canonical : Ast -> Ast.
Variable eqb : Ast -> Ast -> bool.
Hypothesis eqb_exact : forall a b, eqb a b = true <-> a = b.

Definition same_program (a b : Ast) := eqb (canonical a) (canonical b).

Lemma exists_canonical : forall first acc,
  existsb (eqb (canonical first)) (map canonical acc) =
  existsb (same_program first) acc.
Proof.
  intros first acc. induction acc; simpl; [reflexivity|].
  now rewrite IHacc.
Qed.

Theorem canonical_selection_commutes : forall terms acc,
  map canonical (keep_first same_program acc terms) =
  keep_first eqb (map canonical acc) (map canonical terms).
Proof.
  induction terms as [|first rest IH]; intros acc; simpl.
  - apply map_rev.
  - rewrite exists_canonical.
    destruct (existsb (same_program first) acc).
    + apply IH.
    + apply IH.
Qed.

Theorem canonical_program_membership_is_preserved : forall terms program,
  In program (map canonical (keep_first same_program [] terms)) <->
  In program (map canonical terms).
Proof.
  intros. rewrite canonical_selection_commutes.
  apply deduplication_preserves_exact_program_membership. exact eqb_exact.
Qed.

Theorem canonical_programs_have_no_duplicates : forall terms,
  NoDup (map canonical (keep_first same_program [] terms)).
Proof.
  intros. rewrite canonical_selection_commutes.
  apply keep_first_has_no_duplicates; [exact eqb_exact|constructor].
Qed.

Theorem canonical_twins_retain_the_first_original : forall left right,
  canonical left = canonical right ->
  keep_first same_program [] [left; right] = [left].
Proof.
  intros. simpl. unfold same_program.
  assert (eqb (canonical right) (canonical left) = true) as E.
  { apply eqb_exact. symmetry. exact H. }
  now rewrite E.
Qed.

Theorem canonical_comparison_preserves_one_program : forall program,
  keep_first same_program [] [program] = [program].
Proof. reflexivity. Qed.

End CanonicalComparison.
End AlternativeLowering.

Print Assumptions AlternativeLowering.exists_ast_exact.
Print Assumptions AlternativeLowering.keep_first_membership.
Print Assumptions AlternativeLowering.keep_first_has_no_duplicates.
Print Assumptions AlternativeLowering.deduplication_preserves_exact_program_membership.
Print Assumptions AlternativeLowering.distinct_alternatives_are_preserved.
Print Assumptions AlternativeLowering.old_lowering_emits_twins.
Print Assumptions AlternativeLowering.corrected_lowering_emits_one_twin.
Print Assumptions AlternativeLowering.parallel_duplicates_inside_one_alternative_survive.
Print Assumptions AlternativeLowering.failed_lowering_is_rejected.

Print Assumptions AlternativeLowering.canonical_selection_commutes.
Print Assumptions AlternativeLowering.canonical_program_membership_is_preserved.
Print Assumptions AlternativeLowering.canonical_programs_have_no_duplicates.
Print Assumptions AlternativeLowering.canonical_twins_retain_the_first_original.
Print Assumptions AlternativeLowering.canonical_comparison_preserves_one_program.

Print Assumptions AlternativeLowering.exists_canonical.
