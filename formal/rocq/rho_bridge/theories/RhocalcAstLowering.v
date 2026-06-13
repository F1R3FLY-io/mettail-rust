(*
 * RhocalcAstLowering: proof model for the AST-first rhocalc Proc/Name
 * lowerer in `mettail-rho-runtime::rhocalc_ast`.
 *
 * Rust image:
 *   - rhocalc source is parsed by MeTTaIL/WPDA.
 *   - `lower_rhocalc_proc` maps the supported transport-pure process subset
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

Section RhocalcAstLowering.

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
    | PBag : ProcList -> Proc
    | PBoundProc : nat -> Proc
  with Name : Type :=
    | NQuote : Proc -> Name
    | NFree : Channel -> Name
    | NBound : nat -> Name
  with ProcList : Type :=
    | ProcNil : ProcList
    | ProcCons : Proc -> ProcList -> ProcList
  with ProcPairList : Type :=
    | ProcPairNil : ProcPairList
    | ProcPairCons : Proc -> Proc -> ProcPairList -> ProcPairList.

  Scheme Proc_ind' := Induction for Proc Sort Prop
  with Name_ind' := Induction for Name Sort Prop
  with ProcList_ind' := Induction for ProcList Sort Prop
  with ProcPairList_ind' := Induction for ProcPairList Sort Prop.

  Combined Scheme proc_name_list_pair_ind
    from Proc_ind', Name_ind', ProcList_ind', ProcPairList_ind'.

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
    | APar lhs rhs => APar (subst_ast env lhs) (subst_ast env rhs)
    end.

  Fixpoint lower_proc (proc : Proc) : LowerResult :=
    match proc with
    | PZero => Lowered ANil
    | PDrop (NQuote body) => lower_proc body
    | PDrop (NBound index) => Lowered (ABound index)
    | PDrop (NFree channel) => Lowered (AChan channel)
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
    | PBag _ => Rejected
    | PBoundProc index => Lowered (ABound index)
    end
  with lower_name (name : Name) : LowerResult :=
    match name with
    | NQuote body => lower_proc body
    | NFree channel => Lowered (AChan channel)
    | NBound index => Lowered (ABound index)
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
    end.

  Definition lower_artifact (proc : Proc) : option Artifact :=
    match lower_proc proc with
    | Lowered ast => Some (AstArtifact ast)
    | Rejected => None
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

  Theorem accepted_rhocalc_lowering_is_ast_not_source_text :
    forall proc artifact,
      lower_artifact proc = Some artifact ->
      is_source_text_artifact artifact = false.
  Proof.
    intros proc artifact Hlower.
    unfold lower_artifact in Hlower.
    destruct (lower_proc proc) as [ast |] eqn:Hproc; inversion Hlower; reflexivity.
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

  Theorem bag_literal_lowering_is_fail_closed :
    forall items,
      lower_proc (PBag items) = Rejected.
  Proof. intros items. reflexivity. Qed.

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

End RhocalcAstLowering.
