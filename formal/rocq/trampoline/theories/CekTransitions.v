(*
 * CekTransitions: Formal transition rules for PraTTaIL's CEK-based
 *   trampolined parser.
 *
 * Defines the abstract small-step operational semantics of the parser:
 *   - Configuration type (phase, locals, continuation stack)
 *   - Frame type (defunctionalized continuation variants)
 *   - 10 transition rules (Definition 3 of cek-machine.md)
 *   - Abstraction function alpha: CEK -> WPDS configuration
 *   - Structural lemmas on configurations and frames
 *
 * The 10 transition rules model the parser's 'drive/'infix/'unwind loop
 * structure in trampoline.rs. Each rule is a step in the small-step
 * semantics that either consumes input, manipulates the continuation
 * stack, or produces a result.
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition          | Rust / Generated Code               | Location
 *   -------------------------|--------------------------------------|--------------------------
 *   token                    | Token enum variants                  | generated lexer
 *   value                    | Cat AST node                         | generated AST
 *   frame                    | Frame_Cat enum                       | trampoline.rs:2661-2834
 *   phase                    | Drive/Prefix/Infix/Unwind phases     | trampoline.rs ('drive, 'infix)
 *   config                   | (phase, captures, Vec<Frame_Cat>)    | trampoline.rs
 *   cek_step                 | Transition rules 1-10                | cek-machine.md Definition 3
 *   wpds_symbol              | StackSymbol { cat, rule, pos }       | wpds.rs:62-69
 *   alpha                    | Abstraction function alpha            | cek-machine.md Section 3
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

(* ===================================================================== *)
(*  Section 1: Token and Value Types                                       *)
(* ===================================================================== *)

Section CekModel.

  Variable token : Type.
  Variable value : Type.
  Variable category : Type.

  Definition bp := nat.

  (* ================================================================= *)
  (*  Section 2: Token Stream                                            *)
  (* ================================================================= *)

  (* We model token streams as plain lists. The head is the current
     token, and advancing is tail. This avoids cursor/record issues. *)
  Definition token_stream := list token.

  Definition ts_current (ts : token_stream) : option token :=
    match ts with
    | [] => None
    | t :: _ => Some t
    end.

  Definition ts_advance (ts : token_stream) : token_stream :=
    match ts with
    | [] => []
    | _ :: rest => rest
    end.

  Definition ts_length (ts : token_stream) : nat := length ts.

  Lemma ts_advance_length : forall t ts,
    ts_length (ts_advance (t :: ts)) < ts_length (t :: ts).
  Proof.
    intros t ts. unfold ts_advance, ts_length. simpl. lia.
  Qed.

  (* ================================================================= *)
  (*  Section 3: Frame Type                                              *)
  (* ================================================================= *)

  (* Frame tags distinguish continuation types.
     In the implementation, each tag corresponds to a Frame_Cat variant. *)
  Inductive frame_tag : Type :=
    | FT_InfixRHS
    | FT_GroupClose
    | FT_UnaryPrefix
    | FT_RdSegment
    | FT_CollectionElem
    | FT_MixfixStep.

  (* A frame carries a tag, saved binding power, and captured values. *)
  Record frame := mkFrame {
    fr_tag : frame_tag;
    fr_saved_bp : bp;
    fr_captures : list value;
  }.

  Definition kont := list frame.

  (* ================================================================= *)
  (*  Section 4: Phase                                                   *)
  (* ================================================================= *)

  (* The parser's phase determines which transition rules apply. *)
  Inductive phase : Type :=
    | Drive (ph_cat : category) (ph_bp : bp)
    | Prefix (ph_cat : category) (ph_tok : token) (ph_bp : bp)
    | Infix (ph_cat : category) (ph_lhs : value) (ph_bp : bp)
    | Unwind (ph_cat : category) (ph_val : value)
    | Accept (ph_val : value)
    | Error.

  (* ================================================================= *)
  (*  Section 5: Transition Predicates                                   *)
  (* ================================================================= *)

  (* These abstract over the parser's grammar-driven decisions. *)
  Variable is_prefix_with_nt : category -> token -> Prop.
  Variable is_prefix_leaf : category -> token -> Prop.
  Variable is_tail_prefix : category -> token -> Prop.
  Variable is_infix_op : category -> token -> Prop.
  Variable is_postfix_op : category -> token -> Prop.
  Variable infix_lbp : category -> token -> bp.
  Variable infix_rbp : category -> token -> bp.
  Variable prefix_nt_bp : category -> token -> bp.
  Variable tail_prefix_bp : category -> token -> bp.
  Variable make_prefix_frame : category -> token -> bp -> frame.
  Variable make_prefix_value : category -> token -> value.
  Variable make_postfix_value : category -> token -> value -> value.
  Variable unwind_frame : frame -> value -> value.

  (* ================================================================= *)
  (*  Section 6: Transition Rules (10 rules)                             *)
  (* ================================================================= *)

  (* The 10 transition rules define the small-step operational semantics.
     We define the step relation on 4-tuples: (phase, stream, kont, phase', stream', kont').
     Using explicit arguments avoids issues with record/tuple inversion. *)

  Inductive cek_step :
    phase -> token_stream -> kont ->
    phase -> token_stream -> kont -> Prop :=

    (* Rule 1: DRIVE — read token, transition to Prefix *)
    | TR_Drive : forall cat bp0 ts tok K,
        ts_current ts = Some tok ->
        cek_step (Drive cat bp0) ts K
                 (Prefix cat tok bp0) (ts_advance ts) K

    (* Rule 2: PREFIX-NT — push frame, re-enter Drive *)
    | TR_Prefix_NT : forall cat tok bp0 ts K,
        is_prefix_with_nt cat tok ->
        cek_step (Prefix cat tok bp0) ts K
                 (Drive cat (prefix_nt_bp cat tok)) ts
                 (make_prefix_frame cat tok bp0 :: K)

    (* Rule 3: PREFIX-LEAF — produce value, enter Infix *)
    | TR_Prefix_Leaf : forall cat tok bp0 ts K,
        is_prefix_leaf cat tok ->
        cek_step (Prefix cat tok bp0) ts K
                 (Infix cat (make_prefix_value cat tok) bp0) ts K

    (* Rule 4: PREFIX-TAIL — tail-call optimization, no frame *)
    | TR_Prefix_Tail : forall cat tok bp0 ts K,
        is_tail_prefix cat tok ->
        cek_step (Prefix cat tok bp0) ts K
                 (Drive cat (tail_prefix_bp cat tok)) ts K

    (* Rule 5: INFIX — push InfixRHS, re-enter Drive for RHS *)
    | TR_Infix : forall cat lhs bp0 ts tok K,
        ts_current ts = Some tok ->
        is_infix_op cat tok ->
        infix_lbp cat tok >= bp0 ->
        cek_step (Infix cat lhs bp0) ts K
                 (Drive cat (infix_rbp cat tok)) (ts_advance ts)
                 (mkFrame FT_InfixRHS bp0 [lhs] :: K)

    (* Rule 6: POSTFIX — apply postfix op, stay in Infix *)
    | TR_Postfix : forall cat lhs bp0 ts tok K,
        ts_current ts = Some tok ->
        is_postfix_op cat tok ->
        cek_step (Infix cat lhs bp0) ts K
                 (Infix cat (make_postfix_value cat tok lhs) bp0)
                 (ts_advance ts) K

    (* Rule 7: UNWIND-INFIX — pop InfixRHS, enter Infix *)
    | TR_Unwind_Infix : forall cat rhs ts saved_bp captures K,
        cek_step (Unwind cat rhs) ts
                 (mkFrame FT_InfixRHS saved_bp captures :: K)
                 (Infix cat
                   (unwind_frame (mkFrame FT_InfixRHS saved_bp captures) rhs)
                   saved_bp) ts K

    (* Rule 8: UNWIND-PREFIX — pop UnaryPrefix, enter Infix *)
    | TR_Unwind_Prefix : forall cat v0 ts saved_bp captures K,
        cek_step (Unwind cat v0) ts
                 (mkFrame FT_UnaryPrefix saved_bp captures :: K)
                 (Infix cat
                   (unwind_frame (mkFrame FT_UnaryPrefix saved_bp captures) v0)
                   saved_bp) ts K

    (* Rule 9: UNWIND-RD — pop RD/Group/Collection/Mixfix frame *)
    | TR_Unwind_RD : forall cat v0 ts tag saved_bp captures K,
        tag = FT_RdSegment \/ tag = FT_GroupClose \/
        tag = FT_CollectionElem \/ tag = FT_MixfixStep ->
        cek_step (Unwind cat v0) ts
                 (mkFrame tag saved_bp captures :: K)
                 (Infix cat
                   (unwind_frame (mkFrame tag saved_bp captures) v0)
                   saved_bp) ts K

    (* Rule 10: UNWIND-EMPTY — stack empty, accept *)
    | TR_Unwind_Empty : forall cat v ts,
        cek_step (Unwind cat v) ts []
                 (Accept v) ts [].

  (* ================================================================= *)
  (*  Section 7: Multi-step Reachability                                 *)
  (* ================================================================= *)

  Inductive cek_reachable :
    phase -> token_stream -> kont ->
    phase -> token_stream -> kont -> Prop :=
    | cek_reach_refl : forall p ts K,
        cek_reachable p ts K p ts K
    | cek_reach_step : forall p1 ts1 K1 p2 ts2 K2 p3 ts3 K3,
        cek_step p1 ts1 K1 p2 ts2 K2 ->
        cek_reachable p2 ts2 K2 p3 ts3 K3 ->
        cek_reachable p1 ts1 K1 p3 ts3 K3.

  Lemma cek_reachable_one : forall p1 ts1 K1 p2 ts2 K2,
    cek_step p1 ts1 K1 p2 ts2 K2 ->
    cek_reachable p1 ts1 K1 p2 ts2 K2.
  Proof.
    intros p1 ts1 K1 p2 ts2 K2 Hstep.
    apply cek_reach_step with p2 ts2 K2.
    - exact Hstep.
    - apply cek_reach_refl.
  Qed.

  Lemma cek_reachable_trans :
    forall p1 ts1 K1 p2 ts2 K2 p3 ts3 K3,
      cek_reachable p1 ts1 K1 p2 ts2 K2 ->
      cek_reachable p2 ts2 K2 p3 ts3 K3 ->
      cek_reachable p1 ts1 K1 p3 ts3 K3.
  Proof.
    intros p1 ts1 K1 p2 ts2 K2 p3 ts3 K3 H12 H23.
    induction H12 as [p ts K | a1 a2 a3 b1 b2 b3 c1 c2 c3 Hstep Hbc IH].
    - exact H23.
    - apply cek_reach_step with b1 b2 b3.
      + exact Hstep.
      + apply IH. exact H23.
  Qed.

  (* ================================================================= *)
  (*  Section 8: Structural Lemmas                                       *)
  (* ================================================================= *)

  (* Accept is a final state: no transitions from Accept. *)
  Lemma accept_is_final : forall v ts K p' ts' K',
    ~cek_step (Accept v) ts K p' ts' K'.
  Proof.
    intros v ts K p' ts' K' Hstep.
    inversion Hstep.
  Qed.

  (* Error is a final state. *)
  Lemma error_is_final : forall ts K p' ts' K',
    ~cek_step Error ts K p' ts' K'.
  Proof.
    intros ts K p' ts' K' Hstep.
    inversion Hstep.
  Qed.

  (* Unwind with empty stack always produces Accept. *)
  Lemma unwind_empty_accepts : forall cat v ts p' ts' K',
    cek_step (Unwind cat v) ts [] p' ts' K' ->
    p' = Accept v /\ ts' = ts /\ K' = [].
  Proof.
    intros cat v ts p' ts' K' Hstep.
    inversion Hstep; subst.
    - (* TR_Unwind_Infix: K = mkFrame ... :: K0, but K = [] *)
      discriminate.
    - (* TR_Unwind_Prefix: K = mkFrame ... :: K0, but K = [] *)
      discriminate.
    - (* TR_Unwind_RD: K = mkFrame ... :: K0, but K = [] *)
      discriminate.
    - (* TR_Unwind_Empty *)
      split; [reflexivity | split; reflexivity].
  Qed.

  (* Unwind rules do not consume tokens. *)
  Lemma unwind_preserves_stream : forall cat v ts K p' ts' K',
    cek_step (Unwind cat v) ts K p' ts' K' ->
    ts' = ts.
  Proof.
    intros cat v ts K p' ts' K' Hstep.
    inversion Hstep; subst; reflexivity.
  Qed.

  (* Drive requires a nonempty stream. *)
  Lemma drive_needs_token : forall cat bp0 ts K p' ts' K',
    cek_step (Drive cat bp0) ts K p' ts' K' ->
    ts <> [].
  Proof.
    intros cat bp0 ts K p' ts' K' Hstep Hempty.
    inversion Hstep; subst.
    rewrite Hempty in *. simpl in *. discriminate.
  Qed.

  (* Drive produces Prefix. *)
  Lemma drive_produces_prefix : forall cat bp0 ts K p' ts' K',
    cek_step (Drive cat bp0) ts K p' ts' K' ->
    exists tok, p' = Prefix cat tok bp0 /\ K' = K.
  Proof.
    intros cat bp0 ts K p' ts' K' Hstep.
    inversion Hstep; subst.
    exists tok. split; reflexivity.
  Qed.

  (* Prefix preserves or increases stack depth. *)
  Lemma prefix_stack_change : forall cat tok bp0 ts K p' ts' K',
    cek_step (Prefix cat tok bp0) ts K p' ts' K' ->
    K' = K \/ exists fr, K' = fr :: K.
  Proof.
    intros cat tok bp0 ts K p' ts' K' Hstep.
    inversion Hstep; subst.
    - (* TR_Prefix_NT: pushes a frame *)
      right. exists (make_prefix_frame cat tok bp0). reflexivity.
    - (* TR_Prefix_Leaf: preserves stack *)
      left. reflexivity.
    - (* TR_Prefix_Tail: preserves stack *)
      left. reflexivity.
  Qed.

  (* Infix either pushes a frame (infix op) or preserves it (postfix). *)
  Lemma infix_stack_change : forall cat lhs bp0 ts K p' ts' K',
    cek_step (Infix cat lhs bp0) ts K p' ts' K' ->
    K' = K \/ exists fr, K' = fr :: K.
  Proof.
    intros cat lhs bp0 ts K p' ts' K' Hstep.
    inversion Hstep; subst.
    - (* TR_Infix: pushes InfixRHS frame *)
      right. exists (mkFrame FT_InfixRHS bp0 [lhs]). reflexivity.
    - (* TR_Postfix: preserves stack *)
      left. reflexivity.
  Qed.

  (* ================================================================= *)
  (*  Section 9: WPDS Abstraction Function                               *)
  (* ================================================================= *)

  Variable wpds_symbol : Type.
  Variable frame_to_symbol : frame -> wpds_symbol.
  Variable phase_to_symbol : phase -> wpds_symbol.

  Definition alpha (p : phase) (K : kont) : list wpds_symbol :=
    phase_to_symbol p :: map frame_to_symbol K.

  Lemma alpha_length : forall p K,
    length (alpha p K) = S (length K).
  Proof.
    intros p K.
    unfold alpha. simpl.
    rewrite map_length. reflexivity.
  Qed.

  (* ================================================================= *)
  (*  Section 10: Stack Depth                                            *)
  (* ================================================================= *)

  (* Each transition changes stack depth by at most 1. *)
  Lemma step_depth_bound : forall p1 ts1 K1 p2 ts2 K2,
    cek_step p1 ts1 K1 p2 ts2 K2 ->
    length K2 <= S (length K1) /\
    length K1 <= S (length K2).
  Proof.
    intros p1 ts1 K1 p2 ts2 K2 Hstep.
    inversion Hstep; subst; simpl; lia.
  Qed.

  (* ================================================================= *)
  (*  Section 11: Measure Function                                       *)
  (* ================================================================= *)

  (* Convergence measure: |remaining_tokens| + |kont|. *)
  Definition cek_measure (ts : token_stream) (K : kont) : nat :=
    ts_length ts + length K.

End CekModel.

(* ===================================================================== *)
(*  Verification: key types and lemmas are accessible                     *)
(* ===================================================================== *)

Check cek_step.
Check cek_reachable.
Check alpha.
Check accept_is_final.
Check error_is_final.
Check unwind_empty_accepts.
Check step_depth_bound.
Check drive_produces_prefix.
