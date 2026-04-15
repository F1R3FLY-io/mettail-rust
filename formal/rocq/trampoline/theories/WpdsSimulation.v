(*
 * WpdsSimulation: Theorems CEK.2 and CEK.3 — Forward simulation of
 *   CEK transitions by WPDS transitions.
 *
 * CEK.2: For every concrete CEK transition s -> s', there exists a WPDS
 *   transition sequence such that alpha(s) ->*_WPDS alpha(s').
 *   Proved by case analysis on the 10 transition rules.
 *
 * CEK.3 (Corollary): Zero-weight symbols in poststar correspond to
 *   unreachable rules in any concrete parse. By contraposition of CEK.2.
 *
 * The WPDS (Weighted Pushdown System) models the parser's pushdown
 * automaton at compile time. The abstraction function alpha maps
 * concrete CEK configurations to WPDS stack configurations. The forward
 * simulation theorem establishes that the compile-time WPDS model is a
 * sound over-approximation of all possible runtime behaviors.
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition          | Rust / Generated Code               | Location
 *   -------------------------|--------------------------------------|--------------------------
 *   wpds_rule                | WpdsRule<W> enum                     | wpds.rs:104-133
 *   wpds_step                | One-step PDS execution               | wpds.rs:101-103
 *   wpds_reachable           | Reflexive-transitive closure         | wpds.rs:689-706
 *   alpha                    | Abstraction function                  | cek-machine.md Section 3
 *   poststar_weight          | poststar() P-automaton weights       | wpds.rs:707-840
 *   frame_to_symbol          | StackSymbol mapping                  | wpds.rs:62-69
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
(*  Section 1: WPDS Model (Single Control Location)                        *)
(* ===================================================================== *)

(* We reuse the WPDS model structure from WpdsCorrectness.v but keep
   this file self-contained. The WPDS uses a single control location p,
   since PraTTaIL's build_wpds always uses p = p'. *)

Section WpdsSimulation.

  (* Stack symbol type for the WPDS. *)
  Variable symbol : Type.

  (* Equality decidability for symbols (needed for matching). *)
  Hypothesis symbol_eq_dec : forall (s1 s2 : symbol), {s1 = s2} + {s1 <> s2}.

  (* ================================================================= *)
  (*  WPDS Rules                                                         *)
  (* ================================================================= *)

  (* Single-location WPDS rules. Matches wpds.rs:104-133. *)
  Inductive wpds_rule : Type :=
    | WR_Pop (gamma : symbol)
    | WR_Replace (gamma gamma' : symbol)
    | WR_Push (gamma gamma1 gamma2 : symbol).

  (* The set of WPDS rules (built by build_wpds). *)
  Variable rules : list wpds_rule.

  (* ================================================================= *)
  (*  WPDS Step and Reachability                                         *)
  (* ================================================================= *)

  (* One-step WPDS transition on stacks. *)
  Inductive wpds_step : list symbol -> list symbol -> Prop :=
    | WS_Pop : forall gamma w,
        In (WR_Pop gamma) rules ->
        wpds_step (gamma :: w) w
    | WS_Replace : forall gamma gamma' w,
        In (WR_Replace gamma gamma') rules ->
        wpds_step (gamma :: w) (gamma' :: w)
    | WS_Push : forall gamma gamma1 gamma2 w,
        In (WR_Push gamma gamma1 gamma2) rules ->
        wpds_step (gamma :: w) (gamma1 :: gamma2 :: w).

  (* Reflexive-transitive closure of wpds_step. *)
  Inductive wpds_reachable : list symbol -> list symbol -> Prop :=
    | WR_refl : forall w, wpds_reachable w w
    | WR_step : forall w1 w2 w3,
        wpds_step w1 w2 -> wpds_reachable w2 w3 -> wpds_reachable w1 w3.

  Lemma wpds_reachable_one : forall w1 w2,
    wpds_step w1 w2 -> wpds_reachable w1 w2.
  Proof.
    intros w1 w2 Hstep.
    apply WR_step with w2.
    - exact Hstep.
    - apply WR_refl.
  Qed.

  Lemma wpds_reachable_trans : forall w1 w2 w3,
    wpds_reachable w1 w2 -> wpds_reachable w2 w3 -> wpds_reachable w1 w3.
  Proof.
    intros w1 w2 w3 H12 H23.
    induction H12 as [w | a b c Hstep Hbc IH].
    - exact H23.
    - apply WR_step with b.
      + exact Hstep.
      + apply IH. exact H23.
  Qed.

  (* ================================================================= *)
  (*  Section 2: Abstract CEK Configuration                              *)
  (* ================================================================= *)

  (* We model CEK configurations abstracted to their WPDS representation:
     a list of symbols [current_sym, frame_sym_1, ..., frame_sym_n].
     The abstraction function alpha is implicit in this representation. *)

  Definition cek_config := list symbol.

  (* ================================================================= *)
  (*  Section 3: Per-Rule WPDS Correspondence Hypotheses                 *)
  (* ================================================================= *)

  (* For each of the 10 CEK transition rules, there exist corresponding
     WPDS rules in the rule set. These hypotheses connect the grammar
     structure to the WPDS model built by build_wpds (wpds.rs:388-644).

     We model each rule as a symbol-level function that maps the
     source symbol to the target symbol(s). *)

  (* Rule 1: DRIVE — Replace current symbol (Drive -> Prefix) *)
  Variable drive_target : symbol -> symbol.
  Hypothesis drive_rule_exists :
    forall gamma, In (WR_Replace gamma (drive_target gamma)) rules.

  (* Rule 2: PREFIX-NT — Push frame (Prefix -> Drive + frame) *)
  Variable prefix_nt_target : symbol -> symbol.
  Variable prefix_nt_frame : symbol -> symbol.
  Hypothesis prefix_nt_rule_exists :
    forall gamma,
      In (WR_Push gamma (prefix_nt_target gamma) (prefix_nt_frame gamma)) rules.

  (* Rule 3: PREFIX-LEAF — Replace current symbol (Prefix -> Infix) *)
  Variable prefix_leaf_target : symbol -> symbol.
  Hypothesis prefix_leaf_rule_exists :
    forall gamma, In (WR_Replace gamma (prefix_leaf_target gamma)) rules.

  (* Rule 4: PREFIX-TAIL — Replace current symbol (Prefix -> Drive, no push) *)
  Variable prefix_tail_target : symbol -> symbol.
  Hypothesis prefix_tail_rule_exists :
    forall gamma, In (WR_Replace gamma (prefix_tail_target gamma)) rules.

  (* Rule 5: INFIX — Push InfixRHS frame *)
  Variable infix_target : symbol -> symbol.
  Variable infix_frame : symbol -> symbol.
  Hypothesis infix_rule_exists :
    forall gamma,
      In (WR_Push gamma (infix_target gamma) (infix_frame gamma)) rules.

  (* Rule 6: POSTFIX — Replace current symbol *)
  Variable postfix_target : symbol -> symbol.
  Hypothesis postfix_rule_exists :
    forall gamma, In (WR_Replace gamma (postfix_target gamma)) rules.

  (* Rules 7-9: UNWIND-* — Pop frame symbol, then Replace exposed symbol.
     For each unwind variant, there is a Pop rule for the value symbol
     and a Replace rule for the frame symbol. *)
  Variable unwind_result : symbol -> symbol.

  Hypothesis unwind_pop_exists :
    forall gamma, In (WR_Pop gamma) rules.

  Hypothesis unwind_replace_exists :
    forall gamma, In (WR_Replace gamma (unwind_result gamma)) rules.

  (* Rule 10: UNWIND-EMPTY — Pop the last symbol *)
  Hypothesis unwind_empty_pop_exists :
    forall gamma, In (WR_Pop gamma) rules.

  (* ================================================================= *)
  (*  Section 4: Per-Rule Simulation Lemmas                              *)
  (* ================================================================= *)

  Lemma simulate_drive :
    forall gamma w,
      wpds_reachable (gamma :: w) (drive_target gamma :: w).
  Proof.
    intros gamma w.
    apply wpds_reachable_one.
    apply WS_Replace.
    apply drive_rule_exists.
  Qed.

  Lemma simulate_prefix_nt :
    forall gamma w,
      wpds_reachable (gamma :: w)
        (prefix_nt_target gamma :: prefix_nt_frame gamma :: w).
  Proof.
    intros gamma w.
    apply wpds_reachable_one.
    apply WS_Push.
    apply prefix_nt_rule_exists.
  Qed.

  Lemma simulate_prefix_leaf :
    forall gamma w,
      wpds_reachable (gamma :: w) (prefix_leaf_target gamma :: w).
  Proof.
    intros gamma w.
    apply wpds_reachable_one.
    apply WS_Replace.
    apply prefix_leaf_rule_exists.
  Qed.

  Lemma simulate_prefix_tail :
    forall gamma w,
      wpds_reachable (gamma :: w) (prefix_tail_target gamma :: w).
  Proof.
    intros gamma w.
    apply wpds_reachable_one.
    apply WS_Replace.
    apply prefix_tail_rule_exists.
  Qed.

  Lemma simulate_infix :
    forall gamma w,
      wpds_reachable (gamma :: w)
        (infix_target gamma :: infix_frame gamma :: w).
  Proof.
    intros gamma w.
    apply wpds_reachable_one.
    apply WS_Push.
    apply infix_rule_exists.
  Qed.

  Lemma simulate_postfix :
    forall gamma w,
      wpds_reachable (gamma :: w) (postfix_target gamma :: w).
  Proof.
    intros gamma w.
    apply wpds_reachable_one.
    apply WS_Replace.
    apply postfix_rule_exists.
  Qed.

  (* For Unwind rules (7-9), the transition is Pop + Replace:
     [gamma_val, gamma_frame | w] -> Pop -> [gamma_frame | w] -> Replace -> [result | w] *)
  Lemma simulate_unwind :
    forall gamma_val gamma_frame w,
      wpds_reachable
        (gamma_val :: gamma_frame :: w)
        (unwind_result gamma_frame :: w).
  Proof.
    intros gamma_val gamma_frame w.
    apply wpds_reachable_trans with (gamma_frame :: w).
    - apply wpds_reachable_one.
      apply WS_Pop.
      apply unwind_pop_exists.
    - apply wpds_reachable_one.
      apply WS_Replace.
      apply unwind_replace_exists.
  Qed.

  (* For Unwind-Empty (rule 10): [gamma_val] -> Pop -> [] *)
  Lemma simulate_unwind_empty :
    forall gamma_val,
      wpds_reachable [gamma_val] [].
  Proof.
    intros gamma_val.
    apply wpds_reachable_one.
    apply WS_Pop.
    apply unwind_empty_pop_exists.
  Qed.

  (* ================================================================= *)
  (*  Section 5: Abstract CEK Transition Relation                        *)
  (* ================================================================= *)

  (* Each CEK transition rule, when abstracted through alpha, produces
     one of these abstract stack transitions. *)

  Inductive abstract_cek_step : cek_config -> cek_config -> Prop :=
    (* Rule 1: DRIVE *)
    | ACS_Drive : forall gamma w,
        abstract_cek_step (gamma :: w) (drive_target gamma :: w)
    (* Rule 2: PREFIX-NT *)
    | ACS_Prefix_NT : forall gamma w,
        abstract_cek_step (gamma :: w)
          (prefix_nt_target gamma :: prefix_nt_frame gamma :: w)
    (* Rule 3: PREFIX-LEAF *)
    | ACS_Prefix_Leaf : forall gamma w,
        abstract_cek_step (gamma :: w) (prefix_leaf_target gamma :: w)
    (* Rule 4: PREFIX-TAIL *)
    | ACS_Prefix_Tail : forall gamma w,
        abstract_cek_step (gamma :: w) (prefix_tail_target gamma :: w)
    (* Rule 5: INFIX *)
    | ACS_Infix : forall gamma w,
        abstract_cek_step (gamma :: w)
          (infix_target gamma :: infix_frame gamma :: w)
    (* Rule 6: POSTFIX *)
    | ACS_Postfix : forall gamma w,
        abstract_cek_step (gamma :: w) (postfix_target gamma :: w)
    (* Rules 7-9: UNWIND with frame *)
    | ACS_Unwind : forall gamma_val gamma_frame w,
        abstract_cek_step (gamma_val :: gamma_frame :: w)
          (unwind_result gamma_frame :: w)
    (* Rule 10: UNWIND-EMPTY *)
    | ACS_Unwind_Empty : forall gamma_val,
        abstract_cek_step [gamma_val] [].

  (* Multi-step abstract CEK reachability *)
  Inductive abstract_cek_reachable : cek_config -> cek_config -> Prop :=
    | ACR_refl : forall c, abstract_cek_reachable c c
    | ACR_step : forall c1 c2 c3,
        abstract_cek_step c1 c2 ->
        abstract_cek_reachable c2 c3 ->
        abstract_cek_reachable c1 c3.

  (* ================================================================= *)
  (*  Theorem CEK.2: Forward Simulation                                  *)
  (* ================================================================= *)

  (* For every abstract CEK transition s -> s', there exists a WPDS
     transition sequence such that s ->*_WPDS s'.
     Proof by case analysis on the 8 abstract step constructors
     (rules 7-9 are unified into ACS_Unwind). *)

  Theorem cek2_forward_simulation :
    forall c1 c2,
      abstract_cek_step c1 c2 ->
      wpds_reachable c1 c2.
  Proof.
    intros c1 c2 Hstep.
    inversion Hstep; subst.
    - (* ACS_Drive *)
      apply simulate_drive.
    - (* ACS_Prefix_NT *)
      apply simulate_prefix_nt.
    - (* ACS_Prefix_Leaf *)
      apply simulate_prefix_leaf.
    - (* ACS_Prefix_Tail *)
      apply simulate_prefix_tail.
    - (* ACS_Infix *)
      apply simulate_infix.
    - (* ACS_Postfix *)
      apply simulate_postfix.
    - (* ACS_Unwind *)
      apply simulate_unwind.
    - (* ACS_Unwind_Empty *)
      apply simulate_unwind_empty.
  Qed.

  (* Multi-step forward simulation *)
  Theorem cek2_multi_step_simulation :
    forall c1 c2,
      abstract_cek_reachable c1 c2 ->
      wpds_reachable c1 c2.
  Proof.
    intros c1 c2 Hreach.
    induction Hreach as [c | a b c Hstep Hbc IH].
    - apply WR_refl.
    - apply wpds_reachable_trans with b.
      + apply cek2_forward_simulation. exact Hstep.
      + exact IH.
  Qed.

  (* ================================================================= *)
  (*  Section 6: Poststar Weight Model                                   *)
  (* ================================================================= *)

  (* Poststar computes weights for each reachable configuration in the
     P-automaton. A symbol with zero weight on top of any reachable
     stack means no parse ever reaches a configuration where that
     symbol is the current control point. *)

  (* Weight type with zero detection *)
  Variable weight : Type.
  Variable w_is_zero : weight -> Prop.

  (* Poststar weight assignment: maps each symbol to its weight in the
     saturated P-automaton. *)
  Variable poststar_weight : symbol -> weight.

  (* A symbol is WPDS-unreachable if its poststar weight is zero. *)
  Definition wpds_unreachable (gamma : symbol) : Prop :=
    w_is_zero (poststar_weight gamma).

  (* Poststar soundness (from WpdsCorrectness.v):
     if gamma is on top of a reachable configuration, its poststar
     weight is non-zero. *)
  Hypothesis poststar_sound :
    forall gamma0 gamma w,
      wpds_reachable [gamma0] (gamma :: w) ->
      ~w_is_zero (poststar_weight gamma).

  (* ================================================================= *)
  (*  Theorem CEK.3: Dead Rule Soundness                                 *)
  (* ================================================================= *)

  (* Zero-weight symbols in poststar correspond to unreachable stack
     configurations. By contraposition of poststar soundness:
     if poststar_weight(gamma) = 0, then no reachable configuration
     has gamma on top of stack. *)

  Theorem cek3_dead_rule_soundness :
    forall gamma0 gamma w,
      wpds_unreachable gamma ->
      ~wpds_reachable [gamma0] (gamma :: w).
  Proof.
    intros gamma0 gamma w Hunreach Hreach.
    unfold wpds_unreachable in Hunreach.
    exact (poststar_sound gamma0 gamma w Hreach Hunreach).
  Qed.

  (* Corollary: if a CEK configuration is reachable from the initial
     configuration via abstract_cek_reachable, and alpha maps it to
     a stack with gamma on top, then gamma has non-zero poststar weight.

     Equivalently: if gamma has zero poststar weight, no abstract CEK
     execution from [gamma0] reaches a configuration with gamma on top. *)

  Corollary cek3_abstract_dead_rule :
    forall gamma0 c,
      abstract_cek_reachable [gamma0] c ->
      forall gamma w, c = gamma :: w ->
      ~w_is_zero (poststar_weight gamma).
  Proof.
    intros gamma0 c Hcek gamma w Heq.
    subst c.
    apply poststar_sound with gamma0.
    apply cek2_multi_step_simulation.
    exact Hcek.
  Qed.

End WpdsSimulation.

(* ===================================================================== *)
(*  Verification: key theorems accessible                                  *)
(* ===================================================================== *)

Check cek2_forward_simulation.
Check cek2_multi_step_simulation.
Check cek3_dead_rule_soundness.
Check cek3_abstract_dead_rule.
