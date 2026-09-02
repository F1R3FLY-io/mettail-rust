(*
 * TypedSmtCertificates: sort-safe translation and independent model checking
 * for the optional SMT constraint backend.
 *
 * Rust correspondence:
 *   RawTerm / infer_raw       -- SmtTerm validation boundary
 *   Term sort                 -- validated, sort-indexed SMT term image
 *   eval_term                 -- independent pure certificate evaluator
 *   validate_raw_formula      -- checked constraint construction
 *   classify_raw / admit      -- malformed => Undetermined => fail closed
 *
 * The model separates mathematical integers from fixed-width bitvectors.
 * Integer arithmetic uses Z and cannot wrap. Bitvector arithmetic is reduced
 * modulo 2^width, and comparison of bitvectors is unsigned because canonical
 * values lie in [0, 2^width).
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import BinPos.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

Inductive Sort : Type :=
  | IntSort
  | BvSort (width : positive).

Definition sort_eqb (left right : Sort) : bool :=
  match left, right with
  | IntSort, IntSort => true
  | BvSort left_width, BvSort right_width => Pos.eqb left_width right_width
  | _, _ => false
  end.

Lemma sort_eqb_refl : forall sort, sort_eqb sort sort = true.
Proof.
  intros [|width]; simpl; [reflexivity | apply Pos.eqb_refl].
Qed.

Definition Denote (sort : Sort) : Type :=
  match sort with
  | IntSort => Z
  | BvSort _ => Z
  end.

Definition modulus (width : positive) : Z :=
  2 ^ Z.of_nat (Pos.to_nat width).

Definition normalize_bv (width : positive) (value : Z) : Z :=
  value mod modulus width.

Definition add_value (sort : Sort)
    : Denote sort -> Denote sort -> Denote sort :=
  match sort with
  | IntSort => Z.add
  | BvSort width => fun left right => normalize_bv width (left + right)
  end.

Definition sub_value (sort : Sort)
    : Denote sort -> Denote sort -> Denote sort :=
  match sort with
  | IntSort => Z.sub
  | BvSort width => fun left right => normalize_bv width (left - right)
  end.

Definition scale_value (sort : Sort)
    : Z -> Denote sort -> Denote sort :=
  match sort with
  | IntSort => Z.mul
  | BvSort width => fun coefficient value =>
      normalize_bv width (coefficient * value)
  end.

Inductive Term : Sort -> Type :=
  | TIntLit : Z -> Term IntSort
  | TBvLit : forall width, Z -> Term (BvSort width)
  | TVar : forall sort, nat -> Term sort
  | TAdd : forall sort, Term sort -> Term sort -> Term sort
  | TSub : forall sort, Term sort -> Term sort -> Term sort
  | TScale : forall sort, Z -> Term sort -> Term sort.

Definition Environment : Type := forall sort, nat -> Denote sort.

Fixpoint eval_term {sort : Sort}
    (environment : Environment) (term : Term sort) : Denote sort :=
  match term with
  | TIntLit value => value
  | TBvLit width value => normalize_bv width value
  | TVar variable_sort index => environment variable_sort index
  | TAdd value_sort lhs rhs =>
      add_value value_sort (eval_term environment lhs) (eval_term environment rhs)
  | TSub value_sort lhs rhs =>
      sub_value value_sort (eval_term environment lhs) (eval_term environment rhs)
  | TScale value_sort coefficient inner =>
      scale_value value_sort coefficient (eval_term environment inner)
  end.

Definition value_eqb (sort : Sort) : Denote sort -> Denote sort -> bool :=
  match sort with
  | IntSort | BvSort _ => Z.eqb
  end.

Definition value_leb (sort : Sort) : Denote sort -> Denote sort -> bool :=
  match sort with
  | IntSort | BvSort _ => Z.leb
  end.

Inductive Formula : Type :=
  | FTrue
  | FFalse
  | FEq : forall sort, Term sort -> Term sort -> Formula
  | FLe : forall sort, Term sort -> Term sort -> Formula
  | FNot : Formula -> Formula
  | FAnd : Formula -> Formula -> Formula
  | FOr : Formula -> Formula -> Formula.

Fixpoint eval_formula (environment : Environment) (formula : Formula) : bool :=
  match formula with
  | FTrue => true
  | FFalse => false
  | FEq sort lhs rhs =>
      value_eqb sort (eval_term environment lhs) (eval_term environment rhs)
  | FLe sort lhs rhs =>
      value_leb sort (eval_term environment lhs) (eval_term environment rhs)
  | FNot inner => negb (eval_formula environment inner)
  | FAnd lhs rhs => andb (eval_formula environment lhs) (eval_formula environment rhs)
  | FOr lhs rhs => orb (eval_formula environment lhs) (eval_formula environment rhs)
  end.

(* Raw boundary accepted from syntax/deserialization before sort checking. *)
Inductive RawTerm : Type :=
  | RIntLit (value : Z)
  | RBvLit (width : nat) (value : Z)
  | RIntVar (index : nat)
  | RBvVar (width : nat) (index : nat)
  | RAdd (left right : RawTerm)
  | RSub (left right : RawTerm)
  | RScale (coefficient : Z) (inner : RawTerm).

Definition checked_bv_sort (width : nat) : option Sort :=
  match width with
  | O => None
  | S _ => Some (BvSort (Pos.of_nat width))
  end.

Fixpoint infer_raw (term : RawTerm) : option Sort :=
  match term with
  | RIntLit _ | RIntVar _ => Some IntSort
  | RBvLit width _ | RBvVar width _ => checked_bv_sort width
  | RAdd lhs rhs | RSub lhs rhs =>
      match infer_raw lhs, infer_raw rhs with
      | Some left_sort, Some right_sort =>
          if sort_eqb left_sort right_sort then Some left_sort else None
      | _, _ => None
      end
  | RScale _ inner => infer_raw inner
  end.

Inductive RawFormula : Type :=
  | RFTrue
  | RFFalse
  | RFCompare (left right : RawTerm)
  | RFNot (inner : RawFormula)
  | RFAnd (left right : RawFormula)
  | RFOr (left right : RawFormula).

Fixpoint validate_raw_formula (formula : RawFormula) : bool :=
  match formula with
  | RFTrue | RFFalse => true
  | RFCompare lhs rhs =>
      match infer_raw lhs, infer_raw rhs with
      | Some left_sort, Some right_sort => sort_eqb left_sort right_sort
      | _, _ => false
      end
  | RFNot inner => validate_raw_formula inner
  | RFAnd lhs rhs | RFOr lhs rhs =>
      andb (validate_raw_formula lhs) (validate_raw_formula rhs)
  end.

Theorem mixed_integer_bitvector_addition_is_rejected :
  infer_raw (RAdd (RIntLit 1) (RBvLit 8 1)) = None.
Proof. reflexivity. Qed.

Theorem mismatched_bitvector_widths_are_rejected :
  validate_raw_formula
    (RFCompare (RBvVar 8 0) (RBvVar 16 0)) = false.
Proof. reflexivity. Qed.

Theorem zero_width_bitvectors_are_rejected :
  infer_raw (RBvLit 0 0) = None.
Proof. reflexivity. Qed.

Theorem negation_cannot_validate_a_malformed_formula : forall formula,
  validate_raw_formula (RFNot formula) = validate_raw_formula formula.
Proof. reflexivity. Qed.

(* Resource validation happens before allocation-heavy translation.  Numeral
   demand is measured in binary digits, bitvector demand records the largest
   requested sort, and node demand charges every raw constructor exactly once. *)
Definition z_bits (value : Z) : nat :=
  match value with
  | Z0 => 1%nat
  | Zpos magnitude | Zneg magnitude => Pos.size_nat magnitude
  end.

Record WorkDemand : Type := {
  demand_nodes : nat;
  demand_numeral_bits : nat;
  demand_max_bv_width : nat
}.

Definition combine_demand (first second : WorkDemand) : WorkDemand :=
  {| demand_nodes := (demand_nodes first + demand_nodes second)%nat;
     demand_numeral_bits :=
       (demand_numeral_bits first + demand_numeral_bits second)%nat;
     demand_max_bv_width :=
       Nat.max (demand_max_bv_width first) (demand_max_bv_width second) |}.

Definition add_demand_node (demand : WorkDemand) : WorkDemand :=
  {| demand_nodes := S (demand_nodes demand);
     demand_numeral_bits := demand_numeral_bits demand;
     demand_max_bv_width := demand_max_bv_width demand |}.

Fixpoint raw_term_demand (term : RawTerm) : WorkDemand :=
  match term with
  | RIntLit value =>
      {| demand_nodes := 1%nat;
         demand_numeral_bits := z_bits value;
         demand_max_bv_width := 0%nat |}
  | RBvLit width value =>
      {| demand_nodes := 1%nat;
         demand_numeral_bits := z_bits value;
         demand_max_bv_width := width |}
  | RIntVar _ =>
      {| demand_nodes := 1%nat;
         demand_numeral_bits := 0%nat;
         demand_max_bv_width := 0%nat |}
  | RBvVar width _ =>
      {| demand_nodes := 1%nat;
         demand_numeral_bits := 0%nat;
         demand_max_bv_width := width |}
  | RAdd first second | RSub first second =>
      add_demand_node
        (combine_demand (raw_term_demand first) (raw_term_demand second))
  | RScale coefficient inner =>
      let inner_demand := raw_term_demand inner in
      {| demand_nodes := S (demand_nodes inner_demand);
         demand_numeral_bits :=
           (z_bits coefficient + demand_numeral_bits inner_demand)%nat;
         demand_max_bv_width := demand_max_bv_width inner_demand |}
  end.

Fixpoint raw_formula_demand (formula : RawFormula) : WorkDemand :=
  match formula with
  | RFTrue | RFFalse =>
      {| demand_nodes := 1%nat;
         demand_numeral_bits := 0%nat;
         demand_max_bv_width := 0%nat |}
  | RFCompare first second =>
      add_demand_node
        (combine_demand (raw_term_demand first) (raw_term_demand second))
  | RFNot inner => add_demand_node (raw_formula_demand inner)
  | RFAnd first second | RFOr first second =>
      add_demand_node
        (combine_demand (raw_formula_demand first) (raw_formula_demand second))
  end.

Record WorkBudget : Type := {
  budget_nodes : nat;
  budget_numeral_bits : nat;
  budget_max_bv_width : nat
}.

Definition fits_budget (demand : WorkDemand) (budget : WorkBudget) : bool :=
  andb (Nat.leb (demand_nodes demand) (budget_nodes budget))
    (andb
      (Nat.leb (demand_numeral_bits demand) (budget_numeral_bits budget))
      (Nat.leb (demand_max_bv_width demand) (budget_max_bv_width budget))).

Definition budget_extends (smaller larger : WorkBudget) : Prop :=
  (budget_nodes smaller <= budget_nodes larger)%nat /\
  (budget_numeral_bits smaller <= budget_numeral_bits larger)%nat /\
  (budget_max_bv_width smaller <= budget_max_bv_width larger)%nat.

Theorem fits_budget_monotone : forall demand smaller larger,
  budget_extends smaller larger ->
  fits_budget demand smaller = true ->
  fits_budget demand larger = true.
Proof.
  intros demand [small_nodes small_bits small_width]
    [large_nodes large_bits large_width].
  unfold budget_extends, fits_budget; simpl.
  intros [Hnodes [Hbits Hwidth]] Hfits.
  apply andb_true_iff in Hfits as [Hfit_nodes Hfit_rest].
  apply andb_true_iff in Hfit_rest as [Hfit_bits Hfit_width].
  apply Nat.leb_le in Hfit_nodes.
  apply Nat.leb_le in Hfit_bits.
  apply Nat.leb_le in Hfit_width.
  apply andb_true_iff; split; [apply Nat.leb_le; lia |].
  apply andb_true_iff; split; apply Nat.leb_le; lia.
Qed.

Theorem negation_preserves_exhaustion : forall formula budget,
  fits_budget (raw_formula_demand formula) budget = false ->
  fits_budget (raw_formula_demand (RFNot formula)) budget = false.
Proof.
  intros formula [nodes bits width] Hfits.
  cbn [raw_formula_demand].
  remember (raw_formula_demand formula) as demand eqn:Hdemand.
  destruct demand as [need_nodes need_bits need_width].
  cbn [add_demand_node fits_budget] in Hfits |- *.
  apply andb_false_iff in Hfits as [Hnode | Hrest].
  - apply andb_false_iff; left.
    apply Nat.leb_gt in Hnode.
    apply Nat.leb_gt.
    eapply Nat.lt_trans; [exact Hnode | apply Nat.lt_succ_diag_r].
  - apply andb_false_iff; right; exact Hrest.
Qed.

Inductive Verdict : Type :=
  | Proven
  | Refuted
  | Undetermined.

Definition classify_raw (formula : RawFormula) : Verdict :=
  if validate_raw_formula formula then Proven else Undetermined.

Definition admit (verdict : Verdict) : bool :=
  match verdict with
  | Proven => true
  | Refuted | Undetermined => false
  end.

Definition classify_raw_bounded
    (formula : RawFormula) (budget : WorkBudget) : Verdict :=
  if validate_raw_formula formula then
    if fits_budget (raw_formula_demand formula) budget
    then Proven
    else Undetermined
  else Undetermined.

Theorem exhausted_formula_fails_closed : forall formula budget,
  fits_budget (raw_formula_demand formula) budget = false ->
  admit (classify_raw_bounded formula budget) = false.
Proof.
  intros formula budget Hexhausted.
  unfold classify_raw_bounded.
  destruct (validate_raw_formula formula); simpl;
    rewrite ?Hexhausted; reflexivity.
Qed.

Theorem bounded_admission_implies_valid_and_within_budget : forall formula budget,
  admit (classify_raw_bounded formula budget) = true ->
  validate_raw_formula formula = true /\
  fits_budget (raw_formula_demand formula) budget = true.
Proof.
  intros formula budget Hadmitted.
  unfold classify_raw_bounded, admit in Hadmitted.
  destruct (validate_raw_formula formula) eqn:Hvalid; [| discriminate].
  destruct (fits_budget (raw_formula_demand formula) budget) eqn:Hfits;
    [split; assumption | discriminate].
Qed.

Theorem bounded_proven_is_monotone_in_budget : forall formula smaller larger,
  budget_extends smaller larger ->
  classify_raw_bounded formula smaller = Proven ->
  classify_raw_bounded formula larger = Proven.
Proof.
  intros formula smaller larger Hextends Hproven.
  unfold classify_raw_bounded in Hproven |- *.
  destruct (validate_raw_formula formula) eqn:Hvalid; [| discriminate].
  destruct (fits_budget (raw_formula_demand formula) smaller) eqn:Hsmall;
    [| discriminate].
  rewrite (fits_budget_monotone _ _ _ Hextends Hsmall).
  reflexivity.
Qed.

Theorem malformed_formula_fails_closed : forall formula,
  validate_raw_formula formula = false ->
  admit (classify_raw formula) = false.
Proof.
  intros formula Hinvalid.
  unfold classify_raw, admit.
  rewrite Hinvalid.
  reflexivity.
Qed.

Theorem negated_malformed_formula_fails_closed : forall formula,
  validate_raw_formula formula = false ->
  admit (classify_raw (RFNot formula)) = false.
Proof.
  intros formula Hinvalid.
  apply malformed_formula_fails_closed.
  exact Hinvalid.
Qed.

Definition zero_environment : Environment :=
  fun sort _ => match sort with IntSort | BvSort _ => 0 end.

Definition max_i64 : Z := 9223372036854775807.

Theorem mathematical_integer_addition_does_not_wrap :
  eval_term zero_environment
    (TAdd IntSort (TIntLit max_i64) (TIntLit 1)) = max_i64 + 1.
Proof. reflexivity. Qed.

Theorem mathematical_integer_successor_exceeds_i64 :
  max_i64 < eval_term zero_environment
    (TAdd IntSort (TIntLit max_i64) (TIntLit 1)).
Proof. unfold max_i64. simpl. lia. Qed.

Definition width8 : positive := 8%positive.

Theorem bitvector_addition_wraps_modulo_width :
  eval_term zero_environment
    (TAdd (BvSort width8) (TBvLit width8 255) (TBvLit width8 1)) = 0.
Proof. reflexivity. Qed.

Theorem bitvector_comparison_is_unsigned :
  eval_formula zero_environment
    (FLe (BvSort width8) (TBvLit width8 255) (TBvLit width8 1)) = false.
Proof. reflexivity. Qed.

Definition certificate_valid
    (environment : Environment) (formula : Formula) : bool :=
  eval_formula environment formula.

Definition certificate_admitted
    (environment : Environment) (formula : Formula) : bool :=
  certificate_valid environment formula.

Theorem admitted_certificate_rechecks_the_formula : forall environment formula,
  certificate_admitted environment formula = true ->
  eval_formula environment formula = true.
Proof.
  intros environment formula Hadmitted.
  exact Hadmitted.
Qed.

Print Assumptions mixed_integer_bitvector_addition_is_rejected.
Print Assumptions mismatched_bitvector_widths_are_rejected.
Print Assumptions zero_width_bitvectors_are_rejected.
Print Assumptions negated_malformed_formula_fails_closed.
Print Assumptions mathematical_integer_addition_does_not_wrap.
Print Assumptions mathematical_integer_successor_exceeds_i64.
Print Assumptions bitvector_addition_wraps_modulo_width.
Print Assumptions bitvector_comparison_is_unsigned.
Print Assumptions admitted_certificate_rechecks_the_formula.
Print Assumptions fits_budget_monotone.
Print Assumptions negation_preserves_exhaustion.
Print Assumptions exhausted_formula_fails_closed.
Print Assumptions bounded_admission_implies_valid_and_within_budget.
Print Assumptions bounded_proven_is_monotone_in_budget.
