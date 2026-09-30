(** Finite capability projection for the existing tape test generator.

    Categories and constructor labels are natural-number identifiers. A base
    is an already supported depth-zero constructor, not a grammar-productivity
    witness. Each arm records the category-builder calls its current emitter
    can issue. Projection retains the bases unchanged and filters recursive
    arms by those calls, without changing their order. Fatal source diagnostics
    are carried separately and are never filtered as capability gaps.

    Source correspondence: strategies.rs computes bases before its former
    synthetic no-leaf compile_error, then shares the plan with public/private
    builders, generated properties, simulation selection and the gap census.
    The model proves call-domain closure, not grammar completeness, parser
    correctness, or native-stack safety of the existing recursive builders. *)
From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Module TapeGeneratorCapability.
Record Arm := { label : nat; calls : list nat }.
Definition available (bases : nat -> list nat) (category : nat) : bool :=
  match bases category with [] => false | _ :: _ => true end.
Definition supported (bases : nat -> list nat) (arm : Arm) : bool :=
  forallb (available bases) (calls arm).
Definition project (bases : nat -> list nat) (arms : list Arm) : list Arm :=
  filter (supported bases) arms.

Theorem available_exact : forall bases category,
  available bases category = true <-> bases category <> [].
Proof. intros bases category; unfold available; destruct (bases category);
  split; intros H; try discriminate; try reflexivity; contradiction. Qed.

Theorem retained_exact : forall bases arms arm,
  In arm (project bases arms) <->
  In arm arms /\ Forall (fun category => available bases category = true) (calls arm).
Proof.
  intros. unfold project. rewrite filter_In. unfold supported.
  rewrite forallb_forall, Forall_forall. reflexivity.
Qed.

Theorem every_child_has_base : forall bases arms arm category,
  In arm (project bases arms) -> In category (calls arm) -> bases category <> [].
Proof.
  intros bases arms arm category IN CHILD. apply retained_exact in IN.
  destruct IN as [_ ALL]. rewrite Forall_forall in ALL.
  apply available_exact. apply ALL; exact CHILD.
Qed.

(** Subsequence records order and multiplicity, unlike set inclusion. *)
Inductive Subsequence : list Arm -> list Arm -> Prop :=
| sub_nil : forall source, Subsequence [] source
| sub_keep : forall arm kept source,
    Subsequence kept source -> Subsequence (arm :: kept) (arm :: source)
| sub_skip : forall arm kept source,
    Subsequence kept source -> Subsequence kept (arm :: source).

Theorem projection_preserves_order : forall bases arms,
  Subsequence (project bases arms) arms.
Proof.
  intros bases arms. induction arms as [|arm rest IH].
  - constructor.
  - unfold project in *. simpl. destruct (supported bases arm);
      [apply sub_keep | apply sub_skip]; exact IH.
Qed.

Theorem unaffected_arms_unchanged : forall bases arms,
  Forall (fun arm => supported bases arm = true) arms -> project bases arms = arms.
Proof.
  intros bases arms ALL. induction ALL; [reflexivity|].
  unfold project in *. simpl. rewrite H, IHALL. reflexivity.
Qed.

Definition unavailable_calls bases arm :=
  filter (fun category => negb (available bases category)) (calls arm).

Theorem gap_has_exact_witness : forall bases arm,
  supported bases arm = false <-> unavailable_calls bases arm <> [].
Proof.
  intros bases [name children]. unfold supported, unavailable_calls; simpl.
  induction children as [|category rest IH]; simpl.
  - split; intros H; [discriminate|contradiction].
  - destruct (available bases category); simpl.
    + exact IH.
    + split; intros; discriminate.
Qed.

Theorem no_base_is_not_a_grammar_claim : forall bases category,
  available bases category = false <-> bases category = [].
Proof. intros bases category; unfold available; destruct (bases category);
  split; intros; try reflexivity; discriminate. Qed.

Definition available_categories bases categories := filter (available bases) categories.
Theorem simulation_selection_has_base : forall bases categories category,
  In category (available_categories bases categories) -> bases category <> [].
Proof.
  intros bases categories category H. apply filter_In in H.
  apply available_exact. exact (proj2 H).
Qed.

Record SourcePlan := {
  base_labels : list nat;
  recursive_arms : list Arm;
  fatal_diagnostics : list nat
}.
Definition project_plan bases plan :=
  {| base_labels := base_labels plan;
     recursive_arms := project bases (recursive_arms plan);
     fatal_diagnostics := fatal_diagnostics plan |}.
Theorem bases_and_diagnostics_preserved : forall bases plan,
  base_labels (project_plan bases plan) = base_labels plan /\
  fatal_diagnostics (project_plan bases plan) = fatal_diagnostics plan.
Proof. intros; split; reflexivity. Qed.

Theorem positive_depth_decreases : forall depth, depth < S depth.
Proof. intros; lia. Qed.

Example closed_category_with_base_remains_available :
  available (fun category => if Nat.eqb category 7 then [42] else []) 7 = true.
Proof. reflexivity. Qed.
End TapeGeneratorCapability.
