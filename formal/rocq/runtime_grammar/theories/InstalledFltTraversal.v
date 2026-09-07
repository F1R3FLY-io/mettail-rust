(** * Reusing the checked reconstruction machine for installed FLTs

    This module instantiates the existing producer/assembly machine with the
    exact ordered constructor plan from [InstalledFltHeadCodec].  The machine's
    numeric type coordinates here denote semantic sorts; they are not assumed
    equal to grammar category identifiers.  This is the traversal contract,
    not another parser, evaluator, or assembly implementation.

    Reuse boundaries are explicit: the tagged machine supplies stack order and
    frame ownership, installed judgments supply the monotone charge operation
    and whole-result publication, and the head codec supplies exact constructor
    identity and argument order.  The new composition connects the argument
    visits to the same resolved binding and accounts for occurrence work.

    These theorems do not by themselves establish whole-tree semantic
    preservation, native-stack bounds for Rust ownership, or correspondence
    between a cost trace and actual Rust allocations.  A checked local view,
    valid child coordinates, per-path cycle rejection, complete child results,
    canonical reflection and concrete per-operation charging are still required
    by the implementation refinement. *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.
From RuntimeGrammar Require Import TaggedReconstructionMachine InstalledFltHeadCodec
  InstalledFltJudgments.
Import ListNotations.

Module InstalledFltTraversal.
Module Machine := TaggedReconstructionMachine.TaggedReconstructionMachine.
Module Head := InstalledFltHeadCodec.InstalledFltHeadCodec.
Module Service := InstalledFltJudgments.InstalledFltJudgments.

Definition argument_visit (argument : nat * nat) : Machine.Task :=
  Machine.Produce (Machine.Visit (fst argument) Machine.Required (snd argument)).

Definition constructor_frame (entry : Head.ConstructorBinding) (base : nat) : Machine.Frame :=
  Machine.frame (Head.semantic_result entry) (Head.semantic_constructor entry)
    base (length (Head.semantic_domain entry)) Machine.TypedConstructor.

Definition constructor_schedule entry base arguments old :=
  Machine.append_plan_lifo old
    (map argument_visit arguments ++ [Machine.AssembleFrame (constructor_frame entry base)]).

Theorem constructor_executes_all_arguments_before_assembly : forall entry base arguments old,
  Machine.pop_order (constructor_schedule entry base arguments old) =
  (map argument_visit arguments ++ [Machine.AssembleFrame (constructor_frame entry base)])
    ++ Machine.pop_order old.
Proof.
  intros. unfold constructor_schedule.
  apply Machine.lifo_append_executes_plan_before_old_work.
Qed.

Definition visit_coordinates (task : Machine.Task) : option (nat * nat) :=
  match task with
  | Machine.Produce (Machine.Visit sort Machine.Required child) => Some (sort, child)
  | _ => None
  end.

Lemma argument_visit_retains_both_coordinates : forall arguments,
  map visit_coordinates (map argument_visit arguments) = map Some arguments.
Proof.
  induction arguments as [|[sort child] rest IH]; cbn; [reflexivity|now rewrite IH].
Qed.

Theorem resolved_schedule_retains_exact_child_occurrences :
  forall table sort label children entry arguments,
  Head.resolve_constructor_plan table sort label children = Some (entry, arguments) ->
  map fst arguments = Head.semantic_domain entry /\
  map snd arguments = children /\
  map visit_coordinates (map argument_visit arguments) = map Some arguments.
Proof.
  intros table sort label children entry arguments H.
  apply Head.resolved_plan_uses_the_same_exact_binding in H.
  destruct H as [_ [_ [_ [Hdomain Hchildren]]]].
  repeat split; try assumption. apply argument_visit_retains_both_coordinates.
Qed.

Theorem flt_assembly_preserves_the_enclosing_prefix : forall values entry base result output,
  Machine.assemble_values values (constructor_frame entry base) result = Some output ->
  firstn base output = firstn base values /\
  length values = base + length (Head.semantic_domain entry) /\ length output = S base.
Proof.
  intros values entry base result output H.
  (* These existing theorems expose explicit state arguments; passing only the
     equality proof would supply it where the current value list is required. *)
  pose proof (@Machine.successful_assembly_preserves_prefix
    values (constructor_frame entry base) result output H) as Hprefix.
  pose proof (@Machine.successful_assembly_has_exact_net_height
    values (constructor_frame entry base) result output H) as Hheight.
  cbn [constructor_frame] in Hprefix, Hheight. auto.
Qed.

(** Only a completed traversal with exactly one result can export a root.
    Intermediate values are private even when the pending work is malformed. *)
Definition completed_root (tasks : list Machine.Task) (values : list nat) : option nat :=
  match tasks, values with
  | [], [root] => Some root
  | _, _ => None
  end.

Theorem successful_root_requires_complete_unique_result : forall tasks values root,
  completed_root tasks values = Some root -> tasks = [] /\ values = [root].
Proof.
  intros [|task rest] [|value [|extra tail]] root H; cbn in H; try discriminate.
  inversion H; subst. auto.
Qed.

(** Charges describe actual visited occurrences, not distinct graph vertices.
    A shared child reached twice contributes two entries; the scalar theorem
    below applies to each bounded resource dimension separately.  Existing
    [charge_work] is reused, so conversion cannot reset an earlier prefix. *)
Fixpoint charge_occurrences (ceiling used : nat) (charges : list nat) : option nat :=
  match charges with
  | [] => if Nat.leb used ceiling then Some used else None
  | charge :: rest =>
      match Service.charge_work ceiling used charge with
      | Some next => charge_occurrences ceiling next rest
      | None => None
      end
  end.

Definition total_charge (charges : list nat) := fold_right Nat.add 0 charges.

Theorem occurrence_charging_preserves_full_prefix_and_ceiling : forall charges ceiling used total,
  charge_occurrences ceiling used charges = Some total ->
  total = used + total_charge charges /\ used <= total /\ total <= ceiling.
Proof.
  induction charges as [|charge rest IH]; intros ceiling used total H.
  - cbn [charge_occurrences] in H.
    destruct (Nat.leb used ceiling) eqn:E; try discriminate.
    apply Nat.leb_le in E. injection H as Htotal.
    change (total = used + 0 /\ used <= total /\ total <= ceiling). lia.
  - cbn [charge_occurrences] in H.
    destruct (Service.charge_work ceiling used charge) as [next|] eqn:E; try discriminate.
    pose proof (Service.successful_charge_preserves_prefix_and_ceiling ceiling used charge next E)
      as Hcharge.
    specialize (IH ceiling next total H).
    (* Keep the rest's folded total identical to the induction hypothesis;
       unfolding [total_charge] alone leaves an opaque [fold_right] to [lia]. *)
    change (total = used + (charge + total_charge rest) /\ used <= total /\ total <= ceiling).
    destruct Hcharge as [Hnext [Hprefix Hlimit]], IH as [Htotal [Hnexttotal Hceiling]]. lia.
Qed.

Lemma positive_charges_bound_occurrences : forall charges,
  Forall (fun charge => 0 < charge) charges -> length charges <= total_charge charges.
Proof.
  intros charges H. induction H as [|charge rest Hpositive Hrest IH].
  - reflexivity.
  - change (S (length rest) <= charge + total_charge rest). lia.
Qed.

Theorem positive_occurrences_cannot_exceed_remaining_work : forall charges ceiling used total,
  Forall (fun charge => 0 < charge) charges ->
  charge_occurrences ceiling used charges = Some total ->
  length charges <= ceiling - used.
Proof.
  intros charges ceiling used total Hpositive Hcharged.
  pose proof (positive_charges_bound_occurrences charges Hpositive) as Hcount.
  apply occurrence_charging_preserves_full_prefix_and_ceiling in Hcharged.
  destruct Hcharged as [Htotal [Hprefix Hlimit]]. lia.
Qed.

Example repeated_reference_consumes_repeated_work :
  charge_occurrences 11 3 [4; 4] = Some 11 /\
  charge_occurrences 10 3 [4; 4] = None.
Proof. split; reflexivity. Qed.

End InstalledFltTraversal.

Print Assumptions InstalledFltTraversal.resolved_schedule_retains_exact_child_occurrences.
Print Assumptions InstalledFltTraversal.flt_assembly_preserves_the_enclosing_prefix.
Print Assumptions InstalledFltTraversal.successful_root_requires_complete_unique_result.
Print Assumptions InstalledFltTraversal.occurrence_charging_preserves_full_prefix_and_ceiling.
Print Assumptions InstalledFltTraversal.positive_occurrences_cannot_exceed_remaining_work.
