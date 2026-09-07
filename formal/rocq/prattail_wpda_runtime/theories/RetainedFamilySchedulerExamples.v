(* Executable, non-vacuous witnesses for the retained-family scheduler.
 * These evaluate its real dispatcher/driver, not an oracle-only relation.
 * A family is an ordered list of natural-number terms; Pair realizes every
 * ordered combination. The shared diamond and repeated dependency therefore
 * detect both discovery-order emptiness and occurrence-selection collapse.
 * Forest-producer/weight correspondence remains a separate source gate.
 *)
From Stdlib Require Import List Arith.
From PrattailWpdaRuntime Require Import RetainedFamilyScheduler.
Import ListNotations.

Inductive witness_label :=
| Emit : list nat -> witness_label
| Forward : witness_label
| Pair : witness_label
| RejectAssembly : witness_label.

Definition witness_row (allowed : bool) (children : list nat) (label : witness_label)
  : row :=
  {| origin_packing := 0; original_flat := children; admitted := allowed;
     dependencies := children; assembly_label := label |}.

Definition witness_prepare (node : nat) : nat + list row :=
  match node with
  | 0 => inr [witness_row true [1; 2] Pair]
  | 1 | 2 => inr [witness_row true [3] Forward]
  | 3 => inr [witness_row true [] (Emit [1; 2])]
  | 4 => inr [witness_row true [] (Emit [7])]
  | 5 => inr []
  | 6 => inr [witness_row true [3; 3] Pair]
  | 7 => inr [witness_row true [7] Forward]
  | 8 => inr [witness_row true [9] Forward]
  | 9 => inr [witness_row true [8] Forward]
  | 10 => inr [witness_row false [10] Forward; witness_row true [] (Emit [9])]
  | 11 => inr [witness_row true [12; 3] Pair]
  | 12 => inr [witness_row true [11] Forward]
  | 13 => inr [witness_row true [14] Forward]
  | 14 => inl 42
  | 15 => inr [witness_row true [] (Emit [7]); witness_row true [] RejectAssembly]
  | 16 => inr [witness_row true [] (Emit [7]); witness_row true [] (Emit [99])]
  | 17 => inr [witness_row true [5; 3] Pair]
  | _ => inl 45
  end.

Definition witness_assemble (current : row) (inputs : list (list nat)) : nat + list nat :=
  match assembly_label current, inputs with
  | Emit values, [] => inr values
  | Forward, [values] => inr values
  | Pair, [left_values; right_values] =>
      inr (flat_map
        (fun first => map (fun second => 100 * first + second) right_values) left_values)
  | _, _ => inl 43
  end.

Definition witness_observe (node : nat) (acc family : list nat) : nat + list nat :=
  match node, family with
  | 16, [99] => inl 44
  | _, _ => inr (acc ++ family)
  end.

Definition witness_initial (_ : nat) : list nat := [].
Definition witness_finish (acc : list nat) : list nat := acc.

Definition witness_execute (fuel root : nat) : request_failure + list nat :=
  match witness_prepare root with
  | inl fault => inl (PreparationFault root fault)
  | inr rows =>
      match run_scheduler witness_prepare witness_initial witness_finish witness_assemble witness_observe
        fuel (fun _ => None)
        [{| owner := root; rows_left := rows; accumulated := []; frame_phase := ScanRows |}] with
      | inl fault => inl fault
      | inr memo => match memo root with
          | Some family => inr family
          | None => inl (SchedulerInvariantFault root)
          end
      end
  end.

Example nullary_row_is_actually_executed : witness_execute 4 4 = inr [7].
Proof. vm_compute. reflexivity. Qed.

Example completed_empty_node_is_successful_not_missing : witness_execute 1 5 = inr [].
Proof. vm_compute. reflexivity. Qed.

Example shared_diamond_keeps_all_four_combinations :
  witness_execute 24 0 = inr [101; 102; 201; 202].
Proof. vm_compute. reflexivity. Qed.

Example repeated_dependency_occurrences_are_independent_coordinates :
  witness_execute 12 6 = inr [101; 102; 201; 202].
Proof. vm_compute. reflexivity. Qed.

Example completed_empty_dependency_annihilates_the_product : witness_execute 20 17 = inr [].
Proof. vm_compute. reflexivity. Qed.

Example self_cycle_is_not_successful_absence : witness_execute 20 7 = inl (DependencyCycle 7).
Proof. vm_compute. reflexivity. Qed.

Example mutual_cycle_is_not_confused_with_a_shared_dag :
  witness_execute 20 8 = inl (DependencyCycle 8).
Proof. vm_compute. reflexivity. Qed.

Example refused_cyclic_row_does_not_demand_its_child : witness_execute 5 10 = inr [9].
Proof. vm_compute. reflexivity. Qed.

Example cycle_beneath_a_pair_is_not_hidden_by_the_container :
  witness_execute 20 11 = inl (DependencyCycle 11).
Proof. vm_compute. reflexivity. Qed.

Example dependency_preparation_error_is_exact :
  witness_execute 20 13 = inl (PreparationFault 14 42).
Proof. vm_compute. reflexivity. Qed.

Example root_preparation_error_is_exact : witness_execute 20 14 = inl (PreparationFault 14 42).
Proof. vm_compute. reflexivity. Qed.

Example assembly_error_after_an_emitted_row_discards_the_prefix :
  witness_execute 20 15 = inl (AssemblyFault 15 43).
Proof. vm_compute. reflexivity. Qed.

Example observation_error_after_an_emitted_row_discards_the_prefix :
  witness_execute 20 16 = inl (ObservationFault 16 44).
Proof. vm_compute. reflexivity. Qed.

Example zero_scheduler_budget_is_not_an_empty_family : witness_execute 0 4 = inl ResourceFault.
Proof. vm_compute. reflexivity. Qed.

Example budget_exhaustion_after_an_emitted_row_discards_the_prefix :
  witness_execute 3 4 = inl ResourceFault.
Proof. vm_compute. reflexivity. Qed.

Example dependency_unavailable_on_resume_is_corruption_not_absence :
  scheduler_dispatch witness_prepare witness_initial witness_finish witness_assemble witness_observe
    (fun _ => None)
    [{| owner := 1; rows_left := [witness_row true [3] Forward]; accumulated := [];
        frame_phase := AwaitChild [] 3 [] |}] = DispatchFailed (SchedulerInvariantFault 1).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions shared_diamond_keeps_all_four_combinations.
Print Assumptions repeated_dependency_occurrences_are_independent_coordinates.
Print Assumptions completed_empty_dependency_annihilates_the_product.
Print Assumptions mutual_cycle_is_not_confused_with_a_shared_dag.
Print Assumptions refused_cyclic_row_does_not_demand_its_child.
Print Assumptions assembly_error_after_an_emitted_row_discards_the_prefix.
Print Assumptions observation_error_after_an_emitted_row_discards_the_prefix.
Print Assumptions budget_exhaustion_after_an_emitted_row_discards_the_prefix.
