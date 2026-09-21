(** Exact relocation of factoring.rs::FlatNode / flatten_forest and
    mixfix_spine_arm_coords. The Rust bodies and descriptor representation are
    unchanged; only their module and visibility move. There is no new reader,
    recognizer, numbering algorithm, or assumed equality of arbitrary walks.
    OriginalState and RelocatedState wrap the concrete step below separately.

    Source ledger:
    - FlatNode retains its u8 id and ordered borrowed (tree, child-id) entries.
      References are represented by occurrence paths AND the full unchanged
      FactoringTreeRelocation tree. Equal-valued sibling trees therefore retain
      distinct identities. Paths are proof handles, not new Rust allocations.
    - flatten_forest first reports empty roots, then the <2 leaf floor. Its
      existing, unchanged leaf_count helper is interpreted by natural leaf
      cardinality below; this file does not reverify that helper's loop. The
      sum/leaf counters' usize domain is recorded by total <= usize_max.
    - Allocate ALL root ids from 2, then push interior roots in reverse, and
      append the synthetic pre-root row (id 1). For each popped interior,
      allocate ALL immediate children before reverse-pushing them and appending
      the parent's row. Rows are depth-first; id assignment is NOT generic
      preorder. Leaves have id 0 and no row. The defensive popped-leaf continue
      remains represented even though the original allocator filters leaves.
    - Every interior allocation at next_id >= 250 appends its original refusal
      before saturating_add(1). Saturation is at 255 and does not terminate or
      prevent duplicate ids. Root and child message sites remain distinct events
      (their Rust string fragments concatenate to the same final message).
    - mixfix_spine_arm_coords seeds seen with (2,0,0), but does not emit its row.
      It pushes every child in reverse, INCLUDING leaves; popped leaves skip
      advance. Literal kinds 2 and 0 increment only sub_pos; ParamParse resets
      all coordinates to (0,0,0). Other literal kinds panic with that kind.
      The global seen membership test occurs before output/push; collision
      returns None and discards output, not a partial Some. Partial output is
      retained solely as instrumentation of the failure prefix.
    - A list models BTreeSet membership, not its internal ordering/allocation.
      No set iteration occurs in the source. Raw full coordinates are compared.

    Arithmetic and trust boundary: natural s+1 records whether executed s<255;
    claims of faithful returning Rust executions require that flag. Outside
    that domain we do NOT equate debug-overflow panic and release wrapping.
    The explicit kind panic IS modeled. Saturating u8 id addition is modeled
    exactly for valid u8 state; no uniqueness or runtime admission is asserted.
    Finite-run relocation includes output/reference/effect order and failures,
    not all-input termination, borrow checking, allocation, Rust extraction, or
    a new theorem of trie correctness. Source transcription remains reviewed.
    Refusal constructors carry every interpoland; rendering them uses the SAME
    original strings and LIMIT_REFUSAL prefix. Prior refusal strings are opaque
    and retained verbatim. Existing coordinate laws are reused only in their
    stated domain; they do not establish either concrete worklist algorithm.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import FactoringTreeRelocation MixfixSpineCommit.
Import ListNotations.
Import FactoringTreeRelocation.FactoringTreeRelocation.
Set Implicit Arguments.

Module FactoringForestWalkRelocation.

Record TreeRef := { occurrence : list nat; referenced_tree : SpineTree }.
Fixpoint numbered_refs prefix index trees := match trees with
| [] => []
| tree :: rest =>
    {| occurrence := (prefix ++ [index])%list; referenced_tree := tree |} ::
    numbered_refs prefix (S index) rest end.
Definition root_refs roots := numbered_refs [] 0 roots.
Definition child_refs parent children := numbered_refs (occurrence parent) 0 children.

Fixpoint tree_leaf_count tree : nat := match tree with
| Leaf _ _ => 1
| Interior _ children =>
    let fix count children := match children with
      | [] => 0 | child :: rest => tree_leaf_count child + count rest end
    in count children end.
Definition forest_leaf_count roots := fold_right (fun tree n => tree_leaf_count tree + n) 0 roots.

Inductive AllocationSite := RootAllocation | ChildAllocation.
Inductive ForestRefusal :=
| PriorRefusal (message : string)
| EmptyForest
| TooFewLeaves (count : nat)
| NodeIdCeiling (site : AllocationSite).
Definition initial_refusals roots previous :=
  let after_empty := if Nat.eqb (List.length roots) 0
    then (previous ++ [EmptyForest])%list else previous in
  let leaves := forest_leaf_count roots in
  if Nat.ltb leaves 2 then (after_empty ++ [TooFewLeaves leaves])%list else after_empty.
Definition saturating_u8_successor n := Nat.min (S n) 255.
Definition FlatEntry := (TreeRef * nat)%type.
Record FlatNode := { node_id : nat; flat_children : list FlatEntry }.
Record Allocation := {
  allocated_entries : list FlatEntry; allocated_next_id : nat;
  allocated_refusals : list ForestRefusal
}.
Fixpoint allocate_entries site refs next previous := match refs with
| [] => {| allocated_entries := []; allocated_next_id := next; allocated_refusals := previous |}
| ref :: rest =>
    let '(cid, next', previous') := match referenced_tree ref with
    | Leaf _ _ => (0, next, previous)
    | Interior _ _ => (next, saturating_u8_successor next,
        if Nat.leb 250 next then (previous ++ [NodeIdCeiling site])%list else previous) end in
    let after := allocate_entries site rest next' previous' in
    {| allocated_entries := (ref, cid) :: allocated_entries after;
       allocated_next_id := allocated_next_id after;
       allocated_refusals := allocated_refusals after |} end.
Definition has_arm (entry : FlatEntry) := negb (Nat.eqb (snd entry) 0).
Definition interior_entries entries := filter has_arm entries.
Record FlatState := {
  flat_work : list FlatEntry; flat_out : list FlatNode; flat_next_id : nat;
  flat_refusals : list ForestRefusal; flat_arithmetic_ok : bool
}.
Definition flat_state work out next previous valid :=
 {| flat_work := work; flat_out := out; flat_next_id := next;
    flat_refusals := previous; flat_arithmetic_ok := valid |}.
Definition flat_initial usize_max roots previous :=
  let allocated := allocate_entries RootAllocation (root_refs roots) 2
    (initial_refusals roots previous) in
  flat_state (interior_entries (allocated_entries allocated))
    [{| node_id := 1; flat_children := allocated_entries allocated |}]
    (allocated_next_id allocated) (allocated_refusals allocated)
    (Nat.leb (forest_leaf_count roots) usize_max).

Inductive AdvanceResult :=
| Advanced (coord : Coordinate) (addition_ok : bool)
| UnexpectedLiteralKind (kind : nat).
Definition advance (coord : Coordinate) item :=
  let '(kind, completed, sub_pos) := coord in
  match item with
  | ParamParse _ _ => Advanced (0,0,0) true
  | Literal _ _ =>
      if Nat.eqb kind 2 || Nat.eqb kind 0
      then Advanced (kind, completed, S sub_pos) (Nat.ltb sub_pos 255)
      else UnexpectedLiteralKind kind end.
Definition coordinate_eqb (lhs rhs : Coordinate) :=
  let '(k,c,s) := lhs in let '(k',c',s') := rhs in
  Nat.eqb k k' && Nat.eqb c c' && Nat.eqb s s'.
Definition coordinate_seen coord seen := existsb (coordinate_eqb coord) seen.
Definition MixEntry := (TreeRef * Coordinate)%type.
Definition MixRow := (Coordinate * TreeRef)%type.
Record MixState := {
  mix_work : list MixEntry; mix_out : list MixRow;
  mix_seen : list Coordinate; mix_arithmetic_ok : bool
}.
Definition mix_state work out seen valid :=
 {| mix_work := work; mix_out := out; mix_seen := seen; mix_arithmetic_ok := valid |}.
Definition mix_children parent children (coord : Coordinate) :=
  List.map (fun ref => (ref, coord)) (child_refs parent children).
Definition mix_initial root :=
  mix_state [({| occurrence := []; referenced_tree := root |}, (2,0,0))]
    [] [(2,0,0)] true.

Inductive WalkState := Flattening (state : FlatState) | Coordinates (state : MixState).
Inductive WalkOutcome :=
| Running (state : WalkState)
| Flattened (rows : list FlatNode) (previous : list ForestRefusal) (valid : bool)
| CoordinatesReturned (rows : list MixRow) (valid : bool)
| CoordinatesCollided (key : Coordinate) (partial : MixState)
| CoordinatePanicked (kind : nat) (partial : MixState).
Definition core_step state := match state with
| Flattening st => match flat_work st with
    | [] => Flattened (flat_out st) (flat_refusals st) (flat_arithmetic_ok st)
    | (ref, id) :: pending => match referenced_tree ref with
      | Leaf _ _ => Running (Flattening
          (flat_state pending (flat_out st) (flat_next_id st) (flat_refusals st) (flat_arithmetic_ok st)))
      | Interior _ children =>
          let allocated := allocate_entries ChildAllocation (child_refs ref children)
            (flat_next_id st) (flat_refusals st) in
          Running (Flattening (flat_state
            (interior_entries (allocated_entries allocated) ++ pending)%list
            (flat_out st ++ [{| node_id := id; flat_children := allocated_entries allocated |}])%list
            (allocated_next_id allocated) (allocated_refusals allocated) (flat_arithmetic_ok st))) end end
| Coordinates st => match mix_work st with
    | [] => CoordinatesReturned (mix_out st) (mix_arithmetic_ok st)
    | (ref, before) :: pending => match referenced_tree ref with
      | Leaf _ _ => Running (Coordinates
          (mix_state pending (mix_out st) (mix_seen st) (mix_arithmetic_ok st)))
      | Interior item children => match advance before item with
          | UnexpectedLiteralKind kind => CoordinatePanicked kind
              (mix_state pending (mix_out st) (mix_seen st) (mix_arithmetic_ok st))
          | Advanced key valid =>
              let partial := mix_state pending (mix_out st) (mix_seen st) (mix_arithmetic_ok st && valid) in
              if coordinate_seen key (mix_seen st) then CoordinatesCollided key partial
              else Running (Coordinates (mix_state
                (mix_children ref children key ++ pending)%list
                (mix_out st ++ [(key, ref)])%list (key :: mix_seen st) (mix_arithmetic_ok st && valid)))
          end end end end.

(** Module wrappers deliberately share only this concrete unchanged body, not
    an abstract function whose equality is a premise. *)
Record OriginalState := { original_state : WalkState }.
Record RelocatedState := { relocated_state : WalkState }.
Definition relocate st := {| relocated_state := original_state st |}.
Definition original_step st := core_step (original_state st).
Definition relocated_step st := core_step (relocated_state st).
Fixpoint original_execute fuel st := match fuel with
| 0 => Running (original_state st)
| S remaining => match original_step st with
    | Running next => original_execute remaining {| original_state := next |}
    | terminal => terminal end end.
Fixpoint relocated_execute fuel st := match fuel with
| 0 => Running (relocated_state st)
| S remaining => match relocated_step st with
    | Running next => relocated_execute remaining {| relocated_state := next |}
    | terminal => terminal end end.
Theorem exact_walk_step_relocation : forall st,
  relocated_step (relocate st) = original_step st.
Proof. intros []; reflexivity. Qed.
Theorem finite_runs_preserve_rows_handles_effects_and_failures : forall fuel st,
  relocated_execute fuel (relocate st) = original_execute fuel st.
Proof.
  induction fuel; intros; cbn [relocated_execute original_execute]; [reflexivity|].
  rewrite exact_walk_step_relocation.
  destruct (original_step st); try reflexivity.
  exact (IHfuel {| original_state := state |}).
Qed.
Theorem flatten_entry_relocation : forall fuel usize_max roots previous,
  relocated_execute fuel {| relocated_state := Flattening (flat_initial usize_max roots previous) |} =
  original_execute fuel {| original_state := Flattening (flat_initial usize_max roots previous) |}.
Proof.
  intros; exact (finite_runs_preserve_rows_handles_effects_and_failures fuel
    {| original_state := Flattening (flat_initial usize_max roots previous) |}).
Qed.
Theorem coordinate_entry_relocation : forall fuel root,
  relocated_execute fuel {| relocated_state := Coordinates (mix_initial root) |} =
  original_execute fuel {| original_state := Coordinates (mix_initial root) |}.
Proof.
  intros; exact (finite_runs_preserve_rows_handles_effects_and_failures fuel
    {| original_state := Coordinates (mix_initial root) |}).
Qed.

Theorem allocation_preserves_every_borrowed_handle_in_order : forall refs site next previous,
  List.map fst (allocated_entries (allocate_entries site refs next previous)) = refs.
Proof.
  induction refs as [|ref rest IH]; intros; [reflexivity|].
  cbn [allocate_entries]. destruct (referenced_tree ref);
    cbn [allocated_entries List.map fst]; f_equal; apply IH.
Qed.
Theorem reverse_push_filtered_entries_preserves_pop_order : forall entries,
  rev (filter has_arm (rev entries)) = interior_entries entries.
Proof. intros; rewrite filter_rev, rev_involutive; reflexivity. Qed.
Theorem reverse_push_mixfix_children_preserves_pop_order : forall parent children coord,
  rev (List.map (fun ref => (ref, coord)) (rev (child_refs parent children))) =
  mix_children parent children coord.
Proof. intros; rewrite map_rev, rev_involutive; reflexivity. Qed.
Theorem empty_forest_refuses_twice_but_still_emits_pre_root : forall usize_max previous,
  flat_initial usize_max [] previous =
  flat_state [] [{| node_id := 1; flat_children := [] |}] 2
    ((previous ++ [EmptyForest]) ++ [TooFewLeaves 0])%list true.
Proof. reflexivity. Qed.
Theorem id_saturation_is_not_admission :
  saturating_u8_successor 254 = 255 /\ saturating_u8_successor 255 = 255.
Proof. split; reflexivity. Qed.
Theorem repeated_saturated_allocations_keep_refusing : forall ref rest previous,
  (exists item children, referenced_tree ref = Interior item children) ->
  allocate_entries ChildAllocation (ref :: rest) 255 previous =
  let after := allocate_entries ChildAllocation rest 255
    (previous ++ [NodeIdCeiling ChildAllocation])%list in
  {| allocated_entries := (ref,255) :: allocated_entries after;
     allocated_next_id := allocated_next_id after; allocated_refusals := allocated_refusals after |}.
Proof. intros ref rest previous [item [children H]]; cbn [allocate_entries]; rewrite H; reflexivity. Qed.

Theorem coordinate_equality_is_full_tuple_equality : forall lhs rhs,
  coordinate_eqb lhs rhs = true <-> lhs = rhs.
Proof.
  intros [[k c] s] [[k' c'] s']; unfold coordinate_eqb.
  rewrite !andb_true_iff, !Nat.eqb_eq.
  split; [intros [[-> ->] ->]; reflexivity|intros H; inversion H; auto].
Qed.
Theorem coordinate_membership_is_exact : forall coord seen,
  coordinate_seen coord seen = true <-> In coord seen.
Proof.
  intros coord seen; unfold coordinate_seen; rewrite existsb_exists.
  split.
  - intros [other [Hin Heq]]. apply coordinate_equality_is_full_tuple_equality in Heq; subst; assumption.
  - intros Hin; exists coord; split; [assumption|apply coordinate_equality_is_full_tuple_equality; reflexivity].
Qed.
Theorem parameter_reset_preserves_original_coordinates : forall before cat bp,
  advance before (ParamParse cat bp) = Advanced (0,0,0) true.
Proof. intros [[k c] s] cat bp; reflexivity. Qed.
Theorem unsupported_literal_kind_retains_panic_payload : forall k c s text guard,
  k <> 2 -> k <> 0 ->
  advance (k,c,s) (Literal text guard) = UnexpectedLiteralKind k.
Proof.
  intros; unfold advance. apply Nat.eqb_neq in H; apply Nat.eqb_neq in H0.
  rewrite H,H0; reflexivity.
Qed.
Theorem leaves_skip_coordinate_advance : forall path item member before out seen valid,
  core_step (Coordinates (mix_state
    [({| occurrence := path; referenced_tree := Leaf item member |}, before)] out seen valid)) =
  Running (Coordinates (mix_state [] out seen valid)).
Proof. reflexivity. Qed.

Theorem global_collision_returns_before_output_or_child_push :
  forall ref before pending out seen valid item children key addition_valid,
  referenced_tree ref = Interior item children ->
  advance before item = Advanced key addition_valid ->
  coordinate_seen key seen = true ->
  core_step (Coordinates (mix_state ((ref,before)::pending) out seen valid)) =
  CoordinatesCollided key (mix_state pending out seen (valid && addition_valid)).
Proof.
  intros ref before pending out seen valid item children key addition_valid Htree Hadvance Hseen.
  cbn [core_step mix_state mix_work mix_out mix_seen mix_arithmetic_ok].
  rewrite Htree, Hadvance, Hseen; reflexivity.
Qed.

Definition sample_interior children := Interior (Literal "edge" None) children.
Definition numbering_example :=
  [sample_interior [sample_interior [sample_interior []]; sample_interior []]; sample_interior []].
Definition flat_ids result := match result with
| Flattened rows _ _ => List.map node_id rows | _ => [] end.
Theorem root_and_immediate_child_batches_are_not_preorder_ids :
  flat_ids (original_execute 6
    {| original_state := Flattening (flat_initial 100 numbering_example []) |}) = [1;2;4;6;5;3].
Proof. vm_compute; reflexivity. Qed.
Theorem equal_valued_roots_keep_distinct_occurrence_handles : forall tree,
  List.map occurrence (root_refs [tree;tree]) = [[0];[1]].
Proof. reflexivity. Qed.

(** Direct reuse of the existing member-coordinate walk on the permitted
    literal kinds. The imported law is not a claim about global uniqueness. *)
Definition item_code item := match item with Literal _ _ => 0 | ParamParse _ _ => 1 end.
Definition code_is_operand n := Nat.eqb n 1.
Theorem permitted_advance_reuses_existing_coordinate_walk : forall k c s item next valid,
  advance (k,c,s) item = Advanced next valid ->
  walk_from (k,c,s) code_is_operand [item_code item] = [next].
Proof.
  intros k c s [text guard|cat bp] next valid H; cbn [advance] in H.
  - destruct (Nat.eqb k 2 || Nat.eqb k 0); [inversion H; reflexivity|discriminate].
  - inversion H; reflexivity.
Qed.
Theorem existing_coordinate_prefix_length_law_reused : forall items,
  List.length (coords_of code_is_operand (List.map item_code items)) = S (List.length items).
Proof. intros; rewrite coords_of_length, length_map; reflexivity. Qed.

Print Assumptions exact_walk_step_relocation.
Print Assumptions finite_runs_preserve_rows_handles_effects_and_failures.
Print Assumptions flatten_entry_relocation.
Print Assumptions coordinate_entry_relocation.
Print Assumptions allocation_preserves_every_borrowed_handle_in_order.
Print Assumptions reverse_push_filtered_entries_preserves_pop_order.
Print Assumptions reverse_push_mixfix_children_preserves_pop_order.
Print Assumptions empty_forest_refuses_twice_but_still_emits_pre_root.
Print Assumptions id_saturation_is_not_admission.
Print Assumptions repeated_saturated_allocations_keep_refusing.
Print Assumptions coordinate_equality_is_full_tuple_equality.
Print Assumptions coordinate_membership_is_exact.
Print Assumptions parameter_reset_preserves_original_coordinates.
Print Assumptions unsupported_literal_kind_retains_panic_payload.
Print Assumptions leaves_skip_coordinate_advance.
Print Assumptions global_collision_returns_before_output_or_child_push.
Print Assumptions root_and_immediate_child_batches_are_not_preorder_ids.
Print Assumptions equal_valued_roots_keep_distinct_occurrence_handles.
Print Assumptions permitted_advance_reuses_existing_coordinate_walk.
Print Assumptions existing_coordinate_prefix_length_law_reused.

End FactoringForestWalkRelocation.
