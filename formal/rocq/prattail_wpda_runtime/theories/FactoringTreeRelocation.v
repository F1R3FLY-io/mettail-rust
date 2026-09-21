(** Exact module relocation of factoring.rs::finalize_leaf / build_tree.

    This boundary changes visibility/import paths ONLY. It has no reader,
    adapter, new grouping algorithm, or descriptor representation change. The
    full shared mathematical descriptors below therefore serve both modules;
    OriginalState and RelocatedState distinguish their module-local machines.
    Both execute the concrete Rust transcription core_step, not an unspecified
    parser supplied as a theorem premise. The proved claim is relocation
    isomorphism of finite executions, including all outputs and effect prefixes.

    Source ledger, macros/src/gen/runtime/wpda_codegen/factoring.rs:
    - SpineItem equality includes literal text AND required_top_cat, or parsed
      category AND cur_bp. IndexMap entry appends to an existing bucket; a new
      key is appended at its first occurrence. Hash iteration is not substituted.
    - CandidateMember preserves kind/rule/items/truncated/total_positions/
      body_src_idx/mixfix_coords. GroupMember preserves kind/rule/leaf_depth/
      typed commit/full position map/has_post_spine_remainder.
    - finalize_leaf records depth >= 255 first, then casts depth modulo 256.
      Binder uses depth_u8 + 1 and map d + 1; Nullary uses completed 0 and
      0..=depth_u8. Mixfix reads the ORIGINAL usize depth, records a missing
      coordinate after the depth refusal, substitutes (0,0,0), and returns the
      exact inclusive prefix or an empty map. Remainder uses uncast depth.
    - Task stack is represented top-first (Vec::last); values remains bottom-
      first, as the original Vec, so drain(value_base..) is skipn, concatenated
      in forward completion order. Enter with one member finalizes immediately.
    - Other Enter cases scan members in authored order. Exhausted members are
      finalized NOW, before any descendant task, or appended to interior_accepts
      in the false stance. Nonexhausted members use the original items[depth].
      If parts is empty, push accepts only. Otherwise push Assemble, then child
      Enter tasks in reverse. Assemble emits Interior(children) BEFORE accepts.
    - Empty initial member vectors, twins, both accept stances, truncated leaves,
      partial side effects, final pop, and assertion sites remain explicit.

    Arithmetic / failure scope: usize quantities use naturals with an explicit
    caller-supplied usize ceiling for depth + 1. The depth cast is modulo 256;
    a deep leaf can produce a refusal yet have a nonoverflowing Binder addition
    (e.g. depth 20001 casts to 33). arithmetic_ok tracks actual executed additions,
    NOT depth < 255. debug_ok tracks the original debug assertions. Invalid slice
    indices/drains/empty final pop are distinct faults, never fabricated forests.
    Faithful returning Rust executions lie in these execution domains. Outside
    them no debug-panic/release-wrap equivalence is claimed. These are proof
    instruments, not newly inserted Rust checks or proven runtime pre-admission.

    Refusals are exact constructor/interpoland events with the same LIMIT_REFUSAL
    prefix, in original order; applying the SAME Rust formatting operation to
    equal event lists preserves strings. Formatting internals, allocation,
    Drop/Debug lifecycle implementations, hash performance, Rust extraction,
    all-input termination, and a new trie semantics theorem are out of scope.
    The lifecycle code is moved verbatim and checked by its existing tests.

    Existing semantics: TrieLeafBijection / TrieLeafBijectionAccept prove the old
    recursive models' leaf/path/accounting laws; SpineSimulation[Accept] covers
    their static coordinates; MixfixSpineCommit covers its stated mixfix domain.
    We reuse finalize_commit and the two coordinate-coverage lemmas below.
    We DO NOT claim those recursive proofs certify this iterative Enter/Assemble
    loop: its relocation claim is proved directly here, and the existing
    factoring_tree_recursive_oracle tests remain the empirical bridge.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import TrieLeafBijection SpineSimulation.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module FactoringTreeRelocation.

Definition LIMIT_REFUSAL := "mettail: the S1 spine factoring cannot be encoded —".
Inductive SpineItem :=
| Literal (text : string) (required_top_cat : option nat)
| ParamParse (cat_src_idx cur_bp : nat).
Definition optional_index_eqb lhs rhs := match lhs, rhs with
| None, None => true | Some x, Some y => Nat.eqb x y | _, _ => false end.
Definition item_eqb lhs rhs := match lhs, rhs with
| Literal x guard_x, Literal y guard_y => String.eqb x y && optional_index_eqb guard_x guard_y
| ParamParse c b, ParamParse c' b' => Nat.eqb c c' && Nat.eqb b b'
| _, _ => false end.
Lemma optional_index_equality_exact : forall lhs rhs,
  optional_index_eqb lhs rhs = true <-> lhs = rhs.
Proof.
  intros [lhs|] [rhs|]; cbn [optional_index_eqb]; try rewrite Nat.eqb_eq;
    split; intros H; congruence.
Qed.
Theorem item_equality_preserves_full_action_shape : forall lhs rhs,
  item_eqb lhs rhs = true <-> lhs = rhs.
Proof.
  intros [text guard|cat bp] [text' guard'|cat' bp']; cbn [item_eqb];
    try (split; discriminate).
  - rewrite andb_true_iff, String.eqb_eq, optional_index_equality_exact.
    split; [intros [-> ->]; reflexivity|intros H; inversion H; auto].
  - rewrite andb_true_iff, !Nat.eqb_eq. split; [intros [-> ->]; reflexivity|intros H; inversion H; auto].
Qed.

Inductive MemberKind := Binder | Nullary | Mixfix.
Definition Coordinate := (nat * nat * nat)%type.
Record CandidateMember := {
  candidate_kind : MemberKind; candidate_rule : nat; candidate_items : list SpineItem;
  candidate_truncated : bool; candidate_total_positions : nat;
  candidate_body_src_idx : option nat; candidate_mixfix_coords : list Coordinate
}.
Inductive MemberCommit :=
| BinderCommit (rule_idx resume_pos : nat)
| NullaryCommit (rule_idx completed_idx sub_pos : nat)
| MixfixCommit (rule_idx kind completed_idx sub_pos : nat).
Inductive SpinePosMap :=
| BinderMap (pos_at_depth : list nat)
| NullaryMap (sub_pos_at_depth : list nat)
| MixfixMap (coords_at_depth : list Coordinate).
Record GroupMember := {
  group_kind : MemberKind; group_rule : nat; group_leaf_depth : nat;
  group_commit : MemberCommit; group_pos_map : SpinePosMap;
  group_has_post_spine_remainder : bool
}.
Inductive SpineTree :=
| Interior (item : SpineItem) (children : list SpineTree)
| Leaf (item : SpineItem) (member : GroupMember).

(** Constructor plus EVERY variable format argument. Constants in the actual
    messages, including depth limit 254 and LIMIT_REFUSAL, remain unchanged. *)
Inductive Refusal :=
| LeafDepthLimit (rule_idx leaf_depth addressable_depth : nat)
| MissingMixfixCoordinate (rule_idx recorded_count leaf_depth : nat).
Record Effects := {
  interior_accepts : list nat; refusals : list Refusal;
  arithmetic_ok : bool; debug_ok : bool
}.
Definition add_refusal event e :=
 {| interior_accepts := interior_accepts e; refusals := (refusals e ++ [event])%list;
    arithmetic_ok := arithmetic_ok e; debug_ok := debug_ok e |}.
Definition add_interior_accept rule_idx e :=
 {| interior_accepts := (interior_accepts e ++ [rule_idx])%list; refusals := refusals e;
    arithmetic_ok := arithmetic_ok e; debug_ok := debug_ok e |}.
Definition check_arithmetic holds e :=
 {| interior_accepts := interior_accepts e; refusals := refusals e;
    arithmetic_ok := arithmetic_ok e && holds; debug_ok := debug_ok e |}.
Definition check_debug holds e :=
 {| interior_accepts := interior_accepts e; refusals := refusals e;
    arithmetic_ok := arithmetic_ok e; debug_ok := debug_ok e && holds |}.

Definition cast_u8 depth := depth mod 256.
Definition finalize_leaf member depth e :=
  let checked_depth := if Nat.leb 255 depth
    then add_refusal (LeafDepthLimit (candidate_rule member) depth 254) e else e in
  let d := cast_u8 depth in
  let '(commit, pos_map, after) := match candidate_kind member with
  | Binder =>
      (BinderCommit (candidate_rule member) (S d),
       BinderMap (List.map S (seq 0 (S d))), check_arithmetic (Nat.ltb d 255) checked_depth)
  | Nullary =>
      (NullaryCommit (candidate_rule member) 0 d, NullaryMap (seq 0 (S d)), checked_depth)
  | Mixfix =>
      let '(coord, observed) := match nth_error (candidate_mixfix_coords member) depth with
      | Some coord => (coord, checked_depth)
      | None => ((0, 0, 0), add_refusal
          (MissingMixfixCoordinate (candidate_rule member) (List.length (candidate_mixfix_coords member)) depth)
          checked_depth) end in
      let '(kind, completed, sub_pos) := coord in
      (MixfixCommit (candidate_rule member) kind completed sub_pos,
       MixfixMap (if Nat.leb (S depth) (List.length (candidate_mixfix_coords member))
         then firstn (S depth) (candidate_mixfix_coords member) else []), observed)
  end in
  ({| group_kind := candidate_kind member; group_rule := candidate_rule member;
      group_leaf_depth := d; group_commit := commit; group_pos_map := pos_map;
      group_has_post_spine_remainder := candidate_truncated member || Nat.ltb depth (candidate_total_positions member) |}, after).

Theorem exact_cast_domain : forall depth, cast_u8 depth < 256.
Proof. intros; apply Nat.mod_upper_bound; lia. Qed.
Theorem bounded_cast_identity : forall depth, depth < 255 -> cast_u8 depth = depth.
Proof. intros; apply Nat.mod_small; lia. Qed.
Theorem deep_refusal_does_not_imply_addition_overflow :
  cast_u8 (200 * 100 + 1) = 33 /\ Nat.ltb (cast_u8 (200 * 100 + 1)) 255 = true /\
  Nat.leb 255 (200 * 100 + 1) = true.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** First-occurrence IndexMap semantics, preserving complete key equality and
    appending member values without any sort or deduplication. *)
Definition Parts := list (SpineItem * list CandidateMember).
Fixpoint add_to_parts item member (parts : Parts) : Parts := match parts with
| [] => [(item, [member])]
| (key, members) :: rest =>
    if item_eqb key item then (key, (members ++ [member])%list) :: rest
    else (key, members) :: add_to_parts item member rest end.
Theorem matching_bucket_keeps_its_position : forall item member members rest,
  add_to_parts item member ((item, members) :: rest) = (item, (members ++ [member])%list) :: rest.
Proof.
  intros. cbn [add_to_parts]. assert (item_eqb item item = true) as H.
  { apply item_equality_preserves_full_action_shape; reflexivity. }
  rewrite H; reflexivity.
Qed.
Theorem new_bucket_is_appended_at_first_occurrence : forall parts item member,
  Forall (fun entry => item_eqb (fst entry) item = false) parts ->
  add_to_parts item member parts = (parts ++ [(item, [member])])%list.
Proof.
  induction parts as [|[key members] rest IH]; intros item member H; [reflexivity|].
  inversion H as [|entry remaining Hkey Hrest]; subst.
  cbn [add_to_parts fst] in *. rewrite Hkey. rewrite IH; auto.
Qed.

Record ScanState := {
  scan_parts : Parts; scan_accepts : list SpineTree; scan_effects : Effects
}.
Inductive ScanResult :=
| Scanned (state : ScanState)
| InvalidMemberIndex (member : CandidateMember) (depth : nat) (state : ScanState).
Definition scan_state parts accepts e := {| scan_parts := parts; scan_accepts := accepts; scan_effects := e |}.
Fixpoint scan_members (accept_continue : bool) depth edge members state := match members with
| [] => Scanned state
| member :: rest =>
    if Nat.eqb (List.length (candidate_items member)) depth then
      if accept_continue then
        let '(leaf, after) := finalize_leaf member depth (scan_effects state) in
        scan_members accept_continue depth edge rest
          (scan_state (scan_parts state) (scan_accepts state ++ [Leaf edge leaf])%list after)
      else scan_members accept_continue depth edge rest
        (scan_state (scan_parts state) (scan_accepts state)
          (add_interior_accept (candidate_rule member) (scan_effects state)))
    else match nth_error (candidate_items member) depth with
      | Some item => scan_members accept_continue depth edge rest
          (scan_state (add_to_parts item member (scan_parts state)) (scan_accepts state) (scan_effects state))
      | None => InvalidMemberIndex member depth state end end.
Theorem original_unchecked_index_safe_on_its_invariant : forall member depth,
  depth <= List.length (candidate_items member) ->
  Nat.eqb (List.length (candidate_items member)) depth = false ->
  exists item, nth_error (candidate_items member) depth = Some item.
Proof.
  intros member depth Hbound Hneq. apply Nat.eqb_neq in Hneq.
  assert (depth < List.length (candidate_items member)) as Hlt by lia.
  apply (proj2 (nth_error_Some (candidate_items member) depth)) in Hlt.
  destruct (nth_error (candidate_items member) depth); [eauto|contradiction].
Qed.
Theorem parent_accept_is_finalized_before_remaining_members : forall depth edge member rest state,
  List.length (candidate_items member) = depth ->
  scan_members true depth edge (member :: rest) state =
  let '(leaf, after) := finalize_leaf member depth (scan_effects state) in
  scan_members true depth edge rest
    (scan_state (scan_parts state) (scan_accepts state ++ [Leaf edge leaf])%list after).
Proof. intros; cbn [scan_members]; rewrite H, Nat.eqb_refl; reflexivity. Qed.
Theorem false_stance_retains_accept_order_without_finalization : forall depth edge member rest state,
  List.length (candidate_items member) = depth ->
  scan_members false depth edge (member :: rest) state =
  scan_members false depth edge rest
    (scan_state (scan_parts state) (scan_accepts state)
      (add_interior_accept (candidate_rule member) (scan_effects state))).
Proof. intros; cbn [scan_members]; rewrite H, Nat.eqb_refl; reflexivity. Qed.

Inductive Task :=
| Enter (depth : nat) (edge : SpineItem) (members : list CandidateMember)
| Assemble (edge : SpineItem) (accepts : list SpineTree) (value_base : nat).
Record Configuration := {
  tasks : list Task; values : list (list SpineTree); effects : Effects
}.
Definition configure work completed e := {| tasks := work; values := completed; effects := e |}.
Definition child_tasks depth parts := List.map (fun part => Enter (S depth) (fst part) (snd part)) parts.
Theorem reversed_child_push_has_original_pop_order : forall depth parts pending,
  (rev (List.map (fun part => Enter (S depth) (fst part) (snd part)) (rev parts)) ++ pending)%list =
  (child_tasks depth parts ++ pending)%list.
Proof. intros; rewrite map_rev, rev_involutive; reflexivity. Qed.

Inductive Fault :=
| MemberIndexFault (member : CandidateMember) (depth : nat) (partial : ScanState)
| DrainOutOfBounds (value_base value_count : nat)
| EmptyFinalPop.
Inductive CoreStep :=
| Continue (next : Configuration)
| Finished (forest : list SpineTree) (after : Effects)
| Failed (reason : Fault) (at_failure : Configuration).

(** Exact Enter/Assemble body, shared solely because relocation leaves that
    body unchanged. There is no abstract step-function equality assumption. *)
Definition core_step usize_max accept_continue state :=
  let completed := values state in let e := effects state in
  match tasks state with
  | [] =>
      let checked := check_debug (Nat.eqb (List.length completed) 1) e in
      match rev completed with
      | forest :: _ => Finished forest checked
      | [] => Failed EmptyFinalPop (configure [] completed checked) end
  | Enter depth edge members :: pending =>
      match members with
      | [member] =>
          let '(leaf, after) := finalize_leaf member depth e in
          Continue (configure pending (completed ++ [[Leaf edge leaf]])%list after)
      | _ => match scan_members accept_continue depth edge members (scan_state [] [] e) with
          | InvalidMemberIndex member index partial =>
              Failed (MemberIndexFault member index partial) (configure pending completed (scan_effects partial))
          | Scanned scanned => match scan_parts scanned with
              | [] => Continue (configure pending (completed ++ [scan_accepts scanned])%list (scan_effects scanned))
              | _ :: _ => Continue (configure
                  (child_tasks depth (scan_parts scanned) ++
                    Assemble edge (scan_accepts scanned) (List.length completed) :: pending)%list
                  completed (check_arithmetic (Nat.ltb depth usize_max) (scan_effects scanned))) end end end
  | Assemble edge accepts value_base :: pending =>
      if Nat.leb value_base (List.length completed) then
        let children := List.concat (skipn value_base completed) in
        let checked := check_debug (negb (Nat.eqb (List.length children) 0)) e in
        let forest := Interior edge children :: accepts in
        Continue (configure pending (firstn value_base completed ++ [forest])%list checked)
      else Failed (DrainOutOfBounds value_base (List.length completed)) (configure pending completed e)
  end.

Theorem singleton_commits_before_any_partition : forall usize_max stance depth edge member pending completed e,
  core_step usize_max stance (configure (Enter depth edge [member] :: pending) completed e) =
  let '(leaf, after) := finalize_leaf member depth e in
  Continue (configure pending (completed ++ [[Leaf edge leaf]])%list after).
Proof. reflexivity. Qed.
Theorem assembly_preserves_drain_order_and_accepts_last : forall usize_max stance edge accepts base pending completed e,
  base <= List.length completed ->
  core_step usize_max stance (configure (Assemble edge accepts base :: pending) completed e) =
  let children := List.concat (skipn base completed) in
  Continue (configure pending
    (firstn base completed ++ [Interior edge children :: accepts])%list
    (check_debug (negb (Nat.eqb (List.length children) 0)) e)).
Proof.
  intros. unfold core_step; cbn [configure tasks values effects].
  assert (Nat.leb base (List.length completed) = true) as Hle by (apply Nat.leb_le; assumption).
  rewrite Hle; reflexivity.
Qed.
Theorem completed_children_are_spliced_in_forward_order : forall (first second : list SpineTree) remaining,
  List.concat (first :: second :: remaining) =
  (first ++ second ++ List.concat remaining)%list.
Proof. reflexivity. Qed.

(** Separate module-local wrappers around the unchanged descriptors/state. *)
Record OriginalState := { original_configuration : Configuration }.
Record RelocatedState := { relocated_configuration : Configuration }.
Definition relocate state := {| relocated_configuration := original_configuration state |}.
Inductive OriginalOutcome :=
| OriginalContinue (state : OriginalState)
| OriginalFinished (forest : list SpineTree) (after : Effects)
| OriginalFailed (reason : Fault) (state : OriginalState).
Inductive RelocatedOutcome :=
| RelocatedContinue (state : RelocatedState)
| RelocatedFinished (forest : list SpineTree) (after : Effects)
| RelocatedFailed (reason : Fault) (state : RelocatedState).
Definition original_step usize_max stance state :=
  match core_step usize_max stance (original_configuration state) with
  | Continue next => OriginalContinue {| original_configuration := next |}
  | Finished forest after => OriginalFinished forest after
  | Failed reason failed => OriginalFailed reason {| original_configuration := failed |} end.
Definition relocated_step usize_max stance state :=
  match core_step usize_max stance (relocated_configuration state) with
  | Continue next => RelocatedContinue {| relocated_configuration := next |}
  | Finished forest after => RelocatedFinished forest after
  | Failed reason failed => RelocatedFailed reason {| relocated_configuration := failed |} end.
Definition relocate_outcome outcome := match outcome with
| OriginalContinue state => RelocatedContinue (relocate state)
| OriginalFinished forest after => RelocatedFinished forest after
| OriginalFailed reason state => RelocatedFailed reason (relocate state) end.
Theorem exact_enter_assemble_step_relocation : forall usize_max stance state,
  relocated_step usize_max stance (relocate state) = relocate_outcome (original_step usize_max stance state).
Proof.
  intros usize_max stance [configuration]. unfold relocated_step, original_step, relocate; cbn.
  destruct (core_step usize_max stance configuration); reflexivity.
Qed.
Fixpoint original_execute fuel usize_max stance state := match fuel with
| 0 => OriginalContinue state
| S remaining => match original_step usize_max stance state with
    | OriginalContinue next => original_execute remaining usize_max stance next | other => other end end.
Fixpoint relocated_execute fuel usize_max stance state := match fuel with
| 0 => RelocatedContinue state
| S remaining => match relocated_step usize_max stance state with
    | RelocatedContinue next => relocated_execute remaining usize_max stance next | other => other end end.
Theorem finite_execution_preserves_full_forest_and_effect_prefix : forall fuel usize_max stance state,
  relocated_execute fuel usize_max stance (relocate state) =
  relocate_outcome (original_execute fuel usize_max stance state).
Proof.
  induction fuel; intros; cbn [relocated_execute original_execute]; [reflexivity|].
  rewrite exact_enter_assemble_step_relocation.
  destruct (original_step usize_max stance state); cbn [relocate_outcome]; auto.
Qed.
Definition initial depth edge members accepts prior_refusals :=
 {| original_configuration := configure [Enter depth edge members] []
      {| interior_accepts := accepts; refusals := prior_refusals; arithmetic_ok := true; debug_ok := true |} |}.
Theorem original_build_tree_entry_relocation : forall fuel usize_max stance depth edge members accepts prior_refusals,
  relocated_execute fuel usize_max stance (relocate (initial depth edge members accepts prior_refusals)) =
  relocate_outcome (original_execute fuel usize_max stance (initial depth edge members accepts prior_refusals)).
Proof. intros; apply finite_execution_preserves_full_forest_and_effect_prefix. Qed.

Definition outcome_effects result := match result with
| OriginalContinue state | OriginalFailed _ state => effects (original_configuration state)
| OriginalFinished _ after => after end.
Definition relocated_outcome_effects result := match result with
| RelocatedContinue state | RelocatedFailed _ state => effects (relocated_configuration state)
| RelocatedFinished _ after => after end.
Corollary refusal_strings_preserved_under_original_formatter : forall fuel usize_max stance state (render : Refusal -> string),
  List.map render (refusals (relocated_outcome_effects
    (relocated_execute fuel usize_max stance (relocate state)))) =
  List.map render (refusals (outcome_effects (original_execute fuel usize_max stance state))).
Proof.
  intros. rewrite finite_execution_preserves_full_forest_and_effect_prefix.
  destruct (original_execute fuel usize_max stance state); reflexivity.
Qed.
Definition returning_domain result := match result with
| OriginalFinished _ after => arithmetic_ok after && debug_ok after
| _ => false end.
Corollary faithful_returning_domain_is_preserved : forall fuel usize_max stance state,
  returning_domain (original_execute fuel usize_max stance state) = true ->
  relocated_execute fuel usize_max stance (relocate state) =
  relocate_outcome (original_execute fuel usize_max stance state).
Proof. intros; apply finite_execution_preserves_full_forest_and_effect_prefix. Qed.

(** Narrow, direct reuse of the existing static-coordinate laws. This projection
    forgets item shapes solely because finalize_commit never observes them;
    it is NOT a projection of the new iterative tree into the recursive builder. *)
Definition legacy_member member kind :=
 {| m_rule := candidate_rule member; m_kind := kind; m_items := [];
    m_total := candidate_total_positions member; m_trunc := candidate_truncated member |}.
Definition legacy_commit commit := match commit with
| CBinder rule_idx position => BinderCommit rule_idx position
| CNullary rule_idx completed sub_pos => NullaryCommit rule_idx completed sub_pos end.
Theorem binder_leaf_reuses_existing_commit_coordinates : forall member depth e,
  candidate_kind member = Binder -> depth < 255 ->
  group_commit (fst (finalize_leaf member depth e)) =
  legacy_commit (finalize_commit (legacy_member member KBinder) depth).
Proof.
  intros member depth e Hkind Hbound. unfold finalize_leaf. rewrite Hkind.
  rewrite bounded_cast_identity by assumption. reflexivity.
Qed.
Theorem nullary_leaf_reuses_existing_commit_coordinates : forall member depth e,
  candidate_kind member = Nullary -> depth < 255 ->
  group_commit (fst (finalize_leaf member depth e)) =
  legacy_commit (finalize_commit (legacy_member member KNullary) depth).
Proof.
  intros member depth e Hkind Hbound. unfold finalize_leaf. rewrite Hkind.
  rewrite bounded_cast_identity by assumption. reflexivity.
Qed.
Theorem existing_binder_coordinate_coverage_reused : forall depth total,
  depth <= total -> (seq 1 depth ++ seq (binder_pos_at depth) (total - depth))%list = seq 1 total.
Proof. exact commit_alignment_binder. Qed.
Theorem existing_nullary_coordinate_coverage_reused : forall depth total,
  depth <= total -> (seq 0 depth ++ seq (nullary_sub_pos_at depth) (total - depth))%list = seq 0 total.
Proof. exact commit_alignment_nullary. Qed.

Print Assumptions item_equality_preserves_full_action_shape.
Print Assumptions new_bucket_is_appended_at_first_occurrence.
Print Assumptions original_unchecked_index_safe_on_its_invariant.
Print Assumptions parent_accept_is_finalized_before_remaining_members.
Print Assumptions false_stance_retains_accept_order_without_finalization.
Print Assumptions reversed_child_push_has_original_pop_order.
Print Assumptions assembly_preserves_drain_order_and_accepts_last.
Print Assumptions exact_enter_assemble_step_relocation.
Print Assumptions finite_execution_preserves_full_forest_and_effect_prefix.
Print Assumptions original_build_tree_entry_relocation.
Print Assumptions refusal_strings_preserved_under_original_formatter.
Print Assumptions faithful_returning_domain_is_preserved.
Print Assumptions binder_leaf_reuses_existing_commit_coordinates.
Print Assumptions nullary_leaf_reuses_existing_commit_coordinates.
Print Assumptions existing_binder_coordinate_coverage_reused.
Print Assumptions existing_nullary_coordinate_coverage_reused.

End FactoringTreeRelocation.
