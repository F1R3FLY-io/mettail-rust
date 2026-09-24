(* The existing iterative traversal is relocated, not replaced.  This model
   closes its marker-table interface: original optional-then-list row order,
   dense IDs, last-write coordinate lookup, checked source widths, and local
   reverse-push scheduling.  BinderTraversalFrames supplies continuation laws;
   the bounded Rust recursive oracle checks the unchanged forest traversal.
   No claim is made that this file extracts or verifies Rust allocation. *)
From Stdlib Require Import List Arith Lia NArith.
From PrattailWpdaRuntime Require Import BinderTraversalFrames.
Import ListNotations.

Module TraversalMarkerProjection.
Module B := BinderTraversalFrames.

Record Site := { site_index : nat; site_length : nat }.

Definition optional_rows (cat rule : nat) (s : Site) : list B.MarkerMetadata :=
  map (fun sub => B.Build_MarkerMetadata cat rule
       (B.OptionalCoordinate (site_index s) sub))
      (seq 0 (S (S (site_length s)))).

Definition binder_rows (cat rule : nat) (s : Site) : list B.MarkerMetadata :=
  map (fun sub => B.Build_MarkerMetadata cat rule
       (B.BinderListCoordinate (site_index s) sub))
      (seq 0 (S (S (site_length s)))).

Definition rule_rows (cat rule : nat) (optionals binders : list Site) :=
  flat_map (optional_rows cat rule) optionals ++
  flat_map (binder_rows cat rule) binders.

Theorem optional_marker_count : forall cat rule s,
  length (optional_rows cat rule s) = S (S (site_length s)).
Proof. intros; unfold optional_rows; rewrite map_length, seq_length; reflexivity. Qed.

Theorem binder_marker_count : forall cat rule s,
  length (binder_rows cat rule s) = S (S (site_length s)).
Proof. intros; unfold binder_rows; rewrite map_length, seq_length; reflexivity. Qed.

Theorem optional_rows_before_binder_rows : forall cat rule os bs,
  firstn (length (flat_map (optional_rows cat rule) os))
    (rule_rows cat rule os bs) = flat_map (optional_rows cat rule) os.
Proof.
  intros; unfold rule_rows; rewrite firstn_app, firstn_all, Nat.sub_diag.
  simpl; rewrite app_nil_r; reflexivity.
Qed.

Definition metadata_eq_dec : forall (x y : B.MarkerMetadata), {x = y} + {x <> y}.
Proof. decide equality; try apply Nat.eq_dec; decide equality; apply Nat.eq_dec. Defined.

(* HashMap::insert overwrites an earlier equal coordinate.  Dense metadata
   still contains both occurrences.  Lookup therefore selects the LAST row,
   not a first-occurrence or duplicate-rejecting interpretation. *)
Fixpoint last_id (wanted : B.MarkerMetadata) (rows : list B.MarkerMetadata)
  : option nat :=
  match rows with
  | [] => None
  | row :: tail =>
      match last_id wanted tail with
      | Some n => Some (S n)
      | None => if metadata_eq_dec wanted row then Some 0 else None
      end
  end.

Theorem last_id_decodes_exact_coordinate : forall rows wanted n,
  last_id wanted rows = Some n -> nth_error rows n = Some wanted.
Proof.
  induction rows as [|row tail IH]; intros wanted n H; simpl in H.
  - discriminate.
  - destruct (last_id wanted tail) as [k|] eqn:E.
    + inversion H; subst; simpl; eapply IH; exact E.
    + destruct (metadata_eq_dec wanted row) as [Eq|Neq].
      * inversion H; subst; simpl; reflexivity.
      * discriminate.
Qed.

Theorem generated_finite_table_roundtrip : forall cat rule os bs wanted n,
  last_id wanted (rule_rows cat rule os bs) = Some n ->
  nth_error (rule_rows cat rule os bs) n = Some wanted.
Proof. intros; eapply last_id_decodes_exact_coordinate; eassumption. Qed.

Theorem finite_table_ids_injective : forall rows x y n,
  last_id x rows = Some n -> last_id y rows = Some n -> x = y.
Proof.
  intros rows x y n Hx Hy.
  pose proof (last_id_decodes_exact_coordinate rows x n Hx) as X.
  pose proof (last_id_decodes_exact_coordinate rows y n Hy) as Y.
  rewrite X in Y; inversion Y; reflexivity.
Qed.

Definition max8 : N := 255.
Definition max16 : N := 65535.
Definition max32 : N := 4294967295.
Definition checked_width (maximum value : N) : option N :=
  if (value <=? maximum)%N then Some value else None.

Theorem checked_width_exact : forall maximum value result,
  checked_width maximum value = Some result ->
  result = value /\ (value <= maximum)%N.
Proof.
  intros maximum value result; unfold checked_width.
  destruct (value <=? maximum)%N eqn:E; intro H; try discriminate.
  inversion H; subst; split; auto; apply N.leb_le; exact E.
Qed.

Theorem representable_cast_is_identity : forall maximum value,
  (value <= maximum)%N -> N.modulo value (maximum + 1) = value.
Proof. intros; apply N.mod_small; lia. Qed.

Definition rule_resume (index : N) := checked_width max8 (index + 2).
Definition optional_resume (index : N) := checked_width max32 (index + 2).
Definition binder_resume (index last : N) :=
  if N.eqb index last then Some 0%N else optional_resume index.

Theorem rule_resume_boundary : forall i,
  (i <= 253)%N -> rule_resume i = Some (i + 2)%N.
Proof.
  intros i H; unfold rule_resume, checked_width, max8.
  assert (E : (i + 2 <=? 255)%N = true) by (apply N.leb_le; lia).
  rewrite E; reflexivity.
Qed.

Theorem binder_last_resumes_zero : forall i, binder_resume i i = Some 0%N.
Proof. intros; unfold binder_resume; rewrite N.eqb_refl; reflexivity. Qed.

(* A marker is inserted only AFTER next_marker_id.checked_add(1) succeeds.
   Thus max32 itself is not publishable, even for the last row. *)
Definition next_marker (n : N) : option N := checked_width max32 (n + 1).
Fixpoint allocate_rows (rows : list B.MarkerMetadata) (next : N)
  : option (list (N * B.MarkerMetadata) * N) :=
  match rows with
  | [] => Some ([], next)
  | row :: tail =>
      match next_marker next with
      | None => None
      | Some after =>
          match allocate_rows tail after with
          | None => None
          | Some (out, final) => Some ((next, row) :: out, final)
          end
      end
  end.

Theorem allocation_preserves_all_rows : forall rows next output final,
  allocate_rows rows next = Some (output, final) -> map snd output = rows.
Proof.
  induction rows as [|row tail IH]; intros next output final H; simpl in H.
  - inversion H; reflexivity.
  - destruct (next_marker next) as [after|] eqn:E; try discriminate.
    destruct (allocate_rows tail after) as [[rest finish]|] eqn:T; try discriminate.
    inversion H; subst; simpl; f_equal; eapply IH; exact T.
Qed.

Theorem allocation_advances_by_row_count : forall rows next output final,
  allocate_rows rows next = Some (output, final) ->
  final = (next + N.of_nat (length rows))%N.
Proof.
  induction rows as [|row tail IH]; intros next output final H; simpl in H.
  - inversion H; subst; simpl; rewrite N.add_0_r; reflexivity.
  - destruct (next_marker next) as [after|] eqn:E; try discriminate.
    destruct (allocate_rows tail after) as [[rest finish]|] eqn:T; try discriminate.
    inversion H; subst.
    specialize (IH after rest final T).
    unfold next_marker in E; apply checked_width_exact in E; destruct E as [E _].
    change (final = next + N.of_nat (S (length tail)))%N.
    rewrite Nat2N.inj_succ; lia.
Qed.

Theorem first_marker_failure_has_no_partial_table : forall row tail next,
  next_marker next = None -> allocate_rows (row :: tail) next = None.
Proof. intros; simpl; rewrite H; reflexivity. Qed.

Theorem suffix_failure_has_no_partial_table : forall row tail next after,
  next_marker next = Some after -> allocate_rows tail after = None ->
  allocate_rows (row :: tail) next = None.
Proof. intros; simpl; rewrite H, H0; reflexivity. Qed.

Theorem allocated_row_has_dense_id : forall rows next output final index metadata,
  allocate_rows rows next = Some (output, final) ->
  nth_error rows index = Some metadata ->
  nth_error output index = Some ((next + N.of_nat index)%N, metadata).
Proof.
  induction rows as [|row tail IH]; intros next output final index metadata H Row.
  - destruct index; discriminate Row.
  - simpl in H.
    destruct (next_marker next) as [after|] eqn:E; try discriminate.
    destruct (allocate_rows tail after) as [[rest finish]|] eqn:T; try discriminate.
    inversion H; subst output finish.
    destruct index as [|index].
    + simpl in Row; inversion Row; subst metadata; simpl; rewrite N.add_0_r; reflexivity.
    + simpl in Row; simpl nth_error.
      specialize (IH after rest final index metadata T Row).
      rewrite IH.
      unfold next_marker in E; apply checked_width_exact in E; destruct E as [E _].
      rewrite Nat2N.inj_succ; f_equal; f_equal; lia.
Qed.

Theorem allocated_generated_table_roundtrip : forall cat rule os bs output final wanted index,
  allocate_rows (rule_rows cat rule os bs) 0%N = Some (output, final) ->
  last_id wanted (rule_rows cat rule os bs) = Some index ->
  nth_error output index = Some (N.of_nat index, wanted).
Proof.
  intros cat rule os bs output final wanted index Alloc Lookup.
  pose proof (generated_finite_table_roundtrip cat rule os bs wanted index Lookup) as Row.
  pose proof (allocated_row_has_dense_id (rule_rows cat rule os bs) 0%N
    output final index wanted Alloc Row) as H.
  rewrite N.add_0_l in H; exact H.
Qed.

(* Worklist append denotes repeated push; its reversal denotes pop order. *)
Theorem reverse_push_visits_children_before_pending : forall (A : Type)
  (children pending : list A),
  rev (pending ++ rev children) = children ++ rev pending.
Proof. intros; rewrite rev_app_distr, rev_involutive; reflexivity. Qed.

Print Assumptions generated_finite_table_roundtrip.
Print Assumptions finite_table_ids_injective.
Print Assumptions checked_width_exact.
Print Assumptions representable_cast_is_identity.
Print Assumptions allocation_preserves_all_rows.
Print Assumptions allocation_advances_by_row_count.
Print Assumptions first_marker_failure_has_no_partial_table.
Print Assumptions suffix_failure_has_no_partial_table.
Print Assumptions allocated_row_has_dense_id.
Print Assumptions allocated_generated_table_roundtrip.
Print Assumptions reverse_push_visits_children_before_pending.
End TraversalMarkerProjection.
