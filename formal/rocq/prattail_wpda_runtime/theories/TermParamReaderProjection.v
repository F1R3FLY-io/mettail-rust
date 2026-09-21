(** Source correspondence for the ORIGINAL TermParamLeaves iterator.

    Ledger: macros/src/gen/term_param_walk.rs, read in full before modeling.
    - new collects reversed authored parameters with the inherited flag.
    - next pops one (original parameter handle, flag). The first observation
      tests Optional; its children are reverse-pushed with true, then continue.
    - A nonoptional parameter is observed again by the original match. The leaf
      retains its original handle, variant, names, type handle and inherited
      flag. The second Optional arm continues without yielding.
    - Work below has its top at the HEAD, corresponding to Vec::last. The
      reversal lemma relates this representation to the actual reverse-push.
    - Source steps read authored child slices directly. Reader steps enumerate
      valid slice indices and make shallow observations. Their correspondence
      is proved from distinct stores, not assumed as iterator equality.

    Names, types, parameters and sequences are opaque nat handles here. No type
    traversal, name conversion, syntax reconstruction or leaf preprocessing is
    modeled or needed. The projection store is a mathematical witness, not an
    allocated Rust tree. Observation traces retain the two original access
    sites even though a valid reader is immutable and observationally pure.

    Scope: this is a reviewed Rust transcription and finite-run simulation,
    not extraction or verification of arbitrary reader implementations. The
    invalid-reader outcome models an impossible indexing failure on the lawful
    stores. No allocation, panic/unwind, borrowed-lifetime, all-input termination
    or classifier theorem is asserted. Cyclic abstract stores are permitted;
    finite execution equivalence does not pretend they terminate. The separate
    ancestry relation identifies the root/optional origin of each yielded flag.
*)
From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
Set Implicit Arguments.

Module TermParamReaderProjection.

Inductive SourceParam :=
| SSimple (name ty : nat)
| SGuardBody (name : nat)
| SAbstraction (binder body ty : nat)
| SMultiAbstraction (binder body ty : nat)
| SOptional (parameters : nat).

Inductive TermObservation :=
| Simple (name ty : nat)
| GuardBody (name : nat)
| Abstraction (binder body ty : nat)
| MultiAbstraction (binder body ty : nat)
| Optional (parameters : nat).

Definition project_param p := match p with
| SSimple name ty => Simple name ty
| SGuardBody name => GuardBody name
| SAbstraction binder body ty => Abstraction binder body ty
| SMultiAbstraction binder body ty => MultiAbstraction binder body ty
| SOptional parameters => Optional parameters end.

Record SourceStore := {
  source_parameters : nat -> list nat;
  source_param : nat -> SourceParam
}.
Record ViewStore := {
  view_parameters : nat -> list nat;
  view_param : nat -> TermObservation
}.
Definition project_store store :=
 {| view_parameters := source_parameters store;
    view_param := fun handle => project_param (source_param store handle) |}.

Record Reader := {
  params_len : nat -> nat;
  param_at : nat -> nat -> option nat;
  param : nat -> TermObservation
}.
Definition source_reader store :=
 {| params_len := fun handle => length (source_parameters store handle);
    param_at := fun handle => nth_error (source_parameters store handle);
    param := fun handle => project_param (source_param store handle) |}.
Definition view_reader store :=
 {| params_len := fun handle => length (view_parameters store handle);
    param_at := fun handle => nth_error (view_parameters store handle);
    param := view_param store |}.

Theorem sequence_length_correspondence : forall store handle,
  params_len (view_reader (project_store store)) handle =
  params_len (source_reader store) handle.
Proof. reflexivity. Qed.
Theorem sequence_index_correspondence : forall store handle index,
  param_at (view_reader (project_store store)) handle index =
  param_at (source_reader store) handle index.
Proof. reflexivity. Qed.
Theorem shallow_parameter_correspondence : forall store handle,
  param (view_reader (project_store store)) handle =
  project_param (source_param store handle).
Proof. reflexivity. Qed.

Theorem all_payload_handles_preserved : forall name ty binder body children,
  project_param (SSimple name ty) = Simple name ty /\
  project_param (SGuardBody name) = GuardBody name /\
  project_param (SAbstraction binder body ty) = Abstraction binder body ty /\
  project_param (SMultiAbstraction binder body ty) =
    MultiAbstraction binder body ty /\
  project_param (SOptional children) = Optional children.
Proof. intros; repeat split; reflexivity. Qed.

Definition ReaderValid reader := forall handle index,
  param_at reader handle index <> None <-> index < params_len reader handle.
Theorem source_reader_valid : forall store, ReaderValid (source_reader store).
Proof. intros store handle index; unfold source_reader; cbn; apply nth_error_Some. Qed.
Theorem view_reader_valid : forall store, ReaderValid (view_reader store).
Proof. intros store handle index; unfold view_reader; cbn; apply nth_error_Some. Qed.

(** The actual adapter visits (0..len).rev(). No reverse index can fail. *)
Theorem reversed_index_in_bounds : forall size index,
  In index (rev (seq 0 size)) -> index < size.
Proof.
  intros size index Hin. apply in_rev in Hin. apply in_seq in Hin. lia.
Qed.
Theorem reversed_reader_access_safe : forall reader handle index,
  ReaderValid reader -> In index (rev (seq 0 (params_len reader handle))) ->
  exists original, param_at reader handle index = Some original.
Proof.
  intros reader handle index Hvalid Hin.
  pose proof (@reversed_index_in_bounds (params_len reader handle) index Hin) as Hbound.
  apply (proj2 (Hvalid handle index)) in Hbound.
  destruct (param_at reader handle index) as [original|]; [eauto|contradiction].
Qed.

Fixpoint collect_present (items : list (option nat)) : option (list nat) :=
  match items with
  | [] => Some []
  | None :: _ => None
  | Some item :: rest =>
      match collect_present rest with
      | None => None
      | Some handles => Some (item :: handles)
      end
  end.
Definition read_parameters reader handle :=
  collect_present
    (map (param_at reader handle) (seq 0 (params_len reader handle))).

Lemma seq_successor : forall size start,
  seq (S start) size = map S (seq start size).
Proof.
  induction size as [|size IH]; intros start; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
Lemma enumerate_authored_parameters : forall handles,
  map (nth_error handles) (seq 0 (length handles)) = map (@Some nat) handles.
Proof.
  induction handles as [|handle rest IH]; cbn; [reflexivity|].
  rewrite seq_successor, map_map.
  change (Some handle :: map (nth_error rest) (seq 0 (length rest)) =
    Some handle :: map (@Some nat) rest).
  rewrite IH. reflexivity.
Qed.
Lemma collect_all_present : forall handles,
  collect_present (map (@Some nat) handles) = Some handles.
Proof. induction handles; cbn; [reflexivity|rewrite IHhandles; reflexivity]. Qed.
Theorem indexed_reverse_push_exact : forall store handle,
  map (param_at (view_reader (project_store store)) handle)
    (rev (seq 0 (params_len (view_reader (project_store store)) handle))) =
  map (@Some nat) (rev (source_parameters store handle)).
Proof.
  intros. change (map (nth_error (source_parameters store handle))
    (rev (seq 0 (length (source_parameters store handle)))) =
    map (@Some nat) (rev (source_parameters store handle))).
  rewrite map_rev, enumerate_authored_parameters, map_rev. reflexivity.
Qed.
Theorem source_read_parameters_exact : forall store handle,
  read_parameters (source_reader store) handle = Some (source_parameters store handle).
Proof.
  intros. unfold read_parameters, source_reader; cbn.
  rewrite enumerate_authored_parameters. apply collect_all_present.
Qed.
Theorem view_read_parameters_exact : forall store handle,
  read_parameters (view_reader (project_store store)) handle =
  Some (source_parameters store handle).
Proof. apply source_read_parameters_exact. Qed.

Definition Work := list (nat * bool).
Definition tagged (handles : list nat) inherited : Work :=
  map (fun handle => (handle, inherited)) handles.

(** A physical Vec stores bottom first; reversing it exposes the pop order. *)
Theorem original_reverse_push_order : forall handles inherited,
  rev (map (fun handle => (handle, inherited)) (rev handles)) =
  tagged handles inherited.
Proof.
  intros. rewrite map_rev, rev_involutive. reflexivity.
Qed.
Definition source_initial store root inherited :=
  tagged (source_parameters store root) inherited.
Definition reader_initial reader root inherited :=
  option_map (fun handles => tagged handles inherited) (read_parameters reader root).
Theorem initial_worklist_correspondence : forall store root inherited,
  reader_initial (view_reader (project_store store)) root inherited =
  Some (source_initial store root inherited).
Proof.
  intros. unfold reader_initial. rewrite view_read_parameters_exact. reflexivity.
Qed.
Theorem root_preorder : forall store root inherited index handle,
  nth_error (source_parameters store root) index = Some handle ->
  nth_error (source_initial store root inherited) index = Some (handle, inherited).
Proof.
  intros store root inherited index handle H.
  unfold source_initial, tagged. rewrite nth_error_map, H. reflexivity.
Qed.

Inductive LeafKind :=
| LSimple (original name ty : nat)
| LGuardBody (original name : nat)
| LAbstraction (original binder body ty : nat)
| LMultiAbstraction (original binder body ty : nat).
Record Leaf := { kind : LeafKind; is_optional : bool }.
Definition original_handle leaf := match kind leaf with
| LSimple original _ _ | LGuardBody original _
| LAbstraction original _ _ _ | LMultiAbstraction original _ _ _ => original end.

Inductive Step :=
| Done
| Continue (remaining : Work) (observations : list nat)
| Yield (leaf : Leaf) (remaining : Work) (observations : list nat)
| InvalidReader.

Definition source_step store (work : Work) := match work with
| [] => Done
| (original, inherited) :: rest =>
  match source_param store original with
  | SOptional children => Continue (tagged (source_parameters store children) true ++ rest) [original]
  | _ => match source_param store original with
    | SSimple name ty => Yield {| kind := LSimple original name ty; is_optional := inherited |} rest [original; original]
    | SGuardBody name => Yield {| kind := LGuardBody original name; is_optional := inherited |} rest [original; original]
    | SAbstraction binder body ty => Yield {| kind := LAbstraction original binder body ty; is_optional := inherited |} rest [original; original]
    | SMultiAbstraction binder body ty => Yield {| kind := LMultiAbstraction original binder body ty; is_optional := inherited |} rest [original; original]
    | SOptional _ => Continue rest [original; original]
    end
  end
end.

Definition reader_step reader (work : Work) := match work with
| [] => Done
| (original, inherited) :: rest =>
  match param reader original with
  | Optional children => match read_parameters reader children with
    | Some handles => Continue (tagged handles true ++ rest) [original]
    | None => InvalidReader end
  | _ => match param reader original with
    | Simple name ty => Yield {| kind := LSimple original name ty; is_optional := inherited |} rest [original; original]
    | GuardBody name => Yield {| kind := LGuardBody original name; is_optional := inherited |} rest [original; original]
    | Abstraction binder body ty => Yield {| kind := LAbstraction original binder body ty; is_optional := inherited |} rest [original; original]
    | MultiAbstraction binder body ty => Yield {| kind := LMultiAbstraction original binder body ty; is_optional := inherited |} rest [original; original]
    | Optional _ => Continue rest [original; original]
    end
  end
end.

Theorem original_step_correspondence : forall store work,
  reader_step (view_reader (project_store store)) work = source_step store work.
Proof.
  intros store [|[original inherited] rest]; [reflexivity|].
  unfold reader_step, source_step.
  change (param (view_reader (project_store store)) original)
    with (project_param (source_param store original)).
  destruct (source_param store original); cbn [project_param]; try reflexivity.
  rewrite view_read_parameters_exact. reflexivity.
Qed.

(** One bounded next() call: Continue stays inside next; Yield returns its exact
    leaf and residual work. Exhaustion is a proof instrument, not a Rust API. *)
Inductive NextResult :=
| NextDone (observations : list nat)
| NextYield (leaf : Leaf) (remaining : Work) (observations : list nat)
| NextExhausted (remaining : Work) (observations : list nat)
| NextInvalid (remaining : Work) (observations : list nat).
Definition prepend_trace trace result := match result with
| NextDone seen => NextDone (trace ++ seen)
| NextYield leaf rest seen => NextYield leaf rest (trace ++ seen)
| NextExhausted rest seen => NextExhausted rest (trace ++ seen)
| NextInvalid rest seen => NextInvalid rest (trace ++ seen) end.
Fixpoint next_with_fuel (step : Work -> Step) fuel work := match fuel with
| 0 => NextExhausted work []
| S remaining => match step work with
  | Done => NextDone []
  | Continue rest trace => prepend_trace trace (next_with_fuel step remaining rest)
  | Yield leaf rest trace => NextYield leaf rest trace
  | InvalidReader => NextInvalid work [] end
end.
Theorem finite_next_preserves_yield_rest_and_trace : forall fuel store work,
  next_with_fuel (reader_step (view_reader (project_store store))) fuel work =
  next_with_fuel (source_step store) fuel work.
Proof.
  induction fuel as [|fuel IH]; intros store work; cbn [next_with_fuel]; [reflexivity|].
  rewrite original_step_correspondence.
  destruct (source_step store work); try reflexivity. rewrite IH. reflexivity.
Qed.

(** These local order laws apply at EVERY optional expansion. Together with
    pop-at-head and the finite-run theorem, they preserve authored depth-first
    preorder, including repeated handles and empty optional groups. *)
Theorem optional_children_before_siblings : forall store original inherited rest children,
  source_param store original = SOptional children ->
  source_step store ((original, inherited) :: rest) =
  Continue (tagged (source_parameters store children) true ++ rest) [original].
Proof. intros; unfold source_step; rewrite H; reflexivity. Qed.
Theorem optional_child_preorder : forall handles rest index child,
  nth_error handles index = Some child ->
  nth_error (tagged handles true ++ rest) index = Some (child, true).
Proof.
  intros handles rest index child H. rewrite nth_error_app1.
  - unfold tagged. rewrite nth_error_map, H. reflexivity.
  - unfold tagged. rewrite length_map. apply nth_error_Some. rewrite H. discriminate.
Qed.
Theorem nonoptional_yield_retains_origin : forall store original inherited rest leaf remaining seen,
  source_step store ((original, inherited) :: rest) = Yield leaf remaining seen ->
  original_handle leaf = original /\ is_optional leaf = inherited /\
  remaining = rest /\ seen = [original; original].
Proof.
  intros store original inherited rest leaf remaining seen H.
  unfold source_step in H. destruct (source_param store original);
    inversion H; subst; cbn; repeat split; reflexivity.
Qed.

(** Reachability carries the inherited flag through authored parentage. Every
    Optional edge sets it to true; ordinary leaves retain that flag unchanged. *)
Inductive Origin store root inherited : nat -> bool -> Prop :=
| RootOrigin : forall original,
    In original (source_parameters store root) -> Origin store root inherited original inherited
| OptionalOrigin : forall parent parent_flag children original,
    Origin store root inherited parent parent_flag ->
    source_param store parent = SOptional children ->
    In original (source_parameters store children) -> Origin store root inherited original true.
Definition WorkOrigin store root inherited (work : Work) :=
  Forall (fun entry => Origin store root inherited (fst entry) (snd entry)) work.
Theorem initial_ancestry : forall store root inherited,
  WorkOrigin store root inherited (source_initial store root inherited).
Proof.
  intros. unfold WorkOrigin, source_initial, tagged. apply Forall_forall.
  intros entry Hin. apply in_map_iff in Hin.
  destruct Hin as [original [Heq Hin]]. subst entry. cbn. constructor. exact Hin.
Qed.
Theorem optional_expansion_preserves_ancestry : forall store root inherited original flag rest children,
  WorkOrigin store root inherited ((original, flag) :: rest) ->
  source_param store original = SOptional children ->
  WorkOrigin store root inherited (tagged (source_parameters store children) true ++ rest).
Proof.
  intros store root inherited original flag rest children Hwork Hchildren.
  inversion Hwork as [|entry remaining Horigin Hrest]; subst.
  unfold WorkOrigin. apply Forall_app. split; [|exact Hrest].
  unfold tagged. apply Forall_forall. intros entry Hin.
  apply in_map_iff in Hin. destruct Hin as [child [Heq Hin]]. subst entry; cbn.
  eapply OptionalOrigin; [exact Horigin|exact Hchildren|exact Hin].
Qed.
Theorem source_step_preserves_ancestry : forall store root inherited work,
  WorkOrigin store root inherited work ->
  match source_step store work with
  | Done => True
  | Continue rest _ => WorkOrigin store root inherited rest
  | Yield leaf rest _ =>
      Origin store root inherited (original_handle leaf) (is_optional leaf) /\
      WorkOrigin store root inherited rest
  | InvalidReader => False end.
Proof.
  intros store root inherited [|[original flag] rest] Hwork; [exact I|].
  inversion Hwork as [|entry remaining Horigin Hrest]; subst.
  unfold source_step. destruct (source_param store original) eqn:Hparam; cbn.
  - split; assumption.
  - split; assumption.
  - split; assumption.
  - split; assumption.
  - eapply optional_expansion_preserves_ancestry; eauto.
Qed.
Theorem finite_next_preserves_ancestry : forall fuel store root inherited work,
  WorkOrigin store root inherited work ->
  match next_with_fuel (source_step store) fuel work with
  | NextDone _ => True
  | NextYield leaf rest _ =>
      Origin store root inherited (original_handle leaf) (is_optional leaf) /\
      WorkOrigin store root inherited rest
  | NextExhausted rest _ => WorkOrigin store root inherited rest
  | NextInvalid _ _ => False end.
Proof.
  induction fuel as [|fuel IH]; intros store root inherited work Hwork;
    cbn [next_with_fuel]; [exact Hwork|].
  pose proof (source_step_preserves_ancestry Hwork) as Hstep.
  destruct (source_step store work) as [|rest seen|leaf rest seen|]; cbn in Hstep; try exact Hstep.
  specialize (IH store root inherited rest Hstep).
  destruct (next_with_fuel (source_step store) fuel rest); exact IH.
Qed.

Print Assumptions sequence_length_correspondence.
Print Assumptions sequence_index_correspondence.
Print Assumptions shallow_parameter_correspondence.
Print Assumptions all_payload_handles_preserved.
Print Assumptions reversed_reader_access_safe.
Print Assumptions indexed_reverse_push_exact.
Print Assumptions original_reverse_push_order.
Print Assumptions initial_worklist_correspondence.
Print Assumptions original_step_correspondence.
Print Assumptions finite_next_preserves_yield_rest_and_trace.
Print Assumptions root_preorder.
Print Assumptions optional_children_before_siblings.
Print Assumptions optional_child_preorder.
Print Assumptions nonoptional_yield_retains_origin.
Print Assumptions initial_ancestry.
Print Assumptions source_step_preserves_ancestry.
Print Assumptions finite_next_preserves_ancestry.

End TermParamReaderProjection.
