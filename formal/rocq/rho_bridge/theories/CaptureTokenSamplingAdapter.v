(** Capture-token provenance and checked sample admission.

    This model covers the adapter, not the DFA implementation. Resolution and
    DFA sampling are supplied by the existing lexer bridge and automaton walk.
    Admission checks their returned candidate for nonempty accepted text. A
    failed lookup or sample is an error, never an invented empty string.

    Slot names and kinds are finite identifiers. Retaining a token-kind id
    enriches an existing ordered field slot without changing its name, optional
    marker, position, or erased Rust field shape. The concrete tests separately
    check lexer aliases, token-pattern resolution and generated Rust layout. *)
From Stdlib Require Import List Bool Arith.
Import ListNotations.
Module CaptureTokenSamplingAdapter.

Inductive OldSource := TokenText | ParameterSlot (id : nat) | Guest (id : nat).
Inductive Source := Token (kind : nat) | Param (id : nat) | Region (id : nat).
Definition erase_source source :=
  match source with Token _ => TokenText | Param n => ParameterSlot n | Region n => Guest n end.
Record Slot := { slot_name : nat; slot_source : Source; optional : bool }.
Definition erase_slot slot := (slot_name slot, erase_source (slot_source slot), optional slot).
Definition token_kinds slots :=
  flat_map (fun slot => match slot_source slot with Token k => [k] | _ => [] end) slots.

Theorem erasure_preserves_length : forall slots,
  length (map erase_slot slots) = length slots.
Proof. intros; apply map_length. Qed.
Theorem erasure_preserves_position : forall slots index slot,
  nth_error slots index = Some slot ->
  nth_error (map erase_slot slots) index = Some (erase_slot slot).
Proof. intros. rewrite nth_error_map, H. reflexivity. Qed.
Theorem erasure_preserves_append : forall left right,
  map erase_slot (left ++ right) = map erase_slot left ++ map erase_slot right.
Proof. intros; apply map_app. Qed.
Theorem provenance_keeps_order_and_occurrences : forall left right,
  token_kinds (left ++ right) = token_kinds left ++ token_kinds right.
Proof. intros; apply flat_map_app. Qed.

Inductive Failure := UnknownKind | NoSample | EmptySample | RejectedSample.
Inductive Outcome := Accepted (pattern : nat) (text : list nat) | Refused (why : Failure).
Definition check_candidate pattern candidate (accepts : nat -> list nat -> bool) :=
  match candidate with
  | None => Refused NoSample
  | Some [] => Refused EmptySample
  | Some (first :: rest) =>
      if accepts pattern (first :: rest)
      then Accepted pattern (first :: rest) else Refused RejectedSample
  end.
Definition sample resolved (choose : nat -> option (list nat)) accepts :=
  match resolved with None => Refused UnknownKind
  | Some pattern => check_candidate pattern (choose pattern) accepts end.

Theorem accepted_is_resolved_and_checked : forall resolved choose accepts pattern text,
  sample resolved choose accepts = Accepted pattern text ->
  resolved = Some pattern /\ choose pattern = Some text /\
  text <> [] /\ accepts pattern text = true.
Proof.
  intros resolved choose accepts pattern text H.
  destruct resolved as [p|]; [|discriminate].
  unfold sample, check_candidate in H.
  destruct (choose p) as [[|first rest]|] eqn:C; try discriminate.
  destruct (accepts p (first :: rest)) eqn:A; [|discriminate].
  inversion H; subst. repeat split; auto; discriminate.
Qed.
Theorem unknown_is_not_empty_success : forall choose accepts,
  sample None choose accepts = Refused UnknownKind.
Proof. reflexivity. Qed.
Theorem missing_sample_is_refused : forall pattern choose accepts,
  choose pattern = None -> sample (Some pattern) choose accepts = Refused NoSample.
Proof. intros; unfold sample; rewrite H; reflexivity. Qed.
Theorem empty_sample_is_refused : forall pattern choose accepts,
  choose pattern = Some [] -> sample (Some pattern) choose accepts = Refused EmptySample.
Proof. intros; unfold sample; rewrite H; reflexivity. Qed.
Theorem accepted_candidate_is_unchanged : forall pattern choose accepts first rest,
  choose pattern = Some (first :: rest) -> accepts pattern (first :: rest) = true ->
  sample (Some pattern) choose accepts = Accepted pattern (first :: rest).
Proof. intros; unfold sample; rewrite H; unfold check_candidate; rewrite H0; reflexivity. Qed.
Theorem aliases_share_checked_result : forall left right choose accepts,
  left = right -> sample left choose accepts = sample right choose accepts.
Proof. intros; subst; reflexivity. Qed.

Print Assumptions accepted_is_resolved_and_checked.
Print Assumptions erasure_preserves_position.
End CaptureTokenSamplingAdapter.
