(** DDL token receipts use the original declaration projection and writer.

    The source worker is the original prattail_bridge global/mode token loop,
    parameterized by source readers. State includes literal-pattern updates,
    integer alternatives, source origins, and any reader observation trace.
    Both frontends invoke that same worker; this model does not equate readers
    that return different observations, nor prove the Rust body automatically.

    Source writer order and execution append order are deliberately distinct:
    DDL appends literals before explicit tokens. Each append carries its actual
    source ordinal. The unchanged first-variant writer supplies the observation;
    no execution token name, regex, decoder or guessed family participates.
    Missing writer rows stay missing. These are finite projection/receipt laws,
    not a lexer, admission, resource, or whole-parser equivalence proof.
*)
From Stdlib Require Import List String.
From PrattailWpdaRuntime Require Import TokenKindBindingObservation.
Import ListNotations.

Module TokenDeclarationProjection.
Section Source.
Context {Source State Projected : Type}.
Variable original_step : Source -> State -> Projected * State.
Fixpoint project (sources : list Source) (state : State) : list Projected * State :=
  match sources with
  | [] => ([], state)
  | source :: rest =>
      let '(row, next) := original_step source state in
      let '(rows, final) := project rest next in (row :: rows, final)
  end.
Definition macro_projection := project.
Definition ddl_projection := project.
Theorem same_worker_preserves_state_and_reader_trace : forall sources state,
  macro_projection sources state = ddl_projection sources state.
Proof. reflexivity. Qed.
Theorem first_source_precedes_rest : forall source rest state row next,
  original_step source state = (row, next) ->
  project (source :: rest) state =
  let '(rows, final) := project rest next in (row :: rows, final).
Proof. intros; cbn; now rewrite H. Qed.
Theorem empty_source_does_not_observe_reader : forall state,
  project [] state = ([], state).
Proof. reflexivity. Qed.
End Source.

Section Receipts.
Context {Kind : Type}.
Variable source_variant : nat -> string.
Variable writer : string -> option Kind.
Definition append_receipts (source_ordinals : list nat) :=
  map (fun source => writer (source_variant source)) source_ordinals.
Theorem execution_position_uses_its_source_receipt : forall order position source,
  nth_error order position = Some source ->
  nth_error (append_receipts order) position = Some (writer (source_variant source)).
Proof. intros; unfold append_receipts; rewrite nth_error_map, H; reflexivity. Qed.
Theorem append_order_does_not_reorder_writer : forall explicit literals,
  append_receipts (List.app literals explicit) =
  List.app (append_receipts literals) (append_receipts explicit).
Proof. intros; unfold append_receipts; apply map_app. Qed.
Theorem missing_writer_row_has_no_fallback : forall order position source,
  nth_error order position = Some source -> writer (source_variant source) = None ->
  nth_error (append_receipts order) position = Some None.
Proof. intros; rewrite (execution_position_uses_its_source_receipt order position source H), H0;
  reflexivity. Qed.
Theorem display_name_and_decoder_are_not_inputs : forall order,
  append_receipts order = map (fun source => writer (source_variant source)) order.
Proof. reflexivity. Qed.
End Receipts.
Print Assumptions same_worker_preserves_state_and_reader_trace.
Print Assumptions first_source_precedes_rest.
Print Assumptions empty_source_does_not_observe_reader.
Print Assumptions execution_position_uses_its_source_receipt.
Print Assumptions append_order_does_not_reorder_writer.
Print Assumptions missing_writer_row_has_no_fallback.
Print Assumptions display_name_and_decoder_are_not_inputs.
End TokenDeclarationProjection.
