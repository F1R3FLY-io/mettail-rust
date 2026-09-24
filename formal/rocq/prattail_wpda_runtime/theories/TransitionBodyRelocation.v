(** Mechanical relocation of an existing transition body, not a new machine.

    Input includes every observation supplied to the original body; Output
    includes its action and, when observable, callback state/trace. The shared
    worker calls that SAME body. Static and owned views are equivalent only
    when their actual observations agree. No equality of different readers,
    weights, token sources, or transition bodies is assumed or manufactured.

    Rust source correspondence must establish literal body relocation (with
    module/receiver qualification only), unchanged argument binding/order,
    and the original macro's eligibility gate. Existing family models retain
    their original scope; this theorem does not extend their algorithms.
*)
From Stdlib Require Import List.

Definition shared_transition {Input Output : Type}
    (original_body : Input -> Output) (input : Input) := original_body input.

Theorem original_body_is_called_unchanged : forall Input Output
    (body : Input -> Output) input,
    shared_transition body input = body input.
Proof. reflexivity. Qed.

Theorem equal_observations_preserve_complete_output : forall Input Output
    (body : Input -> Output) static_input owned_input,
    static_input = owned_input ->
    shared_transition body static_input = shared_transition body owned_input.
Proof. intros Input Output body static_input owned_input H; now rewrite H. Qed.

Theorem relocation_preserves_order_and_duplicates : forall Input Output
    (body : Input -> Output) inputs,
    map (shared_transition body) inputs = map body inputs.
Proof. reflexivity. Qed.

Print Assumptions original_body_is_called_unchanged.
Print Assumptions equal_observations_preserve_complete_output.
Print Assumptions relocation_preserves_order_and_duplicates.
