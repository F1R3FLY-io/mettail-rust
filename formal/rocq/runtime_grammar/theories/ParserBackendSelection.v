(** * Parser/backend selection and package isolation

    This model concerns generator invocation, retained declaration accounting,
    and dependency reachability, not the correctness of parsing or lowering.
    The enabled generator is supplied unchanged. A disabled generator is not
    invoked and does not produce a backend artifact. Source declarations remain
    available, with an explicit unselected-backend disposition for each roster
    entry. Equation orientations are separate entries in that roster.

    Cargo features are additive. A feature gate on a shared package cannot
    establish permanent parser isolation: another consumer may enable it.
    The final theorem instead uses a closed region of distinct package vertices.
    External edges may be added freely provided they do not originate inside
    that region. The manifest/graph tests must establish that premise for the
    actual packages; this file is not a proof of Cargo's implementation. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.

Module ParserBackendSelection.

  Inductive GeneratorEvent := InvokeBackend.

  Definition selected_generation {Input Output : Type}
      (enabled : bool) (generate : Input -> Output) (input : Input)
      : list GeneratorEvent * option Output :=
    if enabled then ([InvokeBackend], Some (generate input)) else ([], None).

  Theorem disabled_does_not_invoke :
    forall (Input Output : Type) (generate : Input -> Output) input,
      selected_generation false generate input = ([], None).
  Proof. reflexivity. Qed.

  Theorem enabled_invokes_exact_generator :
    forall (Input Output : Type) (generate : Input -> Output) input,
      selected_generation true generate input =
        ([InvokeBackend], Some (generate input)).
  Proof. reflexivity. Qed.

  (** The parser projection is not routed through the backend selector. *)
  Definition compilation {Input Syntax Backend : Type}
      (parse : Input -> Syntax) (generate : Input -> Backend)
      (enabled : bool) (input : Input) :=
    (parse input, selected_generation enabled generate input).

  Theorem parser_projection_unchanged :
    forall (Input Syntax Backend : Type) (parse : Input -> Syntax)
      (generate : Input -> Backend) enabled input,
      fst (compilation parse generate enabled input) = parse input.
  Proof. reflexivity. Qed.

  Inductive ConstructKind := EquationForward | EquationReverse | Rewrite | Fold.
  Inductive Origin := Declared | AutoInjected.
  Record Construct := {
    kind : ConstructKind;
    name : nat;
    origin : Origin
  }.
  Inductive Outcome := Delivered | SuppressedBackendUnselected.
  Record Disposition := { subject : Construct; outcome : Outcome }.

  Definition unselected_inventory (roster : list Construct) : list Disposition :=
    map (fun construct =>
      {| subject := construct; outcome := SuppressedBackendUnselected |}) roster.

  Theorem unselected_retains_exact_roster :
    forall roster, map subject (unselected_inventory roster) = roster.
  Proof.
    intro roster. unfold unselected_inventory. rewrite map_map.
    change (map (fun entry : Construct => entry) roster = roster).
    apply map_id.
  Qed.

  Theorem unselected_retains_cardinality :
    forall roster, length (unselected_inventory roster) = length roster.
  Proof. intro roster; apply length_map. Qed.

  Theorem unselected_never_claims_delivery :
    forall roster disposition,
      In disposition (unselected_inventory roster) ->
      outcome disposition = SuppressedBackendUnselected.
  Proof.
    intros roster disposition Hin. apply in_map_iff in Hin.
    destruct Hin as [entry [Heq _]]. subst disposition. reflexivity.
  Qed.

  (** Feature union on one package is disjunction, not consumer-local choice. *)
  Definition unified_feature (left right : bool) := orb left right.

  Theorem another_consumer_enables_shared_backend :
    unified_feature false true = true.
  Proof. reflexivity. Qed.

  (** Iteration-counted reachability matches a bounded worklist observation.
      No recursion-depth assumption is used in the closure proof. *)
  Inductive Reach (edge : nat -> nat -> Prop) : nat -> nat -> nat -> Prop :=
  | reach_here : forall vertex, Reach edge 0 vertex vertex
  | reach_next : forall steps first second last,
      edge first second -> Reach edge steps second last ->
      Reach edge (S steps) first last.

  Definition closed_region (region : nat -> Prop) (edge : nat -> nat -> Prop) :=
    forall first second, region first -> edge first second -> region second.

  Theorem reach_stays_in_closed_region :
    forall region edge, closed_region region edge ->
      forall steps first last, Reach edge steps first last ->
        region first -> region last.
  Proof.
    intros region edge Hclosed steps first last Hreach.
    induction Hreach as [vertex|steps first second last Hedge Hreach IH].
    - trivial.
    - intro Hfirst. apply IH. eapply Hclosed; eassumption.
  Qed.

  Theorem external_edges_preserve_closed_region :
    forall region edge extra,
      closed_region region edge ->
      (forall first second, extra first second -> ~ region first) ->
      closed_region region (fun first second => edge first second \/ extra first second).
  Proof.
    intros region edge extra Hclosed Hexternal first second Hfirst [Hedge|Hextra].
    - eapply Hclosed; eassumption.
    - exfalso. exact (Hexternal first second Hextra Hfirst).
  Qed.

  Theorem isolated_parser_cannot_reach_node_after_external_unification :
    forall region edge extra parser node,
      closed_region region edge ->
      (forall first second, extra first second -> ~ region first) ->
      region parser -> ~ region node ->
      forall steps,
        ~ Reach (fun first second => edge first second \/ extra first second)
            steps parser node.
  Proof.
    intros region edge extra parser node Hclosed Hexternal Hparser Hnode steps Hreach.
    apply Hnode.
    eapply reach_stays_in_closed_region; [|exact Hreach|exact Hparser].
    eapply external_edges_preserve_closed_region; eassumption.
  Qed.

  Print Assumptions disabled_does_not_invoke.
  Print Assumptions enabled_invokes_exact_generator.
  Print Assumptions parser_projection_unchanged.
  Print Assumptions unselected_retains_exact_roster.
  Print Assumptions unselected_retains_cardinality.
  Print Assumptions unselected_never_claims_delivery.
  Print Assumptions another_consumer_enables_shared_backend.
  Print Assumptions reach_stays_in_closed_region.
  Print Assumptions external_edges_preserve_closed_region.
  Print Assumptions isolated_parser_cannot_reach_node_after_external_unification.
End ParserBackendSelection.
