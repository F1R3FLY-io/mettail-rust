(** Exact relocation of wpda_codegen::guest_body_nested_open_kinds.

    Original token-name matching against a string, original mode-name equality,
    and name rendering are distinct supplied operations. The projection copies
    their inputs without equating source equality with spelling equality.
    First matching token is selected BEFORE checking its optional push target;
    a missing push does not continue searching duplicate token names. The first
    equal mode supplies an ordered token roster; filtering preserves duplicates.

    The finite list functions model the original Rust iterator chains, not a
    recursive Rust implementation. The theorem is source-field substitution and
    exact descriptor output, not arbitrary effectful callback behavior, graph
    admission, raw-versus-qualified token correspondence, lexer correctness, or
    installed-parser cutover. All callbacks below are universally quantified
    pure functions; no relation between name matching and name equality is
    assumed. Runtime adapters must provide the same observations.
*)
From Stdlib Require Import List String Bool.
Import ListNotations.
Set Implicit Arguments.

Module GuestModeDescriptorProjection.
Section Projection.
Context {Name : Type}.
Variable matches_open : Name -> string -> bool.
Variable names_equal : Name -> Name -> bool.
Variable render_name : Name -> string.

Record SourceToken := { token_name : Name; token_push : option Name }.
Record SourceMode := { mode_name : Name; mode_tokens : list SourceToken }.
Record TokenView := { observed_name : Name; observed_push : option Name }.
Record ModeView := { observed_mode_name : Name; observed_tokens : list TokenView }.

Definition project_token token :=
  {| observed_name := token_name token; observed_push := token_push token |}.
Definition project_mode mode :=
  {| observed_mode_name := mode_name mode;
     observed_tokens := map project_token (mode_tokens mode) |}.

Definition source_open open tokens :=
  match find (fun token => matches_open (token_name token) open) tokens with
  | Some token => token_push token | None => None end.
Definition shared_open open tokens :=
  match find (fun token => matches_open (observed_name token) open) tokens with
  | Some token => observed_push token | None => None end.

Definition same_push target push :=
  match push with Some name => names_equal name target | None => false end.
Definition source_nested target tokens :=
  map (fun token => render_name (token_name token))
    (filter (fun token => same_push target (token_push token)) tokens).
Definition shared_nested target tokens :=
  map (fun token => render_name (observed_name token))
    (filter (fun token => same_push target (observed_push token)) tokens).

Definition source_derive open tokens modes :=
  match source_open open tokens with
  | None => []
  | Some target =>
    match find (fun mode => names_equal (mode_name mode) target) modes with
    | None => [] | Some mode => source_nested target (mode_tokens mode) end
  end.
Definition shared_derive open tokens modes :=
  match shared_open open tokens with
  | None => []
  | Some target =>
    match find (fun mode => names_equal (observed_mode_name mode) target) modes with
    | None => [] | Some mode => shared_nested target (observed_tokens mode) end
  end.

Lemma first_token_projection : forall tokens open,
  find (fun token => matches_open (observed_name token) open) (map project_token tokens) =
  option_map project_token (find (fun token => matches_open (token_name token) open) tokens).
Proof.
  induction tokens as [|token rest IH]; intros open; cbn; [reflexivity|].
  destruct (matches_open (token_name token) open); [reflexivity|apply IH].
Qed.

Lemma first_push_projection : forall tokens open,
  shared_open open (map project_token tokens) = source_open open tokens.
Proof.
  intros; unfold shared_open, source_open. rewrite first_token_projection.
  destruct (find (fun token => matches_open (token_name token) open) tokens); reflexivity.
Qed.

Lemma first_mode_projection : forall modes target,
  find (fun mode => names_equal (observed_mode_name mode) target) (map project_mode modes) =
  option_map project_mode (find (fun mode => names_equal (mode_name mode) target) modes).
Proof.
  induction modes as [|mode rest IH]; intros target; cbn; [reflexivity|].
  destruct (names_equal (mode_name mode) target); [reflexivity|apply IH].
Qed.

Lemma ordered_filter_projection : forall tokens target,
  shared_nested target (map project_token tokens) = source_nested target tokens.
Proof.
  induction tokens as [|token rest IH]; intros target; unfold shared_nested, source_nested in *;
    cbn; [reflexivity|].
  destruct (same_push target (token_push token)); cbn; now rewrite IH.
Qed.

Theorem original_guest_descriptor_relocation : forall open tokens modes,
  shared_derive open (map project_token tokens) (map project_mode modes) =
  source_derive open tokens modes.
Proof.
  intros; unfold shared_derive, source_derive. rewrite first_push_projection.
  destruct (source_open open tokens) as [target|]; [|reflexivity].
  rewrite first_mode_projection.
  destruct (find (fun mode => names_equal (mode_name mode) target) modes) as [mode|];
    [apply ordered_filter_projection|reflexivity].
Qed.

Theorem first_matching_token_without_push_stops_lookup : forall open token rest,
  matches_open (token_name token) open = true -> token_push token = None ->
  source_open open (token :: rest) = None.
Proof. intros; unfold source_open; cbn; now rewrite H, H0. Qed.

Theorem first_matching_mode_controls_output : forall open tokens mode rest target,
  source_open open tokens = Some target -> names_equal (mode_name mode) target = true ->
  source_derive open tokens (mode :: rest) = source_nested target (mode_tokens mode).
Proof. intros; unfold source_derive; rewrite H; cbn; now rewrite H0. Qed.

Theorem matching_duplicate_occurrences_are_retained : forall target token,
  same_push target (token_push token) = true ->
  source_nested target [token; token] =
  [render_name (token_name token); render_name (token_name token)].
Proof. intros; unfold source_nested; cbn; now rewrite H. Qed.

Theorem unmatched_push_emits_no_name : forall target token,
  same_push target (token_push token) = false -> source_nested target [token] = [].
Proof. intros; unfold source_nested; cbn; now rewrite H. Qed.

End Projection.
Print Assumptions first_token_projection.
Print Assumptions first_push_projection.
Print Assumptions first_mode_projection.
Print Assumptions ordered_filter_projection.
Print Assumptions original_guest_descriptor_relocation.
Print Assumptions first_matching_token_without_push_stops_lookup.
Print Assumptions first_matching_mode_controls_output.
Print Assumptions matching_duplicate_occurrences_are_retained.
Print Assumptions unmatched_push_emits_no_name.
End GuestModeDescriptorProjection.
