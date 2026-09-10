(** Source-scope resolution before construction.

    Moniker identities and named FLT holes are distinct lookup domains. The
    association-list model represents map lookup and last insertion, not a
    replacement Rust environment implementation. Identity encoding into nat
    must preserve equality; a pretty name is never a moniker identity.

    Ordered slots shift existing indices by the full width, then insert formal
    slot i at width - 1 - i. Later duplicate keys shadow earlier ones, matching
    the existing map insertion. Caller URI injections are an immutable context
    component, not lexical keys. Their enrollment and source-New interpretation
    are separate obligations, not asserted by context preservation here.

    Checked target indices reuse the existing signed-32-bit protocol check.
    Resource precharge and strict evaluation ordering before node bit-vector
    allocation still require concrete source correspondence. *)
From Stdlib Require Import List String Bool Arith Lia ZArith.
From RhoBridge Require Import RholangConstructionProtocol.
Import ListNotations.

Inductive ScopeKey := MonikerKey (identity : nat) | HoleKey (name : string).
Definition key_eqb (lhs rhs : ScopeKey) : bool :=
  match lhs, rhs with
  | MonikerKey a, MonikerKey b => Nat.eqb a b
  | HoleKey a, HoleKey b => String.eqb a b
  | _, _ => false
  end.
Lemma key_eqb_refl : forall key, key_eqb key key = true.
Proof. intros [identity|name]; cbn; [apply Nat.eqb_refl|apply String.eqb_refl]. Qed.
Lemma key_eqb_exact : forall lhs rhs, key_eqb lhs rhs = true <-> lhs = rhs.
Proof.
  intros [a|a] [b|b]; cbn; try (split; discriminate).
  - rewrite Nat.eqb_eq. split; [intro; now subst|intro H; now inversion H].
  - rewrite String.eqb_eq. split; [intro; now subst|intro H; now inversion H].
Qed.

Definition Scope := list (ScopeKey * nat).
Fixpoint lookup_scope (key : ScopeKey) (scope : Scope) : option nat :=
  match scope with
  | [] => None
  | (candidate, index) :: rest =>
    if key_eqb key candidate then Some index else lookup_scope key rest
  end.
Definition shift_scope (width : nat) (scope : Scope) : Scope :=
  map (fun entry => (fst entry, snd entry + width)) scope.
Fixpoint install_slots (slots : list ScopeKey) (scope : Scope) : Scope :=
  match slots with
  | [] => scope
  | key :: rest => install_slots rest ((key, List.length rest) :: scope)
  end.
Definition extend_scope (scope : Scope) (slots : list ScopeKey) : Scope :=
  install_slots slots (shift_scope (List.length slots) scope).

(** The final occurrence is selected, not the first pretty-name match. *)
Fixpoint assigned_index (slots : list ScopeKey) (key : ScopeKey) : option nat :=
  match slots with
  | [] => None
  | candidate :: rest => match assigned_index rest key with
    | Some index => Some index
    | None => if key_eqb key candidate then Some (List.length rest) else None
    end
  end.

Theorem shifting_preserves_lookup_exactly : forall scope key width,
  lookup_scope key (shift_scope width scope) =
  option_map (fun index => index + width) (lookup_scope key scope).
Proof.
  induction scope as [|[candidate index] rest IH]; intros; cbn; [reflexivity|].
  destruct (key_eqb key candidate); cbn; [reflexivity|exact (IH key width)].
Qed.

Theorem ordered_insertion_selects_last_slot : forall slots scope key,
  lookup_scope key (install_slots slots scope) =
  match assigned_index slots key with
  | Some index => Some index
  | None => lookup_scope key scope
  end.
Proof.
  induction slots as [|candidate rest IH]; intros; cbn; [reflexivity|].
  rewrite IH. destruct (assigned_index rest key); [reflexivity|].
  cbn. destruct (key_eqb key candidate); reflexivity.
Qed.

Theorem extension_preserves_selected_slot_or_shifted_outer_lookup : forall scope slots key,
  lookup_scope key (extend_scope scope slots) =
  match assigned_index slots key with
  | Some index => Some index
  | None => option_map (fun index => index + List.length slots) (lookup_scope key scope)
  end.
Proof.
  intros; unfold extend_scope. rewrite ordered_insertion_selects_last_slot.
  destruct (assigned_index slots key); [reflexivity|apply shifting_preserves_lookup_exactly].
Qed.

Theorem assigned_slot_is_inside_its_width : forall slots key index,
  assigned_index slots key = Some index -> index < List.length slots.
Proof.
  induction slots as [|candidate rest IH]; intros key index H; cbn in H; [discriminate|].
  destruct (assigned_index rest key) eqn:HR.
  - inversion H; subst. specialize (IH key index HR). cbn; lia.
  - destruct (key_eqb key candidate); [|discriminate]. inversion H; subst. cbn; lia.
Qed.

Theorem final_duplicate_shadows_every_earlier_slot : forall prefix key,
  assigned_index (prefix ++ [key]) key = Some 0.
Proof.
  induction prefix; intros; cbn.
  - now rewrite key_eqb_refl.
  - now rewrite IHprefix.
Qed.

Theorem surviving_outer_reference_cannot_alias_new_slots : forall scope slots key old,
  assigned_index slots key = None -> lookup_scope key scope = Some old ->
  lookup_scope key (extend_scope scope slots) = Some (old + List.length slots) /\
  List.length slots <= old + List.length slots.
Proof.
  intros. rewrite extension_preserves_selected_slot_or_shifted_outer_lookup, H, H0.
  cbn. split; [reflexivity|lia].
Qed.

Definition lexical_lookup (scope : Scope) (identity : nat) (pretty : option string) : option nat :=
  match lookup_scope (MonikerKey identity) scope with
  | Some index => Some index
  | None => match pretty with
    | Some name => lookup_scope (HoleKey name) scope
    | None => None
    end
  end.

Theorem moniker_identity_precedes_hole_name : forall scope identity pretty index,
  lookup_scope (MonikerKey identity) scope = Some index ->
  lexical_lookup scope identity pretty = Some index.
Proof. intros; unfold lexical_lookup; now rewrite H. Qed.

Theorem hole_fallback_requires_missing_moniker : forall scope identity name index,
  lookup_scope (MonikerKey identity) scope = None ->
  lexical_lookup scope identity (Some name) = Some index <->
  lookup_scope (HoleKey name) scope = Some index.
Proof. intros; unfold lexical_lookup; now rewrite H. Qed.

Inductive AdmissionMode := PublicSource | HarnessSource.
Inductive ReferenceRole := NameReference | ProcessReference.
Inductive ScopeResolution :=
| BoundReference (index : nat)
| FormulaWildcard
| UnresolvedReference (role : ReferenceRole)
| HarnessMarker (role : ReferenceRole) (name : string)
| NamelessHarnessReference
| TargetIndexRejected.

Definition resolve_free (mode : AdmissionMode) (pattern : bool) (role : ReferenceRole)
    (scope : Scope) (identity : nat) (pretty : option string) : ScopeResolution :=
  match lexical_lookup scope identity pretty with
  | Some index => if fits_target_index index then BoundReference index else TargetIndexRejected
  | None => if pattern then FormulaWildcard else
    match mode with
    | PublicSource => UnresolvedReference role
    | HarnessSource => match pretty with
      | Some name => HarnessMarker role name
      | None => NamelessHarnessReference
      end
    end
  end.

Theorem public_resolution_cannot_create_a_harness_marker :
  forall pattern role scope identity pretty marker_role name,
  resolve_free PublicSource pattern role scope identity pretty <> HarnessMarker marker_role name.
Proof.
  intros. unfold resolve_free. destruct (lexical_lookup scope identity pretty).
  - destruct (fits_target_index n); discriminate.
  - destruct pattern; discriminate.
Qed.

Theorem unresolved_public_terms_reject_by_role : forall role scope identity pretty,
  lexical_lookup scope identity pretty = None ->
  resolve_free PublicSource false role scope identity pretty = UnresolvedReference role.
Proof. intros; unfold resolve_free; now rewrite H. Qed.

Theorem unresolved_formula_variable_remains_a_wildcard : forall mode role scope identity pretty,
  lexical_lookup scope identity pretty = None ->
  resolve_free mode true role scope identity pretty = FormulaWildcard.
Proof. intros; unfold resolve_free; now rewrite H. Qed.

Theorem successful_bound_resolution_preserves_checked_index :
  forall mode pattern role scope identity pretty index,
  resolve_free mode pattern role scope identity pretty = BoundReference index ->
  lexical_lookup scope identity pretty = Some index /\
  (0 <= Z.of_nat index <= 2147483647)%Z.
Proof.
  intros mode pattern role scope identity pretty index H.
  unfold resolve_free in H. destruct (lexical_lookup scope identity pretty) eqn:HL.
  - destruct (fits_target_index n) eqn:HF; [|discriminate]. inversion H; subst.
    apply target_index_check_exact in HF. split; [reflexivity|].
    split; [apply Nat2Z.is_nonneg|exact HF].
  - destruct pattern; [discriminate|]. destruct mode; [discriminate|].
    destruct pretty; discriminate.
Qed.

Print Assumptions key_eqb_exact.
Print Assumptions shifting_preserves_lookup_exactly.
Print Assumptions ordered_insertion_selects_last_slot.
Print Assumptions extension_preserves_selected_slot_or_shifted_outer_lookup.
Print Assumptions assigned_slot_is_inside_its_width.
Print Assumptions final_duplicate_shadows_every_earlier_slot.
Print Assumptions surviving_outer_reference_cannot_alias_new_slots.
Print Assumptions moniker_identity_precedes_hole_name.
Print Assumptions hole_fallback_requires_missing_moniker.
Print Assumptions public_resolution_cannot_create_a_harness_marker.
Print Assumptions unresolved_public_terms_reject_by_role.
Print Assumptions unresolved_formula_variable_remains_a_wildcard.
Print Assumptions successful_bound_resolution_preserves_checked_index.
