(* Candidate-local declared-constructor evidence.

   Source correspondence:
   - candidate_walk expands only selected Intermediate entries into its flat;
     Symbols and optional Packing operands remain opaque flat leaves.
   - a cached Fragment Boolean must equal CollectionId membership in that
     exact flat, not membership in a raw-first or descendant alternative.
   - the proposed extension of the existing kept-wrapper event uses this
     Boolean plus the existing leading-trigger and coercion metadata.

   The ordered decision-word theorem covers the observed generated ordinal 0
   when the earlier lateness and weight comparisons tie. It does not claim
   that arbitrary ordinals improve under context, that the entire rank is a
   lawful semiring, or that a finite k-best prefix is complete. The selected
   child contracts below are local induction invariants, not axioms about
   arbitrary production memo entries. Runtime regression tests must establish
   the concrete producer/consumer correspondence at the edited snapshot.
*)
From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Inductive FlatAtom :=
| SemanticSymbol
| DirectCollection
| OpaquePacking
| OtherLeaf.

Definition is_collection (atom : FlatAtom) : bool :=
  match atom with DirectCollection => true | _ => false end.

Definition flat_has_collection (flat : list FlatAtom) : bool :=
  existsb is_collection flat.

Inductive SelectedChild :=
| SelectedLeaf (atom : FlatAtom)
| SelectedFragment (node coordinate : nat)
    (flat : list FlatAtom) (cached_presence : bool).

Definition child_flat (child : SelectedChild) : list FlatAtom :=
  match child with
  | SelectedLeaf atom => [atom]
  | SelectedFragment _ _ flat _ => flat
  end.

Definition child_presence (child : SelectedChild) : bool :=
  match child with
  | SelectedLeaf atom => is_collection atom
  | SelectedFragment _ _ _ cached => cached
  end.

Definition child_exact (child : SelectedChild) : Prop :=
  child_presence child = flat_has_collection (child_flat child).

Fixpoint scan_presence (children : list SelectedChild) (seen : bool) : bool :=
  match children with
  | [] => seen
  | child :: rest => scan_presence rest (seen || child_presence child)
  end.

Lemma flat_presence_app : forall left right,
  flat_has_collection (left ++ right) =
  flat_has_collection left || flat_has_collection right.
Proof. intros. unfold flat_has_collection. apply existsb_app. Qed.

Theorem selected_presence_matches_flat : forall children seen,
  Forall child_exact children ->
  scan_presence children seen =
  seen || flat_has_collection (concat (map child_flat children)).
Proof.
  induction children as [|child rest IH]; intros seen Hexact.
  - destruct seen; reflexivity.
  - inversion Hexact as [|? ? Hchild Hrest]; subst.
    cbn [scan_presence map concat].
    rewrite (IH _ Hrest), flat_presence_app.
    unfold child_exact in Hchild. rewrite Hchild.
    now rewrite orb_assoc.
Qed.

Example empty_collection_is_present :
  scan_presence [SelectedLeaf DirectCollection] false = true.
Proof. reflexivity. Qed.

Example semantic_and_optional_boundaries_are_opaque :
  scan_presence [SelectedLeaf SemanticSymbol; SelectedLeaf OpaquePacking] false = false.
Proof. reflexivity. Qed.

Example selected_coordinate_changes_presence :
  scan_presence [SelectedFragment 7 0 [OtherLeaf] false] false = false /\
  scan_presence [SelectedFragment 7 1 [DirectCollection] true] false = true.
Proof. split; reflexivity. Qed.

Definition keep_constructor
    (old_one_symbol leading_trigger selected_collection declared_coercion : bool)
    : bool :=
  negb declared_coercion &&
    (old_one_symbol || (leading_trigger && selected_collection)).

Theorem old_evidence_is_preserved : forall leading selected,
  keep_constructor true leading selected false = true.
Proof. intros; reflexivity. Qed.

Theorem new_evidence_requires_exact_inputs : forall leading selected coercion,
  keep_constructor false leading selected coercion = true <->
  leading = true /\ selected = true /\ coercion = false.
Proof. intros [] [] []; cbn; intuition discriminate. Qed.

Theorem coercion_does_not_receive_wrapper_evidence : forall old leading selected,
  keep_constructor old leading selected true = false.
Proof. intros; reflexivity. Qed.

(* The Rust comparison pads a missing ordinal with u16::MAX. On its valid
   domain an empty word can never be smaller than a nonempty word, even when
   that word consists solely of MAX ordinals. This definition follows the
   same left-to-right comparison, with no allocation of padded vectors. *)
Definition ordinal_max : nat := 65535.

Fixpoint word_lt (left right : list nat) : bool :=
  match left with
  | [] => false
  | a :: tail =>
      match right with
      | [] => (a <? ordinal_max) ||
          ((a =? ordinal_max) && word_lt tail [])
      | b :: rest =>
          match Nat.compare a b with
          | Lt => true
          | Eq => word_lt tail rest
          | Gt => false
          end
      end
  end.

Lemma word_lt_common_prefix : forall prefix left right,
  word_lt (prefix ++ left) (prefix ++ right) = word_lt left right.
Proof.
  induction prefix as [|a prefix IH]; intros; cbn.
  - reflexivity.
  - now rewrite Nat.compare_refl, IH.
Qed.

Lemma zero_before_suffix_is_strict : forall suffix,
  word_lt (0 :: suffix) suffix = true.
Proof.
  induction suffix as [|a suffix IH].
  - reflexivity.
  - destruct a as [|a]; cbn; auto.
Qed.

Theorem zero_event_survives_common_context : forall prefix suffix,
  word_lt (prefix ++ 0 :: suffix) (prefix ++ suffix) = true.
Proof.
  intros. rewrite word_lt_common_prefix.
  apply zero_before_suffix_is_strict.
Qed.

(* Stable ordering inserts the new event among the already ordered common
   events without changing their relative order. The insertion position may
   depend on token position, depth, and the event's phase; the preference
   theorem deliberately holds at every such position. *)
Record Decision := {
  decision_position : nat;
  decision_depth : nat;
  decision_ordinal : nat
}.

Fixpoint insert_decision (before : Decision -> Decision -> bool)
    (fresh : Decision) (context : list Decision) : list Decision :=
  match context with
  | [] => [fresh]
  | event :: rest =>
      if before fresh event then fresh :: context
      else event :: insert_decision before fresh rest
  end.

Lemma insertion_preserves_common_order : forall before fresh context,
  exists prefix suffix,
    context = prefix ++ suffix /\
    insert_decision before fresh context = prefix ++ fresh :: suffix.
Proof.
  intros before fresh context. induction context as [|event rest IH].
  - exists [], []; auto.
  - cbn. destruct (before fresh event).
    + exists [], (event :: rest); auto.
    + destruct IH as [prefix [suffix [Hrest Hinsert]]].
      exists (event :: prefix), suffix. cbn. split.
      * now rewrite Hrest.
      * now rewrite Hinsert.
Qed.

Theorem ordered_zero_event_improves_tied_rank : forall before fresh context,
  decision_ordinal fresh = 0 ->
  word_lt
    (map decision_ordinal (insert_decision before fresh context))
    (map decision_ordinal context) = true.
Proof.
  intros before fresh context Hzero.
  destruct (insertion_preserves_common_order before fresh context)
    as [prefix [suffix [Hcontext Hinsert]]].
  rewrite Hinsert, Hcontext, !map_app. cbn. rewrite Hzero.
  apply zero_event_survives_common_context.
Qed.

Section UnchangedPayload.
  Context {Weight Value : Type}.
  Record Candidate := {
    candidate_lateness : nat;
    candidate_weight : Weight;
    candidate_value : Value;
    child_events : list Decision;
    owner_events : list Decision;
    scan_events : list Decision
  }.

  Definition add_owner_evidence (enabled : bool) (fresh : Decision)
      (candidate : Candidate) : Candidate :=
    {| candidate_lateness := candidate_lateness candidate;
       candidate_weight := candidate_weight candidate;
       candidate_value := candidate_value candidate;
       child_events := child_events candidate;
       owner_events := owner_events candidate ++ if enabled then [fresh] else [];
       scan_events := scan_events candidate |}.

  Theorem evidence_preserves_earlier_rank_and_value : forall enabled fresh candidate,
    candidate_lateness (add_owner_evidence enabled fresh candidate) =
      candidate_lateness candidate /\
    candidate_weight (add_owner_evidence enabled fresh candidate) =
      candidate_weight candidate /\
    candidate_value (add_owner_evidence enabled fresh candidate) =
      candidate_value candidate.
  Proof. intros; repeat split; reflexivity. Qed.

  Theorem evidence_stays_in_owner_phase : forall fresh candidate,
    child_events (add_owner_evidence true fresh candidate) = child_events candidate /\
    owner_events (add_owner_evidence true fresh candidate) = owner_events candidate ++ [fresh] /\
    scan_events (add_owner_evidence true fresh candidate) = scan_events candidate.
  Proof. intros; repeat split; reflexivity. Qed.

  Theorem adding_evidence_preserves_the_candidate_family : forall enabled fresh family,
    map candidate_value (map (add_owner_evidence enabled fresh) family) =
      map candidate_value family.
  Proof. intros; induction family; cbn; congruence. Qed.
End UnchangedPayload.

Example observed_length_masking : Nat.max 7 5 = Nat.max 7 0.
Proof. reflexivity. Qed.

Example nonzero_event_is_not_unconditionally_better :
  word_lt [1; 0] [0] = false.
Proof. reflexivity. Qed.

Print Assumptions selected_presence_matches_flat.
Print Assumptions new_evidence_requires_exact_inputs.
Print Assumptions zero_event_survives_common_context.
Print Assumptions ordered_zero_event_improves_tied_rank.
Print Assumptions evidence_preserves_earlier_rank_and_value.
Print Assumptions evidence_stays_in_owner_phase.
Print Assumptions adding_evidence_preserves_the_candidate_family.
