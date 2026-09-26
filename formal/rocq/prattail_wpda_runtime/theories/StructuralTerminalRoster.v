(** Exact implicit terminal roster from lexer.rs extract_terminals_from_source.

    The original lexer always inserts these seven Fixed terminals into its
    BTreeSet before authored terminals. The Core bridges previously inserted
    only authored terminal text. Reuse the SAME borrowed roster, then retain
    each bridge's existing BTreeSet iteration and TokenDefinition append.
    This is not another lexer, sort implementation, or token classifier.

    Source roster order is not canonical append order. The canonicalizer below
    is the existing Rust BTreeSet worker; its membership correspondence is an
    explicit source obligation, not an axiom or a new sorting algorithm.
    Earlier token IDs remain unchanged; literal IDs and Core fingerprints may
    change when previously absent terminals enter the sorted output. Both
    bridges extend the roster unconditionally, just like the original lexer.
    DDL still publishes no observation table on unsupported metadata domains.
*)
From Stdlib Require Import List String Arith Lia.
Import ListNotations.
Open Scope string_scope.

Module StructuralTerminalRoster.
Definition structural : list string := ["("; ")"; "{"; "}"; "["; "]"; ","].
Definition extend (authored : list string) := (authored ++ structural)%list.
Definition append_observations {Observation : Type}
    (metadata : option (list Observation)) (observe : string -> Observation)
    (ordered : list string) :=
  option_map (fun prior => (prior ++ map observe ordered)%list) metadata.

Theorem roster_is_exact :
  structural = ["("; ")"; "{"; "}"; "["; "]"; ","].
Proof. reflexivity. Qed.
Theorem source_order_is_not_canonical_append_order :
  structural <> ["("; ")"; ","; "["; "]"; "{"; "}"].
Proof. discriminate. Qed.
Theorem authored_members_are_preserved : forall authored text,
  In text authored -> In text (extend authored).
Proof. intros; apply in_or_app; now left. Qed.
Theorem every_original_structural_member_is_restored : forall authored text,
  In text structural -> In text (extend authored).
Proof. intros; apply in_or_app; now right. Qed.
Theorem no_new_nonstructural_member : forall authored text,
  In text (extend authored) -> In text authored \/ In text structural.
Proof. intros; now apply in_app_or in H. Qed.
Theorem original_lexer_and_bridge_have_same_members : forall authored text,
  In text (structural ++ authored)%list <-> In text (extend authored).
Proof. intros; unfold extend; rewrite !in_app_iff; tauto. Qed.
Theorem unsupported_ddl_metadata_remains_absent : forall Observation
    (observe : string -> Observation) ordered,
  append_observations None observe ordered = None.
Proof. reflexivity. Qed.
Theorem admitted_ddl_appends_original_observations : forall Observation
    (prior : list Observation) observe ordered,
  append_observations (Some prior) observe ordered =
    Some (prior ++ map observe ordered)%list.
Proof. reflexivity. Qed.

Section ExistingCanonicalWorker.
Variable canonical : list string -> list string.
Theorem canonical_membership_correspondence :
  (forall input text, In text (canonical input) <-> In text input) ->
  forall authored text,
    In text (canonical (extend authored)) <->
    In text authored \/ In text structural.
Proof. intros H authored text; rewrite H; apply in_app_iff. Qed.
End ExistingCanonicalWorker.

Section ExistingAppendSites.
Context {Token Observation : Type}.
Variable definition : string -> Token.
Variable observation : string -> Observation.
Definition appended (prior : list (Token * Observation)) ordered :=
  (prior ++ map (fun text => (definition text, observation text)) ordered)%list.
Theorem prior_ids_are_unchanged : forall prior ordered index,
  index < List.length prior ->
  nth_error (appended prior ordered) index = nth_error prior index.
Proof. intros; unfold appended; now apply nth_error_app1. Qed.
Theorem exact_append_site_pairs_definition_and_observation : forall prior ordered index text,
  nth_error ordered index = Some text ->
  nth_error (appended prior ordered) (List.length prior + index) =
    Some (definition text, observation text).
Proof.
  intros; unfold appended; rewrite nth_error_app2 by lia.
  replace (List.length prior + index - List.length prior) with index by lia.
  rewrite nth_error_map, H; reflexivity.
Qed.
End ExistingAppendSites.

Print Assumptions roster_is_exact.
Print Assumptions source_order_is_not_canonical_append_order.
Print Assumptions authored_members_are_preserved.
Print Assumptions every_original_structural_member_is_restored.
Print Assumptions no_new_nonstructural_member.
Print Assumptions original_lexer_and_bridge_have_same_members.
Print Assumptions unsupported_ddl_metadata_remains_absent.
Print Assumptions admitted_ddl_appends_original_observations.
Print Assumptions canonical_membership_correspondence.
Print Assumptions prior_ids_are_unchanged.
Print Assumptions exact_append_site_pairs_definition_and_observation.
End StructuralTerminalRoster.
