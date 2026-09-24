(** Pure data projection of the ORIGINAL build_spine_emission_from_parts.

    The existing prefix/mixfix partition and tree algorithms are reused, not
    rederived. Prefix group member_rule_idxs supplies its sorted unique roster;
    the unchanged helper is an explicit observation boundary here. Mixfix uses
    the existing group_member_rule_idxs (slice order, not a sorted set).

    Original token quotation is interleaved with four data effects: group roster
    insertion, disposition insertion, lex-alt insertion, and mixfix row append.
    Erasing token events commutes with execution of these data effects. Rust
    must retain each data effect's payload and order, including repeated-key
    last writes; this is not a claim that HashMap iteration order is stable.
    No callback/panic/allocation equivalence of reordered quotation is claimed.
    The bridge concerns returning executions with admitted category indexes
    and nonempty prefix groups. Empty-group failure remains explicit below.
    Existing member/tree/partition laws are dependencies, not reimplementations.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import PrefixFactoringProjection
  MixfixDescriptorProjection PrefixCallbackFailure.
Import ListNotations.
Set Implicit Arguments.

Module FactoringEmissionData.
Module P := PrefixFactoringProjection.PrefixFactoringProjection.
Module M := MixfixDescriptorProjection.MixfixDescriptorProjection.
Module C := PrefixCallbackFailure.PrefixCallbackFailure.

Inductive Disposition :=
| GroupFirst (spine body weight : nat)
| GroupRest.

Record MixfixRow := {
  dispatch : nat; trigger : string; result_category : nat; spine : nat;
  min_bp : nat; min_member : nat; members : list nat
}.
Definition mixfix_row dispatch trigger group :=
  {| dispatch := dispatch; trigger := trigger;
     result_category := M.group_result_src group; spine := M.spine_id group;
     min_bp := M.min_l_bp group; min_member := M.min_member_rule_idx group;
     members := M.group_member_rule_idxs group |}.

Inductive Write :=
| PutRoster (category first : nat) (members : list nat)
| PutDisposition (category member : nat) (value : Disposition)
| PutLexAlt (category member : nat) (value : Disposition)
| AppendMixfix (row : MixfixRow).

Record Data := {
  rosters : nat -> nat -> option (list nat);
  dispositions : nat -> nat -> option Disposition;
  lex_alt : nat -> nat -> option Disposition;
  mixfix_rows : list MixfixRow
}.
Definition put {A} (table : nat -> nat -> option A) cat rule value :=
  fun c r => if Nat.eqb c cat && Nat.eqb r rule then Some value else table c r.
Definition write w data := match w with
| PutRoster c r ms =>
  {| rosters := put (rosters data) c r ms; dispositions := dispositions data;
     lex_alt := lex_alt data; mixfix_rows := mixfix_rows data |}
| PutDisposition c r d =>
  {| rosters := rosters data; dispositions := put (dispositions data) c r d;
     lex_alt := lex_alt data; mixfix_rows := mixfix_rows data |}
| PutLexAlt c r d =>
  {| rosters := rosters data; dispositions := dispositions data;
     lex_alt := put (lex_alt data) c r d; mixfix_rows := mixfix_rows data |}
| AppendMixfix row =>
  {| rosters := rosters data; dispositions := dispositions data;
     lex_alt := lex_alt data; mixfix_rows := mixfix_rows data ++ [row] |}
end.

Inductive Event := DataWrite (w : Write) | TokenQuotation (occurrence : nat).
Definition original_step data event := match event with
| DataWrite w => write w data | TokenQuotation _ => data end.
Definition project event := match event with
| DataWrite w => [w] | TokenQuotation _ => [] end.
Definition original events data := fold_left original_step events data.
Definition shared events data :=
  fold_left (fun state w => write w state) (flat_map project events) data.

Theorem erase_quotation_preserves_all_data : forall events data,
  shared events data = original events data.
Proof.
  induction events as [|event rest IH]; intros data; [reflexivity|].
  destruct event; cbn [shared original flat_map project fold_left original_step];
    apply IH.
Qed.

Definition member_writes category member disposition :=
  [PutDisposition category member disposition; PutLexAlt category member disposition].
Definition prefix_group_writes category spine body roster := match roster with
| [] => None
| first :: rest => Some
  (PutRoster category first roster ::
   member_writes category first (GroupFirst spine body first) ++
   flat_map (fun member => member_writes category member GroupRest) rest)
end.

Theorem first_member_keeps_complete_roster_and_weight : forall c s b first rest,
  prefix_group_writes c s b (first :: rest) = Some
    (PutRoster c first (first :: rest) ::
     PutDisposition c first (GroupFirst s b first) ::
     PutLexAlt c first (GroupFirst s b first) ::
     flat_map (fun m => member_writes c m GroupRest) rest).
Proof. reflexivity. Qed.
Theorem empty_prefix_group_is_not_success : forall c s b,
  prefix_group_writes c s b [] = None.
Proof. reflexivity. Qed.
Theorem writes_preserve_disposition_lex_alt_pair : forall c m d,
  member_writes c m d = [PutDisposition c m d; PutLexAlt c m d].
Proof. reflexivity. Qed.
Theorem exact_key_last_write : forall A (table : nat -> nat -> option A) c r old new,
  put (put table c r old) c r new c r = Some new.
Proof. intros. unfold put. now rewrite !Nat.eqb_refl. Qed.
Theorem other_key_preserved : forall A (table : nat -> nat -> option A) c r value x y,
  (Nat.eqb x c && Nat.eqb y r) = false ->
  put table c r value x y = table x y.
Proof. intros. unfold put. now rewrite H. Qed.
Theorem mixfix_keeps_slice_members : forall d t g,
  members (mixfix_row d t g) = M.group_member_rule_idxs g.
Proof. reflexivity. Qed.
Theorem mixfix_keeps_distinct_dispatch_and_result : forall d t g,
  (dispatch (mixfix_row d t g), result_category (mixfix_row d t g)) =
  (d, M.group_result_src g).
Proof. reflexivity. Qed.
Theorem mixfix_appends_in_encounter_order : forall first second data,
  mixfix_rows (write (AppendMixfix second) (write (AppendMixfix first) data)) =
  ((mixfix_rows data ++ [first]) ++ [second])%list.
Proof. reflexivity. Qed.

(** Same-body Result lifting uses the checked generic first-error law. It does
    not identify resolver refusal with observation failure: existing resolver
    Result is an ordinary response and retains the original continuation. *)
Definition reused_callback_failure_law := @C.first_error_skips_any_continuation.
Definition reused_callback_all_ok_law := @C.all_ok_exact_original.

Print Assumptions erase_quotation_preserves_all_data.
Print Assumptions first_member_keeps_complete_roster_and_weight.
Print Assumptions empty_prefix_group_is_not_success.
Print Assumptions writes_preserve_disposition_lex_alt_pair.
Print Assumptions exact_key_last_write.
Print Assumptions other_key_preserved.
Print Assumptions mixfix_keeps_slice_members.
Print Assumptions mixfix_keeps_distinct_dispatch_and_result.
Print Assumptions mixfix_appends_in_encounter_order.
End FactoringEmissionData.
