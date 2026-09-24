(** Checked refinement of the TWO existing factoring spine-ID allocation sites.

    PrefixFactoringProjection and MixfixDescriptorProjection retain the original
    discovery, grouping, tree, callback and late-ceiling algorithms. This model
    changes only base+ordinal and ordinal+1: a representable allocation is exact;
    failure publishes no group ID and appends a hard refusal to the existing
    sink. The ordinal remains unchanged on failure. Callers still run their
    original remaining observations and late recovery/u16 ceiling checks.

    None is NOT an ordinary unfactored candidate: the Rust caller must append
    LIMIT_REFUSAL at that site. Owned assembly rejects a nonempty refusal sink;
    static emission renders it as compile_error. No default ID is manufactured.
    No global grammar limit, new grouping algorithm, or allocator theorem is
    introduced. Other existing width/index preconditions remain unchanged.
*)
From Stdlib Require Import List NArith Lia.
From PrattailWpdaRuntime Require Import TraversalMarkerProjection
  PrefixFactoringProjection MixfixDescriptorProjection.
Import ListNotations.
Open Scope N_scope.

Module FactoringOrdinalAdmission.
Module T := TraversalMarkerProjection.TraversalMarkerProjection.
Module P := PrefixFactoringProjection.PrefixFactoringProjection.
Module M := MixfixDescriptorProjection.MixfixDescriptorProjection.
Definition base : N := N.of_nat P.SPINE_RULE_BASE.

Definition allocate ordinal : option (N * N) :=
  match T.checked_width T.max16 (base + ordinal) with
  | None => None
  | Some id => match T.checked_width T.max16 (ordinal + 1) with
    | None => None | Some next => Some (id, next) end
  end.

Theorem successful_allocation_is_exact : forall ordinal id next,
  allocate ordinal = Some (id, next) ->
  id = base + ordinal /\ next = ordinal + 1 /\ id <= T.max16 /\ next <= T.max16.
Proof.
  intros ordinal id next H; unfold allocate in H.
  destruct (T.checked_width T.max16 (base + ordinal)) as [encoded|] eqn:E;
    try discriminate.
  destruct (T.checked_width T.max16 (ordinal + 1)) as [after|] eqn:A;
    try discriminate.
  inversion H; subst encoded after.
  apply T.checked_width_exact in E; apply T.checked_width_exact in A.
  destruct E as [-> E]; destruct A as [-> A].
  repeat split; assumption || reflexivity.
Qed.

Theorem representable_allocation_preserves_original : forall ordinal,
  base + ordinal <= T.max16 -> ordinal + 1 <= T.max16 ->
  allocate ordinal = Some (base + ordinal, ordinal + 1).
Proof.
  intros ordinal Hbase Hnext; unfold allocate, T.checked_width.
  apply N.leb_le in Hbase; apply N.leb_le in Hnext.
  rewrite Hbase, Hnext; reflexivity.
Qed.

Theorem overflowing_id_refuses : forall ordinal,
  T.max16 < base + ordinal -> allocate ordinal = None.
Proof.
  intros ordinal H; unfold allocate, T.checked_width.
  assert (E : (base + ordinal <=? T.max16) = false) by (apply N.leb_gt; exact H).
  rewrite E; reflexivity.
Qed.

Record State := { next_ordinal : N; published_ids : list N; refusals : list N }.
Definition step state := match allocate (next_ordinal state) with
| Some (id, next) =>
  {| next_ordinal := next; published_ids := published_ids state ++ [id];
     refusals := refusals state |}
| None =>
  {| next_ordinal := next_ordinal state; published_ids := published_ids state;
     refusals := refusals state ++ [next_ordinal state] |}
end.

Theorem failure_keeps_counter_and_published_ids : forall state,
  allocate (next_ordinal state) = None ->
  next_ordinal (step state) = next_ordinal state /\
  published_ids (step state) = published_ids state /\
  refusals (step state) = refusals state ++ [next_ordinal state].
Proof. intros state H; unfold step; rewrite H; repeat split; reflexivity. Qed.

Definition publish state := match refusals state with
| [] => Some (published_ids state) | _ :: _ => None end.
Theorem failed_allocation_cannot_publish : forall state,
  allocate (next_ordinal state) = None -> publish (step state) = None.
Proof.
  intros state H; unfold publish, step; rewrite H; simpl.
  destruct (refusals state); reflexivity.
Qed.

Theorem exact_encoding_boundaries :
  allocate 0 = Some (63488, 1) /\
  allocate 2047 = Some (65535, 2048) /\
  allocate 2048 = None /\ allocate 65535 = None.
Proof. vm_compute; repeat split; reflexivity. Qed.

(** These are the UNCHANGED strict late ceilings: with recovery 0xFE00,
    1,535 groups are below it, whereas 1,536 reach it. The last representable
    ID is not newly admitted merely because checked arithmetic can encode it. *)
Theorem original_late_ceiling_boundaries :
  base + 1535 < 65024 /\ base + 1536 = 65024 /\
  base + 2047 = T.max16.
Proof. vm_compute; repeat split; reflexivity. Qed.

Print Assumptions successful_allocation_is_exact.
Print Assumptions representable_allocation_preserves_original.
Print Assumptions overflowing_id_refuses.
Print Assumptions failure_keeps_counter_and_published_ids.
Print Assumptions failed_allocation_cannot_publish.
Print Assumptions exact_encoding_boundaries.
Print Assumptions original_late_ceiling_boundaries.
End FactoringOrdinalAdmission.
