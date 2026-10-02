(** Exact structural transport for actionless relation observations.

    This refines the v2 result shape, not semantic receipt verification or
    capability authorization. The concrete Par codec must additionally check
    canonical finite-width scalars, fingerprints, resource limits, and closure.
    All rosters retain order and multiplicity, including duplicate proofs. *)
From Stdlib Require Import List.
From RuntimeGrammar Require Import SemanticReceiptTransport SemanticReceiptWire.
Import ListNotations.

Module SemanticRelationWire.
Module R := SemanticReceiptTransport.SemanticReceiptTransport.
Module W := SemanticReceiptWire.SemanticReceiptWire.

Record RelationReceipt := relation_receipt {
  relation_language : R.Bytes;
  relation_theory : R.Bytes;
  relation_image : R.Bytes;
  relation_sort : nat;
  relation_input : R.Bytes;
  relation_output : R.Bytes;
  relation_hops : list R.Hop;
  relation_work : nat
}.

Inductive Direction := GuestToHost | HostToGuest.

Definition encode_direction d := W.UInt (match d with
  | GuestToHost => 0 | HostToGuest => 1 end).
Definition decode_direction v := match v with
  | W.UInt 0 => Some GuestToHost | W.UInt 1 => Some HostToGuest
  | _ => None end.
Lemma direction_inverse : forall d, decode_direction (encode_direction d) = Some d.
Proof. destruct d; reflexivity. Qed.

Record ProjectionReceipt := projection_receipt {
  projected_language : R.Bytes;
  projection_base_image : R.Bytes;
  projection_image : R.Bytes;
  projection_host_signature : R.Bytes;
  projection_host_codec : R.Bytes;
  projection_id : nat;
  projection_direction : Direction;
  projection_input_sort : nat;
  projection_output_sort : nat;
  projection_occurrence : nat;
  projection_rule : nat;
  projection_input : R.Bytes;
  projection_output : R.Bytes;
  projection_resource : R.Resource;
  projection_premises : list R.Premise;
  projection_work : nat
}.

Definition encode_relation r := W.Tuple [
  W.Blob (relation_language r); W.Blob (relation_theory r);
  W.Blob (relation_image r); W.UInt (relation_sort r);
  W.Blob (relation_input r); W.Blob (relation_output r);
  W.Tuple (map W.encode_hop (relation_hops r)); W.UInt (relation_work r)].

Definition decode_relation v := match v with
  | W.Tuple [W.Blob language; W.Blob theory; W.Blob image; W.UInt sort;
             W.Blob input; W.Blob output; W.Tuple hops; W.UInt work] =>
      option_map (fun hs => relation_receipt language theory image sort input output hs work)
        (W.decode_all W.decode_hop hops)
  | _ => None end.

Theorem relation_inverse : forall r, decode_relation (encode_relation r) = Some r.
Proof.
  intros [language theory image sort input output hops work]. cbn.
  rewrite (W.decode_all_map _ _ W.encode_hop W.decode_hop W.hop_inverse).
  reflexivity.
Qed.

Definition encode_projection p := W.Tuple [
  W.Blob (projected_language p); W.Blob (projection_base_image p);
  W.Blob (projection_image p); W.Blob (projection_host_signature p);
  W.Blob (projection_host_codec p); W.UInt (projection_id p);
  encode_direction (projection_direction p); W.UInt (projection_input_sort p);
  W.UInt (projection_output_sort p); W.UInt (projection_occurrence p);
  W.UInt (projection_rule p); W.Blob (projection_input p);
  W.Blob (projection_output p); W.encode_resource (projection_resource p);
  W.Tuple (map W.encode_premise (projection_premises p));
  W.UInt (projection_work p)].

Definition decode_projection v := match v with
  | W.Tuple [W.Blob language; W.Blob base; W.Blob image; W.Blob host;
             W.Blob codec; W.UInt id; direction; W.UInt input_sort;
             W.UInt output_sort; W.UInt occurrence; W.UInt rule;
             W.Blob input; W.Blob output; resource; W.Tuple premises;
             W.UInt work] =>
      match decode_direction direction, W.decode_resource resource,
            W.decode_all W.decode_premise premises with
      | Some d, Some grade, Some ps =>
          Some (projection_receipt language base image host codec id d
            input_sort output_sort occurrence rule input output grade ps work)
      | _, _, _ => None end
  | _ => None end.

Theorem projection_inverse : forall p,
  decode_projection (encode_projection p) = Some p.
Proof.
  intros [language base image host codec id direction input_sort output_sort
          occurrence rule input output resource premises work].
  cbn -[decode_direction encode_direction W.decode_resource W.encode_resource
         W.decode_all W.decode_premise W.encode_premise].
  rewrite direction_inverse, W.resource_inverse.
  rewrite (W.decode_all_map _ _ W.encode_premise W.decode_premise W.premise_inverse).
  reflexivity.
Qed.

Record Result := result {
  result_term : W.Value;
  result_relation : RelationReceipt;
  result_terminal_roster : list RelationReceipt;
  result_projection_roster : list ProjectionReceipt
}.

Definition encode_result r := W.Tuple [
  result_term r; encode_relation (result_relation r);
  W.Tuple (map encode_relation (result_terminal_roster r));
  W.Tuple (map encode_projection (result_projection_roster r))].

Definition decode_result v := match v with
  | W.Tuple [term; relation; W.Tuple terminal; W.Tuple projections] =>
      match decode_relation relation, W.decode_all decode_relation terminal,
            W.decode_all decode_projection projections with
      | Some root, Some ts, Some ps => Some (result term root ts ps)
      | _, _, _ => None end
  | _ => None end.

Theorem result_inverse : forall r, decode_result (encode_result r) = Some r.
Proof.
  intros [term relation terminal projections].
  cbn -[decode_relation encode_relation W.decode_all decode_projection encode_projection].
  rewrite relation_inverse.
  rewrite (W.decode_all_map _ _ encode_relation decode_relation relation_inverse).
  rewrite (W.decode_all_map _ _ encode_projection decode_projection projection_inverse).
  reflexivity.
Qed.

Definition encode_results results := W.Tuple (map encode_result results).
Definition decode_results value := match value with
  | W.Tuple results => W.decode_all decode_result results | _ => None end.

Theorem results_inverse : forall results,
  decode_results (encode_results results) = Some results.
Proof. apply (W.decode_all_map _ _ encode_result decode_result result_inverse). Qed.

Theorem results_retain_all_proof_occurrences : forall results decoded,
  decode_results (encode_results results) = Some decoded -> decoded = results.
Proof. intros. rewrite results_inverse in H. now inversion H. Qed.

Theorem results_encoding_is_injective : forall a b,
  encode_results a = encode_results b -> a = b.
Proof.
  intros a b H. apply (f_equal decode_results) in H.
  rewrite !results_inverse in H. now inversion H.
Qed.

Definition decode_v2_request value := match value with
  | W.Tuple [W.UInt 2; handle; W.Blob category; W.Blob judgment;
             W.Blob projection; input; limits; reply] =>
      Some (handle, category, judgment, projection, input, limits, reply)
  | _ => None end.

Theorem v1_request_cannot_decode_as_v2 : forall handle name input limits reply,
  decode_v2_request (W.Tuple [W.UInt 1; handle; name; input; limits; reply]) = None.
Proof. reflexivity. Qed.

End SemanticRelationWire.

Print Assumptions SemanticRelationWire.relation_inverse.
Print Assumptions SemanticRelationWire.projection_inverse.
Print Assumptions SemanticRelationWire.result_inverse.
Print Assumptions SemanticRelationWire.results_inverse.
Print Assumptions SemanticRelationWire.results_retain_all_proof_occurrences.
Print Assumptions SemanticRelationWire.results_encoding_is_injective.
Print Assumptions SemanticRelationWire.v1_request_cannot_decode_as_v2.
