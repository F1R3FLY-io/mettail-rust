(** Exact tagged-list transport of the existing complete neutral receipts.

    This is the structural wire layer, not a second semantic verifier. UInt
    and Blob are admitted scalar atoms: their finite-width, signed BigInt,
    commitment-length and concrete Par-envelope refinements are separate.
    The schema has fixed nesting depth; variable rosters are traversed once
    per enclosing level. No embedded syntax is parsed and no record is pruned.

    Each layer has an executable partial decoder and a proved left inverse.
    Malformed tags, arities and scalar kinds are refused. The all-roster law
    retains order and multiplicity, including all exhaustive proofs. It does
    not establish canonical sorting, semantic evidence validity, resource
    bounds or authority to publish the decoded records. *)
From Stdlib Require Import List Arith.PeanoNat.
From RuntimeGrammar Require Import SemanticReceiptTransport.
Import ListNotations.

Module SemanticReceiptWire.
Module R := SemanticReceiptTransport.SemanticReceiptTransport.

Inductive Value := UInt (n : nat) | Blob (bytes : R.Bytes) | Tuple (fields : list Value).

Fixpoint decode_all {A B : Type} (decode : A -> option B) (items : list A)
    : option (list B) :=
  match items with
  | [] => Some []
  | item :: rest =>
      match decode item, decode_all decode rest with
      | Some value, Some values => Some (value :: values)
      | _, _ => None
      end
  end.

Lemma decode_all_map : forall (A B : Type) (encode : A -> B) decode,
  (forall x, decode (encode x) = Some x) ->
  forall xs, decode_all decode (map encode xs) = Some xs.
Proof.
  intros A B encode decode inverse xs. induction xs as [|x rest IH].
  - reflexivity.
  - cbn. now rewrite inverse, IH.
Qed.

Definition decode_blob value := match value with Blob b => Some b | _ => None end.
Lemma blob_inverse : forall b, decode_blob (Blob b) = Some b.
Proof. reflexivity. Qed.

Definition encode_opcode opcode := UInt (match opcode with
  | R.ExactTermEq => 0 | R.Utf8AtEnd => 1 | R.Utf8ScalarAt => 2
  | R.Utf8Slice => 3 | R.CheckedNatAdd => 4 | R.Utf8ConcatMany => 5 end).
Definition decode_opcode value := match value with
  | UInt 0 => Some R.ExactTermEq | UInt 1 => Some R.Utf8AtEnd
  | UInt 2 => Some R.Utf8ScalarAt | UInt 3 => Some R.Utf8Slice
  | UInt 4 => Some R.CheckedNatAdd | UInt 5 => Some R.Utf8ConcatMany
  | _ => None end.
Theorem opcode_inverse : forall opcode, decode_opcode (encode_opcode opcode) = Some opcode.
Proof. destruct opcode; reflexivity. Qed.

Definition encode_premise premise := Tuple (match premise with
  | R.Freshness rule index => [UInt 0; UInt rule; UInt index]
  | R.Transition rule index child => [UInt 1; UInt rule; UInt index; UInt child]
  | R.Judgment rule index judgment proofs steps =>
      [UInt 2; UInt rule; UInt index; UInt judgment; UInt proofs; UInt steps]
  | R.ForAll rule index elements => [UInt 3; UInt rule; UInt index; UInt elements]
  | R.Intrinsic rule index opcode inputs outputs work =>
      [UInt 4; UInt rule; UInt index; encode_opcode opcode;
       Tuple (map Blob inputs); Tuple (map Blob outputs); UInt work]
  | R.Guard rule index guard evidence =>
      [UInt 5; UInt rule; UInt index; Blob guard; Blob evidence]
  end).

Definition decode_premise value := match value with
  | Tuple [UInt 0; UInt rule; UInt index] => Some (R.Freshness rule index)
  | Tuple [UInt 1; UInt rule; UInt index; UInt child] => Some (R.Transition rule index child)
  | Tuple [UInt 2; UInt rule; UInt index; UInt judgment; UInt proofs; UInt steps] =>
      Some (R.Judgment rule index judgment proofs steps)
  | Tuple [UInt 3; UInt rule; UInt index; UInt elements] => Some (R.ForAll rule index elements)
  | Tuple [UInt 4; UInt rule; UInt index; opcode; Tuple inputs; Tuple outputs; UInt work] =>
      match decode_opcode opcode, decode_all decode_blob inputs, decode_all decode_blob outputs with
      | Some op, Some ins, Some outs => Some (R.Intrinsic rule index op ins outs work)
      | _, _, _ => None end
  | Tuple [UInt 5; UInt rule; UInt index; Blob guard; Blob evidence] =>
      Some (R.Guard rule index guard evidence)
  | _ => None end.

Theorem premise_inverse : forall premise,
  decode_premise (encode_premise premise) = Some premise.
Proof.
  destruct premise; cbn -[encode_opcode decode_opcode]; try reflexivity.
  rewrite opcode_inverse.
  repeat rewrite (decode_all_map _ _ Blob decode_blob blob_inverse).
  reflexivity.
Qed.

Definition encode_step step := Tuple [UInt (R.step_rule step); Blob (R.step_before step);
  Blob (R.step_after step); Tuple (map encode_premise (R.step_premises step))].
Definition decode_step value := match value with
  | Tuple [UInt rule; Blob before; Blob after; Tuple premises] =>
      option_map (fun ps => R.step rule before after ps) (decode_all decode_premise premises)
  | _ => None end.
Theorem step_inverse : forall step, decode_step (encode_step step) = Some step.
Proof.
  intros [rule before after premises]. cbn.
  rewrite (decode_all_map _ _ encode_premise decode_premise premise_inverse).
  reflexivity.
Qed.

Definition encode_hop hop := Tuple [Blob (R.hop_before hop); Blob (R.hop_after hop);
  Tuple (map encode_step (R.hop_proofs hop)); UInt (R.hop_work hop)].
Definition decode_hop value := match value with
  | Tuple [Blob before; Blob after; Tuple proofs; UInt work] =>
      option_map (fun ps => R.hop before after ps work) (decode_all decode_step proofs)
  | _ => None end.
Theorem hop_inverse : forall hop, decode_hop (encode_hop hop) = Some hop.
Proof.
  intros [before after proofs work]. cbn.
  rewrite (decode_all_map _ _ encode_step decode_step step_inverse).
  reflexivity.
Qed.

Definition encode_resource resource := Tuple (match resource with
  | R.NoGrade => [UInt 0]
  | R.CheckedGrade sort grade image => [UInt 1; UInt sort; Blob grade; Blob image] end).
Definition decode_resource value := match value with
  | Tuple [UInt 0] => Some R.NoGrade
  | Tuple [UInt 1; UInt sort; Blob grade; Blob image] => Some (R.CheckedGrade sort grade image)
  | _ => None end.
Theorem resource_inverse : forall resource,
  decode_resource (encode_resource resource) = Some resource.
Proof. destruct resource; reflexivity. Qed.

Definition encode_effect effect := UInt (match effect with
  | R.Pure => 0 | R.Structural => 1 | R.Behavioral => 2
  | R.ResourceEffect => 3 | R.External => 4 end).
Definition decode_effect value := match value with
  | UInt 0 => Some R.Pure | UInt 1 => Some R.Structural | UInt 2 => Some R.Behavioral
  | UInt 3 => Some R.ResourceEffect | UInt 4 => Some R.External | _ => None end.
Theorem effect_inverse : forall effect, decode_effect (encode_effect effect) = Some effect.
Proof. destruct effect; reflexivity. Qed.

Definition encode_receipt r := Tuple [Blob (R.language r); Blob (R.theory r); Blob (R.image r);
  UInt (R.action r); UInt (R.rule r); Blob (R.input r); Blob (R.output r);
  UInt (R.effect r); encode_effect (R.effect_class r); encode_resource (R.resource r);
  Tuple (map encode_premise (R.premises r)); Tuple (map encode_hop (R.hops r)); UInt (R.work r)].
Definition decode_receipt value := match value with
  | Tuple [Blob language; Blob theory; Blob image; UInt action; UInt rule;
           Blob input; Blob output; UInt effect; effect_class; resource;
           Tuple premises; Tuple hops; UInt work] =>
      match decode_effect effect_class, decode_resource resource,
            decode_all decode_premise premises, decode_all decode_hop hops with
      | Some ec, Some res, Some ps, Some hs =>
          Some (R.receipt language theory image action rule input output effect ec res ps hs work)
      | _, _, _, _ => None end
  | _ => None end.

Theorem receipt_inverse : forall receipt,
  decode_receipt (encode_receipt receipt) = Some receipt.
Proof.
  intros [language theory image action rule input output effect effect_class resource premises hops work].
  cbn -[encode_effect decode_effect encode_resource decode_resource].
  rewrite effect_inverse, resource_inverse.
  rewrite (decode_all_map _ _ encode_premise decode_premise premise_inverse).
  rewrite (decode_all_map _ _ encode_hop decode_hop hop_inverse).
  reflexivity.
Qed.

Theorem receipt_encoding_is_injective : forall a b,
  encode_receipt a = encode_receipt b -> a = b.
Proof.
  intros a b equality. apply (f_equal decode_receipt) in equality.
  rewrite !receipt_inverse in equality. now inversion equality.
Qed.

Definition encode_roster receipts := Tuple (map encode_receipt receipts).
Definition decode_roster value := match value with
  | Tuple receipts => decode_all decode_receipt receipts | _ => None end.
Theorem roster_inverse : forall receipts,
  decode_roster (encode_roster receipts) = Some receipts.
Proof.
  intros. apply (decode_all_map _ _ encode_receipt decode_receipt receipt_inverse).
Qed.

Theorem roster_preserves_every_occurrence : forall receipts decoded,
  decode_roster (encode_roster receipts) = Some decoded -> decoded = receipts.
Proof. intros. rewrite roster_inverse in H. now inversion H. Qed.

(** A reflected term is transported intact next to its complete receipt. This
    wrapper does not inspect the term, prove its closure, or validate its
    semantic relation to the receipt; the installed service owns those facts. *)
Definition encode_result (result : Value * R.Receipt) :=
  Tuple [fst result; encode_receipt (snd result)].
Definition decode_result value := match value with
  | Tuple [term; receipt] => option_map (fun r => (term, r)) (decode_receipt receipt)
  | _ => None end.
Theorem result_inverse : forall result,
  decode_result (encode_result result) = Some result.
Proof.
  intros [term receipt]. cbn -[encode_receipt decode_receipt].
  now rewrite receipt_inverse.
Qed.

Definition encode_results results := Tuple (map encode_result results).
Definition decode_results value := match value with
  | Tuple results => decode_all decode_result results | _ => None end.
Theorem results_inverse : forall results,
  decode_results (encode_results results) = Some results.
Proof. apply (decode_all_map _ _ encode_result decode_result result_inverse). Qed.

Theorem results_retain_pairing_order_and_multiplicity : forall results decoded,
  decode_results (encode_results results) = Some decoded -> decoded = results.
Proof. intros. rewrite results_inverse in H. now inversion H. Qed.

Theorem result_encoding_is_injective : forall a b,
  encode_results a = encode_results b -> a = b.
Proof.
  intros a b H. apply (f_equal decode_results) in H.
  rewrite !results_inverse in H. now inversion H.
Qed.

Example absent_grade_is_not_zero_grade :
  encode_resource R.NoGrade <> encode_resource (R.CheckedGrade 0 [] []).
Proof. discriminate. Qed.
Example unknown_premise_tag_is_refused : decode_premise (Tuple [UInt 6; UInt 0; UInt 0]) = None.
Proof. reflexivity. Qed.
Example extra_premise_field_is_refused :
  decode_premise (Tuple [UInt 0; UInt 0; UInt 0; UInt 0]) = None.
Proof. reflexivity. Qed.

End SemanticReceiptWire.

Print Assumptions SemanticReceiptWire.opcode_inverse.
Print Assumptions SemanticReceiptWire.premise_inverse.
Print Assumptions SemanticReceiptWire.step_inverse.
Print Assumptions SemanticReceiptWire.hop_inverse.
Print Assumptions SemanticReceiptWire.resource_inverse.
Print Assumptions SemanticReceiptWire.effect_inverse.
Print Assumptions SemanticReceiptWire.receipt_inverse.
Print Assumptions SemanticReceiptWire.receipt_encoding_is_injective.
Print Assumptions SemanticReceiptWire.roster_inverse.
Print Assumptions SemanticReceiptWire.roster_preserves_every_occurrence.
Print Assumptions SemanticReceiptWire.result_inverse.
Print Assumptions SemanticReceiptWire.results_inverse.
Print Assumptions SemanticReceiptWire.results_retain_pairing_order_and_multiplicity.
Print Assumptions SemanticReceiptWire.result_encoding_is_injective.
Print Assumptions SemanticReceiptWire.absent_grade_is_not_zero_grade.
Print Assumptions SemanticReceiptWire.unknown_premise_tag_is_refused.
Print Assumptions SemanticReceiptWire.extra_premise_field_is_refused.
