From Stdlib Require Import PeanoNat Lia Wellfounded Wf_nat.

Definition ForestNode := (nat * nat)%type.

Definition span_length (node : ForestNode) : nat := fst node.
Definition grammar_rank (node : ForestNode) : nat := snd node.

Definition node_measure (rank_bound : nat) (node : ForestNode) : nat :=
  span_length node * S rank_bound + grammar_rank node.

Definition ranked_child (rank_bound : nat) (child parent : ForestNode) : Prop :=
  grammar_rank child <= rank_bound /\
  grammar_rank parent <= rank_bound /\
  (span_length child < span_length parent \/
   (span_length child = span_length parent /\
    grammar_rank child < grammar_rank parent)).

Theorem ranked_child_decreases_measure :
  forall rank_bound child parent,
    ranked_child rank_bound child parent ->
    node_measure rank_bound child < node_measure rank_bound parent.
Proof.
  intros rank_bound [child_span child_rank] [parent_span parent_rank].
  unfold ranked_child, node_measure, span_length, grammar_rank. simpl.
  intros [Hchild_rank [Hparent_rank [Hspan | [Hspan Hrank]]]].
  - nia.
  - subst child_span. nia.
Qed.

Theorem ranked_child_is_well_founded :
  forall rank_bound, well_founded (ranked_child rank_bound).
Proof.
  intros rank_bound node.
  remember (node_measure rank_bound node) as measure eqn:Hmeasure.
  revert node Hmeasure.
  induction measure using lt_wf_ind.
  intros node Hnode. constructor. intros child Hchild.
  apply H with (m := node_measure rank_bound child).
  - rewrite Hnode. apply ranked_child_decreases_measure. exact Hchild.
  - reflexivity.
Qed.

Definition zero_span_call_certificate
    (rank : nat -> nat) (parent child : nat) : Prop :=
  rank child < rank parent.

Theorem zero_span_call_cannot_cycle :
  forall rank first second,
    zero_span_call_certificate rank first second ->
    ~ zero_span_call_certificate rank second first.
Proof.
  intros rank first second Hforward Hbackward.
  unfold zero_span_call_certificate in *. lia.
Qed.

Theorem same_span_recursive_realization_terminates :
  forall rank_bound child parent,
    grammar_rank child <= rank_bound ->
    grammar_rank parent <= rank_bound ->
    span_length child = span_length parent ->
    grammar_rank child < grammar_rank parent ->
    node_measure rank_bound child < node_measure rank_bound parent.
Proof.
  intros rank_bound child parent Hchild Hparent Hspan Hrank.
  apply ranked_child_decreases_measure. split; [exact Hchild |].
  split; [exact Hparent |]. right. split; assumption.
Qed.

Print Assumptions ranked_child_is_well_founded.
Print Assumptions zero_span_call_cannot_cycle.
Print Assumptions same_span_recursive_realization_terminates.
