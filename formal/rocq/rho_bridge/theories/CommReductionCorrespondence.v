(*
 * CommReductionCorrespondence: a small process-calculus model for the
 * Rho-native Dovetail backend.
 *
 * A Dovetail rule is represented by a list of premise facts, a pure guard, and
 * one output fact. Lowering turns each rule into a persistent Rho contract with
 * the same premises, guard, and output. RSpace COMM is modeled as a transition
 * that inserts an emitted fact by exact key, and traces are finite sequences of
 * those transitions.
 *
 * Proven here, with no admitted facts:
 *   - one COMM firing of a lowered contract is exactly one Dovetail rule step;
 *   - every lowered Rho trace has a Dovetail transition trace;
 *   - every Dovetail transition trace has a lowered Rho trace;
 *   - exact-key insertion preserves precisely set membership;
 *   - independent scheduler order is observationally irrelevant after exact-key
 *     deduplication.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Section CommReductionCorrespondence.

  (* Facts stand for exact Dovetail fact keys / RSpace payload identities.  Using
     nat keeps this file axiom-free while modeling the exact-key quotient that the
     backend exposes to the differential oracle. *)
  Definition Fact : Type := nat.

  Record Rule : Type := {
    rule_premises : list Fact;
    rule_guard : bool;
    rule_output : Fact
  }.

  Record Contract : Type := {
    contract_premises : list Fact;
    contract_guard : bool;
    contract_output : Fact
  }.

  (* The supported Rho lowering preserves premise channels, the guard, and the
     emitted fact. Unsupported rules are handled by RhoLoweringTotalOrRejects.v;
     this file proves the semantic correspondence for the lowered part. *)
  Definition lower_rule (r : Rule) : Contract :=
    {|
      contract_premises := rule_premises r;
      contract_guard := rule_guard r;
      contract_output := rule_output r
    |}.

  Definition all_present (facts premises : list Fact) : Prop :=
    forall p, In p premises -> In p facts.

  Definition dovetail_step (facts : list Fact) (r : Rule) (out : Fact) : Prop :=
    all_present facts (rule_premises r)
    /\ rule_guard r = true
    /\ out = rule_output r.

  Definition rho_comm (facts : list Fact) (c : Contract) (out : Fact) : Prop :=
    all_present facts (contract_premises c)
    /\ contract_guard c = true
    /\ out = contract_output c.

  Theorem comm_step_correspondence : forall facts r out,
    rho_comm facts (lower_rule r) out <-> dovetail_step facts r out.
  Proof.
    intros facts r out. unfold rho_comm, dovetail_step, lower_rule. simpl.
    split; intro H; exact H.
  Qed.

  Definition insert_exact (f : Fact) (facts : list Fact) : list Fact :=
    if existsb (Nat.eqb f) facts then facts else f :: facts.

  Inductive dovetail_transition (rules : list Rule) : list Fact -> list Fact -> Prop :=
    | dovetail_fire : forall facts r out,
        In r rules ->
        dovetail_step facts r out ->
        dovetail_transition rules facts (insert_exact out facts).

  Inductive rho_transition (contracts : list Contract) : list Fact -> list Fact -> Prop :=
    | rho_fire : forall facts c out,
        In c contracts ->
        rho_comm facts c out ->
        rho_transition contracts facts (insert_exact out facts).

  Lemma lowered_contract_inversion : forall rules c,
    In c (map lower_rule rules) ->
    exists r, In r rules /\ c = lower_rule r.
  Proof.
    intros rules c Hin. apply in_map_iff in Hin.
    destruct Hin as [r [Heq Hin]].
    exists r. split; [exact Hin | symmetry; exact Heq].
  Qed.

  Lemma lower_rule_in : forall rules r,
    In r rules -> In (lower_rule r) (map lower_rule rules).
  Proof.
    intros rules r Hin. apply in_map. exact Hin.
  Qed.

  Theorem lowered_transition_sound : forall rules facts facts',
    rho_transition (map lower_rule rules) facts facts' ->
    dovetail_transition rules facts facts'.
  Proof.
    intros rules facts facts' H.
    inversion H as [facts0 c out Hc Hcomm HeqFacts HeqFacts']; subst.
    apply lowered_contract_inversion in Hc.
    destruct Hc as [r [Hin Hr]]. subst c.
    apply dovetail_fire with (r := r) (out := out).
    - exact Hin.
    - apply comm_step_correspondence. exact Hcomm.
  Qed.

  Theorem lowered_transition_complete : forall rules facts facts',
    dovetail_transition rules facts facts' ->
    rho_transition (map lower_rule rules) facts facts'.
  Proof.
    intros rules facts facts' H.
    inversion H as [facts0 r out Hin Hstep HeqFacts HeqFacts']; subst.
    apply rho_fire with (c := lower_rule r) (out := out).
    - apply lower_rule_in. exact Hin.
    - apply comm_step_correspondence. exact Hstep.
  Qed.

  Theorem lowered_transition_equivalent : forall rules facts facts',
    rho_transition (map lower_rule rules) facts facts'
    <-> dovetail_transition rules facts facts'.
  Proof.
    intros rules facts facts'. split.
    - apply lowered_transition_sound.
    - apply lowered_transition_complete.
  Qed.

  Inductive trace (step : list Fact -> list Fact -> Prop) :
    list Fact -> list Fact -> Prop :=
    | trace_refl : forall facts,
        trace step facts facts
    | trace_cons : forall facts facts' facts'',
        step facts facts' ->
        trace step facts' facts'' ->
        trace step facts facts''.

  Theorem lowered_trace_sound : forall seed rules facts,
    trace (rho_transition (map lower_rule rules)) seed facts ->
    trace (dovetail_transition rules) seed facts.
  Proof.
    intros seed rules facts H.
    induction H as [facts | facts facts' facts'' Hstep _ IH].
    - apply trace_refl.
    - apply trace_cons with (facts' := facts').
      + apply lowered_transition_sound. exact Hstep.
      + exact IH.
  Qed.

  Theorem lowered_trace_complete : forall seed rules facts,
    trace (dovetail_transition rules) seed facts ->
    trace (rho_transition (map lower_rule rules)) seed facts.
  Proof.
    intros seed rules facts H.
    induction H as [facts | facts facts' facts'' Hstep _ IH].
    - apply trace_refl.
    - apply trace_cons with (facts' := facts').
      + apply lowered_transition_complete. exact Hstep.
      + exact IH.
  Qed.

  Theorem lowered_trace_equivalent : forall seed rules facts,
    trace (rho_transition (map lower_rule rules)) seed facts
    <-> trace (dovetail_transition rules) seed facts.
  Proof.
    intros seed rules facts. split.
    - apply lowered_trace_sound.
    - apply lowered_trace_complete.
  Qed.

  Lemma existsb_nat_eq_true : forall x xs,
    existsb (Nat.eqb x) xs = true <-> In x xs.
  Proof.
    intros x xs. rewrite existsb_exists.
    split.
    - intros [y [Hin Heq]]. apply Nat.eqb_eq in Heq. subst y. exact Hin.
    - intros Hin. exists x. split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  Lemma existsb_nat_eq_false : forall x xs,
    existsb (Nat.eqb x) xs = false <-> ~ In x xs.
  Proof.
    intros x xs.
    destruct (existsb (Nat.eqb x) xs) eqn:Hex.
    - split.
      + intro H. discriminate H.
      + intro Hnot. apply existsb_nat_eq_true in Hex. contradiction.
    - split.
      + intro Hfalse. intro Hin.
        assert (Htrue : existsb (Nat.eqb x) xs = true).
        { apply existsb_nat_eq_true. exact Hin. }
        rewrite Htrue in Hex. discriminate Hex.
      + intro Hnot. reflexivity.
  Qed.

  Theorem insert_exact_membership : forall facts f x,
    In x (insert_exact f facts) <-> x = f \/ In x facts.
  Proof.
    intros facts f x. unfold insert_exact.
    destruct (existsb (Nat.eqb f) facts) eqn:Hex.
    - apply existsb_nat_eq_true in Hex.
      split.
      + intro Hin. right. exact Hin.
      + intros [Heq | Hin].
        * subst x. exact Hex.
        * exact Hin.
    - split.
      + intros [Heq | Hin].
        * left. symmetry. exact Heq.
        * right. exact Hin.
      + intros [Heq | Hin].
        * left. symmetry. exact Heq.
        * right. exact Hin.
  Qed.

  Theorem insert_exact_preserves_existing : forall facts f x,
    In x facts -> In x (insert_exact f facts).
  Proof.
    intros facts f x Hin. apply insert_exact_membership. right. exact Hin.
  Qed.

  Theorem insert_exact_adds_output : forall facts f,
    In f (insert_exact f facts).
  Proof.
    intros facts f. apply insert_exact_membership. left. reflexivity.
  Qed.

  Theorem insert_exact_idempotent_membership : forall facts f x,
    In x (insert_exact f (insert_exact f facts))
    <-> In x (insert_exact f facts).
  Proof.
    intros facts f x. repeat rewrite insert_exact_membership.
    split.
    - intros [Hxf | [Hxf | Hin]].
      + left. exact Hxf.
      + left. exact Hxf.
      + right. exact Hin.
    - intros [Hxf | Hin].
      + left. exact Hxf.
      + right. right. exact Hin.
  Qed.

  Theorem insert_exact_commutes_membership : forall facts a b x,
    In x (insert_exact a (insert_exact b facts))
    <-> In x (insert_exact b (insert_exact a facts)).
  Proof.
    intros facts a b x. repeat rewrite insert_exact_membership.
    split.
    - intros [Hxa | [Hxb | Hin]].
      + right. left. exact Hxa.
      + left. exact Hxb.
      + right. right. exact Hin.
    - intros [Hxb | [Hxa | Hin]].
      + right. left. exact Hxb.
      + left. exact Hxa.
      + right. right. exact Hin.
  Qed.

  Theorem independent_comm_order_observationally_equal : forall facts c1 c2 f1 f2 x,
    rho_comm facts c1 f1 ->
    rho_comm facts c2 f2 ->
    In x (insert_exact f1 (insert_exact f2 facts))
    <-> In x (insert_exact f2 (insert_exact f1 facts)).
  Proof.
    intros facts c1 c2 f1 f2 x Hc1 Hc2.
    apply insert_exact_commutes_membership.
  Qed.

End CommReductionCorrespondence.
