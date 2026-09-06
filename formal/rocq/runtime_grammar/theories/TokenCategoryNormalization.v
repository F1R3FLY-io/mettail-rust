(** Typed-token category normalization.

    A category-tagged token is a lexical inhabitant of that category. The
    runtime normalizer must retain this declaration even when the category
    also has explicit term productions. The added rule is administrative:
    it captures exactly that token, preserves the complete decoded semantic
    value, and contributes neither parse cost nor source-production rank.

    This model covers the new normalization and singleton-identity boundary.
    It does not re-prove lexer recognition, decoder authorization, chart
    saturation, or general ambiguity completeness. Those existing mechanisms
    remain unchanged. The token identifier denotes an accepted lexer candidate,
    including logical EOF tokens; no positive byte-length premise is imposed.
*)
From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import DerivationRank ImageAdmission RtnChart.
Import ListNotations.

Record Token := {
  token_id : nat;
  token_category : option nat
}.

Inductive Symbol :=
| CapturedToken (identifier : nat)
| UncapturedToken (identifier : nat)
| Nonterminal (identifier : nat)
| Foreign.

Record Bridge := {
  bridge_category : nat;
  bridge_symbols : list Symbol;
  bridge_production : option nat;
  bridge_cost : nat
}.

Definition make_bridge (token category : nat) : Bridge :=
  {| bridge_category := category;
     bridge_symbols := [CapturedToken token];
     bridge_production := None;
     bridge_cost := 0 |}.

Fixpoint token_bridges (tokens : list Token) : list Bridge :=
  match tokens with
  | [] => []
  | token :: rest =>
      match token_category token with
      | Some category => make_bridge (token_id token) category :: token_bridges rest
      | None => token_bridges rest
      end
  end.

Theorem bridge_membership_exact : forall tokens bridge,
  In bridge (token_bridges tokens) <->
  exists token category,
    In token tokens /\ token_category token = Some category /\
    bridge = make_bridge (token_id token) category.
Proof.
  induction tokens as [|token rest IH]; intros bridge; cbn.
  - split; [contradiction | intros [? [? [H _]]]; contradiction].
  - destruct (token_category token) as [category|] eqn:Hcategory; cbn.
    + rewrite IH. split.
      * intros [H | [other [c [Hin [Hcat Heq]]]]].
        -- exists token, category. split; [now left |]. auto.
        -- exists other, c. split; [now right |]. auto.
      * intros [other [c [[Heq | Hin] [Hcat Hbridge]]]].
        -- subst other. rewrite Hcategory in Hcat. inversion Hcat; subst c.
           left. symmetry. exact Hbridge.
        -- right. exists other, c. auto.
    + rewrite IH. split.
      * intros [other [c [Hin [Hcat Heq]]]].
        exists other, c. split; [now right |]. auto.
      * intros [other [c [[Heq | Hin] [Hcat Hbridge]]]].
        -- subst other. rewrite Hcategory in Hcat. discriminate.
        -- exists other, c. auto.
Qed.

Definition tagged (token : Token) : bool :=
  match token_category token with Some _ => true | None => false end.

Theorem bridge_count_exact : forall tokens,
  length (token_bridges tokens) = length (filter tagged tokens).
Proof.
  induction tokens as [|token rest IH]; cbn; auto.
  unfold tagged at 1. destruct (token_category token); cbn; congruence.
Qed.

Section ExistingProductions.
  Context {Production : Type}.
  Definition normalized_rules (productions : list Production) (tokens : list Token)
      : list (Production + Bridge) :=
    map inl productions ++ map inr (token_bridges tokens).

  Theorem every_existing_production_remains : forall productions tokens production,
    In (inl production) (normalized_rules productions tokens) <->
    In production productions.
  Proof.
    intros. unfold normalized_rules. rewrite in_app_iff.
    split.
    - intros [H | H]; apply in_map_iff in H; destruct H as [x [Heq Hin]].
      + inversion Heq; subst x. exact Hin.
      + discriminate.
    - intro H. left. now apply in_map.
  Qed.

  Theorem existing_order_is_unchanged : forall productions tokens,
    firstn (length productions) (normalized_rules productions tokens) =
    map inl productions.
  Proof.
    intros. unfold normalized_rules.
    rewrite firstn_app, firstn_all2 by now rewrite length_map.
    rewrite length_map, Nat.sub_diag. cbn. now rewrite app_nil_r.
  Qed.
End ExistingProductions.

(** Local image admission checks the exact binding, not merely arity. The
    implementation additionally requires whole-table equality with canonical
    normalization, excluding omitted, duplicate, or reordered bridges. *)
Definition bridge_valid (token : Token) (bridge : Bridge) : bool :=
  match token_category token, bridge_symbols bridge, bridge_production bridge with
  | Some category, [CapturedToken identifier], None =>
      Nat.eqb (bridge_category bridge) category &&
      Nat.eqb identifier (token_id token) && Nat.eqb (bridge_cost bridge) 0
  | _, _, _ => false
  end.

Theorem admitted_bridge_is_exact : forall token bridge,
  bridge_valid token bridge = true <->
  exists category, token_category token = Some category /\
    bridge = make_bridge (token_id token) category.
Proof.
  intros [identifier category] [lhs symbols production cost].
  destruct category as [category|]; cbn [bridge_valid token_category token_id
    bridge_category bridge_symbols bridge_production bridge_cost].
  - destruct symbols as [|symbol rest]; [split; [discriminate | intros [? [_ H]]; discriminate] |].
    destruct symbol; try (split; [discriminate | intros [? [_ H]]; discriminate]).
    destruct rest; try (split; [discriminate | intros [? [_ H]]; discriminate]).
    destruct production; try (split; [discriminate | intros [? [_ H]]; discriminate]).
    rewrite !andb_true_iff, !Nat.eqb_eq. split.
    + intros [[Hlhs Hid] Hcost]. subst. exists category. auto.
    + intros [c [Hc Hbridge]]. inversion Hc; subst c.
      inversion Hbridge. auto.
  - split; [discriminate | intros [? [H _]]; discriminate].
Qed.

Theorem generated_bridge_is_admitted : forall token category,
  token_category token = Some category ->
  bridge_valid token (make_bridge (token_id token) category) = true.
Proof.
  intros. apply admitted_bridge_is_exact. exists category. auto.
Qed.

Section SemanticIdentity.
  Context {Syntax Value Rank : Type}.
  Record SemanticValue := { syntax : Syntax; value : Value }.

  Definition token_value (inputs : list SemanticValue) : option (list SemanticValue) :=
    match inputs with [input] => Some [input] | _ => None end.

  Theorem singleton_preserves_both_fields : forall input,
    token_value [input] = Some [input].
  Proof. reflexivity. Qed.

  Theorem non_singleton_is_rejected : forall inputs,
    length inputs <> 1 -> token_value inputs = None.
  Proof.
    intros [|input [|second rest]] H; cbn in *; auto; contradiction.
  Qed.

  Theorem acceptance_has_exact_arity : forall inputs output,
    token_value inputs = Some output -> output = inputs /\ length inputs = 1.
  Proof.
    intros [|input [|second rest]] output H; cbn in H; try discriminate.
    inversion H. auto.
  Qed.

  Record RankedValue := {
    payload : SemanticValue;
    cost : nat;
    rank : Rank
  }.

  Definition complete_bridge (maximum : nat) (input : RankedValue) : RankedValue :=
    {| payload := payload input;
       cost := cost_times maximum (cost input) cost_one;
       rank := rank input |}.

  Theorem bridge_preserves_payload_cost_and_rank : forall maximum input,
    valid_cost maximum (cost input) -> complete_bridge maximum input = input.
  Proof.
    intros maximum [payload cost rank] Hcost.
    unfold complete_bridge; cbn in *.
    now rewrite cost_times_right_identity.
  Qed.
End SemanticIdentity.

(** Connect the adapter to the existing RTN derivation model. Only exact
    single-token bridge shapes have this projection; admission above proves
    that every generated bridge has precisely that shape. *)
Definition bridge_rtn (bridge : Bridge) : list ImageAdmission.Rule :=
  match bridge_symbols bridge with
  | [CapturedToken identifier] =>
      [{| ImageAdmission.lhs := bridge_category bridge;
          ImageAdmission.rhs := [ImageAdmission.Scan identifier];
          ImageAdmission.production := None |}]
  | _ => []
  end.

Definition extend_rtn (existing : list ImageAdmission.Rule) (tokens : list Token) :=
  existing ++ flat_map bridge_rtn (token_bridges tokens).

Theorem tagged_token_has_rtn_derivation : forall existing tokens token category,
  In token tokens -> token_category token = Some category ->
  RtnChart.Derives (extend_rtn existing tokens) category [token_id token].
Proof.
  intros existing tokens token category Hin Hcategory.
  eapply RtnChart.DeriveRule with
    (rule := {| ImageAdmission.lhs := category;
                ImageAdmission.rhs := [ImageAdmission.Scan (token_id token)];
                ImageAdmission.production := None |}).
  - unfold extend_rtn. apply in_or_app. right. apply in_flat_map.
    exists (make_bridge (token_id token) category). split.
    + apply bridge_membership_exact. exists token, category. auto.
    + cbn [bridge_rtn make_bridge bridge_symbols bridge_category]. now left.
  - constructor. constructor.
Qed.

Theorem tagged_token_has_sound_completed_item : forall existing tokens token category,
  In token tokens -> token_category token = Some category ->
  exists item,
    RtnChart.item_sound (extend_rtn existing tokens) item /\
    RtnChart.complete_item item /\
    ImageAdmission.lhs (RtnChart.item_rule item) = category /\
    RtnChart.consumed item = [token_id token].
Proof.
  intros. apply RtnChart.every_derivation_has_a_sound_completed_item.
  now apply tagged_token_has_rtn_derivation.
Qed.

Example mixed_category_keeps_literal_bridge :
  @normalized_rules nat [17] [{| token_id := 5; token_category := Some 0 |}] =
  [inl 17; inr (make_bridge 5 0)].
Proof. reflexivity. Qed.

Print Assumptions bridge_membership_exact.
Print Assumptions bridge_count_exact.
Print Assumptions every_existing_production_remains.
Print Assumptions existing_order_is_unchanged.
Print Assumptions admitted_bridge_is_exact.
Print Assumptions acceptance_has_exact_arity.
Print Assumptions bridge_preserves_payload_cost_and_rank.
Print Assumptions tagged_token_has_sound_completed_item.
