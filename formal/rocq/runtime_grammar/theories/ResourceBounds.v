From Stdlib Require Import Bool PeanoNat Lia List.
Import ListNotations.

Record RuntimeBudget : Type := {
  input_bytes : nat;
  chart_items : nat;
  forest_nodes : nat;
  semantic_results : nat;
  lexer_mode_depth : nat;
  foreign_nesting : nat
}.

Definition effective_budget
    (requested host : RuntimeBudget) : RuntimeBudget :=
  {| input_bytes := Nat.min (input_bytes requested) (input_bytes host);
     chart_items := Nat.min (chart_items requested) (chart_items host);
     forest_nodes := Nat.min (forest_nodes requested) (forest_nodes host);
     semantic_results := Nat.min (semantic_results requested) (semantic_results host);
     lexer_mode_depth := Nat.min (lexer_mode_depth requested) (lexer_mode_depth host);
     foreign_nesting := Nat.min (foreign_nesting requested) (foreign_nesting host) |}.

Definition budget_le (left right : RuntimeBudget) : Prop :=
  input_bytes left <= input_bytes right /\
  chart_items left <= chart_items right /\
  forest_nodes left <= forest_nodes right /\
  semantic_results left <= semantic_results right /\
  lexer_mode_depth left <= lexer_mode_depth right /\
  foreign_nesting left <= foreign_nesting right.

Theorem effective_budget_is_host_bounded :
  forall requested host, budget_le (effective_budget requested host) host.
Proof.
  intros [ri rc rf rs rl rg] [hi hc hf hs hl hg].
  unfold budget_le, effective_budget. simpl.
  repeat split; rewrite Nat.min_le_iff; auto.
Qed.

Theorem effective_budget_is_request_bounded :
  forall requested host, budget_le (effective_budget requested host) requested.
Proof.
  intros [ri rc rf rs rl rg] [hi hc hf hs hl hg].
  unfold budget_le, effective_budget. simpl.
  repeat split; rewrite Nat.min_le_iff; auto.
Qed.

Record RuntimeUsage : Type := {
  used_input_bytes : nat;
  used_chart_items : nat;
  used_forest_nodes : nat;
  used_semantic_results : nat;
  used_lexer_mode_depth : nat;
  used_foreign_nesting : nat
}.

Definition usage_within (usage : RuntimeUsage) (budget : RuntimeBudget) : Prop :=
  used_input_bytes usage <= input_bytes budget /\
  used_chart_items usage <= chart_items budget /\
  used_forest_nodes usage <= forest_nodes budget /\
  used_semantic_results usage <= semantic_results budget /\
  used_lexer_mode_depth usage <= lexer_mode_depth budget /\
  used_foreign_nesting usage <= foreign_nesting budget.

Lemma usage_within_monotone :
  forall usage smaller larger,
    usage_within usage smaller -> budget_le smaller larger ->
    usage_within usage larger.
Proof.
  intros [ui uc uf us ul ug]
         [si sc sf ss sl sg] [li lc lf ls ll lg].
  unfold usage_within, budget_le. simpl. intros Husage Hbudgets.
  destruct Husage as [Hi [Hc [Hf [Hs [Hl Hg]]]]].
  destruct Hbudgets as [Bi [Bc [Bf [Bs [Bl Bg]]]]].
  repeat split; lia.
Qed.

Theorem admitted_execution_never_exceeds_host_budget :
  forall requested host usage,
    usage_within usage (effective_budget requested host) ->
    usage_within usage host.
Proof.
  intros requested host usage Husage.
  eapply usage_within_monotone; [exact Husage |].
  apply effective_budget_is_host_bounded.
Qed.

Record ImageFootprint : Type := {
  encoded_bytes : nat;
  lexer_states : nat;
  lexer_transitions : nat;
  nonterminals : nat;
  rules : nat;
  symbols : nat
}.

Definition image_withinb (image cap : ImageFootprint) : bool :=
  Nat.leb (encoded_bytes image) (encoded_bytes cap) &&
  Nat.leb (lexer_states image) (lexer_states cap) &&
  Nat.leb (lexer_transitions image) (lexer_transitions cap) &&
  Nat.leb (nonterminals image) (nonterminals cap) &&
  Nat.leb (rules image) (rules cap) &&
  Nat.leb (symbols image) (symbols cap).

Definition image_within (image cap : ImageFootprint) : Prop :=
  encoded_bytes image <= encoded_bytes cap /\
  lexer_states image <= lexer_states cap /\
  lexer_transitions image <= lexer_transitions cap /\
  nonterminals image <= nonterminals cap /\
  rules image <= rules cap /\
  symbols image <= symbols cap.

Theorem image_admission_bound_is_sound :
  forall image cap,
    image_withinb image cap = true -> image_within image cap.
Proof.
  intros image cap H. unfold image_withinb in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[[[Hb Hs] Ht] Hn] Hr] Hy].
  unfold image_within. repeat split; apply Nat.leb_le; assumption.
Qed.

(** Persistent symbolic-template memoization has a separate host-controlled
    budget.  Entries are represented oldest first and carry their logical
    result weight; the executable cache maintains the same two counters. *)
Record SymbolicCacheBudget : Type := {
  symbolic_cache_entries : nat;
  symbolic_cache_weight : nat
}.

Fixpoint total_cache_weight (entries : list nat) : nat :=
  match entries with
  | [] => 0
  | weight :: rest => weight + total_cache_weight rest
  end.

Definition symbolic_cache_within
    (entries : list nat) (budget : SymbolicCacheBudget) : Prop :=
  length entries <= symbolic_cache_entries budget /\
  total_cache_weight entries <= symbolic_cache_weight budget.

Definition symbolic_cache_withinb
    (entries : list nat) (budget : SymbolicCacheBudget) : bool :=
  Nat.leb (length entries) (symbolic_cache_entries budget) &&
  Nat.leb (total_cache_weight entries) (symbolic_cache_weight budget).

Fixpoint evict_oldest_until_within
    (entries : list nat) (budget : SymbolicCacheBudget) : list nat :=
  if symbolic_cache_withinb entries budget then entries
  else
    match entries with
    | [] => []
    | _ :: rest => evict_oldest_until_within rest budget
    end.

Definition insert_symbolic_cache
    (entries : list nat) (budget : SymbolicCacheBudget) (new_weight : nat)
    : list nat :=
  if Nat.leb new_weight (symbolic_cache_weight budget)
  then evict_oldest_until_within (entries ++ [new_weight]) budget
  else entries.

Lemma symbolic_cache_withinb_is_sound :
  forall entries budget,
    symbolic_cache_withinb entries budget = true ->
    symbolic_cache_within entries budget.
Proof.
  intros entries budget Hwithin.
  unfold symbolic_cache_withinb in Hwithin.
  rewrite andb_true_iff in Hwithin.
  destruct Hwithin as [Hentries Hweight].
  split; apply Nat.leb_le; assumption.
Qed.

Theorem eviction_terminates_within_budget :
  forall entries budget,
    symbolic_cache_within (evict_oldest_until_within entries budget) budget.
Proof.
  intros entries.
  induction entries as [|entry rest IH]; intros budget.
  - unfold evict_oldest_until_within, symbolic_cache_within.
    simpl. lia.
  - unfold evict_oldest_until_within; fold evict_oldest_until_within.
    destruct (symbolic_cache_withinb (entry :: rest) budget) eqn:Hwithin.
    + apply symbolic_cache_withinb_is_sound. exact Hwithin.
    + apply IH.
Qed.

Theorem fifo_insertion_preserves_symbolic_cache_budget :
  forall entries budget new_weight,
    symbolic_cache_within entries budget ->
    symbolic_cache_within
      (insert_symbolic_cache entries budget new_weight) budget.
Proof.
  intros entries budget new_weight Hbefore.
  unfold insert_symbolic_cache.
  destruct (Nat.leb new_weight (symbolic_cache_weight budget)).
  - apply eviction_terminates_within_budget.
  - exact Hbefore.
Qed.

Theorem zero_entry_budget_disables_symbolic_cache :
  forall entries weight_limit new_weight,
    symbolic_cache_within
      entries {| symbolic_cache_entries := 0;
                 symbolic_cache_weight := weight_limit |} ->
    insert_symbolic_cache
      entries {| symbolic_cache_entries := 0;
                 symbolic_cache_weight := weight_limit |} new_weight = [].
Proof.
  intros entries weight_limit new_weight Hwithin.
  destruct Hwithin as [Hlength _].
  destruct entries as [|entry rest]; [|simpl in Hlength; lia].
  unfold insert_symbolic_cache.
  cbn.
  destruct (Nat.leb new_weight weight_limit) eqn:Hweight; [|reflexivity].
  unfold evict_oldest_until_within; fold evict_oldest_until_within.
  simpl. reflexivity.
Qed.

Print Assumptions effective_budget_is_host_bounded.
Print Assumptions admitted_execution_never_exceeds_host_budget.
Print Assumptions image_admission_bound_is_sound.
Print Assumptions eviction_terminates_within_budget.
Print Assumptions fifo_insertion_preserves_symbolic_cache_budget.
Print Assumptions zero_entry_budget_disables_symbolic_cache.
