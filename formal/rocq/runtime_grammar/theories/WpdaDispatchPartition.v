(** * Semantics-preserving partitioning of generated WPDA dispatch

    A generated parser has two stacks with very different jobs.  The WPDA/GSS
    stack represents grammar nesting and is intentionally unbounded.  The Rust
    call stack only routes one transition and must remain bounded independently
    of input nesting.  This file proves the two refinements used by code
    generation:

      state router -> state handler -> ordered token router -> transition leaf,

    and, for constructor-bearing tables whose rows require separate native
    frames:

      state handler -> ordered bounded chunks -> transition leaf.

    Relocation and partitioning change only where Rust places native frame
    boundaries.  They do not change lookup priority, fallback, branch order,
    weights, target states, positions, effects, or fork ordinals. *)

From Stdlib Require Import List Arith Lia Relation_Operators.
Import ListNotations.
Set Implicit Arguments.

Section OrderedDispatch.
  Context {Key Action : Type}.
  Variable key_eqb : Key -> Key -> bool.

  Definition Rule : Type := (Key * Action)%type.

  Fixpoint lookup_rules (key : Key) (rules : list Rule) : option Action :=
    match rules with
    | [] => None
    | (rule_key, action) :: tail =>
        if key_eqb key rule_key then Some action else lookup_rules key tail
    end.

  Fixpoint lookup_chunks
      (key : Key) (chunks : list (list Rule)) : option Action :=
    match chunks with
    | [] => None
    | chunk :: tail =>
        match lookup_rules key chunk with
        | Some action => Some action
        | None => lookup_chunks key tail
        end
    end.

  Lemma lookup_rules_app :
    forall key left right,
      lookup_rules key (left ++ right) =
      match lookup_rules key left with
      | Some action => Some action
      | None => lookup_rules key right
      end.
  Proof.
    intros key left; induction left as [|[rule_key action] tail IH];
      intros right; simpl.
    - reflexivity.
    - destruct (key_eqb key rule_key); simpl; auto.
  Qed.

  Theorem lookup_chunks_flatten :
    forall key chunks,
      lookup_chunks key chunks = lookup_rules key (concat chunks).
  Proof.
    intros key chunks; induction chunks as [|chunk tail IH]; simpl.
    - reflexivity.
    - rewrite lookup_rules_app.
      destruct (lookup_rules key chunk); simpl; auto.
  Qed.

  Lemma chunk_hit_has_priority :
    forall key chunk tail action,
      lookup_rules key chunk = Some action ->
      lookup_chunks key (chunk :: tail) = Some action.
  Proof.
    intros key chunk tail action H; simpl; rewrite H; reflexivity.
  Qed.

  Lemma chunk_miss_falls_through :
    forall key chunk tail,
      lookup_rules key chunk = None ->
      lookup_chunks key (chunk :: tail) = lookup_chunks key tail.
  Proof.
    intros key chunk tail H; simpl; rewrite H; reflexivity.
  Qed.

  Record DispatchPartition : Type := {
    monolithic_rules : list Rule;
    partition_chunks : list (list Rule);
    rows_per_chunk : nat;
    rows_per_chunk_positive : 0 < rows_per_chunk;
    chunks_bounded :
      Forall (fun chunk => length chunk <= rows_per_chunk) partition_chunks;
    flatten_exact : concat partition_chunks = monolithic_rules
  }.

  Definition monolithic_dispatch
      (partition : DispatchPartition) (key : Key) : option Action :=
    lookup_rules key (monolithic_rules partition).

  (** The category-token router relocates the original ordered match into a
      non-inlined method after each semantic arm body has been peeled into a
      transition leaf.  Its denotation is therefore the original lookup, with
      no intermediate selection or reordering. *)
  Definition relocated_direct_dispatch
      (rules : list Rule) (key : Key) : option Action :=
    lookup_rules key rules.

  Theorem direct_router_relocation_equivalent :
    forall rules key,
      relocated_direct_dispatch rules key = lookup_rules key rules.
  Proof.
    reflexivity.
  Qed.

  Definition partitioned_dispatch
      (partition : DispatchPartition) (key : Key) : option Action :=
    lookup_chunks key (partition_chunks partition).

  Theorem dispatch_partition_equivalent :
    forall partition key,
      partitioned_dispatch partition key =
      monolithic_dispatch partition key.
  Proof.
    intros partition key.
    unfold partitioned_dispatch, monolithic_dispatch.
    rewrite lookup_chunks_flatten.
    rewrite flatten_exact.
    reflexivity.
  Qed.

  Theorem partition_coverage :
    forall partition row,
      In row (monolithic_rules partition) <->
      exists chunk,
        In chunk (partition_chunks partition) /\ In row chunk.
  Proof.
    intros partition row.
    rewrite <- flatten_exact.
    apply in_concat.
  Qed.

  (** Routing ownership is functional.  This is the disjointness property used
      by the state/category router: a context is covered by one route id and
      cannot simultaneously belong to two different route ids. *)
  Variable route_id : Key -> nat.
  Definition route_accepts (key : Key) (route : nat) : Prop :=
    route_id key = route.

  Theorem route_coverage :
    forall key, exists route, route_accepts key route.
  Proof.
    intro key; exists (route_id key); reflexivity.
  Qed.

  Theorem route_disjoint :
    forall key left right,
      route_accepts key left -> route_accepts key right -> left = right.
  Proof.
    unfold route_accepts; intros key left right Hleft Hright.
    congruence.
  Qed.
End OrderedDispatch.

(** A collection field is structural metadata, not by itself ownership by the
    dedicated collection parser.  That parser owns only a pure collection
    literal: a collection-bearing rule with no nonterminal operand.  All other
    rules are classified by prefix binding power and then by their leading
    syntax shape.  Keeping this classifier total makes the generated lanes
    disjoint and prevents an ordinary terminal-first rule from disappearing
    merely because one of its later fields is a collection. *)
Section RuleLanePartition.
  Inductive LeadingShape : Type :=
  | LeadingTerminal
  | LeadingForeignNonterminal
  | LeadingDynamic.

  Record RuleShape : Type := {
    contains_collection : bool;
    contains_nonterminal : bool;
    has_prefix_binding_power : bool;
    leading_shape : LeadingShape
  }.

  Inductive RuleLane : Type :=
  | CollectionLane
  | PrefixLane
  | TerminalTrieLane
  | ForeignNonterminalLane
  | DynamicLane.

  Definition is_pure_collection_literal (rule : RuleShape) : bool :=
    contains_collection rule && negb (contains_nonterminal rule).

  Definition classify_rule_lane (rule : RuleShape) : RuleLane :=
    if is_pure_collection_literal rule then CollectionLane
    else if has_prefix_binding_power rule then PrefixLane
    else
      match leading_shape rule with
      | LeadingTerminal => TerminalTrieLane
      | LeadingForeignNonterminal => ForeignNonterminalLane
      | LeadingDynamic => DynamicLane
      end.

  Definition lane_accepts (rule : RuleShape) (lane : RuleLane) : Prop :=
    classify_rule_lane rule = lane.

  Theorem rule_lane_coverage :
    forall rule, exists lane, lane_accepts rule lane.
  Proof.
    intro rule; exists (classify_rule_lane rule); reflexivity.
  Qed.

  Theorem rule_lane_disjoint :
    forall rule left right,
      lane_accepts rule left -> lane_accepts rule right -> left = right.
  Proof.
    unfold lane_accepts; intros rule left right Hleft Hright; congruence.
  Qed.

  Theorem pure_collection_owns_collection_lane :
    forall rule,
      is_pure_collection_literal rule = true ->
      classify_rule_lane rule = CollectionLane.
  Proof.
    intros rule Hpure; unfold classify_rule_lane; rewrite Hpure; reflexivity.
  Qed.

  Theorem collection_field_with_nonterminal_is_not_collection_lane :
    forall prefix leading,
      classify_rule_lane
        {| contains_collection := true;
           contains_nonterminal := true;
           has_prefix_binding_power := prefix;
           leading_shape := leading |} <> CollectionLane.
  Proof.
    intros [] []; discriminate.
  Qed.

  Theorem terminal_rule_with_collection_field_uses_trie :
    classify_rule_lane
      {| contains_collection := true;
         contains_nonterminal := true;
         has_prefix_binding_power := false;
         leading_shape := LeadingTerminal |} = TerminalTrieLane.
  Proof.
    reflexivity.
  Qed.

  Theorem pure_collection_never_uses_terminal_trie :
    forall rule,
      is_pure_collection_literal rule = true ->
      classify_rule_lane rule <> TerminalTrieLane.
  Proof.
    intros rule Hpure; rewrite (pure_collection_owns_collection_lane rule Hpure);
      discriminate.
  Qed.
End RuleLanePartition.

Section ExactTransitionObservation.
  Context {Weight : Type}.

  Record WeightedBranch : Type := {
    branch_target : nat;
    branch_weight : Weight;
    branch_ordinal : nat
  }.

  Record Transition : Type := {
    transition_state : nat;
    transition_position : nat;
    transition_effect : nat;
    transition_branches : list WeightedBranch
  }.

  Theorem action_equality_preserves_branch_order :
    forall left right,
      left = right ->
      map branch_ordinal (transition_branches left) =
      map branch_ordinal (transition_branches right).
  Proof.
    intros left right ->; reflexivity.
  Qed.

  Theorem action_equality_preserves_weights :
    forall left right,
      left = right ->
      map branch_weight (transition_branches left) =
      map branch_weight (transition_branches right).
  Proof.
    intros left right ->; reflexivity.
  Qed.

  Theorem action_equality_preserves_control_and_effects :
    forall left right,
      left = right ->
      (transition_state left,
       transition_position left,
       transition_effect left) =
      (transition_state right,
       transition_position right,
       transition_effect right).
  Proof.
    intros left right ->; reflexivity.
  Qed.
End ExactTransitionObservation.

(** A lexical alternative may allocate intermediate graph-structured-stack or
    shared-packed-parse-forest nodes and still fail before producing a complete
    parse.  Such private packings are not an observation of the lexical fork.
    Only completed results cross the branch boundary.  Consequently, adding a
    rejected same-extent alternative cannot change the surviving terms,
    weights, order, or cardinality. *)
Section RejectedLexicalBranchTransparency.
  Context {Term Weight : Type}.

  Record CompletedParse : Type := {
    completed_term : Term;
    completed_weight : Weight
  }.

  Record LexicalBranchRun : Type := {
    branch_private_packings : list nat;
    branch_completed_results : list CompletedParse
  }.

  Definition observe_lexical_fork
      (primary : LexicalBranchRun) (alternatives : list LexicalBranchRun)
      : list CompletedParse :=
    branch_completed_results primary ++
    concat (map branch_completed_results alternatives).

  Theorem rejected_lexical_branch_is_observationally_inert :
    forall primary rejected,
      branch_completed_results rejected = [] ->
      observe_lexical_fork primary [rejected] =
      branch_completed_results primary.
  Proof.
    intros primary rejected Hrejected.
    unfold observe_lexical_fork; simpl.
    rewrite Hrejected, app_nil_r.
    reflexivity.
  Qed.

  Theorem rejected_branch_private_packings_are_inert :
    forall primary left_packings right_packings,
      observe_lexical_fork primary
        [{| branch_private_packings := left_packings;
            branch_completed_results := [] |}] =
      observe_lexical_fork primary
        [{| branch_private_packings := right_packings;
            branch_completed_results := [] |}].
  Proof.
    intros; reflexivity.
  Qed.

  Theorem rejected_branch_preserves_result_cardinality :
    forall primary rejected,
      branch_completed_results rejected = [] ->
      length (observe_lexical_fork primary [rejected]) =
      length (branch_completed_results primary).
  Proof.
    intros primary rejected Hrejected.
    rewrite (rejected_lexical_branch_is_observationally_inert
      primary rejected Hrejected).
    reflexivity.
  Qed.
End RejectedLexicalBranchTransparency.

(** A contextual keyword requires both its fixed-token and identifier readings
    to remain reachable.  Prefix lexical forks do not encode every kind of
    fixed-token rule: collection literals and other multi-token prefix rules
    are owned by normal prefix dispatch.  Therefore contextuality alone may
    not force a lexical fork.  When the fork has no branch for the primary
    fixed-token reading, equal-extent resolution must fall through to normal
    dispatch; when the fork represents that reading, retaining the fork
    preserves the contextual identifier co-reading. *)
Section ContextualPrefixDispatchCompleteness.
  Inductive PrefixDispatchChoice : Type :=
  | FallThroughToPrimary
  | RetainLexicalFork.

  Definition choose_prefix_dispatch
      (is_contextual same_extent normal_has_primary fork_has_primary : bool)
      : PrefixDispatchChoice :=
    if andb (andb same_extent normal_has_primary)
       (orb (negb is_contextual) (negb fork_has_primary))
    then FallThroughToPrimary
    else RetainLexicalFork.

  Definition primary_reading_reachable
      (choice : PrefixDispatchChoice)
      (normal_has_primary fork_has_primary : bool) : bool :=
    match choice with
    | FallThroughToPrimary => normal_has_primary
    | RetainLexicalFork => fork_has_primary
    end.

  Theorem contextual_unrepresented_primary_falls_through :
    choose_prefix_dispatch true true true false = FallThroughToPrimary.
  Proof.
    reflexivity.
  Qed.

  Theorem contextual_represented_primary_retains_fork :
    choose_prefix_dispatch true true true true = RetainLexicalFork.
  Proof.
    reflexivity.
  Qed.

  Theorem reserved_equal_extent_primary_falls_through :
    forall fork_has_primary,
      choose_prefix_dispatch false true true fork_has_primary =
      FallThroughToPrimary.
  Proof.
    intros []; reflexivity.
  Qed.

  Theorem unequal_extent_retains_lexical_fork :
    forall is_contextual normal_has_primary fork_has_primary,
      choose_prefix_dispatch is_contextual false normal_has_primary
        fork_has_primary = RetainLexicalFork.
  Proof.
    intros [] [] []; reflexivity.
  Qed.

  Theorem equal_extent_normal_primary_is_never_lost :
    forall is_contextual fork_has_primary,
      primary_reading_reachable
        (choose_prefix_dispatch is_contextual true true fork_has_primary)
        true fork_has_primary = true.
  Proof.
    intros [] []; reflexivity.
  Qed.
End ContextualPrefixDispatchCompleteness.

Section NonRecursiveControlGraph.
  Inductive DispatchLayer : Type :=
  | StateRouter
  | StateHandler
  | GrammarRouter
  | TransitionLeaf.

  Definition layer_rank (layer : DispatchLayer) : nat :=
    match layer with
    | StateRouter => 3
    | StateHandler => 2
    | GrammarRouter => 1
    | TransitionLeaf => 0
    end.

  Inductive dispatch_edge : DispatchLayer -> DispatchLayer -> Prop :=
  | EdgeState : dispatch_edge StateRouter StateHandler
  | EdgeGrammar : dispatch_edge StateHandler GrammarRouter
  | EdgeLeaf : dispatch_edge GrammarRouter TransitionLeaf.

  Theorem dispatch_edge_decreases :
    forall source target,
      dispatch_edge source target -> layer_rank target < layer_rank source.
  Proof.
    intros source target Hedge; inversion Hedge; simpl; lia.
  Qed.

  Definition dispatch_path := clos_trans DispatchLayer dispatch_edge.

  Theorem dispatch_path_decreases :
    forall source target,
      dispatch_path source target -> layer_rank target < layer_rank source.
  Proof.
    intros source target Hpath; induction Hpath.
    - apply dispatch_edge_decreases; assumption.
    - lia.
  Qed.

  Corollary dispatch_control_graph_is_non_recursive :
    forall layer, ~ dispatch_path layer layer.
  Proof.
    intros layer Hcycle.
    pose proof (dispatch_path_decreases Hcycle).
    lia.
  Qed.
End NonRecursiveControlGraph.

(** A collection-remainder tail starts after the comma following its first
    element.  Its two legal continuations have disjoint first tokens: another
    abstract-syntax-tree (AST) element followed by a comma, or an ellipsis and
    a remainder name.  The executable grammar uses this left-factored shape so
    the pushdown automaton never has to guess whether a comma belongs to an
    inner item list or to its enclosing remainder production. *)
Section DeterministicRemainderTail.
  Inductive TailToken : Type :=
  | TailAst : nat -> TailToken
  | TailComma
  | TailEllipsis
  | TailName : nat -> TailToken.

  Inductive RemainderTail : Type :=
  | RemainderEnd : nat -> RemainderTail
  | RemainderMore : nat -> RemainderTail -> RemainderTail.

  Fixpoint encode_remainder_tail (tail : RemainderTail) : list TailToken :=
    match tail with
    | RemainderEnd name => [TailEllipsis; TailName name]
    | RemainderMore item rest =>
        TailAst item :: TailComma :: encode_remainder_tail rest
    end.

  Inductive TailState : Type :=
  | ExpectTailEntry
  | ExpectTailComma
  | ExpectRemainderName
  | TailAccepted
  | TailRejected.

  Definition step_remainder_tail
      (state : TailState) (token : TailToken) : TailState :=
    match state, token with
    | ExpectTailEntry, TailAst _ => ExpectTailComma
    | ExpectTailEntry, TailEllipsis => ExpectRemainderName
    | ExpectTailComma, TailComma => ExpectTailEntry
    | ExpectRemainderName, TailName _ => TailAccepted
    | _, _ => TailRejected
    end.

  Fixpoint run_remainder_tail
      (state : TailState) (tokens : list TailToken) : TailState :=
    match tokens with
    | [] => state
    | token :: rest =>
        run_remainder_tail (step_remainder_tail state token) rest
    end.

  Theorem encoded_remainder_tail_accepts :
    forall tail,
      run_remainder_tail ExpectTailEntry (encode_remainder_tail tail) =
      TailAccepted.
  Proof.
    induction tail as [name | item rest IH]; simpl; assumption || reflexivity.
  Qed.

  Theorem ellipsis_selects_only_remainder :
    step_remainder_tail ExpectTailEntry TailEllipsis = ExpectRemainderName /\
    forall item,
      step_remainder_tail ExpectTailEntry (TailAst item) = ExpectTailComma.
  Proof.
    split; reflexivity.
  Qed.

  Theorem remainder_tail_step_is_deterministic :
    forall state token left right,
      step_remainder_tail state token = left ->
      step_remainder_tail state token = right ->
      left = right.
  Proof.
    intros state token left right Hleft Hright; congruence.
  Qed.
End DeterministicRemainderTail.

(** Rules marked [same] stay in their predecessor's precedence level.  The
    declaration is meaningful for both infix and postfix operators: postfix
    builders such as [Types], [Terms], and [Rewrites] are freely chainable and
    therefore must not acquire an artificial order from declaration position.
    An unmarked postfix still opens the next tighter level, preserving the
    historical behavior. *)
Section SharedPostfixPrecedence.
  Definition next_postfix_level
      (current : nat) (level_is_open shares_previous : bool) : nat :=
    if andb level_is_open (negb shares_previous) then S current else current.

  Fixpoint postfix_levels
      (current : nat) (level_is_open : bool) (shares : list bool) : list nat :=
    match shares with
    | [] => []
    | share :: rest =>
        let level := next_postfix_level current level_is_open share in
        level :: postfix_levels level true rest
    end.

  Theorem marked_postfix_preserves_level :
    forall current,
      next_postfix_level current true true = current.
  Proof.
    reflexivity.
  Qed.

  Theorem unmarked_postfix_opens_next_level :
    forall current,
      next_postfix_level current true false = S current.
  Proof.
    reflexivity.
  Qed.

  Theorem marked_postfix_chain_has_one_level :
    forall current count,
      postfix_levels current true (repeat true count) = repeat current count.
  Proof.
    intros current count; induction count as [|count IH].
    - reflexivity.
    - cbn.
      f_equal.
      exact IH.
  Qed.
End SharedPostfixPrecedence.

(** Generated display is a token stream, not byte concatenation.  A captured
    value can begin or end with an identifier character, so two adjacent
    captures, or a capture beside an identifier-shaped literal, require a
    separating space.  Delimited literals do not.  The decision is local and
    deterministic, hence it remains compatible with the iterative display
    worklist. *)
Section DisplayLexicalBoundaries.
  Inductive SurfaceKind : Type :=
  | CapturedValue
  | WordLiteral
  | DelimitedLiteral.

  Definition may_end_identifier (kind : SurfaceKind) : bool :=
    match kind with
    | CapturedValue | WordLiteral => true
    | DelimitedLiteral => false
    end.

  Definition may_begin_identifier (kind : SurfaceKind) : bool :=
    match kind with
    | CapturedValue | WordLiteral => true
    | DelimitedLiteral => false
    end.

  Definition needs_lexical_separator
      (left right : SurfaceKind) : bool :=
    andb (may_end_identifier left) (may_begin_identifier right).

  Theorem omitted_separator_is_glom_safe :
    forall left right,
      needs_lexical_separator left right = false ->
      may_end_identifier left = false \/ may_begin_identifier right = false.
  Proof.
    intros [] [] H; simpl in *; auto; discriminate.
  Qed.

  Theorem adjacent_captures_require_separator :
    needs_lexical_separator CapturedValue CapturedValue = true.
  Proof.
    reflexivity.
  Qed.

  Theorem capture_word_boundaries_require_separator :
    needs_lexical_separator CapturedValue WordLiteral = true /\
    needs_lexical_separator WordLiteral CapturedValue = true.
  Proof.
    split; reflexivity.
  Qed.

  (** Delimited collection display (2026-10-21): the [GrammarItem::Collection]
      arm of [generate_engine_regular_arm] in macros/src/gen/syntax/display.rs.
      The rendering writes the opener, then the items joined by the padded
      separator, then the closer.  Each item is a captured value.  The
      rendering therefore has the boundaries in [collection_boundaries]: the
      opener before the first item and the last item before the closer when
      the collection has items, and the opener before the closer when it is
      empty.  The separator is written with a space on each side, so it adds
      no other boundary. *)
  Definition collection_boundaries
      (opener closer : SurfaceKind) (has_items : bool)
      : list (SurfaceKind * SurfaceKind) :=
    if has_items
    then [(opener, CapturedValue); (CapturedValue, closer)]
    else [(opener, closer)].

  (** A boundary policy decides whether one boundary gets a space.  It is
      glom-safe on a rendering when each boundary that needs a separator gets
      one. *)
  Definition glom_safe_on
      (policy : SurfaceKind -> SurfaceKind -> bool)
      (boundaries : list (SurfaceKind * SurfaceKind)) : Prop :=
    forall left right,
      In (left, right) boundaries ->
      needs_lexical_separator left right = true ->
      policy left right = true.

  (** The rendering before 2026-10-21 wrote no space at any collection
      boundary: [String::from(open)], then the joined items, then [close]. *)
  Definition collection_policy_before_fix
      (left right : SurfaceKind) : bool := false.

  (** Counterexample about that rendering: word delimiters are not glom-safe,
      with or without items.  The Rust witness is [PNameBag . Proc ::=
      HashBag(Name) sep "," delim "bnames" "end"], whose term [bnames n , n end]
      rendered as [bnamesn , nend] and read back as the identifier
      [bnamesn]; the empty collection rendered as the identifier
      [bnamesend]. *)
  Theorem word_delimited_collection_before_fix_is_not_glom_safe :
    forall has_items,
      ~ glom_safe_on collection_policy_before_fix
          (collection_boundaries WordLiteral WordLiteral has_items).
  Proof.
    intros has_items Hsafe.
    destruct has_items.
    - assert (Hin : In (WordLiteral, CapturedValue)
                      (collection_boundaries WordLiteral WordLiteral true))
        by (cbn; left; reflexivity).
      specialize (Hsafe _ _ Hin eq_refl).
      unfold collection_policy_before_fix in Hsafe.
      discriminate Hsafe.
    - assert (Hin : In (WordLiteral, WordLiteral)
                      (collection_boundaries WordLiteral WordLiteral false))
        by (cbn; left; reflexivity).
      specialize (Hsafe _ _ Hin eq_refl).
      unfold collection_policy_before_fix in Hsafe.
      discriminate Hsafe.
  Qed.

  (** The corrected rendering writes a space exactly where the lexical
      boundary needs one. *)
  Definition collection_policy (left right : SurfaceKind) : bool :=
    needs_lexical_separator left right.

  Theorem collection_policy_is_glom_safe :
    forall opener closer has_items,
      glom_safe_on collection_policy
        (collection_boundaries opener closer has_items).
  Proof.
    intros opener closer has_items left right _ Hneeds.
    exact Hneeds.
  Qed.

  (** The corrected rendering writes no space that the boundary does not
      need, so each omitted space is glom-safe by
      [omitted_separator_is_glom_safe]. *)
  Theorem collection_policy_writes_only_needed_spaces :
    forall left right,
      collection_policy left right = true ->
      needs_lexical_separator left right = true.
  Proof.
    intros left right H.
    exact H.
  Qed.

  (** Word delimiters get a space at every boundary, with or without items:
      [bnames n , n end] and the empty [bnames end]. *)
  Theorem word_delimited_collection_separates_every_boundary :
    forall has_items left right,
      In (left, right)
        (collection_boundaries WordLiteral WordLiteral has_items) ->
      collection_policy left right = true.
  Proof.
    intros [|] left right Hin; cbn in Hin.
    - destruct Hin as [Heq | [Heq | []]]; inversion Heq; subst; reflexivity.
    - destruct Hin as [Heq | []]; inversion Heq; subst; reflexivity.
  Qed.

  (** Regression fence: bracket delimiters keep the old rendering at every
      boundary, so the output for [par{...}], [set{...}] and [seq[...]] is
      unchanged. *)
  Theorem bracket_delimited_collection_is_unchanged :
    forall has_items left right,
      In (left, right)
        (collection_boundaries DelimitedLiteral DelimitedLiteral has_items) ->
      collection_policy left right = collection_policy_before_fix left right.
  Proof.
    intros [|] left right Hin; cbn in Hin.
    - destruct Hin as [Heq | [Heq | []]]; inversion Heq; subst; reflexivity.
    - destruct Hin as [Heq | []]; inversion Heq; subst; reflexivity.
  Qed.

  (** The three spaces that the generated code writes, in the order of
      [collection_boundaries]: after the opener and before the closer when the
      collection has items, and between them when it is empty.  The Rust
      transcription reads each space from one end of one delimiter. *)
  Definition collection_spaces (opener closer : SurfaceKind)
      : bool * bool * bool :=
    (collection_policy opener CapturedValue,
     collection_policy CapturedValue closer,
     collection_policy opener closer).

  Theorem collection_spaces_follow_the_delimiter_ends :
    forall opener closer,
      collection_spaces opener closer =
        (may_end_identifier opener,
         may_begin_identifier closer,
         andb (may_end_identifier opener) (may_begin_identifier closer)).
  Proof.
    intros [] []; reflexivity.
  Qed.
End DisplayLexicalBoundaries.

(** Only the Rholang quote token [@] uses the quote-sigil operand rescue.  A
    balanced grouping frame and every other leading literal already describe
    their own surface and must not gain an additional parse-visible grouping
    constructor. *)
Section ExplicitGroupingDisplay.
  Inductive OperandFrame : Type :=
  | AtQuotePrefix
  | ExplicitGrouping
  | OtherLeadingLiteral.

  Inductive OperandPlan : Type :=
  | EmitBareOperand
  | EmitWrappedOperand.

  Definition plan_operand
      (frame : OperandFrame) (operand_has_tail : bool) : OperandPlan :=
    match frame with
    | AtQuotePrefix =>
        if operand_has_tail then EmitWrappedOperand else EmitBareOperand
    | ExplicitGrouping | OtherLeadingLiteral => EmitBareOperand
    end.

  Theorem explicit_grouping_never_uses_sigil_rescue :
    forall operand_has_tail,
      plan_operand ExplicitGrouping operand_has_tail = EmitBareOperand.
  Proof.
    intros []; reflexivity.
  Qed.

  Theorem non_quote_literal_never_uses_sigil_rescue :
    forall operand_has_tail,
      plan_operand OtherLeadingLiteral operand_has_tail = EmitBareOperand.
  Proof.
    intros []; reflexivity.
  Qed.

  Theorem at_quote_wraps_exactly_tail_bearing_operands :
    forall operand_has_tail,
      plan_operand AtQuotePrefix operand_has_tail =
      if operand_has_tail then EmitWrappedOperand else EmitBareOperand.
  Proof.
    intros []; reflexivity.
  Qed.
End ExplicitGroupingDisplay.

Print Assumptions encoded_remainder_tail_accepts.
Print Assumptions ellipsis_selects_only_remainder.
Print Assumptions remainder_tail_step_is_deterministic.
Print Assumptions rejected_lexical_branch_is_observationally_inert.
Print Assumptions rejected_branch_private_packings_are_inert.
Print Assumptions rejected_branch_preserves_result_cardinality.
Print Assumptions contextual_unrepresented_primary_falls_through.
Print Assumptions contextual_represented_primary_retains_fork.
Print Assumptions reserved_equal_extent_primary_falls_through.
Print Assumptions unequal_extent_retains_lexical_fork.
Print Assumptions equal_extent_normal_primary_is_never_lost.
Print Assumptions marked_postfix_preserves_level.
Print Assumptions unmarked_postfix_opens_next_level.
Print Assumptions marked_postfix_chain_has_one_level.
Print Assumptions omitted_separator_is_glom_safe.
Print Assumptions adjacent_captures_require_separator.
Print Assumptions capture_word_boundaries_require_separator.
Print Assumptions word_delimited_collection_before_fix_is_not_glom_safe.
Print Assumptions collection_policy_is_glom_safe.
Print Assumptions collection_policy_writes_only_needed_spaces.
Print Assumptions word_delimited_collection_separates_every_boundary.
Print Assumptions bracket_delimited_collection_is_unchanged.
Print Assumptions collection_spaces_follow_the_delimiter_ends.
Print Assumptions explicit_grouping_never_uses_sigil_rescue.
Print Assumptions non_quote_literal_never_uses_sigil_rescue.
Print Assumptions at_quote_wraps_exactly_tail_bearing_operands.

Section SharedDispatchStorage.
  Context {Input State Digest Record : Type}.
  Variable initial : State.
  Variable run : State -> Input -> Digest.

  Fixpoint digest_per_arm (candidates : list (option Input)) : option Digest :=
    match candidates with
    | [] => None
    | None :: rest => digest_per_arm rest
    | Some input :: _ => Some (run initial input)
    end.

  Fixpoint selected_input (candidates : list (option Input)) : option Input :=
    match candidates with
    | [] => None
    | None :: rest => selected_input rest
    | Some input :: _ => Some input
    end.

  Definition digest_shared candidates :=
    option_map (run initial) (selected_input candidates).

  Lemma shared_digest_preserves_selected_stream : forall candidates,
    digest_shared candidates = digest_per_arm candidates.
  Proof.
    induction candidates as [|[input|] rest IH]; simpl; auto.
  Qed.

  Lemma shared_digest_preserves_unmatched_input : forall candidates,
    selected_input candidates = None -> digest_shared candidates = None.
  Proof. intros candidates H. unfold digest_shared. now rewrite H. Qed.

  Lemma copied_selected_record_preserves_lookup : forall selected : option Record,
    option_map (fun record => record) selected = selected.
  Proof. intros [record|]; reflexivity. Qed.
End SharedDispatchStorage.

Print Assumptions shared_digest_preserves_selected_stream.
Print Assumptions shared_digest_preserves_unmatched_input.
Print Assumptions copied_selected_record_preserves_lookup.

Section CrossCategoryPrefixDisplay.
  Definition prefix_source_threshold (source_max : nat) (explicit : option nat) : nat :=
    match explicit with
    | Some threshold => threshold
    | None => Nat.min 255 (source_max + 2)
    end.

  Definition prefix_display_threshold_before (same_category : bool) source_max explicit :=
    if same_category then prefix_source_threshold source_max explicit else 0.

  Definition prefix_display_threshold source_max explicit :=
    prefix_source_threshold source_max explicit.

  Definition prefix_operand_needs_group child_bp threshold := child_bp <? threshold.
  Definition prefix_operand_is_preserved child_bp threshold grouped :=
    orb grouped (threshold <=? child_bp).

  Theorem prefix_display_matches_parser_threshold : forall source_max explicit,
    prefix_display_threshold source_max explicit = prefix_source_threshold source_max explicit.
  Proof. reflexivity. Qed.

  Theorem prefix_explicit_threshold_is_preserved : forall source_max threshold,
    prefix_display_threshold source_max (Some threshold) = threshold.
  Proof. reflexivity. Qed.

  Theorem prefix_default_uses_source_maximum : forall source_max,
    prefix_display_threshold source_max None = Nat.min 255 (source_max + 2).
  Proof. reflexivity. Qed.

  Theorem same_category_prefix_display_is_unchanged : forall source_max explicit,
    prefix_display_threshold source_max explicit =
    prefix_display_threshold_before true source_max explicit.
  Proof. reflexivity. Qed.

  Theorem prefix_grouping_preserves_operand : forall child_bp threshold,
    prefix_operand_is_preserved child_bp threshold
      (prefix_operand_needs_group child_bp threshold) = true.
  Proof.
    intros child_bp threshold.
    unfold prefix_operand_is_preserved, prefix_operand_needs_group.
    destruct (child_bp <? threshold) eqn:Needs; simpl; [reflexivity|].
    apply Nat.ltb_ge in Needs. apply Nat.leb_le. exact Needs.
  Qed.

  Theorem prefix_grouping_is_necessary : forall child_bp threshold,
    prefix_operand_needs_group child_bp threshold = true ->
    prefix_operand_is_preserved child_bp threshold false = false.
  Proof.
    intros child_bp threshold Needs.
    unfold prefix_operand_needs_group in Needs. apply Nat.ltb_lt in Needs.
    unfold prefix_operand_is_preserved. simpl. apply Nat.leb_gt. exact Needs.
  Qed.

  Theorem omitted_cross_category_threshold_loses_infix_operand :
    prefix_operand_needs_group 2 (prefix_display_threshold_before false 3 None) = false /\
    prefix_operand_is_preserved 2 (prefix_source_threshold 3 None) false = false /\
    prefix_operand_is_preserved 2 (prefix_source_threshold 3 None)
      (prefix_operand_needs_group 2 (prefix_display_threshold 3 None)) = true.
  Proof. repeat split; reflexivity. Qed.
End CrossCategoryPrefixDisplay.

Print Assumptions prefix_display_matches_parser_threshold.
Print Assumptions prefix_explicit_threshold_is_preserved.
Print Assumptions prefix_default_uses_source_maximum.
Print Assumptions same_category_prefix_display_is_unchanged.
Print Assumptions prefix_grouping_preserves_operand.
Print Assumptions prefix_grouping_is_necessary.
Print Assumptions omitted_cross_category_threshold_loses_infix_operand.

Module SigilOperandTail.

Definition precedence_governed result source :=
  match source with
  | None => false
  | Some source => Nat.eqb source result
  end.

Definition follow_leading_operand closed result source :=
  andb closed (negb (precedence_governed result source)).

Definition wrap_operand closed result source leading_primary :=
  if follow_leading_operand closed result source then negb leading_primary else true.

Definition wrap_operand_before (closed leading_primary : bool) :=
  if closed then negb leading_primary else true.

Theorem local_operator_never_inherits_primary : forall closed category,
  follow_leading_operand closed category (Some category) = false.
Proof. intros; unfold follow_leading_operand, precedence_governed.
  rewrite Nat.eqb_refl. destruct closed; reflexivity. Qed.

Theorem local_operator_always_groups : forall closed category primary,
  wrap_operand closed category (Some category) primary = true.
Proof. intros; unfold wrap_operand. rewrite local_operator_never_inherits_primary. reflexivity. Qed.

Theorem unclassified_frame_preserves_old_wrap : forall closed category primary,
  wrap_operand closed category None primary = wrap_operand_before closed primary.
Proof. intros []; reflexivity. Qed.

Theorem foreign_operator_preserves_old_wrap : forall closed result source primary,
  source <> result ->
  wrap_operand closed result (Some source) primary = wrap_operand_before closed primary.
Proof. intros closed result source primary Hne.
  unfold wrap_operand, follow_leading_operand, precedence_governed, wrap_operand_before.
  apply Nat.eqb_neq in Hne. rewrite Hne. destruct closed; reflexivity. Qed.

Theorem open_tail_always_groups : forall result source primary,
  wrap_operand false result source primary = true.
Proof. reflexivity. Qed.

Theorem closed_unclassified_tail_follows_primary : forall category primary,
  wrap_operand true category None primary = negb primary.
Proof. reflexivity. Qed.

Theorem local_operator_grouping_preserves_prefix_operand : forall closed category primary child_bp threshold,
  prefix_operand_is_preserved child_bp threshold
    (wrap_operand closed category (Some category) primary) = true.
Proof. intros; rewrite local_operator_always_groups.
  unfold prefix_operand_is_preserved. reflexivity. Qed.

Example closed_literal_does_not_protect_a_local_tail :
  wrap_operand_before true true = false /\
  prefix_operand_is_preserved 2 220 (wrap_operand_before true true) = false /\
  prefix_operand_is_preserved 2 220 (wrap_operand true 0 (Some 0) true) = true.
Proof. repeat split; reflexivity. Qed.

Print Assumptions local_operator_never_inherits_primary.
Print Assumptions local_operator_always_groups.
Print Assumptions unclassified_frame_preserves_old_wrap.
Print Assumptions foreign_operator_preserves_old_wrap.
Print Assumptions open_tail_always_groups.
Print Assumptions closed_unclassified_tail_follows_primary.
Print Assumptions local_operator_grouping_preserves_prefix_operand.
Print Assumptions closed_literal_does_not_protect_a_local_tail.

End SigilOperandTail.
