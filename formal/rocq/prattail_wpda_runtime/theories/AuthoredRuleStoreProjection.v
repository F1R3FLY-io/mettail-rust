(** Retained authored-rule ownership boundary (8512).

    Storage follows grammar-core/src/theory_rule.rs: one flat arena, typed
    handles, and strictly backward edges checked at append. Parameter/name
    sequences and syntax sequences are flat vectors, not recursively owned
    grammar trees. Syntax and operation references share the arena order, so
    their cross-links need no new cycle-search algorithm.

    Source events below are a finite postorder enumeration of ORIGINAL shallow
    reader observations. They are not a parser or a reconstruction from lowered
    syntax. Capture checks and appends those events in order. Its theorem proves
    every accepted event's exact stored payload, index, read result and edge
    discipline. The frontend must separately establish that its explicit-stack
    source enumeration supplies these observations and source equality classes;
    this file does NOT assume or certify an arbitrary frontend traversal.

    Reused source vocabularies: TermParamReaderProjection and
    BinderRuleProjection. Legacy payloads use SyntheticRuleProjection's complete
    five collection kinds. Arrow domain and unsupported type interiors are not
    owned: no existing shallow reader inspects them. Unsupported tags/identity
    remain explicit. Runtime keyed PathMap retains BOTH children as a distinct
    node and yields a distinct not-representable observation, never HashMap.

    Name occurrence, stable spelling, and equality class are separate. A source
    equality-class certificate is necessary; pointer/index equality or spelling
    equality alone is not substituted for the original Ident equality.

    Allocation checks N.of_nat(index) < 2^32 BEFORE append. No wrapping cast is
    modeled as admission. Native allocation, usize/container limits and failed
    allocation are outside scope. This ownership proof does not imply the
    original classifiers' u8/u16 arithmetic domain; their existing finite-run
    and callback hypotheses still apply. No production classifier, normalizer,
    schema rejection, ABI decoder or parser behavior is changed or proved here.
*)
From Stdlib Require Import List String Bool Arith NArith Lia.
From PrattailWpdaRuntime Require Import TermParamReaderProjection
  BinderRuleProjection SyntheticRuleProjection.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module AuthoredRuleStoreProjection.
Module T := TermParamReaderProjection.TermParamReaderProjection.
Module B := BinderRuleProjection.BinderRuleProjection.
Module S := SyntheticRuleProjection.SyntheticRuleProjection.

Inductive Tag := NameTag | NamesTag | TypeTag | ParamTag | ParamsTag
  | SyntaxTag | OperationTag | RuleTag.
Definition tag_eq_dec : forall left right : Tag, {left = right} + {left <> right}.
Proof. decide equality. Defined.
Inductive Handle (kind : Tag) := Ref (index : nat).
Arguments Ref {kind} index.
Definition index {kind} (handle : Handle kind) :=
  match handle with Ref value => value end.
Definition Edge := (Tag * nat)%type.
Definition edge {kind} (handle : Handle kind) : Edge := (kind, index handle).
Definition optional_edge {kind} (handle : option (Handle kind)) : list Edge :=
  match handle with None => [] | Some value => [edge value] end.

Record NamePayload := {
  spelling : string; equality_class : nat
}.
Inductive NonterminalKind := Category | Var | Integer | Boolean
  | StringLiteral | FloatLiteral | Ident.
Inductive SourceLegacy :=
| SourceTerminal (text : string)
| SourceNonterminal (name : nat) (kind : NonterminalKind)
| SourceBinder (category : nat)
| SourceCollection (kind : S.CollectionKind) (element : nat)
    (separator : string) (open close : option string).
Inductive LegacyPayload :=
| Terminal (text : string)
| Nonterminal (name : Handle NameTag) (kind : NonterminalKind)
| Binder (category : Handle NameTag)
| LegacyCollection (kind : S.CollectionKind) (element : Handle NameTag)
    (separator : string) (open close : option string).
Definition own_legacy item := match item with
| SourceTerminal text => Terminal text
| SourceNonterminal name kind => Nonterminal (Ref name) kind
| SourceBinder category => Binder (Ref category)
| SourceCollection kind element separator open close =>
    LegacyCollection kind (Ref element) separator open close end.
Definition read_legacy item := match item with
| Terminal text => SourceTerminal text
| Nonterminal name kind => SourceNonterminal (index name) kind
| Binder category => SourceBinder (index category)
| LegacyCollection kind element separator open close =>
    SourceCollection kind (index element) separator open close end.
Definition legacy_edges item := match item with
| Terminal _ => [] | Nonterminal name _ => [edge name]
| Binder category => [edge category]
| LegacyCollection _ element _ _ _ => [edge element] end.

Inductive ParamPayload :=
| Simple (name : Handle NameTag) (ty : Handle TypeTag)
| GuardBody (name : Handle NameTag)
| Abstraction (binder body : Handle NameTag) (ty : Handle TypeTag)
| MultiAbstraction (binder body : Handle NameTag) (ty : Handle TypeTag)
| Optional (children : Handle ParamsTag).
Definition own_param p := match p with
| T.SSimple name ty => Simple (Ref name) (Ref ty)
| T.SGuardBody name => GuardBody (Ref name)
| T.SAbstraction binder body ty => Abstraction (Ref binder) (Ref body) (Ref ty)
| T.SMultiAbstraction binder body ty => MultiAbstraction (Ref binder) (Ref body) (Ref ty)
| T.SOptional children => Optional (Ref children) end.
Definition read_param p := match p with
| Simple name ty => T.Simple (index name) (index ty)
| GuardBody name => T.GuardBody (index name)
| Abstraction binder body ty => T.Abstraction (index binder) (index body) (index ty)
| MultiAbstraction binder body ty => T.MultiAbstraction (index binder) (index body) (index ty)
| Optional children => T.Optional (index children) end.
Definition param_edges p := match p with
| Simple name ty => [edge name; edge ty]
| GuardBody name => [edge name]
| Abstraction binder body ty | MultiAbstraction binder body ty =>
    [edge binder; edge body; edge ty]
| Optional children => [edge children] end.

Inductive TypePayload :=
| Base (name : Handle NameTag)
| Collection (kind : nat) (element : Handle TypeTag)
| MapType (key value : Handle TypeTag)
| Arrow (codomain : Handle TypeTag)
| UnsupportedType (tag : nat)
| KeyedPathMap (key value : Handle TypeTag).
Inductive SourceType :=
| ExistingType (ty : B.SourceType)
| RuntimeKeyedPathMap (key value : nat).
Definition own_type ty := match ty with
| ExistingType ty => match ty with
  | B.SBase name => Base (Ref name)
  | B.SCollection kind element => Collection kind (Ref element)
  | B.SMapType key value => MapType (Ref key) (Ref value)
  | B.SArrow _ codomain => Arrow (Ref codomain)
  | B.STypeOther tag => UnsupportedType tag end
| RuntimeKeyedPathMap key value => KeyedPathMap (Ref key) (Ref value) end.
Inductive TypeObservation :=
| BaseObservation (name : nat)
| CollectionObservation (kind element : nat)
| MapObservation (key value : nat)
| ArrowObservation (codomain : nat)
| OtherTypeObservation (original : nat)
| KeyedPathMapNotRepresentable (key value : nat).
Definition source_type_observation original ty := match ty with
| ExistingType ty => match ty with
  | B.SBase name => BaseObservation name
  | B.SCollection kind element => CollectionObservation kind element
  | B.SMapType key value => MapObservation key value
  | B.SArrow _ codomain => ArrowObservation codomain
  | B.STypeOther _ => OtherTypeObservation original end
| RuntimeKeyedPathMap key value => KeyedPathMapNotRepresentable key value end.
Definition read_type original ty := match ty with
| Base name => BaseObservation (index name)
| Collection kind element => CollectionObservation kind (index element)
| MapType key value => MapObservation (index key) (index value)
| Arrow codomain => ArrowObservation (index codomain)
| UnsupportedType _ => OtherTypeObservation original
| KeyedPathMap key value => KeyedPathMapNotRepresentable (index key) (index value) end.
Definition type_edges ty := match ty with
| Base name => [edge name] | Collection _ element => [edge element]
| MapType key value | KeyedPathMap key value => [edge key; edge value]
| Arrow codomain => [edge codomain] | UnsupportedType _ => [] end.

Inductive SyntaxPayload :=
| Literal (text : string) | ParamRef (name : Handle NameTag)
| TokenKind (name : Handle NameTag) (bind : option (Handle NameTag))
| GuestBody (open close bind : Handle NameTag) (kind : nat)
| OperationRef (operation : Handle OperationTag).
Definition own_syntax syntax := match syntax with
| B.SLiteral text => Literal text | B.SParam name => ParamRef (Ref name)
| B.SToken name bind => TokenKind (Ref name) (option_map Ref bind)
| B.SGuest open close bind kind => GuestBody (Ref open) (Ref close) (Ref bind) kind
| B.SOp operation => OperationRef (Ref operation) end.
Definition read_syntax syntax := match syntax with
| Literal text => B.Literal text | ParamRef name => B.Param (index name)
| TokenKind name bind => B.Token (index name) (option_map index bind)
| GuestBody open close bind kind => B.Guest (index open) (index close) (index bind) kind
| OperationRef operation => B.Op (index operation) end.
Definition syntax_edges syntax := match syntax with
| Literal _ => [] | ParamRef name => [edge name]
| TokenKind name bind => edge name :: optional_edge bind
| GuestBody open close bind _ => [edge open; edge close; edge bind]
| OperationRef operation => [edge operation] end.

Inductive OperationPayload :=
| Opt (inner : Handle SyntaxTag)
| Sep (collection : Handle NameTag) (separator : string)
    (source : option (Handle OperationTag))
| Map (source : Handle OperationTag) (aliases : Handle NamesTag) (body : Handle SyntaxTag)
| Zip (left right : Handle NameTag)
| UnsupportedOperation (tag : nat).
Definition own_operation operation := match operation with
| B.SOpt inner => Opt (Ref inner)
| B.SSep collection separator source => Sep (Ref collection) separator (option_map Ref source)
| B.SMap source aliases body => Map (Ref source) (Ref aliases) (Ref body)
| B.SZip lhs rhs => Zip (Ref lhs) (Ref rhs)
| B.SOperationOther tag => UnsupportedOperation tag end.
Definition read_operation original operation := match operation with
| Opt inner => B.Opt (index inner)
| Sep collection separator source => B.Sep (index collection) separator (option_map index source)
| Map source aliases body => B.Map (index source) (index aliases) (index body)
| Zip lhs rhs => B.Zip (index lhs) (index rhs)
| UnsupportedOperation _ => B.OperationOther original end.
Definition operation_edges operation := match operation with
| Opt inner => [edge inner]
| Sep collection _ source => edge collection :: optional_edge source
| Map source aliases body => [edge source; edge aliases; edge body]
| Zip lhs rhs => [edge lhs; edge rhs]
| UnsupportedOperation _ => [] end.

Record RulePayload := {
  label : Handle NameTag; category : Handle NameTag;
  term_context : option (Handle ParamsTag);
  syntax_pattern : option (Handle SyntaxTag);
  legacy_items : list LegacyPayload
}.
Definition own_rule (rule : B.Rule) items :=
 {| label := Ref (B.rule_label rule); category := Ref (B.rule_category rule);
    term_context := option_map Ref (B.term_context rule);
    syntax_pattern := option_map Ref (B.syntax_pattern rule);
    legacy_items := List.map own_legacy items |}.
Definition read_rule rule : B.Rule :=
 {| B.rule_label := index (label rule); B.rule_category := index (category rule);
    B.term_context := option_map index (term_context rule);
    B.syntax_pattern := option_map index (syntax_pattern rule) |}.
Definition rule_edges rule :=
  [edge (label rule); edge (category rule)] ++
  optional_edge (term_context rule) ++ optional_edge (syntax_pattern rule) ++
  flat_map legacy_edges (legacy_items rule).

Inductive SourceNode :=
| SourceName (name : NamePayload) | SourceNames (names : list nat)
| SourceTypeNode (ty : SourceType) | SourceParamNode (param : T.SourceParam)
| SourceParams (params : list nat) | SourceSyntax (syntax : list B.SourceSyntax)
| SourceOperation (operation : B.SourceOperation)
| SourceRule (rule : B.Rule) (items : list SourceLegacy).
Inductive Node :=
| NameNode (name : NamePayload) | NamesNode (names : list (Handle NameTag))
| TypeNode (ty : TypePayload) | ParamNode (param : ParamPayload)
| ParamsNode (params : list (Handle ParamTag)) | SyntaxNode (syntax : list SyntaxPayload)
| OperationNode (operation : OperationPayload) | RuleNode (rule : RulePayload).
Definition own_node node := match node with
| SourceName name => NameNode name | SourceNames names => NamesNode (List.map Ref names)
| SourceTypeNode ty => TypeNode (own_type ty)
| SourceParamNode param => ParamNode (own_param param)
| SourceParams params => ParamsNode (List.map Ref params)
| SourceSyntax syntax => SyntaxNode (List.map own_syntax syntax)
| SourceOperation operation => OperationNode (own_operation operation)
| SourceRule rule items => RuleNode (own_rule rule items) end.
Definition node_tag node := match node with
| NameNode _ => NameTag | NamesNode _ => NamesTag | TypeNode _ => TypeTag
| ParamNode _ => ParamTag | ParamsNode _ => ParamsTag | SyntaxNode _ => SyntaxTag
| OperationNode _ => OperationTag | RuleNode _ => RuleTag end.
Definition node_edges node := match node with
| NameNode _ => [] | NamesNode names => List.map edge names
| TypeNode ty => type_edges ty | ParamNode param => param_edges param
| ParamsNode params => List.map edge params
| SyntaxNode syntax => flat_map syntax_edges syntax
| OperationNode operation => operation_edges operation
| RuleNode rule => rule_edges rule end.

Definition index_fits_u32 n := N.ltb (N.of_nat n) (2 ^ 32)%N.
Definition reference_valid (arena : list Node) (reference : Edge) :=
  match nth_error arena (snd reference) with
  | None => false
  | Some node => if tag_eq_dec (node_tag node) (fst reference) then true else false
  end.
Definition node_valid arena node := forallb (reference_valid arena) (node_edges node).
Definition append_checked arena node :=
  if index_fits_u32 (List.length arena) && node_valid arena node
  then Some (arena ++ [node]) else None.
Fixpoint capture_into arena events : option (list Node) :=
  match events with
  | [] => Some arena
  | event :: remaining => match append_checked arena (own_node event) with
    | None => None | Some next => capture_into next remaining end
  end.
Definition capture events := capture_into [] events.

Inductive ValidArena : list Node -> Prop :=
| ValidEmpty : ValidArena []
| ValidAppend arena node : ValidArena arena ->
    index_fits_u32 (List.length arena) = true -> node_valid arena node = true ->
    ValidArena (arena ++ [node]).

Lemma checked_u32_boundary : forall n,
  index_fits_u32 n = true <-> (N.of_nat n < 2 ^ 32)%N.
Proof. intros; unfold index_fits_u32; apply N.ltb_lt. Qed.
Theorem allocation_overflow_refuses_before_append : forall arena node,
  (2 ^ 32 <= N.of_nat (List.length arena))%N -> append_checked arena node = None.
Proof.
  intros arena node H; unfold append_checked, index_fits_u32.
  assert (N.ltb (N.of_nat (List.length arena)) (2 ^ 32) = false) as E
    by (apply N.ltb_ge; exact H).
  rewrite E; reflexivity.
Qed.
Lemma append_checked_exact : forall arena node result,
  append_checked arena node = Some result ->
  result = arena ++ [node] /\ index_fits_u32 (List.length arena) = true /\
  node_valid arena node = true.
Proof.
  intros arena node result; unfold append_checked.
  destruct (index_fits_u32 (List.length arena) && node_valid arena node) eqn:E;
    intros H; [|discriminate].
  inversion H; subst. apply andb_true_iff in E. tauto.
Qed.
Lemma append_checked_preserves_validity : forall arena node result,
  ValidArena arena -> append_checked arena node = Some result -> ValidArena result.
Proof.
  intros arena node result V H. apply append_checked_exact in H.
  destruct H as [-> [I E]]. constructor; assumption.
Qed.
Theorem capture_preserves_validity : forall events arena result,
  ValidArena arena -> capture_into arena events = Some result -> ValidArena result.
Proof.
  induction events as [|event rest IH]; intros arena result V H; cbn in H.
  - inversion H; subst; assumption.
  - destruct (append_checked arena (own_node event)) as [next|] eqn:E; [|discriminate].
    eapply IH; [eapply append_checked_preserves_validity; eauto|exact H].
Qed.
Theorem captured_store_is_valid : forall events result,
  capture events = Some result -> ValidArena result.
Proof. intros; eapply capture_preserves_validity; [constructor|eassumption]. Qed.

Lemma reference_valid_sound : forall arena reference,
  reference_valid arena reference = true ->
  exists node, nth_error arena (snd reference) = Some node /\
    node_tag node = fst reference /\ snd reference < List.length arena.
Proof.
  intros arena [kind position] H; unfold reference_valid in H; cbn in *.
  destruct (nth_error arena position) as [node|] eqn:E; [|discriminate].
  destruct (tag_eq_dec (node_tag node) kind) as [K|K]; [|discriminate].
  exists node; repeat split; try assumption.
  apply nth_error_Some. rewrite E. discriminate.
Qed.
Theorem appended_edges_have_prior_typed_targets : forall arena node result reference,
  append_checked arena node = Some result -> In reference (node_edges node) ->
  exists target, nth_error arena (snd reference) = Some target /\
    node_tag target = fst reference /\ snd reference < List.length arena.
Proof.
  intros arena node result reference H Hin.
  apply append_checked_exact in H; destruct H as [_ [_ H]].
  unfold node_valid in H. apply forallb_forall with (x := reference) in H; [|exact Hin].
  apply reference_valid_sound; exact H.
Qed.
Lemma lookup_append_stable : forall (arena suffix : list Node) position node,
  nth_error arena position = Some node -> nth_error (arena ++ suffix) position = Some node.
Proof.
  intros arena suffix position node E.
  rewrite nth_error_app1; [exact E|].
  apply nth_error_Some. rewrite E. discriminate.
Qed.
Lemma lookup_snoc_cases : forall (arena : list Node) last position node,
  nth_error (arena ++ [last]) position = Some node ->
  nth_error arena position = Some node \/ (position = List.length arena /\ node = last).
Proof.
  intros arena last position node H.
  destruct (lt_dec position (List.length arena)) as [L|L].
  - left. rewrite nth_error_app1 in H by exact L. exact H.
  - right. rewrite nth_error_app2 in H by lia.
    destruct (position - List.length arena) eqn:E; cbn in H; [|destruct n; discriminate].
    inversion H; subst; split; [lia|reflexivity].
Qed.
Theorem valid_arena_edges_strictly_decrease : forall arena,
  ValidArena arena -> forall owner node reference,
  nth_error arena owner = Some node -> In reference (node_edges node) ->
  exists target, nth_error arena (snd reference) = Some target /\
    node_tag target = fst reference /\ snd reference < owner.
Proof.
  intros arena V; induction V as [|arena last V IH Fits Edges]; intros owner node reference E Hin.
  - destruct owner; discriminate.
  - apply lookup_snoc_cases in E. destruct E as [E|[E N]].
    + destruct (IH owner node reference E Hin) as [target [Read [Kind Lower]]].
      exists target; repeat split; try assumption. apply lookup_append_stable; exact Read.
    + subst owner node. unfold node_valid in Edges.
      apply forallb_forall with (x := reference) in Edges; [|exact Hin].
      destruct (@reference_valid_sound arena reference Edges) as [target [Read [Kind Lower]]].
      exists target; repeat split; try assumption. apply lookup_append_stable; exact Read.
Qed.

(** Every graph descent decreases its arena index; no recursive owned node is
    needed and no cycle can return to its start. This is not a Rust stack-size
    or execution-cost theorem. *)
Inductive Descends (arena : list Node) : nat -> nat -> Prop :=
| OneEdge owner node reference : nth_error arena owner = Some node ->
    In reference (node_edges node) -> Descends arena owner (snd reference)
| MoreEdges first middle last : Descends arena first middle ->
    Descends arena middle last -> Descends arena first last.
Theorem valid_descent_decreases : forall arena,
  ValidArena arena -> forall first last, Descends arena first last -> last < first.
Proof.
  intros arena V first last D; induction D.
  - destruct (@valid_arena_edges_strictly_decrease arena V owner node reference H H0)
      as [target [_ [_ Lower]]].
    exact Lower.
  - lia.
Qed.
Corollary valid_arena_has_no_cycle : forall arena position,
  ValidArena arena -> ~ Descends arena position position.
Proof. intros arena position V D; pose proof (@valid_descent_decreases arena V position position D); lia. Qed.

(** Accepted capture is an actual ordered append loop, not a pair of aliases
    to the same abstract reader. No deduplication/reordering is performed. *)
Theorem capture_payloads_exact : forall events arena result,
  capture_into arena events = Some result -> result = arena ++ List.map own_node events.
Proof.
  induction events as [|event rest IH]; intros arena result H; cbn in H.
  - inversion H; subst; rewrite app_nil_r; reflexivity.
  - destruct (append_checked arena (own_node event)) as [next|] eqn:E; [|discriminate].
    apply append_checked_exact in E; destruct E as [E _]; subst next.
    specialize (IH _ _ H). rewrite IH, <- app_assoc. reflexivity.
Qed.
Lemma map_nth_exact : forall (A C : Type) (f : A -> C) xs position,
  nth_error (List.map f xs) position = option_map f (nth_error xs position).
Proof.
  intros A C f xs; induction xs as [|x rest IH]; intros [|position]; cbn; auto.
Qed.
Theorem capture_index_correspondence : forall events arena position source,
  capture events = Some arena -> nth_error events position = Some source ->
  nth_error arena position = Some (own_node source).
Proof.
  intros events arena position source H E. apply capture_payloads_exact in H; cbn in H; subst arena.
  rewrite map_nth_exact, E; reflexivity.
Qed.
Theorem capture_length_and_order : forall events arena,
  capture events = Some arena ->
  List.length arena = List.length events /\ arena = List.map own_node events.
Proof.
  intros events arena H. apply capture_payloads_exact in H; cbn in H; subst arena.
  split; [apply length_map|reflexivity].
Qed.
Theorem capture_old_handles_stable : forall events arena result position node,
  capture_into arena events = Some result -> nth_error arena position = Some node ->
  nth_error result position = Some node.
Proof.
  intros events arena result position node H E. apply capture_payloads_exact in H; subst result.
  apply lookup_append_stable; exact E.
Qed.

(** Deserialization checks exactly the same append boundary. It is not enough
    for a deserialized u32 to be in range: the target tag and backward direction
    must also match. Validation does not reorder or repair invalid nodes. *)
Fixpoint validate_into prefix nodes : option (list Node) :=
  match nodes with
  | [] => Some prefix
  | node :: rest => match append_checked prefix node with
    | None => None | Some next => validate_into next rest end
  end.
Definition validate nodes := validate_into [] nodes.
Theorem validation_retains_exact_nodes : forall nodes prefix result,
  validate_into prefix nodes = Some result -> result = prefix ++ nodes.
Proof.
  induction nodes as [|node rest IH]; intros prefix result H; cbn in H.
  - inversion H; subst; rewrite app_nil_r; reflexivity.
  - destruct (append_checked prefix node) as [next|] eqn:E; [|discriminate].
    apply append_checked_exact in E; destruct E as [E _]; subst next.
    specialize (IH _ _ H). rewrite IH, <- app_assoc; reflexivity.
Qed.
Theorem validation_establishes_validity : forall nodes prefix result,
  ValidArena prefix -> validate_into prefix nodes = Some result -> ValidArena result.
Proof.
  induction nodes as [|node rest IH]; intros prefix result V H; cbn in H.
  - inversion H; subst; assumption.
  - destruct (append_checked prefix node) as [next|] eqn:E; [|discriminate].
    eapply IH; [eapply append_checked_preserves_validity; eauto|exact H].
Qed.
Corollary deserialized_validation_is_not_reconstruction : forall nodes result,
  validate nodes = Some result -> result = nodes /\ ValidArena nodes.
Proof.
  intros nodes result H.
  pose proof (@validation_retains_exact_nodes nodes [] result H) as E; cbn in E; subst result.
  split; [reflexivity|]. eapply validation_establishes_validity; [constructor|exact H].
Qed.
Definition append_transaction arena node :=
  match append_checked arena node with
  | None => (arena, None)
  | Some next => (next, Some (List.length arena)) end.
Theorem rejected_append_leaves_store_unchanged : forall arena node,
  append_checked arena node = None -> append_transaction arena node = (arena, None).
Proof. intros arena node H; unfold append_transaction; rewrite H; reflexivity. Qed.
Theorem successful_append_returns_exact_checked_id : forall arena node next,
  append_checked arena node = Some next ->
  append_transaction arena node = (next, Some (List.length arena)) /\
  index_fits_u32 (List.length arena) = true.
Proof.
  intros arena node next H; split.
  - unfold append_transaction; rewrite H; reflexivity.
  - apply append_checked_exact in H; tauto.
Qed.

Definition parameters arena (handle : Handle ParamsTag) :=
  match nth_error arena (index handle) with
  | Some (ParamsNode params) => Some (List.map index params) | _ => None end.
Definition syntax_items arena (handle : Handle SyntaxTag) :=
  match nth_error arena (index handle) with
  | Some (SyntaxNode syntax) => Some (List.map read_syntax syntax) | _ => None end.
Definition parameter arena (handle : Handle ParamTag) :=
  match nth_error arena (index handle) with
  | Some (ParamNode param) => Some (read_param param) | _ => None end.
Definition operation arena (handle : Handle OperationTag) :=
  match nth_error arena (index handle) with
  | Some (OperationNode op) => Some (read_operation (index handle) op) | _ => None end.
Definition type_observation arena (handle : Handle TypeTag) :=
  match nth_error arena (index handle) with
  | Some (TypeNode ty) => Some (read_type (index handle) ty) | _ => None end.
Definition authored_rule arena (handle : Handle RuleTag) :=
  match nth_error arena (index handle) with
  | Some (RuleNode rule) => Some (read_rule rule, List.map read_legacy (legacy_items rule))
  | _ => None end.
Definition name_payload arena (handle : Handle NameTag) :=
  match nth_error arena (index handle) with Some (NameNode name) => Some name | _ => None end.
Definition names arena (handle : Handle NamesTag) :=
  match nth_error arena (index handle) with
  | Some (NamesNode values) => Some (List.map index values) | _ => None end.
Definition names_equal arena left right :=
  match name_payload arena left, name_payload arena right with
  | Some lhs, Some rhs => Some (Nat.eqb (equality_class lhs) (equality_class rhs))
  | _, _ => None end.

Lemma read_owned_parameter : forall source,
  read_param (own_param source) = T.project_param source.
Proof. destruct source; reflexivity. Qed.
Lemma read_owned_syntax : forall source,
  read_syntax (own_syntax source) = B.project_syntax source.
Proof. destruct source; cbn; try reflexivity. destruct bind; reflexivity. Qed.
Lemma read_owned_operation : forall source original,
  read_operation original (own_operation source) = B.project_operation original source.
Proof. destruct source; intros; cbn; try reflexivity. destruct source; reflexivity. Qed.
Lemma read_owned_type : forall source original,
  read_type original (own_type source) = source_type_observation original source.
Proof. intros [ty|key value] original; [destruct ty|]; reflexivity. Qed.
Lemma read_owned_legacy : forall source, read_legacy (own_legacy source) = source.
Proof. destruct source; reflexivity. Qed.
Lemma read_owned_rule : forall source items, read_rule (own_rule source items) = source.
Proof.
  intros [tc sp label category] items; destruct tc; destruct sp; reflexivity.
Qed.
Lemma indexes_of_refs : forall kind (values : list nat),
  List.map index (List.map (@Ref kind) values) = values.
Proof. intros kind values; induction values; cbn; congruence. Qed.

Theorem captured_parameter_observation : forall events arena position source,
  capture events = Some arena -> nth_error events position = Some (SourceParamNode source) ->
  parameter arena (Ref position) = Some (T.project_param source).
Proof.
  intros events arena position source H E; unfold parameter; cbn.
  rewrite (@capture_index_correspondence events arena position _ H E). cbn. rewrite read_owned_parameter; reflexivity.
Qed.
Theorem captured_parameter_sequence : forall events arena position source,
  capture events = Some arena -> nth_error events position = Some (SourceParams source) ->
  parameters arena (Ref position) = Some source.
Proof.
  intros events arena position source H E; unfold parameters; cbn.
  rewrite (@capture_index_correspondence events arena position _ H E). cbn. rewrite indexes_of_refs; reflexivity.
Qed.
Theorem captured_syntax_sequence : forall events arena position source,
  capture events = Some arena -> nth_error events position = Some (SourceSyntax source) ->
  syntax_items arena (Ref position) = Some (List.map B.project_syntax source).
Proof.
  intros events arena position source H E; unfold syntax_items; cbn.
  rewrite (@capture_index_correspondence events arena position _ H E). cbn. rewrite map_map.
  f_equal. apply map_ext. apply read_owned_syntax.
Qed.
Theorem captured_operation_observation : forall events arena position source,
  capture events = Some arena -> nth_error events position = Some (SourceOperation source) ->
  operation arena (Ref position) = Some (B.project_operation position source).
Proof.
  intros events arena position source H E; unfold operation; cbn.
  rewrite (@capture_index_correspondence events arena position _ H E). cbn. rewrite read_owned_operation; reflexivity.
Qed.
Theorem captured_type_observation : forall events arena position source,
  capture events = Some arena -> nth_error events position = Some (SourceTypeNode source) ->
  type_observation arena (Ref position) = Some (source_type_observation position source).
Proof.
  intros events arena position source H E; unfold type_observation; cbn.
  rewrite (@capture_index_correspondence events arena position _ H E). cbn. rewrite read_owned_type; reflexivity.
Qed.
Theorem captured_rule_and_legacy : forall events arena position source items,
  capture events = Some arena -> nth_error events position = Some (SourceRule source items) ->
  authored_rule arena (Ref position) = Some (source, items).
Proof.
  intros events arena position source items H E; unfold authored_rule; cbn.
  rewrite (@capture_index_correspondence events arena position _ H E). cbn. rewrite read_owned_rule, map_map.
  assert (List.map (fun item => read_legacy (own_legacy item)) items = items) as Exact.
  { clear H E. induction items; cbn; [reflexivity|rewrite read_owned_legacy, IHitems; reflexivity]. }
  rewrite Exact; reflexivity.
Qed.
Theorem captured_name_identity_and_spelling : forall events arena position source,
  capture events = Some arena -> nth_error events position = Some (SourceName source) ->
  name_payload arena (Ref position) = Some source.
Proof.
  intros events arena position source H E; unfold name_payload; cbn.
  rewrite (@capture_index_correspondence events arena position _ H E); reflexivity.
Qed.
Theorem captured_name_sequence : forall events arena position source,
  capture events = Some arena -> nth_error events position = Some (SourceNames source) ->
  names arena (Ref position) = Some source.
Proof.
  intros events arena position source H E; unfold names; cbn.
  rewrite (@capture_index_correspondence events arena position _ H E). cbn. rewrite indexes_of_refs; reflexivity.
Qed.
Theorem captured_name_equality : forall events arena left right lhs rhs,
  capture events = Some arena -> nth_error events left = Some (SourceName lhs) ->
  nth_error events right = Some (SourceName rhs) ->
  names_equal arena (Ref left) (Ref right) =
    Some (Nat.eqb (equality_class lhs) (equality_class rhs)).
Proof.
  intros events arena left right lhs rhs H L R; unfold names_equal.
  rewrite (@captured_name_identity_and_spelling events arena left lhs H L),
    (@captured_name_identity_and_spelling events arena right rhs H R); reflexivity.
Qed.

(** Existing iterator laws consume these exact lists, without filtering unused
    declarations or replacing duplicate names. This law is the finite-arena
    counterpart of T.ReaderValid, restricted to admitted sequence handles. *)
Theorem admitted_sequence_index_law : forall arena handle values index,
  parameters arena handle = Some values ->
  (nth_error values index <> None <-> index < List.length values).
Proof. intros; apply nth_error_Some. Qed.
Theorem admitted_syntax_index_law : forall arena handle values index,
  syntax_items arena handle = Some values ->
  (nth_error values index <> None <-> index < List.length values).
Proof. intros; apply nth_error_Some. Qed.

Theorem independent_optional_presence : forall tc sp label category items,
  B.term_context (read_rule (own_rule
    {| B.term_context := tc; B.syntax_pattern := sp;
       B.rule_label := label; B.rule_category := category |} items)) = tc /\
  B.syntax_pattern (read_rule (own_rule
    {| B.term_context := tc; B.syntax_pattern := sp;
       B.rule_label := label; B.rule_category := category |} items)) = sp.
Proof. intros; rewrite !read_owned_rule; split; reflexivity. Qed.
Theorem operation_source_and_alias_identity : forall source aliases body,
  read_operation 0 (own_operation (B.SMap source aliases body)) = B.Map source aliases body /\
  read_operation 0 (own_operation (B.SSep 1 "" (Some source))) = B.Sep 1 "" (Some source).
Proof. intros; split; reflexivity. Qed.
Theorem unsupported_original_handle_retained : forall tag handle,
  read_operation handle (own_operation (B.SOperationOther tag)) = B.OperationOther handle /\
  read_type handle (own_type (ExistingType (B.STypeOther tag))) = OtherTypeObservation handle.
Proof. intros; split; reflexivity. Qed.
Theorem keyed_pathmap_does_not_become_map : forall key value original,
  read_type original (own_type (RuntimeKeyedPathMap key value)) =
    KeyedPathMapNotRepresentable key value /\
  read_type original (own_type (RuntimeKeyedPathMap key value)) <> MapObservation key value.
Proof. intros; split; [reflexivity|discriminate]. Qed.

Definition same_spelling_distinct_names :=
  [SourceName {| spelling := "x"; equality_class := 0 |};
   SourceName {| spelling := "x"; equality_class := 1 |}].
Example equal_spelling_is_not_identifier_equality :
  names_equal (List.map own_node same_spelling_distinct_names) (Ref 0) (Ref 1) = Some false.
Proof. reflexivity. Qed.
Example distinct_occurrences_can_be_equal :
  names_equal
    [NameNode {| spelling := "x"; equality_class := 7 |};
     NameNode {| spelling := "x"; equality_class := 7 |}]
    (Ref 0) (Ref 1) = Some true.
Proof. reflexivity. Qed.
Example self_referential_optional_refused :
  append_checked [] (ParamNode (Optional (Ref 0))) = None.
Proof. reflexivity. Qed.
Example wrong_kind_reference_refused :
  append_checked [NameNode {| spelling := "x"; equality_class := 0 |}]
    (ParamNode (Optional (Ref 0))) = None.
Proof. reflexivity. Qed.

(** Original macro Option-pair is embedded without changing either presence.
    Runtime half-present input stays stored, but cannot be admitted as the
    original LegacyItemView delimiter field. This does not reject decoding. *)
Definition macro_delimiters (pair : option (string * string)) :=
  match pair with None => (None, None)
  | Some (open, close) => (Some open, Some close) end.
Definition legacy_delimiter_view (open close : option string) :
    option (option (string * string)) :=
  match open, close with
  | None, None => Some None
  | Some open, Some close => Some (Some (open, close))
  | _, _ => None end.
Theorem original_delimiter_presence_preserved : forall delimiters,
  legacy_delimiter_view (fst (macro_delimiters delimiters))
    (snd (macro_delimiters delimiters)) = Some delimiters.
Proof. intros [[open close]|]; reflexivity. Qed.
Theorem half_present_delimiters_not_erased : forall kind element separator open,
  read_legacy (own_legacy (SourceCollection kind element separator (Some open) None)) =
    SourceCollection kind element separator (Some open) None /\
  legacy_delimiter_view (Some open) None = None.
Proof. intros; split; reflexivity. Qed.

Print Assumptions checked_u32_boundary.
Print Assumptions allocation_overflow_refuses_before_append.
Print Assumptions captured_store_is_valid.
Print Assumptions valid_arena_has_no_cycle.
Print Assumptions capture_payloads_exact.
Print Assumptions capture_index_correspondence.
Print Assumptions capture_old_handles_stable.
Print Assumptions deserialized_validation_is_not_reconstruction.
Print Assumptions rejected_append_leaves_store_unchanged.
Print Assumptions successful_append_returns_exact_checked_id.
Print Assumptions captured_parameter_observation.
Print Assumptions captured_parameter_sequence.
Print Assumptions captured_syntax_sequence.
Print Assumptions captured_operation_observation.
Print Assumptions captured_type_observation.
Print Assumptions captured_rule_and_legacy.
Print Assumptions captured_name_equality.
Print Assumptions captured_name_sequence.
Print Assumptions independent_optional_presence.
Print Assumptions keyed_pathmap_does_not_become_map.
Print Assumptions original_delimiter_presence_preserved.
Print Assumptions half_present_delimiters_not_erased.

End AuthoredRuleStoreProjection.
