(** Bounded postorder capture of the existing authored-reader vocabulary.

    Source contract: plan 14264; grammar-core/src/authored.rs's generic typed
    ID payloads and try_for_each_reference. No source syntax is parsed here.
    The finite immutable source table contains the already existing shallow
    SourceNode observations, keyed by (expected tag, ephemeral source identity).
    A concrete frontend must justify its table/borrowed adapter independently.

    One Enter/Finish worklist performs capture. Pending is distinct from Ready;
    children are visited in immediate-field order, and completed shared nodes
    are reused without another source read. Name equality keys are natural
    representatives of the original Eq relation, not spellings or pointer IDs.
    Class lookup/first assignment is concrete below. HashMap storage/iteration,
    allocation, arbitrary frontend termination and parser semantics are not
    part of the correspondence. Admission is an explicit Boolean boundary,
    not a newly invented resource policy. The u32 append and class checks are
    concrete. Every execution theorem is finite; no fuel policy enters Rust.
*)
From Stdlib Require Import List String Bool Arith NArith Lia.
From PrattailWpdaRuntime Require Import AuthoredRuleStoreProjection.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module AuthoredRuleCaptureProjection.
Module A := AuthoredRuleStoreProjection.AuthoredRuleStoreProjection.
Module T := A.T.
Module B := A.B.

Definition edge_eq_dec : forall left right : A.Edge, {left = right} + {left <> right}.
Proof. decide equality; [apply Nat.eq_dec|apply A.tag_eq_dec]. Defined.
Definition SourceGraph := list (A.Edge * A.SourceNode).
Fixpoint lookup_source (graph : SourceGraph) edge := match graph with
| [] => None
| (key, node) :: rest => if edge_eq_dec edge key then Some node else lookup_source rest edge
end.
Definition source_tag source := A.node_tag (A.own_node source).
Definition source_edges source := A.node_edges (A.own_node source).

Definition bind {X Y} (value : option X) (next : X -> option Y) :=
  match value with Some item => next item | None => None end.
Notation "x <- value ;; next" := (bind value (fun x => next))
  (at level 100, value at next level, right associativity).
Fixpoint map_checked {X Y} (f : X -> option Y) values := match values with
| [] => Some []
| value :: rest => first <- f value ;; tail <- map_checked f rest ;; Some (first :: tail)
end.
Definition optional_checked {X Y} (f : X -> option Y) value := match value with
| None => Some None | Some value => mapped <- f value ;; Some (Some mapped) end.
Definition Resolver := A.Edge -> option nat.
Definition resolve (reader : Resolver) tag identity := reader (tag, identity).

(** Fieldwise substitution of references only. All names/types/operations use
    the same resolver, with their original expected tag. These are the existing
    eight shallow payload cases, not a second grammar representation. *)
Definition remap_param (reader : Resolver) param := match param with
| T.SSimple name ty => n <- resolve reader A.NameTag name ;;
    t <- resolve reader A.TypeTag ty ;; Some (T.SSimple n t)
| T.SGuardBody name => n <- resolve reader A.NameTag name ;; Some (T.SGuardBody n)
| T.SAbstraction binder body ty => b <- resolve reader A.NameTag binder ;;
    n <- resolve reader A.NameTag body ;; t <- resolve reader A.TypeTag ty ;;
    Some (T.SAbstraction b n t)
| T.SMultiAbstraction binder body ty => b <- resolve reader A.NameTag binder ;;
    n <- resolve reader A.NameTag body ;; t <- resolve reader A.TypeTag ty ;;
    Some (T.SMultiAbstraction b n t)
| T.SOptional children => c <- resolve reader A.ParamsTag children ;; Some (T.SOptional c)
end.
Definition remap_type (reader : Resolver) ty := match ty with
| A.ExistingType ty => mapped <- match ty with
  | B.SBase name => n <- resolve reader A.NameTag name ;; Some (B.SBase n)
  | B.SCollection kind element => e <- resolve reader A.TypeTag element ;;
      Some (B.SCollection kind e)
  | B.SMapType key value => k <- resolve reader A.TypeTag key ;;
      v <- resolve reader A.TypeTag value ;; Some (B.SMapType k v)
  | B.SArrow domain codomain => c <- resolve reader A.TypeTag codomain ;;
      Some (B.SArrow domain c)
  | B.STypeOther tag => Some (B.STypeOther tag)
  end ;; Some (A.ExistingType mapped)
| A.RuntimeKeyedPathMap key value => k <- resolve reader A.TypeTag key ;;
    v <- resolve reader A.TypeTag value ;; Some (A.RuntimeKeyedPathMap k v)
end.
Definition remap_syntax (reader : Resolver) syntax := match syntax with
| B.SLiteral text => Some (B.SLiteral text)
| B.SParam name => n <- resolve reader A.NameTag name ;; Some (B.SParam n)
| B.SToken name bind => n <- resolve reader A.NameTag name ;;
    b <- optional_checked (resolve reader A.NameTag) bind ;; Some (B.SToken n b)
| B.SGuest open close bind kind => o <- resolve reader A.NameTag open ;;
    c <- resolve reader A.NameTag close ;; b <- resolve reader A.NameTag bind ;;
    Some (B.SGuest o c b kind)
| B.SOp operation => o <- resolve reader A.OperationTag operation ;; Some (B.SOp o)
end.
Definition remap_operation (reader : Resolver) operation := match operation with
| B.SOpt inner => i <- resolve reader A.SyntaxTag inner ;; Some (B.SOpt i)
| B.SSep name separator source => n <- resolve reader A.NameTag name ;;
    s <- optional_checked (resolve reader A.OperationTag) source ;;
    Some (B.SSep n separator s)
| B.SMap source aliases body => s <- resolve reader A.OperationTag source ;;
    a <- resolve reader A.NamesTag aliases ;; b <- resolve reader A.SyntaxTag body ;;
    Some (B.SMap s a b)
| B.SZip lhs rhs => l <- resolve reader A.NameTag lhs ;;
    r <- resolve reader A.NameTag rhs ;; Some (B.SZip l r)
| B.SOperationOther tag => Some (B.SOperationOther tag)
end.
Definition remap_legacy (reader : Resolver) item := match item with
| A.SourceTerminal text => Some (A.SourceTerminal text)
| A.SourceNonterminal name kind => n <- resolve reader A.NameTag name ;;
    Some (A.SourceNonterminal n kind)
| A.SourceBinder category => c <- resolve reader A.NameTag category ;; Some (A.SourceBinder c)
| A.SourceCollection kind element separator open close => e <- resolve reader A.NameTag element ;;
    Some (A.SourceCollection kind e separator open close)
end.
Definition remap_rule (reader : Resolver) rule items :=
  label <- resolve reader A.NameTag (B.rule_label rule) ;;
  category <- resolve reader A.NameTag (B.rule_category rule) ;;
  context <- optional_checked (resolve reader A.ParamsTag) (B.term_context rule) ;;
  syntax <- optional_checked (resolve reader A.SyntaxTag) (B.syntax_pattern rule) ;;
  legacy <- map_checked (remap_legacy reader) items ;;
  Some (A.SourceRule
    {| B.rule_label := label; B.rule_category := category;
       B.term_context := context; B.syntax_pattern := syntax |} legacy).
Definition remap_source (reader : Resolver) source := match source with
| A.SourceName name => Some (A.SourceName name)
| A.SourceNames names => ns <- map_checked (resolve reader A.NameTag) names ;;
    Some (A.SourceNames ns)
| A.SourceTypeNode ty => t <- remap_type reader ty ;; Some (A.SourceTypeNode t)
| A.SourceParamNode param => p <- remap_param reader param ;; Some (A.SourceParamNode p)
| A.SourceParams params => ps <- map_checked (resolve reader A.ParamTag) params ;;
    Some (A.SourceParams ps)
| A.SourceSyntax syntax => ss <- map_checked (remap_syntax reader) syntax ;;
    Some (A.SourceSyntax ss)
| A.SourceOperation operation => o <- remap_operation reader operation ;;
    Some (A.SourceOperation o)
| A.SourceRule rule items => remap_rule reader rule items
end.

Lemma bind_success : forall X Y (value : option X) (next : X -> option Y) result,
  bind value next = Some result -> exists item, value = Some item /\ next item = Some result.
Proof. intros X Y [item|] next result H; cbn in H; [eauto|discriminate]. Qed.
Lemma optional_checked_presence : forall X Y (f : X -> option Y) source result,
  optional_checked f source = Some result ->
  (source = None <-> result = None).
Proof.
  intros X Y f [value|] result H; cbn in H.
  - destruct (f value); cbn in H; [inversion H; split; discriminate|discriminate].
  - inversion H; tauto.
Qed.
Lemma map_checked_length : forall X Y (f : X -> option Y) source result,
  map_checked f source = Some result -> List.length result = List.length source.
Proof.
  intros X Y f source; induction source as [|value rest IH]; intros result H; cbn in H.
  - inversion H; reflexivity.
  - destruct (f value) as [first|] eqn:E; cbn in H; [|discriminate].
    destruct (map_checked f rest) as [tail|] eqn:R; cbn in H; [|discriminate].
    inversion H; cbn; f_equal; eapply IH; reflexivity.
Qed.
Lemma map_checked_index : forall X Y (f : X -> option Y) source result position original,
  map_checked f source = Some result -> nth_error source position = Some original ->
  exists mapped, nth_error result position = Some mapped /\ f original = Some mapped.
Proof.
  intros X Y f source; induction source as [|value rest IH]; intros result position original H E.
  - destruct position; discriminate.
  - cbn in H. destruct (f value) as [first|] eqn:F; cbn in H; [|discriminate].
    destruct (map_checked f rest) as [tail|] eqn:R; cbn in H; [|discriminate].
    inversion H; subst result. destruct position; cbn in E.
    + inversion E; subst original. exists first; split; [reflexivity|exact F].
    + cbn. exact (IH tail position original eq_refl E).
Qed.

Lemma remap_preserves_tag : forall reader source mapped,
  remap_source reader source = Some mapped -> source_tag mapped = source_tag source.
Proof.
  intros reader source mapped H; destruct source; cbn [remap_source] in H;
    repeat match type of H with
    | context [bind ?value ?next] =>
        destruct value eqn:?; cbn [bind] in H; [|discriminate]
    end; try (inversion H; reflexivity).
  unfold remap_rule in H.
  repeat match type of H with
  | context [bind ?value ?next] => destruct value eqn:?; cbn [bind] in H; [|discriminate]
  end. inversion H; reflexivity.
Qed.

(** Concrete first-occurrence equality-class numbering. List position is the
    class number; this models Eq-key lookup + next_class without assuming that
    classes already preserve equality. No spelling is consulted. *)
Fixpoint find_class key keys := match keys with
| [] => None
| first :: rest => if Nat.eqb key first then Some 0 else option_map Datatypes.S (find_class key rest)
end.
Definition intern_class key keys := match find_class key keys with
| Some class => Some (class, keys)
| None => if A.index_fits_u32 (List.length keys)
    then Some (List.length keys, keys ++ [key]) else None end.
Definition assign_name keys source := match source with
| A.SourceName name => answer <- intern_class (A.equality_class name) keys ;;
    let '(class, next) := answer in
    Some (A.SourceName {| A.spelling := A.spelling name; A.equality_class := class |}, next)
| _ => Some (source, keys) end.

Lemma find_class_sound : forall key keys class,
  find_class key keys = Some class -> nth_error keys class = Some key.
Proof.
  intros key keys; induction keys as [|first rest IH]; intros class H; cbn in H; [discriminate|].
  destruct (Nat.eqb key first) eqn:E.
  - apply Nat.eqb_eq in E; subst first; inversion H; reflexivity.
  - destruct (find_class key rest) as [position|] eqn:F; cbn in H; [|discriminate].
    inversion H; subst class; cbn; apply IH; reflexivity.
Qed.
Lemma find_class_absent : forall key keys,
  find_class key keys = None <-> ~ In key keys.
Proof.
  intros key keys; induction keys as [|first rest IH]; cbn; [tauto|].
  destruct (Nat.eqb key first) eqn:E.
  - apply Nat.eqb_eq in E; subst first; split; [discriminate|tauto].
  - apply Nat.eqb_neq in E. destruct (find_class key rest) eqn:F; cbn.
    + split; [discriminate|]. intros N.
      pose proof (@find_class_sound key rest n F) as Read.
      apply nth_error_In in Read. exfalso; apply N; right; exact Read.
    + split.
      * intros _ [Equal|Member]; [congruence|].
        apply (proj1 IH eq_refl); exact Member.
      * intros _; reflexivity.
Qed.
Lemma intern_class_correct : forall key keys class next,
  NoDup keys -> intern_class key keys = Some (class, next) ->
  NoDup next /\ nth_error next class = Some key /\
  exists suffix, next = keys ++ suffix.
Proof.
  intros key keys class next ND H; unfold intern_class in H.
  destruct (find_class key keys) as [old|] eqn:F.
  - inversion H; subst. repeat split; try assumption.
    + apply find_class_sound; exact F.
    + exists []; rewrite app_nil_r; reflexivity.
  - destruct (A.index_fits_u32 (List.length keys)) eqn:Fits; [|discriminate].
    inversion H; subst. split.
    + apply NoDup_app; repeat split; try assumption.
      * constructor; [simpl; tauto|constructor].
      * intros member Hin Hlast. cbn in Hlast; destruct Hlast as [E|[]]; subst member.
        apply find_class_absent in F; contradiction.
    + split.
      * rewrite nth_error_app2 by lia. replace (List.length keys - List.length keys) with 0 by lia.
        reflexivity.
      * eauto.
Qed.

Inductive Mark := Pending | Ready (target : nat).
Definition Memo := A.Edge -> option Mark.
Definition empty_memo : Memo := fun _ => None.
Definition put (memo : Memo) edge mark : Memo :=
  fun query => if edge_eq_dec query edge then Some mark else memo query.
Definition ready_index (memo : Memo) edge := match memo edge with
| Some (Ready target) => Some target | _ => None end.
Inductive Frame := Enter (edge : A.Edge) | Finish (edge : A.Edge) (source : A.SourceNode).
Record State := {
  arena : list A.Node; memo : Memo; classes : list nat;
  work : list Frame; events : list A.SourceNode
}.
Definition state nodes marks keys frames emitted :=
 {| arena := nodes; memo := marks; classes := keys; work := frames; events := emitted |}.
Definition initial roots := state [] empty_memo [] (List.map Enter roots) [].
Inductive Error := MissingSource | WrongSourceTag | Cycle | AdmissionRefused
  | OwnerNotPending | ChildNotReady | ClassOverflow | AppendRefused
  | RootNotReady | ValidationRefused.
Inductive Outcome := Continue (next : State) | Failed (error : Error) (private : State)
  | Complete (nodes : list A.Node) (roots : list nat).
Definition schedule edge source rest :=
  List.map Enter (source_edges source) ++ Finish edge source :: rest.
Definition Admission := State -> A.SourceNode -> nat -> bool.

(** This relation is the finite operational transcription of the loop. Every
    continuation constructor gives the complete next state; failure rules are
    below. The admission callback receives the exact new work length. *)
Inductive Step (graph : SourceGraph) (admit : Admission) (roots : list A.Edge) :
    State -> Outcome -> Prop :=
| StepReuse nodes marks keys emitted edge rest target :
    marks edge = Some (Ready target) ->
    Step graph admit roots (state nodes marks keys (Enter edge :: rest) emitted)
      (Continue (state nodes marks keys rest emitted))
| StepEnter nodes marks keys emitted edge rest source :
    marks edge = None -> lookup_source graph edge = Some source ->
    source_tag source = fst edge ->
    admit (state nodes marks keys (Enter edge :: rest) emitted) source
      (List.length (schedule edge source rest)) = true ->
    Step graph admit roots (state nodes marks keys (Enter edge :: rest) emitted)
      (Continue (state nodes (put marks edge Pending) keys (schedule edge source rest) emitted))
| StepFinish nodes marks keys emitted edge rest source mapped named next_keys next_nodes :
    marks edge = Some Pending ->
    admit (state nodes marks keys (Finish edge source :: rest) emitted) source
      (List.length rest) = true ->
    remap_source (ready_index marks) source = Some mapped ->
    assign_name keys mapped = Some (named, next_keys) ->
    A.append_checked nodes (A.own_node named) = Some next_nodes ->
    Step graph admit roots (state nodes marks keys (Finish edge source :: rest) emitted)
      (Continue (state next_nodes (put marks edge (Ready (List.length nodes))) next_keys rest
        (emitted ++ [named])))
| StepDone nodes marks keys emitted root_ids validated :
    map_checked (ready_index marks) roots = Some root_ids ->
    A.validate nodes = Some validated ->
    Step graph admit roots (state nodes marks keys [] emitted) (Complete nodes root_ids)
| StepCycle nodes marks keys emitted edge rest :
    marks edge = Some Pending ->
    Step graph admit roots (state nodes marks keys (Enter edge :: rest) emitted)
      (Failed Cycle (state nodes marks keys (Enter edge :: rest) emitted))
| StepMissing nodes marks keys emitted edge rest :
    marks edge = None -> lookup_source graph edge = None ->
    Step graph admit roots (state nodes marks keys (Enter edge :: rest) emitted)
      (Failed MissingSource (state nodes marks keys (Enter edge :: rest) emitted))
| StepWrongTag nodes marks keys emitted edge rest source :
    marks edge = None -> lookup_source graph edge = Some source ->
    source_tag source <> fst edge ->
    Step graph admit roots (state nodes marks keys (Enter edge :: rest) emitted)
      (Failed WrongSourceTag (state nodes marks keys (Enter edge :: rest) emitted))
| StepAdmission nodes marks keys emitted edge rest source :
    marks edge = None -> lookup_source graph edge = Some source -> source_tag source = fst edge ->
    admit (state nodes marks keys (Enter edge :: rest) emitted) source
      (List.length (schedule edge source rest)) = false ->
    Step graph admit roots (state nodes marks keys (Enter edge :: rest) emitted)
      (Failed AdmissionRefused (state nodes marks keys (Enter edge :: rest) emitted))
| StepOwner nodes marks keys emitted edge rest source :
    marks edge <> Some Pending ->
    Step graph admit roots (state nodes marks keys (Finish edge source :: rest) emitted)
      (Failed OwnerNotPending (state nodes marks keys (Finish edge source :: rest) emitted))
| StepChild nodes marks keys emitted edge rest source :
    marks edge = Some Pending ->
    admit (state nodes marks keys (Finish edge source :: rest) emitted) source (List.length rest) = true ->
    remap_source (ready_index marks) source = None ->
    Step graph admit roots (state nodes marks keys (Finish edge source :: rest) emitted)
      (Failed ChildNotReady (state nodes marks keys (Finish edge source :: rest) emitted))
| StepClass nodes marks keys emitted edge rest source mapped :
    marks edge = Some Pending ->
    admit (state nodes marks keys (Finish edge source :: rest) emitted) source (List.length rest) = true ->
    remap_source (ready_index marks) source = Some mapped ->
    assign_name keys mapped = None ->
    Step graph admit roots (state nodes marks keys (Finish edge source :: rest) emitted)
      (Failed ClassOverflow (state nodes marks keys (Finish edge source :: rest) emitted))
| StepAppend nodes marks keys emitted edge rest source mapped named next_keys :
    marks edge = Some Pending ->
    admit (state nodes marks keys (Finish edge source :: rest) emitted) source (List.length rest) = true ->
    remap_source (ready_index marks) source = Some mapped ->
    assign_name keys mapped = Some (named, next_keys) ->
    A.append_checked nodes (A.own_node named) = None ->
    Step graph admit roots (state nodes marks keys (Finish edge source :: rest) emitted)
      (Failed AppendRefused (state nodes marks keys (Finish edge source :: rest) emitted))
| StepFinishAdmission nodes marks keys emitted edge rest source :
    marks edge = Some Pending ->
    admit (state nodes marks keys (Finish edge source :: rest) emitted) source (List.length rest) = false ->
    Step graph admit roots (state nodes marks keys (Finish edge source :: rest) emitted)
      (Failed AdmissionRefused (state nodes marks keys (Finish edge source :: rest) emitted))
| StepRoots nodes marks keys emitted :
    map_checked (ready_index marks) roots = None ->
    Step graph admit roots (state nodes marks keys [] emitted)
      (Failed RootNotReady (state nodes marks keys [] emitted))
| StepValidation nodes marks keys emitted root_ids :
    map_checked (ready_index marks) roots = Some root_ids -> A.validate nodes = None ->
    Step graph admit roots (state nodes marks keys [] emitted)
      (Failed ValidationRefused (state nodes marks keys [] emitted)).

Lemma assign_name_preserves_tag : forall keys source named next,
  assign_name keys source = Some (named, next) -> source_tag named = source_tag source.
Proof.
  intros keys source named next H; destruct source; cbn [assign_name] in H;
    try (inversion H; reflexivity).
  destruct (intern_class (A.equality_class name) keys) as [[class values]|] eqn:E;
    cbn [bind] in H; [inversion H; reflexivity|discriminate].
Qed.
Lemma assign_name_preserves_classes : forall keys source named next,
  NoDup keys -> assign_name keys source = Some (named, next) ->
  NoDup next /\ exists suffix, next = keys ++ suffix.
Proof.
  intros keys source named next ND H; destruct source; cbn [assign_name] in H;
    try (inversion H; subst; split; [assumption|exists []; rewrite app_nil_r; reflexivity]).
  destruct (intern_class (A.equality_class name) keys) as [[class values]|] eqn:E;
    cbn [bind] in H; [|discriminate].
  inversion H; subst. destruct (@intern_class_correct _ _ _ _ ND E) as [V [_ Suffix]].
  auto.
Qed.
Definition ReadyTyped (nodes : list A.Node) (marks : Memo) := forall edge target,
  marks edge = Some (Ready target) -> exists node,
  nth_error nodes target = Some node /\ A.node_tag node = fst edge.
Definition ReadyStable (before after : Memo) := forall edge target,
  before edge = Some (Ready target) -> after edge = Some (Ready target).
Definition FramesLaw graph frames := forall edge source,
  In (Finish edge source) frames ->
  lookup_source graph edge = Some source /\ source_tag source = fst edge.
Fixpoint finish_owners frames := match frames with
| [] => [] | Enter _ :: rest => finish_owners rest
| Finish edge _ :: rest => edge :: finish_owners rest end.
Definition PendingLaw marks frames :=
  (forall edge, marks edge = Some Pending <-> In edge (finish_owners frames)) /\
  NoDup (finish_owners frames).
Definition EventLaw st := arena st = List.map A.own_node (events st).
Definition Invariant graph st :=
  A.ValidArena (arena st) /\ EventLaw st /\ ReadyTyped (arena st) (memo st) /\
  NoDup (classes st) /\ FramesLaw graph (work st) /\ PendingLaw (memo st) (work st).

Lemma finish_owners_app : forall lhs rhs,
  finish_owners (lhs ++ rhs) = finish_owners lhs ++ finish_owners rhs.
Proof. induction lhs as [|frame rest IH]; intros rhs; cbn; [reflexivity|destruct frame; cbn; rewrite IH; reflexivity]. Qed.
Lemma enter_frames_have_no_owners : forall edges, finish_owners (List.map Enter edges) = [].
Proof. induction edges; cbn; congruence. Qed.
Lemma scheduled_finish_owners : forall edge source rest,
  finish_owners (schedule edge source rest) = edge :: finish_owners rest.
Proof. intros; unfold schedule; rewrite finish_owners_app, enter_frames_have_no_owners; reflexivity. Qed.
Lemma enter_frames_have_no_source : forall edges edge source,
  ~ In (Finish edge source) (List.map Enter edges).
Proof.
  intros edges edge source H; apply in_map_iff in H; destruct H as [value [E _]]; discriminate.
Qed.
Lemma frames_tail : forall graph frame rest,
  FramesLaw graph (frame :: rest) -> FramesLaw graph rest.
Proof. intros graph frame rest Law edge source H; apply Law; right; exact H. Qed.
Lemma frames_schedule : forall graph edge source rest,
  FramesLaw graph rest -> lookup_source graph edge = Some source -> source_tag source = fst edge ->
  FramesLaw graph (schedule edge source rest).
Proof.
  intros graph edge source rest Law Read Tag query node H; unfold schedule in H.
  apply in_app_or in H; destruct H as [H|H].
  - exfalso; eapply enter_frames_have_no_source; exact H.
  - destruct H as [E|H]; [inversion E; subst; auto|apply Law; exact H].
Qed.
Lemma pending_enter : forall marks edge source rest,
  marks edge = None -> PendingLaw marks (Enter edge :: rest) ->
  PendingLaw (put marks edge Pending) (schedule edge source rest).
Proof.
  intros marks edge source rest Empty [Law ND]; cbn in Law, ND.
  unfold PendingLaw; rewrite scheduled_finish_owners; split.
  - intros query; unfold put; destruct (edge_eq_dec query edge) as [E|E].
    + subst query; cbn; tauto.
    + cbn; rewrite Law; split; intros H; [right; exact H|destruct H; congruence].
  - constructor; [|exact ND]. intros H; apply Law in H; rewrite Empty in H; discriminate.
Qed.
Lemma pending_finish : forall marks edge source rest target,
  PendingLaw marks (Finish edge source :: rest) ->
  PendingLaw (put marks edge (Ready target)) rest.
Proof.
  intros marks edge source rest target [Law ND]; cbn in Law, ND.
  inversion ND as [|head tail Absent Tail]; subst.
  split; [|exact Tail]. intros query; unfold put; destruct (edge_eq_dec query edge) as [E|E].
  - subst query; split; [discriminate|intros H; exfalso; apply Absent; exact H].
  - rewrite Law; cbn; split; intros H; [destruct H; congruence|right; exact H].
Qed.
Lemma put_pending_ready_typed : forall nodes marks edge,
  ReadyTyped nodes marks -> ReadyTyped nodes (put marks edge Pending).
Proof.
  intros nodes marks edge Law query target H; unfold put in H.
  destruct (edge_eq_dec query edge); [discriminate|apply Law; exact H].
Qed.
Lemma put_ready_typed : forall nodes marks edge node next,
  ReadyTyped nodes marks -> A.append_checked nodes node = Some next ->
  A.node_tag node = fst edge ->
  ReadyTyped next (put marks edge (Ready (List.length nodes))).
Proof.
  intros nodes marks edge node next Law Append Tag query target H; unfold put in H.
  destruct (edge_eq_dec query edge) as [E|E].
  - subst query; inversion H; subst target.
    apply A.append_checked_exact in Append; destruct Append as [-> _].
    exists node; split; [|exact Tag].
    rewrite nth_error_app2 by lia. replace (List.length nodes - List.length nodes) with 0 by lia.
    reflexivity.
  - destruct (Law query target H) as [old [Read OldTag]].
    apply A.append_checked_exact in Append; destruct Append as [-> _].
    exists old; split; [apply A.lookup_append_stable; exact Read|exact OldTag].
Qed.
Lemma put_preserves_ready : forall marks edge replacement,
  (marks edge = None \/ marks edge = Some Pending) -> ReadyStable marks (put marks edge replacement).
Proof.
  intros marks edge replacement Old query target H; unfold put.
  destruct (edge_eq_dec query edge) as [E|E]; [|exact H].
  subst query; destruct Old; congruence.
Qed.

Theorem initial_invariant : forall graph roots, Invariant graph (initial roots).
Proof.
  intros graph roots; unfold Invariant, initial; cbn.
  split; [constructor|].
  split; [reflexivity|].
  split; [intros edge target H; discriminate|].
  split; [constructor|].
  split.
  - intros edge source H; exfalso; eapply enter_frames_have_no_source; exact H.
  - split.
    + intros edge; rewrite enter_frames_have_no_owners; cbn; split; [discriminate|tauto].
    + rewrite enter_frames_have_no_owners; constructor.
Qed.
Theorem step_preserves_valid_arena : forall graph admit roots before after,
  Step graph admit roots before (Continue after) -> A.ValidArena (arena before) ->
  A.ValidArena (arena after).
Proof.
  intros graph admit roots before after Transition Valid; inversion Transition; subst; cbn in *;
    try assumption. eapply A.append_checked_preserves_validity; eauto.
Qed.
Theorem step_preserves_event_order : forall graph admit roots before after,
  Step graph admit roots before (Continue after) -> EventLaw before -> EventLaw after.
Proof.
  intros graph admit roots before after Transition Law; inversion Transition; subst;
    unfold EventLaw in *; cbn in *; try assumption.
  match goal with H : A.append_checked _ _ = Some _ |- _ =>
    apply A.append_checked_exact in H; destruct H as [-> _] end.
  rewrite map_app; cbn; rewrite Law; reflexivity.
Qed.
Theorem step_preserves_ready : forall graph admit roots before after,
  Step graph admit roots before (Continue after) -> ReadyStable (memo before) (memo after).
Proof.
  intros graph admit roots before after Transition; inversion Transition; subst; cbn.
  - intros query position Hread; exact Hread.
  - apply put_preserves_ready; auto.
  - apply put_preserves_ready; auto.
Qed.
Theorem step_preserves_frames : forall graph admit roots before after,
  Step graph admit roots before (Continue after) -> FramesLaw graph (work before) ->
  FramesLaw graph (work after).
Proof.
  intros graph admit roots before after Transition Law; inversion Transition; subst; cbn in *.
  - eapply frames_tail; exact Law.
  - apply frames_schedule; [eapply frames_tail; exact Law|assumption|assumption].
  - eapply frames_tail; exact Law.
Qed.
Theorem step_preserves_pending : forall graph admit roots before after,
  Step graph admit roots before (Continue after) -> PendingLaw (memo before) (work before) ->
  PendingLaw (memo after) (work after).
Proof.
  intros graph admit roots before after Transition Law; inversion Transition; subst; cbn in *.
  - exact Law.
  - apply pending_enter; assumption.
  - eapply pending_finish; exact Law.
Qed.
Theorem step_preserves_classes : forall graph admit roots before after,
  Step graph admit roots before (Continue after) -> NoDup (classes before) ->
  NoDup (classes after) /\ exists suffix, classes after = classes before ++ suffix.
Proof.
  intros graph admit roots before after Transition ND; inversion Transition; subst; cbn in *;
    try (split; [assumption|exists []; rewrite app_nil_r; reflexivity]).
  eapply assign_name_preserves_classes; eauto.
Qed.
Theorem step_preserves_ready_types : forall graph admit roots before after,
  Step graph admit roots before (Continue after) -> ReadyTyped (arena before) (memo before) ->
  FramesLaw graph (work before) -> ReadyTyped (arena after) (memo after).
Proof.
  intros graph admit roots before after Transition ReadyLaw FrameLaw.
  inversion Transition; subst; cbn in *.
  - exact ReadyLaw.
  - apply put_pending_ready_typed; exact ReadyLaw.
  - eapply put_ready_typed; [exact ReadyLaw|eassumption|].
    change (source_tag named = fst edge).
    transitivity (source_tag mapped); [eapply assign_name_preserves_tag; eassumption|].
    transitivity (source_tag source); [eapply remap_preserves_tag; eassumption|].
    apply (proj2 (FrameLaw edge source (or_introl eq_refl))).
Qed.
Theorem step_preserves_invariant : forall graph admit roots before after,
  Step graph admit roots before (Continue after) -> Invariant graph before -> Invariant graph after.
Proof.
  intros graph admit roots before after StepLaw [Valid [Events [Ready [Classes [Frames Pending]]]]].
  unfold Invariant.
  split; [eapply step_preserves_valid_arena; eauto|].
  split; [eapply step_preserves_event_order; eauto|].
  split; [eapply step_preserves_ready_types; eauto|].
  split; [exact (proj1 (@step_preserves_classes graph admit roots before after StepLaw Classes))|].
  split; [eapply step_preserves_frames; eauto|].
  eapply step_preserves_pending; eauto.
Qed.

Inductive FiniteRun graph admit roots : State -> nat -> State -> Prop :=
| RunZero st : FiniteRun graph admit roots st 0 st
| RunNext before middle after count :
    Step graph admit roots before (Continue middle) ->
    FiniteRun graph admit roots middle count after ->
    FiniteRun graph admit roots before (Datatypes.S count) after.
Theorem finite_run_preserves_invariant : forall graph admit roots before count after,
  FiniteRun graph admit roots before count after -> Invariant graph before -> Invariant graph after.
Proof.
  intros graph admit roots before count after Run; induction Run; intros Inv; [exact Inv|].
  apply IHRun; eapply step_preserves_invariant; eauto.
Qed.
Theorem finite_run_ready_identity_stable : forall graph admit roots before count after,
  FiniteRun graph admit roots before count after -> ReadyStable (memo before) (memo after).
Proof.
  intros graph admit roots before count after Run; induction Run.
  - intros edge target H; exact H.
  - intros edge target Read; apply IHRun.
    eapply (@step_preserves_ready graph admit roots before middle); eauto.
Qed.
Theorem finite_capture_postorder_and_typed_store : forall graph admit roots count after,
  FiniteRun graph admit roots (initial roots) count after ->
  A.ValidArena (arena after) /\ arena after = List.map A.own_node (events after) /\
  ReadyTyped (arena after) (memo after) /\ PendingLaw (memo after) (work after).
Proof.
  intros graph admit roots count after Run.
  pose proof (@finite_run_preserves_invariant graph admit roots _ _ _ Run
    (initial_invariant graph roots)) as [Valid [Events [Ready [_ [_ Pending]]]]].
  auto.
Qed.

Theorem returned_roots_keep_order_and_multiplicity : forall graph admit roots st nodes ids,
  Step graph admit roots st (Complete nodes ids) ->
  List.length ids = List.length roots /\
  forall position edge, nth_error roots position = Some edge ->
    exists target, nth_error ids position = Some target /\ memo st edge = Some (Ready target).
Proof.
  intros graph admit roots st nodes ids Transition; inversion Transition; subst; cbn; split.
  - eapply map_checked_length; eassumption.
  - intros position edge E.
    match goal with R : map_checked _ _ = Some _ |- _ =>
      destruct (@map_checked_index _ _ _ _ _ _ _ R E) as [target [Read Found]] end.
    exists target; split; [exact Read|].
    unfold ready_index in Found; destruct (marks edge) as [[|value]|] eqn:M;
      try discriminate. inversion Found; subst; reflexivity.
Qed.

Inductive Published := PublishedArena (nodes : list A.Node) (roots : list nat) | Rejected (error : Error).
Definition publish outcome := match outcome with
| Continue _ => None | Failed error _ => Some (Rejected error)
| Complete nodes roots => Some (PublishedArena nodes roots) end.
Theorem every_failure_discards_private_state : forall error private,
  publish (Failed error private) = Some (Rejected error).
Proof. reflexivity. Qed.
Theorem no_failed_capture_publishes_an_arena : forall error private nodes roots,
  publish (Failed error private) <> Some (PublishedArena nodes roots).
Proof. discriminate. Qed.
Theorem shared_completed_node_needs_no_source_read : forall graph admit roots nodes marks keys emitted edge rest target,
  marks edge = Some (Ready target) ->
  Step graph admit roots (state nodes marks keys (Enter edge :: rest) emitted)
    (Continue (state nodes marks keys rest emitted)).
Proof. intros; eapply StepReuse; eassumption. Qed.
Theorem pending_owner_is_an_active_finish : forall marks frames edge,
  PendingLaw marks frames -> (marks edge = Some Pending <-> In edge (finish_owners frames)).
Proof. intros marks frames edge [Law _]; apply Law. Qed.

(** Erasing ONLY references yields a complete nonreference payload signature.
    This uses the existing SourceNode vocabulary: no second semantic AST.
    The name key is erased here because its separate class-numbering theorem
    below proves the equality observation; its spelling is retained. *)
Definition param_payload param := match param with
| T.SSimple _ _ => T.SSimple 0 0 | T.SGuardBody _ => T.SGuardBody 0
| T.SAbstraction _ _ _ => T.SAbstraction 0 0 0
| T.SMultiAbstraction _ _ _ => T.SMultiAbstraction 0 0 0
| T.SOptional _ => T.SOptional 0 end.
Definition type_payload ty := match ty with
| A.ExistingType ty => A.ExistingType (match ty with
  | B.SBase _ => B.SBase 0 | B.SCollection kind _ => B.SCollection kind 0
  | B.SMapType _ _ => B.SMapType 0 0 | B.SArrow _ _ => B.SArrow 0 0
  | B.STypeOther tag => B.STypeOther tag end)
| A.RuntimeKeyedPathMap _ _ => A.RuntimeKeyedPathMap 0 0 end.
Definition syntax_payload syntax := match syntax with
| B.SLiteral text => B.SLiteral text | B.SParam _ => B.SParam 0
| B.SToken _ bind => B.SToken 0 (option_map (fun _ => 0) bind)
| B.SGuest _ _ _ kind => B.SGuest 0 0 0 kind | B.SOp _ => B.SOp 0 end.
Definition operation_payload operation := match operation with
| B.SOpt _ => B.SOpt 0
| B.SSep _ separator source => B.SSep 0 separator (option_map (fun _ => 0) source)
| B.SMap _ _ _ => B.SMap 0 0 0 | B.SZip _ _ => B.SZip 0 0
| B.SOperationOther tag => B.SOperationOther tag end.
Definition legacy_payload item := match item with
| A.SourceTerminal text => A.SourceTerminal text
| A.SourceNonterminal _ kind => A.SourceNonterminal 0 kind
| A.SourceBinder _ => A.SourceBinder 0
| A.SourceCollection kind _ separator open close => A.SourceCollection kind 0 separator open close end.
Definition source_payload source := match source with
| A.SourceName name => A.SourceName {| A.spelling := A.spelling name; A.equality_class := 0 |}
| A.SourceNames names => A.SourceNames (repeat 0 (List.length names))
| A.SourceTypeNode ty => A.SourceTypeNode (type_payload ty)
| A.SourceParamNode param => A.SourceParamNode (param_payload param)
| A.SourceParams params => A.SourceParams (repeat 0 (List.length params))
| A.SourceSyntax syntax => A.SourceSyntax (List.map syntax_payload syntax)
| A.SourceOperation operation => A.SourceOperation (operation_payload operation)
| A.SourceRule rule items => A.SourceRule
    {| B.rule_label := 0; B.rule_category := 0;
       B.term_context := option_map (fun _ => 0) (B.term_context rule);
       B.syntax_pattern := option_map (fun _ => 0) (B.syntax_pattern rule) |}
    (List.map legacy_payload items) end.

Lemma map_checked_payload : forall X Y P (f : X -> option Y) (sx : X -> P) (sy : Y -> P),
  (forall x y, f x = Some y -> sy y = sx x) -> forall source mapped,
  map_checked f source = Some mapped -> List.map sy mapped = List.map sx source.
Proof.
  intros X Y P f sx sy Law source; induction source as [|first rest IH]; intros mapped H; cbn in H.
  - inversion H; reflexivity.
  - destruct (f first) as [head|] eqn:F; cbn in H; [|discriminate].
    destruct (map_checked f rest) as [tail|] eqn:R; cbn in H; [|discriminate].
    inversion H; subst mapped; cbn. rewrite (Law _ _ F), (IH tail eq_refl); reflexivity.
Qed.
Lemma optional_checked_payload : forall X Y (f : X -> option Y) source mapped,
  optional_checked f source = Some mapped ->
  option_map (fun _ => 0) mapped = option_map (fun _ => 0) source.
Proof.
  intros X Y f [value|] mapped H; cbn in H.
  - destruct (f value); cbn in H; [inversion H; reflexivity|discriminate].
  - inversion H; reflexivity.
Qed.

Ltac resolve_option_branches H :=
  cbn [bind] in H;
  repeat match type of H with
  | context [resolve ?reader ?tag ?identity] =>
      destruct (resolve reader tag identity) eqn:?; cbn [bind] in H; [|discriminate]
  | context [bind ?value ?next] =>
      destruct value eqn:?; cbn [bind] in H; [|discriminate]
  end.
Lemma remap_param_payload : forall reader source mapped,
  remap_param reader source = Some mapped -> param_payload mapped = param_payload source.
Proof.
  intros reader source mapped H; destruct source; cbn [remap_param] in H;
    resolve_option_branches H; inversion H; reflexivity.
Qed.
Lemma remap_type_payload : forall reader source mapped,
  remap_type reader source = Some mapped -> type_payload mapped = type_payload source.
Proof.
  intros reader [ty|key value] mapped H; [destruct ty|]; cbn [remap_type] in H;
    resolve_option_branches H; inversion H; reflexivity.
Qed.
Lemma remap_syntax_payload : forall reader source mapped,
  remap_syntax reader source = Some mapped -> syntax_payload mapped = syntax_payload source.
Proof.
  intros reader source mapped H;
    destruct source as [text|name|name binding|open close binding kind|operation]; try destruct binding;
    cbn [remap_syntax optional_checked] in H;
    resolve_option_branches H; inversion H; reflexivity.
Qed.
Lemma remap_operation_payload : forall reader source mapped,
  remap_operation reader source = Some mapped -> operation_payload mapped = operation_payload source.
Proof.
  intros reader source mapped H;
    destruct source as [inner|name separator child|src aliases body|lhs rhs|tag]; try destruct child;
    cbn [remap_operation optional_checked] in H;
    resolve_option_branches H; inversion H; reflexivity.
Qed.
Lemma remap_legacy_payload : forall reader source mapped,
  remap_legacy reader source = Some mapped -> legacy_payload mapped = legacy_payload source.
Proof.
  intros reader source mapped H; destruct source; cbn [remap_legacy] in H;
    resolve_option_branches H; inversion H; reflexivity.
Qed.
Lemma remap_rule_payload : forall reader rule items mapped,
  remap_rule reader rule items = Some mapped ->
  source_payload mapped = source_payload (A.SourceRule rule items).
Proof.
  intros reader rule items mapped H; unfold remap_rule in H.
  destruct (resolve reader A.NameTag (B.rule_label rule)) eqn:L; cbn [bind] in H; [|discriminate].
  destruct (resolve reader A.NameTag (B.rule_category rule)) eqn:C; cbn [bind] in H; [|discriminate].
  destruct (optional_checked (resolve reader A.ParamsTag) (B.term_context rule)) as [tc|] eqn:TC;
    cbn [bind] in H; [|discriminate].
  destruct (optional_checked (resolve reader A.SyntaxTag) (B.syntax_pattern rule)) as [sp|] eqn:SP;
    cbn [bind] in H; [|discriminate].
  destruct (map_checked (remap_legacy reader) items) as [legacy|] eqn:Items;
    cbn [bind] in H; [|discriminate].
  inversion H; subst mapped; cbn [source_payload B.term_context B.syntax_pattern].
  rewrite (@optional_checked_payload _ _ _ _ _ TC), (@optional_checked_payload _ _ _ _ _ SP).
  rewrite (@map_checked_payload _ _ _ _ _ _ (remap_legacy_payload reader) _ _ Items); reflexivity.
Qed.
Theorem remap_preserves_every_nonreference_payload : forall reader source mapped,
  remap_source reader source = Some mapped -> source_payload mapped = source_payload source.
Proof.
  intros reader source mapped H; destruct source; cbn [remap_source] in H.
  - inversion H; reflexivity.
  - destruct (map_checked (resolve reader A.NameTag) names) eqn:E; cbn [bind] in H; [|discriminate].
    inversion H; subst mapped; cbn [source_payload]. rewrite (@map_checked_length _ _ _ _ _ E); reflexivity.
  - destruct (remap_type reader ty) eqn:E; cbn [bind] in H; [|discriminate].
    inversion H; subst mapped; cbn [source_payload]; rewrite (@remap_type_payload _ _ _ E); reflexivity.
  - destruct (remap_param reader param) eqn:E; cbn [bind] in H; [|discriminate].
    inversion H; subst mapped; cbn [source_payload]; rewrite (@remap_param_payload _ _ _ E); reflexivity.
  - destruct (map_checked (resolve reader A.ParamTag) params) eqn:E; cbn [bind] in H; [|discriminate].
    inversion H; subst mapped; cbn [source_payload]. rewrite (@map_checked_length _ _ _ _ _ E); reflexivity.
  - destruct (map_checked (remap_syntax reader) syntax) eqn:E; cbn [bind] in H; [|discriminate].
    inversion H; subst mapped; cbn [source_payload].
    rewrite (@map_checked_payload _ _ _ _ _ _ (remap_syntax_payload reader) _ _ E); reflexivity.
  - destruct (remap_operation reader operation) eqn:E; cbn [bind] in H; [|discriminate].
    inversion H; subst mapped; cbn [source_payload]; rewrite (@remap_operation_payload _ _ _ E); reflexivity.
  - eapply remap_rule_payload; exact H.
Qed.
Theorem name_assignment_preserves_every_nonreference_payload : forall keys source named next,
  assign_name keys source = Some (named, next) -> source_payload named = source_payload source.
Proof.
  intros keys source named next H; destruct source; cbn [assign_name] in H;
    try (inversion H; reflexivity).
  destruct (intern_class (A.equality_class name) keys) as [[class values]|];
    cbn [bind] in H; [inversion H; reflexivity|discriminate].
Qed.

Lemma nodup_nth_unique : forall (keys : list nat) lhs rhs key,
  NoDup keys -> nth_error keys lhs = Some key -> nth_error keys rhs = Some key -> lhs = rhs.
Proof.
  intros keys; induction keys as [|first rest IH]; intros lhs rhs key ND L R.
  - destruct lhs; discriminate.
  - inversion ND as [|head tail Absent Tail]; subst.
    destruct lhs, rhs; cbn in L, R.
    + reflexivity.
    + inversion L; subst key. exfalso; apply Absent; eapply nth_error_In; exact R.
    + inversion R; subst key. exfalso; apply Absent; eapply nth_error_In; exact L.
    + f_equal; eapply IH; eauto.
Qed.
Theorem numbered_classes_equal_iff_original_keys_equal : forall (keys : list nat) lhs rhs left_key right_key,
  NoDup keys -> nth_error keys lhs = Some left_key -> nth_error keys rhs = Some right_key ->
  (lhs = rhs <-> left_key = right_key).
Proof.
  intros keys lhs rhs left_key right_key ND L R; split.
  - intros E; subst rhs; congruence.
  - intros E; subst right_key; eapply nodup_nth_unique; eauto.
Qed.
Theorem previous_name_class_meaning_is_stable : forall graph admit roots before after class key,
  Step graph admit roots before (Continue after) -> NoDup (classes before) ->
  nth_error (classes before) class = Some key -> nth_error (classes after) class = Some key.
Proof.
  intros graph admit roots before after class key StepLaw ND Read.
  destruct (@step_preserves_classes graph admit roots before after StepLaw ND) as [_ [suffix E]].
  rewrite E, nth_error_app1; [exact Read|].
  apply nth_error_Some; rewrite Read; discriminate.
Qed.

(** The only external observations are source lookup and deterministic
    admission. Memo/class/field resolution is pure private bookkeeping. *)
Inductive Callback := ReadSource (edge : A.Edge)
  | AdmitEnter (edge : A.Edge) (scheduled : nat) (accepted : bool)
  | AdmitFinish (edge : A.Edge) (remaining : nat) (accepted : bool).
Definition callback_trace graph admit st := match work st with
| [] => []
| Enter edge :: rest => match memo st edge with
  | Some _ => []
  | None => ReadSource edge :: match lookup_source graph edge with
    | None => []
    | Some source => if A.tag_eq_dec (source_tag source) (fst edge) then
        [AdmitEnter edge (List.length (schedule edge source rest))
          (admit st source (List.length (schedule edge source rest)))] else [] end
  end
| Finish edge source :: rest => match memo st edge with
  | Some Pending => [AdmitFinish edge (List.length rest) (admit st source (List.length rest))]
  | _ => [] end
end.
Theorem ready_reuse_observes_no_source_or_admission : forall graph admit nodes marks keys emitted edge rest target,
  marks edge = Some (Ready target) ->
  callback_trace graph admit (state nodes marks keys (Enter edge :: rest) emitted) = [].
Proof. intros; cbn [callback_trace state work memo]; rewrite H; reflexivity. Qed.
Theorem enter_callback_order_before_pending : forall graph admit nodes marks keys emitted edge rest source accepted,
  marks edge = None -> lookup_source graph edge = Some source -> source_tag source = fst edge ->
  admit (state nodes marks keys (Enter edge :: rest) emitted) source
    (List.length (schedule edge source rest)) = accepted ->
  callback_trace graph admit (state nodes marks keys (Enter edge :: rest) emitted) =
    [ReadSource edge; AdmitEnter edge (List.length (schedule edge source rest)) accepted].
Proof.
  intros graph admit nodes marks keys emitted edge rest source accepted M Read Tag Allowed.
  cbn [callback_trace state work memo]; rewrite M, Read.
  destruct (A.tag_eq_dec (source_tag source) (fst edge)); [rewrite Allowed; reflexivity|contradiction].
Qed.
Theorem finish_admission_before_name_insertion_and_append : forall graph admit nodes marks keys emitted edge rest source accepted,
  marks edge = Some Pending ->
  admit (state nodes marks keys (Finish edge source :: rest) emitted) source (List.length rest) = accepted ->
  callback_trace graph admit (state nodes marks keys (Finish edge source :: rest) emitted) =
    [AdmitFinish edge (List.length rest) accepted].
Proof. intros; cbn [callback_trace state work memo]; rewrite H, H0; reflexivity. Qed.
Theorem rejected_enter_admission_has_no_private_mutation : forall graph admit roots nodes marks keys emitted edge rest source,
  marks edge = None -> lookup_source graph edge = Some source -> source_tag source = fst edge ->
  admit (state nodes marks keys (Enter edge :: rest) emitted) source
    (List.length (schedule edge source rest)) = false ->
  Step graph admit roots (state nodes marks keys (Enter edge :: rest) emitted)
    (Failed AdmissionRefused (state nodes marks keys (Enter edge :: rest) emitted)).
Proof. intros; eapply StepAdmission; eassumption. Qed.

Print Assumptions remap_preserves_tag.
Print Assumptions intern_class_correct.
Print Assumptions initial_invariant.
Print Assumptions step_preserves_invariant.
Print Assumptions finite_run_ready_identity_stable.
Print Assumptions finite_capture_postorder_and_typed_store.
Print Assumptions returned_roots_keep_order_and_multiplicity.
Print Assumptions no_failed_capture_publishes_an_arena.
Print Assumptions pending_owner_is_an_active_finish.
Print Assumptions remap_preserves_every_nonreference_payload.
Print Assumptions numbered_classes_equal_iff_original_keys_equal.
Print Assumptions previous_name_class_meaning_is_stable.
Print Assumptions enter_callback_order_before_pending.
Print Assumptions finish_admission_before_name_insertion_and_append.
Print Assumptions rejected_enter_admission_has_no_private_mutation.

End AuthoredRuleCaptureProjection.
