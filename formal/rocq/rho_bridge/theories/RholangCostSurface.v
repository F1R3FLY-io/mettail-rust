(** * Cost-accounted Rholang surface-to-wire obligations

    This model isolates the interface shared by the legacy syntax adapter and
    the MeTTaIL [language!] adapter.  Each adapter resolves a ground name to a
    bound level or canonical ground bytes and lowers a quoted process to a
    canonical [Par] before emitting the structural signature events modeled
    here.  The shared builder must not perform binder lookup or parse source.

    [direct_signature] is the tree semantics of fundable signatures.  [code]
    describes the postorder events consumed by an explicit-stack builder, and
    [run] is that builder.  A transfer capability is deliberately excluded
    from fundable signatures: it is legal only as the outer annotation on a
    signed receive, where [rewrite_signed] handles it locally.  The theorems
    establish value correspondence, rejection, and the no-synthetic-COMM
    property.  Source correspondence, byte canonicalization, and resource
    admission are separate Rust/property-test obligations; this file does not
    claim to prove those implementation details.
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Module RholangCostSurface.

(** A resolved ground principal or quote is represented by an opaque natural
    number.  Adapters must supply the exact canonical wire image for that
    number; the shared builder never changes its identity. [NameQuote] is a
    Rholang quoted name used as a ground principal. It is deliberately distinct
    from the cryptographic section [Quote], written [#P] in the surface. *)
Inductive Signature : Type :=
| Ground (principal : nat)
| NameQuote (process : nat)
| Quote (process : nat)
| Compound (lhs rhs : Signature)
| Transfer (source target : Signature).

Inductive WireSignature : Type :=
| WGround (principal : nat)
| WName (process : nat)
| WQuote (process : nat)
| WCompound (lhs rhs : WireSignature).

Fixpoint direct_signature (sig : Signature) : option WireSignature :=
  match sig with
  | Ground principal => Some (WGround principal)
  | NameQuote process => Some (WName process)
  | Quote process => Some (WQuote process)
  | Compound lhs rhs =>
      match direct_signature lhs, direct_signature rhs with
      | Some l, Some r => Some (WCompound l r)
      | _, _ => None
      end
  | Transfer _ _ => None
  end.

(** An event stream is postorder.  [BuildCompound] consumes the right and then
    the left stack values, restoring the authored left-to-right operand order. *)
Inductive Event : Type :=
| PushGround (principal : nat)
| PushName (process : nat)
| PushQuote (process : nat)
| BuildCompound.

Fixpoint code (sig : Signature) : option (list Event) :=
  match sig with
  | Ground principal => Some [PushGround principal]
  | NameQuote process => Some [PushName process]
  | Quote process => Some [PushQuote process]
  | Compound lhs rhs =>
      match code lhs, code rhs with
      | Some l, Some r => Some (l ++ r ++ [BuildCompound])
      | _, _ => None
      end
  | Transfer _ _ => None
  end.

Definition step (event : Event) (stack : list WireSignature)
    : option (list WireSignature) :=
  match event with
  | PushGround principal => Some (WGround principal :: stack)
  | PushName process => Some (WName process :: stack)
  | PushQuote process => Some (WQuote process :: stack)
  | BuildCompound =>
      match stack with
      | rhs :: lhs :: rest => Some (WCompound lhs rhs :: rest)
      | _ => None
      end
  end.

Fixpoint run (events : list Event) (stack : list WireSignature)
    : option (list WireSignature) :=
  match events with
  | [] => Some stack
  | event :: rest =>
      match step event stack with
      | Some next => run rest next
      | None => None
      end
  end.

Lemma run_app : forall first second stack,
  run (first ++ second) stack =
    match run first stack with
    | Some next => run second next
    | None => None
    end.
Proof.
  induction first as [|event first IH]; intros second stack; cbn.
  - reflexivity.
  - destruct (step event stack) as [next|]; cbn; auto.
Qed.

Theorem fundable_code_is_exact : forall sig value events,
  direct_signature sig = Some value ->
  code sig = Some events ->
  forall stack, run events stack = Some (value :: stack).
Proof.
  induction sig as [principal|process|process|lhs IHl rhs IHr|source IHs target IHt];
    intros value events Hvalue Hcode stack; cbn in Hvalue, Hcode.
  - inversion Hvalue; inversion Hcode; subst; reflexivity.
  - inversion Hvalue; inversion Hcode; subst; reflexivity.
  - inversion Hvalue; inversion Hcode; subst; reflexivity.
  - destruct (direct_signature lhs) as [left_value|] eqn:Hleft;
      try discriminate.
    destruct (direct_signature rhs) as [right_value|] eqn:Hright;
      try discriminate.
    destruct (code lhs) as [left_code|] eqn:Cleft; try discriminate.
    destruct (code rhs) as [right_code|] eqn:Cright; try discriminate.
    inversion Hvalue; inversion Hcode; subst; clear Hvalue Hcode.
    rewrite run_app.
    rewrite (IHl left_value left_code eq_refl eq_refl stack).
    rewrite run_app.
    rewrite (IHr right_value right_code eq_refl eq_refl
      (left_value :: stack)).
    reflexivity.
  - discriminate.
Qed.

Theorem transfer_is_not_fundable : forall source target,
  direct_signature (Transfer source target) = None /\
  code (Transfer source target) = None.
Proof. intros; split; reflexivity. Qed.

Theorem compound_events_preserve_authored_order : forall lhs rhs,
  run [PushGround lhs; PushGround rhs; BuildCompound] [] =
    Some [WCompound (WGround lhs) (WGround rhs)].
Proof. reflexivity. Qed.

Theorem quoted_name_and_cryptographic_section_remain_distinct : forall process,
  direct_signature (NameQuote process) = Some (WName process) /\
  direct_signature (Quote process) = Some (WQuote process) /\
  WName process <> WQuote process.
Proof. intros; repeat split; try reflexivity; discriminate. Qed.
Print Assumptions quoted_name_and_cryptographic_section_remain_distinct.

(** Appendix C permits a parallel tail beneath one cons cell, for example
    [s :: (left | right)].  The prefix belongs to the whole tail: copying it
    into both branches would create a second authority occurrence.  The
    executable machine below builds the authored tree from a postorder event
    stream with an explicit value stack.  In particular, [BuildStackCons]
    consumes one tail tree and creates exactly one prefix node; no distribution
    over [StackParallel] is present.  The recursive [stack_events] function is
    a mathematical specification of the event stream, not the runtime
    traversal, which schedules child visits on a heap worklist. *)
Inductive StackSyntax : Type :=
| StackEmpty
| StackCons (head : Signature) (tail : StackSyntax)
| StackParallel (lhs rhs : StackSyntax).

Inductive StackTree : Type :=
| TreeEmpty
| TreeCons (head : Signature) (tail : StackTree)
| TreeParallel (lhs rhs : StackTree).

Fixpoint direct_stack (surface : StackSyntax) : StackTree :=
  match surface with
  | StackEmpty => TreeEmpty
  | StackCons head tail => TreeCons head (direct_stack tail)
  | StackParallel lhs rhs =>
      TreeParallel (direct_stack lhs) (direct_stack rhs)
  end.

Inductive StackEvent : Type :=
| PushStackEmpty
| BuildStackCons (head : Signature)
| BuildStackParallel.

Fixpoint stack_events (surface : StackSyntax) : list StackEvent :=
  match surface with
  | StackEmpty => [PushStackEmpty]
  | StackCons head tail => stack_events tail ++ [BuildStackCons head]
  | StackParallel lhs rhs =>
      stack_events lhs ++ stack_events rhs ++ [BuildStackParallel]
  end.

Definition stack_step (event : StackEvent) (values : list StackTree)
    : option (list StackTree) :=
  match event, values with
  | PushStackEmpty, _ => Some (TreeEmpty :: values)
  | BuildStackCons head, tail :: rest =>
      Some (TreeCons head tail :: rest)
  | BuildStackParallel, rhs :: lhs :: rest =>
      Some (TreeParallel lhs rhs :: rest)
  | _, _ => None
  end.

Fixpoint run_stack_events (events : list StackEvent)
    (values : list StackTree) : option (list StackTree) :=
  match events with
  | [] => Some values
  | event :: rest =>
      match stack_step event values with
      | Some next => run_stack_events rest next
      | None => None
      end
  end.

Lemma run_stack_events_app : forall first second values,
  run_stack_events (first ++ second) values =
    match run_stack_events first values with
    | Some next => run_stack_events second next
    | None => None
    end.
Proof.
  induction first as [|event first IH]; intros second values; cbn.
  - reflexivity.
  - destruct (stack_step event values) as [next|]; cbn; auto.
Qed.

Theorem stack_events_retain_the_authored_tree : forall surface values,
  run_stack_events (stack_events surface) values =
    Some (direct_stack surface :: values).
Proof.
  induction surface as [|head tail IH|lhs IHl rhs IHr]; intros values; cbn.
  - reflexivity.
  - rewrite run_stack_events_app, IH. reflexivity.
  - rewrite run_stack_events_app, IHl.
    cbn. rewrite run_stack_events_app, IHr. reflexivity.
Qed.

Fixpoint stack_cons_count (surface : StackSyntax) : nat :=
  match surface with
  | StackEmpty => 0
  | StackCons _ tail => S (stack_cons_count tail)
  | StackParallel lhs rhs =>
      stack_cons_count lhs + stack_cons_count rhs
  end.

Fixpoint event_cons_count (events : list StackEvent) : nat :=
  match events with
  | [] => 0
  | BuildStackCons _ :: rest => S (event_cons_count rest)
  | _ :: rest => event_cons_count rest
  end.

Lemma event_cons_count_app : forall lhs rhs,
  event_cons_count (lhs ++ rhs) =
    event_cons_count lhs + event_cons_count rhs.
Proof.
  induction lhs as [|event lhs IH]; intros rhs; cbn.
  - reflexivity.
  - destruct event; cbn; rewrite IH; lia.
Qed.

Theorem stack_events_never_duplicate_a_cell : forall surface,
  event_cons_count (stack_events surface) = stack_cons_count surface.
Proof.
  induction surface as [|head tail IH|lhs IHl rhs IHr]; cbn.
  - reflexivity.
  - rewrite event_cons_count_app, IH. cbn. lia.
  - rewrite event_cons_count_app, event_cons_count_app, IHl, IHr.
    cbn. lia.
Qed.

Corollary parallel_tail_has_one_shared_prefix : forall sig lhs rhs,
  run_stack_events
    (stack_events (StackCons sig (StackParallel lhs rhs))) [] =
    Some [TreeCons sig
      (TreeParallel (direct_stack lhs) (direct_stack rhs))] /\
  event_cons_count
    (stack_events (StackCons sig (StackParallel lhs rhs))) =
    S (stack_cons_count lhs + stack_cons_count rhs).
Proof.
  intros. split.
  - apply stack_events_retain_the_authored_tree.
  - apply stack_events_never_duplicate_a_cell.
Qed.
Print Assumptions parallel_tail_has_one_shared_prefix.

(** The concrete parser distinguishes a full stack from a non-parallel chain.
    A chain cannot consume a bare [|]: only [ChainGroup] can carry a parallel
    stack beneath a cons.  [StackLift] is the generated typed coercion from a
    chain to a stack, not a new authority cell.  Erasure discards that coercion
    and grouping, retaining exactly the authored Empty/Cons/Parallel tree. *)
Inductive FactoredStack : Type :=
| StackLift (chain : FactoredChain)
| StackJoin (lhs : FactoredStack) (rhs : FactoredChain)
with FactoredChain : Type :=
| ChainEmpty
| ChainCons (head : Signature) (tail : FactoredChain)
| ChainGroup (inner : FactoredStack).

Fixpoint erase_factored_stack (stack : FactoredStack) : StackSyntax :=
  match stack with
  | StackLift chain => erase_factored_chain chain
  | StackJoin lhs rhs =>
      StackParallel (erase_factored_stack lhs) (erase_factored_chain rhs)
  end
with erase_factored_chain (chain : FactoredChain) : StackSyntax :=
  match chain with
  | ChainEmpty => StackEmpty
  | ChainCons head tail => StackCons head (erase_factored_chain tail)
  | ChainGroup inner => erase_factored_stack inner
  end.

Definition factored_siblings (left right : Signature) : FactoredStack :=
  StackJoin
    (StackLift (ChainCons left ChainEmpty))
    (ChainCons right ChainEmpty).

Definition factored_shared_prefix (head left right : Signature)
    : FactoredStack :=
  StackLift (ChainCons head (ChainGroup (factored_siblings left right))).

Theorem factored_siblings_erase_to_independent_chains : forall left right,
  erase_factored_stack (factored_siblings left right) =
    StackParallel (StackCons left StackEmpty) (StackCons right StackEmpty).
Proof. reflexivity. Qed.

Theorem factored_shared_prefix_erases_once : forall head left right,
  erase_factored_stack (factored_shared_prefix head left right) =
    StackCons head
      (StackParallel (StackCons left StackEmpty)
                     (StackCons right StackEmpty)).
Proof. reflexivity. Qed.

Corollary factored_shared_prefix_emits_three_cells : forall head left right,
  event_cons_count
    (stack_events (erase_factored_stack
      (factored_shared_prefix head left right))) = 3.
Proof. intros; reflexivity. Qed.
Print Assumptions factored_shared_prefix_erases_once.
Print Assumptions factored_shared_prefix_emits_three_cells.

(** A residual [StackTree] is also its physical cursor.  The empty path names
    the current node; [false] and [true] select parallel children.  A cons
    exposes only its head, so no child path can bypass a shared prefix.  On
    consuming that head, the residual tail becomes the cursor and both
    parallel children become ready independently.  This is the rule used by
    the authority inventory: advancing one branch cannot advance the other. *)
Fixpoint ready_cells (cursor : StackTree) : list Signature :=
  match cursor with
  | TreeEmpty => []
  | TreeCons head _ => [head]
  | TreeParallel lhs rhs => ready_cells lhs ++ ready_cells rhs
  end.

Fixpoint pop_at (path : list bool) (cursor : StackTree)
    : option StackTree :=
  match cursor, path with
  | TreeCons _ tail, [] => Some tail
  | TreeParallel lhs rhs, false :: rest =>
      match pop_at rest lhs with
      | Some lhs' => Some (TreeParallel lhs' rhs)
      | None => None
      end
  | TreeParallel lhs rhs, true :: rest =>
      match pop_at rest rhs with
      | Some rhs' => Some (TreeParallel lhs rhs')
      | None => None
      end
  | _, _ => None
  end.

Theorem shared_prefix_cursor_gate : forall sig lhs rhs path,
  ready_cells (TreeCons sig (TreeParallel lhs rhs)) = [sig] /\
  pop_at (false :: path) (TreeCons sig (TreeParallel lhs rhs)) = None /\
  pop_at (true :: path) (TreeCons sig (TreeParallel lhs rhs)) = None /\
  pop_at [] (TreeCons sig (TreeParallel lhs rhs)) =
    Some (TreeParallel lhs rhs) /\
  ready_cells (TreeParallel lhs rhs) =
    ready_cells lhs ++ ready_cells rhs.
Proof. intros; repeat split; reflexivity. Qed.

Theorem parallel_children_advance_independently :
  forall lhs_head lhs_tail rhs_head rhs_tail,
  pop_at [false]
    (TreeParallel (TreeCons lhs_head lhs_tail)
                  (TreeCons rhs_head rhs_tail)) =
    Some (TreeParallel lhs_tail (TreeCons rhs_head rhs_tail)) /\
  pop_at [true]
    (TreeParallel (TreeCons lhs_head lhs_tail)
                  (TreeCons rhs_head rhs_tail)) =
    Some (TreeParallel (TreeCons lhs_head lhs_tail) rhs_tail).
Proof. intros; split; reflexivity. Qed.

(** An event checks every requested path against its entry cursor, before
    applying either pop.  Thus a prefix consumed by the first pop cannot
    release a child in that same event, while siblings already ready at entry
    can both advance without copying or coupling their cursors. *)
Definition pop_pair_one_event (first second : list bool)
    (cursor : StackTree) : option StackTree :=
  match pop_at first cursor, pop_at second cursor with
  | Some after_first, Some _ => pop_at second after_first
  | _, _ => None
  end.

Theorem same_event_prefix_cannot_release_child :
  forall sig lhs rhs path,
    pop_pair_one_event [] (false :: path)
      (TreeCons sig (TreeParallel lhs rhs)) = None /\
    pop_pair_one_event [] (true :: path)
      (TreeCons sig (TreeParallel lhs rhs)) = None.
Proof. intros; split; reflexivity. Qed.

Theorem ready_siblings_can_advance_in_one_event :
  forall lhs_head lhs_tail rhs_head rhs_tail,
    pop_pair_one_event [false] [true]
      (TreeParallel (TreeCons lhs_head lhs_tail)
                    (TreeCons rhs_head rhs_tail)) =
    Some (TreeParallel lhs_tail rhs_tail).
Proof. reflexivity. Qed.
Print Assumptions shared_prefix_cursor_gate.
Print Assumptions parallel_children_advance_independently.
Print Assumptions same_event_prefix_cannot_release_child.
Print Assumptions ready_siblings_can_advance_in_one_event.

(** The settlement applicator first builds a branch-lane view, then searches
    each synthetic pop by an iterative depth-first cursor.  Each node entry
    reserves one SearchCandidates unit before inspection; each child edge
    reserves its hash operation, preimage bytes, digest, DFS frame, and path
    element before computing/pushing them.  This event stream specifies the
    logical units for one complete search.  Stopping at a matched branch only
    takes a prefix, so no later work can be performed without its charge.
    A linear stack takes a separate application path and has no tree-search
    charge at all. *)
Inductive BranchCharge : Type :=
| ChargeVisit
| ChargeChildHash.

Fixpoint branch_charge_events (surface : StackSyntax) : list BranchCharge :=
  match surface with
  | StackEmpty => [ChargeVisit]
  | StackCons _ tail => branch_charge_events tail
  | StackParallel lhs rhs =>
      ChargeVisit :: ChargeChildHash ::
        (branch_charge_events lhs ++ ChargeChildHash :: branch_charge_events rhs)
  end.

Fixpoint branch_nodes (surface : StackSyntax) : nat :=
  match surface with
  | StackEmpty => 1
  | StackCons _ tail => branch_nodes tail
  | StackParallel lhs rhs => S (branch_nodes lhs + branch_nodes rhs)
  end.

Fixpoint branch_edges (surface : StackSyntax) : nat :=
  match surface with
  | StackEmpty => 0
  | StackCons _ tail => branch_edges tail
  | StackParallel lhs rhs => 2 + branch_edges lhs + branch_edges rhs
  end.

Fixpoint visit_charges (events : list BranchCharge) : nat :=
  match events with
  | [] => 0
  | ChargeVisit :: rest => S (visit_charges rest)
  | ChargeChildHash :: rest => visit_charges rest
  end.

Fixpoint hash_charges (events : list BranchCharge) : nat :=
  match events with
  | [] => 0
  | ChargeVisit :: rest => hash_charges rest
  | ChargeChildHash :: rest => S (hash_charges rest)
  end.

Lemma branch_charge_counts_app : forall first second,
  visit_charges (first ++ second) =
    visit_charges first + visit_charges second /\
  hash_charges (first ++ second) =
    hash_charges first + hash_charges second.
Proof.
  induction first as [|event first IH]; intros second; cbn.
  - split; reflexivity.
  - destruct event; cbn; destruct (IH second) as [Hv Hh]; rewrite Hv, Hh; lia.
Qed.

Theorem branch_search_charges_cover_full_tree : forall surface,
  visit_charges (branch_charge_events surface) = branch_nodes surface /\
  hash_charges (branch_charge_events surface) = branch_edges surface /\
  S (branch_edges surface) = branch_nodes surface.
Proof.
  induction surface as [|head tail IH|lhs IHl rhs IHr]; cbn.
  - repeat split; reflexivity.
  - exact IH.
  - destruct IHl as [Hvl [Hhl Hel]].
    destruct IHr as [Hvr [Hhr Her]].
    destruct (branch_charge_counts_app (branch_charge_events lhs)
      (ChargeChildHash :: branch_charge_events rhs)) as [Hva Hha].
    cbn in Hva, Hha. rewrite Hva, Hha, Hvl, Hhl, Hvr, Hhr.
    repeat split; lia.
Qed.

Theorem early_branch_match_never_exceeds_precharged_walk : forall first rest,
  visit_charges first <= visit_charges (first ++ rest) /\
  hash_charges first <= hash_charges (first ++ rest).
Proof.
  intros first rest.
  destruct (branch_charge_counts_app first rest) as [Hv Hh].
  rewrite Hv, Hh. lia.
Qed.

Fixpoint has_parallel_tail (surface : StackSyntax) : bool :=
  match surface with
  | StackEmpty => false
  | StackCons _ tail => has_parallel_tail tail
  | StackParallel _ _ => true
  end.

Definition application_charge_events (surface : StackSyntax) : list BranchCharge :=
  if has_parallel_tail surface then branch_charge_events surface else [].

Theorem any_linear_stack_application_has_no_branch_search_charge : forall surface,
  has_parallel_tail surface = false ->
  application_charge_events surface = [].
Proof. intros surface Hlinear; unfold application_charge_events; rewrite Hlinear; reflexivity. Qed.

Theorem linear_stack_application_has_no_branch_search_charge : forall sig,
  application_charge_events (StackCons sig StackEmpty) = [] /\
  visit_charges (application_charge_events (StackCons sig StackEmpty)) = 0 /\
  hash_charges (application_charge_events (StackCons sig StackEmpty)) = 0.
Proof. intros; repeat split; reflexivity. Qed.
Print Assumptions branch_search_charges_cover_full_tree.
Print Assumptions early_branch_match_never_exceeds_precharged_walk.
Print Assumptions any_linear_stack_application_has_no_branch_search_charge.
Print Assumptions linear_stack_application_has_no_branch_search_charge.

(** Signed receives have one rendezvous.  Uniform signing annotates an
    unsigned continuation with the same authority; lollipop annotates the
    rendezvous with its source and the continuation with its target.  Neither
    transformation synthesizes a fuel-gate receive. *)
Inductive Process : Type :=
| Atom (payload : nat)
| Receive (channel : nat) (continuation : Process)
| Signed (sig : Signature) (body : Process).

Definition rewrite_signed (sig : Signature) (body : Process)
    : option Process :=
  match sig, body with
  | Transfer source target, Receive channel continuation =>
      Some (Signed source
        (Receive channel (Signed target continuation)))
  | Transfer _ _, _ => None
  | _, Receive channel continuation =>
      Some (Signed sig (Receive channel
        (match continuation with
         | Signed _ _ => continuation
         | _ => Signed sig continuation
         end)))
  | _, _ => Some (Signed sig body)
  end.

Fixpoint receive_count (body : Process) : nat :=
  match body with
  | Atom _ => 0
  | Receive _ continuation => S (receive_count continuation)
  | Signed _ inner => receive_count inner
  end.

Theorem signed_rewrite_never_adds_a_receive : forall sig body result,
  rewrite_signed sig body = Some result ->
  receive_count result = receive_count body.
Proof.
  intros sig body result H.
  destruct sig; destruct body; cbn in H;
    try (inversion H; subst; cbn; reflexivity);
    try discriminate;
    destruct body; inversion H; subst; cbn; reflexivity.
Qed.

Theorem lollipop_reassigns_only_the_continuation :
  forall source target channel continuation,
  rewrite_signed (Transfer source target)
    (Receive channel continuation) =
    Some (Signed source
      (Receive channel (Signed target continuation))).
Proof. reflexivity. Qed.

Theorem lollipop_without_receive_is_rejected :
  forall source target payload,
  rewrite_signed (Transfer source target) (Atom payload) = None.
Proof. reflexivity. Qed.

Theorem uniform_sign_keeps_an_already_signed_continuation :
  forall sig channel continuation_sig continuation,
  rewrite_signed sig
    (Receive channel (Signed continuation_sig continuation)) =
  match sig with
  | Transfer source target =>
      Some (Signed source
        (Receive channel (Signed target
          (Signed continuation_sig continuation))))
  | _ =>
      Some (Signed sig
        (Receive channel (Signed continuation_sig continuation)))
  end.
Proof. intros; destruct sig; reflexivity. Qed.

End RholangCostSurface.
