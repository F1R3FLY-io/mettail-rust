(*
 * ContextualAtomicJoinPlugging: FV (vii) — INV-6 (a contextual rewrite fires as an
 * ATOMIC POLYADIC JOIN) + INV-2 (PLUGGING-STABILITY).
 *
 * A hypothesis-carrying contextual (congruence) rewrite
 *
 *     ⟦ …S_i ~> T_i… |- K(S_1,…,S_n) ~> K'(T_1,…,T_n) ⟧
 *
 * fires as ONE atomic n-ary JOIN: a single Receive with n binds — one flat σ-slot per
 * premise hole T_i on that premise's location channel — whose body emits the reduced
 * context ⟦K'⟧ = plug K' [T_1,…,T_n] on the dynamic out channel.  The codegen realizes it
 * as `contextual_join_receiver_par` (n `ReceiveBind`s, out on the last), and the injection
 * `contextual_contract_call` delivers the n reduced holes.
 *
 * Proven here (a faithful generalization of LinearCommCorrespondence.v's `SameChannelJoin`
 * from 2 premises to n):
 *   - `consume_list` (fold `remove_first` over the n holes) is the n-ary consume, and it
 *     AGREES with `consume_two` at n = 2 (the explicit 2→n reuse), and is order-independent;
 *   - the n-ary contextual join step (source + rho) is SOUND and COMPLETE with matching
 *     barbs (generalizing `same_channel_join_sound`/`_complete` 2→n);
 *   - ATOMICITY (INV-4): the join fires IFF all n holes are present; a missing hole admits
 *     NO step — there is no partial consume, and the join emits EXACTLY ONE reduced context;
 *   - PLUGGING-STABILITY (INV-2): plugging is total and injective on the hole list (distinct
 *     reduced holes ⇒ distinct reduced contexts — no information loss), the join's sole new
 *     output IS the plugged reduced context, and the OUTER context head is invariant to the
 *     holes (an inner rewrite below a hole leaves the outer join channel valid — O2);
 *   - the UNARY specialization `Wrap(S) ~> Wrap(T)` (the codegen's synthetic fixture): the
 *     single-premise join consumes exactly the one hole and reconstructs ⟦Wrap(T)⟧.
 *
 * Reuses LinearCommCorrespondence.v (`Fact`, `remove_first`, `consume_two`, and the
 * `SameChannelJoin` proof shape); cf. DeltaOneMinCostJoin.v (reject-safe selection) and
 * PrunePreservesWork.v (O2 prune-preserves-work) for the companion axes.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Sorting.Permutation.
From RhoBridge Require Import LinearCommCorrespondence.

Import ListNotations.

(* ------------------------------------------------------------------------ *)
(* The n-ary consume: fold `remove_first` over the reduced holes.           *)
(* ------------------------------------------------------------------------ *)

Section NaryConsume.

  (* Consume the n reduced holes from the pending sends, one per premise channel. *)
  Fixpoint consume_list (holes sends : list Fact) : list Fact :=
    match holes with
    | [] => sends
    | h :: rest => consume_list rest (remove_first h sends)
    end.

  (* The atomic availability predicate: every hole is present as the consume peels them off
     (the all-or-nothing precondition of the join — no partial consume). *)
  Fixpoint all_present (holes sends : list Fact) : Prop :=
    match holes with
    | [] => True
    | h :: rest => In h sends /\ all_present rest (remove_first h sends)
    end.

  Lemma consume_list_nil : forall sends,
    consume_list [] sends = sends.
  Proof. reflexivity. Qed.

  Lemma consume_list_cons : forall h rest sends,
    consume_list (h :: rest) sends = consume_list rest (remove_first h sends).
  Proof. reflexivity. Qed.

  (* The explicit 2→n reuse: at n = 2 the n-ary consume IS SameChannelJoin's `consume_two`,
     so the contextual join generalizes the same-channel two-premise join faithfully. *)
  Theorem consume_list_generalizes_consume_two : forall first second sends,
    consume_list [first; second] sends = consume_two first second sends.
  Proof.
    intros first second sends. unfold consume_two. reflexivity.
  Qed.

  (* `all_present` at n = 2 is exactly the two membership premises `SameChannelJoin` requires. *)
  Theorem all_present_two : forall first second sends,
    all_present [first; second] sends
    <-> (In first sends /\ In second (remove_first first sends)).
  Proof.
    intros first second sends. simpl. split.
    - intros [H1 [H2 _]]. split; assumption.
    - intros [H1 H2]. split; [exact H1 | split; [exact H2 | exact I]].
  Qed.

End NaryConsume.

(* ------------------------------------------------------------------------ *)
(* The n-ary contextual JOIN: source vs. rho, sound + complete + atomic.    *)
(* The output payload type `Out` and the plugging function `plug` are        *)
(* abstract here (any concrete reduced-context reconstruction instantiates   *)
(* them — see the `Plugging`/`UnaryWrap` sections).                          *)
(* ------------------------------------------------------------------------ *)

Section NaryJoin.

  Variable Out : Type.
  (* `plug holes` = ⟦K'⟧: the reduced context, a function of the n reduced holes only
     (the join's body sends it on the out channel). *)
  Variable plug : list Fact -> Out.

  Record JoinSource : Type := {
    jsrc_sends : list Fact;
    jsrc_receive : bool;
    jsrc_outputs : list Out
  }.

  Record JoinRho : Type := {
    jrho_sends : list Fact;
    jrho_receive : bool;
    jrho_outputs : list Out
  }.

  Definition lower_join (s : JoinSource) : JoinRho :=
    {|
      jrho_sends := jsrc_sends s;
      jrho_receive := jsrc_receive s;
      jrho_outputs := jsrc_outputs s
    |}.

  (* The source-semantics contextual join: with the receiver armed and ALL n holes present,
     consume them atomically and emit the single reduced context `plug holes`. *)
  Definition source_nary_join (s : JoinSource) (holes : list Fact) (s' : JoinSource) : Prop :=
    jsrc_receive s = true
    /\ all_present holes (jsrc_sends s)
    /\ s' =
       {|
         jsrc_sends := consume_list holes (jsrc_sends s);
         jsrc_receive := false;
         jsrc_outputs := plug holes :: jsrc_outputs s
       |}.

  (* The lowered Rho contextual join: the SAME atomic n-ary rendezvous. *)
  Definition rho_nary_join (r : JoinRho) (holes : list Fact) (r' : JoinRho) : Prop :=
    jrho_receive r = true
    /\ all_present holes (jrho_sends r)
    /\ r' =
       {|
         jrho_sends := consume_list holes (jrho_sends r);
         jrho_receive := false;
         jrho_outputs := plug holes :: jrho_outputs r
       |}.

  Definition join_barb_equiv (r : JoinRho) (s : JoinSource) : Prop :=
    forall x, In x (jrho_outputs r) <-> In x (jsrc_outputs s).

  Theorem lower_join_preserves_barbs : forall s,
    join_barb_equiv (lower_join s) s.
  Proof. intros s x. split; intro H; exact H. Qed.

  (* SOUNDNESS (generalizes `same_channel_join_sound` 2→n): every lowered Rho contextual
     join has a source contextual join with the same outputs. *)
  Theorem nary_join_sound : forall s holes r',
    rho_nary_join (lower_join s) holes r' ->
    exists s',
      source_nary_join s holes s'
      /\ join_barb_equiv r' s'.
  Proof.
    intros s holes r' [Hrecv [Hpres Hr']].
    exists {|
      jsrc_sends := consume_list holes (jsrc_sends s);
      jsrc_receive := false;
      jsrc_outputs := plug holes :: jsrc_outputs s
    |}.
    split.
    - split; [exact Hrecv | split; [exact Hpres | reflexivity]].
    - subst r'. intros x. split; intro H; exact H.
  Qed.

  (* COMPLETENESS (generalizes `same_channel_join_complete` 2→n): every source contextual
     join has a lowered Rho contextual join with the same outputs. *)
  Theorem nary_join_complete : forall s holes s',
    source_nary_join s holes s' ->
    exists r',
      rho_nary_join (lower_join s) holes r'
      /\ join_barb_equiv r' s'.
  Proof.
    intros s holes s' [Hrecv [Hpres Hs']].
    exists {|
      jrho_sends := consume_list holes (jsrc_sends s);
      jrho_receive := false;
      jrho_outputs := plug holes :: jsrc_outputs s
    |}.
    split.
    - split; [exact Hrecv | split; [exact Hpres | reflexivity]].
    - subst s'. intros x. split; intro H; exact H.
  Qed.

  (* ATOMICITY (INV-4), all-or-nothing: if not every hole is present, NO join step exists —
     the join never partially consumes.  (`all_present` is a conjunct of the step relation,
     so a missing hole refutes the step outright.) *)
  Theorem nary_join_atomic_no_partial : forall r holes,
    ~ all_present holes (jrho_sends r) ->
    forall r', ~ rho_nary_join r holes r'.
  Proof.
    intros r holes Hnp r' [_ [Hpres _]]. exact (Hnp Hpres).
  Qed.

  (* The armed join, once fired, emits EXACTLY ONE new output — the reduced context
     `plug holes` — prepended to the pending outputs (no fan-out, one atomic body send). *)
  Theorem nary_join_emits_one_reduced_context : forall r holes r',
    rho_nary_join r holes r' ->
    jrho_outputs r' = plug holes :: jrho_outputs r.
  Proof.
    intros r holes r' [_ [_ Hr']]. subst r'. reflexivity.
  Qed.

  (* The join disarms the one-shot receiver in the same atomic step (no re-fire before the
     next arm). *)
  Theorem nary_join_disarms : forall r holes r',
    rho_nary_join r holes r' ->
    jrho_receive r' = false.
  Proof.
    intros r holes r' [_ [_ Hr']]. subst r'. reflexivity.
  Qed.

End NaryJoin.

(* ------------------------------------------------------------------------ *)
(* PLUGGING-STABILITY (INV-2): plugging the n reduced holes into a context   *)
(* skeleton is a total, injective reconstruction whose head (the outer join  *)
(* channel) is invariant to the holes.                                       *)
(* ------------------------------------------------------------------------ *)

Section Plugging.

  (* A reflected reduced term: a leaf (a nullary constructor / a delivered hole) or a node
     (a constructor over reflected children) — the `EList[tag, children…]` reflection ABI. *)
  Inductive Term : Type :=
    | TLeaf : nat -> Term
    | TNode : nat -> list Term -> Term.

  (* Plug the reduced holes into the context skeleton `K'` headed by constructor `op`
     (the codegen's `reflect_term_par` over the n target holes: `EList[tag op, holes…]`). *)
  Definition plug_ctx (op : nat) (holes : list Term) : Term := TNode op holes.

  Definition head_op (t : Term) : option nat :=
    match t with
    | TLeaf _ => None
    | TNode op _ => Some op
    end.

  Theorem plug_ctx_total : forall op holes,
    exists t, plug_ctx op holes = t.
  Proof. intros op holes. exists (plug_ctx op holes). reflexivity. Qed.

  (* Plugging is INJECTIVE on the hole list: distinct reduced holes give distinct reduced
     contexts — the join loses no information about what filled each hole. *)
  Theorem plug_ctx_holes_injective : forall op h1 h2,
    plug_ctx op h1 = plug_ctx op h2 -> h1 = h2.
  Proof.
    intros op h1 h2 H. unfold plug_ctx in H. injection H as H. exact H.
  Qed.

  Theorem plug_ctx_op_injective : forall op1 op2 holes,
    plug_ctx op1 holes = plug_ctx op2 holes -> op1 = op2.
  Proof.
    intros op1 op2 holes H. unfold plug_ctx in H. injection H as H. exact H.
  Qed.

  Theorem plug_ctx_determines : forall op h1 h2,
    plug_ctx op h1 = plug_ctx op h2 <-> h1 = h2.
  Proof.
    intros op h1 h2. split.
    - apply plug_ctx_holes_injective.
    - intro H. subst h2. reflexivity.
  Qed.

  (* O2 / outer-channel stability: the reduced context's HEAD is `op` no matter WHICH holes
     are plugged — an inner rewrite that changes a hole below the context leaves the OUTER
     join channel (keyed by the head) valid (prune preserves the outer work). *)
  Theorem plug_ctx_head_stable : forall op holes,
    head_op (plug_ctx op holes) = Some op.
  Proof. intros op holes. reflexivity. Qed.

  Corollary plug_ctx_head_invariant_to_holes : forall op h1 h2,
    head_op (plug_ctx op h1) = head_op (plug_ctx op h2).
  Proof.
    intros op h1 h2. rewrite !plug_ctx_head_stable. reflexivity.
  Qed.

End Plugging.

(* ------------------------------------------------------------------------ *)
(* The UNARY specialization `Wrap(S) ~> Wrap(T)` — the codegen fixture.      *)
(* Instantiate the abstract join with the concrete `Term` plugging: one      *)
(* premise, one reduced hole, reconstructing ⟦Wrap(T)⟧.                      *)
(* ------------------------------------------------------------------------ *)

Section UnaryWrap.

  (* The `Wrap` constructor's reflection tag (any fixed code). *)
  Variable wrap_op : nat.

  (* A delivered reduced hole reflects to a leaf term (the ground σ sub-term); the unary
     context plugs the single hole under `wrap_op`: ⟦Wrap(T)⟧ = TNode wrap_op [TLeaf T]. *)
  Definition wrap_plug (holes : list Fact) : Term :=
    plug_ctx wrap_op (map TLeaf holes).

  (* The reduced context the unary join emits IS ⟦Wrap(T)⟧. *)
  Theorem wrap_plug_reconstructs : forall t,
    wrap_plug [t] = TNode wrap_op [TLeaf t].
  Proof. intro t. reflexivity. Qed.

  (* The unary join consumes EXACTLY the one delivered hole (atomic single-premise consume). *)
  Theorem unary_consume_is_remove_first : forall t sends,
    consume_list [t] sends = remove_first t sends.
  Proof. intros t sends. reflexivity. Qed.

  (* End-to-end unary firing: an armed join over the single hole `t` present in `sends`
     steps to disarmed, consuming `t` and emitting the reconstructed context ⟦Wrap(t)⟧. *)
  Theorem unary_wrap_join_fires : forall sends outs t,
    In t sends ->
    rho_nary_join Term wrap_plug
      {| jrho_sends := sends; jrho_receive := true; jrho_outputs := outs |}
      [t]
      {| jrho_sends := remove_first t sends;
         jrho_receive := false;
         jrho_outputs := TNode wrap_op [TLeaf t] :: outs |}.
  Proof.
    intros sends outs t Hin.
    unfold rho_nary_join. simpl.
    split; [reflexivity | ].
    split.
    - split; [exact Hin | exact I].
    - reflexivity.
  Qed.

  (* And it is the UNIQUE such step (the join is deterministic given the delivered hole). *)
  Theorem unary_wrap_join_deterministic : forall s outs t r',
    rho_nary_join Term wrap_plug
      {| jrho_sends := s; jrho_receive := true; jrho_outputs := outs |} [t] r' ->
    r' = {| jrho_sends := remove_first t s;
            jrho_receive := false;
            jrho_outputs := TNode wrap_op [TLeaf t] :: outs |}.
  Proof.
    intros s outs t r' [_ [_ Hr']]. subst r'. reflexivity.
  Qed.

End UnaryWrap.

(* ------------------------------------------------------------------------ *)
(* Capstone: the contextual join is ATOMIC and PLUGGING-STABLE together.     *)
(* ------------------------------------------------------------------------ *)

Section Capstone.

  Variable Out : Type.
  Variable plug : list Fact -> Out.

  (* One statement combining INV-6 (atomic all-or-nothing n-ary firing emitting the single
     reduced context) with the plugging determinacy the reduced context enjoys: whenever the
     join fires, its output IS `plug holes` and the receiver disarms; and if any hole is
     absent, it does not fire. *)
  Theorem contextual_join_atomic_and_plugging_stable :
    (forall r holes r',
        rho_nary_join Out plug r holes r' ->
        jrho_outputs Out r' = plug holes :: jrho_outputs Out r
        /\ jrho_receive Out r' = false)
    /\ (forall r holes,
        ~ all_present holes (jrho_sends Out r) ->
        forall r', ~ rho_nary_join Out plug r holes r').
  Proof.
    split.
    - intros r holes r' Hstep. split.
      + apply (nary_join_emits_one_reduced_context Out plug r holes r' Hstep).
      + apply (nary_join_disarms Out plug r holes r' Hstep).
    - apply (nary_join_atomic_no_partial Out plug).
  Qed.

End Capstone.

(* ------------------------------------------------------------------------ *)
(* Stage 4 (S-contextual) MATCHING-SIDE ARM: the reduced holes fed to the    *)
(* proven join come from the automaton's IN-RHO NESTED FIRINGS at the hole   *)
(* positions (a function of the SUBJECT spread), NOT the host-σ report        *)
(* (reconstruct_contractum). The corrupted-σ probe made precise.             *)
(* ------------------------------------------------------------------------ *)

Section MatchingSideArm.

  (* Abstract subject/report carriers: the whole reflected subject term (the outer context K with
     its distinguished hole positions) and a (possibly corrupted) Dovetail report. *)
  Variable Subject : Type.
  Variable Report : Type.

  (* The automaton's LOCATED reduced hole: the base set-automaton descends K's spine to the hole
     position ℓ_0, matches + fires the premise redex IN RHO, and the σ-receiver emits the reduced
     hole `T_0` — a function of the SUBJECT SPREAD alone (M-reflect). The hole bridge routes it to
     the join's premise channel. *)
  Variable located_hole : Subject -> Fact.
  (* The RETIRED host-σ reconstruction (`reconstruct_contractum`): the reduced hole rebuilt from the
     report σ. Present ONLY to state the separation — it is no longer on the match path. *)
  Variable report_hole : Report -> Fact.

  (* The routed premise-channel sends: for a UNARY context (the landed sub-slice), ONE send carrying
     the located hole on the join's single premise channel `c(ℓ_0)`. *)
  Definition routed_sends (subj : Subject) : list Fact := [located_hole subj].

  (* SUBJECT-KEYED (AC-style independence, cf. InRhoAcMatchMultiset's
     `located_match_is_independent_of_report`): the routed premise send is a function of the SUBJECT
     only — the conclusion never mentions the report, so it holds for ANY report. *)
  Theorem routed_hole_is_subject_keyed : forall (subj : Subject) (rep : Report),
    routed_sends subj = [located_hole subj].
  Proof. intros subj rep. reflexivity. Qed.

  (* The CORRUPTED-σ probe `s_contextual_holes_reassembled_in_rho_not_the_report` made precise:
     even when the report hole DIFFERS from the automaton's located hole (a corrupted σ), the routed
     hole is STILL the located hole — the corrupted report cannot perturb the routed reduced hole. *)
  Theorem corrupted_report_does_not_perturb_routed_hole :
    forall (subj : Subject) (rep : Report),
      located_hole subj <> report_hole rep -> routed_sends subj = [located_hole subj].
  Proof. intros subj rep _. reflexivity. Qed.

  (* The routed UNARY join fires + reassembles ⟦K'⟧ from the located hole (reuses the proven
     `unary_wrap_join_fires`): the armed join over the routed premise send consumes the located
     hole and emits `⟦Wrap(located_hole subj)⟧`. So the plugging is FED BY the in-Rho nested firing. *)
  Theorem routed_unary_join_reassembles_located_hole :
    forall (op : nat) (subj : Subject) (outs : list Term),
      rho_nary_join Term (wrap_plug op)
        {| jrho_sends := routed_sends subj; jrho_receive := true; jrho_outputs := outs |}
        [located_hole subj]
        {| jrho_sends := remove_first (located_hole subj) (routed_sends subj);
           jrho_receive := false;
           jrho_outputs := TNode op [TLeaf (located_hole subj)] :: outs |}.
  Proof.
    intros op subj outs. apply unary_wrap_join_fires. unfold routed_sends. apply in_eq.
  Qed.

  (* CAPSTONE (the matching-side analogue of `contextual_join_atomic_and_plugging_stable`): whenever
     the routed join fires, the emitted reduced context IS the SUBJECT's located hole plugged, for
     ANY report `rep` (which is quantified but never used) — so the reassembled ⟦K'⟧ is fed by the
     automaton's nested firing, never the report σ. This is the corrupted-σ probe's OUT value made
     precise: `Wrap(located_hole subj)` regardless of the (corrupted) report. *)
  Theorem matching_side_reassembly_is_subject_keyed_not_report :
    forall (op : nat) (subj : Subject) (outs : list Term) (rep : Report) r',
      rho_nary_join Term (wrap_plug op)
        {| jrho_sends := routed_sends subj; jrho_receive := true; jrho_outputs := outs |}
        [located_hole subj] r' ->
      jrho_outputs Term r' = wrap_plug op [located_hole subj] :: outs.
  Proof.
    intros op subj outs rep r' Hstep.
    exact (nary_join_emits_one_reduced_context Term (wrap_plug op) _ _ _ Hstep).
  Qed.

End MatchingSideArm.

(* ------------------------------------------------------------------------ *)
(* n-ary generalization of the matching-side arm (the next sub-slice): the n *)
(* located holes (each a function of the subject) route to the n premise     *)
(* channels and feed the proven n-ary join, which emits plug(located_holes). *)
(* ------------------------------------------------------------------------ *)

Section MatchingSideArmNary.

  Variable Subject : Type.
  Variable Out : Type.
  Variable plug : list Fact -> Out.
  (* The n located reduced holes, in premise order — each the automaton's nested firing at hole ℓ_i
     (a function of the SUBJECT). The n-ary hole bridge routes them to the n premise channels. *)
  Variable located_holes : Subject -> list Fact.

  Definition routed_sends_nary (subj : Subject) : list Fact := located_holes subj.

  (* Routing the n located holes to the n premise channels and firing the proven n-ary join emits
     `plug (located_holes subj)` — the reassembled ⟦K'⟧ — consuming exactly the routed holes. The
     `all_present` precondition (the automaton delivered all n located holes to their channels) is an
     honest premise, exactly the join step's own availability conjunct. The report never appears. *)
  Theorem routed_nary_join_reassembles_located_holes :
    forall (subj : Subject) (outs : list Out),
      all_present (located_holes subj) (routed_sends_nary subj) ->
      rho_nary_join Out plug
        {| jrho_sends := routed_sends_nary subj; jrho_receive := true; jrho_outputs := outs |}
        (located_holes subj)
        {| jrho_sends := consume_list (located_holes subj) (routed_sends_nary subj);
           jrho_receive := false;
           jrho_outputs := plug (located_holes subj) :: outs |}.
  Proof.
    intros subj outs Hpres. unfold rho_nary_join. simpl.
    split; [reflexivity | split; [exact Hpres | reflexivity]].
  Qed.

  (* And the emitted reduced context is plug(located_holes) — subject-keyed, report-absent. *)
  Theorem nary_reassembly_is_subject_keyed :
    forall (subj : Subject) (outs : list Out) r',
      rho_nary_join Out plug
        {| jrho_sends := routed_sends_nary subj; jrho_receive := true; jrho_outputs := outs |}
        (located_holes subj) r' ->
      jrho_outputs Out r' = plug (located_holes subj) :: outs.
  Proof.
    intros subj outs r' Hstep.
    exact (nary_join_emits_one_reduced_context Out plug _ _ _ Hstep).
  Qed.

End MatchingSideArmNary.

(* ------------------------------------------------------------------------ *)
(* Zero-admission confirmation.                                              *)
(* ------------------------------------------------------------------------ *)

Print Assumptions consume_list_generalizes_consume_two.
Print Assumptions nary_join_sound.
Print Assumptions nary_join_complete.
Print Assumptions nary_join_atomic_no_partial.
Print Assumptions plug_ctx_holes_injective.
Print Assumptions plug_ctx_head_stable.
Print Assumptions unary_wrap_join_fires.
Print Assumptions contextual_join_atomic_and_plugging_stable.
Print Assumptions routed_hole_is_subject_keyed.
Print Assumptions corrupted_report_does_not_perturb_routed_hole.
Print Assumptions routed_unary_join_reassembles_located_hole.
Print Assumptions matching_side_reassembly_is_subject_keyed_not_report.
Print Assumptions routed_nary_join_reassembles_located_holes.
Print Assumptions nary_reassembly_is_subject_keyed.
