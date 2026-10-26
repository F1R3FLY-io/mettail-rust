(*
 * LexForkKeywordReservation: the lex-fork at PrefixDispatch must not drop the
 * EXPLICITLY-DECLARED keyword interpretation of a token that is also lexable as
 * an identifier.
 *
 * Rust site: `emit_lex_fork_at_prefix_dispatch`
 * (macros/src/gen/runtime/wpda_codegen/forks.rs). A lex-ambiguous position
 * surfaces a PRIMARY lexical alternative (maximal-munch / keyword winner) plus
 * SECONDARY alternatives. The lex-fork rebuilds dispatch from
 * `lex_alt_rules_for_prefix`, whose `LexAltRuleKind` only represents
 * `Atomic | PrefixOp | CrossCatProjection` — it CANNOT represent collection-
 * literal rules (ListLit/BagLit/MapLit) nor multi-token keyword-prefix rules
 * (ElemList `at(...)`, …). For a keyword that ALSO matches the ident regex
 * (`list`/`at`/`error`/`int`/…) the lattice emits a SAME-LENGTH
 * `{Fixed("kw"), Ident}` ambiguity, so the buggy lex-fork forked only the
 * secondary `Ident -> Var` branch and the keyword parsed as a bare variable.
 *
 * Fix: wire the long-generated-but-never-called `prefix_primary_has_dispatch_rule`
 * into the fall-through decision, guarded by SAME-LENGTH (so genuine multi-length
 * disambiguation such as `-3` = {Minus@1, Integer@2} keeps forking both).
 *
 * Model. A lexical alternative carries a `kind` and a `len` (its end-byte span).
 * Two abstract per-language classifiers (Section variables, NOT axioms — they are
 * universally quantified at Section close):
 *   - `representable k` : the lex-alt table can build a branch for kind `k`
 *     (= `LexAltRuleKind` Atomic/PrefixOp/CrossCatProjection).
 *   - `has_dispatch k`  : the normal PrefixDispatch has an arm for kind `k`
 *     (= `prefix_primary_has_dispatch_rule`).
 *   - `is_contextual k` : the token spelling retains an identifier co-reading.
 * `num_branches` mirrors the Rust branch vector (primary if representable, plus
 * each representable secondary). `fall_through_old` is the original lex-fork
 * decision, `fall_through_new` is the pre-contextual Phase 5A repair,
 * `fall_through_contextual_bug` is the regressed decision, and
 * `fall_through_refined` is the completeness-preserving contextual decision.
 *
 * Proven (zero-admission):
 *   - fix_preserves_keyword : a primary keyword with a normal dispatch arm and
 *     only same-length alternatives ALWAYS falls through to the normal dispatch
 *     (its declared interpretation is taken, never replaced by a lone Var).
 *   - multilength_guard : when some alternative differs in length, the NEW
 *     fall-through equals the OLD one — the fix never perturbs genuine
 *     multi-length disambiguation (regression-safety for `-3` & friends).
 *   - dropped_secondary_is_same_length : whenever the fix's new disjunct fires,
 *     every dropped secondary is a SAME-LENGTH lexical tie with the grammar-
 *     declared keyword — keyword-reservation is evidence (the grammar declares
 *     the literal), not a heuristic prune.
 *   - buggy_lexfork_drops_collection_keyword : the negative fence — a witness
 *     (collection keyword, `representable=false`, `has_dispatch=true`, one
 *     same-length representable Var secondary) where the OLD decision FORKS only
 *     the Var (keyword lost) while the NEW decision falls through (keyword kept).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Import ListNotations.

Section LexForkKeywordReservation.

  (* A lexical alternative at one DAG position: a token kind and an end-byte span. *)
  Record Alt : Type := { akind : nat; alen : nat }.

  (* Per-language classifiers (abstracted on Section close — not axioms). *)
  Variable representable : nat -> bool.   (* LexAltRuleKind-representable      *)
  Variable has_dispatch  : nat -> bool.   (* prefix_primary_has_dispatch_rule  *)
  Variable is_contextual : nat -> bool.   (* identifier co-reading retained    *)

  (* The lex-fork branch vector: the primary contributes a branch iff its kind is
     representable; each representable secondary contributes one. (Mirrors the
     `__branches` Vec and `__primary_survived` flag.) *)
  Definition primary_survived (primary : Alt) : bool := representable (akind primary).

  Definition num_branches (primary : Alt) (secs : list Alt) : nat :=
    (if representable (akind primary) then 1 else 0)
    + length (filter (fun s => representable (akind s)) secs).

  (* `__all_alts_same_length`: every secondary ends at the same byte as the primary. *)
  Definition all_same_length (primary : Alt) (secs : list Alt) : bool :=
    forallb (fun s => Nat.eqb (alen s) (alen primary)) secs.

  (* `__fall_through` BEFORE the fix. *)
  Definition fall_through_old (primary : Alt) (secs : list Alt) : bool :=
    Nat.eqb (num_branches primary secs) 0
    || (Nat.eqb (num_branches primary secs) 1 && primary_survived primary).

  (* `__fall_through` AFTER the fix (the new third disjunct). *)
  Definition fall_through_new (primary : Alt) (secs : list Alt) : bool :=
    fall_through_old primary secs
    || (has_dispatch (akind primary) && all_same_length primary secs).

  (* The regressed contextual rule suppressed normal dispatch solely from the
     token spelling, even when the lexical fork had no primary branch capable
     of executing that token's declared fixed syntax. *)
  Definition fall_through_contextual_bug
      (primary : Alt) (secs : list Alt) : bool :=
    fall_through_old primary secs
    || (has_dispatch (akind primary)
        && all_same_length primary secs
        && negb (is_contextual (akind primary))).

  (* A contextual fork is retained only when it actually represents its primary
     fixed-token reading. Otherwise normal PrefixDispatch is the sole route to
     that declared syntax and must receive control. *)
  Definition fall_through_refined (primary : Alt) (secs : list Alt) : bool :=
    fall_through_old primary secs
    || (has_dispatch (akind primary)
        && all_same_length primary secs
        && (negb (is_contextual (akind primary))
            || negb (primary_survived primary))).

  (* When the lex-fork falls through, the normal `match peek` dispatch runs on the
     PRIMARY token's kind — which (when `has_dispatch` holds) owns the
     collection / keyword-prefix / terminal arm. So "fall through" ≡ "the declared
     keyword interpretation is dispatched", and "Fork" ≡ "branch over the lex-alt
     vector". This is the decision the theorems below pin down. *)

  (* (1) The fix: a primary keyword that owns a normal dispatch arm and has only
     same-length alternatives ALWAYS falls through — its declared interpretation
     is taken, never replaced by the lone secondary Var branch. *)
  Theorem fix_preserves_keyword :
    forall (primary : Alt) (secs : list Alt),
      has_dispatch (akind primary) = true ->
      all_same_length primary secs = true ->
      fall_through_new primary secs = true.
  Proof.
    intros primary secs Hdisp Hlen.
    unfold fall_through_new.
    rewrite Hdisp, Hlen. simpl.
    apply orb_true_r.
  Qed.

  (* A contextual token whose primary kind is absent from the fork must still
     reach its declared normal-dispatch syntax. This is the generalized Set
     collection-opener obligation. *)
  Theorem contextual_unrepresented_primary_is_preserved :
    forall (primary : Alt) (secs : list Alt),
      representable (akind primary) = false ->
      has_dispatch (akind primary) = true ->
      all_same_length primary secs = true ->
      fall_through_refined primary secs = true.
  Proof.
    intros primary secs Hrepr Hdisp Hlen.
    unfold fall_through_refined, primary_survived.
    rewrite Hrepr, Hdisp, Hlen.
    destruct (is_contextual (akind primary)); simpl; apply orb_true_r.
  Qed.

  (* If a contextual primary is already represented in the fork, Phase 5A does
     not erase the fork's identifier alternative. *)
  Theorem contextual_represented_primary_retains_fork :
    forall (primary : Alt) (secs : list Alt),
      fall_through_old primary secs = false ->
      is_contextual (akind primary) = true ->
      primary_survived primary = true ->
      has_dispatch (akind primary) = true ->
      all_same_length primary secs = true ->
      fall_through_refined primary secs = false.
  Proof.
    intros primary secs Hold Hctx Hprimary Hdisp Hlen.
    unfold fall_through_refined.
    rewrite Hold, Hctx, Hprimary, Hdisp, Hlen.
    reflexivity.
  Qed.

  (* Outside contextual spellings, the refinement is exactly the pre-regression
     Phase 5A decision. *)
  Theorem noncontextual_refinement_is_pre_regression :
    forall (primary : Alt) (secs : list Alt),
      is_contextual (akind primary) = false ->
      fall_through_refined primary secs = fall_through_new primary secs.
  Proof.
    intros primary secs Hctx.
    unfold fall_through_refined, fall_through_new.
    rewrite Hctx.
    simpl.
    rewrite andb_true_r.
    reflexivity.
  Qed.

  (* Different lexical extents still require the lexical fork; contextual
     refinement cannot alter that decision. *)
  Theorem refined_multilength_guard :
    forall (primary : Alt) (secs : list Alt),
      all_same_length primary secs = false ->
      fall_through_refined primary secs = fall_through_old primary secs.
  Proof.
    intros primary secs Hlen.
    unfold fall_through_refined.
    rewrite Hlen.
    repeat rewrite andb_false_r.
    apply orb_false_r.
  Qed.

  (* The refined decision never invents a route: success is justified either
     by the old fork simplification or by an already-generated normal-dispatch
     primary arm. Thus the repair adds no transition or stack operation. *)
  Theorem refined_success_uses_existing_route :
    forall (primary : Alt) (secs : list Alt),
      fall_through_refined primary secs = true ->
      fall_through_old primary secs = true \/
      has_dispatch (akind primary) = true.
  Proof.
    intros primary secs H.
    unfold fall_through_refined in H.
    apply orb_true_iff in H as [Hold | Hroute].
    - left. exact Hold.
    - right.
      apply andb_true_iff in Hroute as [Hdispatch_length _].
      apply andb_true_iff in Hdispatch_length as [Hdispatch _].
      exact Hdispatch.
  Qed.

  (* (2) Regression-safety: when SOME alternative differs in length, the new
     fall-through is byte-identical to the old one. The same-length guard makes
     the fix inert on genuine multi-length disambiguation (`-3`, etc.). *)
  Theorem multilength_guard :
    forall (primary : Alt) (secs : list Alt),
      all_same_length primary secs = false ->
      fall_through_new primary secs = fall_through_old primary secs.
  Proof.
    intros primary secs Hlen.
    unfold fall_through_new.
    rewrite Hlen.
    rewrite andb_false_r.
    apply orb_false_r.
  Qed.

  (* A length-distinct alternative makes `all_same_length` false (the hypothesis of
     `multilength_guard`), so the two results coincide for it. *)
  Theorem length_distinct_alt_makes_guard :
    forall (primary : Alt) (secs : list Alt) (s : Alt),
      In s secs ->
      alen s <> alen primary ->
      all_same_length primary secs = false.
  Proof.
    intros primary secs s Hin Hneq.
    apply not_true_is_false. intro Hall.
    unfold all_same_length in Hall.
    rewrite forallb_forall in Hall.
    specialize (Hall s Hin).
    apply Nat.eqb_eq in Hall.
    contradiction.
  Qed.

  (* (3) Evidence, not heuristic: whenever the fix's new disjunct is what makes the
     position fall through, every secondary it drops is a SAME-LENGTH lexical tie
     with the grammar-declared keyword. *)
  Theorem dropped_secondary_is_same_length :
    forall (primary : Alt) (secs : list Alt) (s : Alt),
      has_dispatch (akind primary) = true ->
      all_same_length primary secs = true ->
      In s secs ->
      alen s = alen primary.
  Proof.
    intros primary secs s Hdisp Hlen Hin.
    unfold all_same_length in Hlen.
    rewrite forallb_forall in Hlen.
    specialize (Hlen s Hin).
    apply Nat.eqb_eq in Hlen. exact Hlen.
  Qed.

  (* (4) Negative fence: a collection-literal keyword (NOT lex-alt representable but
     WITH a normal dispatch arm) followed by exactly one same-length representable
     `Var` secondary. The OLD lex-fork FORKS only the Var (the keyword is lost) but
     the NEW lex-fork FALLS THROUGH (the keyword's collection dispatch is kept).
     This is precisely the `list(5)` / `at(...)` / `error op error` bug. *)
  (* kind 0 = collection keyword: dispatchable, NOT lex-alt-representable;
     kind 1 = Ident/Var: lex-alt-representable. *)
  Theorem buggy_lexfork_drops_collection_keyword :
    representable 0 = false ->
    representable 1 = true ->
    has_dispatch 0 = true ->
    fall_through_old {| akind := 0; alen := 4 |} [{| akind := 1; alen := 4 |}] = false /\
    fall_through_new {| akind := 0; alen := 4 |} [{| akind := 1; alen := 4 |}] = true.
  Proof.
    intros Hr0 Hr1 Hd0.
    unfold fall_through_new, fall_through_old, num_branches,
           primary_survived, all_same_length.
    cbn [akind alen filter length].
    rewrite Hr0, Hr1, Hd0.
    cbn.
    split; reflexivity.
  Qed.

  (* Concrete regression witness: the contextual guard alone forks the lone
     identifier branch, whereas the refined law restores the unrepresented
     fixed Set opener through normal dispatch. *)
  Theorem contextual_set_regression_and_repair :
    representable 0 = false ->
    representable 1 = true ->
    has_dispatch 0 = true ->
    is_contextual 0 = true ->
    fall_through_contextual_bug
      {| akind := 0; alen := 3 |} [{| akind := 1; alen := 3 |}] = false /\
    fall_through_refined
      {| akind := 0; alen := 3 |} [{| akind := 1; alen := 3 |}] = true.
  Proof.
    intros Hr0 Hr1 Hd0 Hc0.
    unfold fall_through_contextual_bug, fall_through_refined,
           fall_through_old, num_branches, primary_survived, all_same_length.
    cbn [akind alen filter length].
    rewrite Hr0, Hr1, Hd0, Hc0.
    cbn.
    split; reflexivity.
  Qed.

End LexForkKeywordReservation.

Module CollectionOpenFork.

Record CollectionEdge := {
  owner : nat;
  rule : nat;
  element : nat;
  continuation : nat;
  synthetic_paren : bool;
  alternative : nat;
  target : nat;
  edge_weight : nat
}.

Inductive OpenState :=
| ExpectParen (result rule_id element_id outer_bp : nat)
| ParseElement (position binding_power : nat).

Record CollectionBranch := {
  marker_owner : nat;
  marker_rule : nat;
  marker_slot : nat;
  marker_continuation : nat;
  next_state : OpenState;
  consume_target : nat;
  branch_weight : nat
}.

Definition open_branch (edge : CollectionEdge) : CollectionBranch :=
  {| marker_owner := owner edge;
     marker_rule := rule edge;
     marker_slot := 0;
     marker_continuation := continuation edge;
     next_state := if synthetic_paren edge
                   then ExpectParen (owner edge) (rule edge) (element edge) (continuation edge)
                   else ParseElement (target edge) 0;
     consume_target := target edge;
     branch_weight := edge_weight edge |}.

Inductive Route := Ordinary (witness : nat) | Collection (edge : CollectionEdge).
Inductive Branch := OrdinaryBranch (witness : nat) | CollectionOpening (branch : CollectionBranch).

Definition emit_before (routes : list Route) : list Branch :=
  flat_map (fun route => match route with
            | Ordinary witness => [OrdinaryBranch witness]
            | Collection _ => []
            end) routes.

Definition emit (routes : list Route) : list Branch :=
  map (fun route => match route with
       | Ordinary witness => OrdinaryBranch witness
       | Collection edge => CollectionOpening (open_branch edge)
       end) routes.

Definition fall_through (delimiter_yield : bool) (count : nat)
    (primary_survived primary_dispatch same_length contextual crosscat secondary_survived : bool)
    : bool :=
  negb delimiter_yield &&
  (Nat.eqb count 0 || (Nat.eqb count 1 && primary_survived) ||
   (primary_dispatch && same_length && (negb contextual || negb primary_survived)) ||
   (crosscat && same_length && negb secondary_survived)).

Theorem mixed_length_collection_was_lost : forall edge,
  emit_before [Collection edge; Ordinary 1; Ordinary 2] =
    [OrdinaryBranch 1; OrdinaryBranch 2] /\
  fall_through false 2 false true false false false true = false.
Proof. intros; split; reflexivity. Qed.

Theorem mixed_length_collection_is_retained : forall edge,
  In (CollectionOpening (open_branch edge))
     (emit [Collection edge; Ordinary 1; Ordinary 2]) /\
  fall_through false 3 true true false false false true = false.
Proof. intros; split; [left |]; reflexivity. Qed.

Theorem collection_no_loss : forall routes edge,
  In (Collection edge) routes -> In (CollectionOpening (open_branch edge)) (emit routes).
Proof. intros routes edge IN. apply in_map with (f := fun route => match route with
  | Ordinary witness => OrdinaryBranch witness
  | Collection value => CollectionOpening (open_branch value) end) in IN. exact IN. Qed.

Theorem ordinary_no_loss : forall routes witness,
  In (Ordinary witness) routes -> In (OrdinaryBranch witness) (emit routes).
Proof. intros routes witness IN. apply in_map with (f := fun route => match route with
  | Ordinary value => OrdinaryBranch value
  | Collection edge => CollectionOpening (open_branch edge) end) in IN. exact IN. Qed.

Theorem collection_no_invention : forall routes branch,
  In (CollectionOpening branch) (emit routes) ->
  exists edge, In (Collection edge) routes /\ branch = open_branch edge.
Proof.
  intros routes branch IN. apply in_map_iff in IN.
  destruct IN as [[witness|edge] [EQ IN]]; [discriminate |].
  inversion EQ; subst. exists edge. auto.
Qed.

Theorem rule_order_preserved : forall left right,
  emit (left ++ right) = emit left ++ emit right.
Proof. intros. apply map_app. Qed.

Theorem collection_marker_preserved : forall edge,
  marker_owner (open_branch edge) = owner edge /\
  marker_rule (open_branch edge) = rule edge /\
  marker_slot (open_branch edge) = 0 /\
  marker_continuation (open_branch edge) = continuation edge.
Proof. intros. repeat split; reflexivity. Qed.

Theorem collection_edge_preserved : forall edge,
  consume_target (open_branch edge) = target edge /\
  branch_weight (open_branch edge) = edge_weight edge.
Proof. intros. split; reflexivity. Qed.

Theorem synthetic_paren_is_required : forall edge,
  synthetic_paren edge = true ->
  next_state (open_branch edge) =
    ExpectParen (owner edge) (rule edge) (element edge) (continuation edge).
Proof. intros edge SYNTH. cbn. rewrite SYNTH. reflexivity. Qed.

Theorem direct_opener_starts_element : forall edge,
  synthetic_paren edge = false ->
  next_state (open_branch edge) = ParseElement (target edge) 0.
Proof. intros edge DIRECT. cbn. rewrite DIRECT. reflexivity. Qed.

Theorem primary_only_uses_normal_dispatch : forall contextual,
  fall_through false 1 true true true contextual false false = true.
Proof. intros. reflexivity. Qed.

Theorem contextual_same_length_keeps_both :
  fall_through false 2 true true true true false true = false.
Proof. reflexivity. Qed.

Print Assumptions mixed_length_collection_was_lost.
Print Assumptions mixed_length_collection_is_retained.
Print Assumptions collection_no_loss.
Print Assumptions ordinary_no_loss.
Print Assumptions collection_no_invention.
Print Assumptions rule_order_preserved.
Print Assumptions collection_marker_preserved.
Print Assumptions collection_edge_preserved.
Print Assumptions synthetic_paren_is_required.
Print Assumptions direct_opener_starts_element.
Print Assumptions primary_only_uses_normal_dispatch.
Print Assumptions contextual_same_length_keeps_both.

End CollectionOpenFork.
