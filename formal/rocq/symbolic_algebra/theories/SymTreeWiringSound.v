(*
 * SymTreeWiringSound: soundness of the OSLF substrate Phase 2 structural-type
 * recognizer wiring (prattail/src/structural_types.rs +
 * prattail/src/type_system/dispatch.rs::analyze_refinement_dispatch_structural,
 * feature `sym-tree-structural`).
 *
 * The `.1` wiring decides STRUCTURAL refinement-type dispatch by compiling each
 * refinement pattern into a `SymbolicTreeAutomaton<AnyAlgebra>` over the
 * grammar's ranked alphabet (the Rust `structural_types::category_automaton` /
 * `refined_automaton`), then classifying a pair (A,B) by three tree-automaton
 * emptiness checks:
 *
 *     Disjoint  iff  is_empty(A ∩ B)            (* A.intersect(&B).is_empty() *)
 *     Subtype   iff  is_empty(A ∩ ¬B)           (* A.intersect(&B.complement()) *)
 *     else Overlapping
 *
 * and (`.0`) decides per-category inhabitation by `is_empty` of the category
 * automaton, proven to AGREE with the finite `SetTheoreticTypeSystem` verdict
 * over the same ranked alphabet (prattail/tests/sym_tree_structural_snapshot.rs).
 *
 * The decision substrate is the tree effective Boolean algebra `tree_eba` of
 * `TreeAlgebraClosure.v` — a tree predicate is a deterministic, complete,
 * bottom-up tree automaton over the payload minterm classes; `tconj` is the
 * product (∩), `tneg` is the (single) final-flip (¬ over the alphabet), `tsat`
 * is bottom-up saturation emptiness, and `tree_eba_laws` fixes their meaning.
 * This file lifts those algebra laws into the three decision-level soundness
 * theorems the wiring relies on, ZERO-ADMISSION:
 *
 *   (1) DECISION SOUNDNESS (Section DecisionSoundness):
 *       - `sat ↔ ¬empty`        : `tsat M = false ↔ ∀ t, teval M t = false`
 *                                 (`sat_empty_iff`, reusing `sat_false_iff_empty`).
 *       - DISJOINTNESS          : `tsat (tconj A B) = false`
 *                                 ↔ `∀ t, ¬ (teval A t = true ∧ teval B t = true)`
 *                                 (`disjoint_iff`; conj = product, via
 *                                 `teval_tconj`). This is the Rust `Disjoint` arm.
 *       - SUBTYPE               : `decides_subtype A B = true`
 *                                 ↔ `∀ t, teval A t = true → teval B t = true`
 *                                 (`subtype_iff`; A ∩ ¬B = ∅, neg = final-flip via
 *                                 `teval_tneg`). This is the Rust `Subtype` arm,
 *                                 and it is EXACTLY `decides_implies` on `tree_eba`.
 *       - the two are mutually exclusive on an INHABITED A
 *                                 (`disjoint_subtype_exclusive`): a disjoint pair
 *                                 with A inhabited is not also a subtype — the Rust
 *                                 dispatch returns at most one verdict.
 *
 *   (2) FINITE-ALPHABET AGREEMENT (Section FiniteAgreement):
 *       Over the TRIVIAL single-class (`True`) payload partition (`Sigma := unit`,
 *       `letter := fun _ => tt`, `pick tt := Some d0`), the sym_tree emptiness
 *       verdict equals the finite tree-automaton verdict — both are "no accepted
 *       term exists". Formally `tsat M = true ↔ ∃ t, teval M t = true`
 *       (`finite_agreement`), the single-class instance being witnessed
 *       non-vacuous by `unit_partition_ok`. This is the `.0` snapshot's theorem:
 *       under a trivially-satisfiable payload partition the tree recognizer's
 *       inhabitation verdict coincides with the finite engine's reachability
 *       verdict.
 *
 *   (3) PAYLOAD-GUARD FAITHFULNESS (Section PayloadFaithfulness):
 *       The Tree combinator layer is itself a classical EBA (`tree_layer_is_eba`,
 *       = `tree_eba_laws`), so the carrier may project onto a Tree leaf; and a
 *       same-sort wrapped Tree leaf is decided by the carrier EXACTLY as the bare
 *       Tree algebra (`tree_payload_sat_faithful`, instantiating
 *       `wrapper_sat_faithful` from AnyAlgebraProjectionSound.v at `A := tree_eba`).
 *       This is the precondition that lets `build_tree_algebra`'s
 *       `AnyAlgebra::Tree(TreeAlgebra::new(...))` carry a payload guard whose
 *       SAT the carrier decides faithfully.
 *
 * Spec-to-Code Traceability:
 *   Coq                                  | Rust
 *   -------------------------------------|------------------------------------------
 *   tree_eba / teval / tsat              | SymbolicTreeAutomaton / accepts / !is_empty
 *   tconj (product)                      | SymbolicTreeAutomaton::intersect
 *   tneg  (final flip)                   | SymbolicTreeAutomaton::complement
 *   disjoint_iff                         | dispatch.rs Disjoint  (A∩B is_empty)
 *   decides_subtype / subtype_iff        | dispatch.rs Subtype   (A∩¬B is_empty)
 *   disjoint_subtype_exclusive           | dispatch.rs: at most one verdict per pair
 *   finite_agreement (unit partition)    | structural_verdict ≡ SetTheoreticTypeSystem
 *                                        |   (sym_tree_structural_snapshot.rs)
 *   tree_payload_sat_faithful            | build_tree_algebra payloaded leaf guard
 *
 * Reuses (all zero-admission, registered in this project's _CoqProject):
 *   - EffectiveBooleanAlgebra.v : EBA, EBA_Laws, sat_false_iff_empty,
 *                                 decides_implies, implies_correct.
 *   - TreeAlgebraClosure.v      : DTree, DFTA, teval, tconj, tneg, tsat,
 *                                 tree_eba, tree_eba_laws, tsat_sound/complete,
 *                                 teval_tconj, teval_tneg.
 *   - AnyAlgebraProjectionSound.v : wrapper_sat_faithful (carrier = leaf decision).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

From SymbolicAlgebra Require Import EffectiveBooleanAlgebra.
From SymbolicAlgebra Require Import TreeAlgebraClosure.
From SymbolicAlgebra Require Import AnyAlgebraProjectionSound.

(* ===================================================================== *)
(*  The tree-EBA instance and its decision procedures                    *)
(* ===================================================================== *)

(* We work over the SAME section data as [TreeAlgebraClosure.Tree]: a payload EBA
   [A] with laws, and a finite, complete, inhabited minterm partition [Sigma].
   The exported [tree_eba] / [tsat] / [tconj] / [tneg] / [teval] / [tree_eba_laws]
   are generalized over exactly these, so we re-fix them here and instantiate the
   exported names once. *)
Section Decisions.
  Variable A : EBA.
  Variable Sigma : Type.
  Variable sig_enum : list Sigma.
  Variable sig_all : forall s : Sigma, In s sig_enum.
  Variable letter : Dom A -> Sigma.
  Variable pick : Sigma -> option (Dom A).
  Hypothesis pick_letter : forall s d, pick s = Some d -> letter d = s.
  Hypothesis pick_total : forall s, In s sig_enum -> exists d, pick s = Some d.

  (* Instantiate the exported tree-EBA and its laws at this section's data. The
     exported argument order is [tree_eba A Sigma sig_enum letter pick] and
     [tree_eba_laws A Sigma sig_enum sig_all letter pick pick_letter pick_total]
     ([sig_eqdec] is NOT a parameter of the computational [tree_eba]; the EBA
     [conj]/[neg]/[sat]/[eval] projections carry everything else). *)
  Let TEBA : EBA :=
    tree_eba A Sigma sig_enum letter pick.
  Let TL : EBA_Laws TEBA :=
    tree_eba_laws A Sigma sig_enum sig_all letter pick pick_letter pick_total.

  (* The tree predicate / domain / decisions, as the EBA projections of [TEBA].
     [Pred TEBA = DFTA …] and [Dom TEBA = DTree …] definitionally, and
     [sat TEBA = tsat …], [conj TEBA = tconj …], [neg TEBA = tneg …],
     [eval TEBA = teval …]; we phrase everything through the EBA interface so the
     reused EBA lemmas apply verbatim. *)

  (* =================================================================== *)
  (*  (1) Decision soundness                                             *)
  (* =================================================================== *)

  Section DecisionSoundness.

    (** sat ↔ ¬empty: a tree automaton is unsatisfiable exactly when it accepts
        no term. This is the `!is_empty` ⇔ `tsat` correspondence the Rust
        `is_empty` relies on, lifted from the generic `sat_false_iff_empty`. *)
    Theorem sat_empty_iff :
      forall M : Pred TEBA,
        sat M = false <-> (forall t : Dom TEBA, eval M t = false).
    Proof.
      intro M. exact (sat_false_iff_empty TEBA TL M).
    Qed.

    (** DISJOINTNESS (the Rust `Disjoint` arm): the product automaton `A ∩ B` is
        empty exactly when no term is accepted by both. `conj = product` is
        `teval_tconj`, then `sat_false_iff_empty`. *)
    Theorem disjoint_iff :
      forall P Q : Pred TEBA,
        sat (conj P Q) = false
        <-> (forall t : Dom TEBA, ~ (eval P t = true /\ eval Q t = true)).
    Proof.
      intros P Q. rewrite (sat_false_iff_empty TEBA TL).
      split.
      - intros Hempty t [HP HQ].
        specialize (Hempty t). rewrite (eval_conj TEBA TL) in Hempty.
        rewrite HP, HQ in Hempty. discriminate.
      - intros Hno t. rewrite (eval_conj TEBA TL).
        destruct (eval P t) eqn:EP; destruct (eval Q t) eqn:EQ; try reflexivity.
        exfalso. apply (Hno t). split; [exact EP | exact EQ].
    Qed.

    (** The SUBTYPE decision (the Rust `Subtype` arm): A ⊆ B iff `A ∩ ¬B = ∅`.
        This is *literally* `decides_implies` on the tree EBA. *)
    Definition decides_subtype (P Q : Pred TEBA) : bool := decides_implies TEBA P Q.

    Theorem subtype_iff :
      forall P Q : Pred TEBA,
        decides_subtype P Q = true
        <-> (forall t : Dom TEBA, eval P t = true -> eval Q t = true).
    Proof.
      intros P Q. unfold decides_subtype. exact (implies_correct TEBA TL P Q).
    Qed.

    (** Disjointness and subtype are mutually exclusive when A is INHABITED: a
        disjoint pair (A∩B=∅) with A inhabited cannot also satisfy A⊆B, because
        an inhabitant of A would then lie in B, contradicting disjointness. Hence
        the Rust dispatch returns at most one of `Disjoint` / `Subtype` for an
        inhabited refinement. *)
    Theorem disjoint_subtype_exclusive :
      forall P Q : Pred TEBA,
        sat (conj P Q) = false ->
        (exists t : Dom TEBA, eval P t = true) ->
        decides_subtype P Q = false.
    Proof.
      intros P Q Hdisj [t0 Ht0].
      destruct (decides_subtype P Q) eqn:Hsub; [|reflexivity].
      exfalso.
      (* From the subtype decision: t0 ∈ A ⇒ t0 ∈ B. *)
      pose proof ((proj1 (subtype_iff P Q)) Hsub t0 Ht0) as HQ0.
      (* From disjointness: t0 cannot be in both A and B. *)
      pose proof ((proj1 (disjoint_iff P Q)) Hdisj t0) as Hno0.
      apply Hno0. split; [exact Ht0 | exact HQ0].
    Qed.

    (** SAT soundness/completeness restated through the EBA (the bottom-up
        saturation `tsat` decides inhabitation), for downstream callers. *)
    Theorem subtype_sat_sound :
      forall M : Pred TEBA, sat M = true -> exists t : Dom TEBA, eval M t = true.
    Proof. intro M. exact (sat_sound TEBA TL M). Qed.

    Theorem subtype_sat_complete :
      forall (M : Pred TEBA) (t : Dom TEBA), eval M t = true -> sat M = true.
    Proof. intros M t. exact (sat_complete TEBA TL M t). Qed.

  End DecisionSoundness.

End Decisions.

(* ===================================================================== *)
(*  (2) Finite-alphabet agreement (trivial single-class partition)        *)
(* ===================================================================== *)

(* The `.0` snapshot theorem: over a trivially-satisfiable single-class payload
   partition, the sym_tree inhabitation verdict equals the finite engine's. We
   instantiate the tree EBA with `Sigma := unit` (one class), `letter := fun _ =>
   tt`, and `pick tt := Some d0` for a fixed payload `d0` — i.e. every payload is
   in the one always-satisfiable class — and show `tsat` characterizes
   inhabitation exactly (which is what `SetTheoreticTypeSystem::is_empty`,
   negated, computes). *)
Section FiniteAgreement.
  Variable A : EBA.
  (* A fixed payload inhabits the single class (the partition's [pick] witness);
     the structural recognizer's payloaded leaves carry the always-satisfiable
     `True` guard, whose witness exists — this [d0] is its Coq image. *)
  Variable d0 : Dom A.

  Definition u_enum : list unit := [tt].
  Lemma u_all : forall s : unit, In s u_enum.
  Proof. intro s. destruct s. left. reflexivity. Qed.
  Definition u_letter : Dom A -> unit := fun _ => tt.
  Definition u_pick : unit -> option (Dom A) := fun _ => Some d0.

  Lemma u_pick_letter : forall s d, u_pick s = Some d -> u_letter d = s.
  Proof. intros [] d _. reflexivity. Qed.
  Lemma u_pick_total : forall s, In s u_enum -> exists d, u_pick s = Some d.
  Proof. intros [] _. exists d0. reflexivity. Qed.

  (** The single-class partition is a valid (complete + inhabited) partition
      instance, so the agreement theorem below is NON-vacuous: the tree EBA over
      it is well-formed. *)
  Theorem unit_partition_ok :
    EBA_Laws (tree_eba A unit u_enum u_letter u_pick).
  Proof.
    exact (tree_eba_laws A unit u_enum u_all u_letter u_pick
                         u_pick_letter u_pick_total).
  Qed.

  Let UTEBA : EBA := tree_eba A unit u_enum u_letter u_pick.

  (** FINITE AGREEMENT: over the single-class partition, the sym_tree emptiness
      verdict coincides with the finite reachability verdict — `tsat M = true`
      iff some term is accepted. Both engines decide "is the category inhabited?"
      by the SAME bottom-up reachability (the payload class is always satisfiable,
      so it never prunes a derivation), so their (negated) emptiness verdicts are
      equal. *)
  Theorem finite_agreement :
    forall M : Pred UTEBA,
      sat M = true <-> (exists t : Dom UTEBA, eval M t = true).
  Proof.
    intro M. exact (sat_true_iff_inhabited UTEBA unit_partition_ok M).
  Qed.

  (** The dual phrasing the Rust `is_empty` returns: empty iff no inhabitant. *)
  Corollary finite_agreement_empty :
    forall M : Pred UTEBA,
      sat M = false <-> (forall t : Dom UTEBA, eval M t = false).
  Proof.
    intro M. exact (sat_false_iff_empty UTEBA unit_partition_ok M).
  Qed.

End FiniteAgreement.

(* ===================================================================== *)
(*  (3) Payload-guard faithfulness at the Tree combinator layer           *)
(* ===================================================================== *)

(* The carrier `AnyAlgebra` may project onto a Tree leaf because the Tree
   combinator layer is itself a classical EBA, and a same-sort wrapped Tree leaf
   is decided by the carrier exactly as the bare Tree algebra. We re-export the
   Tree-layer EBA witness and instantiate `wrapper_sat_faithful` at the tree EBA. *)
Section PayloadFaithfulness.
  Variable A : EBA.
  Variable Sigma : Type.
  Variable sig_enum : list Sigma.
  Variable sig_all : forall s : Sigma, In s sig_enum.
  Variable letter : Dom A -> Sigma.
  Variable pick : Sigma -> option (Dom A).
  Hypothesis pick_letter : forall s d, pick s = Some d -> letter d = s.
  Hypothesis pick_total : forall s, In s sig_enum -> exists d, pick s = Some d.

  Let TEBA : EBA := tree_eba A Sigma sig_enum letter pick.

  (** The Tree combinator layer is a classical EBA (so the carrier `AnyAlgebra`
      can hold a `Tree` leaf and project onto it). This is the Tree analogue of
      `carrier_product_layer_is_eba` / `carrier_sum_layer_is_eba`. *)
  Theorem tree_layer_is_eba : EBA_Laws TEBA.
  Proof.
    exact (tree_eba_laws A Sigma sig_enum sig_all letter pick
                         pick_letter pick_total).
  Qed.

  (* The carrier's sort-tag model: at least a `Tree` tag, with decidable
     equality (the Rust `Sort` enum is finite with `Eq`). Two tags suffice to
     witness "same-sort wrapped leaf is faithful, foreign leaf is not". *)
  Inductive STag := TreeTag | OtherTag.
  Definition stag_eqb (a b : STag) : bool :=
    match a, b with
    | TreeTag, TreeTag => true
    | OtherTag, OtherTag => true
    | _, _ => false
    end.
  Lemma stag_eqb_spec : forall a b, stag_eqb a b = true <-> a = b.
  Proof.
    intros [] []; simpl; split; intro H; try reflexivity; try discriminate.
  Qed.

  (** PAYLOAD-GUARD FAITHFULNESS: a same-sort (Tree) wrapped leaf carrying a tree
      predicate `q` is decided by the carrier's projection EXACTLY as the bare
      tree EBA decides `q` (on SAT). This is `wrapper_sat_faithful` instantiated
      at `A := TEBA` and the Tree tag — the precondition that
      `build_tree_algebra`'s `AnyAlgebra::Tree(...)` leaf-guard SAT is faithful. *)
  Theorem tree_payload_sat_faithful :
    forall (q : Pred TEBA),
      sat (fold_pred STag stag_eqb TEBA TreeTag (Native STag TEBA TreeTag q)) = sat q.
  Proof.
    intro q.
    exact (wrapper_sat_faithful STag stag_eqb stag_eqb_spec TEBA TreeTag q).
  Qed.

  (** EVAL faithfulness at the Tree layer (the witness/accept side): the carrier
      evaluates the wrapped tree leaf exactly as the bare tree EBA. *)
  Theorem tree_payload_eval_faithful :
    forall (q : Pred TEBA) (t : Dom TEBA),
      eval (fold_pred STag stag_eqb TEBA TreeTag (Native STag TEBA TreeTag q)) t
      = eval q t.
  Proof.
    intros q t.
    exact (wrapper_eval_faithful STag stag_eqb stag_eqb_spec TEBA TreeTag q t).
  Qed.

End PayloadFaithfulness.

(* Closure under the global context is verified by the zero-admission checker;
   the explicit prints are cheap insurance against a stray axiom leaking in via
   the imported tree-EBA / carrier lemmas. *)
Print Assumptions sat_empty_iff.
Print Assumptions disjoint_iff.
Print Assumptions subtype_iff.
Print Assumptions disjoint_subtype_exclusive.
Print Assumptions unit_partition_ok.
Print Assumptions finite_agreement.
Print Assumptions finite_agreement_empty.
Print Assumptions tree_layer_is_eba.
Print Assumptions tree_payload_sat_faithful.
Print Assumptions tree_payload_eval_faithful.
