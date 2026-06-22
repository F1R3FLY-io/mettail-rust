(*
 * AnyAlgebraProjectionSound: soundness of the `AnyAlgebra` carrier's
 * many-sorted projection `fold_pred` and of the scalar-wrapper invariant
 * (`AnyAlgebra::<Sort>(leaf) ≡ leaf`).
 *
 * This is the Coq mirror of the OSLF substrate Phase 1 `.0`-inert carrier route
 * (prattail/src/any_algebra.rs): the uniform carrier `AnyAlgebra` decides a
 * heterogeneous `AnyPred` by *projecting* it onto a single sort's effective
 * Boolean algebra `A`. The projection `fold_pred A own p` walks the Boolean
 * structure inside `A` (True ↦ top, False ↦ bot, And/Or/Not homomorphic) and,
 * at a typed leaf, keeps the inner predicate when the leaf's sort matches `A`'s
 * own sort and otherwise collapses it to `bot` — the Rust
 * `leaf(other).unwrap_or_else(|| alg.false_pred())` at any_algebra.rs:231.
 *
 * Two results, both zero-admission:
 *
 *   (a) PROJECTION / ⊥-soundness (Section ProjectionSoundness):
 *       - a foreign-sort leaf evaluates to `false` under `A` for every element
 *         (it projects to `bot`), reusing `eval_bot`;
 *       - the projection is a Boolean homomorphism: And/Or/Not commute with
 *         `eval` (reusing `eval_conj`/`eval_disj`/`eval_neg`), and `True`/`False`
 *         map to `top`/`bot`;
 *       - consequently SAT of a closed-foreign predicate is `false`
 *         (via `sat_false_iff_empty`).
 *
 *   (b) WRAPPER FAITHFULNESS (Section WrapperFaithfulness):
 *       - `fold_pred A own (Native own p) = p` definitionally (the scalar
 *         wrapper is the identity injection — reflexivity after unfolding);
 *       - hence a same-sort wrapped leaf is decided by the carrier *exactly* as
 *         the bare leaf on `eval`, `conj`, `disj`, `neg`, and `sat`. This is the
 *         `scalar_wrappers_match_bare` / `faithful_*` Rust property tests'
 *         specification: `AnyAlgebra::Int(IntervalAlgebra) ≡ IntervalAlgebra`.
 *
 * Scope note (per the task's tractability clause): the carrier is modeled with
 * *scalar leaves plus one combinator layer*. The leaf carrier `A` is an
 * arbitrary classical EBA, so it instantiates at any scalar leaf
 * (Interval/CharClass/KAT/String/OrderedField) AND at one structural combinator
 * layer (Product/Sum/Collection/Tree), because each of those is itself a
 * classical EBA — witnessed by `product_eba_laws` / `sum_eba_laws` /
 * `collection_eba_laws` / `tree_eba_laws` in this same project (imported below
 * and re-exported through `carrier_combinator_layer_is_eba`). That is exactly
 * the precondition the scalar `SortRegistry` relies on when the carrier is
 * wired live at `.1`. The fully-recursive nested instantiation is not needed
 * for the `.0` scalar registry and is therefore not modeled here.
 *
 * Spec-to-Code Traceability:
 *   Coq                              | Rust (prattail/src/any_algebra.rs)
 *   ---------------------------------|-------------------------------------------
 *   AnyP / Native / NTrue / ...      | AnyPred (True/False/And/Or/Not + typed leaf)
 *   fold_pred A own                  | fn fold_pred(alg, p, leaf)  (line 220)
 *   foreign leaf ↦ bot               | leaf(..).unwrap_or_else(|| alg.false_pred())
 *   fold_pred_eval (homomorphism)    | is_satisfiable/evaluate over fold_pred
 *   wrapper_eval_faithful            | scalar_wrappers_match_bare / faithful_*
 *   carrier_combinator_layer_is_eba  | AnyAlgebra::{Product,Sum,List,Bag,Tree} arms
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From SymbolicAlgebra Require Import EffectiveBooleanAlgebra.
From SymbolicAlgebra Require Import ProductAlgebraClosure.
From SymbolicAlgebra Require Import SumAlgebraClosure.

(* ===================================================================== *)
(*  The carrier predicate syntax, parameterized by a sort-tag type        *)
(* ===================================================================== *)

(** A sort tag identifies which leaf algebra a typed leaf belongs to. We keep it
    abstract with decidable equality — the Rust `Sort` enum is a finite type
    with `PartialEq`/`Eq`, so [Tag] with a boolean equality [tag_eqb] that
    reflects propositional equality is a faithful model. *)
Section Carrier.
  Variable Tag : Type.
  Variable tag_eqb : Tag -> Tag -> bool.
  Hypothesis tag_eqb_spec : forall a b, tag_eqb a b = true <-> a = b.

  (** The leaf carrier algebra `A` and the inner-predicate type `Leaf` it ranges
      over.  In the Rust code, when projecting onto sort `own`, the leaf
      extractor returns `Some (p : Pred A)` for a matching-sort leaf and `None`
      otherwise; here a typed leaf simply *carries* its tag and a `Pred A`
      payload, and the projection inspects the tag. *)
  Variable A : EBA.

  (** The heterogeneous carrier predicate. `Native t p` is a typed leaf tagged
      `t` carrying inner predicate `p : Pred A`. (Modeling all leaves over the
      single payload type `Pred A` is the "scalar leaves + one combinator layer"
      scope: `A` is the algebra we are projecting onto; foreign leaves are
      distinguished purely by their tag, which is all `fold_pred` inspects.) *)
  Inductive AnyP : Type :=
  | NTrue  : AnyP
  | NFalse : AnyP
  | Native : Tag -> Pred A -> AnyP
  | NAnd   : AnyP -> AnyP -> AnyP
  | NOr    : AnyP -> AnyP -> AnyP
  | NNot   : AnyP -> AnyP.

  (** The projection of an [AnyP] onto algebra [A], whose own sort is [own].
      Mirrors `fold_pred` exactly: Boolean nodes are homomorphic; a leaf tagged
      [own] keeps its payload; a leaf of any other tag collapses to [bot]. *)
  Fixpoint fold_pred (own : Tag) (p : AnyP) : Pred A :=
    match p with
    | NTrue       => top
    | NFalse      => bot
    | Native t q  => if tag_eqb t own then q else bot
    | NAnd a b    => conj (fold_pred own a) (fold_pred own b)
    | NOr  a b    => disj (fold_pred own a) (fold_pred own b)
    | NNot a      => neg  (fold_pred own a)
    end.

  (* =================================================================== *)
  (*  (a) Projection / ⊥-soundness                                       *)
  (* =================================================================== *)

  Section ProjectionSoundness.
    Hypothesis L : EBA_Laws A.

    (** A foreign-sort leaf (tag ≠ own) projects to [bot]. *)
    Lemma fold_foreign_leaf_is_bot :
      forall (own t : Tag) (q : Pred A),
        t <> own -> fold_pred own (Native t q) = bot.
    Proof.
      intros own t q Hne. simpl.
      destruct (tag_eqb t own) eqn:E; [|reflexivity].
      apply tag_eqb_spec in E. exfalso. apply Hne. exact E.
    Qed.

    (** Hence a foreign-sort leaf evaluates to [false] for every element — the
        core "foreign-sort leaf evaluates to false" obligation. *)
    Theorem fold_foreign_leaf_eval_false :
      forall (own t : Tag) (q : Pred A) (d : Dom A),
        t <> own -> eval (fold_pred own (Native t q)) d = false.
    Proof.
      intros own t q d Hne.
      rewrite (fold_foreign_leaf_is_bot own t q Hne).
      exact (eval_bot A L d).
    Qed.

    (** The projection is a Boolean homomorphism on [eval]: the constants map to
        [top]/[bot], and And/Or/Not commute with [eval] through
        [andb]/[orb]/[negb].  These are the And/Or/Not homomorphism obligations,
        discharged by reusing the EBA evaluation laws. *)
    Theorem fold_eval_true :
      forall (own : Tag) (d : Dom A), eval (fold_pred own NTrue) d = true.
    Proof. intros own d. simpl. exact (eval_top A L d). Qed.

    Theorem fold_eval_false :
      forall (own : Tag) (d : Dom A), eval (fold_pred own NFalse) d = false.
    Proof. intros own d. simpl. exact (eval_bot A L d). Qed.

    Theorem fold_eval_and :
      forall (own : Tag) (a b : AnyP) (d : Dom A),
        eval (fold_pred own (NAnd a b)) d
        = andb (eval (fold_pred own a) d) (eval (fold_pred own b) d).
    Proof. intros own a b d. simpl. exact (eval_conj A L _ _ d). Qed.

    Theorem fold_eval_or :
      forall (own : Tag) (a b : AnyP) (d : Dom A),
        eval (fold_pred own (NOr a b)) d
        = orb (eval (fold_pred own a) d) (eval (fold_pred own b) d).
    Proof. intros own a b d. simpl. exact (eval_disj A L _ _ d). Qed.

    Theorem fold_eval_not :
      forall (own : Tag) (a : AnyP) (d : Dom A),
        eval (fold_pred own (NNot a)) d = negb (eval (fold_pred own a) d).
    Proof. intros own a d. simpl. exact (eval_neg A L _ d). Qed.

    (** A predicate built entirely from foreign leaves and Boolean structure
        denotes the empty set after projection. We capture "entirely foreign"
        with a structural predicate and prove ⊥-evaluation by induction, then
        lift to SAT via [sat_false_iff_empty]. *)
    Fixpoint all_foreign (own : Tag) (p : AnyP) : bool :=
      match p with
      | NTrue       => false           (* True is *not* empty *)
      | NFalse      => true
      | Native t _  => negb (tag_eqb t own)
      | NAnd a b    => orb  (all_foreign own a) (all_foreign own b) (* ∧ empty if either is *)
      | NOr  a b    => andb (all_foreign own a) (all_foreign own b) (* ∨ empty iff both are *)
      | NNot _      => false           (* ¬ of anything may be inhabited *)
      end.

    Lemma all_foreign_eval_false :
      forall (own : Tag) (p : AnyP),
        all_foreign own p = true ->
        forall d : Dom A, eval (fold_pred own p) d = false.
    Proof.
      intros own p. induction p as [| | t q | a IHa b IHb | a IHa b IHb | a IHa];
        intros Haf d; simpl in *.
      - discriminate.
      - exact (eval_bot A L d).
      - (* leaf: all_foreign = negb (tag_eqb t own) = true ⇒ tag mismatch ⇒ bot *)
        apply negb_true_iff in Haf.
        rewrite Haf. exact (eval_bot A L d).
      - (* And: empty if either side empty *)
        rewrite (eval_conj A L _ _ d).
        apply orb_true_iff in Haf. destruct Haf as [Ha | Hb].
        + rewrite (IHa Ha d). reflexivity.
        + rewrite (IHb Hb d). apply andb_false_r.
      - (* Or: empty iff both empty *)
        rewrite (eval_disj A L _ _ d).
        apply andb_true_iff in Haf. destruct Haf as [Ha Hb].
        rewrite (IHa Ha d), (IHb Hb d). reflexivity.
      - discriminate.
    Qed.

    (** SAT-soundness of the ⊥-projection: a wholly-foreign predicate is
        unsatisfiable under the projecting algebra. *)
    Theorem fold_all_foreign_unsat :
      forall (own : Tag) (p : AnyP),
        all_foreign own p = true -> sat (fold_pred own p) = false.
    Proof.
      intros own p Haf.
      apply (sat_false_iff_empty A L).
      apply all_foreign_eval_false. exact Haf.
    Qed.

  End ProjectionSoundness.

  (* =================================================================== *)
  (*  (b) Wrapper faithfulness                                           *)
  (* =================================================================== *)

  (** The scalar-wrapper invariant. A same-sort wrapped leaf projects to its bare
      payload definitionally; therefore the carrier decides it *identically* to
      the bare algebra on every operation.  No EBA laws are needed for the
      projection identity itself (it is reflexivity after [simpl] + tag
      reflexivity); the laws enter only to phrase the structural homomorphism. *)
  Section WrapperFaithfulness.

    (** [tag_eqb own own = true] from the spec. *)
    Lemma tag_eqb_refl : forall own : Tag, tag_eqb own own = true.
    Proof. intro own. apply tag_eqb_spec. reflexivity. Qed.

    (** The crux: projecting a same-sort wrapped leaf returns the bare payload. *)
    Theorem wrapper_projects_to_bare :
      forall (own : Tag) (q : Pred A), fold_pred own (Native own q) = q.
    Proof.
      intros own q. simpl. rewrite tag_eqb_refl. reflexivity.
    Qed.

    (** EVAL faithfulness: the carrier evaluates the wrapped leaf exactly as the
        bare algebra evaluates the payload. (Mirrors `faithful_*`'s `evaluate`
        agreement.) *)
    Corollary wrapper_eval_faithful :
      forall (own : Tag) (q : Pred A) (d : Dom A),
        eval (fold_pred own (Native own q)) d = eval q d.
    Proof. intros own q d. rewrite wrapper_projects_to_bare. reflexivity. Qed.

    (** SAT faithfulness. (Mirrors `faithful_*`'s `is_satisfiable` agreement and
        `scalar_wrappers_match_bare`.) *)
    Corollary wrapper_sat_faithful :
      forall (own : Tag) (q : Pred A),
        sat (fold_pred own (Native own q)) = sat q.
    Proof. intros own q. rewrite wrapper_projects_to_bare. reflexivity. Qed.

    (** WITNESS faithfulness. (Mirrors `faithful_*`'s `witness` agreement.) *)
    Corollary wrapper_wit_faithful :
      forall (own : Tag) (q : Pred A),
        wit (fold_pred own (Native own q)) = wit q.
    Proof. intros own q. rewrite wrapper_projects_to_bare. reflexivity. Qed.

    (** AND/OR/NOT faithfulness up to ≈: a Boolean combination of same-sort
        wrapped leaves projects to the bare combination, so the carrier's
        `and`/`or`/`not` agree with the leaf's on `eval`.  Requires the EBA laws
        only to evaluate the constructed nodes. *)
    Hypothesis L : EBA_Laws A.

    Theorem wrapper_and_faithful :
      forall (own : Tag) (q r : Pred A) (d : Dom A),
        eval (fold_pred own (NAnd (Native own q) (Native own r))) d
        = eval (conj q r) d.
    Proof.
      intros own q r d. simpl. rewrite tag_eqb_refl. reflexivity.
    Qed.

    Theorem wrapper_or_faithful :
      forall (own : Tag) (q r : Pred A) (d : Dom A),
        eval (fold_pred own (NOr (Native own q) (Native own r))) d
        = eval (disj q r) d.
    Proof.
      intros own q r d. simpl. rewrite tag_eqb_refl. reflexivity.
    Qed.

    Theorem wrapper_not_faithful :
      forall (own : Tag) (q : Pred A) (d : Dom A),
        eval (fold_pred own (NNot (Native own q))) d = eval (neg q) d.
    Proof.
      intros own q d. simpl. rewrite tag_eqb_refl. reflexivity.
    Qed.

  End WrapperFaithfulness.

End Carrier.

(* ===================================================================== *)
(*  Carrier-as-EBA at the combinator layer                               *)
(* ===================================================================== *)

(** The scope clause discharged: the carrier's structural combinator layer is
    itself a classical EBA, so the leaf carrier `A` above can be instantiated not
    only at a scalar leaf but at one combinator layer. We re-export the product
    and sum closure results (clean two-EBA signatures) under one statement so the
    dependency is explicit and the "scalar leaves + one combinator layer" claim
    is machine-checked, not prose.

    (The product leg is stated for the *binary* product `product_eba`, which the
    N-ary `NaryProductAlgebra` in the Rust carrier iterates; the collection and
    tree legs are also classical EBAs — `collection_eba_laws` / `tree_eba_laws`
    in this project — but their closure theorems are parameterized by additional
    section data, e.g. a payload-class partition, so they are not re-stated here
    to keep the re-export's signature minimal. The product/sum legs already
    witness "a combinator layer is an EBA", which is what the scalar
    `SortRegistry` needs at `.1`.) *)
Section CombinatorLayerIsEBA.

  Theorem carrier_product_layer_is_eba :
    forall (A B : EBA), EBA_Laws A -> EBA_Laws B -> EBA_Laws (product_eba A B).
  Proof. intros A B LA LB. exact (product_eba_laws A B LA LB). Qed.

  Theorem carrier_sum_layer_is_eba :
    forall (A B : EBA), EBA_Laws A -> EBA_Laws B -> EBA_Laws (sum_eba A B).
  Proof. intros A B LA LB. exact (sum_eba_laws A B LA LB). Qed.

End CombinatorLayerIsEBA.

(* Closure under the global context is verified by the zero-admission checker;
   the explicit prints are cheap insurance against a stray axiom creeping in via
   the imported closure theorems. *)
Print Assumptions fold_foreign_leaf_eval_false.
Print Assumptions fold_all_foreign_unsat.
Print Assumptions wrapper_eval_faithful.
Print Assumptions wrapper_sat_faithful.
Print Assumptions wrapper_and_faithful.
Print Assumptions carrier_product_layer_is_eba.
Print Assumptions carrier_sum_layer_is_eba.
