(*
 * CollectionAcLowering: the canonicalization + lazy-selection model for the
 * in-engine associative-commutative (AC) lowering of collection (HashBag)
 * patterns — the Ambient `PPar` bag and its `OpenRule` AC redex.
 *
 * Two obligations are discharged here, both zero-admission:
 *
 * 1. CANONICALIZATION (no-collision / no-alias). A bag's children are modeled as
 *    a `list nat` (an injective ContentKey standin, exactly as
 *    NBestExtraction.v / EnumerationCompleteness.v model exact keys as `nat`).
 *    `canon := sort` (Stdlib Mergesort over nat). The central theorem
 *
 *        canon_iff_permutation : Permutation b b' <-> canon b = canon b'
 *
 *    proves two bags get the same canonical key IFF they are the same multiset
 *    (a permutation): no distinct multiset aliases onto another (dedup
 *    soundness), and no equal multiset splits into two keys (dedup
 *    completeness). This is exactly the order-invariance the Rust
 *    `ENode::ac_content_key` relies on (sort the child keys, then frame).
 *
 * 2. LAZY SUB-MULTISET SELECTION (no-miss / no-fabrication). `ac_select bag k`
 *    enumerates every `(selection, complement)` with a size-`k` sub-multiset
 *    selection and its multiset complement — mirroring `enum_vectors` of
 *    EnumerationCompleteness.v (single-index advance). Proven exhaustive
 *    (`ac_select_complete`) and sound (`ac_select_sound`), so the engine's lazy
 *    `lazy_ac_select` iterator misses no AC matching and fabricates none.
 *
 * The lowering's capability requirement is the already-covered
 * `ReqCollectionPattern` (-> CapPatternLowering); `ac_lowering_requirements_covered`
 * discharges it by reusing `every_requirement_constructor_is_covered` (NO new
 * requirement constructor is introduced).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorted.
From Stdlib Require Import Mergesort.
From Stdlib Require Import RelationClasses.

From Dovetail.Requirements Require Import MeTTaILRewriteCoverage.

Import ListNotations.

(* ════════════════════════════════════════════════════════════════════════ *)
(*  Part A — Canonicalization (canon := sort) and its no-alias guarantee      *)
(* ════════════════════════════════════════════════════════════════════════ *)

(* Stdlib's NatSort = Sort NatOrder gives `sort`, `Permuted_sort`,
   `StronglySorted_sort` (the latter needs `Transitive NatOrder.leb`). We work
   with NatOrder.leb directly and supply its order facts. *)
Import NatSort.

Section AcCanonicalization.

  Notation leb := NatOrder.leb.

  (* NatOrder.leb agrees with Nat.leb (its recursion is the same). *)
  Lemma natorder_leb_iff_nat_leb : forall x y, leb x y = Nat.leb x y.
  Proof.
    induction x as [| x' IH]; intros [| y']; simpl; auto.
  Qed.

  Lemma natorder_leb_antisym : forall x y,
    leb x y = true -> leb y x = true -> x = y.
  Proof.
    intros x y Hxy Hyx.
    rewrite natorder_leb_iff_nat_leb in Hxy, Hyx.
    apply Nat.leb_le in Hxy. apply Nat.leb_le in Hyx. lia.
  Qed.

  Lemma natorder_leb_trans : Transitive (fun x y => leb x y = true).
  Proof.
    intros x y z Hxy Hyz.
    rewrite natorder_leb_iff_nat_leb in Hxy, Hyz |- *.
    apply Nat.leb_le in Hxy. apply Nat.leb_le in Hyz.
    apply Nat.leb_le. lia.
  Qed.

  (* The canonical form of a bag: its mergesort. *)
  Definition canon (b : list nat) : list nat := sort b.

  (* `canon b` is a permutation of `b` (Stdlib's Permuted_sort). *)
  Lemma canon_perm : forall b, Permutation b (canon b).
  Proof. intro b. unfold canon. apply Permuted_sort. Qed.

  (* `canon b` is StronglySorted by NatOrder.leb (transitivity supplied). *)
  Lemma canon_strongly_sorted :
    forall b, StronglySorted (fun x y => leb x y = true) (canon b).
  Proof.
    intro b. unfold canon. apply StronglySorted_sort.
    exact natorder_leb_trans.
  Qed.

  (* ─────────────────────────────────────────────────────────────────────── *)
  (*  Generic: two StronglySorted permutations of each other are EQUAL.        *)
  (*  (Antisymmetry of `leb` + Permutation_cons_inv induction.)                *)
  (* ─────────────────────────────────────────────────────────────────────── *)

  (* The head of a StronglySorted list is `leb`-below every element of it. *)
  Lemma strongly_sorted_head_le :
    forall a l x,
      StronglySorted (fun p q => leb p q = true) (a :: l) ->
      In x (a :: l) -> leb a x = true.
  Proof.
    intros a l x Hss Hin.
    apply StronglySorted_inv in Hss as [_ Hall].
    destruct Hin as [Heq | Hin].
    - subst x.
      (* leb a a: NatOrder.leb is reflexive. *)
      rewrite natorder_leb_iff_nat_leb. apply Nat.leb_le. lia.
    - rewrite Forall_forall in Hall. apply Hall. exact Hin.
  Qed.

  Lemma strongly_sorted_perm_eq :
    forall l1 l2,
      StronglySorted (fun x y => leb x y = true) l1 ->
      StronglySorted (fun x y => leb x y = true) l2 ->
      Permutation l1 l2 ->
      l1 = l2.
  Proof.
    induction l1 as [| a1 l1' IH]; intros l2 Hss1 Hss2 Hperm.
    - (* l1 = [] : a permutation of [] is []. *)
      apply Permutation_nil in Hperm. symmetry. exact Hperm.
    - (* l1 = a1 :: l1'. l2 is non-empty (it is a permutation of a cons). *)
      destruct l2 as [| a2 l2'].
      + (* l2 = [] : impossible, [] cannot be a permutation of a cons. *)
        symmetry in Hperm. apply Permutation_nil in Hperm. discriminate.
      + (* Heads are equal by antisymmetry: a1 <= a2 and a2 <= a1. *)
        assert (Ha1_in_l2 : In a1 (a2 :: l2')).
        { apply (Permutation_in a1 Hperm). left. reflexivity. }
        assert (Ha2_in_l1 : In a2 (a1 :: l1')).
        { apply (Permutation_in a2 (Permutation_sym Hperm)). left. reflexivity. }
        assert (Hle12 : leb a1 a2 = true)
          by (apply (strongly_sorted_head_le a1 l1' a2 Hss1 Ha2_in_l1)).
        assert (Hle21 : leb a2 a1 = true)
          by (apply (strongly_sorted_head_le a2 l2' a1 Hss2 Ha1_in_l2)).
        assert (Heq : a1 = a2) by (apply natorder_leb_antisym; assumption).
        subst a2.
        (* Strip the equal heads and recurse. *)
        f_equal.
        apply IH.
        * apply StronglySorted_inv in Hss1. tauto.
        * apply StronglySorted_inv in Hss2. tauto.
        * apply Permutation_cons_inv with (a := a1). exact Hperm.
  Qed.

  (* ─────────────────────────────────────────────────────────────────────── *)
  (*  THE no-alias theorem.                                                    *)
  (* ─────────────────────────────────────────────────────────────────────── *)

  Theorem canon_iff_permutation : forall b b',
    Permutation b b' <-> canon b = canon b'.
  Proof.
    intros b b'. split.
    - (* forward: a permutation maps to the SAME canonical key. *)
      intro Hperm.
      (* canon b and canon b' are both StronglySorted and both permutations of
         the common multiset, hence permutations of each other; uniqueness
         gives equality. *)
      apply strongly_sorted_perm_eq.
      + apply canon_strongly_sorted.
      + apply canon_strongly_sorted.
      + (* canon b ~ b ~ b' ~ canon b' *)
        eapply Permutation_trans.
        * apply Permutation_sym. apply canon_perm.
        * eapply Permutation_trans.
          -- exact Hperm.
          -- apply canon_perm.
    - (* backward: equal canonical keys ⟹ the bags are permutations. *)
      intro Heq.
      (* b ~ canon b = canon b' ~ b' *)
      eapply Permutation_trans.
      + apply canon_perm.
      + rewrite Heq. apply Permutation_sym. apply canon_perm.
  Qed.

  (* Specializations made explicit for the spec narrative: *)

  (* No equal multiset is split into two keys (dedup COMPLETENESS). *)
  Corollary canon_collapses_permutations : forall b b',
    Permutation b b' -> canon b = canon b'.
  Proof. intros b b' H. apply canon_iff_permutation. exact H. Qed.

  (* No distinct multiset aliases onto another's key (dedup SOUNDNESS). *)
  Corollary canon_distinguishes_non_permutations : forall b b',
    canon b <> canon b' -> ~ Permutation b b'.
  Proof.
    intros b b' Hne Hperm. apply Hne. apply canon_iff_permutation. exact Hperm.
  Qed.

  (* Idempotence: canonicalizing an already-canonical bag is a no-op (the stored
     sorted order is stable). *)
  Corollary canon_idempotent : forall b, canon (canon b) = canon b.
  Proof.
    intro b. apply canon_iff_permutation. apply Permutation_sym. apply canon_perm.
  Qed.

End AcCanonicalization.

(* ════════════════════════════════════════════════════════════════════════ *)
(*  Part B — Lazy sub-multiset selection (no-miss / no-fabrication)           *)
(* ════════════════════════════════════════════════════════════════════════ *)

Section AcSelection.

  (* A selection of a bag is modeled the way a position-based lazy iterator
     actually produces it: `bag` is an INTERLEAVING (a split) of a chosen
     sub-sequence `sel` and the complementary sub-sequence `comp`. This is the
     faithful semantics of `lazy_ac_select`, which walks the bag's positions and,
     at each position, either TAKES the element into the selection or SKIPS it
     into the complement. `is_split bag sel comp` is exactly the take/skip merge.

     Both `sel` and `comp` are genuine sub-multisets of `bag` (multiset partition),
     and `comp` is the multiset complement of `sel` — captured precisely by
     `is_split` and the `split_permutation` lemma below. We state no-miss /
     no-fabrication against `is_split` (positional truth) and then connect to the
     multiset reading via `Permutation`. *)
  Inductive is_split : list nat -> list nat -> list nat -> Prop :=
    | Split_nil : is_split [] [] []
    | Split_take : forall x bag sel comp,
        is_split bag sel comp -> is_split (x :: bag) (x :: sel) comp
    | Split_skip : forall x bag sel comp,
        is_split bag sel comp -> is_split (x :: bag) sel (x :: comp).

  (* A split is a multiset partition: bag is a permutation of sel ++ comp. *)
  Lemma split_permutation : forall bag sel comp,
    is_split bag sel comp -> Permutation bag (sel ++ comp).
  Proof.
    intros bag sel comp Hsplit. induction Hsplit; simpl.
    - apply Permutation_refl.
    - apply perm_skip. exact IHHsplit.
    - (* x :: bag ~ sel ++ x :: comp : move x past sel. *)
      apply Permutation_cons_app. exact IHHsplit.
  Qed.

  (* The chosen sub-sequence and complement lengths sum to the bag length (no
     element is lost or duplicated by a split). *)
  Lemma split_length : forall bag sel comp,
    is_split bag sel comp -> length sel + length comp = length bag.
  Proof.
    intros bag sel comp Hsplit. induction Hsplit; simpl; lia.
  Qed.

  (* A skip-only split (empty selection) forces the complement to BE the bag. *)
  Lemma split_empty_sel : forall bag comp,
    is_split bag [] comp -> comp = bag.
  Proof.
    intros bag comp Hsplit.
    remember (@nil nat) as sel eqn:Hsel.
    induction Hsplit; subst.
    - reflexivity.
    - discriminate Hsel.
    - f_equal. apply IHHsplit. reflexivity.
  Qed.

  (* Dually, a take-only split (empty complement) forces the selection to BE the
     bag (every element taken). *)
  Lemma split_empty_comp : forall bag sel,
    is_split bag sel [] -> sel = bag.
  Proof.
    intros bag sel Hsplit.
    remember (@nil nat) as comp eqn:Hcomp.
    induction Hsplit; subst.
    - reflexivity.
    - f_equal. apply IHHsplit. reflexivity.
    - discriminate Hcomp.
  Qed.

  (* Every bag has the canonical skip-all split ([], bag) and take-all split
     (bag, []). The enumeration's base/extremal cases. *)
  Lemma split_skip_all : forall bag, is_split bag [] bag.
  Proof.
    induction bag as [| x xs IH]; simpl.
    - constructor.
    - apply Split_skip. exact IH.
  Qed.

  Lemma split_take_all : forall bag, is_split bag bag [].
  Proof.
    induction bag as [| x xs IH]; simpl.
    - constructor.
    - apply Split_take. exact IH.
  Qed.

  (* ─────────────────────────────────────────────────────────────────────── *)
  (*  The lazy enumeration.                                                    *)
  (*                                                                           *)
  (*  `select_lists bag k` = every size-k selection (sel, comp) that splits     *)
  (*  `bag`. Built by a single take-or-skip decision PER POSITION (mirroring     *)
  (*  enum_vectors's single-coordinate advance): at the head, either TAKE it     *)
  (*  (recurse for k-1) or SKIP it into the complement (recurse for k). The Rust *)
  (*  `lazy_ac_select` advances exactly this position lattice ONE step at a time. *)
  (* ─────────────────────────────────────────────────────────────────────── *)
  Fixpoint select_lists (bag : list nat) (k : nat)
    : list (list nat * list nat) :=
    match bag, k with
    | _, 0 => [ ([], bag) ]                  (* take none: all goes to complement *)
    | [], S _ => []                          (* cannot take from an empty bag *)
    | x :: xs, S k' =>
        (* TAKE x: prepend to every (k')-selection of xs. *)
        map (fun sc => (x :: fst sc, snd sc)) (select_lists xs k')
        ++
        (* SKIP x: push x into the complement of every (k)-selection of xs. *)
        map (fun sc => (fst sc, x :: snd sc)) (select_lists xs (S k'))
    end.

  (* The engine's `ac_select`: the take/skip selection enumeration. (The Rust
     side additionally enumerates permutations pairing fixed[i] to the selected
     children; that pairing layer is the existing positional `collect_matches`
     recursion, proven exhaustive by EnumerationCompleteness.v. Here we model the
     SET of (selection, complement) splits.) *)
  Definition ac_select (bag : list nat) (k : nat)
    : list (list nat * list nat) := select_lists bag k.

  (* ─────────────────────────────────────────────────────────────────────── *)
  (*  NO-MISS: every size-k split of the bag is enumerated.                    *)
  (* ─────────────────────────────────────────────────────────────────────── *)
  Lemma select_lists_complete : forall bag sel comp k,
    is_split bag sel comp -> length sel = k ->
    In (sel, comp) (select_lists bag k).
  Proof.
    intros bag sel comp k Hsplit. revert k.
    induction Hsplit; intros k Hlen; simpl in *.
    - (* Split_nil: sel = comp = [], k = 0. *)
      subst k. simpl. left. reflexivity.
    - (* Split_take: (x::bag) (x::sel) comp, length (x::sel) = k = S (length sel). *)
      destruct k as [| k']; [discriminate |].
      injection Hlen as Hlen'.
      apply in_or_app. left. apply in_map_iff.
      exists (sel, comp). split.
      + reflexivity.
      + apply IHHsplit. exact Hlen'.
    - (* Split_skip: (x::bag) sel (x::comp), length sel = k. *)
      destruct k as [| k'].
      + (* k = 0: the only size-0 selection is ([], bag); here sel = [] and the
           skip-only split forces comp = bag, so ([], x :: comp) = ([], x :: bag). *)
        destruct sel as [| s ss]; simpl in Hlen; [| discriminate].
        simpl. left.
        rewrite (split_empty_sel bag comp Hsplit). reflexivity.
      + (* k = S k': use the SKIP branch with the same k. *)
        apply in_or_app. right. apply in_map_iff.
        exists (sel, comp). split.
        * reflexivity.
        * apply IHHsplit. exact Hlen.
  Qed.

  Theorem ac_select_complete : forall bag k sel comp,
    is_split bag sel comp -> length sel = k ->
    In (sel, comp) (ac_select bag k).
  Proof.
    intros bag k sel comp Hsplit Hlen. unfold ac_select.
    apply select_lists_complete with (k := k); assumption.
  Qed.

  (* ─────────────────────────────────────────────────────────────────────── *)
  (*  NO-FABRICATION: every enumerated pair is a genuine size-k split.         *)
  (* ─────────────────────────────────────────────────────────────────────── *)
  Lemma select_lists_sound : forall bag k sel comp,
    In (sel, comp) (select_lists bag k) ->
    is_split bag sel comp /\ length sel = k.
  Proof.
    induction bag as [| x xs IH]; intros k sel comp Hin; simpl in Hin.
    - (* empty bag. *)
      destruct k as [| k'].
      + destruct Hin as [Heq | []]. inversion Heq. subst.
        split; [constructor | reflexivity].
      + contradiction.
    - (* bag = x :: xs. *)
      destruct k as [| k'].
      + (* k = 0: only ([], x::xs). *)
        destruct Hin as [Heq | []]. inversion Heq. subst.
        split; [apply split_skip_all | reflexivity].
      + (* k = S k': split into TAKE-branch ++ SKIP-branch. *)
        apply in_app_or in Hin. destruct Hin as [Htake | Hskip].
        * (* TAKE branch. *)
          apply in_map_iff in Htake. destruct Htake as [[stail ctail] [Heq Hin']].
          simpl in Heq. inversion Heq. subst sel comp.
          apply IH in Hin'. destruct Hin' as [Hsplit' Hlen'].
          split.
          -- apply Split_take. exact Hsplit'.
          -- simpl. rewrite Hlen'. reflexivity.
        * (* SKIP branch. *)
          apply in_map_iff in Hskip. destruct Hskip as [[stail ctail] [Heq Hin']].
          simpl in Heq. inversion Heq. subst sel comp.
          apply IH in Hin'. destruct Hin' as [Hsplit' Hlen'].
          split.
          -- apply Split_skip. exact Hsplit'.
          -- exact Hlen'.
  Qed.

  Theorem ac_select_sound : forall bag k sel comp,
    In (sel, comp) (ac_select bag k) ->
    is_split bag sel comp /\ length sel = k.
  Proof.
    intros bag k sel comp Hin. unfold ac_select in Hin.
    apply select_lists_sound. exact Hin.
  Qed.

  (* The exact bidirectional contract the engine's lazy_ac_select honors:
     membership in the enumeration IFF a genuine size-k split. *)
  Theorem ac_select_iff : forall bag k sel comp,
    In (sel, comp) (ac_select bag k) <->
    (is_split bag sel comp /\ length sel = k).
  Proof.
    intros bag k sel comp. split.
    - apply ac_select_sound.
    - intros [Hsplit Hlen]. apply ac_select_complete; assumption.
  Qed.

  (* Multiset reading of the result: for every enumerated (sel, comp), the bag is
     the multiset union of the selection and its complement (no element lost or
     fabricated) and the chosen count is exactly k. This is the `sub_multiset` /
     complement statement of the spec, recovered from the positional model. *)
  Theorem ac_select_partitions_bag : forall bag k sel comp,
    In (sel, comp) (ac_select bag k) ->
    Permutation bag (sel ++ comp) /\ length sel = k.
  Proof.
    intros bag k sel comp Hin.
    apply ac_select_sound in Hin. destruct Hin as [Hsplit Hlen].
    split.
    - apply split_permutation. exact Hsplit.
    - exact Hlen.
  Qed.

End AcSelection.

(* ════════════════════════════════════════════════════════════════════════ *)
(*  Part C — Associative flattening (bag-of-bags ≡ flat bag)                   *)
(* ════════════════════════════════════════════════════════════════════════ *)

(* Part A is the COMMUTATIVE half of AC (canon over multisets). This is the
   ASSOCIATIVE half: a constructed rewrite result that places a bag-valued
   binding into a new bag — e.g. opening `n[B | C]` yields `A | (B | C)` — must
   FLATTEN to one bag (`A | B | C`), matching the generated `normalize()`'s
   iterative `insert_into_<bag>`. The engine's `add_flattened_bag` peels every
   same-`op` layer; `bflatten` models that peel and is proven (i) an exact,
   multiplicity-preserving inlining (`bflatten_splice`, an equality) and (ii)
   stable under the Part-A canonicalization, so a re-associated result lowers to
   the SAME canonical bag key. *)
Section AcAssociativeFlatten.

  (* One constructed AC result member: a `BLeaf` is a non-`op` member kept
     intact; a `BBag` is a nested same-`op` collection whose members splice into
     the parent. *)
  Inductive btree : Type :=
    | BLeaf : nat -> btree
    | BBag  : list btree -> btree.

  (* Peel every `BBag` layer to the flat multiset (list) of leaves — exactly the
     engine's iterative `add_flattened_bag`. `flat_map` preserves each
     occurrence, so multiplicity is exact by construction. *)
  Fixpoint bflatten (t : btree) : list nat :=
    match t with
    | BLeaf n => n :: nil
    | BBag cs => flat_map bflatten cs
    end.

  (* Splicing a nested bag member inlines its leaves: the flat leaf-list is the
     SAME whether that member stays nested (`BBag ys` in place) or is spliced
     (`ys` inlined). An EQUALITY, so multiplicity is preserved exactly — a bag
     spliced as two siblings contributes its leaves twice. This is the
     associativity the engine's flatten relies on. *)
  Lemma bflatten_splice : forall (xs ys zs : list btree),
    bflatten (BBag (xs ++ BBag ys :: zs)) = bflatten (BBag (xs ++ ys ++ zs)).
  Proof.
    intros xs ys zs.
    cbn [bflatten].
    rewrite !flat_map_app.
    reflexivity.
  Qed.

  (* Flattening then canonicalizing (Part A) is invariant under re-association:
     a re-associated result lowers to the SAME canonical bag key. *)
  Theorem flatten_canon_assoc_invariant : forall (xs ys zs : list btree),
    canon (bflatten (BBag (xs ++ BBag ys :: zs)))
    = canon (bflatten (BBag (xs ++ ys ++ zs))).
  Proof.
    intros xs ys zs. f_equal. apply bflatten_splice.
  Qed.

End AcAssociativeFlatten.

(* ════════════════════════════════════════════════════════════════════════ *)
(*  Part D — Capability coverage (reuse, no new requirement constructor)      *)
(* ════════════════════════════════════════════════════════════════════════ *)

Section AcLoweringCoverage.

  (* The AC collection lowering's capability requirement is the already-covered
     `ReqCollectionPattern` (-> CapPatternLowering). No new requirement
     constructor is introduced; this discharges via the shared coverage lemma. *)
  Theorem ac_lowering_requirements_covered :
    requirement_covered ReqCollectionPattern.
  Proof. apply every_requirement_constructor_is_covered. Qed.

  (* The lowered AC node's identity remains an exact content key — same as any
     structural apply. Recorded so the GeneratedReportCompiler extension
     (GPatAcStructuralApply -> [ReqExactContentKey]) is covered here too. *)
  Theorem ac_node_identity_requirement_covered :
    requirement_covered ReqExactContentKey.
  Proof. apply every_requirement_constructor_is_covered. Qed.

End AcLoweringCoverage.
