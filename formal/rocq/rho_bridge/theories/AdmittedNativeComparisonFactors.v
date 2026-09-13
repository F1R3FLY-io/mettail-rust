(** Concrete comparison recipes for the audited native leaf schema.
    The pinned Rust integer intrinsic denotes signed/unsigned comparison;
    String's derived Vec<u8> field uses unsigned-byte lexicographic ordering;
    struct/enum derives use declaration order; Arc forwards to its payload.
    These primitive/compiler interpretations are the source-correspondence
    trust boundary, NOT a compiler correctness theorem proved here.
    This file defines the source equations rather than assuming that an
    arbitrary execute_native result factors through a key.

    uid_digest and binder_digest interpret the distinct fixed DefaultHasher
    expressions. Determinism suffices: no injectivity or source Eq/Ord
    coherence is assumed. Views are proof-only, not runtime representations. *)
From Stdlib Require Import List Arith.PeanoNat Bool ZArith Lia.
From RuntimeGrammar Require Import SemanticComparisonLaws.
From RhoBridge Require Import AdmittedStructuralKeyHash AdmittedComparisonClasses.
Import ListNotations.
Module AdmittedNativeComparisonFactors.

Theorem signed_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws Z.compare.
Proof.
  constructor; [apply Z.compare_eq_iff | apply Z.compare_antisym |].
  intros x y z c H1 H2. destruct c.
  - apply Z.compare_eq_iff in H1, H2. apply Z.compare_eq_iff. congruence.
  - apply Z.compare_lt_iff in H1, H2. apply Z.compare_lt_iff.
    exact (Z.lt_trans x y z H1 H2).
  - apply Z.compare_gt_iff in H1, H2. apply Z.compare_gt_iff.
    exact (Z.lt_trans z y x H2 H1).
Qed.
Definition signed_source_compare := Z.compare.
Theorem signed_factor : forall x y,
  signed_source_compare x y = Z.compare x y.
Proof. reflexivity. Qed.
Definition bool_key (b : bool) : nat := if b then 1 else 0.
Definition bool_source_compare (x y : bool) : comparison :=
  if x then (if y then Eq else Gt) else (if y then Lt else Eq).
Theorem bool_factor : forall x y,
  bool_source_compare x y = Nat.compare (bool_key x) (bool_key y).
Proof. intros [] []; reflexivity. Qed.
Definition bytes_compare := list_compare Nat.compare.
Theorem bytes_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws bytes_compare.
Proof. apply SemanticComparisonLaws.SemanticComparisonLaws.list_laws. exact SemanticComparisonLaws.SemanticComparisonLaws.natural_laws. Qed.
(** The semantic byte primitive, not a reimplementation or machine-work bound. *)
Definition string_source_compare : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.ByteString -> AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.ByteString -> comparison :=
  bytes_compare.
Theorem string_factor : forall x y,
  string_source_compare x y = bytes_compare x y.
Proof. reflexivity. Qed.

Section IdentityAndFlt.
Variables uid_digest binder_digest : nat -> nat.
Definition VarKey := (nat + (nat * nat))%type.
Definition var_key (v : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.MonikerVar) : VarKey :=
  match v with
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Free identity _ => inl (uid_digest identity)
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Bound scope index _ => inr (scope, index)
  end.
Definition var_key_compare :=
  SemanticComparisonLaws.SemanticComparisonLaws.sum_compare Nat.compare (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare Nat.compare Nat.compare).
Definition ordvar_source_compare (x y : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.MonikerVar) : comparison :=
  match x, y with
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Free a _, AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Free b _ => Nat.compare (uid_digest a) (uid_digest b)
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Free _ _, AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Bound _ _ _ => Lt
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Bound _ _ _, AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Free _ _ => Gt
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Bound s i _, AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Bound t j _ => SemanticComparisonLaws.SemanticComparisonLaws.lex (Nat.compare s t) (Nat.compare i j)
  end.
Theorem ordvar_factor : forall x y,
  ordvar_source_compare x y = var_key_compare (var_key x) (var_key y).
Proof. intros [] []; reflexivity. Qed.
Theorem var_key_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws var_key_compare.
Proof.
  apply SemanticComparisonLaws.SemanticComparisonLaws.sum_laws; [exact SemanticComparisonLaws.SemanticComparisonLaws.natural_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; exact SemanticComparisonLaws.SemanticComparisonLaws.natural_laws.
Qed.
Definition binder_key (b : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Binder) := binder_digest (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.binder_identity b).
Definition single_pattern_source_compare (x y : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Binder) :=
  Nat.compare (binder_digest (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.binder_identity x)) (binder_digest (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.binder_identity y)).
Theorem single_pattern_factor : forall x y,
  single_pattern_source_compare x y = Nat.compare (binder_key x) (binder_key y).
Proof. reflexivity. Qed.
Definition non_equal (c : comparison) := match c with Eq => false | _ => true end.
Definition first_non_equal (cs : list comparison) : comparison :=
  match find non_equal cs with Some c => c | None => Eq end.
Lemma first_non_equal_cons : forall c cs,
  first_non_equal (c :: cs) = SemanticComparisonLaws.SemanticComparisonLaws.lex c (first_non_equal cs).
Proof. intros [] cs; reflexivity. Qed.
Definition zipped_pattern_compare (xs ys : list AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Binder) :=
  first_non_equal
    (map (fun p => Nat.compare (binder_key (fst p)) (binder_key (snd p)))
      (combine xs ys)).
Lemma equal_length_zip_find_factor : forall xs ys,
  length xs = length ys ->
  zipped_pattern_compare xs ys =
    list_compare Nat.compare (map binder_key xs) (map binder_key ys).
Proof.
  induction xs as [|x xs IH]; intros [|y ys] E; try discriminate.
  - reflexivity.
  - injection E as E. unfold zipped_pattern_compare in *.
    cbn [combine map fst snd]. rewrite first_non_equal_cons.
    cbn [list_compare]. rewrite (IH ys E).
    destruct (Nat.compare (binder_key x) (binder_key y)); reflexivity.
Qed.
Definition multi_pattern_key (xs : list AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Binder) := (length xs, map binder_key xs).
Definition multi_pattern_key_compare := SemanticComparisonLaws.SemanticComparisonLaws.pair_compare Nat.compare (list_compare Nat.compare).
Definition multi_pattern_source_compare (xs ys : list AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.Binder) :=
  SemanticComparisonLaws.SemanticComparisonLaws.lex (Nat.compare (length xs) (length ys)) (zipped_pattern_compare xs ys).
Theorem multi_pattern_factor : forall xs ys,
  multi_pattern_source_compare xs ys =
    multi_pattern_key_compare (multi_pattern_key xs) (multi_pattern_key ys).
Proof.
  intros xs ys. unfold multi_pattern_source_compare, multi_pattern_key_compare,
    multi_pattern_key, SemanticComparisonLaws.SemanticComparisonLaws.pair_compare. cbn [fst snd].
  destruct (Nat.compare (length xs) (length ys)) eqn:E; cbn [SemanticComparisonLaws.SemanticComparisonLaws.lex].
  - apply equal_length_zip_find_factor. now apply Nat.compare_eq_iff in E.
  - reflexivity.
  - reflexivity.
Qed.
Theorem multi_pattern_key_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws multi_pattern_key_compare.
Proof.
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [exact SemanticComparisonLaws.SemanticComparisonLaws.natural_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.list_laws. exact SemanticComparisonLaws.SemanticComparisonLaws.natural_laws.
Qed.
Definition range_key (r : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltRange) := (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.range_start r, AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.range_end r).
Definition range_key_compare := SemanticComparisonLaws.SemanticComparisonLaws.pair_compare Nat.compare Nat.compare.
Definition range_source_compare (a b : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltRange) :=
  SemanticComparisonLaws.SemanticComparisonLaws.lex (Nat.compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.range_start a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.range_start b))
    (Nat.compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.range_end a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.range_end b)).
Theorem range_factor : forall a b,
  range_source_compare a b = range_key_compare (range_key a) (range_key b).
Proof. reflexivity. Qed.
Theorem range_key_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws range_key_compare.
Proof. apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; exact SemanticComparisonLaws.SemanticComparisonLaws.natural_laws. Qed.
Definition bounds_key (b : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltBounds) :=
  (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.source_bytes b, (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.body_bytes b, (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.piece_count b,
    (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_declarations b, AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_occurrences b)))).
Definition bounds_key_compare := SemanticComparisonLaws.SemanticComparisonLaws.pair_compare Nat.compare
  (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare Nat.compare (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare Nat.compare
    (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare Nat.compare Nat.compare))).
Definition bounds_source_compare (a b : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltBounds) :=
  SemanticComparisonLaws.SemanticComparisonLaws.lex (Nat.compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.source_bytes a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.source_bytes b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (Nat.compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.body_bytes a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.body_bytes b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (Nat.compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.piece_count a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.piece_count b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (Nat.compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_declarations a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_declarations b))
    (Nat.compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_occurrences a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_occurrences b))))).
Theorem bounds_factor : forall a b,
  bounds_source_compare a b = bounds_key_compare (bounds_key a) (bounds_key b).
Proof. reflexivity. Qed.
Theorem bounds_key_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws bounds_key_compare.
Proof. unfold bounds_key_compare. repeat apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; exact SemanticComparisonLaws.SemanticComparisonLaws.natural_laws. Qed.
Definition optional_bytes_key (x : option AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.ByteString) : (nat + AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.ByteString)%type :=
  match x with None => inl 0 | Some bytes => inr bytes end.
Definition optional_bytes_key_compare := SemanticComparisonLaws.SemanticComparisonLaws.sum_compare Nat.compare bytes_compare.
Definition optional_bytes_source_compare (x y : option AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.ByteString) :=
  match x, y with
  | None, None => Eq | None, Some _ => Lt | Some _, None => Gt
  | Some a, Some b => bytes_compare a b
  end.
Theorem optional_bytes_factor : forall x y,
  optional_bytes_source_compare x y =
    optional_bytes_key_compare (optional_bytes_key x) (optional_bytes_key y).
Proof. intros [] []; reflexivity. Qed.
Theorem optional_bytes_key_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws optional_bytes_key_compare.
Proof. apply SemanticComparisonLaws.SemanticComparisonLaws.sum_laws; [exact SemanticComparisonLaws.SemanticComparisonLaws.natural_laws | exact bytes_laws]. Qed.
Definition hole_key (h : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltHole) :=
  (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_id h, (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_name h,
    (optional_bytes_key (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_category h), range_key (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_first_occurrence h)))).
Definition hole_key_compare := SemanticComparisonLaws.SemanticComparisonLaws.pair_compare Nat.compare
  (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare bytes_compare (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare optional_bytes_key_compare range_key_compare)).
Definition hole_source_compare (a b : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltHole) :=
  SemanticComparisonLaws.SemanticComparisonLaws.lex (Nat.compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_id a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_id b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (bytes_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_name a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_name b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (optional_bytes_source_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_category a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_category b))
    (range_source_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_first_occurrence a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.hole_first_occurrence b)))).
Theorem hole_factor : forall a b,
  hole_source_compare a b = hole_key_compare (hole_key a) (hole_key b).
Proof.
  intros a b. unfold hole_source_compare, hole_key_compare, hole_key, SemanticComparisonLaws.SemanticComparisonLaws.pair_compare.
  cbn [fst snd]. rewrite optional_bytes_factor, range_factor. reflexivity.
Qed.
Theorem hole_key_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws hole_key_compare.
Proof.
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [exact SemanticComparisonLaws.SemanticComparisonLaws.natural_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [exact bytes_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [exact optional_bytes_key_laws | exact range_key_laws].
Qed.
Definition PieceKey := ((AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.ByteString * (nat * nat)) + (nat * (nat * nat)))%type.
Definition piece_key (p : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltPiece) : PieceKey :=
  match p with
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.TextPiece text range => inl (text, range_key range)
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.HolePiece identity range => inr (identity, range_key range)
  end.
Definition piece_key_compare := SemanticComparisonLaws.SemanticComparisonLaws.sum_compare
  (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare bytes_compare range_key_compare) (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare Nat.compare range_key_compare).
Definition piece_source_compare (a b : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltPiece) :=
  match a, b with
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.TextPiece x r, AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.TextPiece y s => SemanticComparisonLaws.SemanticComparisonLaws.lex (bytes_compare x y) (range_source_compare r s)
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.TextPiece _ _, AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.HolePiece _ _ => Lt
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.HolePiece _ _, AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.TextPiece _ _ => Gt
  | AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.HolePiece x r, AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.HolePiece y s => SemanticComparisonLaws.SemanticComparisonLaws.lex (Nat.compare x y) (range_source_compare r s)
  end.
Theorem piece_factor : forall a b,
  piece_source_compare a b = piece_key_compare (piece_key a) (piece_key b).
Proof. intros [] []; reflexivity. Qed.
Theorem piece_key_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws piece_key_compare.
Proof.
  apply SemanticComparisonLaws.SemanticComparisonLaws.sum_laws; apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws;
    first [exact bytes_laws | exact SemanticComparisonLaws.SemanticComparisonLaws.natural_laws | exact range_key_laws].
Qed.
Lemma holes_factor : forall xs ys,
  list_compare hole_source_compare xs ys =
    list_compare hole_key_compare (map hole_key xs) (map hole_key ys).
Proof. apply AdmittedComparisonClasses.AdmittedComparisonClasses.list_factor. exact hole_factor. Qed.
Lemma pieces_factor : forall xs ys,
  list_compare piece_source_compare xs ys =
    list_compare piece_key_compare (map piece_key xs) (map piece_key ys).
Proof. apply AdmittedComparisonClasses.AdmittedComparisonClasses.list_factor. exact piece_factor. Qed.
Definition flt_key (n : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltNode) :=
  (var_key (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.selector n),
   (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.selector_name n,
    (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.category n,
     (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.open_src n,
      (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.body_src n,
       (map hole_key (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.holes n),
        (map piece_key (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.pieces n),
         (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.close_src n, (bounds_key (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.bounds n), AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.position n))))))))).
Definition flt_key_compare := SemanticComparisonLaws.SemanticComparisonLaws.pair_compare var_key_compare
  (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare bytes_compare
   (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare bytes_compare
    (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare bytes_compare
     (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare bytes_compare
      (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare (list_compare hole_key_compare)
       (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare (list_compare piece_key_compare)
        (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare bytes_compare
         (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare bounds_key_compare Nat.compare)))))))).
Definition flt_source_compare (a b : AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltNode) :=
  SemanticComparisonLaws.SemanticComparisonLaws.lex (ordvar_source_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.selector a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.selector b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (bytes_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.selector_name a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.selector_name b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (bytes_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.category a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.category b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (bytes_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.open_src a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.open_src b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (bytes_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.body_src a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.body_src b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (list_compare hole_source_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.holes a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.holes b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (list_compare piece_source_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.pieces a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.pieces b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (bytes_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.close_src a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.close_src b))
  (SemanticComparisonLaws.SemanticComparisonLaws.lex (bounds_source_compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.bounds a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.bounds b))
    (Nat.compare (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.position a) (AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.position b)))))))))).
Theorem flt_factor : forall a b,
  flt_source_compare a b = flt_key_compare (flt_key a) (flt_key b).
Proof.
  intros a b. unfold flt_source_compare, flt_key_compare, flt_key, SemanticComparisonLaws.SemanticComparisonLaws.pair_compare.
  cbn [fst snd].
  rewrite ordvar_factor, holes_factor, pieces_factor, bounds_factor. reflexivity.
Qed.
Theorem flt_key_laws : SemanticComparisonLaws.SemanticComparisonLaws.Laws flt_key_compare.
Proof.
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [exact var_key_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [exact bytes_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [exact bytes_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [exact bytes_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [exact bytes_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [apply SemanticComparisonLaws.SemanticComparisonLaws.list_laws; exact hole_key_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [apply SemanticComparisonLaws.SemanticComparisonLaws.list_laws; exact piece_key_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [exact bytes_laws|].
  apply SemanticComparisonLaws.SemanticComparisonLaws.pair_laws; [exact bounds_key_laws | exact SemanticComparisonLaws.SemanticComparisonLaws.natural_laws].
Qed.
(** Arc ordering compares the payload; allocation identity is not a key. *)
Definition arc_flt_source_compare := flt_source_compare.
Theorem arc_flt_factor : forall a b,
  arc_flt_source_compare a b = flt_key_compare (flt_key a) (flt_key b).
Proof. exact flt_factor. Qed.
Theorem flt_class_congruence_left : forall x y z,
  flt_source_compare x y = Eq -> flt_source_compare x z = flt_source_compare y z.
Proof.
  exact (@AdmittedComparisonClasses.AdmittedComparisonClasses.class_congruence_left AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.FltNode _ flt_source_compare
    flt_key_compare flt_key flt_key_laws flt_factor).
Qed.
Theorem ordvar_class_congruence_left : forall x y z,
  ordvar_source_compare x y = Eq -> ordvar_source_compare x z = ordvar_source_compare y z.
Proof.
  exact (@AdmittedComparisonClasses.AdmittedComparisonClasses.class_congruence_left AdmittedStructuralKeyHash.AdmittedStructuralKeyHash.MonikerVar VarKey ordvar_source_compare
    var_key_compare var_key var_key_laws ordvar_factor).
Qed.
End IdentityAndFlt.
Print Assumptions signed_laws.
Print Assumptions signed_factor.
Print Assumptions bool_factor.
Print Assumptions string_factor.
Print Assumptions bytes_laws.
Print Assumptions ordvar_factor.
Print Assumptions var_key_laws.
Print Assumptions single_pattern_factor.
Print Assumptions equal_length_zip_find_factor.
Print Assumptions multi_pattern_factor.
Print Assumptions multi_pattern_key_laws.
Print Assumptions range_factor.
Print Assumptions bounds_factor.
Print Assumptions optional_bytes_factor.
Print Assumptions hole_factor.
Print Assumptions piece_factor.
Print Assumptions holes_factor.
Print Assumptions pieces_factor.
Print Assumptions flt_factor.
Print Assumptions flt_key_laws.
Print Assumptions arc_flt_factor.
Print Assumptions flt_class_congruence_left.
Print Assumptions ordvar_class_congruence_left.
End AdmittedNativeComparisonFactors.
