(*
 * AcBagRhsReflection: FV (AC-bag) for Stage AC2b — a bag-VALUED AC RHS.
 *
 * Stage AC2b lowers a bag-TRANSFORMING AC rewrite `op{x, ...rest} ~> op{f(x), ...rest}` so the AC
 * receiver's body `⟦R⟧σ` is the process-SOUP carrier (codegen `reflect_hashbag_soup_par`): each
 * fixed element `e_i` becomes a send `@"ac:{op}"!(⟦e_i⟧)` and the residual `...rest` is the σ-slot
 * `BoundVar` the AC receiver bound to the leftover soup, ALL composed in PARALLEL. This theory
 * proves the multiset facts that make that carrier faithful — the obligations DISTINCT from
 * AcRestReconstruction (which proves the `rest = bag ⊖ selection` partition and the list-level
 * `flatten` splice): here the object is the SEND CARRIER itself (a parallel composition of
 * per-element sends, the shape `reflect_ac_bag_par` emits and `decode_ac_bag_soup` reads), and the
 * load-bearing facts are that reflecting a bag to that carrier is a MULTISET HOMOMORPHISM
 * (multiplicity-preserving, order-independent), and that the RHS soup — the fixed sends ∥ the
 * residual soup — is BYTE-IDENTICAL to the ground HashBag reflection of the flat transformed bag
 * `fixed ⊎ rest` (so the `...rest` SPLICES, never nests, and OUT decodes exactly to that bag).
 *
 *   (1) FAITHFUL — `soup_elements (reflect_bag_soup bag) = bag`: the carrier carries exactly the
 *       bag's elements, one send each (no loss/gain; the ground reflection `reflect_ac_bag_par`,
 *       inverted by `decode_ac_bag_soup`).
 *   (2) HOMOMORPHISM — `reflect_bag_soup (b1 ++ b2) = reflect_bag_soup b1 ++ reflect_bag_soup b2`:
 *       the parallel composition of soups is the reflection of the multiset union.
 *   (3) SPLICE — `soup_elements (reflect_rhs_soup fixed rest_soup) = fixed ++ soup_elements rest_soup`:
 *       the `...rest` σ-slot splices the residual sends into the flat bag (never nests), so the
 *       carrier's multiset is `fixed ⊎ rest`.
 *   (4) BYTE-IDENTITY — `reflect_rhs_soup fixed (reflect_bag_soup rest) = reflect_bag_soup (fixed ++ rest)`:
 *       the AC receiver's RHS soup EQUALS the ground reflection of the transformed bag `op{fixed ⊎
 *       rest}`, so a bag-VALUED RHS lands on OUT as that exact bag (mirrors `add_flattened_bag`).
 *   (5) MULTIPLICITY — the reflection preserves per-element multiplicity (HashBag is a multiset).
 *   (6) ORDER-INDEPENDENT — a permutation of the bag reflects to a permutation of the carrier (the
 *       carrier is a multiset; parallel composition is commutative/associative up to Permutation).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.

Import ListNotations.

Section AcBagRhsReflection.

  (* A send `@"ac:{op}"!(e)` carries one reflected element `e` (element identities as nat). The op
     (hence the channel) is fixed per bag — the AC LHS/RHS/injection all agree on `op` — so a send
     is determined by its carried element. *)
  Record Send := mkSend { carried : nat }.

  (* The ground HashBag reflection (`reflect_ac_bag_par`): one send per bag element, in parallel. A
     soup is a `list Send`; parallel composition is list append (order is irrelevant — see (6)). *)
  Definition reflect_bag_soup (bag : list nat) : list Send := map mkSend bag.

  (* The elements a soup carries — the read `decode_ac_bag_soup` performs (one datum per send). *)
  Definition soup_elements (soup : list Send) : list nat := map carried soup.

  (* The Stage AC2b RHS reflection (`reflect_hashbag_soup_par`): each fixed element becomes a send,
     parallel-composed with the residual `...rest` soup (the σ-slot `BoundVar`'s runtime value —
     the leftover sends the AC receiver bound). Parallel composition is append. *)
  Definition reflect_rhs_soup (fixed : list nat) (rest_soup : list Send) : list Send :=
    reflect_bag_soup fixed ++ rest_soup.

  (* (1) FAITHFUL: the carrier carries exactly the bag, one send per element (no loss/gain). *)
  Theorem soup_elements_reflect : forall bag,
    soup_elements (reflect_bag_soup bag) = bag.
  Proof.
    intros bag. unfold soup_elements, reflect_bag_soup.
    induction bag as [| h t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  (* (2) HOMOMORPHISM: reflecting a union is the parallel composition of the reflections. *)
  Theorem reflect_bag_soup_app : forall b1 b2,
    reflect_bag_soup (b1 ++ b2) = reflect_bag_soup b1 ++ reflect_bag_soup b2.
  Proof. intros b1 b2. unfold reflect_bag_soup. apply map_app. Qed.

  (* (3) SPLICE: the RHS soup's elements are the fixed elements followed by the residual soup's
     elements — the `...rest` splices its sends into the flat bag, never nesting. *)
  Theorem reflect_rhs_soup_elements : forall fixed rest_soup,
    soup_elements (reflect_rhs_soup fixed rest_soup) = fixed ++ soup_elements rest_soup.
  Proof.
    intros fixed rest_soup. unfold reflect_rhs_soup, soup_elements.
    rewrite map_app.
    assert (H := soup_elements_reflect fixed). unfold soup_elements in H.
    rewrite H. reflexivity.
  Qed.

  (* (4) BYTE-IDENTITY: the AC receiver's RHS soup EQUALS the ground reflection of the flat
     transformed bag `fixed ⊎ rest`, so OUT decodes exactly to `op{fixed ⊎ rest}` (the
     `add_flattened_bag` splice). This is the load-bearing equality behind the e2e firing. *)
  Theorem reflect_rhs_soup_is_ground_reflection : forall fixed rest,
    reflect_rhs_soup fixed (reflect_bag_soup rest) = reflect_bag_soup (fixed ++ rest).
  Proof.
    intros fixed rest. unfold reflect_rhs_soup.
    rewrite <- reflect_bag_soup_app. reflexivity.
  Qed.

  (* (5) MULTIPLICITY: the reflection preserves per-element multiplicity (a HashBag multiset). *)
  Corollary reflect_preserves_multiplicity : forall bag x,
    count_occ Nat.eq_dec (soup_elements (reflect_bag_soup bag)) x = count_occ Nat.eq_dec bag x.
  Proof. intros bag x. rewrite soup_elements_reflect. reflexivity. Qed.

  (* (6) ORDER-INDEPENDENT: a permutation of the bag reflects to a permutation of the carrier —
     the carrier is a multiset (parallel composition is commutative/associative). *)
  Theorem reflect_bag_soup_perm : forall b1 b2,
    Permutation b1 b2 ->
    Permutation (soup_elements (reflect_bag_soup b1)) (soup_elements (reflect_bag_soup b2)).
  Proof.
    intros b1 b2 Hperm. rewrite !soup_elements_reflect. exact Hperm.
  Qed.

  (* Corollary (the e2e firing spec): reflecting the RHS bag `op{fixed, ...rest}` whose `rest`
     binds a bag `r`, and reading the carrier back, yields exactly the transformed multiset
     `fixed ⊎ r` — the bag OUT decodes to. Composes (3)+(1). *)
  Corollary rhs_soup_decodes_to_transformed_bag : forall fixed r,
    soup_elements (reflect_rhs_soup fixed (reflect_bag_soup r)) = fixed ++ r.
  Proof.
    intros fixed r.
    rewrite reflect_rhs_soup_elements, soup_elements_reflect. reflexivity.
  Qed.

End AcBagRhsReflection.

Print Assumptions soup_elements_reflect.
Print Assumptions reflect_bag_soup_app.
Print Assumptions reflect_rhs_soup_elements.
Print Assumptions reflect_rhs_soup_is_ground_reflection.
Print Assumptions reflect_preserves_multiplicity.
Print Assumptions reflect_bag_soup_perm.
Print Assumptions rhs_soup_decodes_to_transformed_bag.
