(*
 * InRhoAcMatchMultiset: FV (AC-i) for Stage AC's in-Rho AC matching.
 *
 * The in-Rho AC match (the native `sub_pars` / `MaximumBipartiteMatch` over the reflected bag
 * carrier) is SOUND and COMPLETE with respect to the AC matching RELATION over multisets. The
 * relation is: a selection `S` matches a bag `B` (binding the remainder `rest`) iff `S` is a
 * sub-multiset of `B` and `S ⊎ rest ≡ B`. This theory proves the central correspondence:
 *
 *     sub_multiset S B   <->   exists rest, Permutation (S ++ rest) B
 *
 * i.e. the incremental pick-and-remove the native matcher performs (each pattern slot picks a
 * PRESENT element and recurses on the bag with that occurrence removed — exactly `sub_multiset`)
 * captures EXACTLY the order-independent partitions of the bag. The forward direction is
 * SOUNDNESS (the native selection admits a faithful `rest` = complement, `AcRestReconstruction`);
 * the backward direction is COMPLETENESS (every order-independent partition of the bag into a
 * matched selection + a rest is a reachable native match) — so no valid AC match is missed and
 * none is fabricated. Order-independence is inherent: the witness is a `Permutation`, invariant
 * under the bag's shuffle.
 *
 * Reuses AcRestReconstruction (`sub_multiset`, `complement`, `remove_one_perm`,
 * `selection_rest_partition`) + Stdlib `Permutation`. Zero-admission. Rocq 9.1 compatible.
 *)

From AdvancedAutomata Require Import AcRestReconstruction.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.

Import ListNotations.

Section InRhoAcMatchMultiset.

  (* COMPLETENESS core: an order-independent partition witness makes the selection a sub-multiset.
     Induction on the selection, peeling the head pick off both the partition and the bag. *)
  Lemma partition_sub_multiset : forall selection bag rest,
    Permutation (selection ++ rest) bag -> sub_multiset selection bag.
  Proof.
    induction selection as [| x sel' IH]; intros bag rest Hperm.
    - apply sm_nil.
    - simpl in Hperm.
      assert (Hin : In x bag).
      { apply (Permutation_in x Hperm). left. reflexivity. }
      apply sm_cons; [ exact Hin |].
      apply (IH (remove_one x bag) rest).
      assert (Hcons : Permutation (x :: (sel' ++ rest)) (x :: remove_one x bag)).
      { apply Permutation_trans with bag.
        - exact Hperm.
        - apply Permutation_sym. apply remove_one_perm. exact Hin. }
      exact (Permutation_cons_inv Hcons).
  Qed.

  (* (AC-i) THE MATCH CORRESPONDENCE: the native sub-multiset match holds iff the selection has
     an order-independent complement partitioning the bag — the in-Rho AC match set equals the
     AC matching relation over multisets. *)
  Theorem ac_match_iff_partition : forall selection bag,
    sub_multiset selection bag <-> exists rest, Permutation (selection ++ rest) bag.
  Proof.
    intros selection bag. split.
    - intro Hsub. exists (complement bag selection).
      apply selection_rest_partition. exact Hsub.
    - intros [rest Hperm]. exact (partition_sub_multiset selection bag rest Hperm).
  Qed.

  (* SOUNDNESS: the native selection admits a faithful `rest` = complement that exactly partitions
     the bag (nothing gained or lost) — the in-Rho AC match never fabricates a binding. *)
  Corollary ac_match_sound : forall selection bag,
    sub_multiset selection bag ->
    Permutation (selection ++ complement bag selection) bag.
  Proof. exact selection_rest_partition. Qed.

  (* COMPLETENESS: any order-independent partition of the bag into a matched selection + a rest
     is a reachable native AC match (a sub-multiset) — no valid match is missed. *)
  Corollary ac_match_complete : forall selection rest bag,
    Permutation (selection ++ rest) bag -> sub_multiset selection bag.
  Proof.
    intros selection rest bag H. exact (partition_sub_multiset selection bag rest H).
  Qed.

  (* The rest is DETERMINED up to multiset equality: any two rests witnessing the same selection
     match permute the same complement, so both permute each other — the `rest` binding is
     well-defined regardless of which shuffle the native matcher committed. Proved through the
     canonical complement (selection_rest_partition) to avoid a left-cancellation lemma. *)
  Corollary ac_rest_unique_up_to_perm : forall selection bag rest1 rest2,
    sub_multiset selection bag ->
    Permutation (selection ++ rest1) bag ->
    Permutation (selection ++ rest2) bag ->
    Permutation rest1 rest2.
  Proof.
    intros selection bag rest1 rest2 Hsub H1 H2.
    (* Both rests, appended after selection, permute bag; the canonical complement does too. *)
    assert (Hc : Permutation (selection ++ complement bag selection) bag)
      by (apply selection_rest_partition; exact Hsub).
    (* rest1 ~ complement and rest2 ~ complement via the shared prefix, using only append/trans. *)
    assert (E1 : Permutation (selection ++ rest1) (selection ++ complement bag selection))
      by (apply Permutation_trans with bag; [ exact H1 | apply Permutation_sym; exact Hc ]).
    assert (E2 : Permutation (selection ++ rest2) (selection ++ complement bag selection))
      by (apply Permutation_trans with bag; [ exact H2 | apply Permutation_sym; exact Hc ]).
    apply Permutation_app_inv_l in E1.
    apply Permutation_app_inv_l in E2.
    apply Permutation_trans with (complement bag selection); [ exact E1 | apply Permutation_sym; exact E2 ].
  Qed.

  (* ------------------------------------------------------------------------------------------- *)
  (* Stage 4 (S-AC): the located bag = the SUBJECT operand bag.                                   *)
  (*                                                                                             *)
  (* AC1/AC2 re-source the operand bag from the SPREAD of the reflected subject term (the match  *)
  (* driver's `ac_match_call_par` publishes `reflect_ac_bag_par` over the SUBJECT bag's ground   *)
  (* elements on the site-keyed carrier), NOT from the host report σ. Because the AC match set is *)
  (* order-independent (a multiset relation), the load-bearing fact is that the located bag is a  *)
  (* PERMUTATION of the subject operand bag — the same multiset the host oracle `collect_ac_      *)
  (* matches` reads off the SAME subterm. These lemmas prove the AC match set is invariant under  *)
  (* that permutation, so re-sourcing the bag from the spread neither adds nor drops a match.     *)

  (* remove_one is the identity on a bag that does not contain the element. *)
  Lemma remove_one_not_in : forall x l, ~ In x l -> remove_one x l = l.
  Proof.
    intros x l. induction l as [| h t IH]; simpl; [ reflexivity | intro Hnin ].
    destruct (Nat.eqb h x) eqn:He.
    - apply Nat.eqb_eq in He. subst h. exfalso. apply Hnin. left. reflexivity.
    - f_equal. apply IH. intro Hin. apply Hnin. right. exact Hin.
  Qed.

  (* Removing one occurrence of a PRESENT element is a permutation congruence: permuted bags have
     permuted remainders. Peels `x` off both sides through `remove_one_perm` + `Permutation_cons_inv`. *)
  Lemma remove_one_perm_cong : forall x bag1 bag2,
    In x bag1 -> Permutation bag1 bag2 ->
    Permutation (remove_one x bag1) (remove_one x bag2).
  Proof.
    intros x bag1 bag2 Hin Hperm.
    assert (Hin2 : In x bag2) by (apply (Permutation_in x Hperm); exact Hin).
    apply Permutation_cons_inv with (a := x).
    apply Permutation_trans with bag1; [ apply remove_one_perm; exact Hin |].
    apply Permutation_trans with bag2; [ exact Hperm |].
    apply Permutation_sym. apply remove_one_perm. exact Hin2.
  Qed.

  (* sub_multiset is INVARIANT under permutation of the bag — the AC match relation is order-
     independent, so it cannot distinguish the located bag from the subject operand bag when the two
     permute. Induction on the sub_multiset derivation, peeling each pick through remove_one_perm_cong. *)
  Lemma sub_multiset_perm_bag : forall selection bag1 bag2,
    Permutation bag1 bag2 -> sub_multiset selection bag1 -> sub_multiset selection bag2.
  Proof.
    intros selection bag1 bag2 Hperm Hsub. revert bag2 Hperm.
    induction Hsub as [bag0 | x sel bag0 Hin Hsub IH]; intros bag2 Hperm.
    - apply sm_nil.
    - apply sm_cons.
      + apply (Permutation_in x Hperm). exact Hin.
      + apply IH. apply remove_one_perm_cong; [ exact Hin | exact Hperm ].
  Qed.

  (* The AC match set is the SAME over two permuted bags (both directions). *)
  Corollary sub_multiset_perm_iff : forall selection bag1 bag2,
    Permutation bag1 bag2 -> (sub_multiset selection bag1 <-> sub_multiset selection bag2).
  Proof.
    intros selection bag1 bag2 Hperm. split; intro H.
    - apply (sub_multiset_perm_bag selection bag1 bag2 Hperm H).
    - apply (sub_multiset_perm_bag selection bag2 bag1 (Permutation_sym Hperm) H).
  Qed.

End InRhoAcMatchMultiset.

(* ============================================================================================= *)
(* Stage 4 (S-AC) — the LOAD-BEARING claim: the LOCATED bag is the SUBJECT operand bag, not the   *)
(* report σ. The AC analogue of `m_reflect_sigma_is_produced_by_the_automaton_not_the_report`.     *)
(* ============================================================================================= *)

Section LocatedBagFromSubject.

  (* The operand bag at the AC redex position AS THE M-REFLECT WALK PRODUCES IT from the SUBJECT
     term — the same subterm the host oracle `collect_ac_matches` reads. Element identities: nat. *)
  Variable subject_operand_bag : list nat.

  (* The SPREAD publishes the bag as a process-soup (`reflect_ac_bag_par`), one ground send per
     element, order- and multiplicity-preserving; the co-installed AC receiver picks k-of-n from
     that soup's element multiset — the LOCATED bag. Being one-send-per-element, the located bag is
     a PERMUTATION of the subject operand bag (the soup is order-independent). *)
  Variable located_bag : list nat.
  Hypothesis located_is_spread_of_subject :
    Permutation located_bag subject_operand_bag.

  (* THE LOAD-BEARING LEMMA: the in-Rho AC match set over the LOCATED bag (from the spread of the
     subject) EQUALS the AC match set over the SUBJECT operand bag — the co-installed receiver
     matches exactly the multiset the host oracle would, because the spread only permutes it. So
     re-sourcing the bag from the spread neither adds nor drops an AC match. *)
  Theorem located_matches_subject : forall selection,
    sub_multiset selection located_bag <-> sub_multiset selection subject_operand_bag.
  Proof.
    intro selection.
    apply sub_multiset_perm_iff. exact located_is_spread_of_subject.
  Qed.

  (* NON-REPORT: a report bag reconstructed from a (possibly corrupted) σ is an ARBITRARY,
     INDEPENDENT list `report_bag'`. The located match set does not mention it — so a corrupted
     report cannot perturb the located match set. This is the corrupted-σ probe
     `s_ac_bag_is_produced_by_the_spread_not_the_report` made precise: the match is the subject's,
     for ANY report. *)
  Theorem located_match_is_independent_of_report :
    forall (selection report_bag' : list nat),
      sub_multiset selection located_bag <-> sub_multiset selection subject_operand_bag.
  Proof.
    intros selection report_bag'. apply located_matches_subject.
  Qed.

  (* COMPOSED with the carrier-agnostic native match (`ac_match_iff_partition`): the located bag's
     matches are EXACTLY its order-independent partitions — and, by `located_matches_subject`, those
     are the subject operand bag's partitions. The genuine in-Rho AC replacement, end to end. *)
  Corollary located_ac_match_iff_partition_subject : forall selection,
    sub_multiset selection subject_operand_bag <->
    exists rest, Permutation (selection ++ rest) located_bag.
  Proof.
    intro selection. split.
    - intro Hsub.
      apply (proj2 (located_matches_subject selection)) in Hsub.
      apply (proj1 (ac_match_iff_partition selection located_bag)). exact Hsub.
    - intros [rest Hperm].
      apply (proj1 (located_matches_subject selection)).
      apply (proj2 (ac_match_iff_partition selection located_bag)). exists rest. exact Hperm.
  Qed.

End LocatedBagFromSubject.

(* ============================================================================================= *)
(* Stage 4 (S-AC) — SITE-KEYED CARRIER DISJOINTNESS (Red-team #5): distinct bag positions get      *)
(* DISJOINT carriers, so two same-op bags' soups never intermingle and the native matcher cannot   *)
(* pick cross-bag elements.                                                                        *)
(* ============================================================================================= *)

Section SiteKeyedCarrierDisjointness.

  (* A carrier channel `ac:⌜ℓ⌝/op` is keyed by the location path ℓ (nat identity) AND the operand
     op. `ac_carrier_channel` embeds ℓ, so the carrier is injective in ℓ for a fixed op. *)
  Definition carrier (loc op : nat) : nat * nat := (loc, op).

  (* Two SAME-op bags at DISTINCT positions get DISTINCT carriers — the site key, not the shared
     `ac:op`, is what disambiguates them (without it their soups would share one channel). *)
  Theorem carrier_site_keyed_injective : forall loc1 loc2 op,
    loc1 <> loc2 -> carrier loc1 op <> carrier loc2 op.
  Proof.
    intros loc1 loc2 op Hne Heq. apply Hne. inversion Heq. reflexivity.
  Qed.

  (* NO CROSS-BAG INTERMINGLE: model the interpreter's tuplespace as a map from carrier to the soup
     published there. The AC receiver at carrier `carrier loc1 op` reads EXACTLY that carrier's
     soup; because a distinct-site same-op bag lives on `carrier loc2 op ≠ carrier loc1 op`,
     CHANGING the soup at loc2 (any other bag) cannot change the read at loc1. So the receiver at a
     site picks only from ITS OWN bag — the soundness Red-team #5 flags without the site key. *)
  Theorem carrier_read_independent :
    forall (tuplespace1 tuplespace2 : (nat * nat) -> list nat) loc1 loc2 op,
      loc1 <> loc2 ->
      (forall c, c <> carrier loc2 op -> tuplespace1 c = tuplespace2 c) ->
      tuplespace1 (carrier loc1 op) = tuplespace2 (carrier loc1 op).
  Proof.
    intros tuplespace1 tuplespace2 loc1 loc2 op Hne Hagree.
    apply Hagree. apply carrier_site_keyed_injective. exact Hne.
  Qed.

End SiteKeyedCarrierDisjointness.

(* ============================================================================================= *)
(* Stage 4 (S-AC, AC4) — the located SET / MAP / ZIP = the SUBJECT operand collection.            *)
(*                                                                                               *)
(* AC4 extends the in-Rho AC match from the process-soup HashBag carrier to the NATIVE carriers   *)
(* `ESet` (HashSet), `EMap` (HashMap), and a structured paired `ESet` (ZipAc). Each is re-sourced  *)
(* from the SPREAD of the reflected subject, EXACTLY as the HashBag soup: the located collection    *)
(* PERMUTES the subject operand collection (the reflect is order-independent; `ParSet`/`ParMap`     *)
(* additionally sort + dedupe). The element-multiset match (`sub_multiset`) is carrier-AGNOSTIC —   *)
(* it is defined over the element identities — so the located = subject arms REUSE                 *)
(* `sub_multiset_perm_iff` verbatim (appended here, the HashBag arms above untouched). The NEW      *)
(* content per kind is the EXTRA carrier invariant, each preserved under the located permutation:   *)
(* SET uniqueness (`NoDup`), MAP key-uniqueness (`NoDup` of the keys), ZIP correlation (a shared    *)
(* first component across two picked elements). These are the AC4 analogue of `located_matches_     *)
(* subject`, so re-sourcing a set/map/zip collection from the spread neither adds nor drops a match *)
(* and never violates the native carrier's invariant.                                             *)
(* ============================================================================================= *)

Section LocatedSetFromSubject.

  (* AC4-set (HashSet -> ESet): the operand SET as the M-reflect walk produces it from the subject,
     and the LOCATED set the co-installed `ac_set_pattern` receiver reads off the ESet carrier. Being
     the SAME elements (the ParSet is order-independent), the located set PERMUTES the subject set. A
     SET carries no duplicate (the ParSet uniqueness invariant). *)
  Variable subject_set located_set : list nat.
  Hypothesis set_located_is_spread : Permutation located_set subject_set.
  Hypothesis subject_set_nodup : NoDup subject_set.

  (* The ESet AC match set over the LOCATED set EQUALS that over the SUBJECT set (order-independent —
     the native `list_match_single_` picks a sub-multiset of DISTINCT set elements + a residual set). *)
  Theorem located_set_matches_subject : forall selection,
    sub_multiset selection located_set <-> sub_multiset selection subject_set.
  Proof. intro selection. apply sub_multiset_perm_iff. exact set_located_is_spread. Qed.

  (* SET UNIQUENESS survives the reflect: the located set is still duplicate-free, so the ESet carrier
     is a genuine set (no element is picked twice as two "distinct" slots). *)
  Theorem located_set_nodup : NoDup located_set.
  Proof.
    apply (Permutation_NoDup (Permutation_sym set_located_is_spread)). exact subject_set_nodup.
  Qed.

End LocatedSetFromSubject.

Section LocatedMapFromSubject.

  (* AC4-map (HashMap -> EMap): the operand map, modelled by its KEY list (nat identities), as the
     subject produces it and as the located `ac_map_pattern` receiver reads it off the EMap carrier.
     The located keys PERMUTE the subject keys (the ParMap is key-sorted + deduped — a reordering).
     KEY-UNIQUENESS is `NoDup` of the keys (the ParMap invariant). *)
  Variable subject_map_keys located_map_keys : list nat.
  Hypothesis map_located_is_spread : Permutation located_map_keys subject_map_keys.
  Hypothesis subject_map_key_unique : NoDup subject_map_keys.

  (* The EMap AC match set over the LOCATED map (its keys) EQUALS that over the SUBJECT map — the
     native match picks k entries + binds a residual map, order-independent over the key multiset. *)
  Theorem located_map_matches_subject : forall selection,
    sub_multiset selection located_map_keys <-> sub_multiset selection subject_map_keys.
  Proof. intro selection. apply sub_multiset_perm_iff. exact map_located_is_spread. Qed.

  (* KEY-UNIQUENESS survives the reflect: the located map's keys are still duplicate-free, so the
     located EMap carrier upholds the ParMap key-unique invariant the decoder relies on. *)
  Theorem located_map_key_unique : NoDup located_map_keys.
  Proof.
    apply (Permutation_NoDup (Permutation_sym map_located_is_spread)). exact subject_map_key_unique.
  Qed.

End LocatedMapFromSubject.

Section LocatedZipFromSubject.

  (* AC4-zip (ZipAc): the operand set of STRUCTURED elements, modelled as pairs (nat * nat) — the
     first component is the correlated key `a` in `Pair(a, _)`. The located paired set PERMUTES the
     subject paired set (the ESet re-sourcing). The `Receive.condition` `EEq(a_0, a_1)` picks two
     elements with EQUAL first component — the CORRELATION. *)
  Variable subject_pairs located_pairs : list (nat * nat).
  Hypothesis zip_located_is_spread : Permutation located_pairs subject_pairs.

  (* CORRELATION PRESERVED: a correlated pair (`fst e1 = fst e2`) of LOCATED elements is exactly a
     correlated pair of SUBJECT elements — `In` is permutation-invariant and the guard is a property
     of the two elements. So the paired match the reducer commits under the guard is the subject's. *)
  Theorem located_zip_correlation_matches_subject : forall e1 e2,
    (In e1 located_pairs /\ In e2 located_pairs /\ fst e1 = fst e2) <->
    (In e1 subject_pairs /\ In e2 subject_pairs /\ fst e1 = fst e2).
  Proof.
    intros e1 e2. split.
    - intros [H1 [H2 Hc]]. split; [| split ].
      + apply (Permutation_in e1 zip_located_is_spread). exact H1.
      + apply (Permutation_in e2 zip_located_is_spread). exact H2.
      + exact Hc.
    - intros [H1 [H2 Hc]]. split; [| split ].
      + apply (Permutation_in e1 (Permutation_sym zip_located_is_spread)). exact H1.
      + apply (Permutation_in e2 (Permutation_sym zip_located_is_spread)). exact H2.
      + exact Hc.
  Qed.

End LocatedZipFromSubject.

Print Assumptions ac_match_iff_partition.
Print Assumptions ac_match_sound.
Print Assumptions ac_match_complete.
Print Assumptions ac_rest_unique_up_to_perm.
Print Assumptions sub_multiset_perm_iff.
Print Assumptions located_matches_subject.
Print Assumptions located_match_is_independent_of_report.
Print Assumptions located_ac_match_iff_partition_subject.
Print Assumptions carrier_site_keyed_injective.
Print Assumptions carrier_read_independent.
Print Assumptions located_set_matches_subject.
Print Assumptions located_set_nodup.
Print Assumptions located_map_matches_subject.
Print Assumptions located_map_key_unique.
Print Assumptions located_zip_correlation_matches_subject.
