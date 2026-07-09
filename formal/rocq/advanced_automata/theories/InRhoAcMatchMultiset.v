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

(* ============================================================================================= *)
(* Stage 4 (S-binder SLICE 3b) — the STRUCTURED-element AC SPREAD match: the located STRUCTURED bag  *)
(* = the subject operand bag, the connective-bound σ (channel occurrences N_i, structural reducts    *)
(* r_j, residual rest) = the host report σ, and the spliced body = the RHS.                          *)
(*                                                                                                   *)
(* The Ambient `OpenRule`  {POpen N P, PAmb N Q, ...rest} ~> {P, Q, ...rest}  generalizes the        *)
(* bare-var AC element (whose value IS the reduct) to a STRUCTURED element `C(N, …, r_j, …)` whose    *)
(* reduct args `r_j` are INNER arguments. The report-path `structural_ac_contract_call` wildcards     *)
(* those args and takes them as separately DELIVERED σ slots (from `find_sigma`); the MATCH receiver  *)
(* `structural_ac_match_receiver_par` instead BINDS them from the operand bag's connective pattern —  *)
(* so, exactly like the linear `ac_match_call_par`, its message is the 2-value `carrier!(⟦bag⟧,@out)` *)
(* the SPREAD delivers, with NO host σ. This section proves the STRUCTURED analogue of the bare-var    *)
(* `LocatedBagFromSubject` results: because the spread only PERMUTES the operand bag, (1a) the         *)
(* located structured bag admits the SAME AC partitions as the subject bag, (2) the σ the connective   *)
(* binds (`names`/`reducts`/`rest`) is EXACTLY a report delivery — binding reduct args from the bag ≡  *)
(* recovering them from σ — and (4) the spliced body `reducts ⊎ rest` reconstructs the RHS multiset,   *)
(* multiplicity-preserving (reusing `AcRestReconstruction`'s flatten splice). Reuses                   *)
(* `ac_match_iff_partition`/`sub_multiset_perm_iff` at the channel-occurrence multiset level +         *)
(* `instantiate_ac_shape` for the body splice + Stdlib `Permutation`. The `^lambda`/nested DESCENT     *)
(* that LOCATES this bag (including under a `new` binder) is the companion                             *)
(* `advanced_automata/InRhoMatchPositional.v::ac_locate_iff_spine`; the reflected-name GUARD           *)
(* `EEq(N_i,N_j)` ⟺ α-equivalence is `rho_bridge/BinderReflectionTotalOrReject.v`.                     *)
(* ============================================================================================= *)

Section StructuralAcSpreadMatch.

  (* A STRUCTURED AC element `C(N, …, r_j, …)`: its constructor tag, the non-linear channel-occurrence
     identity `N` (a nat — the reflected `^bound`/`^free` name), and its structural reduct-arg
     identities `r_j` (the RHS elements it sources — for `POpen N P` the singleton `[P]`; a dropped
     arg contributes nothing). *)
  Record StructElem : Type := {
    se_ctor : nat;
    se_name : nat;
    se_reducts : list nat
  }.

  (* The channel-occurrence multiset of a selection (`map se_name`) — the guard slots N_i. *)
  Definition names (sel : list StructElem) : list nat := map se_name sel.
  (* The structural-reduct multiset of a selection (`flat_map se_reducts`) — the RHS elements r_j, in
     element order (the fired bag is a multiset, so RHS-order = element-order up to permutation). *)
  Definition reducts (sel : list StructElem) : list nat := flat_map se_reducts sel.

  (* Permutation is a congruence for `flat_map` (Stdlib gives `Permutation_map` for `names`; the
     `reducts` re-sourcing is order-independent, proved here from the append congruences). *)
  Lemma Permutation_flat_map_se : forall (f : StructElem -> list nat) l l',
    Permutation l l' -> Permutation (flat_map f l) (flat_map f l').
  Proof.
    intros f l l' H. induction H; simpl.
    - apply Permutation_refl.
    - apply Permutation_app_head. exact IHPermutation.
    - rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
    - eapply Permutation_trans; eassumption.
  Qed.

  (* `flatten (map Leaf l) = l` — a list of ordinary Leaf members flattens to itself (each Leaf
     splices to its singleton). *)
  Lemma flatten_map_leaf : forall l, flatten (map Leaf l) = l.
  Proof.
    induction l as [| x xs IH]; simpl; [ reflexivity | rewrite IH; reflexivity ].
  Qed.

  (* (S-AC.4) THE SPLICED BODY = THE RHS MULTISET. The receiver body `out!(@"ac:op"!(r0) | … | rest)`
     emits one send per RHS reduct occurrence spliced with the residual bag — the multiset
     `reducts ++ rest`. Reuse `AcRestReconstruction`'s flatten splice (`instantiate_ac_shape`): the
     `rest` member splices INLINE (never nests), multiplicity-preserving. Independent of the spread
     source (no section variables). *)
  Theorem fired_bag_is_reducts_splice_rest : forall reduct_ids rest_ids : list nat,
    flatten (map Leaf reduct_ids ++ [Sub rest_ids]) = reduct_ids ++ rest_ids.
  Proof.
    intros reduct_ids rest_ids.
    rewrite instantiate_ac_shape. rewrite flatten_map_leaf. reflexivity.
  Qed.

  (* The subject operand bag (the M-reflect walk reads it off the SAME subtree the host oracle
     `structural_ac_contract_call` reconstructs from σ) and the LOCATED bag the co-installed MATCH
     receiver picks from (one send per element on the site-keyed `ac:` carrier — order-independent,
     so a PERMUTATION of the subject bag). Elements are STRUCTURED. *)
  Variable subject_struct_bag located_struct_bag : list StructElem.
  Hypothesis struct_located_is_spread :
    Permutation located_struct_bag subject_struct_bag.

  (* (S-AC.1a) THE LOCATED STRUCTURED BAG = THE SUBJECT OPERAND BAG: a (selection, rest) is an AC
     partition of the located bag IFF it is one of the subject bag — the native `sub_pars` picks the
     SAME structured elements whether sourced from the spread or (hypothetically) the report, because
     the spread only permutes the bag. Polymorphic over `StructElem` (Permutation is order-
     independent), the structured analogue of `located_matches_subject`. *)
  Theorem located_struct_matches_subject : forall selection rest,
    Permutation (selection ++ rest) located_struct_bag <->
    Permutation (selection ++ rest) subject_struct_bag.
  Proof.
    intros selection rest. split; intro H.
    - apply Permutation_trans with located_struct_bag; [ exact H | exact struct_located_is_spread ].
    - apply Permutation_trans with subject_struct_bag;
        [ exact H | apply Permutation_sym; exact struct_located_is_spread ].
  Qed.

  (* The channel-occurrence multiset of the located bag PERMUTES that of the subject (map preserves
     Permutation) — the guard slots N_i re-source faithfully. *)
  Lemma located_names_perm :
    Permutation (names located_struct_bag) (names subject_struct_bag).
  Proof. unfold names. apply Permutation_map. exact struct_located_is_spread. Qed.

  (* Reuse `sub_multiset_perm_iff` (hence AC-i `ac_match_iff_partition`): the located bag's channel-
     occurrence multiset admits the SAME AC sub-multiset matches as the subject's. *)
  Theorem located_struct_names_match_subject : forall sel_names,
    sub_multiset sel_names (names located_struct_bag) <->
    sub_multiset sel_names (names subject_struct_bag).
  Proof. intro sel_names. apply sub_multiset_perm_iff. exact located_names_perm. Qed.

  (* The located channel-occurrence match set = the order-independent partitions of the LOCATED bag —
     reusing AC-i (`ac_match_iff_partition`) over the located names, transported to the subject via
     `located_struct_names_match_subject`. The genuine in-Rho structural-AC match, at the guard slots. *)
  Corollary located_struct_names_iff_partition : forall sel_names,
    sub_multiset sel_names (names subject_struct_bag) <->
    exists rest, Permutation (sel_names ++ rest) (names located_struct_bag).
  Proof.
    intro sel_names. split.
    - intro Hs. apply (proj2 (located_struct_names_match_subject sel_names)) in Hs.
      apply (proj1 (ac_match_iff_partition sel_names (names located_struct_bag))). exact Hs.
    - intros [rest Hp]. apply (proj1 (located_struct_names_match_subject sel_names)).
      apply (proj2 (ac_match_iff_partition sel_names (names located_struct_bag))).
      exists rest. exact Hp.
  Qed.

  (* The structural-reduct multiset of the located bag PERMUTES that of the subject (`flat_map`
     congruence) — the RHS elements r_j re-source faithfully; binding them from the bag ≡ recovering
     them from σ. *)
  Lemma located_reducts_perm :
    Permutation (reducts located_struct_bag) (reducts subject_struct_bag).
  Proof. unfold reducts. apply Permutation_flat_map_se. exact struct_located_is_spread. Qed.

  (* The σ a partition (selection, rest) delivers: (channel occurrences, structural reducts, residual
     bag) — read by BOTH the spread (off the located bag) and the report (off the subject bag). *)
  Definition delivered_sigma (selection rest : list StructElem)
    : list nat * list nat * list StructElem :=
    (names selection, reducts selection, rest).

  (* (S-AC.2) SPREAD σ = REPORT σ: the SET of σ the spread can bind (from a LOCATED-bag partition)
     EQUALS the set the report can deliver (from a SUBJECT-bag partition). Every σ is deliverable from
     the spread IFF from the report — re-sourcing the bag host→spread neither adds, drops, nor
     perturbs a σ. Non-vacuous: it quantifies over ALL partitions and pivots on S-AC.1a (located =
     subject), with the projections `names`/`reducts`/`rest` functions of the shared selection. This
     is the corrupted-σ probe `s_ac_structural_bag_is_produced_by_the_spread_not_the_report` made
     precise: the deliverable σ is the SUBJECT's, for ANY report. *)
  Theorem deliverable_sigma_sets_agree : forall sigma,
    (exists selection rest,
       Permutation (selection ++ rest) located_struct_bag /\
       delivered_sigma selection rest = sigma) <->
    (exists selection rest,
       Permutation (selection ++ rest) subject_struct_bag /\
       delivered_sigma selection rest = sigma).
  Proof.
    intro sigma. split.
    - intros [selection [rest [Hp Hs]]]. exists selection, rest. split; [| exact Hs ].
      apply (proj1 (located_struct_matches_subject selection rest)). exact Hp.
    - intros [selection [rest [Hp Hs]]]. exists selection, rest. split; [| exact Hs ].
      apply (proj2 (located_struct_matches_subject selection rest)). exact Hp.
  Qed.

  (* (S-AC.4 / OUT = ⟦R⟧σ) The fired OUT bag re-sourced from the SPREAD is a PERMUTATION of the
     report's `⟦R⟧σ`: the reducts re-sourced from the spread permute the report's reducts
     (`located_reducts_perm`), so the whole spliced bag `reducts ⊎ rest` agrees as a MULTISET — the
     fired OUT bag = `⟦R⟧σ`, never the corrupted report's decoy. *)
  Theorem fired_bag_permutes_report_rhs : forall rest_ids,
    Permutation
      (reducts located_struct_bag ++ rest_ids)
      (reducts subject_struct_bag ++ rest_ids).
  Proof. intro rest_ids. apply Permutation_app_tail. exact located_reducts_perm. Qed.

  (* (S-AC CAPSTONE) THE GENUINE IN-RHO STRUCTURAL-AC REPLACEMENT: for every located-bag partition
     (selection, rest) — the spread MATCH — (a) the SAME partition is a subject-bag partition
     (located = subject, S-AC.1a), (b) the σ bound (`names`, `reducts`, `rest`) is exactly a report
     delivery from the subject (S-AC.2), and (c) the fired bag `reducts ++ rest` reconstructs the RHS
     multiset, multiplicity-preserving (S-AC.4). So OUT = `⟦R⟧σ`, sourced from the SUBJECT, never the
     report. *)
  Theorem structural_ac_spread_is_report_faithful : forall selection rest rest_ids,
    Permutation (selection ++ rest) located_struct_bag ->
    Permutation (selection ++ rest) subject_struct_bag
    /\ (exists s r, Permutation (s ++ r) subject_struct_bag
                    /\ delivered_sigma s r = delivered_sigma selection rest)
    /\ flatten (map Leaf (reducts selection) ++ [Sub rest_ids]) = reducts selection ++ rest_ids.
  Proof.
    intros selection rest rest_ids Hloc. split; [| split ].
    - apply (proj1 (located_struct_matches_subject selection rest)). exact Hloc.
    - exists selection, rest. split; [| reflexivity ].
      apply (proj1 (located_struct_matches_subject selection rest)). exact Hloc.
    - apply fired_bag_is_reducts_splice_rest.
  Qed.

End StructuralAcSpreadMatch.

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

(* ---- Stage 4 S-binder (SLICE 3b, structured-element AC spread match) ---- *)
Print Assumptions fired_bag_is_reducts_splice_rest.
Print Assumptions located_struct_matches_subject.
Print Assumptions located_names_perm.
Print Assumptions located_struct_names_match_subject.
Print Assumptions located_struct_names_iff_partition.
Print Assumptions located_reducts_perm.
Print Assumptions deliverable_sigma_sets_agree.
Print Assumptions fired_bag_permutes_report_rhs.
Print Assumptions structural_ac_spread_is_report_faithful.
