From Stdlib Require Import List PeanoNat Bool Lia.
From RhoBridge Require Import MettaFundingLawsConformance.
From CostAccountedRho Require Import AuthorityPresentation LocatedAuthoritySettlement
  LocatedStackConsumption CanonicalCustodyAliasing NativeFundingSnapshot
  OrderedStackMaterialization CostAccountedSyntax CAJoinConservation
  StagedGuestFundingObligations.
Import ListNotations.

Module AP := AuthorityPresentation.
Module LS := LocatedStackConsumption.
Module CC := CanonicalCustodyAliasing.
Module NS := NativeFundingSnapshot.
Module OS := OrderedStackMaterialization.
Module SG := StagedGuestFundingObligations.StagedGuestFundingObligations.

Definition LaneDemand := nat -> nat.

Definition covers (supply demand : LaneDemand) : Prop :=
  forall lane, demand lane <= supply lane.

Fixpoint demand_envelope (demands : list LaneDemand) : LaneDemand :=
  match demands with
  | [] => fun _ => 0
  | demand :: tail => fun lane => Nat.max (demand lane) (demand_envelope tail lane)
  end.

Theorem demand_envelope_covers_each : forall demands demand,
  In demand demands -> covers (demand_envelope demands) demand.
Proof.
  induction demands as [|head tail IH]; intros demand Hin lane.
  - contradiction.
  - destruct Hin as [<- | Hin]; simpl.
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Theorem demand_envelope_is_least : forall demands supply,
  (forall demand, In demand demands -> covers supply demand) ->
  covers supply (demand_envelope demands).
Proof.
  induction demands as [|head tail IH]; intros supply H lane; simpl.
  - apply Nat.le_0_l.
  - apply Nat.max_lub.
    + apply H. left. reflexivity.
    + apply IH. intros demand Hin. apply H. right. exact Hin.
Qed.

Definition relational_roster_funded {Witness : Type}
    (authenticated_prefix : Witness -> LaneDemand -> Prop)
    (demands : list LaneDemand) : Prop :=
  exists witness supply,
    authenticated_prefix witness supply /\
    forall demand, In demand demands -> covers supply demand.

Theorem common_witness_iff_feasible_envelope :
  forall (Witness : Type) (relation : Witness -> LaneDemand -> Prop) demands,
    relational_roster_funded relation demands <->
    exists witness supply,
      relation witness supply /\ covers supply (demand_envelope demands).
Proof.
  intros Witness relation demands. split.
  - intros [witness [supply [Hauth Hall]]].
    exists witness, supply. split; [exact Hauth |].
    apply demand_envelope_is_least. exact Hall.
  - intros [witness [supply [Hauth Henv]]].
    exists witness, supply. split; [exact Hauth |].
    intros demand Hin lane.
    eapply Nat.le_trans.
    + exact (demand_envelope_covers_each demands demand Hin lane).
    + apply Henv.
Qed.

Theorem relational_supply_entails_existing_lane_check :
  forall (Witness : Type) (relation : Witness -> LaneDemand -> Prop)
      demands witness supply,
    relation witness supply ->
    covers supply (demand_envelope demands) ->
    relation witness supply /\
    forall demand, In demand demands -> forall lane,
      is_funded (demand lane) (supply lane) false = true.
Proof.
  intros Witness relation demands witness supply Hauth Henv.
  split; [exact Hauth |]. intros demand Hin lane.
  apply law_sound. split; [reflexivity |].
  eapply Nat.le_trans.
  - exact (demand_envelope_covers_each demands demand Hin lane).
  - apply Henv.
Qed.

Theorem two_axis_composition_retains_both_witnesses :
  forall (PhysicalWitness MonetaryWitness : Type)
      (physical : PhysicalWitness -> LaneDemand -> Prop)
      (monetary : MonetaryWitness -> Prop) demands,
    relational_roster_funded physical demands ->
    (exists economic_witness, monetary economic_witness) ->
    exists physical_witness supply economic_witness,
      physical physical_witness supply /\
      monetary economic_witness /\
      forall demand, In demand demands -> covers supply demand.
Proof.
  intros PhysicalWitness MonetaryWitness physical monetary demands
    [physical_witness [supply [Hphysical Hcovers]]]
    [economic_witness Hmonetary].
  exists physical_witness, supply, economic_witness. auto.
Qed.

Theorem conservative_analyzer_composes_with_relational_supply :
  forall (Candidate Trace Witness : Type)
      (bound : Candidate -> LaneDemand) (actual : Trace -> LaneDemand)
      (realizes : Candidate -> Trace -> Prop)
      (relation : Witness -> LaneDemand -> Prop) candidates witness supply,
    (forall candidate trace, In candidate candidates -> realizes candidate trace ->
      covers (bound candidate) (actual trace)) ->
    relation witness supply ->
    (forall candidate, In candidate candidates -> covers supply (bound candidate)) ->
    relation witness supply /\
    forall candidate trace, In candidate candidates -> realizes candidate trace ->
      covers supply (actual trace).
Proof.
  intros Candidate Trace Witness bound actual realizes relation candidates witness
    supply Hanalyzer Hrelation Hfunded. split; [exact Hrelation |].
  intros candidate trace Hin Hrealizes lane.
  eapply Nat.le_trans.
  - exact (Hanalyzer candidate trace Hin Hrealizes lane).
  - exact (Hfunded candidate Hin lane).
Qed.

Theorem same_invocation_two_axis_composition :
  forall (PhysicalWitness MonetaryWitness : Type)
      (physical : SG.invocation_identity -> PhysicalWitness -> LaneDemand -> Prop)
      (monetary : SG.invocation_identity -> MonetaryWitness -> Prop)
      identity demands,
    relational_roster_funded (physical identity) demands ->
    (exists economic_witness, monetary identity economic_witness) ->
    exists physical_witness supply economic_witness,
      physical identity physical_witness supply /\
      monetary identity economic_witness /\
      forall demand, In demand demands -> covers supply demand.
Proof.
  intros PhysicalWitness MonetaryWitness physical monetary identity demands.
  apply two_axis_composition_retains_both_witnesses.
Qed.

Definition one_lane (target quantity : nat) : LaneDemand :=
  fun lane => if Nat.eqb lane target then quantity else 0.

Example independently_specified_finite_bound_is_conservative :
  covers (one_lane 7 2) (one_lane 7 1).
Proof.
  intro lane. unfold one_lane. destruct (Nat.eqb lane 7); lia.
Qed.

Example inner_lane_cannot_use_outer_signer_supply :
  ~ covers (one_lane 0 10) (one_lane 1 1).
Proof.
  intro H. specialize (H 1). unfold one_lane in H. simpl in H. lia.
Qed.

Record ResourceKey := {
  resource_location : nat;
  resource_class : nat;
  resource_terms : nat;
  resource_authority : nat
}.

Definition resource_at (location class terms authority : nat) : ResourceKey :=
  {| resource_location := location; resource_class := class;
     resource_terms := terms; resource_authority := authority |}.

Theorem authority_lane_erasure_loses_resource_identity :
  forall location class terms authority,
    let original := resource_at location class terms authority in
    let changed_class := resource_at location (S class) terms authority in
    let changed_terms := resource_at location class (S terms) authority in
    let changed_location := resource_at (S location) class terms authority in
    resource_authority original = resource_authority changed_class /\
    resource_authority original = resource_authority changed_terms /\
    resource_authority original = resource_authority changed_location /\
    original <> changed_class /\ original <> changed_terms /\
    original <> changed_location.
Proof.
  intros. cbn. repeat split; try reflexivity; intro Heq;
    inversion Heq; lia.
Qed.

Record DemandPair := { left_units : nat; right_units : nat }.

Definition pair (left right : nat) : DemandPair :=
  {| left_units := left; right_units := right |}.

Definition covers_pair (supply demand : DemandPair) : Prop :=
  left_units demand <= left_units supply /\
  right_units demand <= right_units supply.

Definition same_custody_feasible (capacity : nat) (demand : DemandPair) : Prop :=
  left_units demand + right_units demand <= capacity.

Definition pair_envelope (left right : DemandPair) : DemandPair :=
  pair (Nat.max (left_units left) (left_units right))
       (Nat.max (right_units left) (right_units right)).

Theorem feasible_pair_envelope_exactly_common_supply : forall capacity left right,
  same_custody_feasible capacity (pair_envelope left right) <->
  exists supply,
    same_custody_feasible capacity supply /\
    covers_pair supply left /\ covers_pair supply right.
Proof.
  intros capacity left right. split.
  - intro H. exists (pair_envelope left right).
    split; [exact H |]. unfold covers_pair, pair_envelope, pair; simpl.
    repeat split; apply Nat.le_max_l || apply Nat.le_max_r.
  - intros [supply [Hcapacity [[Hll Hlr] [Hrl Hrr]]]].
    unfold same_custody_feasible, pair_envelope, pair in *; simpl in *.
    assert (Hl : Nat.max (left_units left) (left_units right) <= left_units supply)
      by (apply Nat.max_lub; assumption).
    assert (Hr : Nat.max (right_units left) (right_units right) <= right_units supply)
      by (apply Nat.max_lub; assumption).
    lia.
Qed.

Example individually_fundable_alternatives_have_no_common_supply :
  same_custody_feasible 1 (pair 1 0) /\
  same_custody_feasible 1 (pair 0 1) /\
  ~ exists supply,
      same_custody_feasible 1 supply /\
      covers_pair supply (pair 1 0) /\ covers_pair supply (pair 0 1).
Proof.
  repeat split; try (unfold same_custody_feasible, pair; simpl; lia).
  intros [supply [Hcapacity [[Hleft _] [_ Hright]]]].
  unfold same_custody_feasible in Hcapacity. simpl in *. lia.
Qed.

Example shared_custody_is_not_two_independent_balances :
  1 <= 1 /\ 1 <= 1 /\ ~ same_custody_feasible 1 (pair 1 1).
Proof. unfold same_custody_feasible, pair. simpl. lia. Qed.

Record PrefixSource := {
  source_root : nat;
  source_custody : nat;
  source_resource : ResourceKey;
  source_available_after : option nat;
  source_may_provision : bool;
  source_may_spend : bool
}.

Definition available_at (root event_index : nat) (source : PrefixSource) : Prop :=
  source_root source = root /\ source_may_spend source = true /\
  match source_available_after source with
  | None => True
  | Some birth_index => birth_index < event_index
  end.

Definition eligible_at (root event_index : nat) (required : ResourceKey)
    (source : PrefixSource) : Prop :=
  available_at root event_index source /\ source_resource source = required.

Theorem full_key_eligibility_keeps_provenance : forall root index required source,
  eligible_at root index required source ->
  source_root source = root /\ source_may_spend source = true /\
  resource_location (source_resource source) = resource_location required /\
  resource_class (source_resource source) = resource_class required /\
  resource_terms (source_resource source) = resource_terms required /\
  resource_authority (source_resource source) = resource_authority required.
Proof.
  intros root index required source [[Hroot [Hspend _]] Hkey].
  rewrite Hkey. repeat split; try assumption; reflexivity.
Qed.

Theorem future_or_same_event_birth_is_unavailable : forall root index birth source,
  source_available_after source = Some birth -> index <= birth ->
  ~ available_at root index source.
Proof.
  intros root index birth source Hbirth Hle [_ [_ Hready]].
  rewrite Hbirth in Hready. lia.
Qed.

Theorem provisioning_does_not_grant_spending : forall root index source,
  source_may_provision source = true -> source_may_spend source = false ->
  ~ available_at root index source.
Proof.
  intros root index source _ Hno [_ [Hspend _]]. congruence.
Qed.

Theorem wrong_root_is_unavailable : forall root index source,
  source_root source <> root -> ~ available_at root index source.
Proof. intros root index source Hwrong [Hroot _]. contradiction. Qed.

Definition parent_position_before_event (position : nat) (drawn_now : bool) : nat :=
  position - if drawn_now then 1 else 0.

Definition parent_ready (position required : nat) (drawn_now : bool) : Prop :=
  required <= parent_position_before_event position drawn_now.

Theorem same_event_parent_pop_does_not_release_child : forall required,
  0 < required -> ~ parent_ready required required true.
Proof.
  intros required Hpositive Hready.
  unfold parent_ready, parent_position_before_event in Hready. simpl in Hready. lia.
Qed.

Theorem prior_event_parent_pop_releases_local_gate : forall required,
  parent_ready required required false.
Proof. intros. unfold parent_ready, parent_position_before_event. simpl. lia. Qed.

Record NativePrefixInputs := {
  prefix_store : NS.native_root_store;
  prefix_root : nat;
  prefix_cohort : list nat;
  prefix_snapshot : NS.native_funding_snapshot;
  prefix_authorization : @NS.native_execution_authorization nat nat nat;
  prefix_envelope : nat;
  prefix_controls : nat;
  prefix_wallet_lanes : list nat;
  prefix_custody : nat -> nat;
  prefix_wallet_of : nat -> nat;
  prefix_selected_owners : list nat;
  prefix_signature : nat -> sig;
  prefix_near : nat -> ResourceKey -> Prop;
  prefix_stack_at : nat -> @LS.located_inventory sig ResourceKey;
  prefix_initial_stacks : @LS.located_inventory sig ResourceKey;
  prefix_current_stacks : @LS.located_inventory sig ResourceKey;
  prefix_events : list (@LS.located_request sig nat * (nat -> nat));
  prefix_event_position : nat -> option nat;
  prefix_birth_events : nat -> option (list nat);
  prefix_stack_root : nat -> nat;
  prefix_birth_inventory : @AP.stack_inventory sig;
  prefix_ancestor_gates : nat -> list (nat * nat)
}.

Definition prefix_requests p := map fst (prefix_events p).
Definition prefix_selections p := map LS.request_stacks (prefix_requests p).
Definition prefix_wallet_used p lane :=
  fold_right (fun event amount => snd event lane + amount) 0 (prefix_events p).
Definition prefix_balance p := NS.native_wallet_at (prefix_store p) (prefix_root p).
Definition prefix_remaining p :=
  CC.settled_balance Nat.eq_dec (prefix_wallet_lanes p) (prefix_custody p)
    (prefix_balance p) (prefix_wallet_used p).
Definition prefix_births_by_lane p id :=
  prefix_birth_events p (prefix_stack_root p id).

Record NativePrefixChecked (p : NativePrefixInputs) : Prop := {
  prefix_snapshot_checked : prefix_snapshot p =
    NS.capture_native_snapshot (prefix_store p) (prefix_root p) (prefix_cohort p);
  prefix_execution_checked :
    NS.bind_native_execution Nat.eq_dec Nat.eq_dec Nat.eq_dec
      (prefix_authorization p) (prefix_root p) (prefix_envelope p) (prefix_controls p) =
      Some (prefix_authorization p);
  prefix_wallets_unique : NoDup (prefix_wallet_lanes p);
  prefix_wallets_in_cohort : forall lane, In lane (prefix_wallet_lanes p) ->
    In (prefix_custody p lane) (prefix_cohort p);
  prefix_wallets_authorized :
    CC.direct_wallets_authorized Nat.eq_dec (prefix_wallet_of p)
      (prefix_selected_owners p) (map (prefix_custody p) (prefix_wallet_lanes p)) = true;
  prefix_stacks_rooted : prefix_initial_stacks p = prefix_stack_at p (prefix_root p);
  prefix_prior_capacity :
    CC.physically_admissible Nat.eq_dec (prefix_wallet_lanes p) (prefix_custody p)
      (prefix_balance p) (prefix_wallet_used p);
  prefix_prior_wallet_domain : forall event, In event (prefix_events p) ->
    forall lane, ~ In lane (prefix_wallet_lanes p) -> snd event lane = 0;
  prefix_located_history :
    LS.located_history (prefix_near p) (prefix_requests p)
      (prefix_initial_stacks p) (prefix_current_stacks p);
  prefix_causal_history :
    OS.causal_stack_history (prefix_event_position p) (prefix_births_by_lane p) 0
      (prefix_selections p) (LS.forget_locations (prefix_initial_stacks p))
      (LS.forget_locations (prefix_current_stacks p));
  prefix_birth_metadata :
    OS.birth_metadata_well_formed (prefix_event_position p) (prefix_birth_events p)
      (prefix_birth_inventory p);
  prefix_past_ancestor_gates : forall index request,
    nth_error (prefix_requests p) index = Some request ->
    forall id parent required, In id (LS.request_stacks request) ->
      In (parent, required) (prefix_ancestor_gates p id) ->
      required <= AP.selected_uses parent
        (map LS.request_stacks (firstn index (prefix_requests p)))
}.

Record NativePrefixPresentation := {
  presentation_wallet_draw : nat -> nat;
  presentation_stack_request : @LS.located_request sig nat;
  presentation_logical_lanes : list nat
}.

Definition presentation_wallet_cells p w : list (list sig) :=
  flat_map (fun lane => repeat (payable_sig_atoms (prefix_signature p lane))
    (presentation_wallet_draw w lane)) (prefix_wallet_lanes p).
Definition presentation_stack_cells p w : list (list sig) :=
  map (LS.selected_head (prefix_current_stacks p))
    (LS.request_stacks (presentation_stack_request w)).
Definition presentation_all_cells p w :=
  presentation_wallet_cells p w ++ presentation_stack_cells p w.
Definition presentation_required_atoms p w :=
  concat (map (fun lane => payable_sig_atoms (prefix_signature p lane))
    (presentation_logical_lanes w)).
Definition presentation_lane_supply w : LaneDemand :=
  fun lane => count_occ Nat.eq_dec (presentation_logical_lanes w) lane.

Record NativePresentationChecked (p : NativePrefixInputs)
    (w : NativePrefixPresentation) : Prop := {
  presentation_current_capacity :
    CC.physically_admissible Nat.eq_dec (prefix_wallet_lanes p) (prefix_custody p)
      (prefix_remaining p) (presentation_wallet_draw w);
  presentation_wallet_domain : forall lane,
    ~ In lane (prefix_wallet_lanes p) -> presentation_wallet_draw w lane = 0;
  presentation_located :
    LS.request_admitted (prefix_near p) (presentation_stack_request w)
      (prefix_current_stacks p);
  presentation_births_ready : forall id required,
    In id (LS.request_stacks (presentation_stack_request w)) ->
    prefix_births_by_lane p id = Some required ->
    OS.birth_ready_at (length (prefix_requests p)) (prefix_event_position p) required = true;
  presentation_ancestors_ready : forall id parent required,
    In id (LS.request_stacks (presentation_stack_request w)) ->
    In (parent, required) (prefix_ancestor_gates p id) ->
    required <= AP.selected_uses parent (prefix_selections p);
  presentation_whole_cover :
    AP.exact_cover (presentation_required_atoms p w) (presentation_all_cells p w)
}.

Definition concrete_authenticated_prefix p w supply : Prop :=
  NativePrefixChecked p /\ NativePresentationChecked p w /\
  supply = presentation_lane_supply w.

Definition staged_prefix_supply p (identity : SG.invocation_identity)
    (backing : NativePrefixPresentation * LaneDemand) : Prop :=
  concrete_authenticated_prefix p (fst backing) (snd backing) /\
  prefix_root p = SG.owner_root (SG.invocation_owner identity) /\
  length (prefix_requests p) = SG.invocation_prefix identity.

Theorem staged_common_supply_iff_concrete_prefix :
  forall p (bound : SG.guest_candidate -> LaneDemand) identity candidates,
    SG.roster_has_common_supply (NativePrefixPresentation * LaneDemand)%type
      (staged_prefix_supply p)
      (fun _ backing candidate => covers (snd backing) (bound candidate))
      identity candidates <->
    relational_roster_funded (concrete_authenticated_prefix p) (map bound candidates) /\
    prefix_root p = SG.owner_root (SG.invocation_owner identity) /\
    length (prefix_requests p) = SG.invocation_prefix identity.
Proof.
  intros p bound identity candidates.
  unfold SG.roster_has_common_supply, staged_prefix_supply. split.
  - intros [[witness supply] [[Hauth [Hroot Hprefix]] Hcovered]].
    simpl in *. split; [|auto].
    exists witness, supply. split; [exact Hauth|].
    intros demand Hin. apply in_map_iff in Hin as [candidate [<- Hin]].
    exact (proj1 (@Forall_forall SG.guest_candidate
      (fun candidate => covers supply (bound candidate)) candidates) Hcovered candidate Hin).
  - intros [[witness [supply [Hauth Hcovered]]] [Hroot Hprefix]].
    exists (witness, supply). simpl. split; [auto|].
    apply Forall_forall. intros candidate Hin.
    apply Hcovered. now apply in_map.
Qed.

Theorem concrete_prefix_retains_root_and_signed_controls : forall p w supply,
  concrete_authenticated_prefix p w supply ->
  NS.native_snapshot_root (prefix_snapshot p) = prefix_root p /\
  prefix_root p = NS.execution_authorized_root (prefix_authorization p) /\
  prefix_envelope p = NS.execution_authorized_envelope (prefix_authorization p) /\
  prefix_controls p = NS.execution_authorized_controls (prefix_authorization p).
Proof.
  intros p w supply [Hp _].
  pose proof (prefix_execution_checked p Hp) as Hbind.
  apply NS.native_execution_binding_exact in Hbind.
  rewrite (prefix_snapshot_checked p Hp). simpl. tauto.
Qed.

Theorem concrete_prefix_wallets_have_rooted_authorized_owners : forall p w supply lane,
  concrete_authenticated_prefix p w supply -> In lane (prefix_wallet_lanes p) ->
  In (prefix_custody p lane, prefix_balance p (prefix_custody p lane))
    (NS.native_snapshot_wallets (prefix_snapshot p)) /\
  exists owner, In owner (prefix_selected_owners p) /\
    prefix_wallet_of p owner = prefix_custody p lane.
Proof.
  intros p w supply lane [Hp _] Hin. split.
  - rewrite (prefix_snapshot_checked p Hp).
    apply NS.native_capture_wallet_membership_exact.
    split; [exact (prefix_wallets_in_cohort p Hp lane Hin) | reflexivity].
  - pose proof (prefix_wallets_authorized p Hp) as Howners.
    pose proof (proj1 (CC.direct_wallet_authorization_exact Nat.eq_dec
      (prefix_wallet_of p) (prefix_selected_owners p)
      (map (prefix_custody p) (prefix_wallet_lanes p))) Howners) as Howner_map.
    apply Howner_map. apply in_map. exact Hin.
Qed.

Theorem concrete_prefix_joint_capacity_and_conservation : forall p w supply custody,
  concrete_authenticated_prefix p w supply ->
  let used := CC.physical_draw Nat.eq_dec (prefix_wallet_lanes p)
    (prefix_custody p) (prefix_wallet_used p) custody in
  let current := CC.physical_draw Nat.eq_dec (prefix_wallet_lanes p)
    (prefix_custody p) (presentation_wallet_draw w) custody in
  used + current <= prefix_balance p custody /\
  CC.settled_balance Nat.eq_dec (prefix_wallet_lanes p) (prefix_custody p)
    (prefix_remaining p) (presentation_wallet_draw w) custody +
    used + current = prefix_balance p custody.
Proof.
  intros p w supply custody [Hp [Hw _]]. cbn zeta.
  pose proof (prefix_prior_capacity p Hp custody) as Hprior.
  pose proof (presentation_current_capacity p w Hw custody) as Hcurrent.
  unfold prefix_remaining, CC.settled_balance in *. lia.
Qed.

Theorem concrete_prefix_projection_keeps_whole_compound_atoms : forall p w supply atom,
  concrete_authenticated_prefix p w supply ->
  count_occ sig_eq_dec (concat (presentation_all_cells p w)) atom =
  count_occ sig_eq_dec (presentation_required_atoms p w) atom.
Proof.
  intros p w supply atom [_ [Hw _]].
  apply AP.exact_cover_preserves_each_atom.
  exact (presentation_whole_cover p w Hw).
Qed.

Theorem concrete_prefix_has_exact_ordered_residuals : forall p w supply id place cells,
  concrete_authenticated_prefix p w supply ->
  prefix_initial_stacks p id = Some (place, cells) ->
  prefix_current_stacks p id =
    Some (place, skipn (AP.selected_uses id (prefix_selections p)) cells) /\
  AP.selected_uses id (prefix_selections p) <= length cells.
Proof.
  intros p w supply id place cells [Hp _] Hcells.
  exact (LS.located_histories_preserve_exact_suffix (prefix_near p) _ _ _
    (prefix_located_history p Hp) id place cells Hcells).
Qed.

Theorem concrete_prefix_selected_births_strictly_precede :
  forall p w supply id required event,
    concrete_authenticated_prefix p w supply ->
    In id (LS.request_stacks (presentation_stack_request w)) ->
    prefix_births_by_lane p id = Some required -> In event required ->
    exists position, prefix_event_position p event = Some position /\
      position < length (prefix_requests p).
Proof.
  intros p w supply id required event [_ [Hw _]] Hid Hbirth Hevent.
  eapply OS.every_birth_event_precedes_ready_use; [|exact Hevent].
  exact (presentation_births_ready p w Hw id required Hid Hbirth).
Qed.

Theorem concrete_prefix_selected_ancestors_are_prior_pops :
  forall p w supply id parent required,
    concrete_authenticated_prefix p w supply ->
    In id (LS.request_stacks (presentation_stack_request w)) ->
    In (parent, required) (prefix_ancestor_gates p id) ->
    required <= AP.selected_uses parent (prefix_selections p).
Proof.
  intros p w supply id parent required [_ [Hw _]].
  exact (presentation_ancestors_ready p w Hw id parent required).
Qed.

Theorem concrete_prefix_rejects_shared_custody_overdraw :
  forall p w supply left right custody,
    prefix_wallet_lanes p = [left; right] ->
    prefix_custody p left = custody -> prefix_custody p right = custody ->
    prefix_balance p custody = 1 ->
    presentation_wallet_draw w left = 1 -> presentation_wallet_draw w right = 1 ->
    ~ concrete_authenticated_prefix p w supply.
Proof.
  intros p w supply left right custody Hlanes Hleft Hright Hcapacity
    Hdraw_left Hdraw_right Hprefix.
  pose proof (proj1 (concrete_prefix_joint_capacity_and_conservation
    p w supply custody Hprefix)) as Hbound.
  unfold CC.physical_draw in Hbound.
  rewrite Hlanes, Hcapacity in Hbound. cbn in Hbound.
  rewrite Hleft, Hright, Hdraw_left, Hdraw_right in Hbound.
  destruct (Nat.eq_dec custody custody); [lia |contradiction].
Qed.

Theorem concrete_prefix_rejects_same_or_future_birth :
  forall p w supply id required event position,
    In id (LS.request_stacks (presentation_stack_request w)) ->
    prefix_births_by_lane p id = Some required -> In event required ->
    prefix_event_position p event = Some position ->
    length (prefix_requests p) <= position ->
    ~ concrete_authenticated_prefix p w supply.
Proof.
  intros p w supply id required event position Hid Hbirth Hevent Hposition Hlater Hprefix.
  destruct (concrete_prefix_selected_births_strictly_precede
    p w supply id required event Hprefix Hid Hbirth Hevent) as [actual [Hactual Hprior]].
  rewrite Hposition in Hactual. inversion Hactual. lia.
Qed.

Theorem concrete_roster_instantiates_relational_funding : forall p w demands,
  NativePrefixChecked p -> NativePresentationChecked p w ->
  covers (presentation_lane_supply w) (demand_envelope demands) ->
  relational_roster_funded (concrete_authenticated_prefix p) demands.
Proof.
  intros p w demands Hp Hw Hcover.
  apply common_witness_iff_feasible_envelope.
  exists w, (presentation_lane_supply w). split; [|exact Hcover].
  split; [exact Hp |]. split; [exact Hw |reflexivity].
Qed.

Theorem concrete_roster_retains_joint_backing : forall p demands,
  relational_roster_funded (concrete_authenticated_prefix p) demands ->
  exists w supply,
    concrete_authenticated_prefix p w supply /\
    (forall custody,
      CC.physical_draw Nat.eq_dec (prefix_wallet_lanes p) (prefix_custody p)
        (prefix_wallet_used p) custody +
      CC.physical_draw Nat.eq_dec (prefix_wallet_lanes p) (prefix_custody p)
        (presentation_wallet_draw w) custody <= prefix_balance p custody) /\
    (forall atom,
      count_occ sig_eq_dec (concat (presentation_all_cells p w)) atom =
      count_occ sig_eq_dec (presentation_required_atoms p w) atom) /\
    forall demand, In demand demands -> forall lane,
      is_funded (demand lane) (supply lane) false = true.
Proof.
  intros p demands [w [supply [Hprefix Hcovers]]].
  exists w, supply. split; [exact Hprefix |]. split.
  - intro custody. exact (proj1
      (concrete_prefix_joint_capacity_and_conservation p w supply custody Hprefix)).
  - split.
    + intro atom. exact (concrete_prefix_projection_keeps_whole_compound_atoms
        p w supply atom Hprefix).
    + intros demand Hin lane. apply law_sound. split; [reflexivity |].
      exact (Hcovers demand Hin lane).
Qed.

Definition finite_compound_atoms := [SGround [false]; SGround [true]].
Definition finite_compound_inventory : @LS.located_inventory sig ResourceKey :=
  fun id => if Nat.eq_dec id 0 then
    Some (resource_at 0 0 0 0, [finite_compound_atoms]) else None.
Definition finite_compound_request : @LS.located_request sig nat :=
  {| LS.request_surface := 0; LS.request_demand := finite_compound_atoms;
     LS.request_stacks := [0] |}.

Example complete_compound_head_has_concrete_located_admission :
  LS.request_admitted (fun cut place => cut = resource_location place)
    finite_compound_request finite_compound_inventory.
Proof. apply LS.one_compound_head_is_admitted. reflexivity. Qed.

Example compound_partial_draw_has_no_located_admission :
  ~ LS.request_admitted (fun cut place => cut = resource_location place)
    {| LS.request_surface := 0; LS.request_demand := [SGround [false]];
       LS.request_stacks := [0] |} finite_compound_inventory.
Proof.
  intros [_ [_ Hcover]].
  apply AP.exact_cover_preserves_cardinality in Hcover.
  cbv in Hcover. discriminate.
Qed.

Definition finite_prefix_store : NS.native_root_store :=
  {| NS.native_wallet_at := fun _ _ => 0;
     NS.native_cursor_at := fun _ _ => None |}.

Definition finite_native_prefix : NativePrefixInputs :=
  {| prefix_store := finite_prefix_store;
     prefix_root := 7;
     prefix_cohort := [];
     prefix_snapshot := NS.capture_native_snapshot finite_prefix_store 7 [];
     prefix_authorization :=
       {| NS.execution_authorized_root := 7;
          NS.execution_authorized_envelope := 11;
          NS.execution_authorized_controls := 13 |};
     prefix_envelope := 11;
     prefix_controls := 13;
     prefix_wallet_lanes := [];
     prefix_custody := fun lane => lane;
     prefix_wallet_of := fun owner => owner;
     prefix_selected_owners := [];
     prefix_signature := fun _ => SAnd (SGround [false]) (SGround [true]);
     prefix_near := fun cut place => cut = resource_location place;
     prefix_stack_at := fun _ => finite_compound_inventory;
     prefix_initial_stacks := finite_compound_inventory;
     prefix_current_stacks := finite_compound_inventory;
     prefix_events := [];
     prefix_event_position := fun _ => None;
     prefix_birth_events := fun _ => None;
     prefix_stack_root := fun id => id;
     prefix_birth_inventory := fun _ => None;
     prefix_ancestor_gates := fun _ => [] |}.

Definition finite_native_presentation : NativePrefixPresentation :=
  {| presentation_wallet_draw := fun _ => 0;
     presentation_stack_request := finite_compound_request;
     presentation_logical_lanes := [42] |}.

Theorem finite_native_prefix_is_checked : NativePrefixChecked finite_native_prefix.
Proof.
  constructor.
  - reflexivity.
  - apply NS.native_execution_binding_accepts_authorized_inputs.
  - constructor.
  - intros lane Hin. contradiction.
  - reflexivity.
  - reflexivity.
  - intro custody. cbv. lia.
  - intros event Hin. contradiction.
  - constructor.
  - constructor.
  - intros id required Hbirth. discriminate.
  - intros index request Hnth. destruct index; discriminate.
Qed.

Theorem finite_native_presentation_is_checked :
  NativePresentationChecked finite_native_prefix finite_native_presentation.
Proof.
  constructor.
  - intro custody. cbv. lia.
  - intros lane _. reflexivity.
  - exact complete_compound_head_has_concrete_located_admission.
  - intros id required _ Hbirth. discriminate.
  - intros id parent required _ Hin. contradiction.
  - unfold AP.exact_cover, AP.presentation_atoms. cbn.
    apply Permutation.Permutation_refl.
Qed.

Example concrete_authenticated_relation_has_a_complete_compound_witness :
  concrete_authenticated_prefix finite_native_prefix finite_native_presentation
    (presentation_lane_supply finite_native_presentation).
Proof.
  split; [exact finite_native_prefix_is_checked |].
  split; [exact finite_native_presentation_is_checked |reflexivity].
Qed.

Example concrete_compound_roster_passes_existing_lane_check :
  relational_roster_funded (concrete_authenticated_prefix finite_native_prefix)
    [one_lane 42 1].
Proof.
  apply (concrete_roster_instantiates_relational_funding
    finite_native_prefix finite_native_presentation).
  - exact finite_native_prefix_is_checked.
  - exact finite_native_presentation_is_checked.
  - intro lane. unfold one_lane, presentation_lane_supply. cbn.
    destruct (Nat.eqb_spec lane 42); subst.
    + cbn. lia.
    + destruct (Nat.eq_dec 42 lane); [congruence |cbn; lia].
Qed.

Print Assumptions common_witness_iff_feasible_envelope.
Print Assumptions relational_supply_entails_existing_lane_check.
Print Assumptions two_axis_composition_retains_both_witnesses.
Print Assumptions same_invocation_two_axis_composition.
Print Assumptions staged_common_supply_iff_concrete_prefix.
Print Assumptions conservative_analyzer_composes_with_relational_supply.
Print Assumptions inner_lane_cannot_use_outer_signer_supply.
Print Assumptions authority_lane_erasure_loses_resource_identity.
Print Assumptions feasible_pair_envelope_exactly_common_supply.
Print Assumptions individually_fundable_alternatives_have_no_common_supply.
Print Assumptions full_key_eligibility_keeps_provenance.
Print Assumptions same_event_parent_pop_does_not_release_child.
Print Assumptions concrete_prefix_retains_root_and_signed_controls.
Print Assumptions concrete_prefix_wallets_have_rooted_authorized_owners.
Print Assumptions concrete_prefix_joint_capacity_and_conservation.
Print Assumptions concrete_prefix_projection_keeps_whole_compound_atoms.
Print Assumptions concrete_prefix_has_exact_ordered_residuals.
Print Assumptions concrete_prefix_selected_births_strictly_precede.
Print Assumptions concrete_prefix_selected_ancestors_are_prior_pops.
Print Assumptions concrete_prefix_rejects_shared_custody_overdraw.
Print Assumptions concrete_prefix_rejects_same_or_future_birth.
Print Assumptions concrete_roster_instantiates_relational_funding.
Print Assumptions concrete_roster_retains_joint_backing.
Print Assumptions complete_compound_head_has_concrete_located_admission.
Print Assumptions compound_partial_draw_has_no_located_admission.
Print Assumptions concrete_authenticated_relation_has_a_complete_compound_witness.
Print Assumptions concrete_compound_roster_passes_existing_lane_check.
