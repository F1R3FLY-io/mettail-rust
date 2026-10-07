(** A retained speculative receive must not lose cost-signature evidence.

    The current waiting-continuation wire format retains aggregate authority
    but not an invertible signature for each bind. This model describes the
    deliberately conservative reifier: it may emit unsigned binds only when
    pattern/channel arity is exact and aggregate authority is absent. It says
    nothing about a future versioned
    representation that can preserve individual signatures. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.

Record Waiting := {
  channel_count : nat;
  pattern_count : nat;
  system_body : bool;
  aggregate_authority : option nat
}.

Inductive ReifyError :=
| EmptyChannelGroup
| PatternArityMismatch
| SystemContinuation
| UnreifiableCostAuthority.

Definition reify_waiting (waiting : Waiting)
    : ReifyError + list (option nat) :=
  if Nat.eqb (channel_count waiting) 0 then inl EmptyChannelGroup
  else if Nat.eqb (pattern_count waiting) (channel_count waiting)
       then match aggregate_authority waiting with
            | Some _ => inl UnreifiableCostAuthority
            | None => if system_body waiting then inl SystemContinuation
                      else inr (repeat None (channel_count waiting))
            end
       else inl PatternArityMismatch.

Fixpoint reify_waiting_roster (waiting : list Waiting)
    : ReifyError + list (option nat) :=
  match waiting with
  | [] => inr []
  | first :: rest =>
      match reify_waiting first with
      | inl error => inl error
      | inr binds =>
          match reify_waiting_roster rest with
          | inl error => inl error
          | inr remaining => inr (binds ++ remaining)
          end
      end
  end.

Theorem reify_waiting_success_has_no_lost_authority :
  forall waiting binds,
    reify_waiting waiting = inr binds ->
    aggregate_authority waiting = None.
Proof.
  intros [count patterns system authority] binds H.
  unfold reify_waiting in H; simpl in *.
  destruct (Nat.eqb count 0); [discriminate|].
  destruct (Nat.eqb patterns count); [|discriminate].
  destruct authority; [discriminate|reflexivity].
Qed.

Theorem reify_waiting_success_has_exact_pattern_arity :
  forall waiting binds,
    reify_waiting waiting = inr binds ->
    pattern_count waiting = channel_count waiting.
Proof.
  intros [count patterns system authority] binds H.
  unfold reify_waiting in H; simpl in *.
  destruct (Nat.eqb count 0); [discriminate|].
  destruct (Nat.eqb patterns count) eqn:Harity; [|discriminate].
  now apply Nat.eqb_eq in Harity.
Qed.

Theorem retained_authority_refuses_before_body_inspection :
  forall waiting authority,
    channel_count waiting <> 0 ->
    pattern_count waiting = channel_count waiting ->
    aggregate_authority waiting = Some authority ->
    reify_waiting waiting = inl UnreifiableCostAuthority.
Proof.
  intros [count patterns system present] authority Hnonempty Harity Hpresent.
  unfold reify_waiting; simpl in *.
  apply Nat.eqb_neq in Hnonempty.
  rewrite Hnonempty.
  subst patterns.
  rewrite Nat.eqb_refl.
  rewrite Hpresent.
  reflexivity.
Qed.

Theorem reify_roster_success_has_no_lost_authority :
  forall waiting binds,
    reify_waiting_roster waiting = inr binds ->
    Forall (fun entry => aggregate_authority entry = None) waiting.
Proof.
  induction waiting as [|first rest IH]; intros binds H; simpl in *.
  - constructor.
  - destruct (reify_waiting first) as [error|first_binds] eqn:Hfirst;
      [discriminate|].
    destruct (reify_waiting_roster rest) as [error|rest_binds] eqn:Hrest;
      [discriminate|].
    constructor.
    + eapply reify_waiting_success_has_no_lost_authority; eauto.
    + eapply IH; eauto.
Qed.

Theorem reify_roster_success_has_exact_pattern_arity :
  forall waiting binds,
    reify_waiting_roster waiting = inr binds ->
    Forall (fun entry => pattern_count entry = channel_count entry) waiting.
Proof.
  induction waiting as [|first rest IH]; intros binds H; simpl in *.
  - constructor.
  - destruct (reify_waiting first) as [error|first_binds] eqn:Hfirst;
      [discriminate|].
    destruct (reify_waiting_roster rest) as [error|rest_binds] eqn:Hrest;
      [discriminate|].
    constructor.
    + eapply reify_waiting_success_has_exact_pattern_arity; eauto.
    + eapply IH; eauto.
Qed.

Theorem any_retained_authority_refuses_publication :
  forall waiting,
    (exists entry, In entry waiting /\ aggregate_authority entry <> None) ->
    forall binds, reify_waiting_roster waiting <> inr binds.
Proof.
  intros waiting [entry [Hin Hcost]] binds Hsuccess.
  apply reify_roster_success_has_no_lost_authority in Hsuccess.
  apply Forall_forall with (x := entry) in Hsuccess; auto.
Qed.

(** The reducer evaluates each signed bind and extends its continuation
    authority before storing it. Region construction and extension may fail;
    a failed receive never reaches the waiting store. [region_of] abstracts
    the exact entropy- and position-dependent constructor. [extend] abstracts
    the canonicalizing authority merger: it may deduplicate an existing region
    and therefore is NOT assumed to increase the cardinality. Its one required
    law is that successfully adding a region cannot yield empty authority.
    The initial accumulator represents already present outer authority. *)
Definition extension_retains_region
    (extend : list nat -> nat -> option (list nat)) : Prop :=
  forall regions region result,
    extend regions region = Some result -> result <> [].

(** Concrete success-path witness for the implementation's canonicalizing
    map: equal region identities may collapse, but the newly supplied region
    remains represented. Invalid identities or conflicting signatures fail
    before this success path and are modeled by [None] above. *)
Definition deduplicating_extend (regions : list nat) (region : nat)
    : option (list nat) :=
  Some (nodup Nat.eq_dec (region :: regions)).

Theorem deduplicating_extension_retains_region :
  extension_retains_region deduplicating_extend.
Proof.
  intros regions region result Hextended.
  unfold deduplicating_extend in Hextended.
  remember (nodup Nat.eq_dec (region :: regions)) as canonical eqn:Hcanonical.
  injection Hextended as Hsame.
  intro Hempty.
  assert (Hin : In region canonical).
  { rewrite Hcanonical.
    apply (proj2 (nodup_In Nat.eq_dec (region :: regions) region)).
    simpl; auto. }
  rewrite Hsame, Hempty in Hin. contradiction.
Qed.

Fixpoint retain_signed_regions
    (region_of : nat -> nat -> option nat)
    (extend : list nat -> nat -> option (list nat))
    (position : nat) (binds : list (option nat)) (regions : list nat)
    : option (list nat) :=
  match binds with
  | [] => Some regions
  | None :: rest => retain_signed_regions region_of extend (S position) rest regions
  | Some signature :: rest =>
      match region_of position signature with
      | None => None
      | Some region =>
          match extend regions region with
          | None => None
          | Some extended =>
              retain_signed_regions region_of extend (S position) rest extended
          end
      end
  end.

Lemma retained_regions_never_disappear :
  forall region_of extend position binds regions result,
    extension_retains_region extend ->
    regions <> [] ->
    retain_signed_regions region_of extend position binds regions = Some result ->
    result <> [].
Proof.
  intros region_of extend position binds.
  revert position.
  induction binds as [|bind rest IH];
    intros position regions result Hextend Hnonempty Hsuccess;
    simpl in Hsuccess.
  - inversion Hsuccess; subst; assumption.
  - destruct bind as [signature|].
    + destruct (region_of position signature) as [region|] eqn:Hregion;
        [|discriminate].
      destruct (extend regions region) as [extended|] eqn:Hextended;
        [|discriminate].
      eapply (IH (S position) extended);
        [exact Hextend|eapply Hextend; exact Hextended|exact Hsuccess].
    + eapply (IH (S position) regions); eauto.
Qed.

Theorem successful_signed_receive_retains_authority :
  forall region_of extend position binds regions result,
    extension_retains_region extend ->
    Exists (fun bind => exists signature, bind = Some signature) binds ->
    retain_signed_regions region_of extend position binds regions = Some result ->
    result <> [].
Proof.
  intros region_of extend position binds.
  revert position.
  induction binds as [|bind rest IH];
    intros position regions result Hextend Hsigned Hsuccess.
  - inversion Hsigned.
  - simpl in Hsuccess.
    inversion Hsigned as [head tail Hhead|head tail Htail]; subst.
    + destruct Hhead as [signature Hsignature]; subst bind.
      destruct (region_of position signature) as [region|] eqn:Hregion;
        [|discriminate].
      destruct (extend regions region) as [extended|] eqn:Hextended;
        [|discriminate].
      eapply (retained_regions_never_disappear
        region_of extend (S position) rest extended result);
        [exact Hextend|eapply Hextend; exact Hextended|exact Hsuccess].
    + destruct bind as [signature|].
      * destruct (region_of position signature) as [region|] eqn:Hregion;
          [|discriminate].
        destruct (extend regions region) as [extended|] eqn:Hextended;
          [|discriminate].
        eapply (IH (S position) extended); eauto.
      * eapply (IH (S position) regions); eauto.
Qed.

Definition stored_authority (regions : list nat) : option nat :=
  match regions with
  | [] => None
  | _ => Some (length regions)
  end.

(** This joins reducer admission to the reifier's non-erasure theorem: if
    any bind was signed and its region construction succeeded, the retained
    continuation cannot be published as an unsigned receive, regardless of
    channel/pattern arity or continuation-body kind. *)
Theorem signed_waiting_cannot_publish_as_unsigned :
  forall region_of extend position binds initial_regions result count patterns system emitted,
    extension_retains_region extend ->
    Exists (fun bind => exists signature, bind = Some signature) binds ->
    retain_signed_regions region_of extend position binds initial_regions = Some result ->
    reify_waiting {| channel_count := count;
                     pattern_count := patterns;
                     system_body := system;
                     aggregate_authority := stored_authority result |} <> inr emitted.
Proof.
  intros region_of extend position binds initial_regions result count patterns system emitted
    Hextend Hsigned Hretained Hpublished.
  pose proof (successful_signed_receive_retains_authority
    region_of extend position binds initial_regions result
    Hextend Hsigned Hretained) as Hnonempty.
  apply reify_waiting_success_has_no_lost_authority in Hpublished.
  destruct result as [|region rest]; [contradiction|].
  simpl in Hpublished. discriminate.
Qed.
