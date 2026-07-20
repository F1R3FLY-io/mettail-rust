(*
 * InRhoDriveWithFloat: FV (A-S5.8) — the DRIVER FLOAT PHASE.  The A-S5.8 firing
 * emission routes EVERY contractum through the installed `^float` dispatcher before the
 * re-drive (decision Q-AB = A: `for(@c <- r){ new rf { ^float!(c, rf) | for(@cf <- rf){
 * ^drive!(cf, fuel - 1, ret) } } }`), and the production seed routes through `^float`
 * too (decision Q-SEED = S2).  This file models that composition — `fdrives`, the
 * quiescence driver whose `d_redex_fire` analogue tests and fires on the FLOATED value
 * — over the bag-value fragment of InRhoQuiescenceDriver.v EXTENDED WITH A BINDER
 * constructor (`fval` = `bval` + `FNu`), and proves:
 *
 *   ffloat_canonical / ffloat_idempotent :
 *       the value-level float (hoist every nu to one top run, splice bags flat — the
 *       merge/dispatcher composition of InRhoFloatCanonicalization.v, here as a
 *       structural function) always yields a canonical value and is idempotent — the
 *       fixpoint property the per-firing float rests on.
 *   drive_with_float_on_raw_eq_drive_on_canonical (THE PREMISE DISCHARGE) :
 *       driving a RAW value through the float-routed driver is EXACTLY driving its
 *       float-canonical form — for EVERY firing relation.  The boundary-float premise
 *       ("contracta create no float-hidden redexes", DOC29's pre-A-S5.8 §2.1 row) is
 *       thereby discharged CONSTRUCTIVELY: nothing about the subject's rawness is load
 *       bearing any more, because the driver itself canonicalizes per iteration.
 *   nu_hidden_contractum_redex_fires (+ raw_contractum_is_not_a_redex) :
 *       the non-vacuity witness, shaped exactly like the leg-2 `Seal` witness: a firing
 *       introduces a nu-hidden half of the next redex; WITHOUT the float the raw
 *       contractum matches no rule (the load-bearing contrast), WITH the per-firing
 *       float the hidden redex is exposed and fires to quiescence.
 *   float_phase_conservative (+ corollaries) :
 *       on the nu-FREE fragment (the embedded `bval` values) the float IS the landed
 *       bag drive: `ffloat (embed b) = embed (bdrive b)`.  Every landed
 *       InRhoQuiescenceDriver bag theorem therefore transfers to the float phase as a
 *       corollary (flatness, flatten-agreement, atom preservation) — a CONSERVATIVE
 *       EXTENSION: no landed statement is weakened, InRhoQuiescenceDriver.v is
 *       untouched, and the new clauses degenerate to the landed ones on nu-free
 *       values.
 *
 * Rocq 9.1 compatible.  No Admitted, no Axioms, no Assumptions, no Parameters.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From RhoBridge Require Import InRhoQuiescenceDriver.

Import ListNotations.

(* =====================================================================================
   Part 1 — the fragment: `bval` + a BINDER constructor (`FNu` — the reflected
   `^lambda`), and the value-level float.
   ===================================================================================== *)

Inductive fval : Type :=
  | FAtom : nat -> fval             (* an opaque, never-driven leaf (= BAtom) *)
  | FBag  : list fval -> fval       (* an op-bag soup (= BBag) *)
  | FNu   : fval -> fval.           (* ONE nu binder (the reflected ^lambda) — NEW *)

(* The deep induction principle (the auto-generated one gives no hypothesis on bag
   members — the `bval_ind2` pattern). *)
Lemma fval_ind2 : forall (P : fval -> Prop),
  (forall n, P (FAtom n)) ->
  (forall l, Forall P l -> P (FBag l)) ->
  (forall w, P w -> P (FNu w)) ->
  forall v, P v.
Proof.
  intros P Hatom Hbag Hnu. fix REC 1.
  intro v; destruct v as [n | l | w].
  - apply Hatom.
  - apply Hbag. induction l as [| c cs IH].
    + apply Forall_nil.
    + apply Forall_cons; [apply REC | exact IH].
  - apply Hnu. apply REC.
Qed.

(* `wrap k v` — the k-deep nu run `FNu^k(v)` (the run-length representation). *)
Fixpoint wrap (k : nat) (v : fval) : fval :=
  match k with
  | 0 => v
  | S k' => FNu (wrap k' v)
  end.

(* Strip a float-canonical value into (run length, bag-member fragment): the merge's
   three-case dispatch composed with the run peel — a nu run peels into the run, a bag
   SPLICES its members, an atom wraps as one member. *)
Fixpoint strip (v : fval) : nat * list fval :=
  match v with
  | FNu w => let s := strip w in (S (fst s), snd s)
  | FBag ms => (0, ms)
  | FAtom n => (0, [FAtom n])
  end.

(* THE VALUE-LEVEL FLOAT (the `^float` dispatcher + `^float-merge` satellites'
   composition, as a structural function): a binder floats its body in place; a bag
   floats every element, then merges — extruding each floated element's run into one
   top run and splicing the fragments flat. *)
Fixpoint ffloat (v : fval) : fval :=
  match v with
  | FAtom n => FAtom n
  | FNu w => FNu (ffloat w)
  | FBag l =>
      let fix collect (l : list fval) : nat * list fval :=
        match l with
        | [] => (0, [])
        | e :: rest =>
            let se := strip (ffloat e) in
            let sr := collect rest in
            (fst se + fst sr, snd se ++ snd sr)
        end in
      wrap (fst (collect l)) (FBag (snd (collect l)))
  end.

(* The nested fix, exposed for reasoning. *)
Fixpoint fcollect (l : list fval) : nat * list fval :=
  match l with
  | [] => (0, [])
  | e :: rest =>
      let se := strip (ffloat e) in
      let sr := fcollect rest in
      (fst se + fst sr, snd se ++ snd sr)
  end.

Lemma ffloat_bag : forall l,
  ffloat (FBag l) = wrap (fst (fcollect l)) (FBag (snd (fcollect l))).
Proof.
  intro l. reflexivity.
Qed.

(* =====================================================================================
   Part 2 — canonical forms: ffloat_canonical + ffloat_idempotent (the fixpoint
   property).
   ===================================================================================== *)

Definition atom_like (m : fval) : Prop := exists n, m = FAtom n.
Definition flat_atoms (l : list fval) : Prop := Forall atom_like l.

(* A float-canonical value: one nu run over an atom, or one nu run over a FLAT bag. *)
Inductive fcanonical : fval -> Prop :=
  | fc_wrap_atom : forall k n, fcanonical (wrap k (FAtom n))
  | fc_wrap_bag : forall k ms, flat_atoms ms -> fcanonical (wrap k (FBag ms)).

Lemma strip_wrap_atom : forall k n, strip (wrap k (FAtom n)) = (k, [FAtom n]).
Proof.
  induction k as [| k IH]; intro n; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma strip_wrap_bag : forall k ms, strip (wrap k (FBag ms)) = (k, ms).
Proof.
  induction k as [| k IH]; intro ms; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma strip_of_canonical_flat : forall v,
  fcanonical v -> flat_atoms (snd (strip v)).
Proof.
  intros v Hc. destruct Hc as [k n | k ms Hms].
  - rewrite strip_wrap_atom. simpl.
    apply Forall_cons; [exists n; reflexivity | apply Forall_nil].
  - rewrite strip_wrap_bag. simpl. exact Hms.
Qed.

Lemma wrap_S : forall k v, FNu (wrap k v) = wrap (S k) v.
Proof. reflexivity. Qed.

(* ** ffloat_canonical: the float always rests a canonical value — every nu in ONE top
   run, every bag flat (the in-Rho family's quiescent shape). *)
Theorem ffloat_canonical : forall v, fcanonical (ffloat v).
Proof.
  intro v. induction v as [n | l IH | w IH] using fval_ind2.
  - simpl. apply (fc_wrap_atom 0).
  - rewrite ffloat_bag.
    apply fc_wrap_bag.
    induction l as [| e rest IHl]; simpl.
    + apply Forall_nil.
    + inversion IH as [| ? ? He Hrest]; subst.
      apply Forall_app. split.
      * apply strip_of_canonical_flat. exact He.
      * apply IHl. exact Hrest.
  - simpl. destruct IH as [k n | k ms Hms].
    + rewrite wrap_S. apply fc_wrap_atom.
    + rewrite wrap_S. apply fc_wrap_bag. exact Hms.
Qed.

Lemma fcollect_atoms : forall ms, flat_atoms ms -> fcollect ms = (0, ms).
Proof.
  induction ms as [| m rest IH]; intro H; simpl; [reflexivity |].
  inversion H as [| ? ? [n Hm] Hrest]; subst. simpl.
  rewrite IH by exact Hrest. reflexivity.
Qed.

(* The float FIXES canonical values (the merge base cases compose in place). *)
Lemma ffloat_fixes_canonical : forall v, fcanonical v -> ffloat v = v.
Proof.
  intros v Hc. destruct Hc as [k n | k ms Hms].
  - induction k as [| k IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  - induction k as [| k IH]; [| simpl; rewrite IH; reflexivity].
    (* k = 0: the merge base cases compose the flat members in place. *)
    change (wrap (fst (fcollect ms)) (FBag (snd (fcollect ms))) = FBag ms).
    rewrite (fcollect_atoms ms Hms). reflexivity.
Qed.

(* ** ffloat_idempotent (the fixpoint property, F8-AM-4's identity-on-canonical at the
   value level): a second float pass is the identity. *)
Theorem ffloat_idempotent : forall v, ffloat (ffloat v) = ffloat v.
Proof.
  intro v. apply ffloat_fixes_canonical. apply ffloat_canonical.
Qed.

(* =====================================================================================
   Part 3 — the FLOAT-PHASE DRIVER and THE PREMISE DISCHARGE.
   ===================================================================================== *)

Section DriveWithFloat.

  (* The abstract firing relation of the driven language: `contract subject u` fires
     the redex the driver's Match arms decide on the FLOAT-CANONICAL subject and
     delivers the contractum `u` (which may hide material under fresh nus — the
     F8-AM-1 Binder-template shape). *)
  Variable contract : fval -> fval -> Prop.

  (* The float-routed quiescence driver (the A-S5.8 emission): the redex test and the
     firing BOTH happen on the FLOATED value — `d_redex_fire` routes through float —
     and the contractum re-enters RAW (its own float happens at the next frame).  The
     rest disposition publishes the floated value (the OUT datum is float-canonical). *)
  Inductive fdrives : nat -> fval -> fval -> Prop :=
    | fd_rest : forall fuel v,
        (forall u, ~ contract (ffloat v) u) ->
        fdrives fuel v (ffloat v)
    | fd_fire : forall fuel v u r,
        contract (ffloat v) u ->
        fdrives fuel u r ->
        fdrives (S fuel) v r.

  (* ** THE PREMISE DISCHARGE (drive_with_float_on_raw = drive_on_canonical): driving
     a RAW value is EXACTLY driving its float-canonical form, for every firing
     relation and every schedule depth — the raw/canonical distinction is NOT load
     bearing once the driver floats per iteration.  (The S2 seed's identity on
     host-canonical production subjects is the `ffloat_idempotent` instance.) *)
  Theorem drive_with_float_on_raw_eq_drive_on_canonical : forall fuel v r,
    fdrives fuel v r <-> fdrives fuel (ffloat v) r.
  Proof.
    intros fuel v r. split.
    - intro H. destruct H as [fuel v Hrest | fuel v u r Hfire Hrec].
      + rewrite <- (ffloat_idempotent v) at 2.
        apply fd_rest. rewrite ffloat_idempotent. exact Hrest.
      + eapply fd_fire; [| exact Hrec].
        rewrite ffloat_idempotent. exact Hfire.
    - intro H. inversion H as [fuel' v' Hrest Hfuel Hv Hr | fuel' v' u r' Hfire Hrec]; subst.
      + rewrite ffloat_idempotent.
        apply fd_rest. rewrite ffloat_idempotent in Hrest. exact Hrest.
      + eapply fd_fire; [| exact Hrec].
        rewrite ffloat_idempotent in Hfire. exact Hfire.
  Qed.

End DriveWithFloat.

(* =====================================================================================
   Part 4 — the NON-VACUITY WITNESS (the leg-2 `Seal` shape): a firing introduces a
   nu-HIDDEN half of the next redex; the per-firing float exposes it and it fires.
   ===================================================================================== *)

(* The two-rule witness system: `Seal` fires on the seed and produces a contractum
   whose first member hides `FAtom 1` under a FRESH nu (the F8-AM-1 Binder template);
   `Open` fires only on the FLOAT-CANONICAL form `nu.{1, 2}` — the form in which the
   nu has been extruded and the bag spliced flat. *)
Inductive seal_contract : fval -> fval -> Prop :=
  | sc_seal : seal_contract (FBag [FAtom 0])
                            (FBag [FNu (FBag [FAtom 1]); FAtom 2])
  | sc_open : seal_contract (FNu (FBag [FAtom 1; FAtom 2]))
                            (FNu (FBag [FAtom 3])).

(* The LOAD-BEARING CONTRAST: the RAW `Seal` contractum matches NO rule — without the
   per-firing float the drive would rest with the Open redex hidden under the nu. *)
Lemma raw_contractum_is_not_a_redex : forall r,
  ~ seal_contract (FBag [FNu (FBag [FAtom 1]); FAtom 2]) r.
Proof.
  intros r H. inversion H.
Qed.

(* ** The witness derivation: Seal fires; the float extrudes the contractum's nu and
   splices the bag (`ffloat` computes `nu.{1, 2}`); Open fires; the drive rests at the
   canonical `nu.{3}` — the fired chain {Seal, Open} the leg-2 runtime witness pins. *)
Example nu_hidden_contractum_redex_fires :
  fdrives seal_contract 2 (FBag [FAtom 0]) (FNu (FBag [FAtom 3])).
Proof.
  apply (fd_fire seal_contract 1 (FBag [FAtom 0])
                 (FBag [FNu (FBag [FAtom 1]); FAtom 2])).
  - (* the seed floats to itself and Seal fires *)
    simpl. apply sc_seal.
  - apply (fd_fire seal_contract 0
                   (FBag [FNu (FBag [FAtom 1]); FAtom 2])
                   (FNu (FBag [FAtom 3]))).
    + (* THE FLOAT EXPOSES: ffloat of the contractum = nu.{1, 2} — and Open fires *)
      simpl. apply sc_open.
    + (* the Open contractum floats to itself (canonical) and rests *)
      replace (FNu (FBag [FAtom 3]))
        with (ffloat (FNu (FBag [FAtom 3]))) at 2 by reflexivity.
      apply fd_rest.
      intros u H. simpl in H. inversion H.
Qed.

(* =====================================================================================
   Part 5 — float_phase_conservative: on the nu-FREE fragment the float IS the landed
   bag drive, and every landed theorem transfers as a corollary (conservative
   extension — InRhoQuiescenceDriver.v untouched, no statement weakened).
   ===================================================================================== *)

Fixpoint embed (b : bval) : fval :=
  match b with
  | BAtom n => FAtom n
  | BBag l => FBag (map embed l)
  end.

(* The strip of an embedded FLAT value is its one-member fragment — exactly the host
   `frag` (the three-case dispatch's static image). *)
Lemma strip_embed_frag : forall w,
  is_flat w -> strip (embed w) = (0, map embed (frag w)).
Proof.
  intros [n | l] _; simpl; reflexivity.
Qed.

(* ** float_phase_conservative: `ffloat` on an embedded (nu-free) value computes
   EXACTLY the landed driver's bag drive. *)
Theorem float_phase_conservative : forall b, ffloat (embed b) = embed (bdrive b).
Proof.
  intro b. induction b as [n | l IH] using bval_ind2.
  - reflexivity.
  - simpl embed. rewrite ffloat_bag.
    assert (Hcoll : fcollect (map embed l)
                    = (0, map embed
                            (fold_right (fun e acc => splice_fragment (bdrive e) acc)
                                        nil l))).
    { induction l as [| c rest IHl]; simpl; [reflexivity |].
      inversion IH as [| ? ? Hc Hrest]; subst.
      rewrite IHl by exact Hrest.
      rewrite Hc.
      rewrite (strip_embed_frag (bdrive c) (bag_flatness_sound c)).
      simpl.
      rewrite splice_fragment_is_frag_app.
      rewrite map_app.
      reflexivity. }
    rewrite Hcoll. simpl. reflexivity.
Qed.

(* Corollary (the landed `bag_flatness_sound`, transferred): a nu-free float rests a
   FLAT bag of atoms. *)
Corollary nu_free_float_flatness : forall l,
  exists ms, ffloat (embed (BBag l)) = FBag ms /\ flat_atoms ms.
Proof.
  intro l. rewrite float_phase_conservative.
  simpl.
  eexists. split; [reflexivity |].
  pose proof (bag_flatness_sound (BBag l)) as Hflat.
  simpl in Hflat.
  induction (fold_right (fun e acc => splice_fragment (bdrive e) acc) nil l)
    as [| m rest IH]; simpl.
  - apply Forall_nil.
  - inversion Hflat as [| ? ? Hm Hrest]; subst.
    apply Forall_cons.
    + destruct Hm as [n ->]. exists n. reflexivity.
    + apply IH. exact Hrest.
Qed.

(* Corollary (the landed `driver_flatten_agrees_with_add_flattened_bag`, transferred):
   the nu-free float agrees with the host's value-level flatten. *)
Corollary nu_free_float_agrees_with_add_flattened_bag : forall b,
  ffloat (embed b) = embed (bflatten b).
Proof.
  intro b. rewrite float_phase_conservative.
  rewrite driver_flatten_agrees_with_add_flattened_bag. reflexivity.
Qed.

(* Zero-admission confirmation. *)
Print Assumptions ffloat_canonical.
Print Assumptions ffloat_idempotent.
Print Assumptions drive_with_float_on_raw_eq_drive_on_canonical.
Print Assumptions raw_contractum_is_not_a_redex.
Print Assumptions nu_hidden_contractum_redex_fires.
Print Assumptions float_phase_conservative.
Print Assumptions nu_free_float_flatness.
Print Assumptions nu_free_float_agrees_with_add_flattened_bag.
