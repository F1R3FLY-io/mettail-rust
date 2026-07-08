(*
 * FoldMotionVsCongruence: the Stage 3f fold-vs-equation criterion (D3, INV-9) is
 * SOUND — the discriminator fires EXACTLY the barb-changing (directed-motion) rules
 * as COMMs and treats EXACTLY the barb-preserving (lossless-iso) rules as compile-time
 * congruence.
 *
 * D3 (knotted-topoi §5.2, INV-9): a rewrite fires as a COMM on the Rho interpreter iff
 * it is DIRECTED MOTION changing a CLTS barb; it compiles to compile-time structural
 * CONGRUENCE (no COMM) iff it is a SYMMETRIC IDENTITY or a LOSSLESS ISO COERCION.
 *
 * The Rust discriminator this models (`rholang-codegen/src/rho_net_lower.rs`):
 *
 *   - A COMPUTING native scalar fold `AddInt(a, b) ~> a + b` (`lower_native_fold`, a
 *     `fold` HOL term) is directed compute — it lowers to a flat FIRING DISPATCH
 *     RECEIVER (`NativeFold`) and fires as a COMM emitting the host-computed reduct.
 *
 *   - A LOSSLESS ISO COERCION `NormCast<Src>To<Tgt>In<Result>` `(Cast<Src> v) ~>
 *     (Cast<Tgt> (SrcToTgt v))` — uniquely marked by its `Premise::SyntheticInjGuard`
 *     (`is_lossless_cast_congruence`), which auto-injection attaches ONLY to `NormCast*`
 *     rules — is a value-preserving representation change. It lowers to
 *     `CongruenceClosure`: NO firing receiver, no COMM (the host normalizes it in its
 *     e-graph closure).
 *
 * The SEMANTIC justification (proved here from the barb definition, NOT assumed): a
 * scalar fold redex and its reduct present DIFFERENT barbs (an unreduced `AddInt(2,3)`
 * is observably not the value `5`), so the reduction is observable ⇒ it MUST be a COMM;
 * a lossless cast's two forms present the SAME barb (the representation tag is NOT
 * observable — that is precisely the losslessness), so identifying them is barb-safe ⇒
 * congruence, no COMM. The discriminator (`classify`, keyed on the inj-guard marker) is
 * then proved CONSISTENT with this barb behavior: it calls Congruence only
 * barb-preserving rules and fires only barb-changing rules.
 *
 * This is the Stage 3f companion to NativeSystemProcessBoundary.v (total-or-reject
 * dispatch + payload delegation for the firing side) and the trust boundary
 * RhoHostObligationBoundary.v; it discharges the ADDED D3 barb-boundary obligation.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions (Section
 * Variable/Hypothesis only, discharged when the section closes).
 *)

Section FoldMotionVsCongruence.

  (* ---------------------------------------------------------------------------
     Terms and their CLTS barbs.
     --------------------------------------------------------------------------- *)

  (* An observable CLTS barb. [BVal n] is the barb of a fully-reduced scalar VALUE
     [n]; [BFold op] is the barb of an UNREDUCED fold application headed by operator
     [op] (observably "still an application", not a value). Distinct constructors ⇒
     a value and an unreduced fold are observably different. *)
  Inductive Barb : Type :=
    | BVal  : nat -> Barb
    | BFold : nat -> Barb.

  (* A term. [Val n] a reduced scalar; [FoldRedex op a b] an unreduced native fold
     redex `Op(a, b)` (e.g. `AddInt(2, 3)`); [Cast rep v] a cast wrapper carrying the
     denoted VALUE [v] in REPRESENTATION [rep] (e.g. `Cast<Int>(3)` vs
     `Cast<BigRat>(3)` — same value [3], different [rep]). *)
  Inductive Term : Type :=
    | Val      : nat -> Term
    | FoldRedex : nat -> nat -> nat -> Term
    | Cast     : nat -> nat -> Term.

  (* The observable barb of a term. CRUCIAL (the lossless invariant): a [Cast rep v]
     is observable AS its denoted value [v] — the representation [rep] is NOT
     observable. So two cast forms of the SAME value are barb-equal regardless of
     representation, while a [FoldRedex] presents a [BFold]-barb distinct from any
     value barb. *)
  Definition barb (t : Term) : Barb :=
    match t with
    | Val n           => BVal n
    | FoldRedex op _ _ => BFold op
    | Cast _ v        => BVal v
    end.

  (* ---------------------------------------------------------------------------
     The two rewrite ACTIONS.
     --------------------------------------------------------------------------- *)

  (* The trusted native fold handler (`![…] fold` HOL body — model-b: the host
     computes the reduct). Abstract: the theory is parametric in the arithmetic
     (discharged when the section closes; no axiom). E.g. [compute AddInt 2 3 = 5]. *)
  Variable compute : nat -> nat -> nat -> nat.

  (* A native scalar fold reduces its redex to the host-computed VALUE
     (`lower_native_fold`: fires as a COMM emitting this reduct). *)
  Definition reduce_fold (op a b : nat) : Term := Val (compute op a b).

  (* A lossless cast canonicalization `(Cast<Src> v) ~> (Cast<Tgt> (SrcToTgt v))`
     changes the REPRESENTATION ([srcRep] → [tgtRep]) but PRESERVES the denoted value
     [v] — `SrcToTgt` is a value-preserving (lossless) injection. *)
  Definition normcast (srcRep tgtRep v : nat) : Term := Cast tgtRep v.

  (* ---------------------------------------------------------------------------
     The barb behavior — the SEMANTIC content of D3, proved from [barb].
     --------------------------------------------------------------------------- *)

  (* MOTION: a computing fold CHANGES the barb — the redex `Op(a,b)` presents a
     [BFold]-barb, its reduct presents a [BVal]-barb, and these are never equal. The
     reduction is OBSERVABLE, so per D3 it must fire as a COMM (directed motion
     changing a CLTS barb). *)
  Theorem fold_changes_barb : forall op a b,
    barb (FoldRedex op a b) <> barb (reduce_fold op a b).
  Proof.
    intros op a b. unfold reduce_fold. simpl. discriminate.
  Qed.

  (* CONGRUENCE: a lossless iso PRESERVES the barb — both cast forms are observable as
     the same denoted value [v] (the representation is not observable). Identifying
     them changes NO barb, so per D3/INV-9 it is compile-time congruence, NOT a COMM. *)
  Theorem iso_preserves_barb : forall srcRep tgtRep v,
    barb (Cast srcRep v) = barb (normcast srcRep tgtRep v).
  Proof.
    intros srcRep tgtRep v. unfold normcast. simpl. reflexivity.
  Qed.

  (* ---------------------------------------------------------------------------
     The DISCRIMINATOR — the Rust classifier, keyed on the inj-guard marker.
     --------------------------------------------------------------------------- *)

  (* A rewrite rule of the two D3-relevant families: a computing fold [FoldR op a b],
     or a lossless cast canonicalization [CastR srcRep tgtRep v]. *)
  Inductive Rule : Type :=
    | FoldR : nat -> nat -> nat -> Rule
    | CastR : nat -> nat -> nat -> Rule.

  (* The `Premise::SyntheticInjGuard` marker (`is_lossless_cast_congruence`): auto-
     injection attaches it EXCLUSIVELY to `NormCast*` (lossless cast) rules, so it is
     present iff the rule is a lossless cast. *)
  Definition has_inj_guard (r : Rule) : bool :=
    match r with
    | FoldR _ _ _ => false
    | CastR _ _ _ => true
    end.

  (* The lowering disposition: [Firing] installs a σ-receiver that fires as a COMM
     (`NativeFold` dispatch receiver); [Congruence] installs NO firing receiver
     (`CongruenceClosure` — compile-time e-graph closure). *)
  Inductive Disposition : Type := Firing | Congruence.

  (* The Rust discriminator (`lower_base_rewrite`: `if is_lossless_cast_congruence …
     CongruenceClosure` else fire; `lower_native_fold`: a `fold` fires): a rule with
     the inj-guard is congruence, else it fires. *)
  Definition classify (r : Rule) : Disposition :=
    if has_inj_guard r then Congruence else Firing.

  (* The redex (matched subject) and image (reduct) of a rule. *)
  Definition redex (r : Rule) : Term :=
    match r with
    | FoldR op a b       => FoldRedex op a b
    | CastR srcRep _ v   => Cast srcRep v
    end.
  Definition image (r : Rule) : Term :=
    match r with
    | FoldR op a b           => reduce_fold op a b
    | CastR srcRep tgtRep v  => normcast srcRep tgtRep v
    end.

  (* A rule is barb-CHANGING (directed motion — a COMM is warranted) / barb-PRESERVING
     (an identity — congruence is safe) per the CLTS observation of its redex vs image. *)
  Definition barb_changing (r : Rule) : Prop := barb (redex r) <> barb (image r).
  Definition barb_preserving (r : Rule) : Prop := barb (redex r) = barb (image r).

  (* ---------------------------------------------------------------------------
     SOUNDNESS of the discriminator w.r.t. the barb behavior.
     --------------------------------------------------------------------------- *)

  (* The discriminator treats as CONGRUENCE only barb-PRESERVING rules: omitting the
     COMM for a rule [classify] calls [Congruence] changes NO observable barb, so it is
     SOUND to compile it to compile-time congruence (INV-9). *)
  Theorem classify_congruence_is_barb_preserving : forall r,
    classify r = Congruence -> barb_preserving r.
  Proof.
    intros r H. destruct r as [op a b | srcRep tgtRep v].
    - (* FoldR: classify = Firing, contradicting = Congruence. *)
      unfold classify in H. simpl in H. discriminate H.
    - (* CastR: barb-preserving by iso_preserves_barb. *)
      unfold barb_preserving, redex, image. apply iso_preserves_barb.
  Qed.

  (* The discriminator FIRES (as a COMM) only barb-CHANGING rules: a rule [classify]
     calls [Firing] changes an observable barb, so the COMM is WARRANTED (directed
     motion) — the encoder never fires a barb-preserving identity. *)
  Theorem classify_firing_is_barb_changing : forall r,
    classify r = Firing -> barb_changing r.
  Proof.
    intros r H. destruct r as [op a b | srcRep tgtRep v].
    - (* FoldR: barb-changing by fold_changes_barb. *)
      unfold barb_changing, redex, image. apply fold_changes_barb.
    - (* CastR: classify = Congruence, contradicting = Firing. *)
      unfold classify in H. simpl in H. discriminate H.
  Qed.

  (* ---------------------------------------------------------------------------
     The D3 DICHOTOMY — exhaustive, consistent, and MOTION iff COMM.
     --------------------------------------------------------------------------- *)

  (* Every D3-relevant rule falls in EXACTLY one side, and its disposition MATCHES its
     barb behavior: a computing fold is [Firing] AND barb-changing (a COMM); a lossless
     iso is [Congruence] AND barb-preserving (no COMM). This is the fold-vs-equation
     criterion: fires-as-COMM ⟺ directed motion changing a CLTS barb. *)
  Theorem d3_dichotomy : forall r,
    (classify r = Firing /\ barb_changing r)
    \/ (classify r = Congruence /\ barb_preserving r).
  Proof.
    intro r. destruct r as [op a b | srcRep tgtRep v].
    - left. split.
      + reflexivity.
      + unfold barb_changing, redex, image. apply fold_changes_barb.
    - right. split.
      + reflexivity.
      + unfold barb_preserving, redex, image. apply iso_preserves_barb.
  Qed.

  (* MOTION ⟺ COMM (the criterion, as a biconditional): a rule fires as a COMM (is
     classified [Firing]) IFF it is directed motion (barb-changing). Both directions
     from the soundness theorems + the dichotomy. *)
  Theorem fires_iff_barb_changing : forall r,
    classify r = Firing <-> barb_changing r.
  Proof.
    intro r. split.
    - apply classify_firing_is_barb_changing.
    - intro Hchange. destruct (d3_dichotomy r) as [[Hf _] | [_ Hpres]].
      + exact Hf.
      + (* Congruence ⇒ barb_preserving contradicts barb_changing. *)
        exfalso. apply Hchange. exact Hpres.
  Qed.

  (* And the inj-guard marker (the `SyntheticInjGuard`) is EXACTLY the congruence
     side: a rule is congruence iff it carries the guard — the Rust
     `is_lossless_cast_congruence` discriminator is faithful to D3. *)
  Theorem inj_guard_iff_congruence : forall r,
    has_inj_guard r = true <-> classify r = Congruence.
  Proof.
    intro r. unfold classify. destruct (has_inj_guard r); simpl; split; intro H.
    - reflexivity.
    - reflexivity.
    - discriminate H.
    - discriminate H.
  Qed.

End FoldMotionVsCongruence.

Print Assumptions fold_changes_barb.
Print Assumptions iso_preserves_barb.
Print Assumptions classify_congruence_is_barb_preserving.
Print Assumptions classify_firing_is_barb_changing.
Print Assumptions d3_dichotomy.
Print Assumptions fires_iff_barb_changing.
Print Assumptions inj_guard_iff_congruence.
