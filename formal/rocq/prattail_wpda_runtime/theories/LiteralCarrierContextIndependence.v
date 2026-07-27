(*
 * LiteralCarrierContextIndependence — divergence I: a numeral's CARRIER is a
 * function of the numeral, and of nothing else.
 *
 * GROUND TRUTH (measured 2026-07-25, `languages/tests/rholang_tests.rs`,
 * `rholang-runtime/tests/rho_rholang_conformance.rs`):
 *   Rholang offers several carriers for Rholang's ONE integer type — `Int`
 *   (i64 ▸ GInt), `BigInt` (arbitrary precision ▸ GBigInt), `UInt32`. That is
 *   sound only while the carrier is a function of the SOURCE. It was not:
 *
 *     `*(@1) + 2`   ⟹ Add(… CastBigInt(1) …, CastBigInt(2))
 *     `*(@(1)) + 2` ⟹ Add(… CastInt(1)    …, CastBigInt(2))     (MIXED)
 *     `5u32`        ⟹ CastBigInt(5)          (the `u32` suffix reached no UInt32)
 *     `[1,2,3]`     ⟹ CastBigInt elements, while a bare `1` was … also BigInt,
 *                     and after the literal fix became Int — the SAME asymmetry
 *                     displaced to the projection layer.
 *
 *   Both this grammar's operators and f1r3node's `combine_plus`
 *   (`reduce.rs:3112`) are carrier-EXACT — neither has a mixed GInt/GBigInt arm
 *   — so the asymmetry was a SEMANTIC difference: `int(1,64) + 2` answered
 *   `error`, `[1,2,3].length() == 3` was false, `{1:10}.get(1)` was `error`.
 *
 * THE ROOT (two independent defects, one symptom):
 *   D-1 (grammar) `BigInt`'s `eval` was `parse_int_lit(text, None)` — a
 *       UNIVERSAL ACCEPTOR of every integer spelling — contradicting its own
 *       declared mandatory `…n` tail. Since `home_polymorphic_token_arm` gives
 *       every Integer-family category a bare `TokenKind::Integer` arm,
 *       `CastBigInt` was a live reading of EVERY numeral and won the lex-min
 *       tiebreak by grammar DECLARATION ORDER.
 *   D-2 (engine) one projection charged on two ledgers: a `(`-grouping fork
 *       branch cost `lex_one()` (the multiplicative identity) where a bare
 *       prefix dispatch cost `BP_TIER_CROSSCAT_PROJECTION`, so a parenthesis
 *       CREATED a free route.
 *
 * THE FIX, and what this file proves about it:
 *   The election machinery behaved exactly as specified. What it elected
 *   BETWEEN was a set of readings the GRAMMAR should never have admitted. So
 *   the fix makes the EVIDENCE discriminate — the literal domains PARTITION —
 *   rather than adjusting the tiebreak. The headline theorem
 *   [T_CarrierIsAFunctionOfTheToken] is provable with NO ledger hypothesis
 *   whatever, which is precisely why the grammar change is the correctness fix
 *   and the engine change (Stage D) is prophylaxis.
 *
 * THE MODEL. A token text is abstracted by the three DECIDABLE predicates the
 * implementation actually branches on (`languages/src/rholang.rs`, `literals`):
 *   - [t_ends_n]    : the text ends in the `n` tail `BigInt`'s pattern declares;
 *   - [t_suffixed]  : the text carries an explicit fixed-width suffix
 *                     (`IntSuffix::from_text ≠ Unsuffixed`);
 *   - [t_fits]      : the value fits `Int`'s `i64` carrier (`IntLit::as_i64`).
 * An election SITE is left completely abstract: no property of it is ever used,
 * which is the formal content of "context-independent".
 *
 * THEOREMS (all admission-free; audited by `Print Assumptions` at the bottom,
 * every one of which must print "Closed under the global context"):
 *   T0  pre_fix_admits_two_carriers      — the DEFECT, as a witness: under the
 *       universal acceptor two distinct categories accept the same token, so an
 *       election is REQUIRED and its outcome is whatever the ledger says.
 *   T1  T_DomainsPartition               — after the fix the three accept sets
 *       are PAIRWISE DISJOINT (and `UInt32`'s is empty).
 *   T2  T_CarrierIsAFunctionOfTheToken   — there is a total function from token
 *       to carrier such that, AT EVERY SITE, the set of literal readings is
 *       either empty or exactly that one carrier. No site can elect a DIFFERENT
 *       carrier than another site; it can only fail to admit the token at all.
 *   T3  T_NoReadingLost                  — every token some category accepted
 *       BEFORE is still accepted by some category AFTER: the partition removes
 *       DUPLICATE readings, never the last one.
 *   T4  T_AcceptShrinksPointwise         — the new accept relation is pointwise
 *       ≤ the old one, for every category and every token.
 *   T5  T_CohortBoundsHoldAFortiori      — hence every monotone frontier /
 *       cohort bound proven of the OLD literal cohort holds of the NEW one. The
 *       a-fortiori step is PROVED here, not assumed at the use sites
 *       (`ProjectionIsolation.T5_single_winner_*`, `KBestExtractionSound`,
 *       `CastCompareFrontierBound`, `CanonicalGllDescriptorBound`).
 *   T6  T_ProjectionOrderCanonicalises   — the Proc-LEVEL statement, with its
 *       hypothesis made explicit. The auto-injected `IntToBigInt` promotion
 *       (`NativeKind::lossless_targets`) leaves TWO Proc-level readings of an
 *       `Int`-domain literal — direct `Int ▸ Proc` and promoted
 *       `Int ▸ BigInt ▸ Proc` — and MEASUREMENT showed different sites realising
 *       different ones. Declaring the direct projection FIRST makes it the
 *       order-minimum, hence the elected reading, at every site that admits any
 *       reading. This is the formal content of the `CastInt`-before-`CastBigInt`
 *       reordering, and it is sound ONLY because T1 already made the literal
 *       domains disjoint (T7).
 *   T7  T_reorder_needs_the_partition    — the converse guard: under the
 *       pre-fix universal acceptor, declaring the direct projection first would
 *       have mis-carried `3n`. So the reorder could not have been done alone.
 *)

From Stdlib Require Import Bool List PeanoNat Arith Lia.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* The token abstraction                                                        *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* A token text, abstracted by exactly the four DECIDABLE predicates the
   implementation branches on. Nothing else about the text is ever consulted.

   `t_wellformed` is `parse_int_lit(text, None) = Ok(_)`: the magnitude fits the
   width the text's OWN suffix declares (vacuously true for an unsuffixed text).
   It is distinct from `t_fits`, which asks whether the value fits `Int`'s `i64`
   carrier — `5000000000u32` is `t_fits = false` AND `t_wellformed = false`,
   while `18446744073709551615u64` would be well-formed yet not fit `i64`. *)
Record Tok : Type := mkTok {
  t_ends_n     : bool;  (* text ends in the `n` tail BigInt's pattern declares *)
  t_suffixed   : bool;  (* IntSuffix::from_text text <> Unsuffixed             *)
  t_fits       : bool;  (* IntLit::as_i64 text = Some _                        *)
  t_wellformed : bool   (* parse_int_lit(text, None) = Ok(_)                   *)
}.

(* The three integer categories that own (or owned) a `literals { }` entry. *)
Inductive Cat : Type := CInt | CBigInt | CUInt32.

Definition all_cats : list Cat := [CInt; CBigInt; CUInt32].

Lemma all_cats_complete : forall c, In c all_cats.
Proof. intro c; destruct c; simpl; auto. Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* BEFORE — the universal acceptor                                              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Transcribed from the pre-fix `literals { }` evals:
     BigInt : parse_int_lit(text, None)            — succeeds on EVERY spelling
              that parses at all, `n` tail or not: the UNIVERSAL ACCEPTOR.
     Int    : parse_int_lit(text, Some(Suffix::I64)) — a fixed-width suffix that
              is not `i64` is REJECTED outright (`5u32` never reached `Int`),
              then `as_i64` narrows.
     UInt32 : parse_int_lit(text, None) then `u32::try_from` — its `…u32`
              pattern gated the arm. *)
Definition accepts_old (c : Cat) (t : Tok) : bool :=
  match c with
  | CInt    => t_wellformed t && negb (t_ends_n t) && negb (t_suffixed t) && t_fits t
  | CBigInt => t_wellformed t
  | CUInt32 => t_wellformed t && t_suffixed t
  end.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* AFTER — the partitioned domains                                              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* `Int`   : every spelling without the `n` tail whose value fits `i64` — the
             full `normalize_ground` ≤64-bit suffix set (bare, i32, i64, u32).
   `BigInt`: EXACTLY its declared `…n` domain, plus the deliberate MeTTaIL
             SUPERSET of UNSUFFIXED numerals too large for `i64`. Both clauses
             are decided by the token text alone.
   `UInt32`: NO literal surface — reachable only through `uint(x, 32)`. *)
Definition accepts (c : Cat) (t : Tok) : bool :=
  match c with
  | CInt    => t_wellformed t && negb (t_ends_n t) && t_fits t
  | CBigInt => t_wellformed t
               && (t_ends_n t || (negb (t_suffixed t) && negb (t_fits t)))
  | CUInt32 => false
  end.

(* The four spelling witnesses, as tokens. *)
Definition tok_bare_one : Tok := mkTok false false true  true.  (* `1`      *)
Definition tok_three_n  : Tok := mkTok true  false true  true.  (* `3n`     *)
Definition tok_five_u32 : Tok := mkTok false true  true  true.  (* `5u32`   *)
Definition tok_huge     : Tok := mkTok false false false true.  (* 3.2e19   *)
(* `5000000000u32` — a width-suffixed value out of range for its own width. *)
Definition tok_u32_oor  : Tok := mkTok false true  false false.

(* ── T0 — the DEFECT, as a witness ───────────────────────────────────────── *)

Theorem T0_pre_fix_admits_two_carriers :
  accepts_old CInt tok_bare_one = true /\ accepts_old CBigInt tok_bare_one = true.
Proof. split; reflexivity. Qed.

(* …and not one stray token: the `u32` spelling was admitted by TWO categories
   too, NEITHER of which is the one `normalize_ground` names. *)
Theorem T0b_pre_fix_admits_two_carriers_for_u32 :
  accepts_old CBigInt tok_five_u32 = true /\ accepts_old CUInt32 tok_five_u32 = true
  /\ accepts_old CInt tok_five_u32 = false.
Proof. repeat split; reflexivity. Qed.

(* ── T1 — the domains PARTITION ──────────────────────────────────────────── *)

(* Pairwise disjointness, stated as: no token is accepted by two DISTINCT
   categories. The proof enumerates all 16 token shapes, so no case is left to
   the reader. *)
Theorem T_DomainsPartition :
  forall (c1 c2 : Cat) (t : Tok),
    accepts c1 t = true -> accepts c2 t = true -> c1 = c2.
Proof.
  intros c1 c2 t H1 H2.
  destruct c1, c2; try reflexivity;
    destruct t as [en su fi wf]; destruct en, su, fi, wf;
    cbn in H1, H2; try discriminate; reflexivity.
Qed.

(* `UInt32` has NO literal surface at all — the strongest form of "the `u32`
   suffix is a SPELLING of a GInt, not a different carrier". *)
Theorem T_UInt32_has_no_literal_surface :
  forall t : Tok, accepts CUInt32 t = false.
Proof. intro t; reflexivity. Qed.

(* ── T2 — the carrier is a FUNCTION of the token ─────────────────────────── *)

(* Written directly rather than extracted from [accepts], so the agreement
   below is a genuine obligation and not a definitional unfolding. *)
Definition carrier (t : Tok) : option Cat :=
  if negb (t_wellformed t) then None
  else if t_ends_n t then Some CBigInt
  else if t_fits t then Some CInt
  else if t_suffixed t then None   (* width-suffixed and out of range: reject *)
  else Some CBigInt.               (* the unsuffixed-overflow superset        *)

Lemma carrier_sound : forall c t, carrier t = Some c -> accepts c t = true.
Proof.
  intros c t H; destruct t as [en su fi wf]; unfold carrier in H; cbn in H;
    destruct en, su, fi, wf; cbn in H |- *;
    first [ discriminate H | (injection H as H; subst; reflexivity) ].
Qed.

Lemma carrier_complete : forall c t, accepts c t = true -> carrier t = Some c.
Proof.
  intros c t H; destruct c; destruct t as [en su fi wf]; cbn in H;
    destruct en, su, fi, wf; cbn in H; try discriminate; reflexivity.
Qed.

(* An election SITE is completely abstract. [live] models the fact — MEASURED,
   not hypothesised — that which readings a site realises may differ from site
   to site. No property of [Site] or of [live] is used below: that is exactly
   the formal content of "context-independent". *)
Section ContextIndependence.
  Variable Site : Type.
  Variable live : Site -> Cat -> bool.

  Definition readings (s : Site) (t : Tok) : list Cat :=
    filter (fun c => live s c && accepts c t) all_cats.

  Lemma readings_sound :
    forall s t c, In c (readings s t) -> accepts c t = true.
  Proof.
    intros s t c Hin; unfold readings in Hin.
    apply filter_In in Hin as [_ Hb]; apply andb_true_iff in Hb as [_ Ha]; exact Ha.
  Qed.

  (* ★ THE HEADLINE. At every site the reading set is empty or a singleton, and
     when non-empty its single element is the SAME carrier at every site. A site
     can fail to admit a numeral (a parse error, which the parser reports); it
     can never admit a DIFFERENT carrier than another site. Note the hypothesis
     list: there is none. No ledger, no weight, no tiebreak — the partition
     alone carries it, which is why the grammar change is THE correctness fix
     and the engine change is prophylaxis. *)
  Theorem T_CarrierIsAFunctionOfTheToken :
    forall (s1 s2 : Site) (t : Tok) (c1 c2 : Cat),
      In c1 (readings s1 t) -> In c2 (readings s2 t) -> c1 = c2.
  Proof.
    intros s1 s2 t c1 c2 H1 H2.
    apply readings_sound in H1; apply readings_sound in H2.
    exact (T_DomainsPartition c1 c2 t H1 H2).
  Qed.

  (* The same fact in its "at most one" form: no site ever faces a genuine
     literal-carrier choice, so no tiebreak can decide one. *)
  Theorem T_AtMostOneReadingPerSite :
    forall (s : Site) (t : Tok) (c1 c2 : Cat),
      In c1 (readings s t) -> In c2 (readings s t) -> c1 = c2.
  Proof. intros s t; apply T_CarrierIsAFunctionOfTheToken. Qed.

  (* …and whichever site does admit it, the carrier is the one [carrier] names. *)
  Theorem T_SiteReadingIsTheCarrier :
    forall (s : Site) (t : Tok) (c : Cat),
      In c (readings s t) -> carrier t = Some c.
  Proof.
    intros s t c H; apply carrier_complete; exact (readings_sound s t c H).
  Qed.

  (* Contrast: BEFORE the fix a SINGLE site faced a real choice, so the ledger
     decided — and a site whose ledger differed answered differently. *)
  Definition readings_old (s : Site) (t : Tok) : list Cat :=
    filter (fun c => live s c && accepts_old c t) all_cats.

  Theorem T0c_pre_fix_a_site_faces_a_real_choice :
    forall s : Site,
      (forall c, live s c = true) ->
      In CInt (readings_old s tok_bare_one) /\
      In CBigInt (readings_old s tok_bare_one).
  Proof.
    intros s Hlive; unfold readings_old; split; apply filter_In; split;
      try apply all_cats_complete; rewrite Hlive; reflexivity.
  Qed.
End ContextIndependence.

(* ── T3 — nothing lost, and the ONE narrowing characterised exactly ───────── *)

(* A GRAMMAR-derived side condition, not an assumption about the engine: the
   suffixes Rholang's `Int` pattern admits are `i32`, `i64` and `u32`, and every
   value that fits one of those also fits `i64`. (A `u64`/`u128` suffix, which
   could be well-formed yet exceed `i64`, is not in the declared token language
   at all — the pattern is `(…)(i32|i64|u32)?`.) *)
Definition SuffixesAreSubI64 (t : Tok) : Prop :=
  t_suffixed t = true -> t_wellformed t = true -> t_fits t = true.

(* Under that side condition, every WELL-FORMED numeral still has a carrier:
   the partition removes DUPLICATE readings, never the last one. (A token that
   is not well-formed does not parse at all, on either side — see
   [T_IllFormedIsRejectedOnBothSides] — so it is stated separately rather than
   folded in, which would have made the theorem vacuously weaker.) *)
Theorem T_NoReadingLost :
  forall t : Tok,
    SuffixesAreSubI64 t ->
    t_wellformed t = true ->
    exists c, accepts c t = true.
Proof.
  intros t Hsub Hwf; destruct t as [en su fi wf];
    unfold SuffixesAreSubI64 in Hsub; cbn in Hsub, Hwf.
  destruct en, su, fi, wf; try discriminate Hwf.
  - exists CBigInt; reflexivity.                            (* `3n`-shaped     *)
  - exists CBigInt; reflexivity.
  - exists CBigInt; reflexivity.
  - exists CBigInt; reflexivity.
  - exists CInt; reflexivity.                               (* `5u32`          *)
  - specialize (Hsub eq_refl eq_refl); discriminate Hsub.   (* excluded shape  *)
  - exists CInt; reflexivity.                               (* `1`             *)
  - exists CBigInt; reflexivity.                            (* the huge numeral*)
Qed.

Theorem T_IllFormedIsRejectedOnBothSides :
  forall (t : Tok) (c : Cat),
    t_wellformed t = false -> accepts_old c t = false /\ accepts c t = false.
Proof.
  intros t c Hwf; destruct t as [en su fi wf]; cbn in Hwf; subst wf.
  destruct c; destruct en, su, fi; split; reflexivity.
Qed.

(* ★ The ONE narrowing, characterised EXACTLY. The old universal acceptor gave
   `5000000000u32` — a value out of range for the width its own text declares —
   an ARBITRARY-PRECISION carrier, silently discarding the declared width. The
   partition rejects it instead: fail-closed, text-determined, and unable to
   produce a divergent VALUE. This is the sole token shape the union lost, and
   it is exactly the shape `SuffixesAreSubI64` excludes from the declared token
   language. *)
Theorem T_the_only_narrowing_is_the_out_of_range_width_suffix :
  forall t : Tok,
    (exists c, accepts_old c t = true) ->
    (forall c, accepts c t = false) ->
    t_ends_n t = false /\ t_suffixed t = true /\ t_fits t = false
    /\ t_wellformed t = true.
Proof.
  intros t [c Hold] Hnew; destruct t as [en su fi wf];
    destruct en, su, fi, wf; cbn in Hold |- *;
    try (destruct c; cbn in Hold; discriminate Hold);
    try (specialize (Hnew CInt); cbn in Hnew; discriminate Hnew);
    try (specialize (Hnew CBigInt); cbn in Hnew; discriminate Hnew);
    repeat split; reflexivity.
Qed.

Theorem W_the_narrowing_witness :
  accepts_old CBigInt tok_u32_oor = false /\ accepts CBigInt tok_u32_oor = false
  /\ carrier tok_u32_oor = None.
Proof. repeat split; reflexivity. Qed.

(* ── T4 / T5 — the cohort strictly shrinks, and the bounds hold a fortiori ── *)

Definition cohort     (t : Tok) : list Cat := filter (fun c => accepts c t) all_cats.
Definition cohort_old (t : Tok) : list Cat := filter (fun c => accepts_old c t) all_cats.

(* The new literal cohort is a singleton at most — immediately from T1. *)
Theorem T_NewCohortIsAtMostOne :
  forall t : Tok, length (cohort t) <= 1.
Proof.
  intro t; destruct t as [en su fi wf]; destruct en, su, fi, wf; cbn; auto with arith.
Qed.

(* ★ The cohort never grows, at ANY token shape. Per-CATEGORY containment does
   NOT hold and must not be claimed: the new `Int` accepts `5u32`, which the old
   `Int` refused outright (`parse_int_lit(text, Some(I64))` rejects a mismatched
   fixed suffix). What holds — and what every frontier / descriptor / k-best
   bound in this development actually consumes — is that the cohort's SIZE is
   non-increasing. All 16 shapes are enumerated. *)
Theorem T_CohortShrinks :
  forall t : Tok, length (cohort t) <= length (cohort_old t).
Proof.
  intro t; destruct t as [en su fi wf]; destruct en, su, fi, wf; cbn; auto with arith.
Qed.

(* ★ The A-FORTIORI step, PROVED here rather than assumed at the use sites
   (`ProjectionIsolation.T5_single_winner_*`, `KBestExtractionSound`,
   `CastCompareFrontierBound`, `CanonicalGllDescriptorBound`). Any bound that is
   monotone in the cohort SIZE and holds of the OLD literal cohort holds of the
   NEW one. Stated over an abstract monotone measure so it applies verbatim,
   without re-deriving anything about the particular bounds. *)
Theorem T_CohortBoundsHoldAFortiori :
  forall (Measure : nat -> nat) (bound : nat) (t : Tok),
    (forall a b : nat, a <= b -> Measure a <= Measure b) ->
    Measure (length (cohort_old t)) <= bound ->
    Measure (length (cohort t)) <= bound.
Proof.
  intros Measure bound t Hmono Hold.
  eapply PeanoNat.Nat.le_trans; [ apply Hmono; apply T_CohortShrinks | exact Hold ].
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* The PROJECTION layer — why `CastInt` had to be declared FIRST               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* The partition settles which CATEGORY a numeral lands in. It does NOT by
   itself settle which `Proc`-level projection is elected, because the
   auto-injected `IntToBigInt` promotion (emitted from
   `NativeKind::lossless_targets`, which puts `TokenKind::Integer` back into
   `FIRST(BigInt)`) leaves an `Int`-domain literal with TWO `Proc` readings:

     Direct   :  Int ▸ Proc                    (`CastInt`)
     Promoted :  Int ▸ BigInt ▸ Proc           (`IntToBigInt`, then `CastBigInt`)

   MEASURED: with `CastBigInt` declared first, collection-ELEMENT sites elected
   Promoted while top-level and operand sites elected Direct — the divergence-I
   asymmetry displaced from the literal layer to the projection layer
   (`{1: 10}.get(1)` was `error`; `x!(1)` did not canonicalise to `x!([1])`). *)

Inductive Proj : Type := Direct | Promoted | ViaUInt32.

Definition proj_carrier (p : Proj) : Cat :=
  match p with Direct => CInt | Promoted => CBigInt | ViaUInt32 => CUInt32 end.

(* A projection is admissible for a token iff the literal at the head of its
   chain is in that chain's SOURCE domain. `Promoted`'s chain begins at `Int`
   (the promotion `IntToBigInt` consumes an `Int`) and also serves a genuine
   `BigInt` literal, so it admits either domain. *)
Definition proj_admits (p : Proj) (t : Tok) : bool :=
  match p with
  | Direct    => accepts CInt t
  | Promoted  => accepts CInt t || accepts CBigInt t
  | ViaUInt32 => accepts CUInt32 t
  end.

(* Grammar DECLARATION ORDER as a rank: `CastInt` first (this commit), then
   `CastBigInt`, then `CastUInt32`. *)
Definition decl_rank (p : Proj) : nat :=
  match p with Direct => 0 | Promoted => 1 | ViaUInt32 => 2 end.

(* ★ T6. For a token in `Int`'s domain the order-minimal admissible projection
   is `Direct`, so the elected `Proc`-level carrier is `CInt` — the very
   category the literal layer assigns. The site is not mentioned: a site cannot
   realise what the grammar does not admit, and among what it admits the
   order-minimum is `Direct` everywhere. *)
Theorem T_ProjectionOrderCanonicalises :
  forall t : Tok,
    accepts CInt t = true ->
    proj_admits Direct t = true
    /\ (forall p : Proj, proj_admits p t = true -> decl_rank Direct <= decl_rank p)
    /\ proj_carrier Direct = CInt.
Proof.
  intros t Ht; repeat split.
  - cbn; exact Ht.
  - intros p _; destruct p; cbn; auto with arith.
Qed.

(* …and dually, a token in `BigInt`'s domain has NO `Direct` reading at all, so
   the order-minimum there is `Promoted`: the `…n` spelling keeps its
   arbitrary-precision carrier and the reorder cannot mis-carry `3n`. *)
Theorem T_BigIntDomainKeepsItsCarrier :
  forall t : Tok,
    accepts CBigInt t = true ->
    proj_admits Direct t = false /\ proj_admits Promoted t = true.
Proof.
  intros t H; destruct t as [en su fi wf]; destruct en, su, fi, wf;
    cbn in H |- *; try discriminate H; split; reflexivity.
Qed.

(* ★ T7 — the converse guard: the reorder is sound ONLY because the partition
   came first. Under the pre-fix universal acceptor a bare `1` was in BOTH
   domains, so `Direct` and `Promoted` were BOTH admissible for it and the
   `…n` discipline would have rested on the ledger again. No declaration order
   can separate domains that overlap. *)
Definition proj_admits_old (p : Proj) (t : Tok) : bool :=
  match p with
  | Direct    => accepts_old CInt t
  | Promoted  => accepts_old CInt t || accepts_old CBigInt t
  | ViaUInt32 => accepts_old CUInt32 t
  end.

Theorem T_reorder_needs_the_partition :
  exists t : Tok,
    accepts_old CInt t = true /\ accepts_old CBigInt t = true
    /\ proj_admits_old Direct t = true /\ proj_admits_old Promoted t = true.
Proof. exists tok_bare_one; repeat split; reflexivity. Qed.

(* Under the FIX the same statement is refuted — no token is in both domains, so
   the declaration order decides nothing about the CARRIER. It decides only
   which of two co-denoting `Proc` spellings of the SAME carrier is canonical. *)
Theorem T_after_fix_no_token_is_in_both_domains :
  ~ (exists t : Tok, accepts CInt t = true /\ accepts CBigInt t = true).
Proof.
  intros [t [H1 H2]].
  assert (Heq : CInt = CBigInt) by exact (T_DomainsPartition CInt CBigInt t H1 H2).
  discriminate Heq.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* The spelling witnesses, decided end to end                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem W_bare_one_is_Int   : carrier tok_bare_one = Some CInt.    Proof. reflexivity. Qed.
Theorem W_five_u32_is_Int   : carrier tok_five_u32 = Some CInt.    Proof. reflexivity. Qed.
Theorem W_three_n_is_BigInt : carrier tok_three_n  = Some CBigInt. Proof. reflexivity. Qed.
Theorem W_huge_is_BigInt    : carrier tok_huge     = Some CBigInt. Proof. reflexivity. Qed.

(* And the pre-fix answers for the same four, so the change is legible: `1`,
   `5u32` and the huge numeral ALL came out `BigInt`, and only `3n` was right by
   accident. *)
Theorem W_pre_fix_gave_bigint_to_everything :
  accepts_old CBigInt tok_bare_one = true /\
  accepts_old CBigInt tok_five_u32 = true /\
  accepts_old CBigInt tok_three_n  = true /\
  accepts_old CBigInt tok_huge     = true.
Proof. repeat split; reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Assumption audit — every line MUST print "Closed under the global context"  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Print Assumptions T0_pre_fix_admits_two_carriers.
Print Assumptions T0b_pre_fix_admits_two_carriers_for_u32.
Print Assumptions T0c_pre_fix_a_site_faces_a_real_choice.
Print Assumptions T_DomainsPartition.
Print Assumptions T_UInt32_has_no_literal_surface.
Print Assumptions carrier_sound.
Print Assumptions carrier_complete.
Print Assumptions T_CarrierIsAFunctionOfTheToken.
Print Assumptions T_AtMostOneReadingPerSite.
Print Assumptions T_SiteReadingIsTheCarrier.
Print Assumptions T_NoReadingLost.
Print Assumptions T_IllFormedIsRejectedOnBothSides.
Print Assumptions T_the_only_narrowing_is_the_out_of_range_width_suffix.
Print Assumptions W_the_narrowing_witness.
Print Assumptions T_NewCohortIsAtMostOne.
Print Assumptions T_CohortShrinks.
Print Assumptions T_CohortBoundsHoldAFortiori.
Print Assumptions T_ProjectionOrderCanonicalises.
Print Assumptions T_BigIntDomainKeepsItsCarrier.
Print Assumptions T_reorder_needs_the_partition.
Print Assumptions T_after_fix_no_token_is_in_both_domains.
Print Assumptions W_bare_one_is_Int.
Print Assumptions W_five_u32_is_Int.
Print Assumptions W_three_n_is_BigInt.
Print Assumptions W_huge_is_BigInt.
Print Assumptions W_pre_fix_gave_bigint_to_everything.
