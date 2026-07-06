(*
 * KeywordReservation: the spec for the SHIPPED grammar-derived KEYWORD
 * RESERVATION mechanism — default-reserve + per-language/per-terminal opt-out,
 * plus the nullary-keyword lex-fork seed and the @Nil-send canonicalization
 * (commits 6ebdeb04 / cc6503c6, 2026-07-06, feature/wfst-architecture).
 *
 * THE MECHANISM (lexer-local, grammar-derived):
 *   An identifier-shaped literal terminal declared in the grammar (`Nil`, `Set`,
 *   `error`, `true`, or Fortran's `DO`/`IF`) is a RESERVED keyword by DEFAULT —
 *   a declared literal IS the keyword evidence. Reservation drops the generic
 *   `Ident` co-accept at the keyword's exact-match DFA state (`resolve_accept`,
 *   subset.rs): keywords carry strictly-higher priority than `Ident`, so the
 *   primary winner is unchanged; ONLY the over-generated `Ident` reading (a
 *   declared keyword is not a variable) is removed — a strict refinement, never
 *   a genuine ambiguity (consistent with never-disambiguate-early). The reserved
 *   set is DERIVED from the grammar (identifier-shaped terminals), so it is
 *   general over every language with NO per-language hardcode. A per-language /
 *   per-terminal OPT-OUT (`reserved_keywords: none`, or the contextual escalation
 *   of ident-shaped collection openers like `Set`) preserves FULL ambiguity for
 *   contextual-keyword languages (Fortran: `DO`/`IF` are valid identifiers — the
 *   `DO 10 I=1.5` [assignment] vs `DO 10 I=1,5` [loop] archetype). The parser is
 *   UNTOUCHED — reservation is confined to the lexer accept-set resolution. Env
 *   kill-switch `PRATTAIL_NO_KW_RESERVE`; byte-identical when the reserved set is
 *   empty.
 *
 * TWO PARSER ENABLEMENTS that make `auto` reservation sound + green (cc6503c6):
 *   FIX-FORK (a6683ee9, kind_dispatch.rs): the codegen historically skipped
 *     TerminalKeyword rules in the lex-fork ("keywords are exact byte matches,
 *     never multi-alt") — which reservation INVALIDATES (dropping the `Ident`
 *     co-accept at the keyword's maximal DFA state leaves a spurious
 *     truncated-`Ident` prefix edge). A reserved NULLARY keyword must SEED its
 *     cursor from its OWN `Fixed(kw)` accept, not the (now-removed) `Ident`
 *     co-accept. Gated `NULLARY_KEYWORD_LEXFORK_SEED` (default on); provably
 *     INERT without reservation (the `Ident` co-accept still seeds it).
 *   @Nil-SEND CANON (aa78d51b, rhocalc/runtime.rs): with `Nil` reserved,
 *     `@Nil!(q)` matches BOTH the specialized `POutputNil(q)` and the general
 *     `POutputShort(PZero, q)` — the IDENTICAL term (send `q` on the
 *     null-process channel `NQuote(PZero)`). `normalize_send_sugar_canon`
 *     canonicalizes every `@`-send sugar variant to its channel-first fold target
 *     and recurses into every Proc subterm, so `term_eq` unifies them POST-PARSE.
 *     `parse_via_wpda_all` still returns EVERY reading (never-disambiguate-early
 *     preserved). Gated `PRATTAIL_NO_SEND_SUGAR_CANON`. Idempotent.
 *
 * THE MODEL: a lexer accept STATE carries an alt-set of TokenKinds. A keyword's
 * exact-match state carries {Fixed(kw), Ident} (both accept — the keyword, at
 * higher priority, first). `resolve_accept reserved` drops `Ident` iff the
 * primary is a reserved keyword.
 *
 * THEOREMS (all admission-free; audited by `Print Assumptions`, every one must
 * print "Closed under the global context"):
 *   T1  reserved_set_grammar_derived  — the reserved set = EXACTLY the
 *       identifier-shaped literal terminals of the grammar (In-characterization).
 *   T2  default_reserves              — under `auto`, every ident-shaped terminal
 *       IS reserved (default = reserve).
 *   T3  reserving_removes_ident_co_accept — at the keyword's exact-match state,
 *       {Fixed(kw), Ident} ↦ {Fixed(kw)} (drop `Ident`); a STRICT REFINEMENT
 *       (subset), keeping the keyword, removing only the over-generation.
 *   T4  no_legit_var_lost             — a non-keyword `Ident` state keeps `Ident`;
 *       a NON-reserved keyword state keeps BOTH accepts.
 * ★ T5  contextual_optout_preserves_ambiguity — a contextual opt-out keeps a
 *       would-be-reserved keyword UN-reserved ⇒ both accepts survive (Fortran:
 *       full ambiguity retained).
 *   T6  optout_toggle                 — the mode switch (auto vs none) flips the
 *       outcome: none is the identity (byte-identical), auto is active.
 *   T7  reservation_lexer_local       — reservation is confined to the lexer;
 *       the parser never consults `reserved` (any two settings that agree on the
 *       token stream agree on the parse).
 * ★ T8  nullary_keyword_lexfork_seeds_own_accept — a reserved nullary keyword
 *       parses iff the fork seed is on (its OWN `Fixed(kw)` accept) OR it is not
 *       reserved (the `Ident` co-accept); the pre-fix reserved-without-fork case
 *       FAILS; inert without reservation.
 * ★ T9  send_sugar_canon_unifies      — `@Nil!(q)`: `canon(POutputNil q) =
 *       canon(POutputShort PZero q)` ⇒ `term_eq` true; the two readings stay
 *       DISTINCT pre-canon (parse ambiguity preserved).
 *   T10 canon_idempotent_deterministic — `canon (canon p) = canon p`, and canon
 *       is a (deterministic) function.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions (Section
 * Variables are discharged; every theorem closes under the global context).
 * Model style follows AtQuotedBindGate.v / CrossCatLexCompatGate.v.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section KeywordReservation.

  (* ── Grammar terminals. A terminal is either IDENTIFIER-SHAPED (spelled like an
        identifier — `Nil`/`Set`/`error`/`DO`, reservable) or a BRACKET /
        punctuation opener (`[`/`{`/`(`/`,`/`!`, never reservable). A keyword id is
        modeled as a `nat`. ── *)
  Inductive Terminal : Type :=
    | TIdentShaped (kw : nat)
    | TBracket (b : nat).

  Definition is_ident_shaped (t : Terminal) : bool :=
    match t with
    | TIdentShaped _ => true
    | TBracket _ => false
    end.

  (* ── Lexer accept token kinds: the generic identifier pattern, or a fixed
        keyword literal `Fixed(kw)`. ── *)
  Inductive TokenKind : Type :=
    | Ident
    | Fixed (kw : nat).

  Definition is_ident (k : TokenKind) : bool :=
    match k with Ident => true | Fixed _ => false end.

  (* ── The grammar-derived reserved set: extract the keyword ids of exactly the
        identifier-shaped literal terminals (`collect_first_set`-style filter). ── *)
  Definition reserved_of_grammar (terms : list Terminal) : list nat :=
    flat_map (fun t => match t with TIdentShaped kw => [kw] | TBracket _ => [] end) terms.

  (* ── T1: the reserved set = EXACTLY the identifier-shaped literal terminals. ── *)
  Theorem T1_reserved_set_grammar_derived :
    forall terms kw,
      In kw (reserved_of_grammar terms) <-> In (TIdentShaped kw) terms.
  Proof.
    intros terms kw. unfold reserved_of_grammar. rewrite in_flat_map. split.
    - intros [t [Hin Hkw]]. destruct t as [kw' | b]; simpl in Hkw.
      + destruct Hkw as [Heq | []]. subst kw'. exact Hin.
      + destruct Hkw.
    - intro Hin. exists (TIdentShaped kw). split; [exact Hin | simpl; left; reflexivity].
  Qed.

  (* ONLY ident-shaped terminals are reserved (grammar-derived: bracket / punctuation
     openers like `[`/`{` never join the reserved set — the forward direction of T1,
     stated positively as the over-generation-free direction). *)
  Theorem T1_only_ident_shaped_reserved :
    forall terms kw, In kw (reserved_of_grammar terms) -> In (TIdentShaped kw) terms.
  Proof. intros terms kw H. apply T1_reserved_set_grammar_derived. exact H. Qed.

  (* ── Reservation policy. `PolAuto ctx` = reserve every ident-shaped terminal
        EXCEPT those in the contextual opt-out `ctx`; `PolNone` = reserve nothing
        (`reserved_keywords: none`, byte-identical). ── *)
  Inductive Policy : Type :=
    | PolAuto (ctx : list nat)
    | PolNone.

  Definition reserved_under (p : Policy) (terms : list Terminal) : list nat :=
    match p with
    | PolNone => []
    | PolAuto ctx =>
        filter (fun kw => negb (existsb (Nat.eqb kw) ctx)) (reserved_of_grammar terms)
    end.

  (* Membership helpers on `existsb (Nat.eqb _)`. *)
  Lemma existsb_eqb_in :
    forall kw l, In kw l -> existsb (Nat.eqb kw) l = true.
  Proof.
    intros kw l Hin. apply existsb_exists. exists kw. split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  Lemma not_in_existsb_eqb :
    forall kw l, ~ In kw l -> existsb (Nat.eqb kw) l = false.
  Proof.
    intros kw l Hnin. apply Bool.not_true_is_false. intro Ht.
    apply existsb_exists in Ht. destruct Ht as [x [Hx Heq]].
    apply Nat.eqb_eq in Heq. subst x. contradiction.
  Qed.

  (* A keyword in the contextual opt-out `ctx` is EXCLUDED from the `auto`
     reserved set (filtered out) — the general mechanism behind the Fortran
     opt-out. *)
  Lemma reserved_under_auto_excludes_ctx :
    forall kw terms ctx,
      In kw ctx -> ~ In kw (reserved_under (PolAuto ctx) terms).
  Proof.
    intros kw terms ctx Hctx H. unfold reserved_under in H.
    apply filter_In in H. destruct H as [_ Hp]. cbv beta in Hp.
    rewrite (existsb_eqb_in kw ctx Hctx) in Hp. discriminate.
  Qed.

  (* ── T2: under `auto` with no contextual opt-out, every ident-shaped terminal
        is RESERVED (default = reserve). ── *)
  Theorem T2_default_reserves :
    forall terms kw,
      In (TIdentShaped kw) terms -> In kw (reserved_under (PolAuto []) terms).
  Proof.
    intros terms kw Hin. simpl.
    apply filter_In. split.
    - apply T1_reserved_set_grammar_derived. exact Hin.
    - simpl. reflexivity.
  Qed.

  (* ── The lexer accept-set resolver (`resolve_accept`, subset.rs). If the
        primary (highest-priority) accept `alts[0]` is a reserved keyword, drop the
        generic `Ident` co-accept; otherwise leave the alt-set untouched. When
        `reserved` is empty this branch is never taken ⇒ byte-identical. ── *)
  Definition resolve_accept (reserved : list nat) (alts : list TokenKind) : list TokenKind :=
    match alts with
    | Fixed kw :: _ =>
        if existsb (Nat.eqb kw) reserved
        then filter (fun k => negb (is_ident k)) alts
        else alts
    | _ => alts
    end.

  (* ── T3: at the keyword's exact-match state {Fixed(kw), Ident}, reserving `kw`
        drops the `Ident` co-accept, leaving {Fixed(kw)}. ── *)
  Theorem T3_reserving_removes_ident_co_accept :
    forall kw reserved,
      In kw reserved ->
      resolve_accept reserved [Fixed kw; Ident] = [Fixed kw].
  Proof.
    intros kw reserved Hin. unfold resolve_accept.
    rewrite (existsb_eqb_in kw reserved Hin). simpl. reflexivity.
  Qed.

  (* ── T3: reservation is a STRICT REFINEMENT — every resolved accept was already
        an accept (monotone subset; nothing invented). ── *)
  Theorem T3_resolve_is_refinement :
    forall reserved alts k,
      In k (resolve_accept reserved alts) -> In k alts.
  Proof.
    intros reserved alts k H. unfold resolve_accept in H.
    destruct alts as [| a rest]; [exact H |].
    destruct a as [| kw]; [exact H |].
    destruct (existsb (Nat.eqb kw) reserved).
    - apply filter_In in H. destruct H as [H _]. exact H.
    - exact H.
  Qed.

  (* ── T3: the keyword reading itself is always KEPT (only `Ident` is removed —
        the over-generation, never the keyword). ── *)
  Theorem T3_keeps_keyword :
    forall kw reserved,
      In (Fixed kw) (resolve_accept reserved [Fixed kw; Ident]).
  Proof.
    intros kw reserved. unfold resolve_accept.
    destruct (existsb (Nat.eqb kw) reserved).
    - simpl. left. reflexivity.
    - simpl. left. reflexivity.
  Qed.

  (* ── T4: a plain-variable state (primary `Ident`, not a keyword literal) keeps
        `Ident` — no legitimate variable reading is lost. ── *)
  Theorem T4_no_legit_var_lost :
    forall reserved, resolve_accept reserved [Ident] = [Ident].
  Proof. intro reserved. reflexivity. Qed.

  (* ── T4: a NON-reserved keyword state keeps BOTH accepts (nothing dropped when
        the primary is not reserved). ── *)
  Theorem T4_nonreserved_keeps_ident :
    forall kw reserved,
      ~ In kw reserved ->
      resolve_accept reserved [Fixed kw; Ident] = [Fixed kw; Ident].
  Proof.
    intros kw reserved Hnin. unfold resolve_accept.
    rewrite (not_in_existsb_eqb kw reserved Hnin). reflexivity.
  Qed.

  (* ── T5: a CONTEXTUAL OPT-OUT keeps a would-be-reserved (ident-shaped) keyword
        UN-reserved, so its exact-match state keeps BOTH {Fixed(kw), Ident} —
        FULL AMBIGUITY preserved (Fortran `DO`/`IF`). ── *)
  Theorem T5_contextual_optout_preserves_ambiguity :
    forall kw terms,
      In (TIdentShaped kw) terms ->
      ~ In kw (reserved_under (PolAuto [kw]) terms)
      /\ resolve_accept (reserved_under (PolAuto [kw]) terms) [Fixed kw; Ident]
           = [Fixed kw; Ident].
  Proof.
    intros kw terms Hin.
    assert (Hnr : ~ In kw (reserved_under (PolAuto [kw]) terms)).
    { apply reserved_under_auto_excludes_ctx. simpl. left. reflexivity. }
    split.
    - exact Hnr.
    - apply T4_nonreserved_keeps_ident. exact Hnr.
  Qed.

  (* ── T6: the mode-switch (auto vs none). PolNone reserves nothing ⇒ the resolver
        is the IDENTITY (byte-identical); PolAuto reserves the ident-shaped
        terminals (active). ── *)
  Theorem T6_empty_reserved_identity :
    forall alts, resolve_accept [] alts = alts.
  Proof.
    intro alts. unfold resolve_accept.
    destruct alts as [| a rest]; [reflexivity |].
    destruct a as [| kw]; reflexivity.
  Qed.

  Theorem T6_optout_toggle :
    forall kw terms,
      In (TIdentShaped kw) terms ->
      resolve_accept (reserved_under PolNone terms) [Fixed kw; Ident] = [Fixed kw; Ident]
      /\ resolve_accept (reserved_under (PolAuto []) terms) [Fixed kw; Ident] = [Fixed kw].
  Proof.
    intros kw terms Hin. split.
    - reflexivity.
    - apply T3_reserving_removes_ident_co_accept. apply T2_default_reserves. exact Hin.
  Qed.

  (* ── T7: reservation is LEXER-LOCAL. The parser is a pure function of the token
        stream; it never consults `reserved`. So any two reservation settings that
        agree on the token stream produce the identical parse — the reservation's
        ONLY channel of influence is the lexer's accept-set resolution. ── *)
  Section LexerLocal.

    Variable Token : Type.
    Variable ParseResult : Type.
    (* The PARSER — note: NO `reserved` parameter. *)
    Variable parse : list Token -> ParseResult.
    (* The LEXER — resolves accept-sets using `reserved`, producing a token stream. *)
    Variable lex : list nat -> list Token.

    Definition pipeline (reserved : list nat) : ParseResult := parse (lex reserved).

    (* The pipeline factors as `parse ∘ lex`: the parser sees only tokens. *)
    Theorem T7_pipeline_factors :
      forall reserved, pipeline reserved = parse (lex reserved).
    Proof. intro reserved. reflexivity. Qed.

    (* If two reservation settings yield the same token stream, the whole pipeline
       agrees — the parser has no independent dependence on `reserved`. *)
    Theorem T7_reservation_lexer_local :
      forall r1 r2, lex r1 = lex r2 -> pipeline r1 = pipeline r2.
    Proof. intros r1 r2 H. unfold pipeline. rewrite H. reflexivity. Qed.

  End LexerLocal.

  (* ── T8: the NULLARY-KEYWORD LEX-FORK SEED (FIX-FORK, a6683ee9). A reserved
        nullary keyword's cursor must seed from its OWN `Fixed(kw)` accept, not the
        (reservation-removed) `Ident` co-accept. ── *)
  Section NullaryLexFork.

    (* Whether a reserved nullary keyword parses, given `reserved` (is the keyword
       reserved?) and `fork_seed` (is `NULLARY_KEYWORD_LEXFORK_SEED` on?): it parses
       iff the fork seeds its own accept, OR it is not reserved (the `Ident`
       co-accept still seeds it). *)
    Definition nullary_parses (reserved fork_seed : bool) : bool :=
      fork_seed || negb reserved.

    (* SHIPPED config (cc6503c6): reserved + fork ⇒ parses (own `Fixed(kw)` accept:
       `*x | Nil`, `for(){Nil}`, `@Nil!(Nil)` all parse under reservation). *)
    Theorem T8_shipped_parses : nullary_parses true true = true.
    Proof. reflexivity. Qed.

    (* PRE-FIX bug: reserved WITHOUT the fork ⇒ FAILS (the `Ident` co-accept the
       nullary rule relied on is gone; `*x|Nil` / `for(){Nil}` regressed). *)
    Theorem T8_prefix_bug_fails : nullary_parses true false = false.
    Proof. reflexivity. Qed.

    (* INERT without reservation: the fork seed does not change the outcome when the
       keyword is not reserved (the `Ident` co-accept still seeds it — provably
       byte-identical, so the fork is safe to leave default-on). *)
    Theorem T8_inert_without_reservation :
      forall fs, nullary_parses false fs = nullary_parses false true.
    Proof. intro fs. destruct fs; reflexivity. Qed.

    (* The SEED SOURCE: with the fork the cursor seeds from `Fixed(kw)` (its own
       accept); reserved-without-fork leaves it UN-seeded (the hang/fail); not
       reserved falls back to the `Ident` co-accept. *)
    Inductive SeedSource : Type :=
      | SeedFixed (kw : nat)
      | SeedIdent
      | SeedNone.

    Definition seed_source (kw : nat) (reserved fork_seed : bool) : SeedSource :=
      if fork_seed then SeedFixed kw
      else if reserved then SeedNone
      else SeedIdent.

    (* SHIPPED: reserved + fork ⇒ seeds from its OWN `Fixed(kw)` accept. *)
    Theorem T8_nullary_keyword_lexfork_seeds_own_accept :
      forall kw, seed_source kw true true = SeedFixed kw.
    Proof. intro kw. reflexivity. Qed.

    (* PRE-FIX: reserved + no fork ⇒ the `Ident` co-accept is gone ⇒ NO seed. *)
    Theorem T8_prefix_seed_lost :
      forall kw, seed_source kw true false = SeedNone.
    Proof. intro kw. reflexivity. Qed.

  End NullaryLexFork.

  (* ── T9 / T10: the @Nil-send CANONICALIZATION (aa78d51b). ── *)
  Section SendSugarCanon.

    (* A minimal Proc model with the `@`-send sugar variants of `@Nil!(q)`.
       `NQuoteWrap p` models `NQuote(p)` in a Proc position; `POutputCanon chan q`
       is the channel-first fold target `POutput(NQuote(chan), q)`. *)
    Inductive Proc : Type :=
      | PZero
      | PVar (x : nat)
      | NQuoteWrap (p : Proc)
      | POutputCanon (chan : Proc) (payload : Proc)
      | POutputNil (payload : Proc)
      | POutputShort (chan : Proc) (payload : Proc).

    (* The deep `@`-send-sugar canonicalizer (`normalize_send_sugar_canon`): rewrite
       each send sugar to its channel-first fold target and RECURSE into every
       subterm. `POutputNil q ↦ POutput(NQuote(PZero), canon q)`;
       `POutputShort p q ↦ POutput(NQuote(canon p), canon q)`. *)
    Fixpoint canon (p : Proc) : Proc :=
      match p with
      | PZero => PZero
      | PVar x => PVar x
      | NQuoteWrap q => NQuoteWrap (canon q)
      | POutputCanon c q => POutputCanon (canon c) (canon q)
      | POutputNil q => POutputCanon (NQuoteWrap PZero) (canon q)
      | POutputShort c q => POutputCanon (NQuoteWrap (canon c)) (canon q)
      end.

    (* A structural term equality (`term_eq`) with reflexivity. *)
    Fixpoint term_eq (a b : Proc) : bool :=
      match a, b with
      | PZero, PZero => true
      | PVar x, PVar y => Nat.eqb x y
      | NQuoteWrap p, NQuoteWrap q => term_eq p q
      | POutputCanon c1 q1, POutputCanon c2 q2 => term_eq c1 c2 && term_eq q1 q2
      | POutputNil q1, POutputNil q2 => term_eq q1 q2
      | POutputShort c1 q1, POutputShort c2 q2 => term_eq c1 c2 && term_eq q1 q2
      | _, _ => false
      end.

    Lemma term_eq_refl : forall p, term_eq p p = true.
    Proof.
      induction p as [| x | p IHp | c IHc q IHq | q IHq | c IHc q IHq ]; simpl.
      - reflexivity.
      - apply Nat.eqb_refl.
      - exact IHp.
      - rewrite IHc, IHq. reflexivity.
      - exact IHq.
      - rewrite IHc, IHq. reflexivity.
    Qed.

    (* ── T9: `@Nil!(q)` — `POutputNil(q)` and `POutputShort(PZero, q)` canonicalize
          to the SAME term (`POutput(NQuote(PZero), canon q)`). ── *)
    Theorem T9_send_sugar_canon_unifies :
      forall q, canon (POutputNil q) = canon (POutputShort PZero q).
    Proof. intro q. simpl. reflexivity. Qed.

    (* ⇒ `term_eq` is TRUE on the canonicalized forms (`@Nil!(q)` cohort 2→1). *)
    Theorem T9_term_eq_after_canon :
      forall q, term_eq (canon (POutputNil q)) (canon (POutputShort PZero q)) = true.
    Proof.
      intro q. rewrite (T9_send_sugar_canon_unifies q). apply term_eq_refl.
    Qed.

    (* PARSE AMBIGUITY PRESERVED (never-disambiguate-early): the two readings stay
       DISTINCT before canon, so `parse_via_wpda_all` returns BOTH; canon unifies
       only in the POST-PARSE `term_eq`/COMM comparison path. *)
    Theorem T9_distinct_before_canon :
      forall q, POutputNil q <> POutputShort PZero q.
    Proof. intros q H. discriminate H. Qed.

    (* ── T10: canon is IDEMPOTENT (`canon (canon p) = canon p`) — repeated
          canonicalization is stable. ── *)
    Theorem T10_canon_idempotent :
      forall p, canon (canon p) = canon p.
    Proof.
      induction p as [| x | p IHp | c IHc q IHq | q IHq | c IHc q IHq ]; simpl.
      - reflexivity.
      - reflexivity.
      - rewrite IHp. reflexivity.
      - rewrite IHc, IHq. reflexivity.
      - (* POutputNil q ↦ POutputCanon (NQuoteWrap PZero) (canon q) *)
        rewrite IHq. reflexivity.
      - (* POutputShort c q ↦ POutputCanon (NQuoteWrap (canon c)) (canon q) *)
        rewrite IHc, IHq. reflexivity.
    Qed.

    (* ── T10: canon is a DETERMINISTIC function — equal inputs give equal outputs
          (congruence). Combined with idempotence: the canonical form is a stable,
          well-defined representative. ── *)
    Theorem T10_canon_deterministic :
      forall p1 p2, p1 = p2 -> canon p1 = canon p2.
    Proof. intros p1 p2 H. rewrite H. reflexivity. Qed.

  End SendSugarCanon.

End KeywordReservation.

(* ══════════════ Non-vacuity witnesses (concrete finite instantiations). ══════════════ *)

(* A tiny grammar: `Nil` (ident-shaped, id 0), `Set` (ident-shaped, id 1),
   `[` (bracket, id 0). Reserved (auto, no opt-out) = {Nil, Set}; the bracket is
   NOT reserved. *)
Definition demo_grammar : list Terminal := [TIdentShaped 0; TIdentShaped 1; TBracket 0].

Example T1_witness_nil_reserved : In 0 (reserved_of_grammar demo_grammar).
Proof. apply T1_reserved_set_grammar_derived. simpl. left. reflexivity. Qed.

Example T1_witness_bracket_not_reserved : reserved_of_grammar demo_grammar = [0; 1].
Proof. reflexivity. Qed.

Example T1_witness_brackets_reserve_nothing :
  reserved_of_grammar [TBracket 0; TBracket 1] = [].
Proof. reflexivity. Qed.

(* T3 witness — `Nil` reserved: {Fixed(Nil), Ident} ↦ {Fixed(Nil)} (Ident dropped). *)
Example T3_witness_nil_drops_ident :
  resolve_accept [0] [Fixed 0; Ident] = [Fixed 0].
Proof. reflexivity. Qed.

(* T4 witness — a plain variable `x` (Ident-only) is untouched by ANY reserved set. *)
Example T4_witness_var_kept :
  resolve_accept [0; 1] [Ident] = [Ident].
Proof. reflexivity. Qed.

(* T5 witness — Fortran `DO` (ident-shaped, id 0) with contextual opt-out {DO}:
   both {Fixed(DO), Ident} readings survive (the `DO 10 I=1.5` vs `DO 10 I=1,5`
   archetype — full ambiguity retained). *)
Example T5_witness_fortran_do_ambiguous :
  resolve_accept (reserved_under (PolAuto [0]) demo_grammar) [Fixed 0; Ident]
    = [Fixed 0; Ident].
Proof. reflexivity. Qed.

(* T6 witness — the same `Nil` state resolves differently under the two modes:
   none keeps both, auto drops Ident. *)
Example T6_witness_mode_flip :
  resolve_accept (reserved_under PolNone demo_grammar) [Fixed 0; Ident] = [Fixed 0; Ident]
  /\ resolve_accept (reserved_under (PolAuto []) demo_grammar) [Fixed 0; Ident] = [Fixed 0].
Proof. split; reflexivity. Qed.

(* T8 witness — the FIX-FORK truth table: reservation makes the pre-fix nullary
   keyword fail, and the fork seed recovers it. *)
Example T8_witness_truth_table :
  nullary_parses true true = true          (* reserved + fork: parses (own accept) *)
  /\ nullary_parses true false = false     (* reserved, no fork: FAILS (pre-fix)    *)
  /\ nullary_parses false false = true     (* not reserved: parses (Ident co-accept) *)
  /\ nullary_parses false true = true.     (* not reserved + fork: still parses      *)
Proof. repeat split; reflexivity. Qed.

(* T9 witness — `@Nil!(0)`: the two sugar readings unify under canon, term_eq true,
   yet are distinct pre-canon. *)
Example T9_witness_at_nil_send :
  canon (POutputNil (PVar 0)) = canon (POutputShort PZero (PVar 0))
  /\ term_eq (canon (POutputNil (PVar 0))) (canon (POutputShort PZero (PVar 0))) = true.
Proof. split; [apply T9_send_sugar_canon_unifies | apply T9_term_eq_after_canon]. Qed.

(* T10 witness — canon of `@Nil!(@Nil!(0))` is idempotent. *)
Example T10_witness_idempotent :
  canon (canon (POutputNil (POutputNil (PVar 0)))) = canon (POutputNil (POutputNil (PVar 0))).
Proof. apply T10_canon_idempotent. Qed.

(* ══════════════ Admission audit — every theorem must print
   "Closed under the global context" (no Admitted, no Axiom, no Assumption). ══════════════ *)
Print Assumptions T1_reserved_set_grammar_derived.
Print Assumptions T1_only_ident_shaped_reserved.
Print Assumptions T2_default_reserves.
Print Assumptions T3_reserving_removes_ident_co_accept.
Print Assumptions T3_resolve_is_refinement.
Print Assumptions T3_keeps_keyword.
Print Assumptions T4_no_legit_var_lost.
Print Assumptions T4_nonreserved_keeps_ident.
Print Assumptions T5_contextual_optout_preserves_ambiguity.
Print Assumptions T6_empty_reserved_identity.
Print Assumptions T6_optout_toggle.
Print Assumptions T7_pipeline_factors.
Print Assumptions T7_reservation_lexer_local.
Print Assumptions T8_shipped_parses.
Print Assumptions T8_prefix_bug_fails.
Print Assumptions T8_inert_without_reservation.
Print Assumptions T8_nullary_keyword_lexfork_seeds_own_accept.
Print Assumptions T8_prefix_seed_lost.
Print Assumptions T9_send_sugar_canon_unifies.
Print Assumptions T9_term_eq_after_canon.
Print Assumptions T9_distinct_before_canon.
Print Assumptions T10_canon_idempotent.
Print Assumptions T10_canon_deterministic.
Print Assumptions T1_witness_nil_reserved.
Print Assumptions T1_witness_bracket_not_reserved.
Print Assumptions T1_witness_brackets_reserve_nothing.
Print Assumptions T3_witness_nil_drops_ident.
Print Assumptions T4_witness_var_kept.
Print Assumptions T5_witness_fortran_do_ambiguous.
Print Assumptions T6_witness_mode_flip.
Print Assumptions T8_witness_truth_table.
Print Assumptions T9_witness_at_nil_send.
Print Assumptions T10_witness_idempotent.
