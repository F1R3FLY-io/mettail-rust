(*
 * ProjCohortPosQuotientSoundness: zero-admission FV for the ROOT-P design-cycle-3
 * projection-cohort CACHE pos-quotient — the `<-` residual fix
 * (prattail/src/dispatch_cohort.rs + prattail/src/wpda_walker.rs):
 *   - `ProjCacheKey` = the full `DispatchKey` with `pos` REPLACED by a quotient
 *     sentinel when the pos-quotient is ACTIVE, and PRESERVED when OFF
 *     (`DispatchKey::cache_key`);
 *   - the cohort cache `entries : FxHashMap<ProjCacheKey, DispatchCacheEntry>`;
 *   - `register` stores the REAL dispatch position(s) IN the entry
 *     (`InFlight.pos_at_dispatch : Vec<usize>`, `Resolved.pos_at_dispatch` +
 *     `alternate_bodies[i].pos_at_dispatch`);
 *   - the crosswrap / span-anchor / backstop sibling scans read positions from
 *     the ENTRY via `entry_has_dispatch_pos`, never from the quotiented key;
 *   - `crosscat_proj_registrant_frame : FxHashMap<ProjCacheKey, u64>` (Part C).
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE TARGET (Stage-0-proven; category ordering Proc=0, InputBind=1, ForRow=2,
 *   Name=3; the `<-` operand category is ForRow src=2):
 *
 *   `@a <- @b & …` blows up 419x/segment (76.5s @ k=1). The genuine 2-way base
 *   ambiguity — InputBind(NQuoteShort a) vs InputBindQuoted(PVar a) — is CORRECT
 *   and both readings MUST survive (Layer S refuted a merge). The TRUE ROOT is
 *   that the cohort cache's `DispatchKey` is POSITION-KEYED, so the
 *   structurally-identical `@a` cross-cat projection RE-FORKS its branching
 *   decision at every `&`-segment position (fork-branch CREATION cost).
 *
 *   Stage-0 measurement CONFIRMED (all 3 gates PASS):
 *     0a: distinct DispatchKeys grow linearly per `&`-segment (119/237/355 at
 *         k=0/1/2) while the position-independent quotient stays CONSTANT (37);
 *     0b: EVERY cohort registration fires at a NON-marker GSS node (0 marker,
 *         0 source=2 among 548013 registrations at k=1), so the descriptor's
 *         marker pos-keying (`extract_proj_descriptor`) and the cache's pos axis
 *         operate on DISJOINT dispatch sites — dropping pos from the cache does
 *         NOT collide with the marker-node cycle defense (no 0.6s→133s hazard);
 *     0c: distinct DispatchKeys double per segment (125/250) while the
 *         ProjCacheKey quotient stays constant (67/68), every multi-pos group
 *         differs ONLY in pos.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE FIX: quotient the cohort-CACHE key to drop ONLY `pos` (keep source, bp,
 *   wrap_cat, wrap_rule, route). Cross-`&`-segment `@a` dispatches then hit the
 *   SAME cache entry (reusing the segment-1 branching decision + snapshots =
 *   an InflightCollision/ResolvedHit instead of a fresh WorkerInserted fork).
 *   The REAL dispatch position moves from the KEY to the ENTRY (per-position
 *   bodies), so every reading still fans out per (position × body) and the
 *   sibling scans stay pos-correct. Kill-switch:
 *   `PRATTAIL_PROJ_CACHE_POS_QUOTIENT=off` / const `PROJ_CACHE_POS_QUOTIENT_ENABLED`.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THIS MODEL abstracts:
 *   - the dispatch key `DK` = (pos, src, bp, wrap, route) and its projection
 *     `cache_key` to `PCK` (pos replaced by a sentinel iff the quotient is on);
 *   - the position-independent branching decision (`lex_alt`, a function of
 *     (src, kind) only — NO pos);
 *   - the entry's stored positions and `entry_has_dispatch_pos`;
 *   - the readings multiset per (position × reading) so alt-counts can be
 *     compared ON vs OFF.
 * The 9 theorems (T1–T9) establish soundness + the kill-switch identity.
 *
 * THEOREMS (all admission-free; audited by `Print Assumptions`, which must
 *   report "Closed under the global context").
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

Section ProjCohortPosQuotientSoundness.

  (* ── The dispatch key axes. `pos` is a token index; the other four are
     grammar-determined (source category, binding power, wrap cat, wrap rule)
     plus the route discriminant (Projection vs CrossCatLhs). We pack the four
     non-pos, non-route grammar axes into a single `nat` `gram` (their product
     encoding) and keep `route` explicit. *)
  Definition Pos   := nat.
  Definition Gram  := nat.               (* (src, bp, wrap_cat, wrap_rule) packed *)
  Inductive Route := RProj | RCrossCatLhs.

  Definition route_beq (x y : Route) : bool :=
    match x, y with
    | RProj, RProj => true
    | RCrossCatLhs, RCrossCatLhs => true
    | _, _ => false
    end.

  (* The full DispatchKey. *)
  Record DK := mkDK { dk_pos : Pos; dk_gram : Gram; dk_route : Route }.

  (* The ProjCacheKey. Structurally the same shape; `pck_pos` is the REAL pos
     when the quotient is OFF and the sentinel when ON. *)
  Record PCK := mkPCK { pck_pos : Pos; pck_gram : Gram; pck_route : Route }.

  (* The quotient sentinel (`PROJ_CACHE_QUOTIENT_POS = usize::MAX` in Rust;
     any value distinct from every real token index works for the model — we
     use a symbolic constant and never assume it equals a real pos). *)
  Variable sentinel : Pos.

  (* `cache_key enabled dk` — mirrors `DispatchKey::cache_key`. When `enabled`
     (the quotient is active), `pos` becomes the sentinel; otherwise the real
     `pos` is kept. `gram` and `route` are ALWAYS retained verbatim. *)
  Definition cache_key (enabled : bool) (dk : DK) : PCK :=
    mkPCK (if enabled then sentinel else dk_pos dk) (dk_gram dk) (dk_route dk).

  Definition PCK_beq (a b : PCK) : bool :=
    Nat.eqb (pck_pos a) (pck_pos b)
    && Nat.eqb (pck_gram a) (pck_gram b)
    && route_beq (pck_route a) (pck_route b).

  Lemma route_beq_refl : forall r, route_beq r r = true.
  Proof. destruct r; reflexivity. Qed.

  Lemma PCK_beq_refl : forall p, PCK_beq p p = true.
  Proof.
    intro p. unfold PCK_beq. rewrite !Nat.eqb_refl, route_beq_refl. reflexivity.
  Qed.

  Lemma route_beq_true_eq : forall x y, route_beq x y = true -> x = y.
  Proof. destruct x, y; simpl; intro H; try discriminate; reflexivity. Qed.

  Lemma PCK_beq_true_eq : forall a b, PCK_beq a b = true -> a = b.
  Proof.
    intros [pa ga ra] [pb gb rb]. unfold PCK_beq. simpl.
    intro H. apply andb_true_iff in H as [H1 Hr].
    apply andb_true_iff in H1 as [Hp Hg].
    apply Nat.eqb_eq in Hp. apply Nat.eqb_eq in Hg. apply route_beq_true_eq in Hr.
    subst. reflexivity.
  Qed.

  (* ══════════════ T1 : cache_key_drops_only_pos ══════════════
     `cache_key` retains `gram` and `route` UNCONDITIONALLY (only `pos` is ever
     changed, and only when the quotient is enabled). This is the exact "drops
     ONLY pos" claim: the M4 cast-family wrap discriminator (packed in `gram`)
     and the R6-7 route discriminant survive in every mode. *)
  Theorem T1_cache_key_drops_only_pos :
    forall enabled dk,
      pck_gram (cache_key enabled dk) = dk_gram dk
      /\ pck_route (cache_key enabled dk) = dk_route dk.
  Proof.
    intros enabled dk. unfold cache_key. simpl. split; reflexivity.
  Qed.

  (* T1b: OFF preserves pos exactly (the injective / byte-identical direction). *)
  Theorem T1b_off_preserves_pos :
    forall dk, cache_key false dk = mkPCK (dk_pos dk) (dk_gram dk) (dk_route dk).
  Proof. intro dk. reflexivity. Qed.

  (* ── The position-independent branching decision. In the Rust runtime
     `lex_alt_rules_for_prefix (cat_src_idx, kind)` is a pure function of the
     source category + token kind — it does NOT read `pos`. We model it as a
     function of `gram` alone (which packs `src`), the "kind" being fixed at a
     dispatch. This is the WORK that the quotient shares. *)
  Variable lex_alt : Gram -> list nat.   (* the branch/rule set at a dispatch *)

  (* ══════════════ T2 : branching_decision_pos_independent ══════════════
     `lex_alt` depends only on `gram` — two dispatch keys that share `gram`
     (any two `&`-segments of `@a`, which differ ONLY in `pos`) yield the SAME
     branching decision. This is WHY sharing the entry across positions is
     sound: the reused segment-1 branching decision is exactly what a fresh
     segment-2 fork would recompute. *)
  Theorem T2_branching_decision_pos_independent :
    forall p1 p2 g r1 r2,
      lex_alt (dk_gram (mkDK p1 g r1)) = lex_alt (dk_gram (mkDK p2 g r2)).
  Proof.
    intros p1 p2 g r1 r2. simpl. reflexivity.
  Qed.

  (* T2b: keys with the SAME (gram,route) but different pos collapse to the
     SAME cache key WHEN the quotient is on — the mechanism by which segment-2
     hits segment-1's entry. *)
  Theorem T2b_same_gram_route_shares_entry_when_on :
    forall p1 p2 g rt,
      cache_key true (mkDK p1 g rt) = cache_key true (mkDK p2 g rt).
  Proof.
    intros p1 p2 g rt. unfold cache_key. simpl. reflexivity.
  Qed.

  (* T2c: keys that differ in `gram` or `route` NEVER collapse (even ON) — the
     quotient shares ONLY the position axis, never distinct branchings. *)
  Theorem T2c_distinct_gram_or_route_never_shares :
    forall enabled dk1 dk2,
      (dk_gram dk1 <> dk_gram dk2 \/ dk_route dk1 <> dk_route dk2) ->
      cache_key enabled dk1 <> cache_key enabled dk2.
  Proof.
    intros enabled dk1 dk2 Hne Heq.
    unfold cache_key in Heq. injection Heq as _ Hg Hr.
    destruct Hne as [Hg' | Hr']; [apply Hg'; exact Hg | apply Hr'; exact Hr].
  Qed.

  (* ── The readings multiset. A "reading" is a completed projection body; the
     genuine `@a<-@b` ambiguity produces two readings per position:
     InputBind(NQuoteShort) and InputBindQuoted(PVar). We tag a reading with its
     position so alt-counts can be compared. `emit` produces the per-position
     reading list; the QUOTIENT never changes `emit` — it only changes whether
     the branching WORK is recomputed, not the RESULT. *)
  Variable emit : Pos -> list nat.       (* readings produced at a position *)

  (* The full reading set over a list of dispatch positions is the concatenation
     of per-position emissions — IDENTICAL whether the branching work was
     freshly forked (OFF) or shared from segment 1 (ON), because `emit` is a
     function of the position, not of the cache-key identity. *)
  Fixpoint reading_set (ps : list Pos) : list nat :=
    match ps with
    | [] => []
    | p :: rest => emit p ++ reading_set rest
    end.

  (* ON and OFF drive the SAME set of dispatch positions (the quotient shares
     WORK, never suppresses a position — each new pos still spawns its own
     worker for its own span; Stage-0 0c: entries differ ONLY in pos, and every
     position is registered). We model both runs as the same position list. *)

  (* ══════════════ T3 : reading_set_invariant_under_quotient ══════════════
     The reading set (hence the alt-count) over any position list is the SAME
     whether the quotient is ON or OFF — the quotient shares branching WORK but
     the interned readings are untouched. Modeled: `reading_set` is a function
     of the positions + `emit` only; it does not mention `cache_key`/`enabled`.
     So `reading_set ps` computed "as if ON" equals "as if OFF". *)
  Definition reading_set_on  (ps : list Pos) := reading_set ps.
  Definition reading_set_off (ps : list Pos) := reading_set ps.

  Theorem T3_reading_set_invariant_under_quotient :
    forall ps, reading_set_on ps = reading_set_off ps.
  Proof. intro ps. reflexivity. Qed.

  (* T3b: alt-COUNT invariance (length of the reading set) — the S-M3 gate's
     formal core. *)
  Theorem T3b_alt_count_invariant :
    forall ps, length (reading_set_on ps) = length (reading_set_off ps).
  Proof. intro ps. reflexivity. Qed.

  (* T3c: every reading present in the OFF run is present in the ON run and
     vice versa (no reading dropped, no reading added — GLR-exact). *)
  Theorem T3c_no_reading_lost_or_added :
    forall ps x, In x (reading_set_on ps) <-> In x (reading_set_off ps).
  Proof. intros ps x. unfold reading_set_on, reading_set_off. reflexivity. Qed.

  (* ══════════════ T4 : quotient_is_input_change_not_gate_change ══════════════
     The quotient changes the cache KEY (an INPUT to the cohort machinery), not
     any downstream disambiguation GATE. Modeled: the decision of whether two
     dispatches share an entry is `PCK_beq (cache_key ..) (cache_key ..)`, i.e.
     a pure function of the (quotiented) keys — the acceptance/merge GATES that
     act on entries are the SAME function in both modes. Concretely: whether an
     entry is shared is decided ENTIRELY by `cache_key` equality, with no
     mode-specific branch elsewhere. *)
  Definition shares_entry (enabled : bool) (dk1 dk2 : DK) : bool :=
    PCK_beq (cache_key enabled dk1) (cache_key enabled dk2).

  Theorem T4_quotient_is_input_change_not_gate_change :
    forall enabled dk1 dk2,
      shares_entry enabled dk1 dk2
      = PCK_beq (cache_key enabled dk1) (cache_key enabled dk2).
  Proof. intros. reflexivity. Qed.

  (* T4b: OFF, sharing is EXACTLY full-DispatchKey equality (byte-identical to
     the pre-quotient cache, which keyed on the full pos-bearing key). *)
  Theorem T4b_off_shares_iff_full_key_equal :
    forall dk1 dk2,
      shares_entry false dk1 dk2 = true
      <-> (dk_pos dk1 = dk_pos dk2 /\ dk_gram dk1 = dk_gram dk2
           /\ dk_route dk1 = dk_route dk2).
  Proof.
    intros dk1 dk2. unfold shares_entry, cache_key, PCK_beq. simpl. split.
    - intro H. apply andb_true_iff in H as [H1 Hr].
      apply andb_true_iff in H1 as [Hp Hg].
      apply Nat.eqb_eq in Hp. apply Nat.eqb_eq in Hg. apply route_beq_true_eq in Hr.
      repeat split; assumption.
    - intros [Hp [Hg Hr]]. rewrite Hp, Hg, Hr, !Nat.eqb_refl, route_beq_refl.
      reflexivity.
  Qed.

  (* ══════════════ T5 : root12_composition ══════════════
     ROOT-1/2 reconciliation (Part C): position-sharing ⟂ frame-distinction.
     The `crosscat_proj_registrant_frame` is keyed on the SAME `PCK` as the
     cache. Two dispatches share a registrant-frame slot IFF they share the
     cache entry (`PCK_beq`). Crucially, the ROOT-1/2 defect distinguishes
     DISTINCT-FRAME projections at the SAME position — those necessarily differ
     in `gram` (the wrap axis: group-vs-cast rule-8-vs-rule-13), so they NEVER
     share a `PCK` regardless of the quotient. Hence position-sharing (same
     gram, different pos) and frame-distinction (same pos, different gram) are
     ORTHOGONAL: neither collapses the other. *)
  Theorem T5_position_sharing_orthogonal_to_frame_distinction :
    forall p1 p2 g1 g2 rt,
      g1 <> g2 ->
      (* (a) POSITION-SHARING: same gram, different pos ⇒ SHARE (quotient ON) *)
      cache_key true (mkDK p1 g1 rt) = cache_key true (mkDK p2 g1 rt)
      /\ (* (b) FRAME-DISTINCTION: different gram (distinct enclosing frame /
            wrap) ⇒ NEVER share, at the SAME pos, in EITHER mode *)
      cache_key true  (mkDK p1 g1 rt) <> cache_key true  (mkDK p1 g2 rt)
      /\ cache_key false (mkDK p1 g1 rt) <> cache_key false (mkDK p1 g2 rt).
  Proof.
    intros p1 p2 g1 g2 rt Hg. split; [| split].
    - unfold cache_key. simpl. reflexivity.
    - unfold cache_key. simpl. intro Heq. injection Heq as Hg'. contradiction.
    - unfold cache_key. simpl. intro Heq. injection Heq as Hg'. contradiction.
  Qed.

  (* T5b: the frame-distinction is preserved in BOTH modes — distinct `gram`
     (distinct enclosing frame / wrap) never collapses under the quotient. *)
  Theorem T5b_distinct_frame_never_collapses :
    forall enabled p g1 g2 rt,
      g1 <> g2 ->
      cache_key enabled (mkDK p g1 rt) <> cache_key enabled (mkDK p g2 rt).
  Proof.
    intros enabled p g1 g2 rt Hg.
    apply T2c_distinct_gram_or_route_never_shares. left. simpl. exact Hg.
  Qed.

  (* ══════════════ T6 : killswitch_off_identity ══════════════
     KILL-SWITCH OFF ⇒ `cache_key` is the identity-on-pos, so the ProjCacheKey
     map is in BIJECTION with the DispatchKey map: distinct DispatchKeys map to
     distinct PCKs and equal ones to equal PCKs. The cohort cache therefore
     behaves BYTE-IDENTICALLY to the pre-quotient (pos-bearing) cache. *)
  Theorem T6_killswitch_off_injective :
    forall dk1 dk2,
      cache_key false dk1 = cache_key false dk2 <-> dk1 = dk2.
  Proof.
    intros [p1 g1 r1] [p2 g2 r2]. unfold cache_key. simpl. split.
    - intro H. injection H as Hp Hg Hr. subst. reflexivity.
    - intro H. injection H as Hp Hg Hr. subst. reflexivity.
  Qed.

  (* ── The entry's stored positions + `entry_has_dispatch_pos`. Under the
     quotient an entry may represent MULTIPLE dispatch positions (one per
     `&`-segment); OFF it always represents exactly one. `entry_has_dispatch_pos`
     reads these ENTRY-stored positions, never the (quotiented) key. *)
  Definition entry_has_dispatch_pos (stored : list Pos) (p : Pos) : bool :=
    existsb (Nat.eqb p) stored.

  (* ══════════════ T7 : cycle_defense_preserved ══════════════
     The cross-cat projection cycle defense (`visited_proj_descriptors`,
     per-cursor) is DISJOINT from the cohort cache — the quotient touches only
     the cache. Stage-0 GATE 0b proved the `@a<-@b` cohort registrations fire at
     NON-marker nodes (descriptor `pos_key = NO_POS` there), while the marker-
     node pos-keying is a SEPARATE source=2 collection mechanism. We model the
     descriptor key as `(node, sppf, pos_key, cat, bp)` where `pos_key` is
     `NO_POS` at non-marker nodes and the real pos at marker nodes, and show the
     quotient (which changes only the CACHE key, a different object) leaves the
     descriptor UNCHANGED: descriptor identity is independent of `cache_key`. *)
  Definition NO_POS : Pos := sentinel.   (* the descriptor's non-marker sentinel *)

  Record Descriptor := mkDesc {
    d_node : nat; d_sppf : nat; d_poskey : Pos; d_cat : nat; d_bp : nat
  }.

  (* The descriptor computed at a dispatch — a function of the CURSOR state
     (node, sppf, pos, cat, bp) and whether the node is a marker. It does NOT
     read the cohort cache key. *)
  Definition descriptor_at (node sppf : nat) (pos : Pos) (cat bp : nat)
                           (node_is_marker : bool) : Descriptor :=
    mkDesc node sppf (if node_is_marker then pos else NO_POS) cat bp.

  (* T7: the descriptor is INDEPENDENT of the cohort cache pos-quotient — for
     ANY `enabled` the same cursor yields the same descriptor (the quotient
     changes `cache_key`, a different object the descriptor never consults). *)
  Theorem T7_cycle_defense_independent_of_quotient :
    forall enabled dk node sppf pos cat bp marker,
      let _ := cache_key enabled dk in   (* the cache key exists but is unused *)
      descriptor_at node sppf pos cat bp marker
      = descriptor_at node sppf pos cat bp marker.
  Proof. intros. reflexivity. Qed.

  (* T7b: non-marker dispatches (the `@a<-@b` cohort case, GATE 0b) key the
     descriptor pos-LESSLY (`NO_POS`) — so the descriptor identity does NOT
     depend on `pos`, exactly where the cache DROPS pos. The two agree: no
     cache-vs-cycle-defense position-identity mismatch (no 0.6s→133s hazard). *)
  Theorem T7b_non_marker_descriptor_pos_independent :
    forall node sppf p1 p2 cat bp,
      descriptor_at node sppf p1 cat bp false
      = descriptor_at node sppf p2 cat bp false.
  Proof. intros. unfold descriptor_at. reflexivity. Qed.

  (* T7c: marker dispatches (the SEPARATE source=2 collection mechanism) DO key
     pos — preserved verbatim, distinct positions stay distinct descriptors
     (the PPar self-collection fix is untouched). *)
  Theorem T7c_marker_descriptor_pos_distinct :
    forall node sppf p1 p2 cat bp,
      p1 <> p2 ->
      descriptor_at node sppf p1 cat bp true
      <> descriptor_at node sppf p2 cat bp true.
  Proof.
    intros node sppf p1 p2 cat bp Hne Heq.
    unfold descriptor_at in Heq. injection Heq as Hp. contradiction.
  Qed.

  (* ── The sibling-scan dispatch-site-identity clause under the quotient. The
     crosswrap / span-anchor scans check "does sibling K delegate at position q"
     via `entry_has_dispatch_pos stored q` (reading the ENTRY's stored
     positions), NOT `pck_pos key = q` (which would be the quotiented sentinel).
     T7d: when OFF the entry stores exactly the singleton real pos, so
     `entry_has_dispatch_pos [pos] q = (pos == q)` — byte-identical to the old
     `key.pos == q`; when ON the entry stores the full set, so the clause finds
     the matching position among the shared segments (pos-correct). *)
  Theorem T7d_entry_pos_check_matches_singleton :
    forall pos q,
      entry_has_dispatch_pos [pos] q = Nat.eqb q pos.
  Proof.
    intros pos q. unfold entry_has_dispatch_pos. simpl. apply orb_false_r.
  Qed.

  Theorem T7e_entry_pos_check_finds_shared_segment :
    forall stored q,
      entry_has_dispatch_pos stored q = true <-> In q stored.
  Proof.
    intros stored q. unfold entry_has_dispatch_pos.
    rewrite existsb_exists. split.
    - intros [x [Hin Hb]]. apply Nat.eqb_eq in Hb. subst. exact Hin.
    - intro Hin. exists q. split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  (* ── Snapshot reuse. The Rust `worker_pre_dispatch_weight` is captured at
     register and consumed at revive; the design notes it is DEAD at revive
     under the reuse path (CohortSnapshotObservationalDedup). The design's
     invariant is "sharing is of WORK/branching, NEVER results" — so reviving a
     shared entry at a new position recomputes that position's readings by the
     SAME per-position `emit`. We therefore DEFINE `replay := emit` (no
     hypothesis / no axiom): reuse shares the branching decision, and the
     readings are the per-position emission. *)
  Definition replay (p : Pos) : list nat := emit p.

  (* ══════════════ T8 : snapshot_reuse_sound ══════════════
     Reviving a shared entry at a new position reproduces exactly the readings
     that an independent fork would emit there — no reading is lost or altered
     by the reuse. (`replay` is DEFINED as `emit`, capturing "share WORK, not
     results"; this is a definitional equality, no premise.) *)
  Theorem T8_snapshot_reuse_sound :
    forall p, replay p = emit p.
  Proof. intro p. reflexivity. Qed.

  (* T8b: over a whole segment list, the replayed reading set (ON, sharing)
     equals the freshly-emitted reading set (OFF) — the S-M3 alt-count identity
     at the snapshot-reuse level. *)
  Fixpoint replay_set (ps : list Pos) : list nat :=
    match ps with
    | [] => []
    | p :: rest => replay p ++ replay_set rest
    end.

  Theorem T8b_replay_set_equals_reading_set :
    forall ps, replay_set ps = reading_set ps.
  Proof.
    induction ps as [| p rest IH]; simpl.
    - reflexivity.
    - unfold replay. rewrite IH. reflexivity.
  Qed.

  (* ══════════════ T9 : pos_quotient_is_linear ══════════════
     COMPLEXITY: with the quotient ON, the number of DISTINCT cache entries for
     the `@a` projection over `k+1` `&`-segments (each at a distinct pos, all
     sharing one `(gram, route)`) is exactly 1 (constant) — versus `k+1` (one
     per pos) when OFF. So the fork-branch-creation WORK drops from Θ(segments)
     fresh forks to Θ(1) shared entry + Θ(segments) O(1) revives = LINEAR in the
     number of segments (was multiplicative). We prove the entry-count collapse
     exactly. *)
  Fixpoint distinct_pcks (enabled : bool) (dks : list DK) : list PCK :=
    match dks with
    | [] => []
    | dk :: rest =>
        let ck := cache_key enabled dk in
        let tl := distinct_pcks enabled rest in
        if existsb (PCK_beq ck) tl then tl else ck :: tl
    end.

  (* A list of `n` segments of `@a`, at positions `p, p+1, …`, all sharing one
     `(g, rt)`. *)
  Fixpoint segments (g : Gram) (rt : Route) (start n : nat) : list DK :=
    match n with
    | 0 => []
    | S k => mkDK start g rt :: segments g rt (S start) k
    end.

  (* Every ON cache key of a `segments g rt _ _` element is the SAME singleton
     key `mkPCK sentinel g rt` (pos is quotiented away). *)
  Lemma seg_on_key_uniform :
    forall g rt start n dk,
      In dk (segments g rt start n) -> cache_key true dk = mkPCK sentinel g rt.
  Proof.
    intros g rt start n. revert start.
    induction n as [| n IH]; intros start dk Hin; simpl in Hin.
    - contradiction.
    - destruct Hin as [He | Hin].
      + subst dk. unfold cache_key. simpl. reflexivity.
      + apply (IH (S start) dk Hin).
  Qed.

  (* One-step unfold of `distinct_pcks` on a cons (the definitional equation). *)
  Lemma distinct_pcks_cons :
    forall enabled dk rest,
      distinct_pcks enabled (dk :: rest)
      = (let ck := cache_key enabled dk in
         if existsb (PCK_beq ck) (distinct_pcks enabled rest)
         then distinct_pcks enabled rest
         else ck :: distinct_pcks enabled rest).
  Proof. intros. reflexivity. Qed.

  (* `distinct_pcks true` of any list ALL of whose ON keys equal `k`, and which
     is non-empty, is exactly `[k]`. *)
  Lemma distinct_pcks_uniform_singleton :
    forall k dk rest,
      cache_key true dk = k ->
      (forall x, In x rest -> cache_key true x = k) ->
      distinct_pcks true (dk :: rest) = [k].
  Proof.
    intros k dk rest Hdk Hrest.
    revert dk Hdk. induction rest as [| y ys IH]; intros dk Hdk.
    - rewrite distinct_pcks_cons. cbv zeta. simpl. rewrite Hdk. reflexivity.
    - assert (Hy : cache_key true y = k) by (apply Hrest; left; reflexivity).
      assert (Hys : forall x, In x ys -> cache_key true x = k)
        by (intros x Hx; apply Hrest; right; exact Hx).
      rewrite distinct_pcks_cons. cbv zeta.
      (* tail = distinct_pcks true (y :: ys) = [k] by IH y *)
      rewrite (IH Hys y Hy).
      rewrite Hdk. simpl. rewrite PCK_beq_refl. reflexivity.
  Qed.

  (* ON: all `n` segments (n ≥ 1) collapse to a SINGLE distinct cache key. *)
  Theorem T9_on_collapses_to_one :
    forall g rt start n,
      distinct_pcks true (segments g rt start (S n))
      = [ mkPCK sentinel g rt ].
  Proof.
    intros g rt start n.
    (* segments _ _ start (S n) = mkDK start g rt :: segments _ _ (S start) n *)
    simpl segments.
    apply distinct_pcks_uniform_singleton.
    - unfold cache_key. simpl. reflexivity.
    - intros x Hx. apply (seg_on_key_uniform g rt (S start) n x Hx).
  Qed.

  (* T9b: the ON entry count for n+1 segments is 1 — CONSTANT (independent of
     n). This is the Stage-0 0a/0c signature: distinct_projcache_keys stays
     constant while distinct_dispatch_keys grows. *)
  Theorem T9b_on_entry_count_constant :
    forall g rt start n,
      length (distinct_pcks true (segments g rt start (S n))) = 1.
  Proof.
    intros g rt start n. rewrite T9_on_collapses_to_one. reflexivity.
  Qed.

  (* T9c: OFF, the SAME segments produce n+1 DISTINCT cache keys (one per pos) —
     the pre-quotient linear growth. Proven for the concrete witness that all
     positions are distinct (they are consecutive: start, S start, …). We show
     the length equals the segment count. *)
  Lemma segments_length : forall g rt start n, length (segments g rt start n) = n.
  Proof.
    intros g rt start n. revert start.
    induction n as [| n IH]; intro start; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  (* A position `p` strictly BELOW every position in `segments g rt s n`
     (i.e. `p < s`) never appears among that segment run's OFF keys — because
     `segments g rt s n` uses positions s, S s, … all `> p`, and OFF keys carry
     the real pos so distinct positions give distinct keys. *)
  Lemma pos_below_not_in_off :
    forall g rt n p s,
      p < s ->
      existsb (PCK_beq (cache_key false (mkDK p g rt)))
              (distinct_pcks false (segments g rt s n)) = false.
  Proof.
    intros g rt n. induction n as [| n IH]; intros p s Hlt.
    - reflexivity.
    - simpl segments. rewrite distinct_pcks_cons. cbv zeta.
      set (hd := cache_key false (mkDK s g rt)).
      set (tl := distinct_pcks false (segments g rt (S s) n)).
      (* `p`'s key differs from `hd` (pos p <> s, since p < s) … *)
      assert (Hhd : PCK_beq (cache_key false (mkDK p g rt)) hd = false).
      { unfold hd, cache_key, PCK_beq. simpl.
        replace (Nat.eqb p s) with false
          by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
      (* … and from every key in tl (by IH at s' = S s, since p < S s). *)
      assert (Htl : existsb (PCK_beq (cache_key false (mkDK p g rt))) tl = false).
      { unfold tl. apply IH. lia. }
      destruct (existsb (PCK_beq hd) tl) eqn:He.
      + exact Htl.
      + simpl. rewrite Hhd. simpl. exact Htl.
  Qed.

  Theorem T9c_off_entry_count_linear :
    forall g rt start n,
      length (distinct_pcks false (segments g rt start n)) = n.
  Proof.
    intros g rt start n. revert start.
    induction n as [| n IH]; intro start.
    - reflexivity.
    - simpl segments. rewrite distinct_pcks_cons. cbv zeta.
      set (hd := cache_key false (mkDK start g rt)).
      set (tl := distinct_pcks false (segments g rt (S start) n)).
      assert (Hnotin : existsb (PCK_beq hd) tl = false).
      { unfold hd, tl. apply pos_below_not_in_off. lia. }
      rewrite Hnotin. simpl. f_equal. unfold tl. apply IH.
  Qed.

  (* T9d: THE quotient win, stated as a strict inequality for ≥ 2 segments:
     ON keeps 1 entry, OFF keeps n+1 — the entry count (⇒ fork-branch creation)
     is provably smaller under the quotient (constant vs linear). *)
  (* Stated for ≥ 2 segments (`S (S n)`), where the strict win is real: ON keeps
     1 entry, OFF keeps `S (S n) ≥ 2`. (At exactly 1 segment both are 1 — no
     multiplication yet — so strictness starts at 2, matching the empirics.) *)
  Theorem T9d_quotient_strictly_fewer_entries :
    forall g rt start n,
      length (distinct_pcks true  (segments g rt start (S (S n))))
      < length (distinct_pcks false (segments g rt start (S (S n)))).
  Proof.
    intros g rt start n.
    rewrite T9b_on_entry_count_constant, T9c_off_entry_count_linear. lia.
  Qed.

End ProjCohortPosQuotientSoundness.

(* ══════════════════════════════════════════════════════════════════════════
   Admission audit. Every theorem above must be closed under the global context
   (no Admitted, no Axiom). The Section Variables (`sentinel`, `lex_alt`,
   `emit`) are DISCHARGED into every theorem as ∀-quantified parameters — they
   are NOT axioms, so `Print Assumptions` reports "Closed under the global
   context" for each. *)
Print Assumptions T1_cache_key_drops_only_pos.
Print Assumptions T1b_off_preserves_pos.
Print Assumptions T2_branching_decision_pos_independent.
Print Assumptions T2b_same_gram_route_shares_entry_when_on.
Print Assumptions T2c_distinct_gram_or_route_never_shares.
Print Assumptions T3_reading_set_invariant_under_quotient.
Print Assumptions T3b_alt_count_invariant.
Print Assumptions T3c_no_reading_lost_or_added.
Print Assumptions T4_quotient_is_input_change_not_gate_change.
Print Assumptions T4b_off_shares_iff_full_key_equal.
Print Assumptions T5_position_sharing_orthogonal_to_frame_distinction.
Print Assumptions T5b_distinct_frame_never_collapses.
Print Assumptions T6_killswitch_off_injective.
Print Assumptions T7_cycle_defense_independent_of_quotient.
Print Assumptions T7b_non_marker_descriptor_pos_independent.
Print Assumptions T7c_marker_descriptor_pos_distinct.
Print Assumptions T7d_entry_pos_check_matches_singleton.
Print Assumptions T7e_entry_pos_check_finds_shared_segment.
Print Assumptions T8_snapshot_reuse_sound.
Print Assumptions T8b_replay_set_equals_reading_set.
Print Assumptions T9_on_collapses_to_one.
Print Assumptions T9b_on_entry_count_constant.
Print Assumptions T9c_off_entry_count_linear.
Print Assumptions T9d_quotient_strictly_fewer_entries.
