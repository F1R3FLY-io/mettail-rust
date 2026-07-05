---- MODULE PrattailWpda ----
EXTENDS Naturals, FiniteSets, TLC

\* A small executable abstraction of the active Prattail WPDA runtime.
\* It is intentionally finite: the purpose is to find quotienting and
\* chain-absorption counterexamples against the Rocq proof model.

CONSTANTS
  \* @type: Str;
  Scenario,
  \* @type: Bool;
  WrapObservable

VARIABLES
  \* @type: Set([state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool]);
  full,
  \* @type: Set([state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool]);
  quot,
  \* @type: Int;
  phase

vars == <<full, quot, phase>>

States == {"Chain", "Delegate", "Unwind", "Done", "Collection"}
Positions == 0..3
Sources == {0, 1}
Bps == {0, 1}
Wraps == {0, 1}
Sppfs == {0, 1}
WrapDomain == IF WrapObservable THEN Wraps ELSE {0}

Cursor ==
  [ state: States,
    pos: Positions,
    source: Sources,
    bp: Bps,
    wrap: Wraps,
    sppf: Sppfs,
    absorbed: BOOLEAN ]

Config ==
  [ state: States,
    pos: Positions,
    source: Sources,
    bp: Bps,
    wrap: WrapDomain,
    sppf: Sppfs,
    absorbed: BOOLEAN ]

\* @type: [state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool] => Int;
WrapKey(c) == IF WrapObservable THEN c.wrap ELSE 0

\* @type: [state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool] => [state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool];
ConfigOf(c) ==
  [ state |-> c.state,
    pos |-> c.pos,
    source |-> c.source,
    bp |-> c.bp,
    wrap |-> WrapKey(c),
    sppf |-> c.sppf,
    absorbed |-> c.absorbed ]

\* @type: Set([state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool]) => Set([state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool]);
ConfigSet(S) == { ConfigOf(c) : c \in S }

\* @type: [state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool] => [source: Int, bp: Int];
EquivOf(c) == [ source |-> c.source, bp |-> c.bp ]

\* @type: [state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool] => [source: Int, bp: Int, wrap: Int];
EdgeKindOf(c) == [ source |-> c.source, bp |-> c.bp, wrap |-> c.wrap ]

\* @type: ([state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool], [state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool]) => Bool;
EdgeKindEquivalent(c1, c2) == EdgeKindOf(c1) = EdgeKindOf(c2)

CohortInitial ==
  { [ state |-> "Delegate",
      pos |-> 0,
      source |-> 0,
      bp |-> 0,
      wrap |-> w,
      sppf |-> 0,
      absorbed |-> FALSE ] : w \in Wraps }

ChainInitial ==
  { [ state |-> "Chain",
      pos |-> 1,
      source |-> 0,
      bp |-> 0,
      wrap |-> 0,
      sppf |-> 0,
      absorbed |-> FALSE ] }

CrossCatInitial ==
  { [ state |-> "Delegate",
      pos |-> 0,
      source |-> s,
      bp |-> b,
      wrap |-> w,
      sppf |-> 0,
      absorbed |-> FALSE ] : s \in Sources, b \in Bps, w \in Wraps }

\* ROOT-A — the shared-open `{` prefix-dispatch fork. At the open `{` the
\* codegen forks ONE content into two lineages:
\*   source = 0 — the PPar (braced-parallel `{P|Q}`) collection marker lineage;
\*   source = 1 — the Map cross-cat projection lineage (`{k:v}`).
\* The CONTENT's decisive post-element token is encoded by `bp`:
\*   bp = 0  ⟺  the decisive token is `|`  (the valid parse is PPar, source 0);
\*   bp = 1  ⟺  the decisive token is `:`  (the valid parse is Map,  source 1).
\* Both polarities of content are placed in the initial frontier, so the model
\* checks BOTH `{P|Q}` and `{k:v}` simultaneously. A lineage SURVIVES the
\* decisive token iff `source = bp`; the mismatched lineage is dropped from the
\* frontier (the runtime kills a dead cursor). This is the +1-cursor fork.
\* ROOT-B (2026-06-27): the `{|`-delegate lineage. A multi-char, lex-ambiguous
\* collection open (`{|` len 2 vs `{` len 1) reaches the prefix dispatch INSIDE a
\* CrossCatDelegate committed to its source category. `wrap = 1` marks this
\* source-committed delegate lineage (distinct, hence WrapObservable = TRUE in
\* CollectionFork.cfg); `sppf = 1` marks that it ENTERED the source collection
\* cat (rather than re-projecting across numeric cats — the SnapshotDuplicate
\* storm). Pre-fix the delegate would resolve with sppf = 0 (never interning the
\* source cat); the ROOT-B fix makes it enter (sppf := 1), pinned by the
\* DelegateEntersSourceCat invariant.
CollectionForkInitial ==
  { [ state |-> "Collection",
      pos |-> 0,
      source |-> s,
      bp |-> b,
      wrap |-> 0,
      sppf |-> 0,
      absorbed |-> FALSE ] : s \in Sources, b \in Bps }
  \cup
  { [ state |-> "Collection",
      pos |-> 0,
      source |-> 0,
      bp |-> 0,
      wrap |-> 1,
      sppf |-> 0,
      absorbed |-> FALSE ] }

\* ROOT B+C unified Fix A — the BUG WITNESS model (cohort broadcast). The CURRENT
\* cohort revive BROADCASTS the worker's return frame to every parked Fork
\* projection survivor. A binder-frame survivor (content b = 1) is therefore
\* reconciled against the WORKER's frame (source = 0) instead of its OWN
\* (source = 1), so the `source = bp` resolution drops it — its valid parse is
\* LOST. Encoded purely in the initial frame: the survivor's `source` is the
\* worker's frame 0 (the broadcast), not its content bp = 1. Re-uses the existing
\* Collection step logic (no NextCursor change). The matching FIXED model is the
\* CollectionFork scenario, where survivors carry their OWN frame (source = bp)
\* and reconcile. `BinderForkBroadcastExpectedFail.cfg` runs this and MUST
\* violate NoValidParseLost (FV: ForkSurvivorBinderPop.current_broadcast_drops_matching_rule).
BinderForkBroadcastInitial ==
  { [ state |-> "Collection", pos |-> 0, source |-> 0, bp |-> 0,
      wrap |-> 0, sppf |-> 0, absorbed |-> FALSE ],
    [ state |-> "Collection", pos |-> 0, source |-> 0, bp |-> 1,
      wrap |-> 0, sppf |-> 0, absorbed |-> FALSE ] }

InitialFull ==
  CASE Scenario = "CohortQuotient" -> CohortInitial
    [] Scenario = "ChainAbsorb" -> ChainInitial
    [] Scenario = "CrossCat" -> CrossCatInitial
    [] Scenario = "CollectionFork" -> CollectionForkInitial
    [] Scenario = "BinderForkBroadcast" -> BinderForkBroadcastInitial
    [] OTHER -> CohortInitial

\* @type: [state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool] => Set([state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool]);
NextCursor(c) ==
  CASE c.state = "Chain" ->
        { [c EXCEPT !.state = "Unwind",
                   !.pos = 3,
                   !.absorbed = TRUE] }
    [] c.state = "Delegate" ->
        IF c.absorbed THEN
          { [c EXCEPT !.state = "Unwind"] }
        ELSE IF c.pos < 3 THEN
          { [c EXCEPT !.state = "Unwind",
                     !.pos = c.pos + 1,
                     !.sppf = s] : s \in Sppfs }
        ELSE
          { [c EXCEPT !.state = "Done"] }
    [] c.state = "Unwind" ->
        { [c EXCEPT !.state = "Done"] }
    [] c.state = "Collection" ->
        IF c.wrap = 1 THEN
          \* ROOT-B: source-committed multi-length delegate ENTERS its source
          \* collection cat (sppf := 1 marks entry), never re-projecting.
          { [c EXCEPT !.state = "Done", !.sppf = 1] }
        \* ROOT-A fork resolution: the decisive token (`bp`) selects exactly
        \* one lineage. `source = bp` ⇒ the lineage matches the content and
        \* finalizes (Done = accept); otherwise the lineage is dropped (the
        \* empty set removes the dead cursor from the frontier).
        ELSE IF c.source = c.bp THEN
          { [c EXCEPT !.state = "Done"] }
        ELSE
          { }
    [] OTHER ->
        { c }

\* @type: Set([state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool]) => Set([state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool]);
StepFull(S) == UNION { NextCursor(c) : c \in S }

\* @type: [state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool] => Set([state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool]);
NextConfig(k) ==
  CASE k.state = "Chain" ->
        { [k EXCEPT !.state = "Unwind",
                   !.pos = 3,
                   !.absorbed = TRUE] }
    [] k.state = "Delegate" ->
        IF k.absorbed THEN
          { [k EXCEPT !.state = "Unwind"] }
        ELSE IF k.pos < 3 THEN
          { [k EXCEPT !.state = "Unwind",
                     !.pos = k.pos + 1,
                     !.sppf = s] : s \in Sppfs }
        ELSE
          { [k EXCEPT !.state = "Done"] }
    [] k.state = "Unwind" ->
        { [k EXCEPT !.state = "Done"] }
    [] k.state = "Collection" ->
        \* Quotient stepper mirrors NextCursor's ROOT-A/ROOT-B resolution so the
        \* quotient stays observationally equal to the full frontier.
        IF k.wrap = 1 THEN
          { [k EXCEPT !.state = "Done", !.sppf = 1] }
        ELSE IF k.source = k.bp THEN
          { [k EXCEPT !.state = "Done"] }
        ELSE
          { }
    [] OTHER ->
        { k }

\* @type: Set([state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool]) => Set([state: Str, pos: Int, source: Int, bp: Int, wrap: Int, sppf: Int, absorbed: Bool]);
StepQuot(Q) == UNION { NextConfig(k) : k \in Q }

Init ==
  /\ phase = 0
  /\ full = InitialFull
  /\ quot = ConfigSet(InitialFull)

Next ==
  \/ /\ phase < 4
     /\ full' = StepFull(full)
     /\ quot' = StepQuot(quot)
     /\ phase' = phase + 1
  \/ /\ phase = 4
     /\ UNCHANGED vars

TypeOK ==
  /\ full \in SUBSET Cursor
  /\ quot \in SUBSET Config
  /\ phase \in 0..4

QuotientSound == quot = ConfigSet(full)

QuotientBound == Cardinality(quot) <= Cardinality(full)

NarrowCohortQuotientSafe ==
  \A c1, c2 \in full :
    /\ c1.state = c2.state
    /\ c1.pos = c2.pos
    /\ EquivOf(c1) = EquivOf(c2)
    /\ c1.sppf = c2.sppf
    /\ c1.absorbed = c2.absorbed
    => ConfigOf(c1) = ConfigOf(c2)

NoDelegateInsideAbsorbed ==
  \A c \in full : c.absorbed => c.state # "Delegate"

CrossCatProgress ==
  \A c \in full : c.state = "Delegate" => c.pos < 3

EdgeKindPreservesWrap ==
  \A c1, c2 \in full :
    EdgeKindEquivalent(c1, c2) => c1.wrap = c2.wrap

\* ── ROOT-A CollectionFork invariants ──

\* NO VALID PARSE LOST: once the fork has fully resolved (phase = 4), EVERY
\* content `b` still has its VALID lineage (source = b) accepting (Done). This
\* is the soundness obligation the defect violated: `{1:2}` (bp = 1) lost its
\* Map lineage because the braced PPar arm committed before the projection was
\* tried. With the fork, the matching lineage always survives to accept.
NoValidParseLost ==
  (phase = 4) =>
    \A b \in Bps : \E c \in full : c.state = "Done" /\ c.bp = b /\ c.source = b

\* AT MOST ONE ACCEPT PER CONTENT: for any single content (same `bp`), at most
\* one lineage ever reaches an accepting (Done) state — the decisive token kills
\* the other lineage, so a content never yields two competing accepts.
AtMostOneAcceptPerContent ==
  \A c1, c2 \in full :
    (c1.state = "Done" /\ c2.state = "Done" /\ c1.bp = c2.bp)
      => c1.source = c2.source

\* NO SNAPSHOT EXPLOSION: the quotient never exceeds the full frontier
\* (QuotientBound) AND the frontier itself stays bounded (the fork adds at most
\* one lineage per content — never a frontier blow-up). The shared-open `{`
\* defect history is precisely green-tested fixes that masked frontier
\* explosions; this invariant pins the cardinality.
NoSnapshotExplosion ==
  QuotientBound /\ Cardinality(full) <= 5

\* ROOT-B: a source-committed `{|`-delegate lineage (wrap = 1), once resolved,
\* has ENTERED its source collection cat (sppf = 1) — it never finalizes without
\* interning the source cat (the pre-fix re-projection / SnapshotDuplicate storm
\* would leave it sppf = 0). This is the DelegateEntersSourceCat obligation that
\* CollectionDelegateDispatch.v `delegate_enters_source_collection` discharges at
\* the codegen level.
DelegateEntersSourceCat ==
  \A c \in full : (c.wrap = 1 /\ c.state = "Done") => c.sppf = 1

Spec == Init /\ [][Next]_vars

====
