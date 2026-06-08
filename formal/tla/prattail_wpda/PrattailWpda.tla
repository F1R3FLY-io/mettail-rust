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

States == {"Chain", "Delegate", "Unwind", "Done"}
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

InitialFull ==
  CASE Scenario = "CohortQuotient" -> CohortInitial
    [] Scenario = "ChainAbsorb" -> ChainInitial
    [] Scenario = "CrossCat" -> CrossCatInitial
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

Spec == Init /\ [][Next]_vars

====
