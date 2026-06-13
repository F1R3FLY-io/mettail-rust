---- MODULE RhoNetScheduler ----
EXTENDS Naturals, Sequences, TLC

\* Generated from formal/process/rho_comm_slice.json.
\* Bounded scheduler model for a finite RhoNet COMM fragment.
\*
\* The COMM redexes are independent. A fair scheduler may fire them
\* in any order; once all are fired, the complete observation must
\* become enabled and, under weak fairness, eventually occur.

VARIABLES
  \* @type: Bool;
  firedA,
  \* @type: Bool;
  firedB,
  \* @type: Bool;
  firedC,
  \* @type: Bool;
  completed,
  \* @type: Str;
  trace

vars == <<firedA, firedB, firedC, completed, trace>>

ValidTraces ==
  {"Empty",
   "A",
   "B",
   "C",
   "AB",
   "AC",
   "BA",
   "BC",
   "CA",
   "CB",
   "ABC",
   "ACB",
   "BAC",
   "BCA",
   "CAB",
   "CBA",
   "ABCQ",
   "ACBQ",
   "BACQ",
   "BCAQ",
   "CABQ",
   "CBAQ"}

TraceHasA(t) ==
  t \in {"A",
   "AB",
   "AC",
   "BA",
   "CA",
   "ABC",
   "ACB",
   "BAC",
   "BCA",
   "CAB",
   "CBA",
   "ABCQ",
   "ACBQ",
   "BACQ",
   "BCAQ",
   "CABQ",
   "CBAQ"}

TraceHasB(t) ==
  t \in {"B",
   "AB",
   "BA",
   "BC",
   "CB",
   "ABC",
   "ACB",
   "BAC",
   "BCA",
   "CAB",
   "CBA",
   "ABCQ",
   "ACBQ",
   "BACQ",
   "BCAQ",
   "CABQ",
   "CBAQ"}

TraceHasC(t) ==
  t \in {"C",
   "AC",
   "BC",
   "CA",
   "CB",
   "ABC",
   "ACB",
   "BAC",
   "BCA",
   "CAB",
   "CBA",
   "ABCQ",
   "ACBQ",
   "BACQ",
   "BCAQ",
   "CABQ",
   "CBAQ"}

TraceHasQ(t) ==
  t \in {"ABCQ",
   "ACBQ",
   "BACQ",
   "BCAQ",
   "CABQ",
   "CBAQ"}

AppendA(t) ==
  IF t = "Empty" THEN "A"
  ELSE IF t = "B" THEN "BA"
  ELSE IF t = "C" THEN "CA"
  ELSE IF t = "BC" THEN "BCA"
  ELSE IF t = "CB" THEN "CBA"
  ELSE "CBA"

AppendB(t) ==
  IF t = "Empty" THEN "B"
  ELSE IF t = "A" THEN "AB"
  ELSE IF t = "C" THEN "CB"
  ELSE IF t = "AC" THEN "ACB"
  ELSE IF t = "CA" THEN "CAB"
  ELSE "CAB"

AppendC(t) ==
  IF t = "Empty" THEN "C"
  ELSE IF t = "A" THEN "AC"
  ELSE IF t = "B" THEN "BC"
  ELSE IF t = "AB" THEN "ABC"
  ELSE IF t = "BA" THEN "BAC"
  ELSE "BAC"

AppendQ(t) ==
  IF t = "ABC" THEN "ABCQ"
  ELSE IF t = "ACB" THEN "ACBQ"
  ELSE IF t = "BAC" THEN "BACQ"
  ELSE IF t = "BCA" THEN "BCAQ"
  ELSE IF t = "CAB" THEN "CABQ"
  ELSE IF t = "CBA" THEN "CBAQ"
  ELSE "CBAQ"

Init ==
  /\ firedA = FALSE
  /\ firedB = FALSE
  /\ firedC = FALSE
  /\ completed = FALSE
  /\ trace = "Empty"

FireA ==
  /\ ~firedA
  /\ ~completed
  /\ firedA' = TRUE
  /\ firedB' = firedB
  /\ firedC' = firedC
  /\ completed' = FALSE
  /\ trace' = AppendA(trace)

FireB ==
  /\ ~firedB
  /\ ~completed
  /\ firedA' = firedA
  /\ firedB' = TRUE
  /\ firedC' = firedC
  /\ completed' = FALSE
  /\ trace' = AppendB(trace)

FireC ==
  /\ ~firedC
  /\ ~completed
  /\ firedA' = firedA
  /\ firedB' = firedB
  /\ firedC' = TRUE
  /\ completed' = FALSE
  /\ trace' = AppendC(trace)

Complete ==
  /\ firedA
  /\ firedB
  /\ firedC
  /\ ~completed
  /\ firedA' = firedA
  /\ firedB' = firedB
  /\ firedC' = firedC
  /\ completed' = TRUE
  /\ trace' = AppendQ(trace)

Done ==
  /\ completed
  /\ UNCHANGED vars

Next == FireA \/ FireB \/ FireC \/ Complete \/ Done

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(FireA)
  /\ WF_vars(FireB)
  /\ WF_vars(FireC)
  /\ WF_vars(Complete)

TypeOK ==
  /\ firedA \in BOOLEAN
  /\ firedB \in BOOLEAN
  /\ firedC \in BOOLEAN
  /\ completed \in BOOLEAN
  /\ trace \in ValidTraces

CompleteOnlyAfterInputs ==
  completed => firedA /\ firedB /\ firedC

TraceMatchesState ==
  /\ firedA <=> TraceHasA(trace)
  /\ firedB <=> TraceHasB(trace)
  /\ firedC <=> TraceHasC(trace)
  /\ completed <=> TraceHasQ(trace)

NoPrematureCompletion ==
  completed => trace \in {"ABCQ", "ACBQ", "BACQ", "BCAQ", "CABQ", "CBAQ"}

AllInputsEnableCompletion ==
  firedA /\ firedB /\ firedC /\ ~completed => ENABLED Complete

EventuallyComplete == <>completed

====
