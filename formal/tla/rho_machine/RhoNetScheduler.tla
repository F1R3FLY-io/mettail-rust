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
  firedD,
  \* @type: Bool;
  completed,
  \* @type: Str;
  trace

vars == <<firedA, firedB, firedC, firedD, completed, trace>>

ValidTraces ==
  {"Empty",
   "A",
   "B",
   "C",
   "D",
   "AB",
   "AC",
   "AD",
   "BA",
   "BC",
   "BD",
   "CA",
   "CB",
   "CD",
   "DA",
   "DB",
   "DC",
   "ABC",
   "ABD",
   "ACB",
   "ACD",
   "ADB",
   "ADC",
   "BAC",
   "BAD",
   "BCA",
   "BCD",
   "BDA",
   "BDC",
   "CAB",
   "CAD",
   "CBA",
   "CBD",
   "CDA",
   "CDB",
   "DAB",
   "DAC",
   "DBA",
   "DBC",
   "DCA",
   "DCB",
   "ABCD",
   "ABDC",
   "ACBD",
   "ACDB",
   "ADBC",
   "ADCB",
   "BACD",
   "BADC",
   "BCAD",
   "BCDA",
   "BDAC",
   "BDCA",
   "CABD",
   "CADB",
   "CBAD",
   "CBDA",
   "CDAB",
   "CDBA",
   "DABC",
   "DACB",
   "DBAC",
   "DBCA",
   "DCAB",
   "DCBA",
   "ABCDQ",
   "ABDCQ",
   "ACBDQ",
   "ACDBQ",
   "ADBCQ",
   "ADCBQ",
   "BACDQ",
   "BADCQ",
   "BCADQ",
   "BCDAQ",
   "BDACQ",
   "BDCAQ",
   "CABDQ",
   "CADBQ",
   "CBADQ",
   "CBDAQ",
   "CDABQ",
   "CDBAQ",
   "DABCQ",
   "DACBQ",
   "DBACQ",
   "DBCAQ",
   "DCABQ",
   "DCBAQ"}

TraceHasA(t) ==
  t \in {"A",
   "AB",
   "AC",
   "AD",
   "BA",
   "CA",
   "DA",
   "ABC",
   "ABD",
   "ACB",
   "ACD",
   "ADB",
   "ADC",
   "BAC",
   "BAD",
   "BCA",
   "BDA",
   "CAB",
   "CAD",
   "CBA",
   "CDA",
   "DAB",
   "DAC",
   "DBA",
   "DCA",
   "ABCD",
   "ABDC",
   "ACBD",
   "ACDB",
   "ADBC",
   "ADCB",
   "BACD",
   "BADC",
   "BCAD",
   "BCDA",
   "BDAC",
   "BDCA",
   "CABD",
   "CADB",
   "CBAD",
   "CBDA",
   "CDAB",
   "CDBA",
   "DABC",
   "DACB",
   "DBAC",
   "DBCA",
   "DCAB",
   "DCBA",
   "ABCDQ",
   "ABDCQ",
   "ACBDQ",
   "ACDBQ",
   "ADBCQ",
   "ADCBQ",
   "BACDQ",
   "BADCQ",
   "BCADQ",
   "BCDAQ",
   "BDACQ",
   "BDCAQ",
   "CABDQ",
   "CADBQ",
   "CBADQ",
   "CBDAQ",
   "CDABQ",
   "CDBAQ",
   "DABCQ",
   "DACBQ",
   "DBACQ",
   "DBCAQ",
   "DCABQ",
   "DCBAQ"}

TraceHasB(t) ==
  t \in {"B",
   "AB",
   "BA",
   "BC",
   "BD",
   "CB",
   "DB",
   "ABC",
   "ABD",
   "ACB",
   "ADB",
   "BAC",
   "BAD",
   "BCA",
   "BCD",
   "BDA",
   "BDC",
   "CAB",
   "CBA",
   "CBD",
   "CDB",
   "DAB",
   "DBA",
   "DBC",
   "DCB",
   "ABCD",
   "ABDC",
   "ACBD",
   "ACDB",
   "ADBC",
   "ADCB",
   "BACD",
   "BADC",
   "BCAD",
   "BCDA",
   "BDAC",
   "BDCA",
   "CABD",
   "CADB",
   "CBAD",
   "CBDA",
   "CDAB",
   "CDBA",
   "DABC",
   "DACB",
   "DBAC",
   "DBCA",
   "DCAB",
   "DCBA",
   "ABCDQ",
   "ABDCQ",
   "ACBDQ",
   "ACDBQ",
   "ADBCQ",
   "ADCBQ",
   "BACDQ",
   "BADCQ",
   "BCADQ",
   "BCDAQ",
   "BDACQ",
   "BDCAQ",
   "CABDQ",
   "CADBQ",
   "CBADQ",
   "CBDAQ",
   "CDABQ",
   "CDBAQ",
   "DABCQ",
   "DACBQ",
   "DBACQ",
   "DBCAQ",
   "DCABQ",
   "DCBAQ"}

TraceHasC(t) ==
  t \in {"C",
   "AC",
   "BC",
   "CA",
   "CB",
   "CD",
   "DC",
   "ABC",
   "ACB",
   "ACD",
   "ADC",
   "BAC",
   "BCA",
   "BCD",
   "BDC",
   "CAB",
   "CAD",
   "CBA",
   "CBD",
   "CDA",
   "CDB",
   "DAC",
   "DBC",
   "DCA",
   "DCB",
   "ABCD",
   "ABDC",
   "ACBD",
   "ACDB",
   "ADBC",
   "ADCB",
   "BACD",
   "BADC",
   "BCAD",
   "BCDA",
   "BDAC",
   "BDCA",
   "CABD",
   "CADB",
   "CBAD",
   "CBDA",
   "CDAB",
   "CDBA",
   "DABC",
   "DACB",
   "DBAC",
   "DBCA",
   "DCAB",
   "DCBA",
   "ABCDQ",
   "ABDCQ",
   "ACBDQ",
   "ACDBQ",
   "ADBCQ",
   "ADCBQ",
   "BACDQ",
   "BADCQ",
   "BCADQ",
   "BCDAQ",
   "BDACQ",
   "BDCAQ",
   "CABDQ",
   "CADBQ",
   "CBADQ",
   "CBDAQ",
   "CDABQ",
   "CDBAQ",
   "DABCQ",
   "DACBQ",
   "DBACQ",
   "DBCAQ",
   "DCABQ",
   "DCBAQ"}

TraceHasD(t) ==
  t \in {"D",
   "AD",
   "BD",
   "CD",
   "DA",
   "DB",
   "DC",
   "ABD",
   "ACD",
   "ADB",
   "ADC",
   "BAD",
   "BCD",
   "BDA",
   "BDC",
   "CAD",
   "CBD",
   "CDA",
   "CDB",
   "DAB",
   "DAC",
   "DBA",
   "DBC",
   "DCA",
   "DCB",
   "ABCD",
   "ABDC",
   "ACBD",
   "ACDB",
   "ADBC",
   "ADCB",
   "BACD",
   "BADC",
   "BCAD",
   "BCDA",
   "BDAC",
   "BDCA",
   "CABD",
   "CADB",
   "CBAD",
   "CBDA",
   "CDAB",
   "CDBA",
   "DABC",
   "DACB",
   "DBAC",
   "DBCA",
   "DCAB",
   "DCBA",
   "ABCDQ",
   "ABDCQ",
   "ACBDQ",
   "ACDBQ",
   "ADBCQ",
   "ADCBQ",
   "BACDQ",
   "BADCQ",
   "BCADQ",
   "BCDAQ",
   "BDACQ",
   "BDCAQ",
   "CABDQ",
   "CADBQ",
   "CBADQ",
   "CBDAQ",
   "CDABQ",
   "CDBAQ",
   "DABCQ",
   "DACBQ",
   "DBACQ",
   "DBCAQ",
   "DCABQ",
   "DCBAQ"}

TraceHasQ(t) ==
  t \in {"ABCDQ",
   "ABDCQ",
   "ACBDQ",
   "ACDBQ",
   "ADBCQ",
   "ADCBQ",
   "BACDQ",
   "BADCQ",
   "BCADQ",
   "BCDAQ",
   "BDACQ",
   "BDCAQ",
   "CABDQ",
   "CADBQ",
   "CBADQ",
   "CBDAQ",
   "CDABQ",
   "CDBAQ",
   "DABCQ",
   "DACBQ",
   "DBACQ",
   "DBCAQ",
   "DCABQ",
   "DCBAQ"}

AppendA(t) ==
  IF t = "Empty" THEN "A"
  ELSE IF t = "B" THEN "BA"
  ELSE IF t = "C" THEN "CA"
  ELSE IF t = "D" THEN "DA"
  ELSE IF t = "BC" THEN "BCA"
  ELSE IF t = "BD" THEN "BDA"
  ELSE IF t = "CB" THEN "CBA"
  ELSE IF t = "CD" THEN "CDA"
  ELSE IF t = "DB" THEN "DBA"
  ELSE IF t = "DC" THEN "DCA"
  ELSE IF t = "BCD" THEN "BCDA"
  ELSE IF t = "BDC" THEN "BDCA"
  ELSE IF t = "CBD" THEN "CBDA"
  ELSE IF t = "CDB" THEN "CDBA"
  ELSE IF t = "DBC" THEN "DBCA"
  ELSE IF t = "DCB" THEN "DCBA"
  ELSE "DCBA"

AppendB(t) ==
  IF t = "Empty" THEN "B"
  ELSE IF t = "A" THEN "AB"
  ELSE IF t = "C" THEN "CB"
  ELSE IF t = "D" THEN "DB"
  ELSE IF t = "AC" THEN "ACB"
  ELSE IF t = "AD" THEN "ADB"
  ELSE IF t = "CA" THEN "CAB"
  ELSE IF t = "CD" THEN "CDB"
  ELSE IF t = "DA" THEN "DAB"
  ELSE IF t = "DC" THEN "DCB"
  ELSE IF t = "ACD" THEN "ACDB"
  ELSE IF t = "ADC" THEN "ADCB"
  ELSE IF t = "CAD" THEN "CADB"
  ELSE IF t = "CDA" THEN "CDAB"
  ELSE IF t = "DAC" THEN "DACB"
  ELSE IF t = "DCA" THEN "DCAB"
  ELSE "DCAB"

AppendC(t) ==
  IF t = "Empty" THEN "C"
  ELSE IF t = "A" THEN "AC"
  ELSE IF t = "B" THEN "BC"
  ELSE IF t = "D" THEN "DC"
  ELSE IF t = "AB" THEN "ABC"
  ELSE IF t = "AD" THEN "ADC"
  ELSE IF t = "BA" THEN "BAC"
  ELSE IF t = "BD" THEN "BDC"
  ELSE IF t = "DA" THEN "DAC"
  ELSE IF t = "DB" THEN "DBC"
  ELSE IF t = "ABD" THEN "ABDC"
  ELSE IF t = "ADB" THEN "ADBC"
  ELSE IF t = "BAD" THEN "BADC"
  ELSE IF t = "BDA" THEN "BDAC"
  ELSE IF t = "DAB" THEN "DABC"
  ELSE IF t = "DBA" THEN "DBAC"
  ELSE "DBAC"

AppendD(t) ==
  IF t = "Empty" THEN "D"
  ELSE IF t = "A" THEN "AD"
  ELSE IF t = "B" THEN "BD"
  ELSE IF t = "C" THEN "CD"
  ELSE IF t = "AB" THEN "ABD"
  ELSE IF t = "AC" THEN "ACD"
  ELSE IF t = "BA" THEN "BAD"
  ELSE IF t = "BC" THEN "BCD"
  ELSE IF t = "CA" THEN "CAD"
  ELSE IF t = "CB" THEN "CBD"
  ELSE IF t = "ABC" THEN "ABCD"
  ELSE IF t = "ACB" THEN "ACBD"
  ELSE IF t = "BAC" THEN "BACD"
  ELSE IF t = "BCA" THEN "BCAD"
  ELSE IF t = "CAB" THEN "CABD"
  ELSE IF t = "CBA" THEN "CBAD"
  ELSE "CBAD"

AppendQ(t) ==
  IF t = "ABCD" THEN "ABCDQ"
  ELSE IF t = "ABDC" THEN "ABDCQ"
  ELSE IF t = "ACBD" THEN "ACBDQ"
  ELSE IF t = "ACDB" THEN "ACDBQ"
  ELSE IF t = "ADBC" THEN "ADBCQ"
  ELSE IF t = "ADCB" THEN "ADCBQ"
  ELSE IF t = "BACD" THEN "BACDQ"
  ELSE IF t = "BADC" THEN "BADCQ"
  ELSE IF t = "BCAD" THEN "BCADQ"
  ELSE IF t = "BCDA" THEN "BCDAQ"
  ELSE IF t = "BDAC" THEN "BDACQ"
  ELSE IF t = "BDCA" THEN "BDCAQ"
  ELSE IF t = "CABD" THEN "CABDQ"
  ELSE IF t = "CADB" THEN "CADBQ"
  ELSE IF t = "CBAD" THEN "CBADQ"
  ELSE IF t = "CBDA" THEN "CBDAQ"
  ELSE IF t = "CDAB" THEN "CDABQ"
  ELSE IF t = "CDBA" THEN "CDBAQ"
  ELSE IF t = "DABC" THEN "DABCQ"
  ELSE IF t = "DACB" THEN "DACBQ"
  ELSE IF t = "DBAC" THEN "DBACQ"
  ELSE IF t = "DBCA" THEN "DBCAQ"
  ELSE IF t = "DCAB" THEN "DCABQ"
  ELSE IF t = "DCBA" THEN "DCBAQ"
  ELSE "DCBAQ"

Init ==
  /\ firedA = FALSE
  /\ firedB = FALSE
  /\ firedC = FALSE
  /\ firedD = FALSE
  /\ completed = FALSE
  /\ trace = "Empty"

FireA ==
  /\ ~firedA
  /\ ~completed
  /\ firedA' = TRUE
  /\ firedB' = firedB
  /\ firedC' = firedC
  /\ firedD' = firedD
  /\ completed' = FALSE
  /\ trace' = AppendA(trace)

FireB ==
  /\ ~firedB
  /\ ~completed
  /\ firedA' = firedA
  /\ firedB' = TRUE
  /\ firedC' = firedC
  /\ firedD' = firedD
  /\ completed' = FALSE
  /\ trace' = AppendB(trace)

FireC ==
  /\ ~firedC
  /\ ~completed
  /\ firedA' = firedA
  /\ firedB' = firedB
  /\ firedC' = TRUE
  /\ firedD' = firedD
  /\ completed' = FALSE
  /\ trace' = AppendC(trace)

FireD ==
  /\ ~firedD
  /\ ~completed
  /\ firedA' = firedA
  /\ firedB' = firedB
  /\ firedC' = firedC
  /\ firedD' = TRUE
  /\ completed' = FALSE
  /\ trace' = AppendD(trace)

Complete ==
  /\ firedA
  /\ firedB
  /\ firedC
  /\ firedD
  /\ ~completed
  /\ firedA' = firedA
  /\ firedB' = firedB
  /\ firedC' = firedC
  /\ firedD' = firedD
  /\ completed' = TRUE
  /\ trace' = AppendQ(trace)

Done ==
  /\ completed
  /\ UNCHANGED vars

Next == FireA \/ FireB \/ FireC \/ FireD \/ Complete \/ Done

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(FireA)
  /\ WF_vars(FireB)
  /\ WF_vars(FireC)
  /\ WF_vars(FireD)
  /\ WF_vars(Complete)

TypeOK ==
  /\ firedA \in BOOLEAN
  /\ firedB \in BOOLEAN
  /\ firedC \in BOOLEAN
  /\ firedD \in BOOLEAN
  /\ completed \in BOOLEAN
  /\ trace \in ValidTraces

CompleteOnlyAfterInputs ==
  completed => firedA /\ firedB /\ firedC /\ firedD

TraceMatchesState ==
  /\ firedA <=> TraceHasA(trace)
  /\ firedB <=> TraceHasB(trace)
  /\ firedC <=> TraceHasC(trace)
  /\ firedD <=> TraceHasD(trace)
  /\ completed <=> TraceHasQ(trace)

NoPrematureCompletion ==
  completed => trace \in {"ABCDQ", "ABDCQ", "ACBDQ", "ACDBQ", "ADBCQ", "ADCBQ", "BACDQ", "BADCQ", "BCADQ", "BCDAQ", "BDACQ", "BDCAQ", "CABDQ", "CADBQ", "CBADQ", "CBDAQ", "CDABQ", "CDBAQ", "DABCQ", "DACBQ", "DBACQ", "DBCAQ", "DCABQ", "DCBAQ"}

AllInputsEnableCompletion ==
  firedA /\ firedB /\ firedC /\ firedD /\ ~completed => ENABLED Complete

EventuallyComplete == <>completed

====
