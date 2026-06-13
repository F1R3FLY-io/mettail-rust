---- MODULE RhoPurseSettlement ----
EXTENDS Naturals, TLC

\* Bounded TLA+ model for M-RHO.3 per-purse settlement determinism.
\*
\* Two reserve actions target distinct purses. TLC explores both schedules and
\* checks that the final ledger is independent of scheduler order. Duplicate
\* and missing-purse rejects are explicit fail-closed stuttering actions.

CONSTANTS P0, P1

Purses == {P0, P1}

VARIABLES
  available,
  escrowed,
  charged,
  firedLeft,
  firedRight,
  duplicateRejected,
  missingRejected

vars ==
  <<available, escrowed, charged, firedLeft, firedRight,
    duplicateRejected, missingRejected>>

InitialAvailable ==
  [p \in Purses |-> IF p = P0 THEN 10 ELSE 20]

ZeroFunds ==
  [p \in Purses |-> 0]

FinalAvailable ==
  [p \in Purses |-> IF p = P0 THEN 6 ELSE 15]

FinalEscrowed ==
  [p \in Purses |-> IF p = P0 THEN 4 ELSE 5]

Init ==
  /\ available = InitialAvailable
  /\ escrowed = ZeroFunds
  /\ charged = ZeroFunds
  /\ firedLeft = FALSE
  /\ firedRight = FALSE
  /\ duplicateRejected = FALSE
  /\ missingRejected = FALSE

Reserve(p, amount) ==
  /\ available[p] >= amount
  /\ available' = [available EXCEPT ![p] = @ - amount]
  /\ escrowed' = [escrowed EXCEPT ![p] = @ + amount]
  /\ charged' = charged

FireLeft ==
  /\ ~firedLeft
  /\ Reserve(P0, 4)
  /\ firedLeft' = TRUE
  /\ UNCHANGED <<firedRight, duplicateRejected, missingRejected>>

FireRight ==
  /\ ~firedRight
  /\ Reserve(P1, 5)
  /\ firedRight' = TRUE
  /\ UNCHANGED <<firedLeft, duplicateRejected, missingRejected>>

DuplicateReject ==
  /\ ~duplicateRejected
  /\ duplicateRejected' = TRUE
  /\ UNCHANGED <<available, escrowed, charged, firedLeft, firedRight,
                  missingRejected>>

MissingReject ==
  /\ ~missingRejected
  /\ missingRejected' = TRUE
  /\ UNCHANGED <<available, escrowed, charged, firedLeft, firedRight,
                  duplicateRejected>>

Done ==
  /\ firedLeft
  /\ firedRight
  /\ duplicateRejected
  /\ missingRejected
  /\ UNCHANGED vars

Next ==
  \/ FireLeft
  \/ FireRight
  \/ DuplicateReject
  \/ MissingReject
  \/ Done

TypeOK ==
  /\ available \in [Purses -> Nat]
  /\ escrowed \in [Purses -> Nat]
  /\ charged \in [Purses -> Nat]
  /\ firedLeft \in BOOLEAN
  /\ firedRight \in BOOLEAN
  /\ duplicateRejected \in BOOLEAN
  /\ missingRejected \in BOOLEAN

TotalPreserved ==
  \A p \in Purses :
    available[p] + escrowed[p] + charged[p] = InitialAvailable[p]

DistinctPurseCommutes ==
  firedLeft /\ firedRight =>
    /\ available = FinalAvailable
    /\ escrowed = FinalEscrowed
    /\ charged = ZeroFunds

RejectsAreFailClosed ==
  /\ duplicateRejected /\ ~firedLeft /\ ~firedRight => available = InitialAvailable
  /\ missingRejected /\ ~firedLeft /\ ~firedRight => available = InitialAvailable

====
