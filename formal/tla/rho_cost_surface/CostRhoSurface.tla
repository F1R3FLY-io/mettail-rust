---- MODULE CostRhoSurface ----
EXTENDS Naturals, TLC

\* Bounded Cost(Rho) front-end authority/fingerprint model. Syntax is evidence,
\* never supply. Only separate Provision/Spend authority may change the ledger.
\* Scope boundary: this does NOT prove Cost(G) R1--R3, wrapped-continuation
\* subject reduction, or the exact semantic-grade-to-host-demand projector.
CONSTANT LanguageFingerprint

Surfaces == {"Unsigned", "SignedGround", "StackGround", "StackTransfer"}
Phases == {"Raw", "Lowered", "Committed", "Rejected"}
Grade(s) == CASE s = "Unsigned" -> 0
                [] s = "SignedGround" -> 1
                [] s = "StackGround" -> 1
                [] s = "StackTransfer" -> 1
Fundable(s) == s # "StackTransfer"

VARIABLES surface, phase, planGrade, planFingerprint,
          certificateFingerprint, hasProvision, hasSpend, guardOK,
          provisioned, available, minted, spent
vars == <<surface, phase, planGrade, planFingerprint,
          certificateFingerprint, hasProvision, hasSpend, guardOK,
          provisioned, available, minted, spent>>
ledger == <<available, minted, spent>>

Init ==
  /\ surface \in Surfaces
  /\ phase = "Raw"
  /\ planGrade = 0
  /\ planFingerprint = ""
  /\ certificateFingerprint = ""
  /\ hasProvision \in BOOLEAN
  /\ hasSpend \in BOOLEAN
  /\ guardOK \in BOOLEAN
  /\ provisioned = FALSE
  /\ available = 2
  /\ minted = 0
  /\ spent = 0

Lower ==
  /\ phase = "Raw"
  /\ Fundable(surface)
  /\ phase' = "Lowered"
  /\ planGrade' = Grade(surface)
  /\ planFingerprint' = LanguageFingerprint
  /\ certificateFingerprint' = LanguageFingerprint
  /\ UNCHANGED <<surface, hasProvision, hasSpend, guardOK,
                 provisioned, available, minted, spent>>

RejectUnfundable ==
  /\ phase = "Raw"
  /\ ~Fundable(surface)
  /\ phase' = "Rejected"
  /\ UNCHANGED <<surface, planGrade, planFingerprint,
                 certificateFingerprint, hasProvision, hasSpend,
                 guardOK, provisioned, available, minted, spent>>

Provision ==
  /\ phase = "Lowered"
  /\ hasProvision
  /\ ~provisioned
  /\ available' = available + 1
  /\ minted' = minted + 1
  /\ provisioned' = TRUE
  /\ UNCHANGED <<surface, phase, planGrade, planFingerprint,
                 certificateFingerprint, hasProvision, hasSpend,
                 guardOK, spent>>

Commit ==
  /\ phase = "Lowered"
  /\ hasSpend
  /\ guardOK
  /\ available >= planGrade
  /\ available' = available - planGrade
  /\ spent' = spent + planGrade
  /\ phase' = "Committed"
  /\ UNCHANGED <<surface, planGrade, planFingerprint,
                 certificateFingerprint, hasProvision, hasSpend,
                 guardOK, provisioned, minted>>

RejectCommit ==
  /\ phase = "Lowered"
  /\ (~hasSpend \/ ~guardOK \/ available < planGrade)
  /\ phase' = "Rejected"
  /\ UNCHANGED <<surface, planGrade, planFingerprint,
                 certificateFingerprint, hasProvision, hasSpend,
                 guardOK, provisioned, available, minted, spent>>

Done ==
  /\ phase \in {"Committed", "Rejected"}
  /\ UNCHANGED vars

Next == Lower \/ RejectUnfundable \/ Provision \/ Commit \/ RejectCommit \/ Done
Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ surface \in Surfaces
  /\ phase \in Phases
  /\ planGrade \in Nat
  /\ planFingerprint \in STRING
  /\ certificateFingerprint \in STRING
  /\ hasProvision \in BOOLEAN
  /\ hasSpend \in BOOLEAN
  /\ guardOK \in BOOLEAN
  /\ provisioned \in BOOLEAN
  /\ available \in Nat
  /\ minted \in Nat
  /\ spent \in Nat

Conservation == available + spent = 2 + minted
NoSyntaxMint == (phase = "Lowered" /\ ~provisioned) => minted = 0
NoMintWithoutAuthority == minted > 0 => hasProvision
NoSpendWithoutAuthority == spent > 0 => hasSpend
RejectedNeverSpends == phase = "Rejected" => spent = 0
FundabilityGate == phase \in {"Lowered", "Committed"} => Fundable(surface)
GradeProvenance ==
  phase \in {"Lowered", "Committed"} =>
    /\ planGrade = Grade(surface)
    /\ planFingerprint = LanguageFingerprint
    /\ certificateFingerprint = LanguageFingerprint

====
