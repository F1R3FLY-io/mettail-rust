---- MODULE TheoremChannel ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT UnsafeMode

TermIds == 0..1
NoTerm == 2
Epochs == 0..2
ValidTerms == {0}
Operations == {"None", "Produce", "Consume"}
Phases == {"Idle", "Prepared"}
Decisions == {"None", "Proven", "Refuted", "Undetermined"}
WorkBudgets == 0..1
StructuralRequiredWork == 1

PatternAccepts(term) == term = 0

CheckerDecision(term, workBudget, certificateSupplied, certificateMatches) ==
  IF workBudget < StructuralRequiredWork
  THEN "Undetermined"
  ELSE IF certificateSupplied
       THEN IF certificateMatches /\ term \in ValidTerms
            THEN "Proven"
            ELSE "Refuted"
       ELSE IF term \in ValidTerms THEN "Proven" ELSE "Refuted"

VARIABLES
  phase,
  operation,
  languageEpoch,
  spaceEpoch,
  preparedLanguageEpoch,
  preparedSpaceEpoch,
  candidate,
  proofCacheHit,
  checkerDecision,
  checkerWorkBudget,
  logicalWorkCharged,
  certificateSupplied,
  certificateMatches,
  publishRight,
  matchRight,
  checkRight,
  produceRight,
  consumeRight,
  messages,
  captures,
  commitments,
  preparedCommitCount,
  preparedMessages,
  preparedCaptures,
  rejectedCommitCount,
  rejectedMessages,
  rejectedCaptures,
  lastCommittedOperation,
  lastCommittedTerm,
  rejectionWasAtomic

vars ==
  <<phase, operation, languageEpoch, spaceEpoch,
    preparedLanguageEpoch, preparedSpaceEpoch, candidate, proofCacheHit,
    checkerDecision, checkerWorkBudget, logicalWorkCharged,
    certificateSupplied, certificateMatches, publishRight, matchRight,
    checkRight, produceRight, consumeRight, messages, captures, commitments,
    preparedCommitCount, preparedMessages, preparedCaptures,
    rejectedCommitCount, rejectedMessages, rejectedCaptures,
    lastCommittedOperation, lastCommittedTerm, rejectionWasAtomic>>

Init ==
  /\ phase = "Idle"
  /\ operation = "None"
  /\ languageEpoch = 0
  /\ spaceEpoch = 0
  /\ preparedLanguageEpoch = 0
  /\ preparedSpaceEpoch = 0
  /\ candidate = NoTerm
  /\ proofCacheHit = FALSE
  /\ checkerDecision = "None"
  /\ checkerWorkBudget = 0
  /\ logicalWorkCharged = 0
  /\ certificateSupplied = FALSE
  /\ certificateMatches = FALSE
  /\ publishRight = TRUE
  /\ matchRight = TRUE
  /\ checkRight = TRUE
  /\ produceRight = TRUE
  /\ consumeRight = TRUE
  /\ messages = {0}
  /\ captures = {}
  /\ commitments = {}
  /\ preparedCommitCount = 0
  /\ preparedMessages = {}
  /\ preparedCaptures = {}
  /\ rejectedCommitCount = 0
  /\ rejectedMessages = {}
  /\ rejectedCaptures = {}
  /\ lastCommittedOperation = "None"
  /\ lastCommittedTerm = NoTerm
  /\ rejectionWasAtomic = FALSE

PrepareProduce(term, cached, workBudget, supplied, matches) ==
  /\ phase = "Idle"
  /\ term \in TermIds
  /\ CheckerDecision(term, workBudget, supplied, matches) = "Proven"
  /\ publishRight
  /\ checkRight
  /\ produceRight
  /\ phase' = "Prepared"
  /\ operation' = "Produce"
  /\ preparedLanguageEpoch' = languageEpoch
  /\ preparedSpaceEpoch' = spaceEpoch
  /\ candidate' = term
  /\ proofCacheHit' = cached
  /\ checkerDecision' = "Proven"
  /\ checkerWorkBudget' = workBudget
  /\ logicalWorkCharged' = StructuralRequiredWork
  /\ certificateSupplied' = supplied
  /\ certificateMatches' = matches
  /\ preparedCommitCount' = Cardinality(commitments)
  /\ preparedMessages' = messages
  /\ preparedCaptures' = captures
  /\ rejectionWasAtomic' = FALSE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, publishRight, matchRight,
                  checkRight, produceRight, consumeRight, messages, captures,
                  commitments, rejectedCommitCount, rejectedMessages,
                  rejectedCaptures, lastCommittedOperation, lastCommittedTerm>>

PrepareConsume(term, cached, workBudget, supplied, matches) ==
  /\ phase = "Idle"
  /\ term \in messages
  /\ CheckerDecision(term, workBudget, supplied, matches) = "Proven"
  /\ PatternAccepts(term)
  /\ matchRight
  /\ checkRight
  /\ consumeRight
  /\ phase' = "Prepared"
  /\ operation' = "Consume"
  /\ preparedLanguageEpoch' = languageEpoch
  /\ preparedSpaceEpoch' = spaceEpoch
  /\ candidate' = term
  /\ proofCacheHit' = cached
  /\ checkerDecision' = "Proven"
  /\ checkerWorkBudget' = workBudget
  /\ logicalWorkCharged' = StructuralRequiredWork
  /\ certificateSupplied' = supplied
  /\ certificateMatches' = matches
  /\ preparedCommitCount' = Cardinality(commitments)
  /\ preparedMessages' = messages
  /\ preparedCaptures' = captures
  /\ rejectionWasAtomic' = FALSE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, publishRight, matchRight,
                  checkRight, produceRight, consumeRight, messages, captures,
                  commitments, rejectedCommitCount, rejectedMessages,
                  rejectedCaptures, lastCommittedOperation, lastCommittedTerm>>

Prepare ==
  \/ \E term \in TermIds, cached \in BOOLEAN, workBudget \in WorkBudgets,
        supplied \in BOOLEAN, matches \in BOOLEAN :
       PrepareProduce(term, cached, workBudget, supplied, matches)
  \/ \E term \in messages, cached \in BOOLEAN, workBudget \in WorkBudgets,
        supplied \in BOOLEAN, matches \in BOOLEAN :
       PrepareConsume(term, cached, workBudget, supplied, matches)

RejectChecked(term, cached, workBudget, supplied, matches) ==
  /\ phase = "Idle"
  /\ term \in TermIds
  /\ CheckerDecision(term, workBudget, supplied, matches) # "Proven"
  /\ proofCacheHit' = cached
  /\ checkerDecision' = CheckerDecision(term, workBudget, supplied, matches)
  /\ checkerWorkBudget' = workBudget
  /\ logicalWorkCharged' = StructuralRequiredWork
  /\ certificateSupplied' = supplied
  /\ certificateMatches' = matches
  /\ rejectedCommitCount' = Cardinality(commitments)
  /\ rejectedMessages' = messages
  /\ rejectedCaptures' = captures
  /\ rejectionWasAtomic' = TRUE
  /\ UNCHANGED <<phase, operation, languageEpoch, spaceEpoch,
                  preparedLanguageEpoch, preparedSpaceEpoch, candidate,
                  publishRight, matchRight, checkRight, produceRight,
                  consumeRight, messages, captures, commitments,
                  preparedCommitCount, preparedMessages, preparedCaptures,
                  lastCommittedOperation, lastCommittedTerm>>

RevokeLanguage ==
  /\ languageEpoch < 2
  /\ languageEpoch' = languageEpoch + 1
  /\ publishRight' = FALSE
  /\ matchRight' = FALSE
  /\ checkRight' = FALSE
  /\ UNCHANGED <<phase, operation, spaceEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit,
                  checkerDecision, checkerWorkBudget, logicalWorkCharged,
                  certificateSupplied, certificateMatches, produceRight,
                  consumeRight, messages, captures, commitments,
                  preparedCommitCount, preparedMessages, preparedCaptures,
                  rejectedCommitCount, rejectedMessages, rejectedCaptures,
                  lastCommittedOperation, lastCommittedTerm,
                  rejectionWasAtomic>>

RevokeSpace ==
  /\ spaceEpoch < 2
  /\ spaceEpoch' = spaceEpoch + 1
  /\ produceRight' = FALSE
  /\ consumeRight' = FALSE
  /\ UNCHANGED <<phase, operation, languageEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit,
                  checkerDecision, checkerWorkBudget, logicalWorkCharged,
                  certificateSupplied, certificateMatches, publishRight,
                  matchRight, checkRight, messages, captures, commitments,
                  preparedCommitCount, preparedMessages, preparedCaptures,
                  rejectedCommitCount, rejectedMessages, rejectedCaptures,
                  lastCommittedOperation, lastCommittedTerm,
                  rejectionWasAtomic>>

CommitProduce ==
  /\ phase = "Prepared"
  /\ operation = "Produce"
  /\ preparedLanguageEpoch = languageEpoch
  /\ preparedSpaceEpoch = spaceEpoch
  /\ publishRight
  /\ checkRight
  /\ produceRight
  /\ checkerDecision = "Proven"
  /\ phase' = "Idle"
  /\ operation' = "None"
  /\ messages' = messages \cup {candidate}
  /\ commitments' =
       commitments \cup
         {<<"Produce", candidate,
            preparedLanguageEpoch, languageEpoch,
            preparedSpaceEpoch, spaceEpoch, publishRight, checkRight,
            produceRight, checkerDecision>>}
  /\ lastCommittedOperation' = "Produce"
  /\ lastCommittedTerm' = candidate
  /\ rejectionWasAtomic' = FALSE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit, publishRight,
                  matchRight, checkRight, produceRight, consumeRight, captures,
                  preparedCommitCount, preparedMessages, preparedCaptures,
                  checkerDecision, checkerWorkBudget, logicalWorkCharged,
                  certificateSupplied, certificateMatches, rejectedCommitCount,
                  rejectedMessages, rejectedCaptures>>

CommitConsume ==
  /\ phase = "Prepared"
  /\ operation = "Consume"
  /\ candidate \in messages
  /\ preparedLanguageEpoch = languageEpoch
  /\ preparedSpaceEpoch = spaceEpoch
  /\ matchRight
  /\ checkRight
  /\ consumeRight
  /\ checkerDecision = "Proven"
  /\ phase' = "Idle"
  /\ operation' = "None"
  /\ messages' = messages \ {candidate}
  /\ commitments' =
       commitments \cup
         {<<"Consume", candidate,
            preparedLanguageEpoch, languageEpoch,
            preparedSpaceEpoch, spaceEpoch, matchRight, checkRight,
            consumeRight, checkerDecision>>}
  /\ captures' = {candidate}
  /\ lastCommittedOperation' = "Consume"
  /\ lastCommittedTerm' = candidate
  /\ rejectionWasAtomic' = FALSE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit, publishRight,
                  matchRight, checkRight, produceRight, consumeRight,
                  preparedCommitCount, preparedMessages, preparedCaptures,
                  checkerDecision, checkerWorkBudget, logicalWorkCharged,
                  certificateSupplied, certificateMatches, rejectedCommitCount,
                  rejectedMessages, rejectedCaptures>>

Commit == CommitProduce \/ CommitConsume

MustReject ==
  \/ preparedLanguageEpoch # languageEpoch
  \/ preparedSpaceEpoch # spaceEpoch
  \/ checkerDecision # "Proven"
  \/ ~checkRight
  \/ (operation = "Produce" /\ (~publishRight \/ ~produceRight))
  \/ (operation = "Consume" /\
       (~matchRight \/ ~consumeRight \/ candidate \notin messages))

RejectPrepared ==
  /\ phase = "Prepared"
  /\ MustReject
  /\ phase' = "Idle"
  /\ operation' = "None"
  /\ rejectedCommitCount' = Cardinality(commitments)
  /\ rejectedMessages' = messages
  /\ rejectedCaptures' = captures
  /\ rejectionWasAtomic' = TRUE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit, publishRight,
                  matchRight, checkRight, produceRight, consumeRight, messages,
                  captures, commitments, preparedCommitCount, preparedMessages,
                  preparedCaptures, checkerDecision, checkerWorkBudget,
                  logicalWorkCharged, certificateSupplied, certificateMatches,
                  lastCommittedOperation, lastCommittedTerm>>

UnsafeCommit ==
  /\ UnsafeMode
  /\ phase = "Prepared"
  /\ operation \in {"Produce", "Consume"}
  /\ phase' = "Idle"
  /\ operation' = "None"
  /\ messages' =
       IF operation = "Produce"
       THEN messages \cup {candidate}
       ELSE messages \ {candidate}
  /\ commitments' =
       commitments \cup
         {<<operation, candidate,
            preparedLanguageEpoch, languageEpoch,
            preparedSpaceEpoch, spaceEpoch,
            IF operation = "Produce" THEN publishRight ELSE matchRight,
            checkRight,
            IF operation = "Produce" THEN produceRight ELSE consumeRight,
            checkerDecision>>}
  /\ captures' = IF operation = "Consume" THEN {candidate} ELSE captures
  /\ lastCommittedOperation' = operation
  /\ lastCommittedTerm' = candidate
  /\ rejectionWasAtomic' = FALSE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit, publishRight,
                  matchRight, checkRight, produceRight, consumeRight,
                  preparedCommitCount, preparedMessages, preparedCaptures,
                  checkerDecision, checkerWorkBudget, logicalWorkCharged,
                  certificateSupplied, certificateMatches, rejectedCommitCount,
                  rejectedMessages, rejectedCaptures>>

IdleStep ==
  /\ phase = "Idle"
  /\ UNCHANGED vars

Next ==
  \/ Prepare
  \/ \E term \in TermIds, cached \in BOOLEAN, workBudget \in WorkBudgets,
        supplied \in BOOLEAN, matches \in BOOLEAN :
       RejectChecked(term, cached, workBudget, supplied, matches)
  \/ RevokeLanguage
  \/ RevokeSpace
  \/ Commit
  \/ RejectPrepared
  \/ UnsafeCommit
  \/ IdleStep

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ phase \in Phases
  /\ operation \in Operations
  /\ languageEpoch \in Epochs
  /\ spaceEpoch \in Epochs
  /\ preparedLanguageEpoch \in Epochs
  /\ preparedSpaceEpoch \in Epochs
  /\ candidate \in TermIds \cup {NoTerm}
  /\ proofCacheHit \in BOOLEAN
  /\ checkerDecision \in Decisions
  /\ checkerWorkBudget \in WorkBudgets
  /\ logicalWorkCharged \in Nat
  /\ certificateSupplied \in BOOLEAN
  /\ certificateMatches \in BOOLEAN
  /\ publishRight \in BOOLEAN
  /\ matchRight \in BOOLEAN
  /\ checkRight \in BOOLEAN
  /\ produceRight \in BOOLEAN
  /\ consumeRight \in BOOLEAN
  /\ messages \subseteq TermIds
  /\ captures \subseteq TermIds
  /\ commitments \subseteq
       (Operations \ {"None"}) \X TermIds \X Epochs \X Epochs
         \X Epochs \X Epochs \X BOOLEAN \X BOOLEAN \X BOOLEAN \X Decisions
  /\ preparedCommitCount \in Nat
  /\ preparedMessages \subseteq TermIds
  /\ preparedCaptures \subseteq TermIds
  /\ rejectedCommitCount \in Nat
  /\ rejectedMessages \subseteq TermIds
  /\ rejectedCaptures \subseteq TermIds
  /\ lastCommittedOperation \in Operations
  /\ lastCommittedTerm \in TermIds \cup {NoTerm}
  /\ rejectionWasAtomic \in BOOLEAN

AllCommitsAuthorized ==
  \A record \in commitments :
    /\ record[3] = record[4]
    /\ record[5] = record[6]
    /\ record[7] = TRUE
    /\ record[8] = TRUE
    /\ record[9] = TRUE

AllCommitsAreProven ==
  \A record \in commitments : record[10] = "Proven"

AllProducedTermsAdmitted ==
  \A record \in commitments :
    record[1] = "Produce" => record[2] \in ValidTerms

PreparedCarriesCheckedEvidence ==
  phase = "Prepared" =>
    /\ candidate \in ValidTerms
    /\ checkerDecision = "Proven"
    /\ logicalWorkCharged = StructuralRequiredWork
    /\ (operation = "Consume" => PatternAccepts(candidate))

PreparedStateIsInvisible ==
  phase = "Prepared" =>
    /\ Cardinality(commitments) = preparedCommitCount
    /\ messages = preparedMessages
    /\ captures = preparedCaptures

CapturesCarryCheckedConsumeEvidence ==
  \A term \in captures :
    /\ term \in ValidTerms
    /\ PatternAccepts(term)
    /\ \E record \in commitments :
         /\ record[1] = "Consume"
         /\ record[2] = term
         /\ record[7] = TRUE
         /\ record[8] = TRUE
         /\ record[9] = TRUE
         /\ record[10] = "Proven"

RejectedTransactionIsAtomic ==
  rejectionWasAtomic =>
    /\ phase = "Idle"
    /\ Cardinality(commitments) = rejectedCommitCount
    /\ messages = rejectedMessages
    /\ captures = rejectedCaptures

ExhaustionIsUndetermined ==
  checkerDecision # "None" /\
  checkerWorkBudget < StructuralRequiredWork =>
    checkerDecision = "Undetermined"

InvalidPresentedCertificateIsRefuted ==
  checkerDecision # "None" /\
  checkerWorkBudget >= StructuralRequiredWork /\
  certificateSupplied /\ ~certificateMatches =>
    checkerDecision = "Refuted"

CacheChargeIsTransparent ==
  checkerDecision # "None" => logicalWorkCharged = StructuralRequiredWork

CacheNeverConveysAuthority ==
  \A record \in commitments :
    /\ record[7] = TRUE
    /\ record[8] = TRUE
    /\ record[9] = TRUE

====
