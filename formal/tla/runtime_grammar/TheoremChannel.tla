---- MODULE TheoremChannel ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT UnsafeMode

TermIds == 0..1
NoTerm == 2
Epochs == 0..2
ValidTerms == {0}
Operations == {"None", "Produce", "Consume"}
Phases == {"Idle", "Prepared"}

CertificateAccepts(term) == term \in ValidTerms
PatternAccepts(term) == term = 0

VARIABLES
  phase,
  operation,
  languageEpoch,
  spaceEpoch,
  preparedLanguageEpoch,
  preparedSpaceEpoch,
  candidate,
  proofCacheHit,
  publishRight,
  matchRight,
  produceRight,
  consumeRight,
  messages,
  captures,
  commitments,
  preparedCommitCount,
  lastCommittedOperation,
  lastCommittedTerm,
  rejectionWasAtomic

vars ==
  <<phase, operation, languageEpoch, spaceEpoch,
    preparedLanguageEpoch, preparedSpaceEpoch, candidate, proofCacheHit,
    publishRight, matchRight, produceRight, consumeRight, messages, captures,
    commitments, preparedCommitCount, lastCommittedOperation,
    lastCommittedTerm, rejectionWasAtomic>>

Init ==
  /\ phase = "Idle"
  /\ operation = "None"
  /\ languageEpoch = 0
  /\ spaceEpoch = 0
  /\ preparedLanguageEpoch = 0
  /\ preparedSpaceEpoch = 0
  /\ candidate = NoTerm
  /\ proofCacheHit = FALSE
  /\ publishRight = TRUE
  /\ matchRight = TRUE
  /\ produceRight = TRUE
  /\ consumeRight = TRUE
  /\ messages = {0}
  /\ captures = {}
  /\ commitments = {}
  /\ preparedCommitCount = 0
  /\ lastCommittedOperation = "None"
  /\ lastCommittedTerm = NoTerm
  /\ rejectionWasAtomic = TRUE

PrepareProduce(term, cached) ==
  /\ phase = "Idle"
  /\ term \in TermIds
  /\ CertificateAccepts(term)
  /\ publishRight
  /\ produceRight
  /\ phase' = "Prepared"
  /\ operation' = "Produce"
  /\ preparedLanguageEpoch' = languageEpoch
  /\ preparedSpaceEpoch' = spaceEpoch
  /\ candidate' = term
  /\ proofCacheHit' = cached
  /\ captures' = {}
  /\ preparedCommitCount' = Cardinality(commitments)
  /\ rejectionWasAtomic' = TRUE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, publishRight, matchRight,
                  produceRight, consumeRight, messages, commitments,
                  lastCommittedOperation, lastCommittedTerm>>

PrepareConsume(term, cached) ==
  /\ phase = "Idle"
  /\ term \in messages
  /\ CertificateAccepts(term)
  /\ PatternAccepts(term)
  /\ matchRight
  /\ consumeRight
  /\ phase' = "Prepared"
  /\ operation' = "Consume"
  /\ preparedLanguageEpoch' = languageEpoch
  /\ preparedSpaceEpoch' = spaceEpoch
  /\ candidate' = term
  /\ proofCacheHit' = cached
  /\ captures' = {}
  /\ preparedCommitCount' = Cardinality(commitments)
  /\ rejectionWasAtomic' = TRUE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, publishRight, matchRight,
                  produceRight, consumeRight, messages, commitments,
                  lastCommittedOperation, lastCommittedTerm>>

Prepare ==
  \/ \E term \in TermIds, cached \in BOOLEAN : PrepareProduce(term, cached)
  \/ \E term \in messages, cached \in BOOLEAN : PrepareConsume(term, cached)

RejectInvalidProduce(term, cached) ==
  /\ phase = "Idle"
  /\ term \in TermIds
  /\ ~CertificateAccepts(term)
  /\ proofCacheHit' = cached
  /\ rejectionWasAtomic' = TRUE
  /\ UNCHANGED <<phase, operation, languageEpoch, spaceEpoch,
                  preparedLanguageEpoch, preparedSpaceEpoch, candidate,
                  publishRight, matchRight, produceRight, consumeRight,
                  messages, captures, commitments, preparedCommitCount,
                  lastCommittedOperation, lastCommittedTerm>>

RevokeLanguage ==
  /\ languageEpoch < 2
  /\ languageEpoch' = languageEpoch + 1
  /\ publishRight' = FALSE
  /\ matchRight' = FALSE
  /\ UNCHANGED <<phase, operation, spaceEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit, produceRight,
                  consumeRight, messages, captures, commitments,
                  preparedCommitCount, lastCommittedOperation,
                  lastCommittedTerm, rejectionWasAtomic>>

RevokeSpace ==
  /\ spaceEpoch < 2
  /\ spaceEpoch' = spaceEpoch + 1
  /\ produceRight' = FALSE
  /\ consumeRight' = FALSE
  /\ UNCHANGED <<phase, operation, languageEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit, publishRight,
                  matchRight, messages, captures, commitments,
                  preparedCommitCount, lastCommittedOperation,
                  lastCommittedTerm, rejectionWasAtomic>>

CommitProduce ==
  /\ phase = "Prepared"
  /\ operation = "Produce"
  /\ preparedLanguageEpoch = languageEpoch
  /\ preparedSpaceEpoch = spaceEpoch
  /\ publishRight
  /\ produceRight
  /\ phase' = "Idle"
  /\ operation' = "None"
  /\ messages' = messages \cup {candidate}
  /\ commitments' =
       commitments \cup
         {<<"Produce", candidate,
            preparedLanguageEpoch, languageEpoch,
            preparedSpaceEpoch, spaceEpoch, publishRight, produceRight>>}
  /\ captures' = {}
  /\ lastCommittedOperation' = "Produce"
  /\ lastCommittedTerm' = candidate
  /\ rejectionWasAtomic' = TRUE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit, publishRight,
                  matchRight, produceRight, consumeRight, preparedCommitCount>>

CommitConsume ==
  /\ phase = "Prepared"
  /\ operation = "Consume"
  /\ candidate \in messages
  /\ preparedLanguageEpoch = languageEpoch
  /\ preparedSpaceEpoch = spaceEpoch
  /\ matchRight
  /\ consumeRight
  /\ phase' = "Idle"
  /\ operation' = "None"
  /\ messages' = messages \ {candidate}
  /\ commitments' =
       commitments \cup
         {<<"Consume", candidate,
            preparedLanguageEpoch, languageEpoch,
            preparedSpaceEpoch, spaceEpoch, matchRight, consumeRight>>}
  /\ captures' = {candidate}
  /\ lastCommittedOperation' = "Consume"
  /\ lastCommittedTerm' = candidate
  /\ rejectionWasAtomic' = TRUE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit, publishRight,
                  matchRight, produceRight, consumeRight, preparedCommitCount>>

Commit == CommitProduce \/ CommitConsume

MustReject ==
  \/ preparedLanguageEpoch # languageEpoch
  \/ preparedSpaceEpoch # spaceEpoch
  \/ (operation = "Produce" /\ (~publishRight \/ ~produceRight))
  \/ (operation = "Consume" /\
       (~matchRight \/ ~consumeRight \/ candidate \notin messages))

RejectPrepared ==
  /\ phase = "Prepared"
  /\ MustReject
  /\ phase' = "Idle"
  /\ operation' = "None"
  /\ captures' = {}
  /\ rejectionWasAtomic' = TRUE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit, publishRight,
                  matchRight, produceRight, consumeRight, messages,
                  commitments, preparedCommitCount, lastCommittedOperation,
                  lastCommittedTerm>>

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
            IF operation = "Produce" THEN produceRight ELSE consumeRight>>}
  /\ captures' = IF operation = "Consume" THEN {candidate} ELSE {}
  /\ lastCommittedOperation' = operation
  /\ lastCommittedTerm' = candidate
  /\ rejectionWasAtomic' = TRUE
  /\ UNCHANGED <<languageEpoch, spaceEpoch, preparedLanguageEpoch,
                  preparedSpaceEpoch, candidate, proofCacheHit, publishRight,
                  matchRight, produceRight, consumeRight, preparedCommitCount>>

IdleStep ==
  /\ phase = "Idle"
  /\ UNCHANGED vars

Next ==
  \/ Prepare
  \/ \E term \in TermIds, cached \in BOOLEAN : RejectInvalidProduce(term, cached)
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
  /\ publishRight \in BOOLEAN
  /\ matchRight \in BOOLEAN
  /\ produceRight \in BOOLEAN
  /\ consumeRight \in BOOLEAN
  /\ messages \subseteq TermIds
  /\ captures \subseteq TermIds
  /\ commitments \subseteq
       (Operations \ {"None"}) \X TermIds \X Epochs \X Epochs
         \X Epochs \X Epochs \X BOOLEAN \X BOOLEAN
  /\ preparedCommitCount \in Nat
  /\ lastCommittedOperation \in Operations
  /\ lastCommittedTerm \in TermIds \cup {NoTerm}
  /\ rejectionWasAtomic \in BOOLEAN

AllCommitsAuthorized ==
  \A record \in commitments :
    /\ record[3] = record[4]
    /\ record[5] = record[6]
    /\ record[7] = TRUE
    /\ record[8] = TRUE

AllProducedTermsAdmitted ==
  \A record \in commitments :
    record[1] = "Produce" => record[2] \in ValidTerms

PreparedCarriesCheckedEvidence ==
  phase = "Prepared" =>
    /\ candidate \in ValidTerms
    /\ (operation = "Consume" => PatternAccepts(candidate))

PreparedStateIsInvisible ==
  phase = "Prepared" =>
    /\ Cardinality(commitments) = preparedCommitCount
    /\ captures = {}

CapturesCarryCheckedConsumeEvidence ==
  captures # {} =>
    /\ lastCommittedOperation = "Consume"
    /\ captures = {lastCommittedTerm}
    /\ lastCommittedTerm \in ValidTerms
    /\ PatternAccepts(lastCommittedTerm)

RejectedTransactionIsAtomic == rejectionWasAtomic

CacheNeverConveysAuthority ==
  \A record \in commitments :
    /\ record[7] = TRUE
    /\ record[8] = TRUE

====
