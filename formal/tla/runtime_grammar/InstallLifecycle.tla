---- MODULE InstallLifecycle ----
EXTENDS Naturals, FiniteSets, TLC

Rights == {"Parse", "Match"}
Commitments == {1, 2}
Tokens == {1, 2}
Aliases == {"calc", "logic"}
Generations == 0..2
NoCommitment == 0
NoToken == 0

VARIABLES
  phase,
  live,
  generation,
  commitment,
  ceiling,
  pendingCommitment,
  pendingRights,
  pendingToken,
  handles,
  aliasBindings,
  preparedLive,
  preparedGeneration,
  preparedCommitment,
  preparedCeiling,
  preparedHandles,
  preparedAliases

vars ==
  <<phase, live, generation, commitment, ceiling,
    pendingCommitment, pendingRights, pendingToken,
    handles, aliasBindings,
    preparedLive, preparedGeneration, preparedCommitment,
    preparedCeiling, preparedHandles, preparedAliases>>

Handle(token, gen, image, rights) == <<token, gen, image, rights>>

TokenCompatible(token, proposed) ==
  \A existing \in handles : existing[1] = token => existing = proposed

ValidHandle(handle) ==
  /\ live
  /\ handle[2] = generation
  /\ handle[3] = commitment
  /\ \A right \in handle[4] : right \in ceiling

Init ==
  /\ phase = "Idle"
  /\ live = FALSE
  /\ generation = 0
  /\ commitment = NoCommitment
  /\ ceiling = {}
  /\ pendingCommitment = NoCommitment
  /\ pendingRights = {}
  /\ pendingToken = NoToken
  /\ handles = {}
  /\ aliasBindings = {}
  /\ preparedLive = FALSE
  /\ preparedGeneration = 0
  /\ preparedCommitment = NoCommitment
  /\ preparedCeiling = {}
  /\ preparedHandles = {}
  /\ preparedAliases = {}

PrepareInstall(image, rights, token) ==
  /\ phase = "Idle"
  /\ image \in Commitments
  /\ rights \subseteq Rights
  /\ token \in Tokens
  /\ phase' = "Prepared"
  /\ pendingCommitment' = image
  /\ pendingRights' = rights
  /\ pendingToken' = token
  /\ preparedLive' = live
  /\ preparedGeneration' = generation
  /\ preparedCommitment' = commitment
  /\ preparedCeiling' = ceiling
  /\ preparedHandles' = handles
  /\ preparedAliases' = aliasBindings
  /\ UNCHANGED <<live, generation, commitment, ceiling,
                  handles, aliasBindings>>

Prepare ==
  \E image \in Commitments, rights \in SUBSET Rights, token \in Tokens :
    PrepareInstall(image, rights, token)

CommitFresh ==
  LET nextGeneration == generation + 1 IN
  LET proposed == Handle(pendingToken, nextGeneration,
                         pendingCommitment, pendingRights) IN
  /\ phase = "Prepared"
  /\ ~live
  /\ generation < 2
  /\ TokenCompatible(pendingToken, proposed)
  /\ phase' = "Idle"
  /\ live' = TRUE
  /\ generation' = nextGeneration
  /\ commitment' = pendingCommitment
  /\ ceiling' = pendingRights
  /\ handles' = handles \cup {proposed}
  /\ UNCHANGED <<pendingCommitment, pendingRights, pendingToken,
                  aliasBindings, preparedLive, preparedGeneration,
                  preparedCommitment, preparedCeiling,
                  preparedHandles, preparedAliases>>

CommitReuse ==
  LET proposed == Handle(pendingToken, generation,
                         pendingCommitment, pendingRights) IN
  /\ phase = "Prepared"
  /\ live
  /\ commitment = pendingCommitment
  /\ TokenCompatible(pendingToken, proposed)
  /\ phase' = "Idle"
  /\ ceiling' = ceiling \cup pendingRights
  /\ handles' = handles \cup {proposed}
  /\ UNCHANGED <<live, generation, commitment,
                  pendingCommitment, pendingRights, pendingToken,
                  aliasBindings, preparedLive, preparedGeneration,
                  preparedCommitment, preparedCeiling,
                  preparedHandles, preparedAliases>>

RejectPrepared ==
  LET proposed == Handle(pendingToken, generation,
                         pendingCommitment, pendingRights) IN
  /\ phase = "Prepared"
  /\ \/ (live /\ commitment # pendingCommitment)
     \/ ~TokenCompatible(pendingToken, proposed)
     \/ (~live /\ generation = 2)
  /\ phase' = "Idle"
  /\ UNCHANGED <<live, generation, commitment, ceiling,
                  pendingCommitment, pendingRights, pendingToken,
                  handles, aliasBindings, preparedLive, preparedGeneration,
                  preparedCommitment, preparedCeiling,
                  preparedHandles, preparedAliases>>

BindAlias(alias, token) ==
  /\ phase = "Idle"
  /\ alias \in Aliases
  /\ token \in Tokens
  /\ ~\E binding \in aliasBindings : binding[1] = alias
  /\ \E handle \in handles : handle[1] = token /\ ValidHandle(handle)
  /\ aliasBindings' = aliasBindings \cup {<<alias, token>>}
  /\ UNCHANGED <<phase, live, generation, commitment, ceiling,
                  pendingCommitment, pendingRights, pendingToken, handles,
                  preparedLive, preparedGeneration, preparedCommitment,
                  preparedCeiling, preparedHandles, preparedAliases>>

Bind == \E alias \in Aliases, token \in Tokens : BindAlias(alias, token)

Revoke ==
  /\ phase = "Idle"
  /\ live
  /\ generation < 2
  /\ live' = FALSE
  /\ generation' = generation + 1
  /\ ceiling' = {}
  /\ UNCHANGED <<phase, commitment,
                  pendingCommitment, pendingRights, pendingToken,
                  handles, aliasBindings, preparedLive, preparedGeneration,
                  preparedCommitment, preparedCeiling,
                  preparedHandles, preparedAliases>>

IdleStep ==
  /\ phase = "Idle"
  /\ UNCHANGED vars

Next ==
  \/ Prepare
  \/ CommitFresh
  \/ CommitReuse
  \/ RejectPrepared
  \/ Bind
  \/ Revoke
  \/ IdleStep

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ phase \in {"Idle", "Prepared"}
  /\ live \in BOOLEAN
  /\ generation \in Generations
  /\ commitment \in Commitments \cup {NoCommitment}
  /\ ceiling \subseteq Rights
  /\ pendingCommitment \in Commitments \cup {NoCommitment}
  /\ pendingRights \subseteq Rights
  /\ pendingToken \in Tokens \cup {NoToken}
  /\ handles \subseteq Tokens \X Generations \X Commitments \X SUBSET Rights
  /\ aliasBindings \subseteq Aliases \X Tokens
  /\ preparedLive \in BOOLEAN
  /\ preparedGeneration \in Generations
  /\ preparedCommitment \in Commitments \cup {NoCommitment}
  /\ preparedCeiling \subseteq Rights
  /\ preparedHandles \subseteq Tokens \X Generations \X Commitments \X SUBSET Rights
  /\ preparedAliases \subseteq Aliases \X Tokens

PreparationIsInvisible ==
  phase = "Prepared" =>
    /\ live = preparedLive
    /\ generation = preparedGeneration
    /\ commitment = preparedCommitment
    /\ ceiling = preparedCeiling
    /\ handles = preparedHandles
    /\ aliasBindings = preparedAliases

ValidHandlesCannotAmplify ==
  \A handle \in handles :
    ValidHandle(handle) => \A right \in handle[4] : right \in ceiling

OneMeaningPerToken ==
  \A left \in handles, right \in handles :
    left[1] = right[1] => left = right

AliasesNameMintedTokens ==
  \A binding \in aliasBindings :
    \E handle \in handles : handle[1] = binding[2]

ActiveHandlesUseInstalledCommitment ==
  \A handle \in handles : ValidHandle(handle) => handle[3] = commitment

RevocationInvalidatesEveryHandle ==
  ~live => \A handle \in handles : ~ValidHandle(handle)

====
