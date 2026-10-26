---- MODULE StagedLanguageCapabilities ----
EXTENDS Naturals, FiniteSets, TLC

\* A bounded ownership contract, not a model of today's node wiring.
\* Two attempts and roots plus an optional second language expose sibling
\* aliasing, root reset, per-language revocation, and independent replay. The opaque
\* token bytes intentionally omit the attempt: current Rust hashes language,
\* generation, rights, and policy, and consults a process-local directory.
CONSTANTS A, B, R0, R1, L0, L1, UnsafeMode,
          TwoLanguages, MaxEpoch, MaxGeneration
ASSUME /\ A # B /\ R0 # R1 /\ L0 # L1

Attempts == {A, B}
Roots == {R0, R1}
Languages == IF TwoLanguages THEN {L0, L1} ELSE {L0}
NoRoot == "NoRoot"
NoActor == "NoActor"
Phases == {"Idle", "Open", "Aborted"}
TokenIds == Languages \X (0..MaxGeneration)

\* RegistrySnapshot and cached artifacts are data.  Neither is a capability.
Artifact(l) == <<"sealed-image", l>>
Artifacts == {Artifact(l) : l \in Languages}
Result(r, l) == <<r, l>>
Observation(l, r) == <<l, r, Result(r, l)>>

VARIABLES phase, root, epoch, generation, staged, live, issued,
          cache, observations, lastActor, lastKind, lastLanguage,
          beforeLocal, beforeCache
vars == <<phase, root, epoch, generation, staged, live, issued,
          cache, observations, lastActor, lastKind, lastLanguage,
          beforeLocal, beforeCache>>

StagedFor(a) == {l \in Languages : <<a, l>> \in staged}
Token(a, l) == <<l, generation[a][l]>>
NewTokens(a) == {Token(a, l) : l \in StagedFor(a)}
LocalView(a) ==
  <<phase[a], root[a], epoch[a], generation[a], StagedFor(a),
    live[a], issued[a], observations[a]>>

\* Ghost snapshots let TLC check that an action by a leaves every sibling's
\* mutable authority, root, generation, staged work, and observation intact.
Advance(a, kind, l) ==
  /\ lastActor' = a
  /\ lastKind' = kind
  /\ lastLanguage' = l
  /\ beforeLocal' = [b \in Attempts |-> LocalView(b)]
  /\ beforeCache' = cache

Init ==
  /\ phase = [a \in Attempts |-> "Idle"]
  /\ root = [a \in Attempts |-> NoRoot]
  /\ epoch = [a \in Attempts |-> 0]
  /\ generation = [a \in Attempts |-> [l \in Languages |-> 0]]
  /\ staged = {}
  /\ live = [a \in Attempts |-> {}]
  /\ issued = [a \in Attempts |-> {}]
  /\ cache = {}
  /\ observations = [a \in Attempts |-> {}]
  /\ lastActor = NoActor
  /\ lastKind = "Init"
  /\ lastLanguage = L0
  /\ beforeLocal = [a \in Attempts |-> LocalView(a)]
  /\ beforeCache = cache

Begin(a, r) ==
  /\ a \in Attempts /\ r \in Roots
  /\ phase[a] = "Idle" /\ epoch[a] < MaxEpoch
  /\ phase' = [phase EXCEPT ![a] = "Open"]
  /\ root' = [root EXCEPT ![a] = r]
  /\ epoch' = [epoch EXCEPT ![a] = @ + 1]
  /\ generation' = [generation EXCEPT ![a] = [l \in Languages |-> 0]]
  /\ Advance(a, "Begin", L0)
  /\ UNCHANGED <<staged, live, issued, cache, observations>>

Stage(a, l) ==
  /\ a \in Attempts /\ l \in Languages
  /\ phase[a] = "Open" /\ <<a, l>> \notin staged
  /\ staged' = staged \cup {<<a, l>>}
  /\ cache' = cache \cup {Artifact(l)}
  /\ Advance(a, "Stage", L0)
  /\ UNCHANGED <<phase, root, epoch, generation, live, issued, observations>>

\* Complete staged set publishes in one transition; artifact preparation and
\* failed admission have no partial authority publication.
Commit(a) ==
  /\ a \in Attempts /\ phase[a] = "Open"
  /\ StagedFor(a) # {}
  /\ staged' = staged \ ({a} \X Languages)
  /\ live' = [live EXCEPT ![a] = @ \cup NewTokens(a)]
  /\ issued' = [issued EXCEPT ![a] = @ \cup NewTokens(a)]
  /\ Advance(a, "Commit", L0)
  /\ UNCHANGED <<phase, root, epoch, generation, cache, observations>>

Reject(a) ==
  /\ a \in Attempts /\ phase[a] = "Open" /\ StagedFor(a) # {}
  /\ staged' = staged \ ({a} \X Languages)
  /\ Advance(a, "Reject", L0)
  /\ UNCHANGED <<phase, root, epoch, generation, live, issued, cache,
                  observations>>

Revoke(a, l) ==
  /\ a \in Attempts /\ l \in Languages
  /\ phase[a] = "Open" /\ Token(a, l) \in live[a]
  /\ generation[a][l] < MaxGeneration
  /\ live' = [live EXCEPT ![a] = @ \ {Token(a, l)}]
  /\ generation' = [generation EXCEPT ![a][l] = @ + 1]
  /\ Advance(a, "Revoke", l)
  /\ UNCHANGED <<phase, root, epoch, staged, issued, cache, observations>>

Observe(a, l) ==
  /\ a \in Attempts /\ l \in Languages
  /\ phase[a] = "Open" /\ Token(a, l) \in live[a]
  /\ Observation(l, root[a]) \notin observations[a]
  /\ observations' = [observations EXCEPT
                      ![a] = @ \cup {Observation(l, root[a])}]
  /\ Advance(a, "Observe", L0)
  /\ UNCHANGED <<phase, root, epoch, generation, staged, live, issued, cache>>

\* An offered failure destroys the private directory and uncommitted output.
Abort(a) ==
  /\ a \in Attempts /\ phase[a] = "Open"
  /\ phase' = [phase EXCEPT ![a] = "Aborted"]
  /\ staged' = staged \ ({a} \X Languages)
  /\ live' = [live EXCEPT ![a] = {}]
  /\ issued' = [issued EXCEPT ![a] = {}]
  /\ observations' = [observations EXCEPT ![a] = {}]
  /\ Advance(a, "Abort", L0)
  /\ UNCHANGED <<root, epoch, generation, cache>>

\* RSpace reset and attempt-directory teardown are one proposed boundary.
Reset(a) ==
  /\ a \in Attempts /\ phase[a] \in {"Open", "Aborted"}
  /\ phase' = [phase EXCEPT ![a] = "Idle"]
  /\ root' = [root EXCEPT ![a] = NoRoot]
  /\ staged' = staged \ ({a} \X Languages)
  /\ live' = [live EXCEPT ![a] = {}]
  /\ issued' = [issued EXCEPT ![a] = {}]
  /\ observations' = [observations EXCEPT ![a] = {}]
  /\ Advance(a, "Reset", L0)
  /\ UNCHANGED <<epoch, generation, cache>>

\* Each unsafe action is individually enabled by its negative-control config.
BadShare(a, b, t) ==
  /\ UnsafeMode = "SharedAuthority"
  /\ a \in Attempts /\ b \in Attempts /\ a # b
  /\ phase[b] = "Open" /\ t \in live[a] /\ t \notin issued[b]
  /\ live' = [live EXCEPT ![b] = @ \cup {t}]
  /\ Advance(a, "BadShare", L0)
  /\ UNCHANGED <<phase, root, epoch, generation, staged, issued, cache,
                  observations>>

BadAbort(a) ==
  /\ UnsafeMode = "AbortLeak"
  /\ a \in Attempts /\ phase[a] = "Open" /\ live[a] # {}
  /\ phase' = [phase EXCEPT ![a] = "Aborted"]
  /\ staged' = staged \ ({a} \X Languages)
  /\ Advance(a, "BadAbort", L0)
  /\ UNCHANGED <<root, epoch, generation, live, issued, cache, observations>>

BadReset(a) ==
  /\ UnsafeMode = "ResetLeak"
  /\ a \in Attempts /\ phase[a] = "Open" /\ live[a] # {}
  /\ phase' = [phase EXCEPT ![a] = "Idle"]
  /\ root' = [root EXCEPT ![a] = NoRoot]
  /\ staged' = staged \ ({a} \X Languages)
  /\ Advance(a, "BadReset", L0)
  /\ UNCHANGED <<epoch, generation, live, issued, cache, observations>>

BadRevive(a, l) ==
  LET old == <<l, generation[a][l] - 1>> IN
  /\ UnsafeMode = "StaleRevival"
  /\ a \in Attempts /\ l \in Languages
  /\ phase[a] = "Open" /\ generation[a][l] > 0
  /\ old \in issued[a] /\ old \notin live[a]
  /\ live' = [live EXCEPT ![a] = @ \cup {old}]
  /\ Advance(a, "BadRevive", L0)
  /\ UNCHANGED <<phase, root, epoch, generation, staged, issued, cache,
                  observations>>

BadReplay(a, l, wrongRoot) ==
  /\ UnsafeMode = "ReplayDrift"
  /\ a \in Attempts /\ l \in Languages /\ wrongRoot \in Roots
  /\ phase[a] = "Open" /\ Token(a, l) \in live[a]
  /\ wrongRoot # root[a]
  /\ observations' = [observations EXCEPT
                      ![a] = @ \cup {<<l, root[a], Result(wrongRoot, l)>>}]
  /\ Advance(a, "BadReplay", L0)
  /\ UNCHANGED <<phase, root, epoch, generation, staged, live, issued, cache>>

BadCacheGrant(a, l) ==
  /\ UnsafeMode = "CacheGrantsAuthority"
  /\ a \in Attempts /\ l \in Languages
  /\ phase[a] = "Open" /\ Artifact(l) \in cache
  /\ Token(a, l) \notin issued[a]
  /\ live' = [live EXCEPT ![a] = @ \cup {Token(a, l)}]
  /\ Advance(a, "BadCacheGrant", L0)
  /\ UNCHANGED <<phase, root, epoch, generation, staged, issued, cache,
                  observations>>

BadCollateralRevoke(a, l, other) ==
  /\ UnsafeMode = "CollateralRevoke"
  /\ a \in Attempts /\ l \in Languages /\ other \in Languages
  /\ l # other /\ phase[a] = "Open"
  /\ Token(a, l) \in live[a] /\ Token(a, other) \in live[a]
  /\ generation[a][l] < MaxGeneration
  /\ live' = [live EXCEPT
              ![a] = @ \ {Token(a, l), Token(a, other)}]
  /\ generation' = [generation EXCEPT ![a][l] = @ + 1]
  /\ Advance(a, "Revoke", l)
  /\ UNCHANGED <<phase, root, epoch, staged, issued, cache, observations>>

IdleStep == UNCHANGED vars

Next ==
  \/ \E a \in Attempts, r \in Roots : Begin(a, r)
  \/ \E a \in Attempts, l \in Languages : Stage(a, l)
  \/ \E a \in Attempts : Commit(a) \/ Reject(a) \/ Abort(a) \/ Reset(a)
  \/ \E a \in Attempts, l \in Languages : Revoke(a, l) \/ Observe(a, l)
  \/ \E a \in Attempts, b \in Attempts, t \in TokenIds : BadShare(a, b, t)
  \/ \E a \in Attempts : BadAbort(a) \/ BadReset(a)
  \/ \E a \in Attempts, l \in Languages : BadRevive(a, l)
  \/ \E a \in Attempts, l \in Languages, r \in Roots : BadReplay(a, l, r)
  \/ \E a \in Attempts, l \in Languages : BadCacheGrant(a, l)
  \/ \E a \in Attempts, l \in Languages, other \in Languages :
       BadCollateralRevoke(a, l, other)
  \/ IdleStep

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ phase \in [Attempts -> Phases]
  /\ root \in [Attempts -> Roots \cup {NoRoot}]
  /\ epoch \in [Attempts -> 0..MaxEpoch]
  /\ generation \in [Attempts -> [Languages -> 0..MaxGeneration]]
  /\ staged \subseteq Attempts \X Languages
  /\ live \in [Attempts -> SUBSET TokenIds]
  /\ issued \in [Attempts -> SUBSET TokenIds]
  /\ cache \subseteq Artifacts
  /\ observations \in [Attempts -> SUBSET
                        (Languages \X Roots \X (Roots \X Languages))]
  /\ lastActor \in Attempts \cup {NoActor}
  /\ lastKind \in {"Init", "Begin", "Stage", "Commit", "Reject",
                   "Revoke", "Observe", "Abort", "Reset", "BadShare",
                   "BadAbort", "BadReset", "BadRevive", "BadReplay",
                   "BadCacheGrant"}
  /\ lastLanguage \in Languages
  /\ DOMAIN beforeLocal = Attempts
  /\ beforeCache \subseteq Artifacts

SiblingLocalStateStable ==
  lastActor # NoActor =>
    \A b \in Attempts : b # lastActor => LocalView(b) = beforeLocal[b]

CacheOnlyGrows == beforeCache \subseteq cache
CanonicalCacheContents == cache \subseteq Artifacts
StageAndRejectDoNotPublish ==
  lastKind \in {"Stage", "Reject"} =>
    /\ live[lastActor] = beforeLocal[lastActor][6]
    /\ issued[lastActor] = beforeLocal[lastActor][7]

InactiveHasNoAuthority ==
  \A a \in Attempts : phase[a] # "Open" =>
    /\ live[a] = {} /\ issued[a] = {}
    /\ StagedFor(a) = {} /\ observations[a] = {}

LiveWasLocallyIssued ==
  \A a \in Attempts : live[a] \subseteq issued[a]

LiveUsesCurrentGeneration ==
  \A a \in Attempts :
    \A t \in live[a] :
      /\ t[1] \in Languages
      /\ t[2] = generation[a][t[1]]

OtherLanguageUnaffectedByRevoke ==
  lastKind = "Revoke" =>
    \A l \in Languages : l # lastLanguage =>
      /\ generation[lastActor][l] = beforeLocal[lastActor][4][l]
      /\ {t \in live[lastActor] : t[1] = l} =
         {t \in beforeLocal[lastActor][6] : t[1] = l}

ObservationsAreRooted ==
  \A a \in Attempts :
    \A row \in observations[a] :
      /\ phase[a] = "Open"
      /\ row[2] = root[a]
      /\ row[3] = Result(root[a], row[1])

IndependentReplayAgrees ==
  \A a \in Attempts, b \in Attempts, l \in Languages :
    a # b /\ root[a] = root[b] /\ root[a] \in Roots
    /\ (\E left \in observations[a] : left[1] = l)
    /\ (\E right \in observations[b] : right[1] = l)
    =>
      {left[3] : left \in {row \in observations[a] : row[1] = l}} =
      {right[3] : right \in {row \in observations[b] : row[1] = l}}

====
