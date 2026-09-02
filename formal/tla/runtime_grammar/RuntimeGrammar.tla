---- MODULE RuntimeGrammar ----
EXTENDS Naturals, FiniteSets, TLC

CoreFingerprint == 1
StaticParserEpoch == 7
Descriptors == 0..4
Reachable == {0, 1, 2, 3}

Successors ==
  [descriptor \in Descriptors |->
    CASE descriptor = 0 -> {1, 2}
      [] descriptor = 1 -> {3}
      [] descriptor = 2 -> {3}
      [] OTHER -> {}]

VARIABLES
  phase,
  cacheFingerprint,
  snapshotFingerprint,
  imageFingerprint,
  imageVerified,
  staleRejected,
  pending,
  seen,
  forest,
  registryLoads,
  filesystemLoads,
  staticParserEpoch

vars ==
  <<phase, cacheFingerprint, snapshotFingerprint, imageFingerprint,
    imageVerified, staleRejected, pending, seen, forest, registryLoads,
    filesystemLoads, staticParserEpoch>>

Init ==
  /\ phase = "Ready"
  /\ cacheFingerprint \in {0, CoreFingerprint}
  /\ snapshotFingerprint = 0
  /\ imageFingerprint = 0
  /\ imageVerified = FALSE
  /\ staleRejected = FALSE
  /\ pending = {}
  /\ seen = {}
  /\ forest = {}
  /\ registryLoads = 0
  /\ filesystemLoads = 0
  /\ staticParserEpoch = StaticParserEpoch

LoadRegistry ==
  /\ phase = "Ready"
  /\ phase' = "Snapshot"
  /\ snapshotFingerprint' = CoreFingerprint
  /\ registryLoads' = registryLoads + 1
  /\ UNCHANGED <<cacheFingerprint, imageFingerprint, imageVerified,
                  staleRejected, pending, seen, forest, filesystemLoads,
                  staticParserEpoch>>

RejectStaleCache ==
  /\ phase = "Snapshot"
  /\ cacheFingerprint # snapshotFingerprint
  /\ phase' = "Compiling"
  /\ staleRejected' = TRUE
  /\ UNCHANGED <<cacheFingerprint, snapshotFingerprint, imageFingerprint,
                  imageVerified, pending, seen, forest, registryLoads,
                  filesystemLoads, staticParserEpoch>>

CompileAndVerify ==
  /\ phase = "Compiling"
  /\ phase' = "Parsing"
  /\ imageFingerprint' = snapshotFingerprint
  /\ imageVerified' = TRUE
  /\ pending' = {0}
  /\ UNCHANGED <<cacheFingerprint, snapshotFingerprint, staleRejected,
                  seen, forest, registryLoads, filesystemLoads,
                  staticParserEpoch>>

InstallCached ==
  /\ phase = "Snapshot"
  /\ cacheFingerprint = snapshotFingerprint
  /\ phase' = "Parsing"
  /\ imageFingerprint' = cacheFingerprint
  /\ imageVerified' = TRUE
  /\ pending' = {0}
  /\ UNCHANGED <<cacheFingerprint, snapshotFingerprint, staleRejected,
                  seen, forest, registryLoads, filesystemLoads,
                  staticParserEpoch>>

Process(descriptor) ==
  /\ phase = "Parsing"
  /\ descriptor \in pending
  /\ seen' = seen \cup {descriptor}
  /\ pending' =
       (pending \ {descriptor}) \cup
       (Successors[descriptor] \ (seen \cup pending))
  /\ forest' = forest \cup {descriptor}
  /\ UNCHANGED <<phase, cacheFingerprint, snapshotFingerprint,
                  imageFingerprint, imageVerified, staleRejected,
                  registryLoads, filesystemLoads, staticParserEpoch>>

Work == \E descriptor \in Descriptors : Process(descriptor)

Finish ==
  /\ phase = "Parsing"
  /\ pending = {}
  /\ phase' = "Done"
  /\ UNCHANGED <<cacheFingerprint, snapshotFingerprint, imageFingerprint,
                  imageVerified, staleRejected, pending, seen, forest,
                  registryLoads, filesystemLoads, staticParserEpoch>>

DoneStep ==
  /\ phase = "Done"
  /\ UNCHANGED vars

Next ==
  \/ LoadRegistry
  \/ RejectStaleCache
  \/ CompileAndVerify
  \/ InstallCached
  \/ Work
  \/ Finish
  \/ DoneStep

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(LoadRegistry)
  /\ WF_vars(RejectStaleCache)
  /\ WF_vars(CompileAndVerify)
  /\ WF_vars(InstallCached)
  /\ WF_vars(Work)
  /\ WF_vars(Finish)

TypeOK ==
  /\ phase \in {"Ready", "Snapshot", "Compiling", "Parsing", "Done"}
  /\ cacheFingerprint \in {0, CoreFingerprint}
  /\ snapshotFingerprint \in {0, CoreFingerprint}
  /\ imageFingerprint \in {0, CoreFingerprint}
  /\ imageVerified \in BOOLEAN
  /\ staleRejected \in BOOLEAN
  /\ pending \subseteq Descriptors
  /\ seen \subseteq Descriptors
  /\ forest \subseteq Descriptors
  /\ registryLoads \in Nat
  /\ filesystemLoads \in Nat
  /\ staticParserEpoch \in Nat

VerifiedInstallation ==
  phase \in {"Parsing", "Done"} =>
    /\ imageVerified
    /\ imageFingerprint = snapshotFingerprint
    /\ snapshotFingerprint = CoreFingerprint

StaleCacheNeverInstalled ==
  staleRejected /\ imageVerified =>
    /\ cacheFingerprint # imageFingerprint
    /\ imageFingerprint = CoreFingerprint

WorklistDisjoint == (seen \cap pending) = {}

ReachabilitySound == seen \subseteq Reachable

ForestMatchesProcessedDescriptors == forest = seen

StaticParserNoninterference == staticParserEpoch = StaticParserEpoch

RegistryLoadingDoesNotUseFilesystem ==
  /\ registryLoads <= 1
  /\ filesystemLoads = 0

EventuallyDone == <> (phase = "Done")

====
