---- MODULE DerivationRank ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************
Canonical rank assembly for generated and runtime WPDA parsers.

The model separates a completed derivation from the order in which parser
workers discover it.  Two grammatical child slots may complete in either
order, the parent production may commit before, between, or after them, and
zero-cost synthetic factoring steps may occur anywhere.  Safe assembly reads
the grammatical slots and constructs the parent-before-child rank.  Unsafe
assembly instead exposes transition timing; its configuration must violate
FinalCanonicalRank, demonstrating that this model detects the historical
ordering defect.

A rank is a function from logical input positions to two-phase buckets.
Lexical evidence and completed productions are separate sequences, so every
lexical decision is observed before every production at the same position.
***************************************************************************)

CONSTANT UnsafeMode

Positions == 0..1
ChildIds == {1, 2}
LexicalChoices == {"host-open", "left-open", "right-token"}
ProductionRules == {"parent", "left", "right"}
CostCap == 3

EmptyBucket == [lexical |-> <<>>, productions |-> <<>>]
EmptyRank == [position \in Positions |-> EmptyBucket]

CombineBucket(left, right) ==
  [lexical |-> left.lexical \o right.lexical,
   productions |-> left.productions \o right.productions]

CombineRank(left, right) ==
  [position \in Positions |-> CombineBucket(left[position], right[position])]

LexicalRank(origin, decision) ==
  [position \in Positions |->
    IF position = origin
    THEN [lexical |-> <<decision>>, productions |-> <<>>]
    ELSE EmptyBucket]

ProductionRank(origin, rule) ==
  [position \in Positions |->
    IF position = origin
    THEN [lexical |-> <<>>, productions |-> <<rule>>]
    ELSE EmptyBucket]

LocalLexical == LexicalRank(0, "host-open")

ChildRanks ==
  [child \in ChildIds |->
    IF child = 1
    THEN CombineRank(LexicalRank(0, "left-open"),
                     ProductionRank(0, "left"))
    ELSE CombineRank(LexicalRank(1, "right-token"),
                     ProductionRank(1, "right"))]

(***************************************************************************
This left-to-right expression is the denotational counterpart of the
iterative child-slot fold proved equivalent in Rocq.
***************************************************************************)
CanonicalChildren == CombineRank(ChildRanks[1], ChildRanks[2])

CanonicalRank ==
  CombineRank(ProductionRank(0, "parent"),
    CombineRank(LocalLexical, CanonicalChildren))

SatAdd(left, right) ==
  IF left + right <= CostCap THEN left + right ELSE CostCap

ParentCost == 1
ChildCosts == [child \in ChildIds |-> 1]
CanonicalCost == SatAdd(ParentCost, SatAdd(ChildCosts[1], ChildCosts[2]))

BucketType == [lexical : Seq(LexicalChoices),
               productions : Seq(ProductionRules)]
RankType == [Positions -> BucketType]

VARIABLES
  phase,
  completedChildren,
  parentCommitted,
  completionTrace,
  timingRank,
  timingCost,
  factorDepth,
  resultRank,
  resultCost

vars ==
  <<phase, completedChildren, parentCommitted, completionTrace,
    timingRank, timingCost, factorDepth, resultRank, resultCost>>

Init ==
  /\ phase = "Running"
  /\ completedChildren = {}
  /\ parentCommitted = FALSE
  /\ completionTrace = <<>>
  /\ timingRank = LocalLexical
  /\ timingCost = 0
  /\ factorDepth = 0
  /\ resultRank = EmptyRank
  /\ resultCost = 0

CompleteChild(child) ==
  /\ phase = "Running"
  /\ child \in ChildIds \ completedChildren
  /\ completedChildren' = completedChildren \cup {child}
  /\ completionTrace' = Append(completionTrace, child)
  /\ timingRank' = CombineRank(timingRank, ChildRanks[child])
  /\ timingCost' = SatAdd(timingCost, ChildCosts[child])
  /\ UNCHANGED <<phase, parentCommitted, factorDepth,
                  resultRank, resultCost>>

CommitParent ==
  /\ phase = "Running"
  /\ ~parentCommitted
  /\ parentCommitted' = TRUE
  /\ timingRank' = CombineRank(timingRank, ProductionRank(0, "parent"))
  /\ timingCost' = SatAdd(timingCost, ParentCost)
  /\ UNCHANGED <<phase, completedChildren, completionTrace, factorDepth,
                  resultRank, resultCost>>

(***************************************************************************
Synthetic trie/spine nodes are administrative identities.  The bounded depth
keeps model checking finite; the Rocq proof covers every natural depth.
***************************************************************************)
SyntheticFactor ==
  /\ phase = "Running"
  /\ factorDepth < 2
  /\ factorDepth' = factorDepth + 1
  /\ timingRank' = CombineRank(EmptyRank, timingRank)
  /\ timingCost' = SatAdd(0, timingCost)
  /\ UNCHANGED <<phase, completedChildren, parentCommitted,
                  completionTrace, resultRank, resultCost>>

Assemble ==
  /\ phase = "Running"
  /\ completedChildren = ChildIds
  /\ parentCommitted
  /\ phase' = "Committed"
  /\ resultRank' = IF UnsafeMode THEN timingRank ELSE CanonicalRank
  /\ resultCost' = timingCost
  /\ UNCHANGED <<completedChildren, parentCommitted, completionTrace,
                  timingRank, timingCost, factorDepth>>

CommittedStep ==
  /\ phase = "Committed"
  /\ UNCHANGED vars

Next ==
  \/ \E child \in ChildIds : CompleteChild(child)
  \/ CommitParent
  \/ SyntheticFactor
  \/ Assemble
  \/ CommittedStep

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ phase \in {"Running", "Committed"}
  /\ completedChildren \subseteq ChildIds
  /\ parentCommitted \in BOOLEAN
  /\ completionTrace \in Seq(ChildIds)
  /\ timingRank \in RankType
  /\ timingCost \in 0..CostCap
  /\ factorDepth \in 0..2
  /\ resultRank \in RankType
  /\ resultCost \in 0..CostCap

FinalCanonicalRank ==
  phase = "Committed" => resultRank = CanonicalRank

Observation(bucket) ==
  [index \in DOMAIN bucket.lexical |->
    <<"Lexical", bucket.lexical[index]>>] \o
  [index \in DOMAIN bucket.productions |->
    <<"Production", bucket.productions[index]>>]

PhaseOrdered(bucket) ==
  LET observed == Observation(bucket) IN
  \A first, second \in DOMAIN observed :
    first < second /\ observed[first][1] = "Production"
      => observed[second][1] = "Production"

LexicalBeforeProduction ==
  phase = "Committed" =>
    \A position \in Positions : PhaseOrdered(resultRank[position])

OuterBeforeChildAtSharedOrigin ==
  phase = "Committed" =>
    resultRank[0].productions = <<"parent", "left">>

NoLostOrDuplicatedEvidence ==
  phase = "Committed" =>
    /\ resultRank[0].lexical = <<"host-open", "left-open">>
    /\ resultRank[0].productions = <<"parent", "left">>
    /\ resultRank[1].lexical = <<"right-token">>
    /\ resultRank[1].productions = <<"right">>

ScalarCostIndependent ==
  phase = "Committed" => resultCost = CanonicalCost

ScheduleIndependent ==
  phase = "Committed" =>
    /\ resultRank = CanonicalRank
    /\ completionTrace \in {<<1, 2>>, <<2, 1>>}

FactorizationTransparent ==
  phase = "Committed" =>
    /\ resultRank = CanonicalRank
    /\ resultCost = CanonicalCost

====
