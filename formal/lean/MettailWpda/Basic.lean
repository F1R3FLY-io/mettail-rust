import Mathlib.Data.Nat.Basic

set_option linter.style.header false

/-!
Auxiliary Lean checks for the Prattail WPDA runtime quotient.
-/

namespace MettailWpda

inductive Control where
  | prefixDispatch
  | infixChainIterative
  | crossCatDelegate
  | ambiguityFanout
  | unwinding
  | done
  | error
  deriving DecidableEq, Repr

structure EquivKey where
  source : Nat
  bp : Nat
  deriving DecidableEq, Repr

structure DispatchKey where
  pos : Nat
  source : Nat
  bp : Nat
  wrapCat : Nat
  wrapRule : Nat
  deriving DecidableEq, Repr

def equivOfDispatch (d : DispatchKey) : EquivKey :=
  { source := d.source, bp := d.bp }

structure ConfigKey where
  control : Control
  node : Nat
  pos : Nat
  incomingEdge : Option Nat
  incomingEdgeStack : Nat
  collectionDepth : Nat
  origin : Option EquivKey
  sppfTop : Option Nat
  lexAlt : Nat
  weightSrc : Nat
  weightRule : Nat
  lexStamp : Option Nat
  deriving DecidableEq, Repr

def withCohortOrigin (base : ConfigKey) (d : DispatchKey) : ConfigKey :=
  { base with origin := some (equivOfDispatch d) }

def withLexStamp (base : ConfigKey) (stamp : Nat) : ConfigKey :=
  { base with lexStamp := some stamp }

def lexForkChildConfig (base : ConfigKey) (stamp nextPos : Nat) : ConfigKey :=
  { withLexStamp base stamp with pos := nextPos }

def withIncomingEdgeStack (base : ConfigKey) (stack : Nat) : ConfigKey :=
  { base with incomingEdgeStack := stack }

theorem withIncomingEdgeStackSetsStack
    (base : ConfigKey)
    (stack : Nat) :
    (withIncomingEdgeStack base stack).incomingEdgeStack = stack := by
  rfl

theorem differentIncomingEdgeStacks_preventMerge
    {c1 c2 : ConfigKey} :
    c1.incomingEdgeStack ≠ c2.incomingEdgeStack ->
    c1 ≠ c2 := by
  intro hdiff heq
  apply hdiff
  rw [heq]

inductive LexAltOperatorAction where
  | postfix
  | infix
  | mixfix
  deriving DecidableEq, Repr

def runtimeLexAltOperatorChild
    (_action : LexAltOperatorAction)
    (parent : ConfigKey)
    (stamp nextPos : Nat) : ConfigKey :=
  lexForkChildConfig parent stamp nextPos

theorem lexAltOperatorChildAdvancesToNextPos
    (action : LexAltOperatorAction)
    (parent : ConfigKey)
    (stamp nextPos : Nat) :
    (runtimeLexAltOperatorChild action parent stamp nextPos).pos = nextPos := by
  rfl

theorem lexAltOperatorChildRecordsStamp
    (action : LexAltOperatorAction)
    (parent : ConfigKey)
    (stamp nextPos : Nat) :
    (runtimeLexAltOperatorChild action parent stamp nextPos).lexStamp = some stamp := by
  rfl

def cohortReturnFrameWithLexStamp (parent : ConfigKey) (stamp : Nat) : ConfigKey :=
  withLexStamp parent stamp

theorem pausedCohortReturnFrameRecordsLexStamp
    (parent : ConfigKey)
    (stamp : Nat) :
    (cohortReturnFrameWithLexStamp parent stamp).lexStamp = some stamp := by
  rfl

def lexForkOnlySecondarySurvived
    (branchesNonempty primarySurvived : Bool) : Bool :=
  branchesNonempty && !primarySurvived

def lexForkFallThrough
    (branchesEmpty primaryOnlySurvived primaryHasDispatchRule
      onlySecondarySurvived : Bool) : Bool :=
  branchesEmpty ||
    primaryOnlySurvived ||
      (onlySecondarySurvived && primaryHasDispatchRule)

theorem lexForkOnlySecondaryWhenNonemptyWithoutPrimary :
    lexForkOnlySecondarySurvived true false = true := by
  rfl

theorem lexForkFallsThroughWhenOnlySecondaryAndPrimaryHasDispatch :
    lexForkFallThrough false false true true = true := by
  rfl

theorem lexForkDoesNotFallThroughForSecondaryWithoutPrimaryDispatch :
    lexForkFallThrough false false false true = false := by
  rfl

theorem lexForkFallThroughOnlySecondaryMatchesPrimaryDispatch
    (primaryHasDispatchRule : Bool) :
    lexForkFallThrough false false primaryHasDispatchRule true =
      primaryHasDispatchRule := by
  cases primaryHasDispatchRule <;> rfl

theorem lexForkFallsThroughWhenNoBranches :
    lexForkFallThrough true false false false = true := by
  rfl

theorem lexForkFallsThroughWhenOnlyPrimarySurvived :
    lexForkFallThrough false true false false = true := by
  rfl

inductive EdgeKind where
  | generic
  | crossCatProjection
      (source : Nat) (bp : Nat) (wrapCat : Nat) (wrapRule : Nat)
  | crossCatLhs (source : Nat)
  | crossCatLhsReentry (source : Nat)
  | other (tag : Nat)
  deriving DecidableEq, Repr

def edgeKindOfDispatch (d : DispatchKey) : EdgeKind :=
  EdgeKind.crossCatProjection d.source d.bp d.wrapCat d.wrapRule

theorem equivOfDispatch_ignoresPosAndWrap
    (p1 p2 source bp wc1 wr1 wc2 wr2 : Nat) :
    equivOfDispatch
      { pos := p1, source := source, bp := bp, wrapCat := wc1, wrapRule := wr1 }
    =
    equivOfDispatch
      { pos := p2, source := source, bp := bp, wrapCat := wc2, wrapRule := wr2 } := by
  rfl

theorem dispatchKeyEq_preservesFullPosition
    {d1 d2 : DispatchKey} :
    d1 = d2 ->
    d1.pos = d2.pos := by
  intro h
  rw [h]

example :
    ({ pos := 0, source := 1, bp := 2, wrapCat := 3, wrapRule := 4 } : DispatchKey) ≠
    ({ pos := 4294967296, source := 1, bp := 2, wrapCat := 3, wrapRule := 4 } : DispatchKey) := by
  decide

def packedDispatchPosLimit : Nat := 2 ^ 40

def packedDispatchPositionValid (pos : Nat) : Prop :=
  pos < packedDispatchPosLimit

def packedDispatchPositionBits (pos : Nat) : Nat :=
  pos % packedDispatchPosLimit

theorem packedDispatchPositionBitsPreserveValid
    {pos : Nat} :
    packedDispatchPositionValid pos ->
    packedDispatchPositionBits pos = pos := by
  intro hvalid
  exact Nat.mod_eq_of_lt hvalid

theorem packedDispatchPositionBitsInjectiveValid
    {pos1 pos2 : Nat} :
    packedDispatchPositionValid pos1 ->
    packedDispatchPositionValid pos2 ->
    packedDispatchPositionBits pos1 = packedDispatchPositionBits pos2 ->
    pos1 = pos2 := by
  intro hvalid1 hvalid2 hbits
  rw [packedDispatchPositionBitsPreserveValid hvalid1] at hbits
  rw [packedDispatchPositionBitsPreserveValid hvalid2] at hbits
  exact hbits

theorem packedDispatchPositionLimitInvalid :
    ¬ packedDispatchPositionValid packedDispatchPosLimit := by
  simp [packedDispatchPositionValid]

example :
    ({ pos := 0, source := 1, bp := 2, wrapCat := 3, wrapRule := 4 } : DispatchKey) ≠
    ({ pos := packedDispatchPosLimit, source := 1, bp := 2, wrapCat := 3, wrapRule := 4 } :
      DispatchKey) := by
  decide

theorem crossCatEdgeEq_preservesWrap
    {source bp wc1 wr1 wc2 wr2 : Nat} :
    EdgeKind.crossCatProjection source bp wc1 wr1 =
      EdgeKind.crossCatProjection source bp wc2 wr2 ->
    wc1 = wc2 ∧ wr1 = wr2 := by
  intro h
  injection h with _ _ hWrapCat hWrapRule
  exact ⟨hWrapCat, hWrapRule⟩

theorem dispatchEdgeEq_preservesWrap
    {d1 d2 : DispatchKey} :
    edgeKindOfDispatch d1 = edgeKindOfDispatch d2 ->
    d1.wrapCat = d2.wrapCat ∧ d1.wrapRule = d2.wrapRule := by
  cases d1
  cases d2
  intro h
  simp [edgeKindOfDispatch] at h
  simpa using h.2.2

theorem crossCatLhsEdgeEq_preservesSource
    {s1 s2 : Nat} :
    EdgeKind.crossCatLhs s1 = EdgeKind.crossCatLhs s2 ->
    s1 = s2 := by
  intro h
  cases h
  rfl

theorem crossCatLhsReentryEdgeEq_preservesSource
    {s1 s2 : Nat} :
    EdgeKind.crossCatLhsReentry s1 = EdgeKind.crossCatLhsReentry s2 ->
    s1 = s2 := by
  intro h
  cases h
  rfl

def lhsReentryAfterPop : EdgeKind -> Option EdgeKind
  | .crossCatLhs source => some (.crossCatLhsReentry source)
  | _ => none

theorem crossCatLhsPopReentersOnce
    (source : Nat) :
    lhsReentryAfterPop (.crossCatLhs source) =
      some (.crossCatLhsReentry source) := by
  rfl

theorem crossCatLhsReentryIsOneShot
    (source : Nat) :
    lhsReentryAfterPop (.crossCatLhsReentry source) = none := by
  rfl

def crossCatLhsInfixEvidence (edge : EdgeKind) (topCat : Nat) : Option Nat :=
  match edge with
  | .crossCatLhs source
  | .crossCatLhsReentry source =>
      if source = topCat then some source else none
  | _ => none

def categoryChangingInfix (sourceCat resultCat : Nat) : Bool :=
  decide (sourceCat ≠ resultCat)

def categoryChangingInfixAllowed
    (edge : EdgeKind)
    (topCat sourceCat resultCat : Nat) : Bool :=
  if categoryChangingInfix sourceCat resultCat then
    match crossCatLhsInfixEvidence edge topCat with
    | some witnessedSource => decide (witnessedSource = sourceCat)
    | none => false
  else
    true

theorem sameCategoryInfixNeedsNoLhsEvidence
    (edge : EdgeKind)
    (topCat sourceCat : Nat) :
    categoryChangingInfixAllowed edge topCat sourceCat sourceCat = true := by
  simp [categoryChangingInfixAllowed, categoryChangingInfix]

theorem categoryChangingInfixRequiresLhsEvidence
    {edge : EdgeKind}
    {topCat sourceCat resultCat : Nat} :
    categoryChangingInfix sourceCat resultCat = true ->
    categoryChangingInfixAllowed edge topCat sourceCat resultCat = true ->
    crossCatLhsInfixEvidence edge topCat = some sourceCat := by
  intro hchanging hallowed
  unfold categoryChangingInfixAllowed at hallowed
  rw [hchanging] at hallowed
  cases hev : crossCatLhsInfixEvidence edge topCat with
  | none =>
      rw [hev] at hallowed
      cases hallowed
  | some witnessedSource =>
      rw [hev] at hallowed
      have hwitness : witnessedSource = sourceCat := of_decide_eq_true hallowed
      exact congrArg some hwitness

theorem genericEdgeRejectsCategoryChangingInfix
    {topCat sourceCat resultCat : Nat} :
    categoryChangingInfix sourceCat resultCat = true ->
    categoryChangingInfixAllowed
      .generic topCat sourceCat resultCat = false := by
  intro hchanging
  simp [categoryChangingInfixAllowed, hchanging, crossCatLhsInfixEvidence]

theorem dispatchKeysWithSameSourceBp_shareOrigin
    (base : ConfigKey)
    (p1 p2 source bp wc1 wr1 wc2 wr2 : Nat) :
    withCohortOrigin base
      { pos := p1, source := source, bp := bp, wrapCat := wc1, wrapRule := wr1 }
    =
    withCohortOrigin base
      { pos := p2, source := source, bp := bp, wrapCat := wc2, wrapRule := wr2 } := by
  rfl

theorem differentSppfTops_preventMerge
    {c1 c2 : ConfigKey} :
    c1.sppfTop ≠ c2.sppfTop ->
    c1 ≠ c2 := by
  intro hdiff heq
  apply hdiff
  rw [heq]

theorem differentLexStamps_preventMerge
    {c1 c2 : ConfigKey} :
    c1.lexStamp ≠ c2.lexStamp ->
    c1 ≠ c2 := by
  intro hdiff heq
  apply hdiff
  rw [heq]

inductive TokenClass where
  | openDelimiter
  | closeDelimiter
  | other
  deriving DecidableEq, Repr

def isOpenDelimiter : TokenClass -> Bool
  | .openDelimiter => true
  | _ => false

def isCloseDelimiter : TokenClass -> Bool
  | .closeDelimiter => true
  | _ => false

def tokenWindow
    (tokens : List TokenClass)
    (start finish : Nat) : List TokenClass :=
  (tokens.drop start).take (finish - start)

def allOpenPrefix (tokens : List TokenClass) (finish : Nat) : Bool :=
  decide (finish <= tokens.length) &&
    (tokens.take finish).all isOpenDelimiter

def allCloseWindow
    (tokens : List TokenClass)
    (start finish : Nat) : Bool :=
  decide (finish <= tokens.length) &&
    (tokenWindow tokens start finish).all isCloseDelimiter

def eoiAcceptsSemanticRoot
    (tokens : List TokenClass)
    (rootLo rootHi cursorPos : Nat) : Bool :=
  decide (cursorPos <= tokens.length) &&
    (rootHi == cursorPos ||
      (decide (rootHi < cursorPos) &&
        allOpenPrefix tokens rootLo &&
        allCloseWindow tokens rootHi cursorPos))

theorem sameSpanAcceptsWithoutDelimiterWindows
    (tokens : List TokenClass)
    (rootLo rootHi : Nat) :
    rootHi <= tokens.length ->
    eoiAcceptsSemanticRoot tokens rootLo rootHi rootHi = true := by
  intro hlen
  simp [eoiAcceptsSemanticRoot, hlen]

theorem delimiterSuffixRejectsNonOpenPrefix
    {tokens : List TokenClass}
    {rootLo rootHi cursorPos : Nat} :
    rootHi < cursorPos ->
    allOpenPrefix tokens rootLo = false ->
    eoiAcceptsSemanticRoot tokens rootLo rootHi cursorPos = false := by
  intro hlt hprefix
  simp [eoiAcceptsSemanticRoot, hlt, Nat.ne_of_lt hlt, hprefix]

theorem delimiterWrappedRootAccepts
    {tokens : List TokenClass}
    {rootLo rootHi cursorPos : Nat} :
    cursorPos <= tokens.length ->
    rootHi < cursorPos ->
    allOpenPrefix tokens rootLo = true ->
    allCloseWindow tokens rootHi cursorPos = true ->
    eoiAcceptsSemanticRoot tokens rootLo rootHi cursorPos = true := by
  intro hpos hlt hprefix hsuffix
  simp [eoiAcceptsSemanticRoot, hpos, hlt, hprefix, hsuffix]

theorem delimiterSuffixAcceptRequiresOpenPrefix
    {tokens : List TokenClass}
    {rootLo rootHi cursorPos : Nat} :
    rootHi ≠ cursorPos ->
    eoiAcceptsSemanticRoot tokens rootLo rootHi cursorPos = true ->
    allOpenPrefix tokens rootLo = true := by
  intro hneq haccept
  by_cases hlt : rootHi < cursorPos
  · have hparts :
        cursorPos <= tokens.length ∧
          allOpenPrefix tokens rootLo = true ∧
          allCloseWindow tokens rootHi cursorPos = true := by
      simpa [eoiAcceptsSemanticRoot, hneq, hlt] using haccept
    cases hprefix : allOpenPrefix tokens rootLo
    · simp [hprefix] at hparts
    · rfl
  · exfalso
    simp [eoiAcceptsSemanticRoot, hneq, hlt] at haccept

example :
    eoiAcceptsSemanticRoot
      [.openDelimiter, .other, .closeDelimiter] 2 2 3 = false := by
  rfl

example :
    eoiAcceptsSemanticRoot
      [.openDelimiter, .other, .closeDelimiter] 3 4 4 = false := by
  rfl

example :
    eoiAcceptsSemanticRoot
      [.openDelimiter, .other] 1 2 3 = false := by
  rfl

inductive TokenPositionSpace where
  | linearTokenPositions
  | nonlinearNodePositions
  deriving DecidableEq, Repr

def runtimeEoiAcceptsSemanticRoot
    (space : TokenPositionSpace)
    (tokens : List TokenClass)
    (rootLo rootHi cursorPos : Nat) : Bool :=
  match space with
  | .linearTokenPositions =>
      eoiAcceptsSemanticRoot tokens rootLo rootHi cursorPos
  | .nonlinearNodePositions =>
      true

theorem linearRuntimeEoiAcceptanceIsDelimiterWindowAcceptance
    (tokens : List TokenClass)
    (rootLo rootHi cursorPos : Nat) :
    runtimeEoiAcceptsSemanticRoot
      .linearTokenPositions tokens rootLo rootHi cursorPos =
    eoiAcceptsSemanticRoot tokens rootLo rootHi cursorPos := by
  rfl

theorem nonlinearNodePositionsDoNotScanNumericTokenWindows
    (tokens : List TokenClass)
    (rootLo rootHi cursorPos : Nat) :
    runtimeEoiAcceptsSemanticRoot
      .nonlinearNodePositions tokens rootLo rootHi cursorPos = true := by
  rfl

inductive CursorBoundingMode where
  | unbounded
  | beamSize (budget : Nat)
  | ambiguityBudget (budget : Nat)
  deriving DecidableEq, Repr

def cursorBoundBudget : CursorBoundingMode -> Option Nat
  | .unbounded => none
  | .beamSize budget => some budget
  | .ambiguityBudget budget => some budget

def cursorBoundCheck
    (mode : CursorBoundingMode)
    (actualFrontierLen : Nat) : Option (Nat × Nat) :=
  match cursorBoundBudget mode with
  | none => none
  | some budget =>
      if budget < actualFrontierLen
      then some (budget, actualFrontierLen)
      else none

def cursorBoundFrontierLen
    (_mode : CursorBoundingMode)
    (actualFrontierLen : Nat) : Nat :=
  actualFrontierLen

theorem beamSizeMatchesAmbiguityBudget
    (budget actualFrontierLen : Nat) :
    cursorBoundCheck (.beamSize budget) actualFrontierLen =
      cursorBoundCheck (.ambiguityBudget budget) actualFrontierLen := by
  rfl

theorem beamSizeOverflowReportsActual
    {budget actualFrontierLen : Nat} :
    budget < actualFrontierLen ->
    cursorBoundCheck (.beamSize budget) actualFrontierLen =
      some (budget, actualFrontierLen) := by
  intro h
  simp [cursorBoundCheck, cursorBoundBudget, h]

theorem beamSizeWithinBudgetReportsNoError
    {budget actualFrontierLen : Nat} :
    actualFrontierLen <= budget ->
    cursorBoundCheck (.beamSize budget) actualFrontierLen = none := by
  intro h
  have hnot : ¬ budget < actualFrontierLen := Nat.not_lt.mpr h
  simp [cursorBoundCheck, cursorBoundBudget, hnot]

theorem cursorBoundPreservesFrontierLength
    (mode : CursorBoundingMode)
    (actualFrontierLen : Nat) :
    cursorBoundFrontierLen mode actualFrontierLen = actualFrontierLen := by
  rfl

theorem beamSizePreservesFrontierLength
    (budget actualFrontierLen : Nat) :
    cursorBoundFrontierLen (.beamSize budget) actualFrontierLen =
      actualFrontierLen := by
  rfl

structure WeightedFrontierItem where
  weight : Nat
  node : Nat
  deriving DecidableEq, Repr

def frontierMinimal
    (picked : WeightedFrontierItem)
    (frontier : List WeightedFrontierItem) : Prop :=
  picked ∈ frontier ∧
    ∀ item, item ∈ frontier -> picked.weight <= item.weight

def lazyForceStep
    (frontier forced : List WeightedFrontierItem) : Prop :=
  forced.length <= 1 ∧
    ∀ item, item ∈ forced -> item ∈ frontier

def priorityForceStep
    (frontier forced : List WeightedFrontierItem) : Prop :=
  lazyForceStep frontier forced ∧
    ∀ picked, forced = [picked] -> frontierMinimal picked frontier

theorem singletonForceIsLazy
    {frontier : List WeightedFrontierItem}
    {picked : WeightedFrontierItem} :
    picked ∈ frontier ->
    lazyForceStep frontier [picked] := by
  intro hin
  constructor
  · simp
  · intro item hitem
    have hitem_eq : item = picked := by
      simpa using hitem
    rw [hitem_eq]
    exact hin

theorem emptyForceIsLazy
    (frontier : List WeightedFrontierItem) :
    lazyForceStep frontier [] := by
  simp [lazyForceStep]

theorem priorityForceNoBetterRemaining
    {frontier : List WeightedFrontierItem}
    {picked item : WeightedFrontierItem} :
    priorityForceStep frontier [picked] ->
    item ∈ frontier ->
    picked.weight <= item.weight := by
  intro hstep hin
  rcases hstep with ⟨_, hminimal⟩
  exact (hminimal picked rfl).2 item hin

theorem priorityForcePreservesAmbiguityUntilDemand
    {frontier forced : List WeightedFrontierItem}
    {item : WeightedFrontierItem} :
    priorityForceStep frontier forced ->
    item ∈ forced ->
    item ∈ frontier := by
  intro hstep hin
  exact hstep.1.2 item hin

def normalizeRecoveryBeamWidth : Option Int -> Option Int
  | none => none
  | some width =>
      if 0 <= width then some width else none

theorem negativeRecoveryBeamWidthIsDisabled
    {width : Int} :
    width < 0 ->
    normalizeRecoveryBeamWidth (some width) = none := by
  intro h
  have hnot : ¬ 0 <= width := by
    intro hle
    exact (Int.not_lt_of_ge hle) h
  simp [normalizeRecoveryBeamWidth, hnot]

theorem nonnegativeRecoveryBeamWidthIsPreserved
    {width : Int} :
    0 <= width ->
    normalizeRecoveryBeamWidth (some width) = some width := by
  intro h
  simp [normalizeRecoveryBeamWidth, h]

def normalizeRecoveryWeight (default value : Int) : Int :=
  if 0 <= value then value else default

theorem negativeRecoveryWeightUsesDefault
    {default value : Int} :
    value < 0 ->
    normalizeRecoveryWeight default value = default := by
  intro h
  have hnot : ¬ 0 <= value := by
    intro hle
    exact (Int.not_lt_of_ge hle) h
  simp [normalizeRecoveryWeight, hnot]

theorem nonnegativeRecoveryWeightIsPreserved
    {default value : Int} :
    0 <= value ->
    normalizeRecoveryWeight default value = value := by
  intro h
  simp [normalizeRecoveryWeight, h]

theorem normalizedRecoveryWeightIsNonnegative
    {default value : Int} :
    0 <= default ->
    0 <= normalizeRecoveryWeight default value := by
  intro hdefault
  unfold normalizeRecoveryWeight
  by_cases hvalue : 0 <= value
  · simp [hvalue]
  · simp [hvalue, hdefault]

def recoveryWindowLen (tokenCount pos : Nat) : Option Nat :=
  if pos <= tokenCount
  then some (tokenCount - pos)
  else none

theorem recoveryWindowPastInputIsNone
    {tokenCount pos : Nat} :
    tokenCount < pos ->
    recoveryWindowLen tokenCount pos = none := by
  intro h
  have hnot : ¬ pos <= tokenCount := Nat.not_le_of_gt h
  simp [recoveryWindowLen, hnot]

theorem recoveryWindowAtEofIsEmpty
    (tokenCount : Nat) :
    recoveryWindowLen tokenCount tokenCount = some 0 := by
  simp [recoveryWindowLen]

theorem recoveryWindowInBoundsHasSuffixLength
    {tokenCount pos : Nat} :
    pos <= tokenCount ->
    recoveryWindowLen tokenCount pos = some (tokenCount - pos) := by
  intro h
  simp [recoveryWindowLen, h]

def recoveryForkMaxBranches : Nat := 8

def synthesizedRecoveryCandidateCount (singleStep multiStep : Bool) : Nat :=
  (if singleStep then 1 else 0) + (if multiStep then 1 else 0)

theorem synthesizedRecoveryCandidateCountLeBranchCap
    (singleStep multiStep : Bool) :
    synthesizedRecoveryCandidateCount singleStep multiStep <=
      recoveryForkMaxBranches := by
  cases singleStep <;> cases multiStep <;>
    simp [synthesizedRecoveryCandidateCount, recoveryForkMaxBranches]

structure RecoveryConfig where
  skipPerTokenBits : Nat
  deleteCostBits : Nat
  substituteCostBits : Nat
  insertCostBits : Nat
  swapCostBits : Nat
  maxSkipLookahead : Nat
  deepNestingThreshold : Nat
  deepNestingSkipMultBits : Nat
  shallowDepthThreshold : Nat
  shallowDepthSkipMultBits : Nat
  lowBpThreshold : Nat
  lowBpSkipMultBits : Nat
  collectionInsertMultBits : Nat
  groupInsertMultBits : Nat
  bracketInsertMultBits : Nat
  mixfixSubstituteMultBits : Nat
  beamWidthBits : Option Nat
  vpaNestingCeiling : Option Nat
  maxRecoveryDepth : Nat
  deriving DecidableEq, Repr

def recoverySynthesisEnabled (cfg : RecoveryConfig) : Prop :=
  0 < cfg.maxRecoveryDepth

theorem maxRecoveryDepthZero_disablesSynthesis
    {cfg : RecoveryConfig} :
    cfg.maxRecoveryDepth = 0 ->
    ¬ recoverySynthesisEnabled cfg := by
  intro hdepth henabled
  simp [recoverySynthesisEnabled, hdepth] at henabled

theorem positiveMaxRecoveryDepth_enablesSynthesis
    {cfg : RecoveryConfig} :
    0 < cfg.maxRecoveryDepth ->
    recoverySynthesisEnabled cfg := by
  intro hdepth
  exact hdepth

structure RecoveryConfigSignature where
  skipPerTokenBits : Nat
  deleteCostBits : Nat
  substituteCostBits : Nat
  insertCostBits : Nat
  swapCostBits : Nat
  maxSkipLookahead : Nat
  deepNestingThreshold : Nat
  deepNestingSkipMultBits : Nat
  shallowDepthThreshold : Nat
  shallowDepthSkipMultBits : Nat
  lowBpThreshold : Nat
  lowBpSkipMultBits : Nat
  collectionInsertMultBits : Nat
  groupInsertMultBits : Nat
  bracketInsertMultBits : Nat
  mixfixSubstituteMultBits : Nat
  beamWidthBits : Option Nat
  vpaNestingCeiling : Option Nat
  maxRecoveryDepth : Nat
  deriving DecidableEq, Repr

def recoveryConfigSignatureOf (cfg : RecoveryConfig) : RecoveryConfigSignature :=
  { skipPerTokenBits := cfg.skipPerTokenBits,
    deleteCostBits := cfg.deleteCostBits,
    substituteCostBits := cfg.substituteCostBits,
    insertCostBits := cfg.insertCostBits,
    swapCostBits := cfg.swapCostBits,
    maxSkipLookahead := cfg.maxSkipLookahead,
    deepNestingThreshold := cfg.deepNestingThreshold,
    deepNestingSkipMultBits := cfg.deepNestingSkipMultBits,
    shallowDepthThreshold := cfg.shallowDepthThreshold,
    shallowDepthSkipMultBits := cfg.shallowDepthSkipMultBits,
    lowBpThreshold := cfg.lowBpThreshold,
    lowBpSkipMultBits := cfg.lowBpSkipMultBits,
    collectionInsertMultBits := cfg.collectionInsertMultBits,
    groupInsertMultBits := cfg.groupInsertMultBits,
    bracketInsertMultBits := cfg.bracketInsertMultBits,
    mixfixSubstituteMultBits := cfg.mixfixSubstituteMultBits,
    beamWidthBits := cfg.beamWidthBits,
    vpaNestingCeiling := cfg.vpaNestingCeiling,
    maxRecoveryDepth := cfg.maxRecoveryDepth }

structure RecoveryDepthObservation where
  deep : Bool
  shallow : Bool
  vpaOver : Bool
  deriving DecidableEq, Repr

def observeRecoveryDepth (cfg : RecoveryConfig) (depth : Nat) :
    RecoveryDepthObservation :=
  { deep := cfg.deepNestingThreshold < depth,
    shallow := depth < cfg.shallowDepthThreshold,
    vpaOver :=
      match cfg.vpaNestingCeiling with
      | some ceiling => ceiling < depth
      | none => false }

structure RecoveryWfstSignature where
  tokenIds : List (Nat × Nat)
  syncTokens : List Nat
  predictionDiscounts : List (Nat × Nat)
  bracketMismatchIds : List Nat
  recursiveCategory : Bool
  deriving DecidableEq, Repr

structure RecoveryInfraSignature where
  tokenIds : List (Nat × Nat)
  syncTokens : List Nat
  config : RecoveryConfigSignature
  wfst : RecoveryWfstSignature
  deriving DecidableEq, Repr

def recoveryInfraSignatureWithActiveConfig
    (tokenIds : List (Nat × Nat))
    (syncTokens : List Nat)
    (wfst : RecoveryWfstSignature)
    (cfg : RecoveryConfig) : RecoveryInfraSignature :=
  { tokenIds := tokenIds,
    syncTokens := syncTokens,
    config := recoveryConfigSignatureOf cfg,
    wfst := wfst }

theorem activeConfigSignature_observesMaxRecoveryDepth
    (cfg : RecoveryConfig) :
    (recoveryConfigSignatureOf cfg).maxRecoveryDepth =
    cfg.maxRecoveryDepth := by
  rfl

theorem equalActiveConfigSignature_preservesDepthObservation
    {cfg1 cfg2 : RecoveryConfig}
    {depth : Nat} :
    recoveryConfigSignatureOf cfg1 = recoveryConfigSignatureOf cfg2 ->
    observeRecoveryDepth cfg1 depth = observeRecoveryDepth cfg2 depth := by
  intro h
  cases cfg1
  cases cfg2
  simp [recoveryConfigSignatureOf] at h
  simp [observeRecoveryDepth, h]

theorem activeConfigSignature_observesDepthThresholds
    (cfg : RecoveryConfig) :
    (recoveryConfigSignatureOf cfg).deepNestingThreshold =
      cfg.deepNestingThreshold ∧
    (recoveryConfigSignatureOf cfg).shallowDepthThreshold =
      cfg.shallowDepthThreshold ∧
    (recoveryConfigSignatureOf cfg).vpaNestingCeiling =
      cfg.vpaNestingCeiling := by
  exact ⟨rfl, rfl, rfl⟩

theorem activeConfigSignature_observesBranchSynthesisFields
    (cfg : RecoveryConfig) :
    (recoveryConfigSignatureOf cfg).skipPerTokenBits =
      cfg.skipPerTokenBits ∧
    (recoveryConfigSignatureOf cfg).deleteCostBits =
      cfg.deleteCostBits ∧
    (recoveryConfigSignatureOf cfg).substituteCostBits =
      cfg.substituteCostBits ∧
    (recoveryConfigSignatureOf cfg).insertCostBits =
      cfg.insertCostBits ∧
    (recoveryConfigSignatureOf cfg).swapCostBits =
      cfg.swapCostBits ∧
    (recoveryConfigSignatureOf cfg).maxSkipLookahead =
      cfg.maxSkipLookahead ∧
    (recoveryConfigSignatureOf cfg).deepNestingSkipMultBits =
      cfg.deepNestingSkipMultBits ∧
    (recoveryConfigSignatureOf cfg).shallowDepthSkipMultBits =
      cfg.shallowDepthSkipMultBits ∧
    (recoveryConfigSignatureOf cfg).lowBpThreshold =
      cfg.lowBpThreshold ∧
    (recoveryConfigSignatureOf cfg).lowBpSkipMultBits =
      cfg.lowBpSkipMultBits ∧
    (recoveryConfigSignatureOf cfg).collectionInsertMultBits =
      cfg.collectionInsertMultBits ∧
    (recoveryConfigSignatureOf cfg).groupInsertMultBits =
      cfg.groupInsertMultBits ∧
    (recoveryConfigSignatureOf cfg).bracketInsertMultBits =
      cfg.bracketInsertMultBits ∧
    (recoveryConfigSignatureOf cfg).mixfixSubstituteMultBits =
      cfg.mixfixSubstituteMultBits ∧
    (recoveryConfigSignatureOf cfg).beamWidthBits =
      cfg.beamWidthBits := by
  simp [recoveryConfigSignatureOf]

theorem activeInfraSignatureEq_preservesMaxRecoveryDepth
    {tokenIds : List (Nat × Nat)}
    {syncTokens : List Nat}
    {wfst : RecoveryWfstSignature}
    {cfg1 cfg2 : RecoveryConfig} :
    recoveryInfraSignatureWithActiveConfig tokenIds syncTokens wfst cfg1 =
      recoveryInfraSignatureWithActiveConfig tokenIds syncTokens wfst cfg2 ->
    cfg1.maxRecoveryDepth = cfg2.maxRecoveryDepth := by
  intro h
  have hcfg :
      recoveryConfigSignatureOf cfg1 = recoveryConfigSignatureOf cfg2 :=
    congrArg (fun sig => sig.config) h
  exact congrArg (fun sig => sig.maxRecoveryDepth) hcfg

theorem activeInfraSignatureEq_preservesConfigSignature
    {tokenIds : List (Nat × Nat)}
    {syncTokens : List Nat}
    {wfst : RecoveryWfstSignature}
    {cfg1 cfg2 : RecoveryConfig} :
    recoveryInfraSignatureWithActiveConfig tokenIds syncTokens wfst cfg1 =
      recoveryInfraSignatureWithActiveConfig tokenIds syncTokens wfst cfg2 ->
    recoveryConfigSignatureOf cfg1 = recoveryConfigSignatureOf cfg2 := by
  intro h
  exact congrArg (fun sig => sig.config) h

theorem activeInfraSignatureEq_preservesWfstSignature
    {tokenIds : List (Nat × Nat)}
    {syncTokens : List Nat}
    {wfst1 wfst2 : RecoveryWfstSignature}
    {cfg : RecoveryConfig} :
    recoveryInfraSignatureWithActiveConfig tokenIds syncTokens wfst1 cfg =
      recoveryInfraSignatureWithActiveConfig tokenIds syncTokens wfst2 cfg ->
    wfst1 = wfst2 := by
  intro h
  exact congrArg (fun sig => sig.wfst) h

theorem activeInfraSignatureEq_preservesTokenIds
    {tokenIds1 tokenIds2 : List (Nat × Nat)}
    {syncTokens : List Nat}
    {wfst : RecoveryWfstSignature}
    {cfg : RecoveryConfig} :
    recoveryInfraSignatureWithActiveConfig tokenIds1 syncTokens wfst cfg =
      recoveryInfraSignatureWithActiveConfig tokenIds2 syncTokens wfst cfg ->
    tokenIds1 = tokenIds2 := by
  intro h
  exact congrArg (fun sig => sig.tokenIds) h

theorem activeInfraSignatureEq_preservesSyncTokens
    {tokenIds : List (Nat × Nat)}
    {syncTokens1 syncTokens2 : List Nat}
    {wfst : RecoveryWfstSignature}
    {cfg : RecoveryConfig} :
    recoveryInfraSignatureWithActiveConfig tokenIds syncTokens1 wfst cfg =
      recoveryInfraSignatureWithActiveConfig tokenIds syncTokens2 wfst cfg ->
    syncTokens1 = syncTokens2 := by
  intro h
  exact congrArg (fun sig => sig.syncTokens) h

inductive ReplayRepairAction where
  | skipToSync (skipCount : Nat)
  | deleteToken
  | insertToken
  | substituteToken
  | swapTokens (posA posB : Nat)
  deriving DecidableEq, Repr

def directReplayActionTarget : ReplayRepairAction -> Option Nat
  | .skipToSync skipCount => some skipCount
  | .deleteToken => some 1
  | .insertToken => some 0
  | .substituteToken => some 1
  | .swapTokens posA posB =>
      if Nat.min posA posB = 0 ∧ Nat.max posA posB = 1
      then some 2
      else none

theorem directInsertTargetIsNonadvancing :
    directReplayActionTarget .insertToken = some 0 := by
  rfl

theorem directSubstituteTargetIsOne :
    directReplayActionTarget .substituteToken = some 1 := by
  rfl

theorem directHeadSwapTargetIsTwo :
    directReplayActionTarget (.swapTokens 0 1) = some 2 := by
  simp [directReplayActionTarget]

theorem directNonheadSwapHasNoTarget :
    directReplayActionTarget (.swapTokens 2 3) = none := by
  simp [directReplayActionTarget]

inductive RecoveryEffect where
  | recoveryEvent
  | insertToken (pos : Nat)
  | substituteToken (pos : Nat)
  | swapTokens (posA posB : Nat)
  | commitLexAlternative
  | applyRecoverySequence (targetPos : Nat) (actions : List ReplayRepairAction)
  | nonRecovery
  deriving DecidableEq, Repr

def effectIsRecovery : RecoveryEffect -> Bool
  | .recoveryEvent
  | .insertToken _
  | .substituteToken _
  | .swapTokens _ _
  | .commitLexAlternative
  | .applyRecoverySequence _ _ => true
  | .nonRecovery => false

def recoveryDeltaTargetPosition
    (stateTarget : Option Nat) : RecoveryEffect -> Option Nat
  | .insertToken pos =>
      match stateTarget with
      | some target => if target = pos then some pos else none
      | none => none
  | .substituteToken pos =>
      match stateTarget with
      | some target =>
          let effectTarget := pos + 1
          if target = effectTarget then some effectTarget else none
      | none => none
  | .swapTokens posA posB =>
      match stateTarget with
      | some target =>
          let effectTarget := Nat.max posA posB + 1
          if target = effectTarget then some effectTarget else none
      | none => none
  | .applyRecoverySequence effectTarget _ =>
      match stateTarget with
      | some target => if target = effectTarget then some effectTarget else none
      | none => none
  | effect =>
      if effectIsRecovery effect then stateTarget else none

theorem directInsertDeltaTargetAcceptsMatchingBranchState
    (pos : Nat) :
    recoveryDeltaTargetPosition (some pos) (.insertToken pos) =
      some pos := by
  simp [recoveryDeltaTargetPosition]

theorem directSubstituteDeltaTargetAcceptsSuccessor
    (pos : Nat) :
    recoveryDeltaTargetPosition (some (pos + 1)) (.substituteToken pos) =
      some (pos + 1) := by
  simp [recoveryDeltaTargetPosition]

theorem directSwapDeltaTargetAcceptsAfterWindowMax
    (posA posB : Nat) :
    recoveryDeltaTargetPosition
      (some (Nat.max posA posB + 1))
      (.swapTokens posA posB) =
    some (Nat.max posA posB + 1) := by
  simp [recoveryDeltaTargetPosition]

theorem directSubstituteDeltaTargetRejectsMismatchedBranchState
    {stateTarget pos : Nat} :
    stateTarget ≠ pos + 1 ->
    recoveryDeltaTargetPosition
      (some stateTarget)
      (.substituteToken pos) =
    none := by
  intro h
  simp [recoveryDeltaTargetPosition, h]

def recoveryDeltaTargetValid
    (stateTarget : Option Nat) : RecoveryEffect -> Bool
  | .insertToken pos =>
      match stateTarget with
      | some target => target == pos
      | none => true
  | .substituteToken pos =>
      match stateTarget with
      | some target => target == pos + 1
      | none => true
  | .swapTokens posA posB =>
      match stateTarget with
      | some target => target == Nat.max posA posB + 1
      | none => true
  | .applyRecoverySequence effectTarget _ =>
      match stateTarget with
      | some target => target == effectTarget
      | none => true
  | _ => true

def firstRecoveryDeltaTarget
    (stateTarget : Option Nat) : List RecoveryEffect -> Option Nat
  | [] => none
  | effect :: rest =>
      match recoveryDeltaTargetPosition stateTarget effect with
      | some target => some target
      | none => firstRecoveryDeltaTarget stateTarget rest

def recoveryEffectsTargetPosition
    (stateTarget : Option Nat)
    (effects : List RecoveryEffect) : Option Nat :=
  if effects.all (recoveryDeltaTargetValid stateTarget)
  then firstRecoveryDeltaTarget stateTarget effects
  else none

theorem multiEffectTargetAcceptsMatchingDirectAndSequence
    (pos : Nat)
    (actions : List ReplayRepairAction) :
    recoveryEffectsTargetPosition
      (some (pos + 1))
      [.substituteToken pos,
       .applyRecoverySequence (pos + 1) actions] =
    some (pos + 1) := by
  simp [recoveryEffectsTargetPosition, recoveryDeltaTargetValid,
    firstRecoveryDeltaTarget, recoveryDeltaTargetPosition]

theorem multiEffectTargetRejectsMismatchedDirectAndSequence
    {pos sequenceTarget : Nat}
    (actions : List ReplayRepairAction) :
    pos + 1 ≠ sequenceTarget ->
    recoveryEffectsTargetPosition
      (some (pos + 1))
      [.substituteToken pos,
       .applyRecoverySequence sequenceTarget actions] =
    none := by
  intro h
  simp [recoveryEffectsTargetPosition, recoveryDeltaTargetValid, h]

def replayRepairActionMutatesTokenSource : ReplayRepairAction -> Bool
  | .insertToken => true
  | .substituteToken => true
  | .swapTokens _ _ => true
  | .skipToSync _ => false
  | .deleteToken => false

def recoveryEffectMutatesTokenSource : RecoveryEffect -> Bool
  | .insertToken _ => true
  | .substituteToken _ => true
  | .swapTokens _ _ => true
  | .commitLexAlternative => true
  | .applyRecoverySequence _ actions =>
      actions.any replayRepairActionMutatesTokenSource
  | .recoveryEvent => false
  | .nonRecovery => false

structure TokenDependentCacheState where
  dispatchCohort : Bool
  pendingDrainKeys : Bool
  recoveryCohort : Bool
  chainEarley : Bool
  chainAbsorbedIntervals : Bool
  dispatchRegistrations : Nat
  recoveryRegistrations : Nat
  deriving DecidableEq, Repr

def tokenDependentCachesCleared
    (state : TokenDependentCacheState) : Bool :=
  (state.dispatchCohort == false) &&
    (state.pendingDrainKeys == false) &&
    (state.recoveryCohort == false) &&
    (state.chainEarley == false) &&
    (state.chainAbsorbedIntervals == false)

def invalidateTokenDependentCaches
    (state : TokenDependentCacheState) : TokenDependentCacheState :=
  { dispatchCohort := false,
    pendingDrainKeys := false,
    recoveryCohort := false,
    chainEarley := false,
    chainAbsorbedIntervals := false,
    dispatchRegistrations := state.dispatchRegistrations,
    recoveryRegistrations := state.recoveryRegistrations }

def replayCacheStateAfter
    (effect : RecoveryEffect)
    (state : TokenDependentCacheState) : TokenDependentCacheState :=
  if recoveryEffectMutatesTokenSource effect
  then invalidateTokenDependentCaches state
  else state

def rebindMutableTokenSourceCacheState
    (state : TokenDependentCacheState) : TokenDependentCacheState :=
  invalidateTokenDependentCaches state

theorem mutatingRecoveryReplayClearsTokenDependentCaches
    {effect : RecoveryEffect}
    {state : TokenDependentCacheState} :
    recoveryEffectMutatesTokenSource effect = true ->
    tokenDependentCachesCleared
      (replayCacheStateAfter effect state) = true := by
  intro hmut
  simp [replayCacheStateAfter, hmut, tokenDependentCachesCleared,
    invalidateTokenDependentCaches]

theorem mutableTokenSourceRebindClearsTokenDependentCaches
    {state : TokenDependentCacheState} :
    tokenDependentCachesCleared
      (rebindMutableTokenSourceCacheState state) = true := by
  simp [rebindMutableTokenSourceCacheState, tokenDependentCachesCleared,
    invalidateTokenDependentCaches]

theorem nonmutatingRecoveryReplayPreservesTokenDependentCaches
    {effect : RecoveryEffect}
    {state : TokenDependentCacheState} :
    recoveryEffectMutatesTokenSource effect = false ->
    replayCacheStateAfter effect state = state := by
  intro hmut
  simp [replayCacheStateAfter, hmut]

theorem tokenMutationPreservesDispatchDiagnostics
    {state : TokenDependentCacheState} :
    (invalidateTokenDependentCaches state).dispatchRegistrations =
      state.dispatchRegistrations := by
  rfl

theorem tokenMutationPreservesRecoveryDiagnostics
    {state : TokenDependentCacheState} :
    (invalidateTokenDependentCaches state).recoveryRegistrations =
      state.recoveryRegistrations := by
  rfl

theorem mutableTokenSourceRebindPreservesDispatchDiagnostics
    {state : TokenDependentCacheState} :
    (rebindMutableTokenSourceCacheState state).dispatchRegistrations =
      state.dispatchRegistrations := by
  rfl

theorem mutableTokenSourceRebindPreservesRecoveryDiagnostics
    {state : TokenDependentCacheState} :
    (rebindMutableTokenSourceCacheState state).recoveryRegistrations =
      state.recoveryRegistrations := by
  rfl

example :
    recoveryEffectMutatesTokenSource
      (.applyRecoverySequence 0 [.insertToken]) = true := by
  rfl

example :
    recoveryEffectMutatesTokenSource
      (.applyRecoverySequence 2 [.deleteToken, .skipToSync 1]) = false := by
  rfl

end MettailWpda
