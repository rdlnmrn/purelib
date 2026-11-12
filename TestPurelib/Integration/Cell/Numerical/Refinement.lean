module
import Purelib.Integration.Cell.Numerical.Continuous.Comparison
import Purelib.Integration.Cell.Numerical.Common.Split
import Purelib.Integration.Cell.Numerical.Continuous.Producer
import Purelib.Integration.Cell.Numerical.Continuous.Operational
import Purelib.Integration.Cell.Numerical.Common.Operational.Observation
import Purelib.Integration.Cell.Numerical.Common.Observation.Independent
import Purelib.Integration.Cell.Numerical.Common.Observation.Independent.History
import Purelib.Integration.Cell.Numerical.Continuous.Observation
import Purelib.Integration.Cell.Numerical.Continuous.Observation.Continuation
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! Numerical point states with nonzero uncertainty and independent common partitions. -/

namespace TestPurelib.Integration.Cell.Numerical.Refinement

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration
open Purelib.Integration.NumericalFrontier
open Purelib.Integration.NumericalFrontier.Common
open Purelib.Integration.NumericalFrontier.Continuous.Observation
open Purelib.Integration.NumericalFrontier.Common.Observation

/-- A nonnegative point radius bounded by its original initial radius. -/
private abbrev Radius := {radius : Fraction.Rational // 0 ≤ radius ∧ radius ≤ 1}

/-- The rational interval around a point with its retained state radius. -/
private def radiusRange (point : Fraction.Rational) (radius : Radius) : Purelib.Data.Rat.Interval :=
  ⟨point - radius.val, point + radius.val, by
    have signed := Arithmetic.neg_le_self_of_nonnegative radius.property.1
    have shifted := Arithmetic.add_le_add_right_direct signed point
    have first : -radius.val + point = point - radius.val := by ring1
    have second : radius.val + point = point + radius.val := by ring1
    rw [first, second] at shifted
    exact shifted⟩

/-- A retained radius interval contains its original rational center. -/
private theorem radiusRange_contains (point : Fraction.Rational) (radius : Radius) :
    (radiusRange point radius).Contains point := by
  have negative := Arithmetic.neg_le_neg_direct radius.property.1
  rw [neg_zero] at negative
  have lower := Arithmetic.add_le_add_right_direct negative point
  have upper := Arithmetic.add_le_add_right_direct radius.property.1 point
  have first : -radius.val + point = point - radius.val := by ring1
  have second : radius.val + point = point + radius.val := by ring1
  rw [first, Fraction.Field.zero_add] at lower
  rw [Fraction.Field.zero_add, second] at upper
  exact ⟨lower, upper⟩

/-- The actual radius interval has twice the retained radius as its width. -/
private theorem radiusRange_width (point : Fraction.Rational) (radius : Radius) :
    (radiusRange point radius).width = radius.val + radius.val := by
  change (point + radius.val) - (point - radius.val) = radius.val + radius.val
  ring1

/-- A smaller retained radius refines the original point interval. -/
private theorem radiusRange_refines (point : Fraction.Rational) (inner outer : Radius)
    (ordered : inner.val ≤ outer.val) : (radiusRange point inner).Refines (radiusRange point outer) := by
  constructor
  · exact Arithmetic.sub_le_sub_left_direct ordered point
  · exact Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl point) ordered

/-- A point process that retains a nonzero rational radius and narrows it on each request. -/
private def noisy (point : Fraction.Rational) : BoundProcess where
  State := Radius
  bound := radiusRange point
  initial := ⟨1, by decide, by decide⟩
  request := fun state tolerance positive =>
    ⟨min state.val (tolerance / 4),
      Fraction.Order.Basic.le_min state.property.1 (Bounds.Quarter.quarter_pos positive).le,
      (Fraction.Order.Basic.min_le_left _ _).trans state.property.2⟩
  request_refines := by
    intro state tolerance positive
    apply radiusRange_refines
    exact Fraction.Order.Basic.min_le_left _ _
  accurate := by
    intro state tolerance positive
    rw [radiusRange_width]
    have each := Fraction.Order.Basic.min_le_right state.val (tolerance / 4)
    have sum := Arithmetic.add_le_add_direct each each
    rw [Bounds.Quarter.two_quarters] at sum
    exact sum.trans_lt (Fraction.Order.Field.half_lt_self positive)
  refinesInitial := by
    intro state
    apply radiusRange_refines
    exact state.property.2

/-- Each retained numerical point state contains its original rational center. -/
private theorem noisy_contains (point : Fraction.Rational) (state : (noisy point).State) :
    ((noisy point).bound state).Contains point := radiusRange_contains point state

/-- The point family has the original identity function's effective variation. -/
private def modulus : Rational.Uniform.Numerical noisy where
  radius := fun variation => variation
  radius_pos := fun _ positive => positive
  variation := by
    intro variation positive first second _ ordered _ small firstState secondState
    have firstInside := noisy_contains first firstState
    have secondInside := noisy_contains second secondState
    have negative := Arithmetic.neg_le_neg_direct positive.le
    rw [neg_zero] at negative
    have shifted := Arithmetic.add_le_add_right_direct negative first
    have firstLe : first - variation ≤ first := by
      have identity : -variation + first = first - variation := by ring1
      rw [identity, Fraction.Field.zero_add] at shifted
      exact shifted
    have lower := Arithmetic.sub_le_sub_right_direct firstInside.1 variation
    have upper := Arithmetic.add_le_add_right_direct firstInside.2 variation
    have pointBound := Arithmetic.sub_le_iff_le_add_direct.mp small.le
    have identity : variation + first = first + variation := by ring1
    rw [identity] at pointBound
    exact ⟨lower.trans (firstLe.trans (ordered.trans secondInside.2)),
      secondInside.1.trans (pointBound.trans upper)⟩

/-- The finite exact identity source. -/
private def identity (point : Fraction.Rational) : Fraction.Rational := point

/-- The original exact identity source has its direct effective variation. -/
private def identityModulus : Rational.Uniform.Modulus identity where
  radius := fun variation => variation
  radius_pos := fun _ positive => positive
  variation := by
    intro variation positive first second _ ordered _ small
    have negative := Arithmetic.neg_le_neg_direct positive.le
    rw [neg_zero] at negative
    have shifted := Arithmetic.add_le_add_right_direct negative first
    have lower : first - variation ≤ first := by
      have identity : -variation + first = first - variation := by ring1
      rw [identity, Fraction.Field.zero_add] at shifted
      exact shifted
    have upper := Arithmetic.sub_le_iff_le_add_direct.mp small.le
    have identity : variation + first = first + variation := by ring1
    rw [identity] at upper
    exact ⟨lower.trans ordered, upper⟩

/-- The exact identity source represented by the original rational bound processes. -/
private def exactModulus := Rational.Uniform.Numerical.ofExact identityModulus

/-- The two original positive integration requests. -/
private def requestFour : AccuracyRequest := ⟨4, by decide⟩
private def requestTwo : AccuracyRequest := ⟨2, by decide⟩

/-- The two independently computed numerical source frontiers. -/
private def firstResult : NumericalFrontier.Continuous.Result modulus :=
  NumericalFrontier.Continuous.build modulus requestFour
private def secondResult : NumericalFrontier.Continuous.Result modulus :=
  NumericalFrontier.Continuous.build modulus requestTwo

/-- An independent exact point-process construction of the same identity source. -/
private def exactResult : NumericalFrontier.Continuous.Result exactModulus :=
  NumericalFrontier.Continuous.build exactModulus requestTwo

/-- The actual noisy-point bank retained by the first numerical preparation. -/
private def firstBank := firstResult.frontier.cells.map (fun cell => cell.item)

/-- A cache-aware observation of that same numerical preparation. -/
private def samePrepared := firstResult.preparation
private def sameObservation := Continuous.Observation.cachedResultComputation samePrepared firstBank
private def sameOracle := Continuous.Observation.originalCachedReply samePrepared firstBank

/-- A tighter preparation reads the same point bank and continues matching old states when needed. -/
private def tighterPrepared := secondResult.preparation
private def tighterObservation :=
  Continuous.Observation.cachedResultComputation tighterPrepared firstBank
private def tighterOracle := Continuous.Observation.originalCachedReply tighterPrepared firstBank

/-- Return the second original interval's point when the first occurrence is requested. -/
private def wrongNumericalReply (entry : Continuous.Observation.Entry tighterPrepared) :
    Continuous.Observation.CachedReply tighterPrepared firstBank :=
  match tighterPrepared.partition.intervals.attach with
  | _ :: second :: _ => Continuous.Observation.originalCachedReply tighterPrepared firstBank second
  | _ => Continuous.Observation.originalCachedReply tighterPrepared firstBank entry

/-- The common point request retains nonzero observation uncertainty. -/
private def pointRequest : AccuracyRequest := ⟨1, by decide⟩

/-- The actual common refinement and its two original point histories. -/
private def common := NumericalFrontier.commonReadings firstResult.frontier secondResult.frontier pointRequest

/-- The actual numerical producer as the original persistent integration process. -/
private def process : IntegrationProcess (NumericalPoint noisy) :=
  (NumericalFrontier.Continuous.producer modulus).integrationProcess

/-- A saved nonempty numerical request history. -/
private def saved : process.State := process.request process.initial requestFour.tolerance requestFour.positive

/-- Continue the saved numerical frontier with a different request. -/
private def later : process.State := process.request saved requestTwo.tolerance requestTwo.positive

/-- A second nonempty request history in the opposite order. -/
private def divergent : process.State :=
  process.request (process.request process.initial requestTwo.tolerance requestTwo.positive)
    requestFour.tolerance requestFour.positive

/-- Exact rational point processes support the same public numerical-history observer. -/
private def exactProcess := (NumericalFrontier.Continuous.producer exactModulus).integrationProcess
private def exactSaved := exactProcess.request exactProcess.initial requestFour.tolerance requestFour.positive

example := Continuation.historyComputation_original
  exactModulus exactSaved requestTwo

example := Continuation.historyComputation_replay
  exactModulus exactSaved requestTwo

/-- The actual common point requests for both saved histories. -/
private def historyCommon := NumericalFrontier.commonReadings later.1 divergent.1 pointRequest

/-- Point states of the original noisy process have executable rational equality. -/
private instance noisyStateDecidableEq (point : Fraction.Rational) : DecidableEq (noisy point).State :=
  inferInstanceAs (DecidableEq Radius)

/-- The complete observed continuation from the original retained noisy frontier and bank. -/
private def observedContinuation :=
  Continuation.computation modulus firstResult.frontier firstBank requestTwo
private def continuationBank := NumericalFrontier.Producer.effectiveBank firstResult.frontier firstBank
private def continuationOracle :=
  Continuation.originalReplyAll tighterPrepared continuationBank requestTwo

example : (observedContinuation.protocol.run continuationOracle).value =
    .ok ((NumericalFrontier.Continuous.producer modulus).advanceCached firstBank firstResult.frontier requestTwo) :=
  Continuation.computation_original modulus firstResult.frontier firstBank
    requestTwo

example : observedContinuation.protocol.replayExact (observedContinuation.protocol.run continuationOracle).trace =
    .ok (.ok ((NumericalFrontier.Continuous.producer modulus).advanceCached firstBank firstResult.frontier
      requestTwo)) :=
  Continuation.computation_replay modulus firstResult.frontier firstBank
    requestTwo

/-- Fresh points are requested once and the subsequent common construction reuses those exact states. -/
example : (observedContinuation.protocol.run continuationOracle).trace.length = 3 := by decide +kernel

/-- A looser request accepts the saved frontier without any numerical point call. -/
example : let request : AccuracyRequest := ⟨8, by decide⟩
    let prepared := NumericalFrontier.Continuous.Preparation.prepare modulus request
    ((Continuation.computation
      modulus firstResult.frontier firstBank request).protocol.run
      (Continuation.originalReplyAll
        prepared continuationBank request)).trace.length = 0 := by
  decide +kernel

/-- A common response carrying a different point bank is rejected at the actual request. -/
private def wrongBankOracle (_ : Continuation.Query tighterPrepared) :
    Continuation.Reply tighterPrepared firstBank requestTwo :=
  .inr ⟨[], NumericalFrontier.Common.Observation.originalReply [] requestTwo
    ⟨⟨0, 1⟩, by exact ⟨by decide, by decide, by decide⟩⟩⟩

example : let query : NumericalFrontier.Common.Observation.Query := ⟨⟨0, 1⟩, by exact ⟨by decide, by decide, by decide⟩⟩
    let handler := Continuation.commonHandler tighterPrepared firstBank
      requestTwo firstBank query
    (match (handler.protocol.run wrongBankOracle).value with
    | .error (.bank _ _ _) => true
    | _ => false) = true ∧ (handler.protocol.run wrongBankOracle).trace.length = 1 := by
  decide +kernel

/-- The public persistent request observes the actual nonempty numerical history. -/
example : let prepared := NumericalFrontier.Continuous.Preparation.prepare modulus requestTwo
    let bank := NumericalFrontier.Producer.effectiveBank saved.1
      ((NumericalFrontier.Continuous.producer modulus).retainedReadings saved.2)
    ((Continuation.historyComputation modulus saved requestTwo).protocol.run
      (Continuation.originalReplyAll prepared bank requestTwo)).value =
        .ok (process.request saved requestTwo.tolerance requestTwo.positive) :=
  Continuation.historyComputation_original modulus saved requestTwo

/-- Direct continuation carries the saved start state into the fresh tighter point request. -/
example : (match (NumericalFrontier.Continuous.producer modulus).advanceCached [] firstResult.frontier requestTwo with
    | .reused _ _ => false
    | .refined _ cached fresh _ _ _ =>
        cached.isEmpty && match fresh.frontier.cells with
        | [] => false
        | cell :: _ => decide (cell.item.previous.val = (1 / 4 : Fraction.Rational))) = true := by
  decide +kernel

/-- A direct satisfied request makes no point calls, including with an empty supplied bank. -/
example : let request : AccuracyRequest := ⟨8, by decide⟩
    let prepared := NumericalFrontier.Continuous.Preparation.prepare modulus request
    let bank := NumericalFrontier.Producer.effectiveBank firstResult.frontier []
    ((Continuation.computation modulus firstResult.frontier [] request).protocol.run
      (Continuation.originalReplyAll prepared bank request)).trace.length = 0 := by
  decide +kernel

/-- A point reading continued from its original width-two initial state. -/
private def observed : NumericalPoint noisy :=
  NumericalPoint.observe noisy ⟨0, 1⟩ (1 / 2) (by decide) (by decide) (noisy (1 / 2)).initial pointRequest

/-- The next point request narrows the actual retained nonzero observation. -/
private def tighterRequest : AccuracyRequest := ⟨1 / 2, by decide⟩

/-- A saved point interval narrow enough for an intermediate request. -/
private def narrowObserved : NumericalPoint noisy := observed.refine tighterRequest

/-- A different cell whose start is the original saved point. -/
private def revisitedInterval : Partition.Interval := ⟨1 / 2, 1⟩

/-- The revisited interval is a valid positive-length unit cell. -/
private theorem revisitedValid : revisitedInterval.Valid := ⟨by decide, by decide, by decide⟩

/-- An intermediate request that the later saved point already satisfies. -/
private def intermediateRequest : AccuracyRequest := ⟨1 / 3, by decide⟩

/-- A stricter point request that requires continuing the original saved state. -/
private def veryTightRequest : AccuracyRequest := ⟨1 / 8, by decide⟩

/-- The common refinement of the original noisy and exact point-process families. -/
private def crossCommon := NumericalFrontier.commonReadings firstResult.frontier exactResult.frontier pointRequest

/-- The independent-source observer retains the original two frontiers and ordered common occurrences. -/
private def independentProgram := Independent.computation firstResult.frontier exactResult.frontier pointRequest
private def independentOracle := Independent.originalReply firstResult.frontier exactResult.frontier pointRequest

example : (independentProgram.protocol.run independentOracle).value = .ok crossCommon :=
  Independent.computation_original firstResult.frontier exactResult.frontier pointRequest

example : independentProgram.protocol.replayExact (independentProgram.protocol.run independentOracle).trace =
    .ok (.ok crossCommon) :=
  Independent.computation_replay firstResult.frontier exactResult.frontier pointRequest

/-- The first common occurrence reuses the original left parent point. -/
private def firstIndependentIndex : Independent.Index firstResult.frontier exactResult.frontier :=
  ⟨0, by decide +kernel⟩

/-- The second common occurrence requires a point from the original left source. -/
private def secondIndependentIndex : Independent.Index firstResult.frontier exactResult.frontier :=
  ⟨1, by decide +kernel⟩

example : ((Independent.leftRequest firstResult.frontier exactResult.frontier pointRequest
    firstIndependentIndex).protocol.run independentOracle).trace.length = 0 := by decide +kernel

example : ((Independent.leftRequest firstResult.frontier exactResult.frontier pointRequest
    secondIndependentIndex).protocol.run independentOracle).trace.length = 1 := by decide +kernel

example : (Independent.leftPoint firstResult.frontier exactResult.frontier pointRequest
    secondIndependentIndex).previous.val = (1 : Fraction.Rational) := by decide +kernel

/-- A reply from the other original owner is rejected at the first actual point request. -/
private def wrongIndependentOwner : Independent.Query firstResult.frontier exactResult.frontier →
    Independent.Reply firstResult.frontier exactResult.frontier pointRequest
  | .inl index =>
      .inr ⟨index, ⟨Independent.rightPoint firstResult.frontier exactResult.frontier pointRequest index, rfl⟩⟩
  | .inr index =>
      .inl ⟨index, ⟨Independent.leftPoint firstResult.frontier exactResult.frontier pointRequest index, rfl⟩⟩

example : (match (independentProgram.protocol.run wrongIndependentOwner).value with
    | .error (.owner _) => true
    | _ => false) = true ∧ (independentProgram.protocol.run wrongIndependentOwner).trace.length = 1 := by decide +kernel

/-- A reply for the first occurrence is invalid at the later requested occurrence. -/
private def wrongIndependentIndex : Independent.Query firstResult.frontier exactResult.frontier →
    Independent.Reply firstResult.frontier exactResult.frontier pointRequest
  | .inl _ => .inl ⟨firstIndependentIndex,
      ⟨Independent.leftPoint firstResult.frontier exactResult.frontier pointRequest firstIndependentIndex, rfl⟩⟩
  | .inr _ => .inr ⟨firstIndependentIndex,
      ⟨Independent.rightPoint firstResult.frontier exactResult.frontier pointRequest firstIndependentIndex, rfl⟩⟩

example : (match (independentProgram.protocol.run wrongIndependentIndex).value with
    | .error (.index _ _ _) => true
    | _ => false) = true ∧ (independentProgram.protocol.run wrongIndependentIndex).trace.length = 1 := by decide +kernel

/-- Both original noisy frontiers share each cache-selected common point observation. -/
private def sharedCommon :=
  NumericalFrontier.commonReadingsCached firstResult.frontier secondResult.frontier [observed, narrowObserved]
    pointRequest

/-- The original point-equivalence scheduler and coherence contracts for both source families. -/
private def jointEquivalent (point : Fraction.Rational) (_lower : 0 ≤ point) (_upper : point ≤ 1) :
    OperationalEquivalence (noisy point) (BoundProcess.exact point) :=
  OperationalEquivalence.ofAnchoredAt (noisy point) point (noisy_contains point)
private theorem jointLeftCoherent (point : Fraction.Rational) (lower : 0 ≤ point) (upper : point ≤ 1) :
    (noisy point).Coherent := modulus.coherent point lower upper
private theorem jointRightCoherent (point : Fraction.Rational) (_lower : 0 ≤ point) (_upper : point ≤ 1) :
    (BoundProcess.exact point).Coherent := BoundProcess.exact_coherent point

/-- The actual joint point requests produced by the original anchored equivalence. -/
private def crossJoint := NumericalFrontier.requestJointReadings crossCommon tighterRequest
  jointEquivalent jointLeftCoherent jointRightCoherent

/-- Both original point sources are observed before their actual returned common readings are jointly compared. -/
private def combinedProgram := Independent.Joint.computation firstResult.frontier exactResult.frontier
  pointRequest tighterRequest jointEquivalent jointLeftCoherent jointRightCoherent
private def combinedOracle := Independent.Joint.originalReply firstResult.frontier exactResult.frontier
  pointRequest tighterRequest jointEquivalent jointLeftCoherent jointRightCoherent

example : (combinedProgram.protocol.run combinedOracle).value = .ok ⟨crossCommon, crossJoint⟩ :=
  Independent.Joint.computation_original firstResult.frontier exactResult.frontier pointRequest tighterRequest
    jointEquivalent jointLeftCoherent jointRightCoherent

example : combinedProgram.protocol.replayExact (combinedProgram.protocol.run combinedOracle).trace =
    .ok (.ok ⟨crossCommon, crossJoint⟩) :=
  Independent.Joint.computation_replay firstResult.frontier exactResult.frontier pointRequest tighterRequest
    jointEquivalent jointLeftCoherent jointRightCoherent

/-- Each original common reading receives exactly one joint scheduler request after point acquisition. -/
example : (combinedProgram.protocol.run combinedOracle).trace.length =
    (independentProgram.protocol.run independentOracle).trace.length + crossCommon.readings.length := by decide +kernel

/-- The returned joint readings pay for the actual two retained numerical answers. -/
example (result : Independent.Joint.Result firstResult.frontier exactResult.frontier pointRequest tighterRequest) :
    Fraction.abs (firstResult.answer - exactResult.answer) ≤
      (integralBound firstResult.frontier.cells).width + (integralBound exactResult.frontier.cells).width +
        (pointRequest.tolerance + pointRequest.tolerance + tighterRequest.tolerance) :=
  result.2.answers_difference_le firstResult.answer exactResult.answer firstResult.answer_contains
    exactResult.answer_contains

/-- A wrong owner in the independent phase stops before any later point or joint request. -/
private def combinedWrongOwner : Independent.Joint.Query firstResult.frontier exactResult.frontier pointRequest →
    Independent.Joint.Reply firstResult.frontier exactResult.frontier pointRequest tighterRequest
      jointEquivalent jointLeftCoherent jointRightCoherent
  | .inl question => .inl (wrongIndependentOwner question)
  | .inr child => combinedOracle (.inr child)

example : (match (combinedProgram.protocol.run combinedWrongOwner).value with
    | .error (.point (.owner _)) => true
    | _ => false) = true ∧ (combinedProgram.protocol.run combinedWrongOwner).trace.length = 1 := by decide +kernel

/-- An original point reply at a joint request is rejected after all preceding point requests. -/
private def combinedWrongJoint : Independent.Joint.Query firstResult.frontier exactResult.frontier pointRequest →
    Independent.Joint.Reply firstResult.frontier exactResult.frontier pointRequest tighterRequest
      jointEquivalent jointLeftCoherent jointRightCoherent
  | .inl question => .inl (independentOracle question)
  | .inr _ => .inl (independentOracle (.inl firstIndependentIndex))

example : (match (combinedProgram.protocol.run combinedWrongJoint).value with
    | .error (.operation (.inr _)) => true
    | _ => false) = true ∧
      (combinedProgram.protocol.run combinedWrongJoint).trace.length =
        (independentProgram.protocol.run independentOracle).trace.length + 1 := by decide +kernel

/-- Both saved histories are advanced before comparing their actual returned frontiers. -/
private def historyJointProgram := Independent.History.computation modulus exactModulus saved exactSaved
  tighterRequest tighterRequest pointRequest tighterRequest jointEquivalent jointLeftCoherent jointRightCoherent
private def historyJointOracle := Independent.History.originalReply modulus exactModulus saved exactSaved
  tighterRequest tighterRequest pointRequest tighterRequest jointEquivalent jointLeftCoherent jointRightCoherent

example := Independent.History.computation_original modulus exactModulus saved exactSaved
  tighterRequest tighterRequest pointRequest tighterRequest jointEquivalent jointLeftCoherent jointRightCoherent

example := Independent.History.computation_replay modulus exactModulus saved exactSaved
  tighterRequest tighterRequest pointRequest tighterRequest jointEquivalent jointLeftCoherent jointRightCoherent

/-- The complete trace keeps left history, right history, and joint requests in that order. -/
private def historyStages : List Nat := (historyJointProgram.protocol.run historyJointOracle).trace.map fun exchange =>
  match exchange.query with
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

example : historyStages.filter (· == 0) ++ historyStages.filter (· == 1) ++ historyStages.filter (· == 2) =
    historyStages ∧ historyStages.contains 0 = true ∧ historyStages.contains 1 = true ∧
      historyStages.contains 2 = true := by decide +kernel

/-- A reply for the right history cannot be substituted for the first left-history request. -/
private def wrongHistoryReply : Continuation.Reply
    (NumericalFrontier.Continuous.Preparation.prepare exactModulus tighterRequest)
    (NumericalFrontier.Producer.effectiveBank exactSaved.1
      ((NumericalFrontier.Continuous.producer exactModulus).retainedReadings exactSaved.2)) tighterRequest :=
  .inr ⟨[], NumericalFrontier.Common.Observation.originalReply [] tighterRequest
    ⟨⟨0, 1⟩, by exact ⟨by decide, by decide, by decide⟩⟩⟩

private def wrongHistoryOracle : Independent.History.Query modulus exactModulus saved exactSaved
    tighterRequest tighterRequest pointRequest → Independent.History.Reply modulus exactModulus saved exactSaved
      tighterRequest tighterRequest pointRequest tighterRequest jointEquivalent jointLeftCoherent jointRightCoherent
  | .inl _ => .inr (.inl wrongHistoryReply)
  | query => historyJointOracle query

example : (match (historyJointProgram.protocol.run wrongHistoryOracle).value with
    | .error (.operation _) => true
    | _ => false) = true ∧ (historyJointProgram.protocol.run wrongHistoryOracle).trace.length = 1 := by decide +kernel

/-- The numerical comparison observes those exact joint states and interval readbacks. -/
private def jointProgram := Operational.Observation.computation crossCommon tighterRequest
  jointEquivalent jointLeftCoherent jointRightCoherent
private def jointOracle := Operational.Observation.originalReply crossCommon tighterRequest
  jointEquivalent jointLeftCoherent jointRightCoherent

example := Operational.Observation.computation_original crossCommon tighterRequest
  jointEquivalent jointLeftCoherent jointRightCoherent

example := Operational.Observation.computation_replay crossCommon tighterRequest
  jointEquivalent jointLeftCoherent jointRightCoherent

/-- The second original common occurrence supplies a deliberate wrong-index reply. -/
private def wrongJointIndex : Operational.Observation.Query crossCommon :=
  ⟨1, by decide +kernel⟩

private def wrongJointReply (_ : Operational.Observation.Query crossCommon) :=
  jointOracle wrongJointIndex

example : (match (jointProgram.protocol.run wrongJointReply).value with
    | .error _ => true
    | .ok _ => false) = true ∧ (jointProgram.protocol.run wrongJointReply).trace.length = 1 := by decide +kernel

/-- The actual joint scheduler is requested once for each original common-point occurrence. -/
example : (jointProgram.protocol.run jointOracle).trace.length = crossCommon.readings.length := by decide +kernel


example : ((noisy (1 / 2)).bound observed.previous).width = 2 ∧ observed.reading.width = 1 / 2 ∧
    (observed.refine tighterRequest).reading.width = 1 / 4 := by decide +kernel

/-- A repeated preparation reuses its actual point states without issuing point requests. -/
example : (sameObservation.protocol.run sameOracle).trace.length = 0 := by decide +kernel

/-- The tighter preparation makes the actual three requests needed on its new mesh. -/
example : (tighterObservation.protocol.run tighterOracle).trace.length = 3 := by decide +kernel

example : (tighterObservation.protocol.run tighterOracle).value =
    .ok (NumericalFrontier.Continuous.CachedResult.build modulus firstBank requestTwo) :=
  Continuous.Observation.cachedResult_original modulus firstBank requestTwo

example : tighterObservation.protocol.replayExact (tighterObservation.protocol.run tighterOracle).trace =
    .ok (.ok (NumericalFrontier.Continuous.CachedResult.build modulus firstBank requestTwo)) :=
  Continuous.Observation.cachedResult_replay modulus firstBank requestTwo

/-- A wrong numerical occurrence is reported and stops before any later point request. -/
example : (match (tighterObservation.protocol.run wrongNumericalReply).value with
    | .error invalid => decide (invalid.reported.val.start = 1 / 3)
    | .ok _ => false) = true := by decide +kernel

example : (tighterObservation.protocol.run wrongNumericalReply).trace.length = 1 := by decide +kernel

example : Purelib.Data.Rat.Interval.Refines (observed.refine tighterRequest).reading observed.reading :=
  observed.refine_reading tighterRequest

example : observed.retag ⟨0, 1⟩ observed.point (by decide) (by decide) pointRequest =
    observed.move ⟨0, 1⟩ observed.point (by decide) (by decide) rfl :=
  observed.retag_reused_at_point ⟨0, 1⟩ (by decide) (by decide) pointRequest (by decide +kernel)

example : observed.retag ⟨0, 1⟩ observed.point (by decide) (by decide) tighterRequest =
    NumericalPoint.observe noisy ⟨0, 1⟩ observed.point (by decide) (by decide) observed.state tighterRequest :=
  observed.retag_refines_at_point_of_not_accurate ⟨0, 1⟩ (by decide) (by decide) tighterRequest (by decide +kernel)

/-- A later sufficient point is selected before refining an earlier wider point at the same tag. -/
example : (NumericalPoint.atStartCached noisy [observed, narrowObserved] revisitedInterval revisitedValid
    intermediateRequest).val.reading.width = 1 / 4 := by decide +kernel

/-- A stricter request supplies the exact saved radius as the new point request's predecessor. -/
example : (NumericalPoint.atStartCached noisy [observed] revisitedInterval revisitedValid
    veryTightRequest).val.previous.val = 1 / 4 := by decide +kernel

/-- Each common child uses one actual point observation for both same-source parents. -/
example (reading : NumericalFrontier.CommonReading firstResult.frontier secondResult.frontier pointRequest)
    (member : reading ∈ sharedCommon.readings) : reading.leftPoint = reading.rightPoint :=
  NumericalFrontier.commonReadingsCached_points_eq firstResult.frontier secondResult.frontier
    [observed, narrowObserved] pointRequest reading member

example : common.refinement.partition.intervals.length = 4 ∧ common.pointBudget = 5 / 48 := by decide +kernel

example : common.pointBudget ≤ pointRequest.tolerance + pointRequest.tolerance :=
  common.pointBudget_le (fun point lower upper => modulus.coherent point lower upper)

example : crossJoint.readings.length = 4 := by decide +kernel

example : crossCommon.pointBudget ≤ pointRequest.tolerance + pointRequest.tolerance + tighterRequest.tolerance :=
  crossJoint.pointBudget_le

example : Fraction.abs (firstResult.answer - exactResult.answer) ≤
    (integralBound firstResult.frontier.cells).width + (integralBound exactResult.frontier.cells).width +
      (pointRequest.tolerance + pointRequest.tolerance + tighterRequest.tolerance) :=
  crossJoint.answers_difference_le firstResult.answer exactResult.answer firstResult.answer_contains
    exactResult.answer_contains

example : Fraction.abs (firstResult.answer - exactResult.answer) ≤
    requestFour.tolerance + requestTwo.tolerance +
      (pointRequest.tolerance + pointRequest.tolerance + tighterRequest.tolerance) :=
  firstResult.answer_difference_le_of_operational exactResult pointRequest tighterRequest
    (fun point _ _ => OperationalEquivalence.ofAnchoredAt (noisy point) point (noisy_contains point))

example : common.intersection.cells.length = 4 := by decide +kernel

example : Purelib.Data.Rat.Interval.Refines (integralBound common.intersection.cells)
    (integralBound firstResult.frontier.cells) := common.intersection_refines_left

example : Purelib.Data.Rat.Interval.Refines (integralBound common.intersection.cells)
    (integralBound secondResult.frontier.cells) := common.intersection_refines_right

example : IntegrationFrontierRefines common.intersection.cells firstResult.frontier.cells :=
  NumericalFrontier.CommonReadings.commonReadings_intersection_refines firstResult.frontier secondResult.frontier
    pointRequest

/-- A satisfied numerical request takes the saved branch and retains the original point states. -/
example : NumericalFrontier.Producer.advance (NumericalFrontier.Continuous.producer modulus)
    firstResult.frontier requestFour = .reused requestFour firstResult.accurate :=
  NumericalFrontier.Producer.advance_reused (NumericalFrontier.Continuous.producer modulus)
    firstResult.frontier requestFour firstResult.accurate

/-- A satisfied numerical request selects reuse for any deferred observation bank. -/
example (readBank : Unit → List (NumericalPoint noisy)) :
    (NumericalFrontier.Continuous.producer modulus).advanceWithBank readBank firstResult.frontier requestFour =
      .reused requestFour firstResult.accurate :=
  (NumericalFrontier.Continuous.producer modulus).advanceWithBank_reused readBank
    firstResult.frontier requestFour firstResult.accurate

/-- The initial numerical history reads the carried frontier's actual point states. -/
example (actual : NumericalFrontier noisy)
    (same : actual = (NumericalFrontier.Continuous.producer modulus).frontier
      (NumericalFrontier.Continuous.producer modulus).controller.origin) :
    (NumericalFrontier.Continuous.producer modulus).retainedReadingsAt actual .initial same =
      actual.cells.map (fun cell => cell.item) := by
  rfl

example : IntegrationFrontierRefines (process.frontier later) (process.frontier saved) :=
  process.request_refines saved requestTwo.tolerance requestTwo.positive

example : (integralBound (process.frontier later)).width < requestTwo.tolerance :=
  process.request_width_lt saved requestTwo.tolerance requestTwo.positive

example : Fraction.abs ((integralBound later.1.cells).midpoint - (integralBound divergent.1.cells).midpoint) ≤
    (integralBound later.1.cells).width + (integralBound divergent.1.cells).width + historyCommon.pointBudget :=
  historyCommon.answers_difference_le _ _ (integralBound later.1.cells).midpoint_contains
    (integralBound divergent.1.cells).midpoint_contains

example : Fraction.abs (firstResult.answer - secondResult.answer) ≤
    (integralBound firstResult.frontier.cells).width + (integralBound secondResult.frontier.cells).width +
      common.pointBudget :=
  common.answers_difference_le firstResult.answer secondResult.answer firstResult.answer_contains
    secondResult.answer_contains

example : Fraction.abs (firstResult.answer - secondResult.answer) ≤
    requestFour.tolerance + requestTwo.tolerance + (pointRequest.tolerance + pointRequest.tolerance) :=
  firstResult.answer_difference_le secondResult pointRequest

end TestPurelib.Integration.Cell.Numerical.Refinement
