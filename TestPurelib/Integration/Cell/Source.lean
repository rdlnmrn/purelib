module
import Purelib.Integration.Cell.Source
import Purelib.Integration.Cell.Source.Refinement
import Purelib.Integration.Cell.Source.Comparison
import Purelib.Integration.Cell.Source.Comparison.Weights
import Purelib.Integration.Cell.Source.Comparison.Observation
import Purelib.Integration.Cell.Source.Comparison.Observation.Cache
import Purelib.Integration.Cell.Source.Comparison.Intersection
import Purelib.Integration.Cell.Source.Continuous
import Purelib.Integration.Cell.Source.Continuous.Comparison
import Purelib.Integration.Cell.Source.Continuous.Producer
import Purelib.Integration.Cell.Source.Continuous.Observation.Continuation
import Purelib.Integration.Partition.Uniform.Grid
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! Exact rational readings over independently partitioned unit intervals. -/

namespace TestPurelib.Integration.Cell.Source

open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Integration.SourceFrontier
open Purelib.Integration.Partition
open Purelib.Approximation
open Purelib.Integration.SourceFrontier.Continuous.Observation

/-- The exact rational identity source. -/
private def source (point : Fraction.Rational) : Fraction.Rational := point

/-- The identity source computes its own distance for each requested variation. -/
private def identityModulus : Rational.Uniform.Modulus source where
  radius := id
  radius_pos := fun _ positive => positive
  variation := by
    intro variation positive first second _ ordered _ small
    have negative := Fraction.Order.Arithmetic.neg_le_neg_direct positive.le
    rw [neg_zero] at negative
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct negative first
    have lower : first - variation ≤ first := by
      have identity : -variation + first = first - variation := by ring1
      rw [identity, Fraction.Field.zero_add] at shifted
      exact shifted
    change second - first < variation at small
    have upper := Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mp small.le
    have swapped : variation + first = first + variation := by ring1
    rw [swapped] at upper
    exact ⟨lower.trans ordered, upper⟩

/-- The shared persistent producer retains the original identity modulus and its results. -/
private def identityProducer : SourceFrontier.Producer source := SourceFrontier.Continuous.producer identityModulus

/-- The computed frontier for a unit-width request to the identity source. -/
private def identityResult : SourceFrontier.Continuous.Result identityModulus :=
  SourceFrontier.Continuous.build identityModulus ⟨1, by decide⟩

/-- An independent coarser request to the same exact nonconstant source. -/
private def coarseIdentityResult : SourceFrontier.Continuous.Result identityModulus :=
  SourceFrontier.Continuous.build identityModulus ⟨2, by decide⟩

/-- Continue the saved identity frontier with a separate coarser request. -/
private def firstContinuation : SourceFrontier.Producer.Continuation identityProducer identityResult.frontier :=
  SourceFrontier.Producer.advance identityProducer identityResult.frontier ⟨2, by decide⟩

/-- Continue the actual nonempty saved frontier with another positive request. -/
private def secondContinuation :
    SourceFrontier.Producer.Continuation identityProducer firstContinuation.frontier :=
  SourceFrontier.Producer.advance identityProducer firstContinuation.frontier ⟨1, by decide⟩

/-- The existing bound-process interface built from the identity source. -/
private def identityProcess : BoundProcess := identityProducer.boundProcess

/-- The original cell-splitting integration process for the same exact source. -/
private def identityIntegration : IntegrationProcess (SourcePoint source) :=
  identityProducer.integrationProcess

/-- One saved frontier from the original cell-splitting process. -/
private def integrationState : identityIntegration.State :=
  identityIntegration.request identityIntegration.initial 2 (by decide)

/-- An actual saved state after requesting a second, independently computed partition. -/
private def firstState : identityProcess.State := identityProcess.request identityProcess.initial 2 (by decide)

/-- Continue from the nonempty saved state with another request. -/
private def secondState : identityProcess.State := identityProcess.request firstState 1 (by decide)

/-- A tighter request changes the retained mesh after a nonempty history. -/
private def finerState : identityProcess.State := identityProcess.request firstState (1 / 2) (by decide)

/-- An independently ordered request history from the same original source. -/
private def divergentState : identityProcess.State :=
  identityProcess.request identityProcess.initial (1 / 2) (by decide)

/-- Common readings retain the actual frontiers from both independent histories. -/
private def divergentCommon : SourceFrontier.CommonReadings secondState.1 divergentState.1 :=
  SourceFrontier.commonReadings secondState.1 divergentState.1

/-- A second exact source with the same unit restriction and a different exterior. -/
private def alternateSource (point : Fraction.Rational) : Fraction.Rational :=
  if 0 ≤ point ∧ point ≤ 1 then point else 0

/-- The unsplit unit interval. -/
private def unitInterval : Partition.Interval := ⟨0, 1⟩

/-- The left half of the unit interval. -/
private def leftInterval : Partition.Interval := ⟨0, 1 / 2⟩

/-- The right half of the unit interval. -/
private def rightInterval : Partition.Interval := ⟨1 / 2, 1⟩

/-- A distinct partition into four original quarter intervals. -/
private def quarters : Unit.Normalized := Unit.Normalized.ofRequest [1 / 4, 1 / 2, 3 / 4]

/-- The original midpoint reading of the unsplit interval. -/
private def wholePoint : SourcePoint source :=
  SourcePoint.observe source unitInterval (1 / 2) (by decide) (by decide)

/-- The original quarter-point reading of the left half. -/
private def leftPoint : SourcePoint alternateSource :=
  SourcePoint.observe alternateSource leftInterval (1 / 4) (by decide) (by decide)

/-- The original three-quarter-point reading of the right half. -/
private def rightPoint : SourcePoint alternateSource :=
  SourcePoint.observe alternateSource rightInterval (3 / 4) (by decide) (by decide)

/-- The actual saved observations from a separate coarse identity-source request. -/
private def coarseBank := coarseIdentityResult.frontier.cells.map (fun cell => cell.item)

/-- Observe a tighter request from the retained coarse identity frontier and its actual source bank. -/
private def observedRequest : AccuracyRequest := ⟨1, by decide⟩
private def observedPreparation := SourceFrontier.Continuous.Preparation.prepare identityModulus observedRequest
private def observedContinuation :=
  Continuation.computation identityModulus coarseIdentityResult.frontier coarseBank observedRequest
private def observedOracle := Continuation.originalReplyAll observedPreparation

/-- A finite source reply with the wrong tag at any displayed request. -/
private def wrongObservedReply (_ : Continuation.Query observedPreparation) : SourcePoint source :=
  SourcePoint.observe source unitInterval 1 (by decide) (by decide)

example : (observedContinuation.protocol.run observedOracle).value =
    .ok (identityProducer.advanceCached coarseBank coarseIdentityResult.frontier observedRequest) :=
  Continuation.computation_original identityModulus coarseIdentityResult.frontier coarseBank observedRequest

example : observedContinuation.protocol.replayExact (observedContinuation.protocol.run observedOracle).trace =
    .ok (.ok (identityProducer.advanceCached coarseBank coarseIdentityResult.frontier observedRequest)) :=
  Continuation.computation_replay identityModulus coarseIdentityResult.frontier coarseBank observedRequest

/-- The one shared start is reused; the four new mesh starts are the only source requests. -/
example : (observedContinuation.protocol.run observedOracle).trace.length = 4 := by decide +kernel

/-- A direct continuation with no extra bank still reuses the saved frontier's start reading. -/
example : ((Continuation.computation identityModulus coarseIdentityResult.frontier [] observedRequest).protocol.run
    observedOracle).trace.length = 4 := by decide +kernel

example : (match (observedContinuation.protocol.run wrongObservedReply).value with
    | .error (.source invalid) => decide (invalid.reported = 1)
    | _ => false) = true := by decide +kernel

example : (observedContinuation.protocol.run wrongObservedReply).trace.length = 1 := by decide +kernel

/-- A nonempty saved process history supplies its actual bank to a further observed continuation. -/
example : let request : AccuracyRequest := ⟨1 / 2, by decide⟩
    let cached := identityProducer.retainedReadings firstState.2
    let prepared := SourceFrontier.Continuous.Preparation.prepare identityModulus request
    ((Continuation.computation identityModulus firstState.1 cached request).protocol.run
      (Continuation.originalReplyAll prepared)).value =
        .ok (identityProducer.advanceCached cached firstState.1 request) :=
  Continuation.computation_original identityModulus firstState.1 _ ⟨1 / 2, by decide⟩

/-- The public persistent request and exact replay retain the same nonempty history state. -/
example : let request : AccuracyRequest := ⟨1 / 2, by decide⟩
    let prepared := SourceFrontier.Continuous.Preparation.prepare identityModulus request
    ((Continuation.historyComputation identityModulus integrationState request).protocol.run
      (Continuation.originalReplyAll prepared)).value =
        .ok (identityIntegration.request integrationState request.tolerance request.positive) :=
  Continuation.historyComputation_original identityModulus integrationState ⟨1 / 2, by decide⟩

/-- The unsplit cell with the exact unit range. -/
private def wholeCell : IntegrationCell (SourcePoint source) :=
  ⟨wholePoint, 1, by decide, 0, 1, by decide⟩

/-- The left half with its exact identity-source range. -/
private def leftCell : IntegrationCell (SourcePoint alternateSource) :=
  ⟨leftPoint, 1 / 2, by decide, 0, 1 / 2, by decide⟩

/-- The right half with its exact identity-source range. -/
private def rightCell : IntegrationCell (SourcePoint alternateSource) :=
  ⟨rightPoint, 1 / 2, by decide, 1 / 2, 1, by decide⟩

/-- The source-admitted unsplit partition with its retained midpoint reading. -/
private def whole : SourceFrontier source where
  partition := Unit.Normalized.ofRequest []
  cells := [wholeCell]
  domains_eq := rfl
  weight_eq := by
    intro cell member
    have equal := Membership.mem_singleton.mp member
    cases equal
    decide
  source_range := by
    intro cell member point lower upper
    have equal := Membership.mem_singleton.mp member
    cases equal
    exact ⟨lower, upper⟩

/-- The independently constructed halves with distinct retained tags and ranges. -/
private def halves : SourceFrontier alternateSource where
  partition := Unit.Normalized.ofRequest [1 / 2]
  cells := [leftCell, rightCell]
  domains_eq := by decide +kernel
  weight_eq := by
    intro cell member
    rcases Membership.mem_cons.mp member with equal | remaining
    · cases equal
      decide
    · have equal := Membership.mem_singleton.mp remaining
      cases equal
      decide
  source_range := by
    intro cell member point lower upper
    rcases Membership.mem_cons.mp member with equal | remaining
    · cases equal
      have unitBounds : 0 ≤ point ∧ point ≤ 1 := ⟨lower, upper.trans (by decide)⟩
      change 0 ≤ alternateSource point ∧ alternateSource point ≤ 1 / 2
      rw [alternateSource, if_pos unitBounds]
      exact ⟨lower, upper⟩
    · have equal := Membership.mem_singleton.mp remaining
      cases equal
      have unitBounds : 0 ≤ point ∧ point ≤ 1 := ⟨(by decide : (0 : Fraction.Rational) ≤ 1 / 2).trans lower, upper⟩
      change 1 / 2 ≤ alternateSource point ∧ alternateSource point ≤ 1
      rw [alternateSource, if_pos unitBounds]
      exact ⟨lower, upper⟩

/-- The actual common refinement and its separately retained source readings. -/
private def common : SourceFrontier.CommonReadings whole halves :=
  SourceFrontier.commonReadings whole halves

/-- The original comparison exposes the distinct owners' needed common-point reads. -/
private def observedComparison := Comparison.Observation.computation whole halves
private def comparisonOracle := Comparison.Observation.originalReply source alternateSource

example : (observedComparison.protocol.run comparisonOracle).value = .ok common :=
  Comparison.Observation.computation_original whole halves

example : observedComparison.protocol.replayExact (observedComparison.protocol.run comparisonOracle).trace =
    .ok (.ok common) := Comparison.Observation.computation_replay whole halves

/-- The midpoint parent is reused once; the other three owner-specific readings are requested. -/
example : (observedComparison.protocol.run comparisonOracle).trace.length = 3 := by decide +kernel

/-- Retain the actual left and right common readings under their separate original owners. -/
private def commonLeftBank := common.readings.map SourceFrontier.CommonReading.leftPoint
private def commonRightBank := common.readings.map SourceFrontier.CommonReading.rightPoint

/-- Repeat the exact comparison with its actual previously returned common points. -/
private def cachedComparison :=
  Comparison.Observation.Cache.computation commonLeftBank commonRightBank whole halves

example : (cachedComparison.protocol.run comparisonOracle).value = .ok ⟨common, rfl⟩ :=
  Comparison.Observation.Cache.computation_original commonLeftBank commonRightBank whole halves

example : cachedComparison.protocol.replayExact (cachedComparison.protocol.run comparisonOracle).trace =
    .ok (.ok ⟨common, rfl⟩) :=
  Comparison.Observation.Cache.computation_replay commonLeftBank commonRightBank whole halves

/-- Both original owners reuse the returned common readings without a source query. -/
example : (cachedComparison.protocol.run comparisonOracle).trace = [] := by decide +kernel

/-- A left-only bank leaves the two original right-owner reads as the only cache misses. -/
private def leftCachedComparison := Comparison.Observation.Cache.computation commonLeftBank [] whole halves

example : (leftCachedComparison.protocol.run comparisonOracle).trace.length = 2 := by decide +kernel

/-- A wrong owner at the first right-source miss stops the cached comparison. -/
private def wrongCachedOwner (_ : Comparison.Observation.Query) :
    Comparison.Observation.Reply source alternateSource := .inl wholePoint

example : (match (leftCachedComparison.protocol.run wrongCachedOwner).value with
    | .error (.owner (.inr _)) => true
    | _ => false) = true ∧ (leftCachedComparison.protocol.run wrongCachedOwner).trace.length = 1 := by decide +kernel

/-- A same-owner reply at the wrong tag stops the cached comparison at that miss. -/
private def wrongCachedTag (_ : Comparison.Observation.Query) :
    Comparison.Observation.Reply source alternateSource := .inr rightPoint

example : (match (leftCachedComparison.protocol.run wrongCachedTag).value with
    | .error (.tag (.inr _) _ _) => true
    | _ => false) = true ∧ (leftCachedComparison.protocol.run wrongCachedTag).trace.length = 1 := by decide +kernel

/-- A reply from the other source owner stops the original comparison immediately. -/
private def wrongComparisonOwner (_ : Comparison.Observation.Query) :
    Comparison.Observation.Reply source alternateSource := .inr leftPoint

example : (match (observedComparison.protocol.run wrongComparisonOwner).value with
    | .error (.owner _) => true
    | _ => false) = true := by decide +kernel

example : (observedComparison.protocol.run wrongComparisonOwner).trace.length = 1 := by decide +kernel

/-- A same-owner reply at the wrong rational point also stops the comparison. -/
private def wrongComparisonTag (_ : Comparison.Observation.Query) :
    Comparison.Observation.Reply source alternateSource := .inl wholePoint

example : (match (observedComparison.protocol.run wrongComparisonTag).value with
    | .error (.tag _ _ _) => true
    | _ => false) = true := by decide +kernel

example : (observedComparison.protocol.run wrongComparisonTag).trace.length = 1 := by decide +kernel

/-- The rational midpoint of a retained child interval. -/
private def midpointTag (interval : Partition.Interval) : Fraction.Rational := (interval.start + interval.finish) / 2

/-- A valid child contains its midpoint tag. -/
private theorem midpointTag_inside (interval : Partition.Interval) (valid : interval.Valid) :
    interval.start ≤ midpointTag interval ∧ midpointTag interval ≤ interval.finish :=
  ⟨Interval.Bisection.lower_le_midpoint ⟨interval.start, interval.finish, valid.2.1.le⟩,
    Interval.Bisection.midpoint_le_upper ⟨interval.start, interval.finish, valid.2.1.le⟩⟩

/-- The same original frontiers with independently selected midpoint tags on their common children. -/
private def midpointCommon : SourceFrontier.CommonReadings whole halves :=
  SourceFrontier.commonReadingsWithTags whole halves midpointTag midpointTag_inside

/-- The independently supplied quarter partition keeps both original parent owners. -/
private def quarterRefinement : Unit.Common.CommonRefinement whole.partition halves.partition :=
  Unit.Common.CommonRefinement.ofPartition whole.partition halves.partition quarters (by
    intro cut member
    change cut ∈ [] at member
    nomatch member) (by
    intro cut member
    change cut ∈ [1 / 2] at member
    have equal := Membership.mem_singleton.mp member
    rw [equal]
    change (1 / 2 : Fraction.Rational) ∈ [1 / 4, 1 / 2, 3 / 4]
    exact List.Mem.tail _ (List.Mem.head _))

/-- Read the separately supplied quarter refinement at all of its midpoint tags. -/
private def quarterCommon : SourceFrontier.CommonReadings whole halves :=
  SourceFrontier.readRefinement whole halves quarterRefinement midpointTag midpointTag_inside

/-- Split the original cell at one half using independent quarter and midpoint tags. -/
private def split : IntegrationSplit wholeCell :=
  IntegrationCell.Source.splitAt wholeCell (whole.admitted wholeCell List.mem_cons_self) (1 / 2) (1 / 4) (1 / 2)
    (by decide) (by decide) (by decide)

/-- Split at the endpoint while retaining the zero-length left child. -/
private def endpointSplit : IntegrationSplit wholeCell :=
  IntegrationCell.Source.splitAt wholeCell (whole.admitted wholeCell List.mem_cons_self) 0 0 (1 / 2)
    (by decide) (by decide) (by decide)

/-- The retained left child from the first split. -/
private def firstChild : IntegrationCell (SourcePoint source) :=
  IntegrationCell.Source.leftChild wholeCell (1 / 2) (1 / 4) (by decide) (by decide)

/-- The first child's pointwise source admission follows from the actual parent split. -/
private theorem firstChild_admitted : IntegrationCell.Source.Admitted firstChild :=
  IntegrationCell.Source.splitAt_child_admitted wholeCell (whole.admitted wholeCell List.mem_cons_self)
    (1 / 2) (1 / 4) (1 / 2) (by decide) (by decide) (by decide) firstChild List.mem_cons_self

/-- Split the retained child again without rebuilding or replacing its parent. -/
private def finerSplit : IntegrationSplit firstChild :=
  IntegrationCell.Source.splitAt firstChild firstChild_admitted (1 / 4) 0 (1 / 4)
    (by decide) (by decide) (by decide)

/-- Build the same two-interval partition directly from its exact source and unit range. -/
private def constructed : SourceFrontier source := by
  let partition := Unit.Normalized.ofRequest [1 / 2]
  exact SourceFrontier.ofRanges source partition (fun _ => ⟨0, 1, by decide⟩) (by
    intro interval member point lower upper
    have valid := partition.valid interval member
    exact ⟨valid.1.trans lower, upper.trans valid.2.2⟩)

/-- The identity source on the retained halves with each exact child interval as its value range. -/
private def identityHalves : SourceFrontier source :=
  SourceFrontier.ofRanges source (Unit.Normalized.ofRequest [1 / 2])
    (fun tag => ⟨tag.interval.start, tag.interval.finish, tag.start_le.trans tag.point_le_finish⟩)
    (fun _ _ _ lower upper => ⟨lower, upper⟩)

/-- Common readings preserve the original unsplit frontier and the exact half-interval ranges. -/
private def intersectionCommon : SourceFrontier.CommonReadings whole identityHalves :=
  SourceFrontier.commonReadings whole identityHalves

/-- The common children with their two original source ranges intersected. -/
private def intersected : SourceFrontier source := intersectionCommon.intersection

/-- An exact constant-one source on the same independently retained partition. -/
private def ones : SourceFrontier (fun _ => 1) :=
  SourceFrontier.ofRanges (fun _ => 1) (Unit.Normalized.ofRequest [1 / 2]) (fun _ => ⟨1, 1, le_rfl⟩)
    (fun _ _ _ _ _ => ⟨le_rfl, le_rfl⟩)

/-- Common readings of the identity and constant-one sources retain their actual discrepancies. -/
private def differingCommon : SourceFrontier.CommonReadings constructed ones :=
  SourceFrontier.commonReadings constructed ones

/-- The source replacement agrees only on the unit interval, not everywhere. -/
example : source 2 ≠ alternateSource 2 := by decide +kernel

/-- A third-unit mesh request computes four retained intervals. -/
example : (Uniform.Grid.forWidth (1 / 3)).intervals.length = 4 := by decide +kernel

/-- The concrete source request computes five cells from its quarter-width modulus response. -/
example : identityResult.frontier.cells.length = 5 := by decide +kernel

/-- Its finite source-linked integral enclosure satisfies the retained request. -/
example : (integralBound identityResult.frontier.cells).width < 1 := identityResult.accurate

/-- The constructor evaluates the actual source at its retained left-endpoint tags. -/
example : identityResult.frontier.taggedSum = (2 / 5 : Fraction.Rational) := by decide +kernel

/-- The chosen rational answer is the midpoint of the actual computed source enclosure. -/
example : identityResult.answer = (2 / 5 : Fraction.Rational) := by decide +kernel

/-- A separate request computes a different partition and rational answer. -/
example : coarseIdentityResult.frontier.cells.length = 3 ∧
    coarseIdentityResult.answer = (1 / 3 : Fraction.Rational) := by decide +kernel

/-- The two actual continuous constructions agree within their retained positive requests. -/
example : Fraction.abs (identityResult.answer - coarseIdentityResult.answer) < 1 + 2 :=
  identityResult.answer_difference_lt_of_same coarseIdentityResult (fun _ _ _ => rfl)

/-- Both actual saved continuations refine their immediately preceding enclosures. -/
example : (integralBound firstContinuation.frontier.cells).Refines (integralBound identityResult.frontier.cells) ∧
    (integralBound secondContinuation.frontier.cells).Refines (integralBound firstContinuation.frontier.cells) :=
  ⟨firstContinuation.refines_previous, secondContinuation.refines_previous⟩

/-- The second actual continuation meets its own retained request. -/
example : (integralBound secondContinuation.frontier.cells).width < 1 := secondContinuation.accurate

/-- A looser request reuses the original five-cell frontier without building another partition. -/
example : firstState.1.partition.intervals.length = 5 := by decide +kernel

/-- The exact saved branch is selected before any fresh producer result is constructed. -/
example : firstContinuation = .reused ⟨2, by decide⟩ (identityResult.accurate.trans (by decide)) :=
  SourceFrontier.Producer.advance_reused identityProducer identityResult.frontier ⟨2, by decide⟩
    (identityResult.accurate.trans (by decide))

/-- A satisfied request selects reuse for any deferred observation bank. -/
example (readBank : Unit → List (SourcePoint source)) :
    identityProducer.advanceWithBank readBank identityResult.frontier ⟨2, by decide⟩ =
      .reused ⟨2, by decide⟩ (identityResult.accurate.trans (by decide)) :=
  identityProducer.advanceWithBank_reused readBank identityResult.frontier ⟨2, by decide⟩
    (identityResult.accurate.trans (by decide))

/-- The initial history reads the carried frontier's actual cells. -/
example (actual : SourceFrontier source)
    (same : actual = identityProducer.frontier identityProducer.controller.origin) :
    identityProducer.retainedReadingsAt actual .initial same = actual.cells.map (fun cell => cell.item) := by
  rfl

/-- A subsequent satisfied request retains the very same original frontier. -/
example : secondContinuation.frontier = identityResult.frontier := by
  have first : firstContinuation.frontier = identityResult.frontier := by
    change (SourceFrontier.Producer.advance identityProducer identityResult.frontier ⟨2, by decide⟩).frontier = _
    rw [SourceFrontier.Producer.advance_reused identityProducer identityResult.frontier ⟨2, by decide⟩
      (identityResult.accurate.trans (by decide))]
    rfl
  have paid : (integralBound firstContinuation.frontier.cells).width < (1 : Fraction.Rational) := by
    rw [first]
    exact identityResult.accurate
  change (SourceFrontier.Producer.advance identityProducer firstContinuation.frontier ⟨1, by decide⟩).frontier = _
  rw [SourceFrontier.Producer.advance_reused identityProducer firstContinuation.frontier ⟨1, by decide⟩ paid]
  exact first

/-- The bound-process request refines the actual nonempty saved state and meets the new tolerance. -/
example : (identityProcess.bound secondState).Refines (identityProcess.bound firstState) ∧
    (identityProcess.bound secondState).width < 1 :=
  ⟨identityProcess.request_refines firstState 1 (by decide), identityProcess.accurate firstState 1 (by decide)⟩

/-- A later request is a certified finite split refinement of the actual saved frontier. -/
example : IntegrationFrontierRefines
    (identityIntegration.frontier (identityIntegration.request integrationState 1 (by decide)))
    (identityIntegration.frontier integrationState) :=
  identityIntegration.request_refines integrationState 1 (by decide)

/-- Independently ordered saved histories compare through their actual rational source restrictions. -/
example : Fraction.abs
    ((identityProcess.bound secondState).midpoint - (identityProcess.bound divergentState).midpoint) ≤
    (identityProcess.bound secondState).width + (identityProcess.bound divergentState).width :=
  divergentCommon.answers_difference_le_of_same _ _
    (identityProcess.bound secondState).midpoint_contains (identityProcess.bound divergentState).midpoint_contains
    (fun _ _ _ => rfl)

/-- The computed tagged sum has the proved half-width error bound against the chosen answer. -/
example : Fraction.abs (identityResult.frontier.taggedSum - identityResult.answer) ≤
    (integralBound identityResult.frontier.cells).width * (1 / 2) :=
  identityResult.answer_error _ identityResult.frontier.taggedSum_contains

/-- Every actual retained interval in that computed mesh is strictly shorter than a third. -/
example (interval : Partition.Interval) (member : interval ∈ (Uniform.Grid.forWidth (1 / 3)).intervals) :
    interval.signedLength < 1 / 3 := Uniform.Grid.forWidth_interval_lt (by decide) interval member

/-- The unsplit source frontier retains exactly unit weight. -/
example : integrationWeight whole.cells = 1 := whole.totalWeight

/-- Clamping quarter intervals to the retained left parent accounts for its length exactly. -/
example : Partition.Interval.lengthSum (quarters.intervals.map
    (fun child => ⟨leftInterval.clamp child.start, leftInterval.clamp child.finish⟩)) =
    leftInterval.signedLength := quarters.clamped_lengthSum leftInterval (by
  change (0 : Fraction.Rational) ≤ 0 ∧ (0 : Fraction.Rational) < 1 / 2 ∧ (1 / 2 : Fraction.Rational) ≤ 1
  exact ⟨by decide, by decide, by decide⟩)

/-- The parent retains its two quarter lengths and assigns zero to the intervals beyond its endpoint. -/
example : quarters.intervals.map (fun child =>
    (⟨leftInterval.clamp child.start, leftInterval.clamp child.finish⟩ : Partition.Interval).signedLength) =
    [1 / 4, 1 / 4, 0, 0] := by decide +kernel

/-- The original midpoint tagged sum is contained in its source-linked range. -/
example : (integralBound whole.cells).Contains whole.taggedSum := whole.taggedSum_contains

/-- The source reading at the original midpoint is reused unchanged. -/
example : wholePoint.readAt (1 / 2) = wholePoint.reading := wholePoint.readAt_point

/-- A later mesh can retrieve a reading retained by an earlier request. -/
example : ((identityProducer.retainedReadings finerState.2).map (fun point => point.point)).contains (1 / 5) =
    true := by
  decide +kernel

/-- Looking past a different cached tag reuses the matching saved reading. -/
example : SourcePoint.readCached source
    [SourcePoint.observe source unitInterval 0 (by decide) (by decide), wholePoint] (1 / 2) =
    wholePoint.reading := by
  rw [SourcePoint.readCached_cons_ne _ _ _ (by decide)]
  change SourcePoint.readCached source [wholePoint] wholePoint.point = wholePoint.reading
  exact SourcePoint.readCached_head wholePoint []

/-- A common comparison consumes one saved reading for both original parent points. -/
example : (SourceFrontier.cachedPair [wholePoint] wholePoint
    (SourcePoint.observe source unitInterval (1 / 4) (by decide) (by decide)) (1 / 2)).val =
    (wholePoint.reading, wholePoint.reading) := by
  change (SourcePoint.readCached source [wholePoint] wholePoint.point,
    SourcePoint.readCached source [wholePoint] wholePoint.point) = _
  rw [SourcePoint.readCached_head]

/-- The actual common cells read back to the computed common interval cache. -/
example : common.cells.map (fun cell => cell.item.entry.child) = common.refinement.partition.intervals :=
  common.cells_domains

/-- The two independently constructed frontiers agree on their common tagged sum. -/
example : common.leftSum = common.rightSum := common.leftSum_eq_rightSum (fun point lower upper => by
  change point = alternateSource point
  rw [alternateSource, if_pos ⟨lower, upper⟩])

/-- Equal restricted sources have zero length-weighted discrepancy at the actual common tags. -/
example : common.pointBudget = 0 := by decide +kernel

/-- Distinct sources retain their computed nonzero discrepancy rather than assuming agreement. -/
example : differingCommon.pointBudget = (3 / 4 : Fraction.Rational) := by decide +kernel

/-- The common sums are quantitatively controlled by their actual point-reading budget. -/
example : Fraction.abs (differingCommon.leftSum - differingCommon.rightSum) ≤ differingCommon.pointBudget :=
  differingCommon.sum_difference_le_pointBudget

/-- The two original enclosures bound their own tagged answers using their actual common readings. -/
example : Fraction.abs (whole.taggedSum - halves.taggedSum) ≤
    (integralBound whole.cells).width + (integralBound halves.cells).width + common.pointBudget :=
  common.answers_difference_le _ _ whole.taggedSum_contains halves.taggedSum_contains

/-- The unit-restricted source equality removes the point budget for distinct partitions and tags. -/
example : Fraction.abs (whole.taggedSum - halves.taggedSum) ≤
    (integralBound whole.cells).width + (integralBound halves.cells).width :=
  common.answers_difference_le_of_same _ _ whole.taggedSum_contains halves.taggedSum_contains (by
    intro point lower upper
    change point = alternateSource point
    rw [alternateSource, if_pos ⟨lower, upper⟩])

/-- The computed common child lengths still add to exactly one. -/
example : integrationWeight common.cells = 1 := common.totalWeight

/-- Both original partitions retain their own parent occurrence at each common child. -/
example : common.readings.map (fun reading => (reading.entry.leftOwner.index, reading.entry.rightOwner.index)) =
    [(0, 0), (0, 1)] := by decide +kernel

/-- The computed shared left-endpoint tags have exact weighted sum one quarter. -/
example : common.leftSum = (1 / 4 : Fraction.Rational) := by decide +kernel

/-- Midpoint tags give a different actual common sum while retaining the same original parents. -/
example : midpointCommon.leftSum = (1 / 2 : Fraction.Rational) := by decide +kernel

/-- The independently tagged common sum is still admitted by the original frontier. -/
example : (integralBound whole.cells).Contains midpointCommon.leftSum := midpointCommon.leftSum_contains

/-- The separately supplied refinement retains all four child occurrences. -/
example : quarterCommon.readings.length = 4 := by decide +kernel

/-- Its actual four midpoint readings also remain inside the original two enclosures. -/
example : (integralBound whole.cells).Contains quarterCommon.leftSum ∧
    (integralBound halves.cells).Contains quarterCommon.rightSum :=
  ⟨quarterCommon.leftSum_contains, quarterCommon.rightSum_contains⟩

/-- The range constructor computes the two original left-endpoint tags. -/
example : constructed.cells.map (fun cell => cell.item.point) = [0, 1 / 2] := by decide +kernel

/-- Its actual cached source readings have the expected weighted sum. -/
example : constructed.taggedSum = (1 / 4 : Fraction.Rational) := by decide +kernel

/-- Source-derived intersections narrow the unsplit enclosure from width one to one half. -/
example : (integralBound intersected.cells).width = (1 / 2 : Fraction.Rational) := by decide +kernel

/-- The intersected child frontier refines each original integral enclosure. -/
example : (integralBound intersected.cells).Refines (integralBound whole.cells) ∧
    (integralBound intersected.cells).Refines (integralBound identityHalves.cells) :=
  ⟨intersectionCommon.intersection_refines_left, intersectionCommon.intersection_refines_right⟩

/-- The actual split uses the displayed child tags and sums their source readings. -/
example : weightedEvaluation SourcePoint.reading split.children = (3 / 8 : Fraction.Rational) := by decide +kernel

/-- An endpoint cut retains both children and their exact zero and unit weights. -/
example : endpointSplit.children.map (fun cell => cell.weight) = [0, 1] := by decide +kernel

/-- A second split of the actual child retains both quarter-length occurrences. -/
example : finerSplit.children.map (fun cell => cell.weight) = [1 / 4, 1 / 4] := by decide +kernel

/-- The right child reuses the parent reading when its tag is the parent's original midpoint. -/
example : (IntegrationCell.Source.rightChild wholeCell (1 / 2) (1 / 2) (by decide) (by decide)).item.reading =
    wholePoint.reading := by
  change wholePoint.readAt (1 / 2) = wholePoint.reading
  exact wholePoint.readAt_point

/-- The source-linked split's child-tagged sum lies in the original parent enclosure. -/
example : (integralBound [wholeCell]).Contains (weightedEvaluation SourcePoint.reading split.children) :=
  IntegrationCell.Source.splitAt_taggedSum_contains wholeCell (whole.admitted wholeCell List.mem_cons_self)
    (1 / 2) (1 / 4) (1 / 2)
    (by decide) (by decide) (by decide)

/-- The original frontier also bounds the retained tags through its certified split history. -/
example : (integralBound whole.cells).Contains (weightedEvaluation SourcePoint.reading split.children) := by
  apply whole.refinedTaggedSum_contains split.children
  · change IntegrationFrontierRefines ([] ++ split.children ++ []) ([] ++ [wholeCell] ++ [])
    exact IntegrationFrontierRefines.split [] [] wholeCell split
  · intro cell member
    exact IntegrationCell.Source.splitAt_child_admitted wholeCell (whole.admitted wholeCell List.mem_cons_self)
      (1 / 2) (1 / 4) (1 / 2) (by decide) (by decide) (by decide) cell member

end TestPurelib.Integration.Cell.Source
