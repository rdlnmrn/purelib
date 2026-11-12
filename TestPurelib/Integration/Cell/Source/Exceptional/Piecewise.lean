module
import Purelib.Integration.Cell.Source.Exceptional.Piecewise
import Purelib.Integration.Cell.Source.Exceptional.Region
import Purelib.Integration.Cell.Source.Exceptional.Region.Builder
import Purelib.Integration.Cell.Source.Exceptional.Region.Observation
import Purelib.Integration.Cell.Source.Exceptional.Producer
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! Piece-specific radii and a rational jump on an original subdivision. -/

namespace TestPurelib.Integration.Cell.Source.Exceptional.Piecewise

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Integration.SourceFrontier.Exceptional
open Purelib.Integration.SourceFrontier.Exceptional.Region

/-- The source takes different constant values on the two sides of one rational cut. -/
private def step (point : Fraction.Rational) : Fraction.Rational :=
  if point < 1 / 2 then 0 else 1

/-- A value is within a positive variation of itself. -/
private theorem selfVariation (value variation : Fraction.Rational) (positive : 0 < variation) :
    value - variation ≤ value ∧ value ≤ value + variation := by
  have negative := Fraction.Order.Arithmetic.neg_le_neg_direct positive.le
  rw [neg_zero] at negative
  have lower := Fraction.Order.Arithmetic.add_le_add_right_direct negative value
  have upper := Fraction.Order.Arithmetic.add_le_add_right_direct positive.le value
  have lowerEq : -variation + value = value - variation := by ring1
  have upperEq : variation + value = value + variation := by ring1
  rw [lowerEq, Fraction.Field.zero_add] at lower
  rw [Fraction.Field.zero_add, upperEq] at upper
  exact ⟨lower, upper⟩

/-- The original subdivision and its two distinct piece-radius rules. -/
private def subdivision : Piecewise.Modulus step where
  partition := Partition.Unit.Normalized.ofRequest [1 / 2]
  magnitude := 1
  magnitude_nonnegative := by decide
  bounded := by
    intro point _ _
    unfold step
    split <;> decide
  radius := fun interval variation => if interval.start = 0 then variation else variation / 2
  radius_pos := by
    intro interval _ variation positive
    split
    · exact positive
    · exact Fraction.Order.Field.div_pos_direct positive (by decide)
  variation := by
    intro interval _ variation positive first second _ ordered _ avoids _
    have cutMember : (1 / 2 : Fraction.Rational) ∈
        (Partition.Unit.Normalized.ofRequest [1 / 2]).cuts :=
      (Partition.Unit.Normalize.mem_normalize (1 / 2) [1 / 2]).mpr
        ⟨List.Mem.head [], by decide, by decide⟩
    have noHalf := avoids (1 / 2) (List.Mem.tail 0 (List.Mem.tail 1 cutMember))
    have same : step first = step second := by
      by_cases firstBefore : first < 1 / 2
      · by_cases secondBefore : second < 1 / 2
        · unfold step
          rw [if_pos firstBefore, if_pos secondBefore]
        · have after := Fraction.Order.Arithmetic.le_of_not_gt_direct secondBefore
          exact (noHalf ⟨firstBefore.le, after⟩).elim
      · by_cases secondBefore : second < 1 / 2
        · have after := Fraction.Order.Arithmetic.le_of_not_gt_direct firstBefore
          exact (secondBefore.2 (after.trans ordered)).elim
        · unfold step
          rw [if_neg firstBefore, if_neg secondBefore]
    rw [same]
    exact selfVariation (step second) variation positive

/-- The finite subdivision derives the original exceptional-source contract. -/
private def modulus := subdivision.toExceptional

/-- Two independent positive requests use the same original subdivision source. -/
private def firstRequest : AccuracyRequest :=
  ⟨80, Fraction.Cast.Order.natCast_pos_direct (by decide : 0 < 80)⟩
private def secondRequest : AccuracyRequest :=
  ⟨64, Fraction.Cast.Order.natCast_pos_direct (by decide : 0 < 64)⟩
private def first := SourceFrontier.Exceptional.build modulus firstRequest
private def second := SourceFrontier.Exceptional.build modulus secondRequest

example : modulus.points = [0, 1, 1 / 2] := by decide +kernel

example : subdivision.radius ⟨0, 1 / 2⟩ 4 = 4 ∧ subdivision.radius ⟨1 / 2, 1⟩ 4 = 2 := by
  constructor <;> decide +kernel

example : (integralBound first.frontier.cells).width < firstRequest.tolerance := first.accurate

example : (integralBound second.frontier.cells).width < secondRequest.tolerance := second.accurate

/-- The actual derived source supplies persistent integration refinements. -/
private def process := (SourceFrontier.Exceptional.producer modulus).integrationProcess
private def saved := process.request process.initial firstRequest.tolerance firstRequest.positive
private def later := process.request saved secondRequest.tolerance secondRequest.positive

example : IntegrationFrontierRefines (process.frontier later) (process.frontier saved) :=
  process.request_refines saved secondRequest.tolerance secondRequest.positive

/-- A nonuniform cell boundary is shared with an exceptional region endpoint. -/
private def regionPartition := Partition.Unit.Normalized.ofRequest [1 / 4, 1 / 2, 3 / 4]
private def region : Partition.Interval := ⟨1 / 4, 1 / 2⟩

example : regionPartition.regionsLength [region, region] = (3 / 4 : Fraction.Rational) := by decide +kernel

example : regionPartition.regionsLength [] = 0 := by decide +kernel

example (retained : IntegrationCell (SourcePoint step))
    (unmarked : retained.item.interval.regionMarked [region] = false) :
    (Region.cell [region] ⟨-1, 1, by decide⟩ (fun _ _ => rfl) retained).item.reading = retained.item.reading :=
  Region.cell_reading_of_unmarked [region] ⟨-1, 1, by decide⟩ (fun _ _ => rfl) retained unmarked

/-- An exact zero source on the single original unit cell. -/
private def zeroSource (_ : Fraction.Rational) : Fraction.Rational := 0

/-- The original cell caches the exact zero reading and range. -/
private def zeroFrontier : SourceFrontier zeroSource :=
  SourceFrontier.ofRanges zeroSource (Partition.Unit.Normalized.ofRequest []) (fun _ => ⟨0, 0, by decide⟩) (by
    intro _ _ _ _ _
    change (0 : Fraction.Rational) ≤ 0 ∧ 0 ≤ 0
    exact ⟨by decide, by decide⟩)

/-- Run the checked replacement with a half-unit width request. -/
private def regionAttempt (regions : List Partition.Interval) : Region.Attempt zeroSource zeroSource :=
  Region.Attempt.make zeroFrontier regions ⟨0, 1, by decide⟩ (fun _ _ => rfl)
    (fun _ _ _ => by
      change (0 : Fraction.Rational) ≤ 0 ∧ 0 ≤ 1
      exact ⟨by decide, by decide⟩) ⟨1 / 2, by decide⟩

/-- Expose only the finite outcome tag for executable checking. -/
private def attemptSucceeded (regions : List Partition.Interval) : Bool :=
  match (regionAttempt regions).check with
  | .sufficient _ => true
  | .inconclusive _ => false

example : attemptSucceeded [] = true := by decide +kernel

example : attemptSucceeded [⟨0, 1⟩] = false := by decide +kernel

/-- The endpoint value differs from the constant source immediately to its right. -/
private def endpointJump (point : Fraction.Rational) : Fraction.Rational := if point = 0 then 1 else 0

/-- A shrinking closed region covers the endpoint, with constant variation outside it. -/
private def endpointRegions : Rational.Exceptional.Region.Modulus endpointJump where
  magnitude := 1
  magnitude_nonnegative := by decide
  bounded := by
    intro point _ _
    unfold endpointJump
    split <;> decide
  regions := fun length => [⟨0, min length 1⟩]
  region_bounds := by
    intro length positive region member
    have equal : region = ⟨0, min length 1⟩ := by
      cases member with
      | head => rfl
      | tail _ impossible => nomatch impossible
    rw [equal]
    change (0 : Fraction.Rational) ≤ 0 ∧ 0 ≤ min length 1 ∧ min length 1 ≤ 1
    exact ⟨by decide, Fraction.Order.Basic.le_min positive.le (by decide), Fraction.Order.Basic.min_le_right _ _⟩
  regions_length_le := by
    intro length _
    change min length 1 - 0 + 0 ≤ length
    have identity : min length 1 - 0 + 0 = min length 1 := by ring1
    rw [identity]
    exact Fraction.Order.Basic.min_le_left _ _
  radius := fun _ _ => 1
  radius_pos := by intro _ _ _ _; decide
  variation := by
    intro length positive variation variationPositive first second lower ordered _ avoids _
    have minPositive : 0 ≤ min length 1 := Fraction.Order.Basic.le_min positive.le (by decide)
    have firstNonzero : first ≠ 0 := by
      intro zero
      have secondNonnegative := lower.trans ordered
      have noRegion := avoids ⟨0, min length 1⟩ (List.Mem.head [])
      apply noRegion
      rw [zero]
      exact ⟨minPositive, secondNonnegative⟩
    have secondNonzero : second ≠ 0 := by
      intro zero
      have firstNonpositive : first ≤ 0 := zero ▸ ordered
      exact firstNonzero (Fraction.Order.Basic.le_antisymm _ _ firstNonpositive lower)
    have same : endpointJump first = endpointJump second := by
      unfold endpointJump
      rw [if_neg firstNonzero, if_neg secondNonzero]
    rw [same]
    exact selfVariation (endpointJump second) variation variationPositive

/-- The actual endpoint-region construction derives its frontier from the source data. -/
private def endpointIntegrated := Region.Builder.build endpointRegions ⟨8, by decide⟩

/-- The original endpoint-region result is reconstructed from its retained interval-start replies. -/
example : let request : AccuracyRequest := ⟨8, by decide⟩
    let prepared := Region.Builder.Preparation.prepare endpointRegions request
    let program := Builder.Observation.computation endpointRegions [] request
    (program.protocol.run (SourceFrontier.Observation.originalReply endpointJump prepared.partition)).value =
      .ok ⟨Region.Builder.buildCached endpointRegions [] request, rfl⟩ :=
  Builder.Observation.computation_original endpointRegions [] ⟨8, by decide⟩

example : let request : AccuracyRequest := ⟨8, by decide⟩
    let prepared := Region.Builder.Preparation.prepare endpointRegions request
    let program := Builder.Observation.computation endpointRegions [] request
    program.protocol.replayExact
      (program.protocol.run (SourceFrontier.Observation.originalReply endpointJump prepared.partition)).trace =
        .ok (.ok ⟨Region.Builder.buildCached endpointRegions [] request, rfl⟩) :=
  Builder.Observation.computation_replay endpointRegions [] ⟨8, by decide⟩

example : endpointJump 0 = 1 ∧ endpointJump (1 / 2) = 0 := by decide +kernel

example : (integralBound endpointIntegrated.frontier.cells).width <
    endpointIntegrated.preparation.request.tolerance := endpointIntegrated.accurate

/-- Persistent requests retain the original effective-region source and saved frontier. -/
private def endpointProcess := (Region.Builder.producer endpointRegions).integrationProcess
private def endpointSaved := endpointProcess.request endpointProcess.initial 8 (by decide)
private def endpointLater := endpointProcess.request endpointSaved 4 (by decide)

example : IntegrationFrontierRefines (endpointProcess.frontier endpointLater)
    (endpointProcess.frontier endpointSaved) :=
  endpointProcess.request_refines endpointSaved 4 (by decide)

/-- The retained endpoint-region history has a complete public-request observer and replay. -/
example := Builder.Observation.historyComputation_original endpointRegions endpointSaved ⟨4, by decide⟩

example := Builder.Observation.historyComputation_replay endpointRegions endpointSaved ⟨4, by decide⟩

/-- A different saved request order retains a separate original source history. -/
private def endpointOther := endpointProcess.request endpointProcess.initial 4 (by decide)
private def endpointDiverged := endpointProcess.request endpointOther 8 (by decide)

example : Fraction.abs ((integralBound endpointLater.1.cells).midpoint -
    (integralBound endpointDiverged.1.cells).midpoint) ≤
      (integralBound endpointLater.1.cells).width + (integralBound endpointDiverged.1.cells).width :=
  (SourceFrontier.commonReadings endpointLater.1 endpointDiverged.1).answers_difference_le_of_same _ _
    (Purelib.Data.Rat.Interval.midpoint_contains _) (Purelib.Data.Rat.Interval.midpoint_contains _) (fun _ _ _ => rfl)

/-- A cut value differs from both adjacent constant values. -/
private def isolatedCut (point : Fraction.Rational) : Fraction.Rational :=
  if point = 1 / 2 then 2 else step point

/-- The original subdivision controls the altered cut value through its exceptional-region rule. -/
private def isolatedSubdivision : Piecewise.Modulus isolatedCut where
  partition := subdivision.partition
  magnitude := 2
  magnitude_nonnegative := by decide
  bounded := by
    intro point _ _
    unfold isolatedCut
    by_cases cut : point = 1 / 2
    · rw [if_pos cut]
      decide
    · rw [if_neg cut]
      unfold step
      split <;> decide
  radius := subdivision.radius
  radius_pos := subdivision.radius_pos
  variation := by
    intro interval member variation positive first second lower ordered upper avoids small
    have cutMember : (1 / 2 : Fraction.Rational) ∈
        (Partition.Unit.Normalized.ofRequest [1 / 2]).cuts :=
      (Partition.Unit.Normalize.mem_normalize (1 / 2) [1 / 2]).mpr
        ⟨List.Mem.head [], by decide, by decide⟩
    have noCut := avoids (1 / 2) (List.Mem.tail 0 (List.Mem.tail 1 cutMember))
    have firstNotCut : first ≠ 1 / 2 := by
      intro equal
      apply noCut
      exact ⟨equal ▸ Fraction.Order.Basic.le_refl _, equal ▸ ordered⟩
    have secondNotCut : second ≠ 1 / 2 := by
      intro equal
      apply noCut
      exact ⟨equal ▸ ordered, equal ▸ Fraction.Order.Basic.le_refl _⟩
    change isolatedCut first - variation ≤ isolatedCut second ∧
      isolatedCut second ≤ isolatedCut first + variation
    unfold isolatedCut
    rw [if_neg firstNotCut, if_neg secondNotCut]
    exact subdivision.variation interval member variation positive first second lower ordered upper avoids small

/-- The actual finite-exception builder integrates the source with its distinct cut value. -/
private def isolatedResult := SourceFrontier.Exceptional.build isolatedSubdivision.toExceptional ⟨8, by decide⟩

example : isolatedCut 0 = 0 ∧ isolatedCut (1 / 2) = 2 ∧ isolatedCut 1 = 1 := by decide +kernel

example : (integralBound isolatedResult.frontier.cells).width < isolatedResult.preparation.request.tolerance :=
  isolatedResult.accurate

end TestPurelib.Integration.Cell.Source.Exceptional.Piecewise
