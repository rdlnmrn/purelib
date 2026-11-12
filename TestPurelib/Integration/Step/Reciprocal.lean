module
import Purelib.Integration.Step.Reciprocal.Integration
import Purelib.Integration.Step.Reciprocal.Integration.Observation
import Purelib.Integration.Step.Reciprocal.Integration.Continuation
import Purelib.Integration.Cell.Source.Exceptional
import Purelib.Data.Rat.Fraction.Cast.Order

/-! Exact rational evaluations at and around reciprocal cut points. -/

namespace TestPurelib.Integration.Step.Reciprocal

open Purelib.Data.Rat
open Purelib.Integration.Step.Reciprocal
open Purelib.Integration
open Purelib.Approximation

example : value 0 = 0 := value_zero

example : value (1 / 2) = 0 := value_at_reciprocal 2 (by decide)

example : value (1 / 3) = 1 := value_at_reciprocal 3 (by decide)

example : value (1 / 4) = 0 := value_at_reciprocal 4 (by decide)

example : value (2 / 5) = 0 := by decide

example : value (3 / 5) = 1 := by decide

example : value (2 / 7) = 1 := by decide

example : value (2 / 5) ≠ value (2 / 7) := by decide

example : cuts 3 = [1 / 2, 1 / 3, 1 / 4] := by decide

example (count : Nat) : (cuts count).length = count ∧ (cuts count).Nodup := cuts_distinct count

example : tailCount (1 / 2) = 6 := by decide

example : truncated 5 (1 / 7) = 0 ∧ value (1 / 7) = 1 := by decide

example : truncated 5 (1 / 3) = value (1 / 3) := by decide

/-- A finite exceptional construction for the original rule truncated at one fifth. -/
private def truncatedResult : SourceFrontier.Exceptional.Result (truncatedModulus 5 (by decide)) :=
  SourceFrontier.Exceptional.build (truncatedModulus 5 (by decide))
    ⟨32, Fraction.Cast.Order.natCast_pos_direct (by decide : 0 < 32)⟩

example : (integralBound truncatedResult.frontier.cells).width < 32 := truncatedResult.accurate

/-- Two positive requests select distinct reciprocal tails. -/
private def requestOne : AccuracyRequest := ⟨1, by decide⟩
private def requestTwo : AccuracyRequest := ⟨2, by decide⟩

/-- The first actual original-source integration result. -/
private def firstResult : Result := build requestOne

/-- An independently constructed result with another selected tail. -/
private def secondResult : Result := build requestTwo

/-- A coarse request whose complete reciprocal-step frontier has a small finite grid. -/
private def coarseRequest : AccuracyRequest :=
  ⟨80, Fraction.Cast.Order.natCast_pos_direct (by decide : 0 < 80)⟩

/-- The actual original-source result for the coarse request. -/
private def coarseResult : Result := build coarseRequest

/-- The actual reciprocal-step producer supplies the original persistent integration process. -/
private def process : IntegrationProcess (SourcePoint value) := producer.integrationProcess

/-- A nonempty saved history of reciprocal-step integration. -/
private def saved : process.State :=
  process.request process.initial requestTwo.tolerance requestTwo.positive

/-- A saved original reading above the first request's truncated tail. -/
private def aboveTail : SourcePoint value :=
  SourcePoint.observe value ⟨0, 1⟩ (1 / 2) (by decide) (by decide)

/-- A saved original reading inside that tail, where the sources may differ. -/
private def insideTail : SourcePoint value :=
  SourcePoint.observe value ⟨0, 1⟩ (1 / 10) (by decide) (by decide)

example : (auxiliaryCachedReadings requestOne [aboveTail, insideTail]).map (fun point => point.point) =
    [1 / 2] := by decide +kernel

example : (auxiliaryCachedReadings requestOne [aboveTail, insideTail]).map (fun point => point.reading) =
    [aboveTail.reading] := by decide +kernel

/-- The observed coarse request retains both original source owners and their ordered calls. -/
private def observedCoarse := Observation.computation [] coarseRequest
private def coarseOracle := Observation.originalReply coarseRequest

example := Observation.computation_original [] coarseRequest
example := Observation.computation_replay [] coarseRequest

/-- A wrong source operation stops the original reciprocal construction at its first call. -/
private def wrongOwner (_ : Observation.Query coarseRequest) : Observation.Reply coarseRequest := .inr insideTail

example : (match (observedCoarse.protocol.run wrongOwner).value with
    | .error (.operation _) => true
    | _ => false) = true ∧ (observedCoarse.protocol.run wrongOwner).trace.length = 1 := by decide +kernel

/-- An original truncated point on the marked initial tail. -/
private def tailOriginal : SourcePoint (truncated (tailCount coarseRequest.tolerance)) :=
  SourcePoint.observe _ ⟨0, 1⟩ 0 (by decide) (by decide)

/-- The same original point retained in one finite integration cell. -/
private def tailCell : IntegrationCell (SourcePoint (truncated (tailCount coarseRequest.tolerance))) :=
  ⟨tailOriginal, 1, by decide, 0, 1, by decide⟩

/-- The original reciprocal target point at that same tag. -/
private def tailTarget : SourcePoint value := SourcePoint.observe value ⟨0, 1⟩ 0 (by decide) (by decide)

/-- An uncached marked tail makes one target-source request; the saved target point makes none. -/
example : let endpoint := 1 / (tailCount coarseRequest.tolerance : Fraction.Rational)
    let program := SourceFrontier.Initial.Observation.cell [] endpoint unitRange (agreement coarseRequest) tailCell
    (program.protocol.run (SourceFrontier.Initial.Observation.originalReply value)).trace.length = 1 := by
  decide +kernel

example : let endpoint := 1 / (tailCount coarseRequest.tolerance : Fraction.Rational)
    let program := SourceFrontier.Initial.Observation.cell [tailTarget] endpoint unitRange (agreement coarseRequest)
      tailCell
    (program.protocol.run (SourceFrontier.Initial.Observation.originalReply value)).trace.length = 0 := by
  decide +kernel

/-- The original nonempty reciprocal history has a complete public-request observer and exact replay. -/
example := Observation.Continuation.historyComputation_original saved requestOne
example := Observation.Continuation.historyComputation_replay saved requestOne

example : tailCount requestOne.tolerance = 4 ∧ tailCount requestTwo.tolerance = 3 := by decide +kernel

example : coarseResult.frontier.cells.length = 6 ∧ coarseResult.answer = 7 / 12 := by decide +kernel

example : (integralBound firstResult.frontier.cells).width < requestOne.tolerance := firstResult.accurate

example : Fraction.abs (firstResult.answer - secondResult.answer) <
    requestOne.tolerance + requestTwo.tolerance := firstResult.answer_difference_lt secondResult

example : IntegrationFrontierRefines
    (process.frontier (process.request saved requestOne.tolerance requestOne.positive)) (process.frontier saved) :=
  process.request_refines saved requestOne.tolerance requestOne.positive

example (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    1 / (tailCount tolerance : Fraction.Rational) < tolerance / 2 := tail_width_lt tolerance positive

example (radius : Fraction.Rational) (positive : 0 < radius) :
    ∃ left right : Fraction.Rational,
      0 < left ∧ right ≤ 1 ∧ left < 1 / 2 ∧ 1 / 2 < right ∧
      1 / 2 - left < radius ∧ right - 1 / 2 < radius ∧
      ((value left = 0 ∧ value right = 1) ∨ (value left = 1 ∧ value right = 0)) :=
  jump_witnesses 0 radius positive

end TestPurelib.Integration.Step.Reciprocal
