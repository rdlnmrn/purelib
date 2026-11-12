module
import Purelib.Integration.Cell.Source.Exceptional
import Purelib.Integration.Cell.Source.Exceptional.Producer
import Purelib.Integration.Cell.Source.Exceptional.Observation
import Purelib.Integration.Cell.Source.Comparison.Weights
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Tactic.Ring

/-! Finite exceptional-source requests with actual rational point readings. -/

namespace TestPurelib.Integration.Cell.Source.Exceptional

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Integration.SourceFrontier

/-- A constant source value obeys every positive variation request. -/
private theorem constantVariation (value variation : Fraction.Rational) (positive : 0 < variation) :
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

/-- The exact zero source. -/
private def zeroSource (_ : Fraction.Rational) : Fraction.Rational := 0

/-- Zero magnitude remains valid with repeated and endpoint exceptions. -/
private def zeroModulus : Rational.Exceptional.Modulus zeroSource where
  points := [0, 1 / 2, 1 / 2, 1]
  magnitude := 0
  magnitude_nonnegative := by decide
  bounded := fun _ _ _ => by
    change -(0 : Fraction.Rational) ≤ 0 ∧ (0 : Fraction.Rational) ≤ 0
    decide
  radius := fun _ => 1
  radius_pos := fun _ _ => by decide
  variation := fun variation positive _ _ _ _ _ _ _ => constantVariation 0 variation positive

/-- A fixed positive request for the zero-source examples. -/
private def request80 : AccuracyRequest :=
  ⟨80, Fraction.Cast.Order.natCast_pos_direct (by decide : 0 < 80)⟩

/-- The actual zero-source result with a nonempty exceptional list. -/
private def zeroResult : SourceFrontier.Exceptional.Result zeroModulus :=
  SourceFrontier.Exceptional.build zeroModulus request80

/-- Uniform variation of the exact zero source. -/
private def zeroUniform : Rational.Uniform.Modulus zeroSource where
  radius := fun _ => 1
  radius_pos := fun _ _ => by decide
  variation := fun variation positive _ _ _ _ _ _ => constantVariation 0 variation positive

/-- The empty-exception constructor reuses the original uniform source modulus. -/
private def emptyModulus : Rational.Exceptional.Modulus zeroSource :=
  Rational.Exceptional.ofUniform zeroUniform 0 (by decide) (fun _ _ _ => by
    change -(0 : Fraction.Rational) ≤ 0 ∧ (0 : Fraction.Rational) ≤ 0
    decide)

/-- The exact empty-exception result from the same zero source. -/
private def emptyResult : SourceFrontier.Exceptional.Result emptyModulus :=
  SourceFrontier.Exceptional.build emptyModulus request80

/-- A rational step whose value at the jump differs from both neighboring constant values. -/
private def stepSource (point : Fraction.Rational) : Fraction.Rational :=
  if point = 1 / 2 then 1 / 2 else if point < 1 / 2 then 0 else 1

/-- The step is globally bounded and constant on every rational interval avoiding its retained jump. -/
private def stepModulus : Rational.Exceptional.Modulus stepSource where
  points := [1 / 2]
  magnitude := 1
  magnitude_nonnegative := by decide
  bounded := by
    intro point _ _
    unfold stepSource
    split
    · decide
    · split <;> decide
  radius := fun _ => 1
  radius_pos := fun _ _ => by decide
  variation := by
    intro variation positive first second _ ordered _ noExceptions _
    have noHalf := noExceptions (1 / 2) List.mem_cons_self
    have firstNe : first ≠ 1 / 2 := by
      intro equal
      apply noHalf
      rw [← equal]
      exact ⟨le_rfl, ordered⟩
    have secondNe : second ≠ 1 / 2 := by
      intro equal
      apply noHalf
      rw [← equal]
      exact ⟨ordered, le_rfl⟩
    have same : stepSource first = stepSource second := by
      by_cases firstBefore : first < 1 / 2
      · by_cases secondBefore : second < 1 / 2
        · unfold stepSource
          rw [if_neg firstNe, if_pos firstBefore, if_neg secondNe, if_pos secondBefore]
        · have after := Fraction.Order.Arithmetic.le_of_not_gt_direct secondBefore
          exact (noHalf ⟨firstBefore.le, after⟩).elim
      · by_cases secondBefore : second < 1 / 2
        · have after := Fraction.Order.Arithmetic.le_of_not_gt_direct firstBefore
          exact (secondBefore.2 (Fraction.Order.Basic.le_trans _ _ _ after ordered)).elim
        · unfold stepSource
          rw [if_neg firstNe, if_neg firstBefore, if_neg secondNe, if_neg secondBefore]
    rw [same]
    exact constantVariation (stepSource second) variation positive

/-- The first fixed positive request for the step. -/
private def request32 : AccuracyRequest :=
  ⟨32, Fraction.Cast.Order.natCast_pos_direct (by decide : 0 < 32)⟩

/-- The computed three-cell source frontier for the step. -/
private def stepResult : SourceFrontier.Exceptional.Result stepModulus :=
  SourceFrontier.Exceptional.build stepModulus request32

/-- The second fixed positive request for the step. -/
private def request64 : AccuracyRequest :=
  ⟨64, Fraction.Cast.Order.natCast_pos_direct (by decide : 0 < 64)⟩

/-- An independently requested second frontier of the same finite step rule. -/
private def secondStepResult : SourceFrontier.Exceptional.Result stepModulus :=
  SourceFrontier.Exceptional.build stepModulus request64

/-- The same finite step constructor supplies the original persistent integration process. -/
private def stepProcess : IntegrationProcess (SourcePoint stepSource) :=
  (SourceFrontier.Exceptional.producer stepModulus).integrationProcess

/-- A saved nonempty request history for the actual step source. -/
private def savedStep : stepProcess.State :=
  stepProcess.request stepProcess.initial request32.tolerance request32.positive

/-- The exceptional observer retains the actual saved step-source points. -/
private def stepBank := stepResult.frontier.cells.map (fun cell => cell.item)
private def stepPrepared := SourceFrontier.Exceptional.Preparation.prepare stepModulus request32
private def observedStep := Exceptional.Observation.computation stepModulus stepBank request32
private def stepOracle := SourceFrontier.Observation.originalReply stepSource stepPrepared.partition

example := Exceptional.Observation.computation_original stepModulus stepBank request32

example := Exceptional.Observation.computation_replay stepModulus stepBank request32

/-- All original step-mesh starts are already saved and require no source request. -/
example : (observedStep.protocol.run stepOracle).trace.length = 0 := by decide +kernel

/-- Without a saved bank, the original marked and regular three-cell mesh requests all three starts. -/
example : let program := Exceptional.Observation.computation stepModulus [] request32
    (program.protocol.run stepOracle).trace.length = 3 := by decide +kernel

/-- The actual nonempty step history has a complete public-request observer and replay. -/
example := Exceptional.Observation.historyComputation_original stepModulus savedStep request64

example := Exceptional.Observation.historyComputation_replay stepModulus savedStep request64

/-- The step reads the original rational jump and both neighboring rational pieces. -/
example : stepSource (1 / 4) = 0 ∧ stepSource (1 / 2) = 1 / 2 ∧ stepSource (3 / 4) = 1 := by decide +kernel

/-- The zero-magnitude constructor produces a zero-width enclosure despite repeated endpoint exceptions. -/
example : (integralBound zeroResult.frontier.cells).width = 0 ∧ zeroResult.answer = 0 := by decide +kernel

/-- The empty-exception construction computes an actual finite source frontier and its midpoint. -/
example : emptyResult.frontier.cells.length = 2 ∧ emptyResult.answer = 0 := by decide +kernel

/-- Only the retained cell containing the rational jump is marked on the computed three-cell grid. -/
example : stepResult.frontier.cells.map (fun cell => cell.item.interval.marked stepModulus.points) =
    [false, true, false] := by decide +kernel

/-- The actual finite step-source enclosure meets its original request. -/
example : (integralBound stepResult.frontier.cells).width < 32 := stepResult.accurate

/-- Continuing the saved step-source history uses actual certified frontier splits. -/
example : IntegrationFrontierRefines
    (stepProcess.frontier (stepProcess.request savedStep request64.tolerance request64.positive))
    (stepProcess.frontier savedStep) := stepProcess.request_refines savedStep request64.tolerance request64.positive

/-- Distinct requests for the same step source agree up to their two original enclosure widths. -/
example : Fraction.abs (stepResult.answer - secondStepResult.answer) ≤
    (integralBound stepResult.frontier.cells).width + (integralBound secondStepResult.frontier.cells).width :=
  (SourceFrontier.commonReadings stepResult.frontier secondStepResult.frontier).answers_difference_le_of_same
    _ _ stepResult.answer_contains secondStepResult.answer_contains (fun _ _ _ => rfl)

end TestPurelib.Integration.Cell.Source.Exceptional
