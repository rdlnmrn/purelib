module
import Purelib.Integration.Cell.Numerical.Continuous
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! Finite numerical point requests and integration with reading uncertainty. -/

namespace TestPurelib.Integration.Cell.Numerical

open Purelib.Approximation
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration
open Purelib.Integration.Partition

/-- A coarse interval enclosing the original rational point. -/
private def wide (point : Fraction.Rational) : Rat.Interval :=
  ⟨point - 1, point + 1, by
    have signed := Arithmetic.add_le_add_right_direct
      (by decide : (-1 : Fraction.Rational) ≤ 1) point
    have first : -1 + point = point - 1 := by ring1
    have second : 1 + point = point + 1 := by ring1
    rw [first, second] at signed
    exact signed⟩

/-- The original rational point lies in its coarse interval. -/
private theorem wide_contains (point : Fraction.Rational) : (wide point).Contains point := by
  have lower := Arithmetic.add_le_add_right_direct
    (by decide : (-1 : Fraction.Rational) ≤ 0) point
  have upper := Arithmetic.add_le_add_right_direct
    (by decide : (0 : Fraction.Rational) ≤ 1) point
  have first : -1 + point = point - 1 := by ring1
  have second : 1 + point = point + 1 := by ring1
  rw [first, Fraction.Field.zero_add] at lower
  rw [Fraction.Field.zero_add, second] at upper
  exact ⟨lower, upper⟩

/-- A point process with an initially coarse reading and an exact requested refinement. -/
private def noisy (point : Fraction.Rational) : BoundProcess where
  State := Bool
  bound state := if state then Rat.Interval.exact point else wide point
  initial := false
  request := fun _ _ _ => true
  request_refines := by
    intro state _ _
    cases state with
    | false =>
        change (Rat.Interval.exact point).Refines (wide point)
        exact ⟨(wide_contains point).1, (wide_contains point).2⟩
    | true => exact Rat.Interval.Refines.refl _
  accurate := by
    intro _ _ positive
    change (Rat.Interval.exact point).width < _
    rw [Rat.Interval.exact_width]
    exact positive
  refinesInitial := by
    intro state
    cases state with
    | false => exact Rat.Interval.Refines.refl _
    | true =>
        change (Rat.Interval.exact point).Refines (wide point)
        exact ⟨(wide_contains point).1, (wide_contains point).2⟩

/-- Every original noisy-process state contains its original rational point. -/
private theorem noisy_contains (point : Fraction.Rational) (state : (noisy point).State) :
    ((noisy point).bound state).Contains point := by
  cases state with
  | false => exact wide_contains point
  | true => exact ⟨le_rfl, le_rfl⟩

/-- The original point-process family has the identity source's effective variation. -/
private def noisyModulus : Rational.Uniform.Numerical noisy where
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

/-- A positive request for the original numerical integration. -/
private def request : AccuracyRequest := ⟨4, by decide⟩

/-- The actual finite numerical integration result. -/
private def result : NumericalFrontier.Continuous.Result noisyModulus :=
  NumericalFrontier.Continuous.build noisyModulus request

/-- The first test point has a coarse initial bound and a genuine narrower requested reading. -/
private def observed : NumericalPoint noisy :=
  NumericalPoint.observe noisy ⟨0, 1⟩ (1 / 2) (by decide) (by decide) false ⟨1, by decide⟩

example : ((noisy (1 / 2)).bound observed.previous).width = 2 ∧ observed.reading.width = 0 := by decide +kernel

example : Rat.Interval.Refines (observed.refine request).reading observed.reading :=
  observed.refine_reading request

example : result.frontier.cells.length = 2 := by decide +kernel

example : (integralBound result.frontier.cells).width < request.tolerance := result.accurate

end TestPurelib.Integration.Cell.Numerical
