module
public import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Integration.Cell.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite rational probability

A probability distribution is a displayed finite weighted list whose total is
exactly one.  Events are executable Boolean tests, so their probabilities and
expectations are exact rational calculations.
-/

namespace Purelib.Measure
namespace Distribution

/-! ## Expectation as an exact finite integral -/

section
open Purelib
open Purelib.Data.Rat
open Purelib.Integration in
/-- Convert every original distribution atom into an exact-range integration cell for the supplied observable.

The original payload occurrences, weights and nonnegativity certificates remain unchanged. -/
def expectationCells {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) : List (Integration.IntegrationCell α) :=
  distribution.atoms.map fun atom =>
    IntegrationCell.exact atom.item atom.weight (value atom.item)
      atom.nonnegative

/-- The expectation cells' lower integral is the original observable expectation. -/
theorem lowerIntegral_expectationCells {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    Integration.lowerIntegral (distribution.expectationCells value) =
      distribution.expectation value := by
  unfold expectationCells expectation
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, Integration.lowerIntegral, expectationWeight]
      rw [inductionHypothesis]
      rfl

/-- The expectation cells' upper integral is the original observable expectation. -/
theorem upperIntegral_expectationCells {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    Integration.upperIntegral (distribution.expectationCells value) =
      distribution.expectation value := by
  unfold expectationCells expectation
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, Integration.upperIntegral, expectationWeight]
      rw [inductionHypothesis]
      rfl

/-- Exact expectation cells produce the singleton interval at the original expectation. -/
theorem integralBound_expectationCells {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    Integration.integralBound (distribution.expectationCells value) =
      Interval.exact (distribution.expectation value) := by
  apply Interval.ext
  · exact distribution.lowerIntegral_expectationCells value
  · exact distribution.upperIntegral_expectationCells value

/-- The exact expectation-cell enclosure has zero width. -/
theorem integralBound_expectationCells_width {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    (Integration.integralBound (distribution.expectationCells value)).width = 0 := by
  rw [distribution.integralBound_expectationCells, Interval.exact_width]
end

end Distribution

end Purelib.Measure

end
