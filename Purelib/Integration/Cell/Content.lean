module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Integration.Cell.Basic

import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Integral
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Exact integration against finite contents

A finite-content integral is an exact rational weighted sum.  The usual
linearity, monotonicity, indicator, restriction, and pushforward identities
are all finite list calculations.
-/

namespace Purelib.Measure
namespace Content

open Purelib in
open Purelib.Data.Rat in
open Purelib.Integration in
/-- Convert each original content atom into an exact-range integration cell.

Payload order, repeated occurrences and nonnegative weights remain unchanged; the supplied observable supplies both
range endpoints. -/
def integralCells {α : Type} (content : Content α)
    (value : α → Fraction.Rational) : List (Integration.IntegrationCell α) :=
  content.atoms.map fun atom =>
    IntegrationCell.exact atom.item atom.weight (value atom.item)
      atom.nonnegative

open Purelib
open Purelib.Data.Rat
/-- The exact content cells' lower integral equals the original content integral. -/
theorem lowerIntegral_integralCells {α : Type}
    (content : Content α) (value : α → Fraction.Rational) :
    Integration.lowerIntegral (content.integralCells value) = content.integral value := by
  unfold integralCells integral
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, Integration.lowerIntegral,
        Distribution.expectationWeight]
      rw [inductionHypothesis]
      rfl

/-- The exact content cells' upper integral equals the original content integral. -/
theorem upperIntegral_integralCells {α : Type}
    (content : Content α) (value : α → Fraction.Rational) :
    Integration.upperIntegral (content.integralCells value) = content.integral value := by
  unfold integralCells integral
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, Integration.upperIntegral,
        Distribution.expectationWeight]
      rw [inductionHypothesis]
      rfl

/-- Exact content cells enclose the original integral in its singleton rational interval. -/
theorem integralBound_integralCells {α : Type}
    (content : Content α) (value : α → Fraction.Rational) :
    Integration.integralBound (content.integralCells value) =
      Interval.exact (content.integral value) := by
  apply Interval.ext
  · exact content.lowerIntegral_integralCells value
  · exact content.upperIntegral_integralCells value

end Content

end Purelib.Measure

end
