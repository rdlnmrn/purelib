module
public import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Integration.Cell.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib
/-- Attach the supplied rational range enclosure to each original distribution atom.

The cell conversion retains the original payload occurrence, weight and nonnegativity evidence. -/
def enclosureCells {α : Type} (distribution : Distribution α)
    (ranges : α → Data.Rat.Interval) : List (Integration.IntegrationCell α) :=
  distribution.atoms.map fun atom =>
    { item := atom.item
      weight := atom.weight
      weight_nonnegative := atom.nonnegative
      lower := (ranges atom.item).lower
      upper := (ranges atom.item).upper
      range_valid := (ranges atom.item).valid }

/-- The enclosure cells' lower integral is the original expectation of lower range endpoints.

Each retained atom contributes its original weight times the lower endpoint of its assigned range. -/
theorem lowerIntegral_enclosureCells {α : Type}
    (distribution : Distribution α) (ranges : α → Data.Rat.Interval) :
    Integration.lowerIntegral (distribution.enclosureCells ranges) =
      distribution.expectation (fun item => (ranges item).lower) := by
  unfold enclosureCells expectation
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, Integration.lowerIntegral, expectationWeight,
        inductionHypothesis, -eq_self, -iff_self]
      rfl

/-- The enclosure cells' upper integral is the original expectation of upper range endpoints.

Each retained atom contributes its original weight times the upper endpoint of its assigned range. -/
theorem upperIntegral_enclosureCells {α : Type}
    (distribution : Distribution α) (ranges : α → Data.Rat.Interval) :
    Integration.upperIntegral (distribution.enclosureCells ranges) =
      distribution.expectation (fun item => (ranges item).upper) := by
  unfold enclosureCells expectation
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, Integration.upperIntegral, expectationWeight,
        inductionHypothesis, -eq_self, -iff_self]
      rfl

end

open Purelib in
open Purelib.Data.Rat in
open Purelib.Integration in
/-- The enclosure cells' weighted oscillation is the original expectation of range widths.

Each retained atom contributes its original weight times the difference of its assigned range endpoints. -/
theorem integralOscillation_enclosureCells {α : Type}
    (distribution : Distribution α) (ranges : α → Data.Rat.Interval) :
    Integration.integralOscillation (distribution.enclosureCells ranges) =
      distribution.expectation (fun item => (ranges item).width) := by
  unfold enclosureCells expectation
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, Integration.integralOscillation, expectationWeight,
        IntegrationCell.oscillation, Interval.width, inductionHypothesis, -eq_self, -iff_self]
      rfl
end Distribution

end Purelib.Measure

end
