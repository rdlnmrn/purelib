module
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Content
public import Purelib.Integration.Box.Cell
import Purelib.Integration.Box.Refinement
import Purelib.Integration.Cell.Basic
import Purelib.Measure.Box.Coupling
public import Purelib.Measure.Box.Distribution

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Enclosure.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Adapters.Measure.RootIsolation.Box.WorkedExamples

open Purelib.Measure
open Purelib.Geometry.Rational
open Purelib.Examples
open Purelib
open Purelib.Data.Rat
open Purelib.Integration

/-! ## Exact rational box content -/

/-- The rational rectangle with corners (0,0) and (2,3). -/
def rectangle : Box where
  xLower := 0
  xUpper := 2
  yLower := 0
  yUpper := 3
  x_valid := by decide
  y_valid := by decide

/-- The displayed rectangle has rational content six. -/
example : Box.Content.boxContent rectangle = 6 := by
  decide

/-- Equal-weight distribution on the rectangle's two vertical halves.

Splits the original box at real coordinate one, retaining both certified child boxes. -/
def rectangleVerticalLaw :
  Measure.Distribution Box :=
  Box.Distribution.verticalSplitDistribution rectangle 1
    (by decide) (by decide)

/-- The vertical split law retains exactly two child atoms. -/
example : rectangleVerticalLaw.atoms.length = 2 := by
  decide

/-- The expected child content is three. -/
example : rectangleVerticalLaw.expectation
    Box.Content.boxContent = 3 := by
  decide

/-- The fixed interval [2,4] used to enclose either child box's content. -/
def coarseRectangleChildContentRange (_ :
  Box) : Interval :=
  ⟨2, 4, by decide⟩

/-- The exact rational interval at the supplied box's content. -/
def exactRectangleChildContentRange (box :
  Box) : Interval :=
  Interval.exact (Box.Content.boxContent box)

/-- The constant coarse content interval has enclosed expectation [2,4]. -/
example : rectangleVerticalLaw.enclosedExpectation
      coarseRectangleChildContentRange =
    ⟨2, 4, by decide⟩ := by
  apply Interval.ext <;> decide

/-- The coarse enclosed expectation contains the exact expected content. -/
example : (rectangleVerticalLaw.enclosedExpectation
      coarseRectangleChildContentRange).Contains
    (rectangleVerticalLaw.expectation Box.Content.boxContent) := by
  decide

/-- Exact child-content intervals refine the coarse enclosed expectation.

Uses the distribution's exact-interval expectation identity and the concrete rational endpoints. -/
example : Interval.Refines
    (rectangleVerticalLaw.enclosedExpectation
      exactRectangleChildContentRange)
    (rectangleVerticalLaw.enclosedExpectation
      coarseRectangleChildContentRange) := by
  unfold exactRectangleChildContentRange
  rw [rectangleVerticalLaw.enclosedExpectation_exact]
  exact ⟨by decide, by decide⟩

/-- The left-half predicate has probability one half under the split law. -/
example : rectangleVerticalLaw.probability
    (fun child => decide (child.xUpper ≤ 1)) = 1 / 2 := by
  decide

/-- The retained parent-law coupling has exactly two joint atoms. -/
example : (Box.Coupling.verticalSplitParentLawCoupling
    rectangle 1 (by decide) (by decide)).coupling.joint.atoms.length =
      2 := by
  decide

/-- The two vertical child contents add to the original rectangle's content. -/
example :
    Box.Content.boxContent
        (rectangle.verticalLeft 1 (by decide)) +
      Box.Content.boxContent
        (rectangle.verticalRight 1 (by decide)) =
      Box.Content.boxContent rectangle :=
  Box.Content.vertical_content_add rectangle 1 (by decide)

/-- The rectangle equipped with the certified value range [1,3]. -/
def rectangleRangeCell :
  Box.Cell.BoxIntegrationCell where
  box := rectangle
  lower := 1
  upper := 3
  range_valid := by decide

/-- The same-range vertical split refines the original integral bound.

Keeps the original certified cell range and compares its actual two children with the original single-cell enclosure. -/
example : Interval.Refines
    (Integration.integralBound (Box.Cell.boxIntegrationCells
      (Box.Refinement.verticalSameRangeSplit
        rectangleRangeCell 1 (by decide)).children))
    (Integration.integralBound [rectangleRangeCell.toIntegrationCell])
      :=
  Box.Refinement.verticalSameRange_integralBound_refines
    rectangleRangeCell 1 (by decide)

end Purelib.Examples.Adapters.Measure.RootIsolation.Box.WorkedExamples

end
