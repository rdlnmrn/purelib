module
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Cell.Basic
public import Purelib.Measure.Box.Cover

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Integration.Box.Cell
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
public import Purelib.Measure.IntervalIntegration

open Purelib.Measure.Box.Cover (BoxCover)

/-!
# Finite rational box integration

Displayed RFAP boxes supply exact nonnegative cell weights for the generic
finite integration layer.  Vertical and horizontal rational cuts become
certified integration subdivisions by exact finite area conservation.
-/

@[expose] public section

namespace Purelib.Integration.Cover.Cells
namespace BoxIntegrationCell
end BoxIntegrationCell
namespace BoxIntegrationSplit
end BoxIntegrationSplit

/-! ## Bounded upper sums on finite covers -/

open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Measure in
/-- Attach the same retained ordered range to each original box-cover occurrence.

The exact box list and any overlap or repetition remain unchanged; weights are the original individual box contents. -/
def coverRangeCells (cover : BoxCover) (lower upper :
  Fraction.Rational)
    (valid : lower ≤ upper) : List Box.Cell.BoxIntegrationCell :=
  cover.boxes.map fun box => ⟨box, lower, upper, valid⟩

section
open Purelib
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Measure
/-- The cover cells' lower integral is original total cover content times the retained lower value.

Every original box occurrence receives the same lower endpoint. Finite induction separates that common scalar from the
ordered content sum. -/
theorem lowerIntegral_coverRangeCells (cover : BoxCover)
    (lower upper : Fraction.Rational) (valid : lower ≤ upper) :
    Integration.lowerIntegral
        (Box.Cell.boxIntegrationCells (coverRangeCells cover lower upper valid)) =
      cover.content * lower := by
  rcases cover with ⟨boxes⟩
  induction boxes with
  | nil =>
      simp only [coverRangeCells, Box.Cell.boxIntegrationCells,
        Integration.lowerIntegral, BoxCover.content,
        List.map_nil, List.sum_nil, zero_mul, -eq_self, -iff_self]
      rfl
  | cons box remaining inductionHypothesis =>
      simp only [coverRangeCells, Box.Cell.boxIntegrationCells, List.map_cons,
        Integration.lowerIntegral,
        Box.Cell.BoxIntegrationCell.toIntegrationCell, BoxCover.content,
        List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]
      ring1

/-- The cover cells' upper integral is original total cover content times the retained upper value.

Every original box occurrence receives the same upper endpoint. Finite induction separates that common scalar from the
ordered content sum. -/
theorem upperIntegral_coverRangeCells (cover : BoxCover)
    (lower upper : Fraction.Rational) (valid : lower ≤ upper) :
    Integration.upperIntegral
        (Box.Cell.boxIntegrationCells (coverRangeCells cover lower upper valid)) =
      cover.content * upper := by
  rcases cover with ⟨boxes⟩
  induction boxes with
  | nil =>
      simp only [coverRangeCells, Box.Cell.boxIntegrationCells,
        Integration.upperIntegral, BoxCover.content,
        List.map_nil, List.sum_nil, zero_mul, -eq_self, -iff_self]
      rfl
  | cons box remaining inductionHypothesis =>
      simp only [coverRangeCells, Box.Cell.boxIntegrationCells, List.map_cons,
        Integration.upperIntegral,
        Box.Cell.BoxIntegrationCell.toIntegrationCell, BoxCover.content,
        List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]
      ring1

end

namespace EffectiveNull
end EffectiveNull

end Purelib.Integration.Cover.Cells

end
