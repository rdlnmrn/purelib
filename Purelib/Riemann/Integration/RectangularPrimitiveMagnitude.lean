module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds

public import Purelib.Riemann.Readings.RectangularSeamBounds

open Purelib.Riemann.Normalization.InverseRootPolynomial

@[expose] public section

/-! Fixed ambient increment bounds for any retained ready primitive bank.
No accuracy-request index is needed for this magnitude estimate. -/
section

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives ambient_numerator_inverse_le)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

namespace Purelib.Riemann.Integration.RectangularPrimitiveMagnitude

open Purelib.Data in
/-- The exact rational coordinate type. -/
private abbrev Coordinate := Rat.Fraction.Rational

end Purelib.Riemann.Integration.RectangularPrimitiveMagnitude

section
variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {columns rows : Nat}
    {geometry : Geometry columns rows} {models : Bank polynomial geometry}

namespace Purelib.Riemann.Integration.RectangularPrimitiveModels.Primitives

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Bound a retained primitive increment by the fixed ambient slope budget.

Both endpoints lie in the same model cell, and all cells refine the clear ambient region; the estimate requires no new
accuracy-request index. -/
theorem local_increment_bound (primitives :
  Primitives models numerator)
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) {first last : Gaussian}
    (firstInside : (geometry.box column row).Contains first)
    (lastInside : (geometry.box column row).Contains last) :
    Gaussian.Basic.Canonical.normSq (primitives.value column row last - primitives.value column row first) ≤
      boundarySlope bounds := by
  have inside := fun parameter (within : 0 ≤ parameter ∧ parameter ≤ 1) =>
    Rational.Box.contains_line firstInside lastInside within
  have coefficientBound (parameter : RectangularPrimitiveMagnitude.Coordinate)
      (within : 0 ≤ parameter ∧ parameter ≤ 1) :
      Gaussian.Basic.Canonical.normSq ((primitives.cells column row).coefficient.eval
        (Rational.Affine.line first (last - first) parameter)) ≤ bounds.numeratorUpper * bounds.inverseUpper := by
    rw [primitives.coefficient_eq]
    exact ambient_numerator_inverse_le bounds (models.ready column row).model
      (refines column row) (inside parameter within)
  have estimate := Dense.Gaussian.Primitive.Segment.Bounds.DensePrimitive.segment_increment_le (primitives.dense column
    row) first (last - first)
    (⟨0, 1, by decide⟩ : Data.Rat.Interval.Bounds) inside
    (bounds.numeratorUpper * bounds.inverseUpper) (fun parameter within => by
      have scalar := coefficientBound parameter within
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, Integration.RectangularPrimitiveModels.Primitives.dense,
        Integration.RectangularPrimitiveModels.Primitives.value,
    Readings.RectangularSeamBounds.boundarySlope] using scalar)
    (show (0 : RectangularPrimitiveMagnitude.Coordinate) ≤ 1 ∧ 1 ≤ 1 from ⟨by decide, le_rfl⟩)
    (show (0 : RectangularPrimitiveMagnitude.Coordinate) ≤ 0 ∧ 0 ≤ 1 from ⟨le_rfl, by decide⟩)
  rw [Normalization.InverseModelEdgeTransition.line_one, Normalization.InverseModelEdgeTransition.line_zero] at estimate
  have endpointDifference : (1 : RectangularPrimitiveMagnitude.Coordinate) - 0 = 1 := by decide
  simp only [endpointDifference, one_pow, Rat.Fraction.Field.mul_one_direct] at estimate
  have lengthBound := Rational.Box.normSq_sub_le_diagonalSq
    ((refines column row).contains lastInside) ((refines column row).contains firstInside)
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, Integration.RectangularPrimitiveModels.Primitives.dense,
    Integration.RectangularPrimitiveModels.Primitives.value,
    Readings.RectangularSeamBounds.boundarySlope] using
    estimate.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lengthBound
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative
        bounds.inverseUpper_positive.le)))

end Purelib.Riemann.Integration.RectangularPrimitiveModels.Primitives

end
end
