module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
import Purelib.Riemann.Branches.RectangularSheetGauge

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Paths.RectangularSeamTraceBounds
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap
public import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Tactic.Ring

public section

/-! Corrected ribbons between arbitrary retained owners on a shared segment.
The overlap error shrinks with the numerical request; the fixed drift ceiling
suffices and does not depend on the number of dyadic subdivisions. -/
namespace Purelib.Riemann.Readings.RectangularPairedSeamBounds

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives ambient_numerator_inverse_le)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Paths.RectangularSeamTraceBounds (SeamTraceBounds)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Data.Gaussian.Basic.Canonical

namespace Primitives

variable {polynomial numerator : Polynomial} {ambient : Box}
  {clearance : RegionClearance polynomial ambient} {columns rows : Nat}
  {geometry : Geometry columns rows} {models : Bank polynomial geometry}

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Bound an actual primitive's increment by the fixed boundary slope times parameter distance squared.

Both physical endpoints lie in the retained owner box, whose ambient refinement supplies the coefficient and
segment-length bounds. -/
theorem segment_parameter_increment_bound (primitives : Primitives models numerator)
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) {start finish : Gaussian}
    (startInside : (geometry.box column row).Contains start)
    (finishInside : (geometry.box column row).Contains finish)
    {first last : Coordinate} (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    Gaussian.Basic.Canonical.normSq (primitives.value column row (Rational.Affine.line start (finish - start) last) -
      primitives.value column row (Rational.Affine.line start (finish - start) first)) ≤
      boundarySlope bounds * (last - first) ^ 2 := by
  have inside := fun parameter (within : 0 ≤ parameter ∧ parameter ≤ 1) =>
    Rational.Box.contains_line startInside finishInside within
  have coefficientBound (parameter : Coordinate) (within : 0 ≤ parameter ∧ parameter ≤ 1) :
      Gaussian.Basic.Canonical.normSq ((primitives.cells column row).coefficient.eval
        (Rational.Affine.line start (finish - start) parameter)) ≤ bounds.numeratorUpper * bounds.inverseUpper := by
    rw [primitives.coefficient_eq]
    exact ambient_numerator_inverse_le bounds (models.ready column row).model
      (refines column row) (inside parameter within)
  have estimate := Dense.Gaussian.Primitive.Segment.Bounds.DensePrimitive.segment_increment_le (primitives.dense column
    row) start (finish - start)
    (⟨0, 1, by decide⟩ : Data.Rat.Interval.Bounds) inside
    (bounds.numeratorUpper * bounds.inverseUpper) (fun parameter within => by
      have scalar := coefficientBound parameter within
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar) lastInside firstInside
  have lengthBound := Rational.Box.normSq_sub_le_diagonalSq
    ((refines column row).contains finishInside) ((refines column row).contains startInside)
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, Integration.RectangularPrimitiveModels.Primitives.dense,
    Integration.RectangularPrimitiveModels.Primitives.value,
    Readings.RectangularSeamBounds.boundarySlope] using
    estimate.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lengthBound
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative
          bounds.inverseUpper_positive.le)))
    (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _))

end Primitives

namespace GridPrimitiveAccuracy

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows : Nat} {target : Coordinate}
    {geometry : Geometry columns rows} {bank : Bank polynomial geometry}

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
open Purelib.Geometry in
open Purelib.LinearAlgebra in
/-- Certify a corrected ribbon between arbitrary retained owners on one shared segment.

The overlap error is four times the requested global bound; the original boundary slope controls increments and four
times that slope controls drift, independently of later dyadic depth. -/
theorem paired_segment_trace_bounds (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} (anchors
      : PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (refines : ∀ column row, (geometry.box column row).Refines
      ambient)
    (piece : PairedSegmentPiece geometry geometry) :
    let point := fun parameter => Rational.Affine.line piece.first (piece.last - piece.first) parameter
    SeamTraceBounds (fun parameter => anchors.alignedValue offsets piece.leftColumn piece.leftRow (point parameter))
      (fun parameter => anchors.alignedValue offsets piece.rightColumn piece.rightRow (point parameter))
      (4 * request.globalBound) (boundarySlope bounds) (4 * boundarySlope bounds) := by
  let point := fun parameter => Rational.Affine.line piece.first (piece.last - piece.first) parameter
  have increment (column : Fin (columns + 1)) (row : Fin (rows + 1))
      (startInside : (geometry.box column row).Contains piece.first)
      (finishInside : (geometry.box column row).Contains piece.last)
      (first last : Coordinate) (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
      Gaussian.Basic.Canonical.normSq (anchors.alignedValue offsets column row (point last) -
        anchors.alignedValue offsets column row (point first)) ≤ boundarySlope bounds * (last - first) ^ 2 := by
    dsimp only [PrimitiveAnchors.alignedValue]
    rw [show (offsets.values column row + primitives.value column row (point last)) -
        (offsets.values column row + primitives.value column row (point first)) =
        primitives.value column row (point last) - primitives.value column row (point first) by ring1]
    exact Readings.RectangularPairedSeamBounds.Primitives.segment_parameter_increment_bound primitives bounds refines
      column row startInside finishInside firstInside lastInside
  refine ⟨?_, increment _ _ piece.rightFirst piece.rightLast, ?_⟩
  · intro parameter within
    exact Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.overlap_bound request anchors offsets refines _
      _ _ _
      (Rational.Box.contains_line piece.leftFirst piece.leftLast within)
      (Rational.Box.contains_line piece.rightFirst piece.rightLast within)
  · intro first last firstInside lastInside
    have left := increment _ _ piece.leftFirst piece.leftLast first last firstInside lastInside
    have right := increment _ _ piece.rightFirst piece.rightLast first last firstInside lastInside
    rw [show (anchors.alignedValue offsets piece.leftColumn piece.leftRow (point last) -
        anchors.alignedValue offsets piece.rightColumn piece.rightRow (point last)) -
        (anchors.alignedValue offsets piece.leftColumn piece.leftRow (point first) -
        anchors.alignedValue offsets piece.rightColumn piece.rightRow (point first)) =
        (anchors.alignedValue offsets piece.leftColumn piece.leftRow (point last) -
        anchors.alignedValue offsets piece.leftColumn piece.leftRow (point first)) -
        (anchors.alignedValue offsets piece.rightColumn piece.rightRow (point last) -
        anchors.alignedValue offsets piece.rightColumn piece.rightRow (point first)) by ring1]
    have scalar := Gaussian.Norm.Bounds.normSq_sub_le_two
      (anchors.alignedValue offsets piece.leftColumn piece.leftRow (point last) -
        anchors.alignedValue offsets piece.leftColumn piece.leftRow (point first))
      (anchors.alignedValue offsets piece.rightColumn piece.rightRow (point last) -
        anchors.alignedValue offsets piece.rightColumn piece.rightRow (point first))
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.trans
      ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add left right) (by decide)).trans_eq (by
        ring1))

end GridPrimitiveAccuracy
end Purelib.Riemann.Readings.RectangularPairedSeamBounds
