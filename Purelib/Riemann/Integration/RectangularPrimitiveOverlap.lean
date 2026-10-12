module
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Branches.RectangularSheetGauge

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
import Purelib.Geometry.Rectangle.Partition.RectangularOverlapGeometry
public import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Arbitrary vertex comparisons on a fixed primitive grid

A fine-mesh vertex may be owned by any coarse cell containing it.  Any two
such cells are joined through at most two shared edges containing that very
point.  Their squared difference is at most four times the computed grid
allowance, independently of the later mesh size.  A zero allowance remains
zero rather than being replaced by the strictly positive request target.
-/

section

open Purelib.Riemann.Normalization.RectangularInverseModels (Axis Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Data.Gaussian.Basic.Canonical

namespace Purelib.Riemann.Integration.RectangularPrimitiveOverlap

open Purelib.Data.Gaussian in
/-- Reversing a Gaussian difference preserves its squared norm. -/
private theorem normSq_sub_swap (first second : Gaussian) : normSq (first - second) = normSq (second - first) := by
  rw [show first - second = -(second - first) by ring1, Basic.Canonical.normSq_neg]

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rectangle.Partition in
/-- Adjacent shared-boundary estimates control any two original axis cells containing the same coordinate.

Strictly ordered coordinates force the two owners to coincide or be neighbors, preserving their exact finite indices. -/
private theorem axis_compare {steps : Nat} (axis : Axis steps) (point : Coordinate)
    (values : Fin (steps + 1) → Gaussian) {target : Coordinate} (nonnegative : 0 ≤ target)
    (adjacent : ∀ edge : Fin steps, point = axis.coordinates edge.castSucc.succ →
      normSq (values edge.castSucc - values edge.succ) ≤ target)
    (first last : Fin (steps + 1))
    (firstInside : axis.coordinates first.castSucc ≤ point ∧ point ≤ axis.coordinates first.succ)
    (lastInside : axis.coordinates last.castSucc ≤ point ∧ point ≤ axis.coordinates last.succ) :
    normSq (values first - values last) ≤ target := by
  rcases Nat.lt_trichotomy first.val last.val with before | equal | after
  · rcases RectangularOverlapGeometry.Axis.shared_boundary axis first last firstInside lastInside before with ⟨edge,
      firstEq, lastEq, pointEq⟩
    rw [firstEq, lastEq]
    exact adjacent edge pointEq
  · have same := Fin.ext equal
    rw [same, Basic.sub_self, Basic.Canonical.normSq_zero]
    exact nonnegative
  · rcases RectangularOverlapGeometry.Axis.shared_boundary axis last first lastInside firstInside after with ⟨edge,
      lastEq, firstEq, pointEq⟩
    rw [firstEq, lastEq, normSq_sub_swap]
    exact adjacent edge pointEq

end Purelib.Riemann.Integration.RectangularPrimitiveOverlap

section

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows : Nat} {target : Coordinate}
    {geometry : Geometry columns rows} {bank : Bank polynomial geometry}

section
open Purelib
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Branches

namespace Purelib.Riemann.Integration.RectangularPrimitiveOverlap.GridPrimitiveAccuracy

/-- Two original cell readings in one row at a shared point differ by at most the retained global bound. -/
theorem same_row_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} (anchors :
      PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (first last : Fin (columns + 1)) (row : Fin (rows + 1)) {point : Gaussian}
    (firstInside : (geometry.box first row).Contains point) (lastInside : (geometry.box last row).Contains point) :
    normSq (anchors.alignedValue offsets first row point - anchors.alignedValue offsets last row point) ≤
      request.globalBound := by
  apply RectangularPrimitiveOverlap.axis_compare geometry.x point.re
    (fun column => anchors.alignedValue offsets column row point)
    (request.edgeBound_nonnegative.trans request.edgeBound_le_globalBound)
    ?_ first last ⟨firstInside.1, firstInside.2.1⟩ ⟨lastInside.1, lastInside.2.1⟩
  intro edge pointEq
  rcases RectangularOverlapGeometry.horizontal_parameter geometry edge row pointEq firstInside.2.2 with
    ⟨parameter, inside, equal⟩
  have estimate := GridPrimitiveAccuracy.horizontal_bound request anchors offsets refines edge row inside
  dsimp only at estimate
  rw [equal] at estimate
  exact estimate

/-- Two original cell readings in one column at a shared point differ by at most the retained global bound. -/
theorem same_column_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} (anchors :
      PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin (columns + 1)) (first last : Fin (rows + 1)) {point : Gaussian}
    (firstInside : (geometry.box column first).Contains point) (lastInside : (geometry.box column last).Contains point)
      :
    normSq (anchors.alignedValue offsets column first point - anchors.alignedValue offsets column last point) ≤
      request.globalBound := by
  apply RectangularPrimitiveOverlap.axis_compare geometry.y point.im
    (fun row => anchors.alignedValue offsets column row point)
    (request.edgeBound_nonnegative.trans request.edgeBound_le_globalBound)
    ?_ first last firstInside.2.2 lastInside.2.2
  intro edge pointEq
  rcases RectangularOverlapGeometry.vertical_parameter geometry column edge ⟨firstInside.1, firstInside.2.1⟩
    pointEq with ⟨parameter, inside, equal⟩
  have estimate := GridPrimitiveAccuracy.vertical_bound request anchors offsets refines column edge inside
  dsimp only at estimate
  rw [equal] at estimate
  exact estimate

end Purelib.Riemann.Integration.RectangularPrimitiveOverlap.GridPrimitiveAccuracy

end

namespace Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- Any two original cell readings at a shared point differ by at most four times the retained global bound.

A retained intermediate cell uses the target column and source row, so the two original adjacent-axis estimates compare
readings of the same point. -/
theorem overlap_bound (request :
  GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} (anchors :
      PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (firstColumn lastColumn : Fin (columns + 1)) (firstRow lastRow : Fin (rows + 1)) {point : Gaussian}
    (firstInside : (geometry.box firstColumn firstRow).Contains point)
    (lastInside : (geometry.box lastColumn lastRow).Contains point) :
    normSq (anchors.alignedValue offsets firstColumn firstRow point - anchors.alignedValue offsets lastColumn lastRow
      point) ≤ 4 * request.globalBound := by
  have middleInside : (geometry.box lastColumn firstRow).Contains point :=
    ⟨lastInside.1, lastInside.2.1, firstInside.2.2⟩
  have horizontal := RectangularPrimitiveOverlap.GridPrimitiveAccuracy.same_row_bound request anchors offsets refines
    firstColumn lastColumn firstRow firstInside middleInside
  have vertical := RectangularPrimitiveOverlap.GridPrimitiveAccuracy.same_column_bound request anchors offsets refines
    lastColumn firstRow lastRow middleInside lastInside
  have pathBound := Norm.Bounds.normSq_sub_le_via
    (anchors.alignedValue offsets firstColumn firstRow point)
    (anchors.alignedValue offsets lastColumn firstRow point)
    (anchors.alignedValue offsets lastColumn lastRow point)
  simp only [Norm.Basic.normSq_eq_canonical] at pathBound
  have sumBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add horizontal vertical)
    (by decide : (0 : Fraction.Rational) ≤ 2)
  exact pathBound.trans (sumBound.trans_eq (by ring1))

end Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy

end

end
