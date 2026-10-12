module
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveMagnitude
public import Purelib.Riemann.Integration.RectangularSharedPrimitives

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
import Purelib.Riemann.Periods.RectangularSharedBilinearError
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.RectangularSeamBounds

open Purelib.Riemann.Normalization.InverseRootPolynomial

@[expose] public section

/-! A fixed centered magnitude for a trace contained in one retained model
box, even when its shared vertices select different containing owners. -/
namespace Purelib.Riemann.Paths.RectangularTraceMagnitude

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows : Nat} {target :
      Purelib.Data.Rat.Fraction.Rational}
    {geometry : Geometry columns rows} {bank : Bank polynomial geometry}

open Purelib.Data in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.LinearAlgebra in
open Purelib.Riemann.Branches.RectangularSheetGauge in
open Purelib.Riemann.Integration.RectangularPrimitiveModels in
open Purelib.Riemann.Integration.RectangularSharedPrimitives in
open Purelib.Topology in
/-- Bound a shared primitive increment whose endpoints lie in one retained model box.

Ambient containment and a global ownership error at most one give the fixed bound of 32 plus twice the boundary slope,
even when the shared vertices select different owners. -/
theorem shared_centered_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Transitions.oriented transitions gauge) numerator} {anchors : PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles} (readings : SharedPrimitiveValues anchors offsets surface)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (small : request.globalBound ≤ 1)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (first last : Fin surface.mesh.vertices.length)
    (firstInside : (geometry.box column row).Contains (surface.mesh.coordinate first))
    (lastInside : (geometry.box column row).Contains (surface.mesh.coordinate last)) :
    normSq (readings.values last - readings.values first) ≤ 32 + 2 * boundarySlope bounds := by
  let original := primitives.value column row (surface.mesh.coordinate last) -
    primitives.value column row (surface.mesh.coordinate first)
  have ownership := GridPrimitiveAccuracy.shared_local_increment_bound
    request readings refines column row first last firstInside lastInside
  have localBound := Primitives.local_increment_bound
    primitives bounds refines column row firstInside lastInside
  rw [← Basic.normSq_eq_canonical] at ownership localBound
  have capped := Arithmetic.mul_le_mul_of_nonneg_left_direct small
    (show (0 : Rat.Fraction.Rational) ≤ 16 by decide +kernel)
  have estimate := (Bounds.normSq_add_le_two ((readings.values last - readings.values first) - original) original).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (ownership.trans capped) localBound) (by decide))
  rw [show ((readings.values last - readings.values first) - original) + original =
    readings.values last - readings.values first by ring1] at estimate
  rw [Basic.normSq_eq_canonical] at estimate
  exact estimate.trans_eq (by ring1)

end Purelib.Riemann.Paths.RectangularTraceMagnitude
