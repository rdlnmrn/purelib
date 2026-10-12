module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Readings.RectangularPointReadings

@[expose] public section

/-! Compare a cached point owner with any containing cell of the same bank. -/
namespace Purelib.Riemann.Readings.RectangularPointOwnerBounds
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
  {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows count : Nat} {target : Coordinate}
  {geometry : Geometry columns rows} {bank : Bank polynomial geometry}

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Compare a cached point reading with any containing cell of its oriented model bank.

When all cells refine the same clear ambient region, the squared difference is at most four times the primitive
request's global bound. -/
theorem point_cell_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors
      : PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {points : Fin count → Gaussian}
    (readings : PointReadings anchors offsets points)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (vertex : Fin count) (column : Fin (columns + 1)) (row : Fin (rows + 1))
    (inside : (geometry.box column row).Contains (points vertex)) :
    Data.Gaussian.Norm.Basic.normSq (readings.values vertex - anchors.alignedValue offsets column row (points
      vertex)) ≤ 4 * request.globalBound := by
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  have owned : (geometry.box (readings.owners vertex).column (readings.owners vertex).row).Contains (points vertex) :=
    readings.point_eq vertex ▸ (readings.owners vertex).contains
  rw [readings.value_eq, readings.point_eq]
  exact Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.overlap_bound request anchors offsets refines _ _
    _ _ owned inside

end Purelib.Riemann.Readings.RectangularPointOwnerBounds
