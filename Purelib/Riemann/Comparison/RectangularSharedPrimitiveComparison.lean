module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Integration.RectangularSharedPrimitives

open Purelib.Riemann.Normalization.InverseRootPolynomial

@[expose] public section

/-!
# Comparing different meshes using the same numerical primitive bank

Different meshes may assign a shared coordinate to different containing
cells. Sharing the polynomials and offsets does not erase that discrepancy;
the same finite overlap budget bounds it without a Taylor or mesh-size term.
-/

namespace Purelib.Riemann.Comparison.RectangularSharedPrimitiveComparison

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
  {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows : Nat} {target : Coordinate}
  {geometry : Geometry columns rows} {bank : Bank polynomial geometry}

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound the discrepancy between equal coordinates in two meshes using one primitive bank.

Both retained triangulations refine the same ambient region and use the same primitive anchors and offsets. Their values
differ by squared norm at most four times the request's global overlap bound. -/
theorem shared_cross_mesh_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors
      : PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {firstTriangles lastTriangles : List (ModelTriangle geometry)}
    {firstSurface : OwnedTriangulation firstTriangles} {lastSurface : OwnedTriangulation lastTriangles}
    (first : SharedPrimitiveValues anchors offsets firstSurface) (last : SharedPrimitiveValues anchors offsets
      lastSurface)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (firstVertex : Fin firstSurface.mesh.vertices.length) (lastVertex : Fin lastSurface.mesh.vertices.length)
    (coordinateEq : firstSurface.mesh.coordinate firstVertex = lastSurface.mesh.coordinate lastVertex) :
    Data.Gaussian.Norm.Basic.normSq (first.values firstVertex - last.values lastVertex) ≤ 4 * request.globalBound :=
      by
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  rw [first.value_eq, last.value_eq, firstSurface.point_eq, lastSurface.point_eq, coordinateEq]
  exact Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.overlap_bound request anchors offsets refines _ _
    _ _
    (coordinateEq ▸ firstSurface.owner_inside firstVertex) (lastSurface.owner_inside lastVertex)

end Purelib.Riemann.Comparison.RectangularSharedPrimitiveComparison
