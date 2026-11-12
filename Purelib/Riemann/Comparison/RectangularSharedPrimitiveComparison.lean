module
public import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
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

variable {pairs : Nat}

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
theorem shared_cross_mesh_bound (request : GridPrimitiveAccuracy bounds columns target pairs)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs}
    {anchors : PrimitiveAnchors primitives}
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

namespace Purelib.Riemann.Meshes.RectangularFaceModels.RectangularPatch

open Purelib.Riemann.Integration

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Order
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann.Normalization.RegularFaceInverseModels (Clearance Bounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Transitions)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds PrimitiveEdgeAccuracy)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.TracedPrimitiveNeighborhood (Neighborhood)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {box prefixAmbient : Box} {clearance : Clearance curve.polynomial box} {modelBounds : Bounds clearance}
    {start : Gaussian} {source : Owner (curve.polynomial.eval start)}
    {prefixPath : ClearPath curve.polynomial prefixAmbient start box.anchor} {entered : TracedPath prefixPath source}
    {columns rows : Nat} {geometry : Geometry columns rows}
    (patch : RectangularPatch modelBounds entered.finishOwner geometry)
    {numerator : Polynomial} {index pairs : Nat}
    {primitives : Primitives (Transitions.oriented (patch.sheets.refine index).transitions
      (patch.sheets.refine index).gauge) numerator pairs}

/-- The retained primitive coefficient uses the same source-calibrated transported model at its original odd power.

The actual prefix, ending Owner and winding reference derive the model
readback. The complete primitive cache and its additive constant remain
unchanged.
-/
theorem primitive_coefficient_eq (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    (primitives : Primitives (Transitions.oriented (patch.sheets.refine index).transitions
      (patch.sheets.refine index).gauge) numerator pairs)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (point : Gaussian) :
    (primitives.cells column row).coefficient.eval point = match (generalizing := false) pairs with
      | 0 => numerator.eval point * ((patch.transported.cell column row).model.refine (index + 2)).value.eval point
      | remaining + 1 => numerator.eval point *
          ((patch.transported.cell column row).model.refine (index + 2)).value.eval point ^
            (2 * (remaining + 1) + 1) := by
  rewrite [primitives.coefficient_eq, patch.oriented_value prefixInside differential degreePositive reference]
  cases pairs with
  | zero => rfl
  | succ remaining => rfl

/-- Compare the retained rectangular primitive and actual source-trace primitive at their independent original indices.

Both endpoints lie in their displayed original domains. The actual prefix
and winding reference derive the transition sign, while the same odd-power
weight pays the primitive discrepancy.
-/
theorem primitive_trace_increment_le (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    (primitives : Primitives (Transitions.oriented (patch.sheets.refine index).transitions
      (patch.sheets.refine index).gauge) numerator pairs)
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    {ambient : Box} {point : Gaussian} {path : ClearPath curve.polynomial ambient start point}
    (traced : TracedPath path source) (inside : InBox box path)
    (frame : OwnerFrame (curve.polynomial.eval point)) (pointInside : (geometry.box column row).Contains point)
    {count : Nat} (neighborhood : Neighborhood traced count) (rightIndex : Nat)
    (second : PrimitiveModel neighborhood.patch (rightIndex + 2) numerator pairs)
    (bounds : PrimitiveOverlapBounds (clearance.restrict (patch.cell_refines column row)) numerator)
    (finish : Gaussian) (leftFinish : (geometry.box column row).Contains finish)
    (rightFinish : neighborhood.patch.box.Contains finish) :
    normSq ((primitives.value column row finish - primitives.value column row point) -
      (second.primitive.value.eval finish - second.primitive.value.eval point)) ≤
      12 * (((patch.transported.cell column row).model.refine (index + 2)).bound +
        (neighborhood.patch.base.refine (rightIndex + 2)).bound) * bounds.weight pairs * normSq (finish - point) := by
  exact (patch.transported.cell column row).trace_primitive_increment_le
    (numerator := numerator) (pairs := pairs) prefixInside differential degreePositive reference
    traced inside frame pointInside neighborhood index rightIndex (primitives.dense column row)
    (patch.primitive_coefficient_eq prefixInside differential degreePositive reference primitives column row)
    second bounds finish leftFinish rightFinish

/-- One original request pays both actual primitive caches at independently retained later indices.

The original request and its two floor certificates are consumed directly;
neither the primitive bank nor the source neighborhood is reacquired.
-/
theorem primitive_trace_increment_lt (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    (primitives : Primitives (Transitions.oriented (patch.sheets.refine index).transitions
      (patch.sheets.refine index).gauge) numerator pairs)
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    {ambient : Box} {point : Gaussian} {path : ClearPath curve.polynomial ambient start point}
    (traced : TracedPath path source) (inside : InBox box path)
    (frame : OwnerFrame (curve.polynomial.eval point)) (pointInside : (geometry.box column row).Contains point)
    {count : Nat} (neighborhood : Neighborhood traced count) {rightIndex : Nat}
    (second : PrimitiveModel neighborhood.patch (rightIndex + 2) numerator pairs)
    {bounds : PrimitiveOverlapBounds (clearance.restrict (patch.cell_refines column row)) numerator}
    {finish : Gaussian} {target : Coordinate}
    (request : PrimitiveEdgeAccuracy bounds (patch.transported.cell column row).model
      neighborhood.patch.base.model point finish target pairs)
    (leftLater : request.index ≤ index) (rightLater : request.index ≤ rightIndex)
    (leftFinish : (geometry.box column row).Contains finish) (rightFinish : neighborhood.patch.box.Contains finish) :
    normSq ((primitives.value column row finish - primitives.value column row point) -
      (second.primitive.value.eval finish - second.primitive.value.eval point)) < target := by
  exact (patch.transported.cell column row).trace_primitive_increment_lt
    (numerator := numerator) (pairs := pairs) prefixInside differential degreePositive reference
    traced inside frame pointInside neighborhood request index rightIndex leftLater rightLater
    (primitives.dense column row)
    (patch.primitive_coefficient_eq prefixInside differential degreePositive reference primitives column row)
    second leftFinish rightFinish

/-- The actual spanning-tree offset cancels from the same retained local primitive increment.

Both endpoint evaluations use the original anchor and offset caches; the
remaining difference is paid by the original primitive request.
-/
theorem aligned_trace_increment_lt (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    (anchors : PrimitiveAnchors primitives) (offsets : Offsets anchors.edges)
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    {ambient : Box} {point : Gaussian} {path : ClearPath curve.polynomial ambient start point}
    (traced : TracedPath path source) (inside : InBox box path)
    (frame : OwnerFrame (curve.polynomial.eval point)) (pointInside : (geometry.box column row).Contains point)
    {count : Nat} (neighborhood : Neighborhood traced count) {rightIndex : Nat}
    (second : PrimitiveModel neighborhood.patch (rightIndex + 2) numerator pairs)
    {bounds : PrimitiveOverlapBounds (clearance.restrict (patch.cell_refines column row)) numerator}
    {finish : Gaussian} {target : Coordinate}
    (request : PrimitiveEdgeAccuracy bounds (patch.transported.cell column row).model
      neighborhood.patch.base.model point finish target pairs)
    (leftLater : request.index ≤ index) (rightLater : request.index ≤ rightIndex)
    (leftFinish : (geometry.box column row).Contains finish) (rightFinish : neighborhood.patch.box.Contains finish) :
    normSq ((anchors.alignedValue offsets column row finish - anchors.alignedValue offsets column row point) -
      (second.primitive.value.eval finish - second.primitive.value.eval point)) < target := by
  have increments : anchors.alignedValue offsets column row finish - anchors.alignedValue offsets column row point =
      primitives.value column row finish - primitives.value column row point := by
    simp only [PrimitiveAnchors.alignedValue]
    ring1
  rewrite [increments]
  exact patch.primitive_trace_increment_lt prefixInside differential degreePositive reference
    primitives column row traced inside frame pointInside neighborhood
    second request leftLater rightLater leftFinish rightFinish

/-- Shared mesh values pay both endpoint ownership changes and the same retained local primitive discrepancy.

The global overlap charge remains explicit. The original source prefix,
point neighborhood, grid request and two later-floor certificates retain
their actual owners and odd-power coefficient units.
-/
theorem shared_trace_increment_lt (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    {globalBounds : PrimitiveOverlapBounds clearance numerator} {tolerance : Coordinate}
    (gridRequest : GridPrimitiveAccuracy globalBounds columns tolerance pairs)
    {primitives : Primitives (Transitions.oriented
      (patch.sheets.refine gridRequest.index).transitions (patch.sheets.refine gridRequest.index).gauge)
      numerator pairs}
    {anchors : PrimitiveAnchors primitives} {offsets : Offsets anchors.edges}
    {triangles : List (ModelTriangle geometry)} {surface : OwnedTriangulation triangles}
    (readings : SharedPrimitiveValues anchors offsets surface)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (first last : Fin surface.mesh.vertices.length)
    (firstInside : (geometry.box column row).Contains (surface.mesh.coordinate first))
    (lastInside : (geometry.box column row).Contains (surface.mesh.coordinate last))
    {ambient : Box} {path : ClearPath curve.polynomial ambient start (surface.mesh.coordinate first)}
    (traced : TracedPath path source) (inside : InBox box path)
    (frame : OwnerFrame (curve.polynomial.eval (surface.mesh.coordinate first)))
    {count : Nat} (neighborhood : Neighborhood traced count) {rightIndex : Nat}
    (second : PrimitiveModel neighborhood.patch (rightIndex + 2) numerator pairs)
    {bounds : PrimitiveOverlapBounds (clearance.restrict (patch.cell_refines column row)) numerator}
    {target : Coordinate}
    (request : PrimitiveEdgeAccuracy bounds (patch.transported.cell column row).model neighborhood.patch.base.model
      (surface.mesh.coordinate first) (surface.mesh.coordinate last) target pairs)
    (leftLater : request.index ≤ gridRequest.index) (rightLater : request.index ≤ rightIndex)
    (rightFinish : neighborhood.patch.box.Contains (surface.mesh.coordinate last)) :
    normSq ((readings.values last - readings.values first) -
      (second.primitive.value.eval (surface.mesh.coordinate last) -
        second.primitive.value.eval (surface.mesh.coordinate first))) < 32 * gridRequest.globalBound + 2 * target := by
  let localIncrement := primitives.value column row (surface.mesh.coordinate last) -
    primitives.value column row (surface.mesh.coordinate first)
  let actualIncrement := second.primitive.value.eval (surface.mesh.coordinate last) -
    second.primitive.value.eval (surface.mesh.coordinate first)
  have ownership := RectangularSharedPrimitives.GridPrimitiveAccuracy.shared_local_increment_bound
    gridRequest readings patch.cell_refines column row first last firstInside lastInside
  have analytic := patch.primitive_trace_increment_lt prefixInside differential degreePositive reference
    primitives column row traced inside frame firstInside neighborhood second request leftLater rightLater
    lastInside rightFinish
  have identity : (readings.values last - readings.values first) - actualIncrement =
      ((readings.values last - readings.values first) - localIncrement) + (localIncrement - actualIncrement) := by ring1
  change normSq ((readings.values last - readings.values first) - actualIncrement) < _
  rewrite [identity]
  have triangle := Norm.Bounds.normSq_add_le_two
    ((readings.values last - readings.values first) - localIncrement) (localIncrement - actualIncrement)
  simp only [Norm.Basic.normSq_eq_canonical] at triangle ownership analytic
  rewrite [Norm.Basic.normSq_eq_canonical]
  exact triangle.trans_lt
    ((Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      ((Arithmetic.add_le_add_direct ownership
        (Purelib.Data.Rat.Fraction.Order.Basic.le_refl _)).trans_lt
        (Arithmetic.add_lt_add_left_direct analytic (16 * gridRequest.globalBound)))).trans_eq (by ring1))

end Purelib.Riemann.Meshes.RectangularFaceModels.RectangularPatch
