module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic

public import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Errors
public import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Integration.Surface.Sewn.Selection.Paired
import Purelib.Riemann.Periods.SelectedBilinearRequests
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

public section

/-! Exact position readback for the original cached face-selection mask. -/

namespace Purelib.Integration.Surface.Sewn.Selection.BilinearReadback

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Purelib.Topology.Polygon.Stokes.OrientedTriangle
  vertexCount}
  {patch : Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch faces} {localValues : Fin faceCount →
    Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
  {sample : Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample patch localValues} {keep : Fin faceCount →
    Bool}

open Purelib.Algebra in
open Purelib.Integration.Surface.Sewn.Selection in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface.Sewing in
/-- Read the selected paired area as the exact masked sum over original cut triangles.

The original face-bank length and trace-to-triangle identities preserve each retained source selection at its original
index. -/
theorem paired_area_eq_masked (selected : Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample keep)
    (primitive : Fin patch.cut.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive (selected.triangles.flatMap Stokes.OrientedTriangle.boundary) =
      FiniteSum.Fin.sumFin (fun position : Fin patch.cut.triangles.length =>
        if keep (Bilinear.Errors.traceAt sample position).source then
          Stokes.edgeListArea primitive patch.cut.triangles[position.val].boundary else 0) := by
  rw [Paired.paired_area_readback selected primitive,
    Purelib.Polynomial.Geometry.Grid.CellBoundary.sumValues_filter_eq_sumFin_count sample.faces.entries _ _
      (SewnPrimitiveBoundary.FaceBank.entries_length sample.faces)]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  change (if keep (Bilinear.Errors.traceAt sample position).source then
    Stokes.edgeListArea primitive (Bilinear.Errors.traceAt sample position).triangle.boundary else 0) = _
  rw [Bilinear.Errors.traceAt_triangle sample position]

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Surface.Sewn.Selection in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface.Sewing in
/-- A retained paired-area request certifies selected sewn area against the original selected local wedge sum.

Both original sample owners supply their separate local accuracy witnesses, and the common request and magnitude bounds
apply to the exact masked source faces. -/
theorem paired_request_accurate {rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    {right : SewnPrimitiveSamples.CachedSample patch rightLocal} {magnitude target : SewnPrimitiveFaces.Coordinate}
    (selected : Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample keep) (bilinear :
      Topology.Surface.Sewing.Bilinear.Samples
      sample right)
    (request : Bilinear.Requests.AreaRequest patch magnitude target)
    (leftAccurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance sample.sewn.readings)
    (rightAccurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance right.sewn.readings)
    (bounded : ∀ position (index : Fin 3),
      (PrimitiveAreaBounds.PrimitivePoint.Bounded (⟨localValues (Bilinear.Errors.traceAt sample position).source index -
        localValues (Bilinear.Errors.traceAt sample position).source 0,
        rightLocal (Bilinear.Errors.traceAt sample position).source index - rightLocal (Bilinear.Errors.traceAt sample
          position).source 0⟩ :
          Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq
      (Stokes.edgeListArea bilinear.values (selected.triangles.flatMap Stokes.OrientedTriangle.boundary) -
        FiniteSum.Fin.sumFin (fun position : Fin patch.cut.triangles.length =>
          if keep (Bilinear.Errors.traceAt sample position).source then Stokes.triangleWedgeArea
            ⟨localValues (Bilinear.Errors.traceAt sample position).source 0, rightLocal (Bilinear.Errors.traceAt sample
              position).source 0⟩
            ⟨localValues (Bilinear.Errors.traceAt sample position).source 1, rightLocal (Bilinear.Errors.traceAt sample
              position).source 1⟩
            ⟨localValues (Bilinear.Errors.traceAt sample position).source 2, rightLocal (Bilinear.Errors.traceAt sample
              position).source 2⟩
          else 0)) < target := by
  rw [BilinearReadback.paired_area_eq_masked selected bilinear.values,
    ← FiniteSum.Fin.sumFin_sub]
  have estimate := SelectedBilinearRequests.selected_accurate request bilinear
    (fun position => keep (Bilinear.Errors.traceAt sample position).source)
    leftAccurate rightAccurate bounded
  have equal : ∀ triangle : Stokes.OrientedTriangle patch.cut.count,
      Stokes.edgeListArea bilinear.values triangle.boundary = Stokes.triangleWedgeArea
        (bilinear.values triangle.first) (bilinear.values triangle.second) (bilinear.values triangle.third) := by
    intro triangle
    simp only [Stokes.OrientedTriangle.boundary, Stokes.edgeListArea, Stokes.edgeArea, Stokes.triangleWedgeArea,
      -eq_self, -iff_self]
    ring1
  simpa only [equal, ite_sub_ite, sub_self, -eq_self, -iff_self] using estimate

end Purelib.Integration.Surface.Sewn.Selection.BilinearReadback
