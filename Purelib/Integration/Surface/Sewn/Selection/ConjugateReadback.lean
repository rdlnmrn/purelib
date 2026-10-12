module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin

public import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Errors
public import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
public import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Integration.Surface.Sewn.Selection.BilinearReadback
import Purelib.Riemann.Readings.SelectedConjugateRequests
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! The original face mask selects conjugate areas on the same cached pair. -/
namespace Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Data.Gaussian.Basic (conj)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Purelib.Topology.Polygon.Stokes.OrientedTriangle
  vertexCount}
  {patch : Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch faces} {localValues : Fin faceCount →
    Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
  {sample : Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample patch localValues} {keep : Fin faceCount →
    Bool}

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Surface.Sewn.Selection in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface.Sewing in
/-- A retained conjugate-area request certifies selected sewn area against the original conjugated local wedge sum.

Conjugation applies only to the original left readings; both sample owners, local accuracy witnesses, source mask and
retained magnitude request remain separate. -/
theorem conjugate_request_accurate {rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    {right : SewnPrimitiveSamples.CachedSample patch rightLocal} {magnitude target : SewnPrimitiveFaces.Coordinate}
    (selected : Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample keep) (bilinear :
      SewnConjugateSamples.ConjugatePair sample right)
    (request : Bilinear.Requests.AreaRequest patch magnitude target)
    (leftAccurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance sample.sewn.readings)
    (rightAccurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance right.sewn.readings)
    (bounded : ∀ position (index : Fin 3),
      (PrimitiveAreaBounds.PrimitivePoint.Bounded (⟨conj (localValues (Bilinear.Errors.traceAt sample position).source
        index) - Data.Gaussian.Basic.conj (localValues (Bilinear.Errors.traceAt sample position).source 0),
        rightLocal (Bilinear.Errors.traceAt sample position).source index - rightLocal (Bilinear.Errors.traceAt sample
          position).source 0⟩ :
          Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq
      (Stokes.edgeListArea bilinear.values (selected.triangles.flatMap Stokes.OrientedTriangle.boundary) -
        FiniteSum.Fin.sumFin (fun position : Fin patch.cut.triangles.length =>
          if keep (Bilinear.Errors.traceAt sample position).source then Stokes.triangleWedgeArea
            ⟨conj (localValues (Bilinear.Errors.traceAt sample position).source 0), rightLocal (Bilinear.Errors.traceAt
              sample position).source 0⟩
            ⟨conj (localValues (Bilinear.Errors.traceAt sample position).source 1), rightLocal (Bilinear.Errors.traceAt
              sample position).source 1⟩
            ⟨conj (localValues (Bilinear.Errors.traceAt sample position).source 2), rightLocal (Bilinear.Errors.traceAt
              sample position).source 2⟩
          else 0)) < target := by
  rw [BilinearReadback.paired_area_eq_masked selected bilinear.values, ← FiniteSum.Fin.sumFin_sub]
  have estimate := SelectedConjugateRequests.selected_conjugate_accurate request bilinear (fun position => keep
    (Bilinear.Errors.traceAt sample position).source)
    leftAccurate rightAccurate bounded
  have equal : ∀ triangle : Stokes.OrientedTriangle patch.cut.count,
      Stokes.edgeListArea bilinear.values triangle.boundary = Stokes.triangleWedgeArea
        (bilinear.values triangle.first) (bilinear.values triangle.second) (bilinear.values triangle.third) := by
    intro triangle
    simp only [Stokes.OrientedTriangle.boundary, Stokes.edgeListArea, Stokes.edgeArea, Stokes.triangleWedgeArea]
    ring1
  simpa only [equal, ite_sub_ite, sub_self] using estimate

end Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection
