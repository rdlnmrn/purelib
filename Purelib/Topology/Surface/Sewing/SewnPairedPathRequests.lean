module
import Purelib.Data.Gaussian.Norm.Basic

public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPathArea
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.SewnPairedPathArea
public import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Data.Rat.Fraction.Order.Basic

public section

/-! The existing geometry-first path-area budget pays both differential
samples at one tolerance, including all inherited sewing errors. -/

section

open Purelib.Data.Rat

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Integration.Path

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPathArea.PathSources

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

namespace Purelib.Topology.Surface.Sewing.SewnPairedPathRequests

open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate FaceBank)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources)
open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests (PathAreaRequest)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
  {count : Nat} {magnitude target : SewnPrimitiveFaces.Coordinate}
  {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {leftValues rightValues : PrimitiveSewing.PrimitiveValues patch.count}
  {leftBank : SewnPrimitiveFaces.FaceBank patch leftLocal leftValues} {rightBank : SewnPrimitiveFaces.FaceBank patch
    rightLocal rightValues}
  {edges : List (Stokes.OrientedEdge patch.count)} {sources : SewnPrimitiveFaces.PathSources patch edges}

/-- One retained path-area budget bounds the complete paired original/source polygon discrepancy. -/
theorem paired_accurate (request : SewnPathAreaRequests.PathAreaRequest assembly count magnitude target)
    (left : PathSources.Sample sources leftBank) (right : PathSources.Sample sources rightBank)
    (lengthEq : edges.length = count)
    (bounded : ∀ source ∈ sources.sources,
      (PrimitivePoint.Bounded (⟨source.increment leftLocal, source.increment rightLocal⟩ : Stokes.PrimitivePoint))
        magnitude)
    (leftSmall : left.bound < request.error) (rightSmall : right.bound < request.error) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (edges.map (fun edge =>
      (⟨leftValues edge.finish - leftValues edge.start,
        rightValues edge.finish - rightValues edge.start⟩ : Stokes.PrimitivePoint))) -
      PairedIncrementArea.area (sources.sources.map (fun source =>
        (⟨source.increment leftLocal, source.increment rightLocal⟩ : Stokes.PrimitivePoint)))) < target := by
  have estimate := SewnPairedPathArea.paired_area_error_le left right request.magnitude_nonnegative bounded
  rw [lengthEq] at estimate
  exact estimate.trans_lt (request.paid ((Sample.bound_nonnegative left).trans (Fraction.Order.Basic.le_max_left _ _))
    (Fraction.Order.Basic.max_lt leftSmall rightSmall))

/-- Both cached original sewn samples satisfy the paired-area target at the same retained contact tolerance. -/
theorem paired_cached_accurate {sewnPatch : SewingTree.SewnPatch faces}
    (request : SewnPathAreaRequests.PathAreaRequest sewnPatch.assembly count magnitude target)
    (left : SewnPrimitiveSamples.CachedSample sewnPatch leftLocal) (right : SewnPrimitiveSamples.CachedSample sewnPatch
      rightLocal)
    (leftAccurate : SewnPrimitiveRequests.LocalAccuracy request.path.tolerance left.sewn.readings)
    (rightAccurate : SewnPrimitiveRequests.LocalAccuracy request.path.tolerance right.sewn.readings)
    {edges : List (Stokes.OrientedEdge sewnPatch.cut.count)} (sources : SewnPrimitiveFaces.PathSources sewnPatch.cut
      edges)
    (lengthEq : edges.length = count)
    (bounded : ∀ source ∈ sources.sources,
      (PrimitivePoint.Bounded (⟨source.increment leftLocal, source.increment rightLocal⟩ : Stokes.PrimitivePoint))
        magnitude) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (edges.map (fun edge =>
      (⟨left.sewn.values edge.finish - left.sewn.values edge.start,
        right.sewn.values edge.finish - right.sewn.values edge.start⟩ : Stokes.PrimitivePoint))) -
      PairedIncrementArea.area (sources.sources.map (fun source =>
        (⟨source.increment leftLocal, source.increment rightLocal⟩ : Stokes.PrimitivePoint)))) < target :=
  paired_accurate request (CachedSample.pathSample left sources) (CachedSample.pathSample right
    sources) lengthEq bounded
    (request.path.cached_accurate left leftAccurate sources lengthEq.le)
    (request.path.cached_accurate right rightAccurate sources lengthEq.le)

end Purelib.Topology.Surface.Sewing.SewnPairedPathRequests

end
