module
import Purelib.Data.List.OfFn.Basic
import Purelib.Algebra.FiniteSum.Fin

import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
public import Purelib.Integration.Path.JoinedTraceIndices
public import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Basic

public section

/-! Pointwise sample readback preserves every cached numerical field. No
function extensionality or reevaluation of primitive values is needed. -/
namespace Purelib.Integration.Polynomial.Rectangle.SampleReadback
open Purelib.Integration.Path
open Purelib.Integration.Polynomial
open Purelib.Topology.Polygon
open Purelib.Riemann.Periods

open Purelib.Data.List

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample area)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)

open Purelib.Algebra in
/-- Pointwise equality of indexed primitive readings preserves their exact edge-area sum. -/
theorem area_congr {count : Nat} {first last : Fin (count + 1) → Stokes.PrimitivePoint}
    (equal : ∀ vertex, first vertex = last vertex) : CenteredBilinearPath.area first = CenteredBilinearPath.area last :=
  FiniteSum.Fin.sumFin_congr
    (fun edge => congrArg₂ Stokes.edgeArea (equal edge.castSucc) (equal edge.succ))

namespace Sample
variable {count : Nat} {first last : Fin (count + 1) → Purelib.Topology.Polygon.Stokes.PrimitivePoint}

/-- Transport a sample to pointwise equal original readings while retaining all its computed caches.

The centered values, centered area, endpoint correction and original area are reused; only their original-reading
certificates are transported. -/
@[expose] def readback (sample : CenteredBilinearPath.Sample first) (equal : ∀ vertex, first vertex = last vertex) :
  CenteredBilinearPath.Sample last where
  centered := sample.centered
  centered_eq vertex := by rw [sample.centered_eq, equal vertex, equal 0]
  centeredArea := sample.centeredArea
  centeredArea_eq := sample.centeredArea_eq
  endpoint := sample.endpoint
  endpoint_eq := by rw [sample.endpoint_eq, equal 0, equal (Fin.last count)]
  originalArea := sample.originalArea
  originalArea_eq := sample.originalArea_eq.trans (Rectangle.SampleReadback.area_congr equal)
  decomposition := sample.decomposition

/-- Transport a retained sample along equality of its original edge count using the corresponding finite-index cast. -/
@[expose] def castCount {firstCount lastCount : Nat} (equal : firstCount = lastCount)
    {values : Fin (firstCount + 1) → Stokes.PrimitivePoint} (sample : CenteredBilinearPath.Sample values) :
    CenteredBilinearPath.Sample (fun vertex : Fin (lastCount + 1) => values (Fin.cast (congrArg (· + 1) equal.symm)
      vertex)) := by
  cases equal
  exact sample

/-- Pointwise readback transport retains the exact centered-area cache. -/
theorem readback_centeredArea (sample : CenteredBilinearPath.Sample first) (equal : ∀ vertex, first vertex = last
  vertex) :
    (Rectangle.SampleReadback.Sample.readback sample equal).centeredArea = sample.centeredArea := rfl

/-- Pointwise readback transport retains the exact increment list from the centered cache. -/
theorem readback_increments (sample : CenteredBilinearPath.Sample first) (equal : ∀ vertex, first vertex = last vertex)
  :
    CenteredPathIncrements.Sample.increments (Rectangle.SampleReadback.Sample.readback sample equal) =
      CenteredPathIncrements.Sample.increments sample := rfl

/-- Count transport preserves the retained centered-area cache. -/
theorem castCount_centeredArea {firstCount lastCount : Nat} (equal : firstCount = lastCount)
    {values : Fin (firstCount + 1) → Stokes.PrimitivePoint} (sample : CenteredBilinearPath.Sample values) :
    (Rectangle.SampleReadback.Sample.castCount equal sample).centeredArea = sample.centeredArea := by
  cases equal
  rfl

/-- Count transport preserves the retained sample's increment list. -/
theorem castCount_increments {firstCount lastCount : Nat} (equal : firstCount = lastCount)
    {values : Fin (firstCount + 1) → Stokes.PrimitivePoint} (sample : CenteredBilinearPath.Sample values) :
    CenteredPathIncrements.Sample.increments (Rectangle.SampleReadback.Sample.castCount equal sample) =
      CenteredPathIncrements.Sample.increments sample := by
  cases equal
  rfl

end Sample
namespace VertexTrace
variable {Vertex : Type}

/-- Read the original indexed sample through its retained vertex-trace representation.

The exact count equality and indexed-reading theorem transport the existing sample without recomputing centered values
or area caches. -/
@[expose] def ofIndexedSample {count : Nat} (vertices : Fin (count + 1) → Vertex) (values : Vertex →
  Stokes.PrimitivePoint)
    (sample : CenteredBilinearPath.Sample (fun vertex => values (vertices vertex))) :
    CenteredBilinearPath.Sample (fun vertex => values ((JoinedTrace.VertexTrace.ofIndexed vertices).indexed vertex)) :=
  let equal : count = (JoinedTrace.VertexTrace.ofIndexed vertices).rest.length := by
    dsimp only [JoinedTrace.VertexTrace.ofIndexed]
    exact OfFn.Basic.length_ofFn.symm
  Rectangle.SampleReadback.Sample.readback
    (Rectangle.SampleReadback.Sample.castCount equal sample)
    (fun vertex => congrArg values (JoinedTraceIndices.ofIndexed_indexed vertices vertex).symm)

/-- The indexed-trace sample retains the original centered-area cache. -/
theorem ofIndexedSample_area {count : Nat} (vertices : Fin (count + 1) → Vertex) (values : Vertex →
  Stokes.PrimitivePoint)
    (sample : CenteredBilinearPath.Sample (fun vertex => values (vertices vertex))) :
    (Rectangle.SampleReadback.VertexTrace.ofIndexedSample vertices values sample).centeredArea = sample.centeredArea :=
  Rectangle.SampleReadback.Sample.castCount_centeredArea _ sample

/-- The indexed-trace sample retains the original increment list. -/
theorem ofIndexedSample_increments {count : Nat} (vertices : Fin (count + 1) → Vertex) (values : Vertex →
  Stokes.PrimitivePoint)
    (sample : CenteredBilinearPath.Sample (fun vertex => values (vertices vertex))) :
    CenteredPathIncrements.Sample.increments (Rectangle.SampleReadback.VertexTrace.ofIndexedSample vertices values
      sample) =
      CenteredPathIncrements.Sample.increments sample :=
  Rectangle.SampleReadback.Sample.castCount_increments _ sample

end VertexTrace
end Purelib.Integration.Polynomial.Rectangle.SampleReadback

end
