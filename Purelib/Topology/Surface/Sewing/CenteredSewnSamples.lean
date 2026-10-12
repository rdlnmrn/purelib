module
public import Purelib.Topology.Surface.Sewing.CutCycleChains
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryDefectReadings
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Integration.Path.CenteredPrimitiveArea
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Integration.Energy

open Purelib.Integration.Path

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Word

public section

/-!
# Centered energy readings of one already sewn surface

Only the anchored values and their conjugate pairs are materialized. The
sewing, face allowances and cached complete boundary area are reused. Exact
readbacks also admit generated centered data without resewing the surface.
-/

namespace Purelib.Topology.Surface.Sewing.CenteredSewnSamples

open Purelib

open Purelib.Data.Rat

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeListArea)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces} {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}

set_option genInjectivity false in
/-- Anchored primitive and conjugate energy values for one existing sewn sample.

All values retain the original cut-vertex bank and subtract its actual anchor reading; the original sewing and area
caches remain the owners of the readbacks. -/
structure Centered (sample : SewnPrimitiveSamples.CachedSample patch localValues) where
  /-- Cached original scalar readings after subtracting the retained anchor value. -/ primitives :
    PrimitiveSewing.PrimitiveValues patch.cut.count
  /-- Each centered primitive is its original sewn value minus the original anchor value. -/ primitives_eq : ∀ vertex,
    primitives vertex = sample.sewn.values vertex - sample.sewn.values patch.cut.anchor
  /-- Cached conjugate primitive-point pairs of those exact centered readings. -/ energyValues :
    Data.Vector Stokes.PrimitivePoint patch.cut.count
  /-- Every energy point is constructed from the corresponding retained centered primitive. -/ energyValues_eq : ∀
    vertex, energyValues vertex = Polygon.energyPrimitivePoint (primitives vertex)

constructive_injectivity Centered

namespace Centered

variable {sample : SewnPrimitiveSamples.CachedSample patch localValues}

/-- Cache anchored scalar values and their conjugate primitive-point pairs from the original sewn sample. -/
@[expose] def build (sample : SewnPrimitiveSamples.CachedSample patch localValues) : CenteredSewnSamples.Centered sample
  :=
  let origin := sample.sewn.values patch.cut.anchor
  let primitives := Data.Vector.Basic.vectorOfFn fun vertex => sample.sewn.values vertex - origin
  let energyValues := Data.Vector.Basic.vectorOfFn fun vertex => Polygon.energyPrimitivePoint (primitives vertex)
  ⟨primitives, Data.Vector.Basic.vectorOfFn_apply _, energyValues, Data.Vector.Basic.vectorOfFn_apply _⟩

/-- Centered energy values are the original energy values minus the original anchor's energy value. -/
theorem energyValues_sub (centered : CenteredSewnSamples.Centered sample) (vertex : Fin patch.cut.count) :
    centered.energyValues vertex = (PrimitivePoint.sub (sample.energyValues vertex)) (sample.energyValues
      patch.cut.anchor) := by
  rw [centered.energyValues_eq, centered.primitives_eq, sample.energyValues_eq, sample.energyValues_eq]
  unfold Polygon.energyPrimitivePoint PrimitivePoint.sub
  congr 1
  apply Gaussian.Basic.ext
  · rfl
  · simp only [Data.Gaussian.Basic.conj, Gaussian.Basic.sub_im, -eq_self, -iff_self]; ring1

/-- Every retained centered energy point has conjugate coordinates. -/
theorem conjugate (centered : CenteredSewnSamples.Centered sample) (vertex : Fin patch.cut.count) :
  (PrimitivePoint.Conjugate (centered.energyValues vertex)) := by
  rw [centered.energyValues_eq]
  rfl

/-- The right energy coordinate reads the exact retained centered scalar primitive. -/
theorem right_eq (centered : CenteredSewnSamples.Centered sample) (vertex : Fin patch.cut.count) :
    (centered.energyValues vertex).right = centered.primitives vertex := by
  rw [centered.energyValues_eq]
  rfl

/-- The centered energy point at the original cut anchor is zero. -/
theorem anchor_eq_zero (centered : CenteredSewnSamples.Centered sample) :
    centered.energyValues patch.cut.anchor = PrimitivePoint.zero := by
  rw [centered.energyValues_eq, centered.primitives_eq, Gaussian.Basic.sub_self]
  rfl

/-- Constant recentering leaves the original sewn pair mismatch unchanged. -/
theorem defect_normSq (centered : CenteredSewnSamples.Centered sample)
    (entry : ProjectedEdgePair.Sample (labels := patch.cut.vertexLabels) centered.energyValues) :
    Data.Gaussian.Norm.Basic.normSq entry.defect.right = Data.Gaussian.Norm.Basic.normSq
      ((sample.sewn.values entry.pair.first.finish - sample.sewn.values entry.pair.first.start) +
        (sample.sewn.values entry.pair.second.finish - sample.sewn.values entry.pair.second.start)) := by
  rw [BoundaryDefectReadings.defect_right_normSq entry centered.primitives centered.right_eq]
  simp only [centered.primitives_eq, -eq_self, -iff_self]
  congr 1
  ring1

/-- Centering preserves the complete closed boundary area of the original cached sample. -/
theorem boundary_area (centered : CenteredSewnSamples.Centered sample) :
    Stokes.edgeListArea centered.energyValues patch.cut.boundary = sample.boundaryArea := by
  have equal (edges : List (Stokes.OrientedEdge patch.cut.count)) :
      Stokes.edgeListArea centered.energyValues edges =
        Stokes.edgeListArea (fun vertex => (PrimitivePoint.sub (sample.energyValues vertex)) (sample.energyValues
          patch.cut.anchor)) edges := by
    induction edges with
    | nil => rfl
    | cons edge edges ih =>
      simp only [Stokes.edgeListArea, centered.energyValues_sub, ih, -eq_self, -iff_self]
      rfl
  rw [equal, CenteredPrimitiveArea.edgeListArea_sub_constant_closed sample.energyValues _ patch.cut.closed]
  exact sample.boundaryArea_eq.symm

/-- The genuine one-sided boundary contribution remains present after recentering, as do all jump and defect terms of
the same cached pairing. -/
theorem boundary_decomposition (centered : CenteredSewnSamples.Centered sample)
    {pairing : ProjectedEdgePairs.ProjectedEdgePairing patch.cut.vertexLabels patch.cut.boundary}
    (boundary : ProjectedEdgePairing.PrimitiveSample pairing centered.energyValues) :
    sample.boundaryArea = boundary.boundaryArea + boundary.jumpSum + boundary.defectSum :=
  centered.boundary_area.symm.trans boundary.boundary_decomposition

/-- The centered energy increment of a cut cycle reads the original endpoint difference.

Centering subtracts the same retained anchor from both sewn scalar endpoints.
The complete original cut path determines the increment and keeps its distinct endpoints. -/
theorem cycle_increment_right {vertexCount faceCount : Nat}
    {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount} {patch : SewingTree.SewnPatch faces}
    {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    (sample : SewnPrimitiveSamples.CachedSample patch localValues) (centered : CenteredSewnSamples.Centered sample)
    (cycle : CutCycleChains.ClosedCutCycle patch.cut.vertexLabels (patch.cut.boundary.map (VertexSewing.OrientedEdge.map
      patch.cut.vertexLabels))) :
    (cycle.increment centered.energyValues).right = sample.sewn.values cycle.finish - sample.sewn.values cycle.start :=
      by
  rw [CutCycleChains.ClosedCutCycle.increment_eq]
  simp only [Stokes.PrimitivePoint.sub, centered.right_eq, centered.primitives_eq, -eq_self, -iff_self]
  ring1

end Centered
end Purelib.Topology.Surface.Sewing.CenteredSewnSamples
