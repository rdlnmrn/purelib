module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Sewing.CenteredSewnSamples
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Data

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Cut.WordArea.CutBoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Word

@[expose] public section

/-!
# Two-differential readings of the same sewn cut surface

Reuse two retained scalar samples on one assembly. Centering uses the actual
cut anchor, and the complete cut-word correction and physical boundary remain
in the exact identities. No sewing or primitive preparation is repeated.
-/

namespace Purelib.Topology.Surface.Sewing.Bilinear

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces} {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}

set_option genInjectivity false in
/-- Centered two-component primitive readings from two cached samples on one retained cut surface.

The original cut anchor determines both origins, and the complete boundary area is cached with its exact edge-list
readback. -/
structure Samples (left : SewnPrimitiveSamples.CachedSample patch leftLocal) (right : SewnPrimitiveSamples.CachedSample
  patch rightLocal) where
  /-- Cached two-component primitive on the original cut-vertex bank. -/ values : Data.Vector
    Stokes.PrimitivePoint patch.cut.count
  /-- Both components subtract their own original sample value at the common cut anchor. -/ values_eq : ∀ vertex, values
    vertex =
    ⟨left.sewn.values vertex - left.sewn.values patch.cut.anchor,
      right.sewn.values vertex - right.sewn.values patch.cut.anchor⟩
  /-- Cached complete area of the original cut boundary. -/ boundaryArea : Gaussian.Basic.Canonical
  /-- The boundary area is the exact edge-list area of the retained bilinear values. -/ boundaryArea_eq : boundaryArea =
    Stokes.edgeListArea values patch.cut.boundary

constructive_injectivity Samples

namespace Samples

variable {left : SewnPrimitiveSamples.CachedSample patch leftLocal} {right : SewnPrimitiveSamples.CachedSample patch
  rightLocal}

/-- Cache the two anchored primitive components and the complete original cut-boundary area. -/
def build (left : SewnPrimitiveSamples.CachedSample patch leftLocal) (right : SewnPrimitiveSamples.CachedSample patch
  rightLocal) : Samples left right :=
  let leftOrigin := left.sewn.values patch.cut.anchor
  let rightOrigin := right.sewn.values patch.cut.anchor
  let values := Data.Vector.Basic.vectorOfFn fun vertex =>
    (⟨left.sewn.values vertex - leftOrigin, right.sewn.values vertex - rightOrigin⟩ : Stokes.PrimitivePoint)
  ⟨values, Data.Vector.Basic.vectorOfFn_apply _, Stokes.edgeListArea values patch.cut.boundary, rfl⟩

/-- The retained bilinear primitive vanishes at the original cut anchor. -/
theorem anchor_eq_zero (sample : Samples left right) :
    sample.values patch.cut.anchor = PrimitivePoint.zero := by
  rw [sample.values_eq, sub_self, sub_self]
  rfl

/-- Centering preserves the first original scalar sample's edge increments. -/
theorem increment_left (sample : Samples left right) (edge : Stokes.OrientedEdge patch.cut.count) :
    (sample.values edge.finish).left - (sample.values edge.start).left =
      left.sewn.values edge.finish - left.sewn.values edge.start := by
  simp only [sample.values_eq]
  ring1

/-- Centering preserves the second original scalar sample's edge increments. -/
theorem increment_right (sample : Samples left right) (edge : Stokes.OrientedEdge patch.cut.count) :
    (sample.values edge.finish).right - (sample.values edge.start).right =
      right.sewn.values edge.finish - right.sewn.values edge.start := by
  simp only [sample.values_eq]
  ring1

/-- The complete cut-triangle incidence area equals the retained bilinear boundary area. -/
theorem surface_eq_boundary (sample : Samples left right) :
    Stokes.edgeListArea sample.values (patch.cut.triangles.flatMap OrientedTriangle.boundary) = sample.boundaryArea :=
  (patch.cut.boundary_area sample.values).symm.trans sample.boundaryArea_eq.symm

/-- Cache the full signed-word comparison for the retained bilinear primitive and original cut boundary. -/
def wordSample (sample : Samples left right)
    (word : BoundaryWord.CutBoundaryWord patch.cut.vertexLabels patch.cut.boundary) :
    CutBoundaryWord.AreaSample word sample.values (sample.values patch.cut.anchor) :=
  AreaSample.build word sample.values (sample.values patch.cut.anchor)

/-- The retained boundary area equals the original word-matrix contraction plus its full closed correction. -/
theorem boundary_eq_word (sample : Samples left right)
    {word : BoundaryWord.CutBoundaryWord patch.cut.vertexLabels patch.cut.boundary}
    (area : CutBoundaryWord.AreaSample word sample.values (sample.values patch.cut.anchor)) :
    sample.boundaryArea =
      Pairing.contract (fun row column => word.signature.matrix row column) area.values + area.closedCorrection :=
  sample.boundaryArea_eq.trans (area.closed_area_eq patch.cut.closed)

/-- The complete cut-surface area equals the original word-matrix contraction and retained closed correction. -/
theorem surface_eq_word (sample : Samples left right)
    {word : BoundaryWord.CutBoundaryWord patch.cut.vertexLabels patch.cut.boundary}
    (area : CutBoundaryWord.AreaSample word sample.values (sample.values patch.cut.anchor)) :
    Stokes.edgeListArea sample.values (patch.cut.triangles.flatMap OrientedTriangle.boundary) =
      Pairing.contract (fun row column => word.signature.matrix row column) area.values + area.closedCorrection :=
  sample.surface_eq_boundary.trans (sample.boundary_eq_word area)

/-- The original bilinear boundary area splits into physical boundary, jump and defect contributions. -/
theorem boundary_decomposition (sample : Samples left right)
    {pairing : ProjectedEdgePairs.ProjectedEdgePairing patch.cut.vertexLabels patch.cut.boundary}
    (boundary : ProjectedEdgePairing.PrimitiveSample pairing sample.values) :
    sample.boundaryArea = boundary.boundaryArea + boundary.jumpSum + boundary.defectSum :=
  sample.boundaryArea_eq.trans boundary.boundary_decomposition

end Samples
end Purelib.Topology.Surface.Sewing.Bilinear
