module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Sewing.CenteredSewnSamples
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Sewing.Bilinear.Errors
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.CenteredSewnSamples

open Purelib.Topology.Surface.Word

public section

/-! Conjugate/value pairs reuse the already sewn scalar samples. Their exact
boundary identity retains the complete word correction and physical edges. -/
namespace Purelib.Topology.Surface.Sewing.SewnConjugateSamples

open Purelib

open Purelib.Data.Rat

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeArea edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces} {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}

set_option genInjectivity false in
/-- Centered conjugate/value readings from two cached scalar samples on the same cut patch.

The first original sample is conjugated after anchoring; the second is anchored directly, and the complete original
boundary area is cached. -/
structure ConjugatePair (left : SewnPrimitiveSamples.CachedSample patch leftLocal) (right :
  SewnPrimitiveSamples.CachedSample patch rightLocal) where
  /-- Cached conjugate/value primitive points on the original cut-vertex bank. -/ values : Data.Vector
    Stokes.PrimitivePoint patch.cut.count
  /-- The components use their original sample values and the shared original cut anchor. -/ values_eq : ∀ vertex,
    values vertex =
    ⟨conj (left.sewn.values vertex - left.sewn.values patch.cut.anchor),
      right.sewn.values vertex - right.sewn.values patch.cut.anchor⟩
  /-- Cached complete conjugate/value area of the original cut boundary. -/ boundaryArea : Gaussian.Basic.Canonical
  /-- The boundary cache is exactly the edge-list area of the retained primitive points. -/ boundaryArea_eq :
    boundaryArea = Stokes.edgeListArea values patch.cut.boundary

constructive_injectivity ConjugatePair

namespace ConjugatePair

variable {left : SewnPrimitiveSamples.CachedSample patch leftLocal} {right : SewnPrimitiveSamples.CachedSample patch
  rightLocal}

/-- Gaussian conjugation preserves subtraction. -/
theorem conj_sub (a b : Gaussian.Basic.Canonical) : Data.Gaussian.Basic.conj (a - b) = Data.Gaussian.Basic.conj
  a - Data.Gaussian.Basic.conj b := by
  apply Gaussian.Basic.ext
  · rfl
  · simp only [Data.Gaussian.Basic.conj, Gaussian.Basic.sub_im, -eq_self, -iff_self]; ring1

/-- Cache the anchored original conjugate/value pair and its complete cut-boundary area. -/
@[expose] def build (left : SewnPrimitiveSamples.CachedSample patch leftLocal) (right :
  SewnPrimitiveSamples.CachedSample patch rightLocal) : ConjugatePair left right :=
  let leftOrigin := left.sewn.values patch.cut.anchor
  let rightOrigin := right.sewn.values patch.cut.anchor
  let values := Data.Vector.Basic.vectorOfFn fun vertex =>
    (⟨conj (left.sewn.values vertex - leftOrigin), right.sewn.values vertex - rightOrigin⟩ : Stokes.PrimitivePoint)
  ⟨values, Data.Vector.Basic.vectorOfFn_apply _, Stokes.edgeListArea values patch.cut.boundary, rfl⟩

/-- The first retained component reads the conjugate of the original first sample's edge increment. -/
theorem increment_left (sample : ConjugatePair left right) (edge : Stokes.OrientedEdge
  patch.cut.count) :
    (sample.values edge.finish).left - (sample.values edge.start).left =
      Data.Gaussian.Basic.conj (left.sewn.values edge.finish - left.sewn.values edge.start) := by
  rw [sample.values_eq, sample.values_eq]
  change Data.Gaussian.Basic.conj _ - Data.Gaussian.Basic.conj _ = _
  rw [← conj_sub]
  exact congrArg Data.Gaussian.Basic.conj (by ring1)

/-- The second retained component reads the original second sample's edge increment. -/
theorem increment_right (sample : ConjugatePair left right) (edge : Stokes.OrientedEdge
  patch.cut.count) :
    (sample.values edge.finish).right - (sample.values edge.start).right =
      right.sewn.values edge.finish - right.sewn.values edge.start := by
  simp only [sample.values_eq, -eq_self, -iff_self]
  ring1

/-- The complete original cut-triangle incidence area equals the retained conjugate/value boundary area. -/
theorem surface_eq_boundary (sample : ConjugatePair left right) :
    Stokes.edgeListArea sample.values (patch.cut.triangles.flatMap OrientedTriangle.boundary) = sample.boundaryArea :=
  (patch.cut.boundary_area sample.values).symm.trans sample.boundaryArea_eq.symm

/-- The retained boundary area is the original word-matrix contraction plus its full closed correction. -/
theorem boundary_eq_word (sample : ConjugatePair left right)
    {word : BoundaryWord.CutBoundaryWord patch.cut.vertexLabels patch.cut.boundary}
    (area : CutBoundaryWord.AreaSample word sample.values (sample.values patch.cut.anchor)) :
    sample.boundaryArea =
      Pairing.contract (fun row column => word.signature.matrix row column) area.values + area.closedCorrection :=
  sample.boundaryArea_eq.trans (area.closed_area_eq patch.cut.closed)

/-- On the diagonal, the conjugate pair is the centered version of the original Hermitian surface sample; its complete
boundary area is unchanged. -/
theorem diagonal_boundary {surface : SewnPrimitiveSamples.CachedSample patch leftLocal} (sample :
  ConjugatePair surface surface) :
    sample.boundaryArea = surface.boundaryArea := by
  let centered := Centered.build surface
  have values (vertex) : sample.values vertex = centered.energyValues vertex := by
    rw [sample.values_eq, centered.energyValues_eq, centered.primitives_eq]
    rfl
  have equal (word : List (Stokes.OrientedEdge patch.cut.count)) :
      Stokes.edgeListArea sample.values word = Stokes.edgeListArea centered.energyValues word := by
    induction word with
    | nil => rfl
    | cons edge rest ih =>
        exact congrArg₂ (· + ·) (congrArg₂ Stokes.edgeArea (values edge.start) (values edge.finish)) ih
  exact sample.boundaryArea_eq.trans ((equal patch.cut.boundary).trans centered.boundary_area)

end ConjugatePair
end Purelib.Topology.Surface.Sewing.SewnConjugateSamples
