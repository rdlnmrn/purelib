module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
public import Purelib.Integration.Energy.Polygon

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Topology.Surface.Cut.Patch

open Purelib

open Purelib.Data

open Purelib.Integration.Energy

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.WordArea.CutBoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

open Purelib.Topology.Surface.Word

@[expose] public section

/-!
# Cached sewn surfaces and their complete cut-word area

One retained assembly produces the sewn values, the full face-error bank,
and the conjugate/value readings used by the second bilinear relation.
The boundary identity includes every cut-word correction and physical edge.
Smallness of these computed corrections is not assumed or asserted here.
-/

namespace Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples

open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing
open Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch.Assembly (Sample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open Purelib.Topology.Surface.Cut.WordArea

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

set_option genInjectivity false in
/-- One sewn surface with its retained face errors and complete boundary-area reading.

The cached conjugate/value points use the actual sewn values, and the boundary area keeps every original cut-edge
occurrence. -/
structure CachedSample (patch : SewingTree.SewnPatch faces) (localValues : Fin faceCount →
  PrimitiveSewing.PrimitiveValues 3) where
  /-- Actual primitive sample of the original assembly. -/ sewn : Assembly.Sample patch.assembly localValues
  /-- Face-error bank indexed by those exact sewn values. -/ faces : SewnPrimitiveFaces.FaceBank patch.cut localValues
    sewn.values
  /-- The cached bank is the one built from the actual sewn readings. -/ faces_eq : faces = FaceBank.build sewn.readings
  /-- Cached conjugate/value point at each retained cut vertex. -/ energyValues : Data.Vector
    Stokes.PrimitivePoint patch.cut.count
  /-- Each cached energy point is constructed from that vertex's actual sewn primitive value. -/ energyValues_eq : ∀
    vertex, energyValues vertex = Polygon.energyPrimitivePoint (sewn.values vertex)
  /-- Cached Gaussian area of the complete cut boundary. -/ boundaryArea : Gaussian.Basic.Canonical
  /-- The cached area is the exact edge-list reading of the retained energy points. -/ boundaryArea_eq : boundaryArea =
    Stokes.edgeListArea energyValues patch.cut.boundary

constructive_injectivity CachedSample

namespace CachedSample

variable {patch : SewingTree.SewnPatch faces} {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}

/-- Sample the retained assembly once and cache face errors, energy points and boundary area. -/
def build (patch : SewingTree.SewnPatch faces) (localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3) :
  SewnPrimitiveSamples.CachedSample patch localValues :=
  let sewn := Assembly.sample localValues patch.assembly
  let faces := FaceBank.build sewn.readings
  let energyValues := Data.Vector.Basic.vectorOfFn fun vertex => Polygon.energyPrimitivePoint (sewn.values vertex)
  ⟨sewn, faces, rfl, energyValues, Data.Vector.Basic.vectorOfFn_apply _, Stokes.edgeListArea energyValues
    patch.cut.boundary, rfl⟩

/-- The cached face squared errors are bounded by twice the cached total allowance. -/
theorem face_errors (sample : SewnPrimitiveSamples.CachedSample patch localValues) : sample.faces.squaredErrors ≤ 2 *
  sample.faces.totalAllowance :=
  sample.faces.aggregate_error_bound

/-- The area over the actual cut triangles is the retained boundary area. -/
theorem surface_eq_boundary (sample : SewnPrimitiveSamples.CachedSample patch localValues) :
    Stokes.edgeListArea sample.energyValues (patch.cut.triangles.flatMap OrientedTriangle.boundary) =
      sample.boundaryArea :=
  (patch.cut.boundary_area sample.energyValues).symm.trans sample.boundaryArea_eq.symm

/-- Consume an already retained geometric word, without pairing the cut boundary again or replaying the sewing. -/
def wordSample (sample : SewnPrimitiveSamples.CachedSample patch localValues) (word : BoundaryWord.CutBoundaryWord
  patch.cut.vertexLabels patch.cut.boundary) :
    CutBoundaryWord.AreaSample word sample.energyValues (sample.energyValues patch.cut.anchor) :=
  AreaSample.build word sample.energyValues (sample.energyValues patch.cut.anchor)

/-- Split the cached boundary area into the original cut-word matrix contraction and full closed correction. -/
theorem boundary_eq_word (sample : SewnPrimitiveSamples.CachedSample patch localValues)
    {word : BoundaryWord.CutBoundaryWord patch.cut.vertexLabels patch.cut.boundary}
    (area : CutBoundaryWord.AreaSample word sample.energyValues (sample.energyValues patch.cut.anchor)) :
    sample.boundaryArea = Pairing.contract (fun row column => word.signature.matrix row column) area.values +
      area.closedCorrection :=
  sample.boundaryArea_eq.trans (area.closed_area_eq patch.cut.closed)

/-- Read the actual sewn surface area as its cut-word contraction plus retained closed correction. -/
theorem surface_eq_word (sample : SewnPrimitiveSamples.CachedSample patch localValues)
    {word : BoundaryWord.CutBoundaryWord patch.cut.vertexLabels patch.cut.boundary}
    (area : CutBoundaryWord.AreaSample word sample.energyValues (sample.energyValues patch.cut.anchor)) :
    Stokes.edgeListArea sample.energyValues (patch.cut.triangles.flatMap OrientedTriangle.boundary) =
      Pairing.contract (fun row column => word.signature.matrix row column) area.values + area.closedCorrection :=
  sample.surface_eq_boundary.trans (sample.boundary_eq_word area)

end CachedSample
end Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
