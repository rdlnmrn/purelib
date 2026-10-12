module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.Topology.NewtonSewnExcision
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Paid local-area comparison for actual Newton excision

The retained annuli are compared to the local source areas of exactly their
cut-triangle occurrences. A single geometry-first request pays their union,
so the number of holes introduces no additional unbudgeted summation. This
controls sewing discrepancy; it does not assert that the local annular area
vanishes or replace the separate Newton-boundary comparison.
-/

namespace Purelib.Riemann.Topology.NewtonSewnAreaComparison.AreaExcision

open Purelib.Topology.Polygon.Stokes (OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample (AreaExcision)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate)

open Purelib.Data.Gaussian.Basic.Canonical

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → OrientedTriangle vertexCount}
  {patch : SewnPatch faces} {localValues : Fin faceCount →
    PrimitiveValues 3} {sample :
    CachedSample patch localValues}

open Purelib.Integration in
open Purelib.Data in
/-- The remaining-area discrepancy equals the total period discrepancy minus the removed local-area discrepancy. -/
theorem local_comparison_error (excision : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.AreaExcision
  sample) (periodArea localRemoved : Gaussian.Basic.Canonical) :
    excision.remaining.area - (periodArea - localRemoved) =
      (sample.boundaryArea - periodArea) - (excision.removedArea - localRemoved) := by
  rw [← excision.partition]
  ring1

open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- Two strict quarter-target comparisons pay the complete remaining-area target.

The exact excision partition relates the actual remaining area to the supplied period area minus retained local removed
area. -/
theorem local_accurate (excision : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.AreaExcision sample)
  (periodArea localRemoved : Gaussian.Basic.Canonical) {target : Surface.Sewing.SewnPrimitiveFaces.Coordinate}
    (periodBound : normSq (sample.boundaryArea - periodArea) < target / 4)
    (removedBound : normSq (excision.removedArea - localRemoved) < target / 4) :
    normSq (excision.remaining.area - (periodArea - localRemoved)) < target := by
  rw [local_comparison_error excision periodArea localRemoved]
  have scalar := Gaussian.Norm.Bounds.normSq_sub_le_two (sample.boundaryArea - periodArea) (excision.removedArea -
    localRemoved)
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  apply scalar.trans_lt
  apply (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide : (0 : Surface.Sewing.SewnPrimitiveFaces.Coordinate) < 2)
      (Rat.Fraction.Order.Arithmetic.add_lt_add_direct periodBound removedBound)).trans_eq
  calc
    2 * (target / 4 + target / 4) = (target / 4) * 4 := by ring1
    _ = target := Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

end Purelib.Riemann.Topology.NewtonSewnAreaComparison.AreaExcision

namespace Purelib.Riemann.Topology.NewtonSewnAreaComparison.Sewn

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests (SelectionAreaPreparation)
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample (FaceSelection)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (Sewn sourceMask)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Coordinate}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}
  {localValues : Fin lifted.mesh.triangles.length → PrimitiveValues 3}
  {excision : AllHoleExcision grid lifted} {sample :
    CachedSample lifted.cutPolygon.patch localValues}

set_option genInjectivity false in
open Purelib.Integration in
/-- Retain local source-area readbacks for the actual removed and remaining Newton faces.

One union mask identifies all removed annuli on the original cached cut surface, preserving the existing remaining
selection. -/
structure LocalAreas (sewn : Sewn excision sample) where
  /-- The actual original triangle selection removed by the union of retained annular masks. -/ removed :
    Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample (fun index => excision.entries.any
    (fun entry => sourceMask entry index))
  /-- The local source-area readback on that exact removed selection. -/ annular : removed.LocalArea
  /-- The local source-area readback on the original retained remaining selection. -/ remaining :
    sewn.remaining.LocalArea

constructive_injectivity LocalAreas

namespace LocalAreas

open Purelib.Integration in
/-- Build local area readbacks for the retained all-hole excision.

The removed union is selected once, and both local readbacks use the original cached surface and remaining geometry. -/
def build (sewn : Sewn excision sample) : LocalAreas sewn :=
  let removed := Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection.build sample (fun index =>
    excision.entries.any (fun entry => sourceMask entry index))
  ⟨removed, Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection.LocalArea.build removed,
    Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection.LocalArea.build sewn.remaining⟩

variable {sewn : Sewn excision sample}

/-- The retained union selection's sewn area equals the original total annular area. -/
theorem removed_area (areas : LocalAreas sewn) : areas.removed.area = sewn.annularArea := by
  have equal := (areas.removed.partition sewn.remaining).trans sewn.partition.symm
  exact add_right_cancel equal

variable {differential : Differential genus} {domains :
  FaceDomainBank lifted.frames grid.faces.regulars}
  {index : Nat} {shared : FacePrimitiveBank
    differential index domains}
  {triangles : TriangleReadings shared
    lifted.mesh}
  {surface : CachedSample lifted.cutPolygon.patch triangles.values}
    {retained : Sewn excision surface}
  {prepared : SelectionAreaPreparation
    lifted.cutPolygon.patch domains differential} {error : Coordinate} {floor : Nat}

section
open Purelib.Curves
/-- One paid selection request controls the full removed annular union against its actual local source area. -/
theorem annular_accurate (areas : LocalAreas retained) (request :
  Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests.SelectionAreaPreparation.Request prepared error floor)
    (later : request.contact.index ≤ index) : normSq (retained.annularArea - areas.annular.value) < error := by
  rw [← areas.removed_area]
  exact request.accurate later triangles surface areas.removed areas.annular

/-- The same selection request controls the actual remaining sewn area against its local source readback. -/
theorem remaining_accurate (areas : LocalAreas retained) (request :
  Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests.SelectionAreaPreparation.Request prepared error floor)
    (later : request.contact.index ≤ index) : normSq (retained.remaining.area - areas.remaining.value) < error :=
  request.accurate later triangles surface retained.remaining areas.remaining

end

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- Transport the supplied period-area estimate through the actual Newton excision.

The original selection request pays the annular sewing discrepancy, leaving the retained local annular source term
explicit in the final comparison. -/
theorem period_accurate (areas : LocalAreas retained) (request :
  Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests.SelectionAreaPreparation.Request prepared (error / 4) floor)
    (later : request.contact.index ≤ index) (periodArea : Gaussian)
    (periodBound : normSq (surface.boundaryArea - periodArea) < error / 4) :
    normSq (retained.remaining.area - (periodArea - areas.annular.value)) < error := by
  have periodScalar := periodBound
  have annularScalar := areas.annular_accurate request later
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at periodScalar annularScalar
  have scalar := Topology.NewtonSewnAreaComparison.AreaExcision.local_accurate
    retained.areaExcision periodArea areas.annular.value periodScalar annularScalar
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

end LocalAreas
end Purelib.Riemann.Topology.NewtonSewnAreaComparison.Sewn
