module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.Topology.NewtonSewnExcision
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnBilinearRequest
import Purelib.Riemann.Periods.BilinearBoundaryReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums

@[expose] public section

/-! The cached Newton annulus uses exactly the fine triangles selected
inside its band, with its physical hole absent from the selection. -/
namespace Purelib.Riemann.Topology.NewtonBandSelectedSewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AnnularEntry)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus sourceMask sourceMask_triangleIndex)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition (selectedFullTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
  {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {stage : Nat} {cache : Numerics
    domains stage}

open Purelib.Algebra in
open Purelib.Curves in
/-- The original annular source mask selects exactly the complete two-sheet bilinear triangle sum inside the retained
band. -/
private theorem source_sum (entry : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current) (left :
  Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh)
    (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) :
    FiniteSum.Fin.sumFin (fun source => if sourceMask entry source
      then Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea
        left right source else 0) =
      Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition.selectedFullTriangleArea left right (fun position =>
        decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box entry.hole.index)))
          := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.LiftedMesh.triangle_sum]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  have mask (upper : Bool) :
      sourceMask entry (current.mesh.triangleIndex position sheet upper) =
      decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box entry.hole.index)) :=
    sourceMask_triangleIndex entry position sheet upper
  rw [mask false, mask true]
  rfl

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
/-- Compare the actual sewn paired annulus with its original selected fine triangles.

The two retained sewn value caches define the paired primitive on the same cut surface, and the request pays the area
error with the physical hole excluded. -/
theorem selected_accurate
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
    {leftSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values}
    {rightSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values}
    (annulus : SewnAnnulus leftSurface)
    {prepared : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i
      j} {error : Rat.Fraction.Rational} {floor : Nat}
    (request : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request prepared error floor)
      (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (edgeListArea (fun vertex =>
      (⟨leftSurface.sewn.values vertex, rightSurface.sewn.values vertex⟩ : PrimitivePoint))
        (annulus.selected.triangles.flatMap OrientedTriangle.boundary) -
      Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition.selectedFullTriangleArea left right (fun position =>
        decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines
          (grid.bands.box annulus.source.hole.index)))) < error := by
  let bilinear := Topology.Surface.Sewing.Bilinear.Samples.build leftSurface rightSurface
  have estimated :=
    Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnBilinearRequest.BilinearPreparation.Request.selected_accurate
    request later left right bilinear annulus.selected
  have area := Periods.BilinearBoundaryReadback.triangles_eq_raw
    bilinear (annulus.selected.triangles)
  rw [area] at estimated
  exact (congrArg (fun triangles => Data.Gaussian.Norm.Basic.normSq (edgeListArea (fun vertex =>
    (⟨leftSurface.sewn.values vertex, rightSurface.sewn.values vertex⟩ : PrimitivePoint))
      (annulus.selected.triangles.flatMap OrientedTriangle.boundary) - triangles))
    (source_sum annulus.source left right)).symm.trans_lt estimated

end Purelib.Riemann.Topology.NewtonBandSelectedSewing
