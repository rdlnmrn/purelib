module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnConjugateRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas
import Purelib.Riemann.Periods.BilinearBoundaryReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums

@[expose] public section

/-! The cached Newton annulus uses exactly the fine triangles selected
inside its band, with its physical hole absent from the selection. -/
namespace Purelib.Riemann.Topology.NewtonBandSelectedConjugateSewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AnnularEntry)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas (selectedConjugateFullTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
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
open Purelib.Riemann in
open Purelib.Curves in
/-- The original annular source mask selects exactly the complete two-sheet conjugate triangle sum inside the retained
band. -/
private theorem source_sum (entry : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current) (left :
  Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh)
    (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) :
    FiniteSum.Fin.sumFin (fun source => if Topology.NewtonSewnExcision.AllHoleExcision.sourceMask entry source
      then Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left right source
        else 0) =
      Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right (fun
        position =>
        decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box entry.hole.index)))
          := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.LiftedMesh.triangle_sum current.mesh]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  have mask (upper : Bool) :
      Topology.NewtonSewnExcision.AllHoleExcision.sourceMask entry (Meshes.GridLiftedMesh.LiftedMesh.triangleIndex
        current.mesh position sheet upper) =
      decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box entry.hole.index)) :=
    Topology.NewtonSewnExcision.AllHoleExcision.sourceMask_triangleIndex entry position sheet upper
  rw [mask false, mask true]
  rfl

open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
/-- Compare the actual sewn conjugate annulus with its original selected fine triangles.

The supplied pair retains both sewn value caches on the same mesh, while the original source mask excludes the physical
hole and the request pays the selected area error. -/
theorem selected_conjugate_accurate
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
    {leftSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values}
    {rightSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values}
    (pair : Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
    (annulus : SewnAnnulus leftSurface)
    {prepared : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i
      j} {error : Rat.Fraction.Rational} {floor : Nat}
    (request : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request prepared error floor)
      (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (edgeListArea pair.values
        (annulus.selected.triangles.flatMap OrientedTriangle.boundary) -
      Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right (fun
        position =>
        decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines
          (grid.bands.box annulus.source.hole.index)))) < error := by
  have estimated :=
    Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request.selected_conjugate_accurate
    request later left right pair annulus.selected
  exact (congrArg (fun triangles => Data.Gaussian.Norm.Basic.normSq (edgeListArea pair.values
      (annulus.selected.triangles.flatMap OrientedTriangle.boundary) - triangles))
    (source_sum annulus.source left right)).symm.trans_lt estimated

end Purelib.Riemann.Topology.NewtonBandSelectedConjugateSewing
