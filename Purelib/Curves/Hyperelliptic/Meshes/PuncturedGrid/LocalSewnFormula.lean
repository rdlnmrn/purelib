module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! The actual sewn boundary consumes the complete local triangle comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.RootIsolation
open Purelib

open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)

open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}
  {mesh : LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
  target}

variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Fraction.Rational} {floor stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

variable {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
/-- The paid original local triangle and sewing comparisons bound the complete sewn boundary with its physical
correction retained.

Both original triangle readings share the numerical bank; the local, corner and sewing requests must all be sufficiently
late. -/
theorem
  local_sewn_boundary_bound
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      ((target / 4) / 4))
    {retained : CrossingBank exterior.prepared.energy mesh}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent (((target / 4) / 4) / 4) floor)
    (corner : Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget.CornerRequest fixed i j (target / 4))
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (original : FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (normalized : FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize i j)
    {forest : Topology.Surface.Sewing.SewingForest mesh.triangulation.faces}
    {polygon : Topology.Surface.Sewing.SewingConnected.SewingForest.SinglePolygon forest}
    {prepared : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation polygon domains i j}
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request prepared target floor)
    {leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample polygon.patch left.values}
    {rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample polygon.patch right.values}
    (surface : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface)
    (sewingLater : sewing.index ≤ stage)
    (neighbors : PuncturedFaces.NeighborBank faces) (positive : 0 < target)
    (later : total.allocated.index ≤ stage) (cornerLater : corner.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
      surface.boundaryArea -
      (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors
        -
        Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right)) ≤ 4 *
          target := open Purelib.Algebra in by
  have localBound :=
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.CrossingRequests.TotalRequest.local_full_triangle_paid
    exterior total corner left right samples original normalized neighbors
    positive later cornerLater
  rw [Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.RegularMeshes.TwoSheetRequest.fullTriangleArea_eq_sum left right]
    at localBound
  have sewnBound := sewing.accurate sewingLater left right surface
  have equal : Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
    surface.boundaryArea -
      (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors
        -
        Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right) =
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
        FiniteSum.Fin.sumFin (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left
        right) -
        (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized
          neighbors -
          Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right)) -
      (surface.boundaryArea - FiniteSum.Fin.sumFin
        (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right)) := by ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add localBound sewnBound.le) (by decide)).trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest
