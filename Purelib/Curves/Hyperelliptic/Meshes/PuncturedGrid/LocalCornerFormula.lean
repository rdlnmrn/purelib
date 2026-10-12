module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedSeamBudget
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

public section

/-! The actual local area is approximated by physical perimeters and fixed corner jumps. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalCornerFormula

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
  target}

variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Fraction.Rational} {floor stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

variable {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}

namespace CrossingRequests

/-- The retained original local-total sum differs from physical perimeters and fixed corner jumps by the paid local and
corner errors. -/
theorem TotalRequest.local_physical_corner_bound {localTarget cornerTarget : Fraction.Rational}
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      (localTarget / 4))
    {retained : Matched.CrossingBank exterior.prepared.energy mesh}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent ((localTarget / 4) / 4) floor)
    (corner : Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget.CornerRequest fixed i j cornerTarget)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (original : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (normalized : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (positive : 0 < localTarget)
    (later : total.allocated.index ≤ stage) (cornerLater : corner.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors -
      retained.cornerJump cache.normalize i j) ≤ 2 * (localTarget + cornerTarget) := by
  have localBound :=
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedSeamBudget.CrossingRequests.TotalRequest.local_physical_jump_paid
    exterior total samples original normalized neighbors positive later
  have cornerBound := Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget.CornerRequest.bound corner cornerLater
    samples
  have equal : Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors -
        retained.cornerJump cache.normalize i j =
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
        Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors
          - samples.endpointJump) +
        (samples.endpointJump - retained.cornerJump cache.normalize i j) := by ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add localBound cornerBound) (by decide))

/-- The common quarter-target allocations pay the complete original local-total versus physical-perimeter and
corner-jump comparison. -/
theorem TotalRequest.local_physical_corner_paid
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      ((target / 4) / 4))
    {retained : Matched.CrossingBank exterior.prepared.energy mesh}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent (((target / 4) / 4) / 4) floor)
    (corner : Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget.CornerRequest fixed i j (target / 4))
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (original : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (normalized : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (positive : 0 < target)
    (later : total.allocated.index ≤ stage) (cornerLater : corner.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors -
      retained.cornerJump cache.normalize i j) ≤ target := by
  have estimate := local_physical_corner_bound exterior total corner samples original normalized neighbors
    (Fraction.Order.Field.div_pos_direct positive (by decide)) later cornerLater
  apply estimate.trans_eq
  calc
    2 * (target / 4 + target / 4) = target / 4 * 4 := by ring1
    _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

end CrossingRequests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalCornerFormula
