module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting
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

/-! Existing exterior requests pay every normalized seam and corner contribution. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedSeamBudget

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

/-- The original pair budgets bound the complete seam and corner sum over both sheets.

The squared-norm bound retains the actual regular-face count and the original per-pair target. -/
theorem FacePerimeters.seam_corner_bound
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      target)
    (perimeters : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (later : exterior.prepared.energy.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.seamTotalSum perimeters +
      Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.cornerTotalSum perimeters) ≤
      4 * (faces.regulars.length : Fraction.Rational)^2 * exterior.pairTarget := open Purelib.Algebra in by
  let difference := fun position sheet => ((perimeters.assemblies.get position).get sheet).localTotal -
    ((perimeters.assemblies.get position).get sheet).exterior
  have bounded (position : Fin faces.regulars.length) (sheet : Fin 2) :
      Data.Gaussian.Norm.Basic.normSq (difference position sheet) ≤ exterior.pairTarget := by
    have estimate :=
      Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearAssembly.EnergyPreflight.Request.clipped_local_sub_exterior_bound
      ((exterior.prepared.energy.entries.get sheet).entries.get position).modelRequest
      (((exterior.prepared.energy.entries.get sheet).index_ge position).trans
        ((exterior.prepared.energy.index_ge sheet).trans later))
      (cache.atDomain position sheet) i j ((perimeters.assemblies.get position).get sheet)
    exact estimate.trans (exterior.pair_bound stage later sheet position i j)
  have equal : Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.seamTotalSum perimeters +
      Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.cornerTotalSum perimeters =
      FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (difference position)) := by
    unfold Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.seamTotalSum
      Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.cornerTotalSum
    rw [← FiniteSum.Fin.sumFin_add]
    apply FiniteSum.Fin.sumFin_congr
    intro position
    rw [← FiniteSum.Fin.sumFin_add]
    apply FiniteSum.Fin.sumFin_congr
    intro sheet
    dsimp only [difference, -eq_self, -iff_self]
    rw [((perimeters.assemblies.get position).get sheet).decomposition]
    ring1
  rw [equal]
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ ((2 : Fraction.Rational)^2 * exterior.pairTarget)
    (fun position => Gaussian.Norm.Sum.Indexed.normSq_sumFin_le (difference position) exterior.pairTarget (bounded
      position))
  exact estimate.trans_eq (by ring1)

/-- The original exterior request pays the complete normalized seam and corner sum at every sufficient stage.

The retained genus and face-count weights pay the same per-pair estimates used by the cached face perimeters. -/
theorem FacePerimeters.seam_corner_paid
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      target)
    (perimeters : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (positive : 0 < target) (later : exterior.prepared.energy.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.seamTotalSum perimeters +
      Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.cornerTotalSum perimeters) ≤ target := by
  have genusLe : (1 : Fraction.Rational) ≤ (genus : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct (Nat.succ_le_of_lt ((Nat.zero_le i.val).trans_lt i.isLt))
  have squareLe : (1 : Fraction.Rational) ≤ (genus : Fraction.Rational)^2 := by
    simpa only [one_mul, pow_two, -eq_self, -iff_self] using Fraction.Order.Arithmetic.mul_le_mul_direct genusLe genusLe
      (by decide : (0 : Fraction.Rational) ≤ 1) ((by decide : (0 : Fraction.Rational) ≤ 1).trans genusLe)
  have factorLe : (4 : Fraction.Rational) ≤ 8 * (genus : Fraction.Rational)^2 := by
    have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe
      (by decide +kernel : (0 : Fraction.Rational) ≤ 8)
    exact (by decide +kernel : (4 : Fraction.Rational) ≤ 8).trans (by
        simpa only [mul_one, -eq_self, -iff_self]
          using estimate)
  have weightLe := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct factorLe
      (Fraction.Order.Arithmetic.sq_nonneg_direct (faces.regulars.length : Fraction.Rational)))
        exterior.pair_positive.le
  have reorder : (8 * (genus : Fraction.Rational)^2) * (faces.regulars.length : Fraction.Rational)^2 *
    exterior.pairTarget =
      8 * (faces.regulars.length : Fraction.Rational)^2 * (genus : Fraction.Rational)^2 * exterior.pairTarget := by
        ring1
  rw [reorder] at weightLe
  have localNonnegative : 0 ≤ 2 * exterior.localTarget := by
    rw [exterior.localTarget_eq]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Field.div_pos_direct positive (by decide)).le
  have paid : 8 * (faces.regulars.length : Fraction.Rational)^2 * (genus : Fraction.Rational)^2 * exterior.pairTarget ≤
    target :=
    (le_add_of_nonneg_left localNonnegative).trans exterior.paid
  exact (Hyperelliptic.Meshes.PuncturedGrid.NormalizedSeamBudget.FacePerimeters.seam_corner_bound
    exterior perimeters later).trans (weightLe.trans paid)

namespace CrossingRequests

/-- The actual local face areas differ from physical boundaries and endpoint jumps
by the two allocated finite errors, including every seam and corner. -/
theorem TotalRequest.local_physical_jump_bound
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      target)
    {retained : Matched.CrossingBank exterior.prepared.energy mesh}
      {jumpTarget : Fraction.Rational}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent (jumpTarget / 4) floor)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (original : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (normalized : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (positive : 0 < target)
    (later : total.allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors -
      samples.endpointJump) ≤
      2 * (jumpTarget + target) := by
  have jump :=
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.CrossingRequests.TotalRequest.original_local_jump_bound
    total samples original normalized neighbors later
  have seam := Hyperelliptic.Meshes.PuncturedGrid.NormalizedSeamBudget.FacePerimeters.seam_corner_paid
    exterior normalized positive (total.allocated.base_le.trans later)
  have equal : Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors -
      samples.endpointJump =
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
        Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.seamTotalSum normalized -
        Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.cornerTotalSum normalized -
        Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors
          -
        samples.endpointJump) +
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.seamTotalSum normalized +
        Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.cornerTotalSum normalized) := by ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add jump seam)
      (by decide : (0 : Fraction.Rational) ≤ 2))

/-- A positive user request pays seams, corners, and matched-side approximation
on the same prepared mesh and normalized numerical bank. -/
theorem TotalRequest.local_physical_jump_paid
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      (target / 4))
    {retained : Matched.CrossingBank exterior.prepared.energy mesh}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent ((target / 4) / 4) floor)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (original : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (normalized : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (positive : 0 < target)
    (later : total.allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors -
      samples.endpointJump) ≤ target := by
  have estimate :=
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedSeamBudget.CrossingRequests.TotalRequest.local_physical_jump_bound
    exterior total samples original normalized neighbors
    (Fraction.Order.Field.div_pos_direct positive (by decide)) later
  apply estimate.trans_eq
  calc
    2 * (target / 4 + target / 4) = target / 4 * 4 := by ring1
    _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

end CrossingRequests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedSeamBudget
