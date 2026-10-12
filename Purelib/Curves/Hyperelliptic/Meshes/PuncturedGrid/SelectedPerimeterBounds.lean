module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedSeamBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearAssembly
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Tactic.Ring

public section

/-! Restrict the existing fine perimeter bank to any retained face subset.
Every selected face keeps all four full side traces, both sheets, seams and
corners. The original shared request pays the subset without a new mesh. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} {cuts :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}
  {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage} {i
    j : Fin genus}
  {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    target}

namespace Matched.FacePerimeters

/-- Sum all four oriented cached sides on the selected original faces and both sheets. -/
@[expose] def
  selectedPerimeterSum
  (perimeters : FacePerimeters (request := request) cache i j)
    (keep : Fin faces.regulars.length → Bool) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet => if keep position then
    let sides := (perimeters.perimeters.get position).get sheet
    sides.bottom + sides.right - sides.top - sides.left else 0))

/-- Sum every retained seam and corner correction on the selected original faces and both sheets. -/
@[expose] def
  selectedSeamCornerSum
  (perimeters : FacePerimeters (request := request) cache i j)
    (keep : Fin faces.regulars.length → Bool) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet => if keep position then
    ((perimeters.assemblies.get position).get sheet).seams +
      ((perimeters.assemblies.get position).get sheet).cornerTotal else 0))

end Matched.FacePerimeters

namespace SelectedPerimeterBounds

/-- The selected original local-total sum minus its normalized perimeter sum is exactly the selected seam and corner
correction. -/
theorem selected_normalized_decomposition
    (original : Matched.FacePerimeters (request := request) cache i j)
    (normalized : Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (keep : Fin faces.regulars.length → Bool) :
    original.selectedLocalSum keep - normalized.selectedPerimeterSum keep = normalized.selectedSeamCornerSum keep := by
  have pointwise (position : Fin faces.regulars.length) (sheet : Fin 2) :
      (if keep position then ((original.assemblies.get position).get sheet).localTotal else 0) -
      (if keep position then
        let sides := (normalized.perimeters.get position).get sheet
        sides.bottom + sides.right - sides.top - sides.left else 0) =
      (if keep position then ((normalized.assemblies.get position).get sheet).seams +
        ((normalized.assemblies.get position).get sheet).cornerTotal else 0) := by
    cases keep position with
    | false => change (0 : Gaussian.Basic.Canonical) - 0 = 0; ring1
    | true =>
        simp only [if_pos (rfl : true = true), -eq_self, -iff_self]
        rw [← ((normalized.perimeters.get position).get sheet).exterior_eq,
          ← Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.normalized_corrected_exterior_eq
            original normalized position sheet]
        ring1
  have equal := FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_congr (pointwise position))
  have split := FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_sub
    (fun sheet => if keep position then ((original.assemblies.get position).get sheet).localTotal else 0)
    (fun sheet => if keep position then
      let sides := (normalized.perimeters.get position).get sheet
      sides.bottom + sides.right - sides.top - sides.left else 0))
  rw [split, FiniteSum.Fin.sumFin_sub] at equal
  exact equal

/-- The original per-pair budget bounds the complete selected seam and corner sum with its actual face-count weight. -/
theorem selected_seam_corner_bound
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      target)
    (perimeters : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (keep : Fin faces.regulars.length → Bool) (later : exterior.prepared.energy.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (perimeters.selectedSeamCornerSum keep) ≤ 4 * (faces.regulars.length :
      Fraction.Rational)^2 * exterior.pairTarget := by
  have bounded (position : Fin faces.regulars.length) (sheet : Fin 2) :
      Data.Gaussian.Norm.Basic.normSq (if keep position then ((perimeters.assemblies.get position).get sheet).seams
        +
        ((perimeters.assemblies.get position).get sheet).cornerTotal else 0) ≤ exterior.pairTarget := by
    cases keep position with
    | false =>
      simpa only [if_neg Bool.false_ne_true, Gaussian.Norm.Basic.normSq_zero, -eq_self, -iff_self] using
        exterior.pair_positive.le
    | true =>
      have estimate :=
        DomainBilinearAssembly.EnergyPreflight.Request.clipped_local_sub_exterior_bound
        ((exterior.prepared.energy.entries.get sheet).entries.get position).modelRequest
        (((exterior.prepared.energy.entries.get sheet).index_ge position).trans
          ((exterior.prepared.energy.index_ge sheet).trans later))
        (cache.atDomain position sheet) i j ((perimeters.assemblies.get position).get sheet)
      have bound := estimate.trans (exterior.pair_bound stage later sheet position i j)
      have equal : ((perimeters.assemblies.get position).get sheet).localTotal -
          ((perimeters.assemblies.get position).get sheet).exterior =
          ((perimeters.assemblies.get position).get sheet).seams +
            ((perimeters.assemblies.get position).get sheet).cornerTotal := by
        rw [((perimeters.assemblies.get position).get sheet).decomposition]
        ring1
      simpa only [if_pos (rfl : true = true), equal, -eq_self, -iff_self] using bound
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ ((2 : Fraction.Rational)^2 * exterior.pairTarget)
    (fun position => Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ exterior.pairTarget (bounded position))
  exact estimate.trans_eq (by ring1)

/-- No subtraction of possibly cancelling discarded areas is used here.
The subset's local and seam errors are each bounded from their own terms. -/
theorem selected_perimeter_bound
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      target)
    (original : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (normalized : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize i j)
    (keep : Fin faces.regulars.length → Bool) (later : exterior.prepared.ownership.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (normalized.selectedPerimeterSum keep) ≤ target := by
  have localBound := Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.FacePerimeters.selected_local_bound
    exterior.prepared original keep later
  have seamBound := Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterBounds.selected_seam_corner_bound exterior
    normalized keep
    (exterior.prepared.ownership.energy_le.trans later)
  have equal : normalized.selectedPerimeterSum keep = original.selectedLocalSum keep - normalized.selectedSeamCornerSum
    keep := by
    rw [← Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterBounds.selected_normalized_decomposition original
      normalized keep]
    ring1
  rw [equal]
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct localBound
      seamBound) (by decide))
  have genusLe : (1 : Fraction.Rational) ≤ (genus : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct (Nat.succ_le_of_lt ((Nat.zero_le i.val).trans_lt i.isLt))
  have genusSquare : (1 : Fraction.Rational) ≤ (genus : Fraction.Rational)^2 := by
    simpa only [one_pow, -eq_self, -iff_self] using Fraction.Order.Arithmetic.pow_le_pow_direct (by
        decide : (0 : Fraction.Rational) ≤ 1) genusLe 2
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct genusSquare
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 8)
        (Fraction.Order.Arithmetic.sq_nonneg_direct (faces.regulars.length : Fraction.Rational))))
    exterior.pair_positive.le
  exact estimate.trans ((show 2 * (exterior.localTarget + 4 * (faces.regulars.length : Fraction.Rational)^2 *
    exterior.pairTarget) =
    2 * exterior.localTarget + (8 * (faces.regulars.length : Fraction.Rational)^2 * 1) * exterior.pairTarget by
      ring1).trans_le
    ((Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) paid).trans exterior.paid))

end SelectedPerimeterBounds

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
