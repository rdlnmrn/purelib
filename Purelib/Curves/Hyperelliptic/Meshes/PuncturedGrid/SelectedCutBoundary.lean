module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCornerBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

public section

/-! The actual cut request controls the boundary of any selected face set,
with precisely the source triangles carried by its internal crossings. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCornerBounds
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
open Purelib.Data.Rat
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest (Readings)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {i j : Fin genus} {target : Rational} {floor stage : Nat}
  {request : CutPairingRequest lifted domains i j
    target floor}
  {cache : Numerics domains stage}

namespace Readings

/-- Internal pairs have been replaced by their original source triangle areas; selected physical sides and interfaces to
discarded faces remain. -/
@[expose] def selectedCorrection (readings : CutPairingRequest.Readings request cache) (keep : Fin
  base.faces.regulars.length → Bool) : Gaussian :=
  FacePerimeters.selectedBoundary readings.normalized readings.neighbors keep +
    CrossingBank.selectedTriangleArea request.crossings readings.left readings.right keep

/-- Every selected-face correction fits one quarter of the original paid cut target.

The bound retains actual source triangles at internal crossings and the physical or discarded-face sides on the
selection boundary. -/
theorem selected_corrected_bound (readings : CutPairingRequest.Readings request cache) (keep : Fin
  base.faces.regulars.length → Bool)
    (later : request.index ≤ stage) : Data.Gaussian.Norm.Basic.normSq
      (selectedCorrection readings keep) ≤ target
      / 4 := by
  have perimeter := SelectedPerimeterBounds.selected_perimeter_bound request.exterior readings.original
    readings.normalized keep
    (request.ownership_le.trans later)
  have crossing := request.total.selected_boundary_bound readings.crossings readings.normalized readings.neighbors keep
    (request.crossing_le.trans later)
  have jumpBound : Data.Gaussian.Norm.Basic.normSq (FacePerimeters.selectedBoundary readings.normalized
    readings.neighbors keep + readings.crossings.selectedJump keep) ≤
      2 * (((((target / 4) / 4) / 4) / 4) + ((((target / 4) / 4) / 4) / 4)) := by
    have equal : FacePerimeters.selectedBoundary readings.normalized readings.neighbors keep +
      readings.crossings.selectedJump keep =
        readings.normalized.selectedPerimeterSum keep -
          (readings.normalized.selectedPerimeterSum keep - FacePerimeters.selectedBoundary readings.normalized
            readings.neighbors keep -
            readings.crossings.selectedJump keep) := by ring1
    rw [equal]
    exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct perimeter crossing) (by decide))
  have corner := CornerRequest.selected_triangle_bound
    request.corner (request.corner_le.trans later) readings.crossings readings.left readings.right keep
  have equal : selectedCorrection readings keep =
      (FacePerimeters.selectedBoundary readings.normalized readings.neighbors keep + readings.crossings.selectedJump
        keep) -
        (readings.crossings.selectedJump keep - CrossingBank.selectedTriangleArea request.crossings readings.left
          readings.right keep) := by
    dsimp only [selectedCorrection, -eq_self,
      -iff_self]
    ring1
  rw [equal]
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct jumpBound corner) (by decide))
  apply estimate.trans
  calc
    _ = 2 * (((((target / 4) / 4) / 4) / 4) * 4 + (((target / 4) / 4) / 4)) := by ring1
    _ = 2 * ((((target / 4) / 4) / 4) + (((target / 4) / 4) / 4)) := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by
      decide)]
    _ = (((target / 4) / 4) / 4) * 4 := by ring1
    _ = (target / 4) / 4 := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
    _ ≤ target / 4 := Fraction.Order.Field.divide_le_self (Fraction.Order.Field.div_pos_direct request.positive (by
      decide)).le (by decide)

end Readings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary
