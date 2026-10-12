module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
public import Purelib.Riemann.RootContinuation.NewtonRequestedFullHoleAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FullHoleRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineTransport
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! The actual retained sewn surface has only the fixed exterior correction
left after the complete annular-hole comparison. -/
section

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Riemann.Branches.NewtonRequestedCutComparison (CutAnnularReadings)
open Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank (InterfaceBank)
open Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank (OmittedHoleBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FullHoleRemainder (fullHoleEvaluation_eq_correction)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus} {target radius :
    Rational} {floor : Nat}

namespace Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

open Purelib.Curves.Hyperelliptic in
/-- The full original hole remainder equals the physical correction minus its exterior component. -/
theorem
  fullHoleRemainder_eq_physical
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) :
    prepared.fullHoleRemainder readings = readings.physical -
      Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection readings.normalized
        readings.neighbors readings.left readings.right .exterior := by
  have holes := Meshes.PuncturedGrid.FullHoleRemainder.fullHoleEvaluation_eq_correction readings.normalized
    readings.neighbors readings.left readings.right
  change prepared.fullHoleRemainder readings = _ at holes
  rw [holes, readings.physical_components]
  ring1

end Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

section

namespace Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

open Purelib.Curves.Hyperelliptic in
/-- The original selected and remaining annular areas sum to the retained paired reading. -/
theorem selected_remaining_eq_paired
  (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    {readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache}
    (cached : CutAnnularReadings prepared.comparison readings) :
    cached.annuli.selectedArea + cached.remaining.remainingArea = readings.paired := by
  have boundary : readings.surface.boundaryArea = readings.paired :=
    (readings.surface.boundary_eq_word readings.word).trans
      (congrArg (fun value => value + readings.word.closedCorrection)
        (readings.integral.contract_eq readings.word.values))
  exact cached.remaining.partition.trans ((cached.remaining.boundary_eq_bilinear readings.surface).trans boundary)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A strict squared-norm bound for the original remaining area plus its exterior correction.

Both terms read from the same retained boundary preparation, cache and annular comparison; the requested rational amount
bounds their exact sum. -/
@[expose] def RetainedExteriorBound
  (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : prepared.Readings cache) (requested : Fraction.Rational) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (readings.2.val.remaining.remainingArea +
    Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection readings.1.normalized
      readings.1.neighbors readings.1.left readings.1.right .exterior) < requested

end Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

namespace Purelib.Riemann.RootContinuation.NewtonRetainedExteriorBound.BoundaryPreparation

open Purelib.Data.Rat in
/-- One quarter of a positive rational value is at most four times that value. -/
private theorem quarter_le_four {value : Fraction.Rational} (positive : 0 < value) : value / 4 ≤ 4 * value := by
  apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Fraction.Rational) < 4)).mpr
  exact (show value = 1 * value by ring1).le.trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (1 : Fraction.Rational) ≤ 16)
      positive.le).trans_eq (by ring1))

open Purelib.Data.Gaussian in
/-- The exact area partition and hole correction identify the retained exterior remainder by subtraction. -/
private theorem retained_identity {removed remaining paired holes physical exterior : Basic.Canonical}
    (partition : removed + remaining = paired) (holeEq : holes = physical - exterior) :
    remaining + exterior = (paired + physical) - (removed + holes) := by
  rw [holeEq, ← partition]
  ring1

end Purelib.Riemann.RootContinuation.NewtonRetainedExteriorBound.BoundaryPreparation

namespace Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The original remaining area plus exterior correction is bounded by sixteen times the target.

The selected-interface and omitted-hole banks share the supplied original readings and later stage; their full-hole
payment combines with the retained corrected-area estimate. -/
theorem retained_exterior_bound
  (prepared : BoundaryPreparation preparation first second target radius floor)
    (interfaces : InterfaceBank prepared.excision prepared.traces first second)
    (omitted : OmittedHoleBank prepared.excision prepared.traces first second)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : prepared.Readings cache)
    (later : prepared.index ≤ stage) (interfaceLater : interfaces.index ≤ stage) (omittedLater : omitted.index ≤ stage)
      :
    RetainedExteriorBound prepared readings (16 * target) := by
  have full := prepared.full_holes_bound interfaces omitted readings.2.val later interfaceLater omittedLater
  have positive : 0 < target := (Fraction.Order.Arithmetic.mul_pos_direct prepared.fine.positive (by
      decide : (0 : Fraction.Rational) < 4)).trans_eq
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  have corrected := ((readings.1.corrected_bound ((Data.Nat.Order.le_max_left _ _).trans later)).trans
    prepared.paid.cutTarget_le).trans (NewtonRetainedExteriorBound.BoundaryPreparation.quarter_le_four positive)
  have partition := prepared.selected_remaining_eq_paired readings.2.val
  have holes := prepared.fullHoleRemainder_eq_physical readings.1
  have equal := NewtonRetainedExteriorBound.BoundaryPreparation.retained_identity partition holes
  have added := (Fraction.Order.Arithmetic.add_lt_add_left_direct full (Data.Gaussian.Norm.Basic.normSq
    (readings.1.paired +
    readings.1.physical))).trans_le
    (Fraction.Order.Arithmetic.add_le_add_direct corrected (le_refl (4 * target)))
  have estimate := (Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2) added)
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_lt (estimate.trans_eq (by ring1))

end Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

end
end
