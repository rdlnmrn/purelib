module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Tactic.Ring

public section

/-! The requested cut pairing consumes the actual all-hole excision on its
retained primitive bank. The remaining ambient and annular contributions are
cached explicitly, including origins, jumps, defects, and outer offsets. -/
namespace Purelib.Riemann.Branches.NewtonRequestedCutComparison

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison (Sample)
open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison
  (SewnSample)
open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison
  (PhysicalTerm)
open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalSides.NewtonPreparation.FamilyAreaRequest
open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining.NewtonPreparation.FamilyAreaRequest
open PairedComparison.SewnSample (Excision)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles
open PhysicalComparison.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.PhysicalSides

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {request : FamilyAreaRequest
    preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {excision : AllHoleExcision request.single.grid lifted}
  {prepared :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision} {first second : Fin genus}
  {domains : FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}
  {comparison :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
    prepared first second domains}
  {cutTarget : Rational} {floor stage : Nat}
  {cut : CutPairingRequest lifted domains first
    second cutTarget floor}
  {cache : Numerics domains stage}

open Purelib.Curves in
open Purelib.Data in
set_option genInjectivity false in
/-- Retained annular and remaining-triangle readings on a cut comparison's exact scalar surfaces.

The source, sewn annuli, physical sides and remaining excision share the acquired left/right surfaces. The cached
correction retains both the exterior contribution and every physical-hole correction. -/
structure CutAnnularReadings (comparison :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison prepared
  first second domains)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings cut cache) where
  /-- The paired comparison sample on the exact left and right cut readings. -/ source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.Sample
    comparison readings.left readings.right
  /-- The sewn annular sample using the retained left and right scalar surfaces. -/ annuli :
    Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
    source readings.leftSurface readings.rightSurface
  /-- The physical-side data of the same sewn annular sample. -/ sides :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalSides
    annuli
  /-- The remaining excision triangles of the same sewn annular sample. -/ remaining :
    PairedRemaining.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.Excision
    annuli
  /-- The cached exterior and physical-hole correction sum. -/ correction : Gaussian.Basic.Canonical
  /-- The cache equals the exterior correction plus all retained physical-hole contributions. -/ correction_eq :
    correction =
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection readings.normalized
      readings.neighbors readings.left readings.right .exterior +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sides.entries.map (fun entry =>

          remainingCorrection
          entry readings.normalized))

constructive_injectivity CutAnnularReadings

namespace CutAnnularReadings

variable {readings : CutPairingRequest.Readings
  cut cache}

section
open Purelib.Curves
open Purelib.Data
/-- Acquire the annular, physical-side and remaining-triangle caches from one cut reading.

Build each dependent cache from its retained predecessor and compute the exact combined correction once. -/
@[expose] def build (comparison :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison prepared
  first second domains)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings cut cache) :
      CutAnnularReadings comparison readings :=
  let source :=
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.Sample.build
    comparison readings.left readings.right
  let annuli :=
    PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.build
    source readings.leftSurface readings.rightSurface
  let sides :=
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalSides.build
    annuli
  let remaining :=
    PairedRemaining.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.Excision.build
    annuli
  let correction := Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection
    readings.normalized readings.neighbors readings.left readings.right .exterior +
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (sides.entries.map (fun entry =>

        remainingCorrection
        entry readings.normalized))
  ⟨source, annuli, sides, remaining, correction, rfl⟩

/-- Compute the physical-hole correction allowance from the cut sewing budget.

The squared hole count retains aggregate multiplicity; the weight and error are those of the same sewing request. -/
@[expose] def correctionAllowance (cut : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted
  domains first second cutTarget floor) : Rat.Fraction.Rational :=
  (request.single.grid.faces.holes.length : Rat.Fraction.Rational) *
    ((request.single.grid.faces.holes.length : Rat.Fraction.Rational) *
      (8 * (8 * (cut.sewing.budget.weight * cut.sewing.budget.error))))

/-- After the cut stage, annular correction plus physical reading differs from the cached correction by at most its
allowance. -/
theorem physical_accurate (cached : CutAnnularReadings comparison readings) (later : cut.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (cached.annuli.correction + readings.physical - cached.correction) ≤
      correctionAllowance cut := by
  rw [cached.correction_eq]
  exact
    global_correction_accurate
    cached.sides readings.normalized readings.neighbors cut.sewing
    (cut.sewing_le.trans later) readings.surface

end

section
open Purelib.Data
/-- The annularly corrected paired reading has quadrance at most twice the cut target plus correction allowance.

The stage has reached the cut request, and all terms use the retained comparison surfaces. -/
theorem pairing_bound (cached : CutAnnularReadings comparison readings) (later : cut.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.paired - cached.annuli.correction + cached.correction) ≤
      2 * (cutTarget + correctionAllowance cut) := by
  have paired := readings.corrected_bound later
  have physical := cached.physical_accurate later
  have equal : readings.paired - cached.annuli.correction + cached.correction =
      (readings.paired + readings.physical) -
        (cached.annuli.correction + readings.physical - cached.correction) := by ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add paired physical) (by decide))

/-- Combine a strict remaining-area estimate with a weak corrected-pair estimate.

The quadrance of the corrected remainder is strictly below twice the sum of the two displayed bounds. -/
private theorem remaining_estimate {remaining paired correction physical : Gaussian.Basic.Canonical}
    {firstBound secondBound : Rat.Fraction.Rational}
    (first : Data.Gaussian.Norm.Basic.normSq (remaining - (paired - correction)) < firstBound)
    (second : Data.Gaussian.Norm.Basic.normSq (paired - correction + physical) ≤ secondBound) :
    Data.Gaussian.Norm.Basic.normSq (remaining + physical) < 2 * (firstBound + secondBound) := by
  have equal : remaining + physical = (remaining - (paired - correction)) + (paired - correction + physical) := by ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rat.Fraction.Rational) < 2)
      ((Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct first (Data.Gaussian.Norm.Basic.normSq (paired -
        correction + physical))).trans_le
        (Rat.Fraction.Order.Arithmetic.add_le_add_direct (le_refl firstBound) second)))

/-- The corrected remaining triangles satisfy the combined cut and Newton comparison bound.

Both retained request stages have been reached, and the boundary readback is transported from the same acquired surface.
-/
theorem remaining_bound (cached : CutAnnularReadings comparison readings)
    (cutLater : cut.index ≤ stage) (annuliLater : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (cached.remaining.remainingArea + cached.correction) <
      2 * (target + 2 * (cutTarget + correctionAllowance cut)) := by
  have remaining := cached.remaining.remaining_bilinear_accurate readings.surface annuliLater
  have boundary : readings.surface.boundaryArea = readings.paired :=
    (readings.surface.boundary_eq_word readings.word).trans
      (congrArg (fun value => value + readings.word.closedCorrection)
        (readings.integral.contract_eq readings.word.values))
  have transported := (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq
    (cached.remaining.remainingArea - (value - cached.annuli.correction))) boundary).symm.trans_lt remaining
  exact remaining_estimate transported (cached.pairing_bound cutLater)

end

open Purelib.Curves
open Purelib.Data
/-- A shared primitive cache, its cut readings and a certified corrected remaining-triangle estimate.

The cache is acquired at the maximum of the cut and annular comparison stages, preserving both request indices and the
exact dependent readings. -/
@[expose] def Acquisition (comparison :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison prepared
  first second domains)
    (cut : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted domains first second
      cutTarget floor) :=
  (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains (max cut.index
    comparison.index)) ×
  (readings : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings cut cache) ×
  { cached : CutAnnularReadings comparison readings //
    Data.Gaussian.Norm.Basic.normSq (cached.remaining.remainingArea + cached.correction) <
      2 * (target + 2 * (cutTarget + correctionAllowance cut)) }

/-- Construct a complete cut-annulus acquisition at the maximum required stage.

Build one primitive bank per standard differential, derive the cut readings and annular caches from it, and retain the
proved corrected remainder bound. -/
@[expose] def acquire (comparison :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison prepared
  first second domains)
    (cut : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted domains first second
      cutTarget floor) : Acquisition comparison cut :=
  let index := max cut.index comparison.index
  let cache := Vector.DependentVector.ofFn fun row =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build (standardDifferential row) index
      domains
  let readings := Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings.build cut cache
  let cached := build comparison readings
  ⟨cache, readings, cached, cached.remaining_bound (Data.Nat.Order.le_max_left _ _) (Data.Nat.Order.le_max_right _ _)⟩

end CutAnnularReadings
end Purelib.Riemann.Branches.NewtonRequestedCutComparison
