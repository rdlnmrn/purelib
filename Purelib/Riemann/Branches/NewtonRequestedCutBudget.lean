module
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.SewingTree
public import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Tactic.Ring

public section

/-! Pay the complete annular multiplicity before acquiring cut readings.
The hole count is read from the actual requested Newton grid. -/
namespace Purelib.Riemann.Branches.NewtonRequestedCutBudget

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Riemann.Branches.NewtonRequestedCutComparison (CutAnnularReadings)

open Purelib.Approximation in
open Purelib.Data in
/-- The finite per-term allowance is at most its positive total target. -/
private theorem perTerm_le {value : Rat.Fraction.Rational} (positive : 0 < value) (count : Nat) :
    Rational.Budget.Aggregate.perTerm value count ≤ value := by
  have countNonnegative : (0 : Rat.Fraction.Rational) ≤ count := Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    count)
  have extra : (0 : Rat.Fraction.Rational) ≤ 2 * (count : Rat.Fraction.Rational)^2 + 4 * count + 1 :=
    add_nonneg (add_nonneg
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) countNonnegative)) (by decide)
  have denominatorGe : (1 : Rat.Fraction.Rational) ≤ 2 * ((count : Rat.Fraction.Rational) + 1)^2 :=
    (le_add_of_nonneg_right extra).trans_eq (by ring1)
  rw [Rational.Budget.Aggregate.perTerm, Rational.Budget.Aggregate.countCoordinate_eq]
  apply (Rat.Fraction.Order.Field.div_le_iff_pos ((by decide : (0 : Rat.Fraction.Rational) < 1).trans_le
    denominatorGe)).mpr
  exact (show value = value * 1 by ring1).le.trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct denominatorGe positive.le)

open Purelib.Topology in
open Purelib.Approximation in
open Purelib.Data in
/-- A bilinear sewing request's weight times error is at most its target. -/
private theorem sewing_error_le {vertexCount faceCount : Nat}
    {faces : Fin faceCount → Polygon.Stokes.OrientedTriangle vertexCount}
    {patch : Surface.Sewing.SewingTree.SewnPatch faces} {magnitude target : Rat.Fraction.Rational}
    (budget : Surface.Sewing.Bilinear.Requests.AreaRequest patch magnitude target) :
    budget.weight * budget.error ≤ target := by
  have errorLe : budget.error ≤ Rational.Budget.Weighted.allowance target budget.weight := by
    rw [budget.error_eq]
    exact (Fraction.Order.Basic.min_le_right _ _).trans (perTerm_le
      (Rational.Budget.Weighted.allowance_positive budget.positive budget.weight_nonnegative) _)
  exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe budget.weight_nonnegative).trans
    (Rational.Budget.Weighted.mul_allowance_le budget.positive.le budget.weight_nonnegative)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational}
  {request : Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest
    preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}
  {first second : Fin genus} {cutTarget : Purelib.Data.Rat.Fraction.Rational} {floor : Nat}

namespace CutAnnularReadings

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- The cut correction allowance is at most four times squared hole count times cut target.

The count comes from the retained requested grid, independently of later triangle and subdivision counts. -/
theorem correctionAllowance_le (cut : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted
  domains first second cutTarget floor) :
    Branches.NewtonRequestedCutComparison.CutAnnularReadings.correctionAllowance cut ≤ 4 *
      (request.single.grid.faces.holes.length : Rat.Fraction.Rational)^2 * cutTarget := by
  have bounded := sewing_error_le cut.sewing.budget
  have countNonnegative : (0 : Rat.Fraction.Rational) ≤ request.single.grid.faces.holes.length :=
    Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have scaled := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
          (show (0 : Rat.Fraction.Rational) ≤ 8 by decide)) (show (0 : Rat.Fraction.Rational) ≤ 8 by decide))
            countNonnegative) countNonnegative
  apply scaled.trans_eq
  have quarter : cutTarget / 4 * 4 = cutTarget := Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have sixteenth : (cutTarget / 4) / 4 * 4 = cutTarget / 4 := Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  calc
    _ = 4 * (request.single.grid.faces.holes.length : Rat.Fraction.Rational)^2 * (((cutTarget / 4) / 4 * 4) * 4) := by
      ring1
    _ = _ := by rw [sixteenth, quarter]

open Purelib.Curves in
open Purelib.Approximation in
open Purelib.Data in
/-- The product of squared family count and squared original outer-occurrence count. -/
@[expose] def outerWeight (request :
  Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation target
  radius) : Rat.Fraction.Rational :=
  (Rational.Budget.Aggregate.countCoordinate request.count)^2 *
    (Rational.Budget.Aggregate.countCoordinate request.single.count)^2

open Purelib.Curves
open Purelib.Data
/-- The retained outer-occurrence weight is nonnegative. -/
theorem outerWeight_nonnegative (request :
  Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation target
  radius) : 0 ≤ outerWeight request :=
  Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- Charge the cut sewing weight and error by the retained outer-occurrence weight. -/
@[expose] def outerAllowance (cut : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted
  domains first second cutTarget floor) : Rat.Fraction.Rational :=
  outerWeight request * (cut.sewing.budget.weight * cut.sewing.budget.error)

/-- The outer allowance is bounded by outer-occurrence weight times cut target. -/
theorem outerAllowance_le (cut : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted domains
  first second cutTarget floor) :
    outerAllowance cut ≤ outerWeight request * cutTarget := by
  have quarter {value : Rat.Fraction.Rational} (positive : 0 < value) : value / 4 ≤ value := by
    apply (Rat.Fraction.Order.Field.div_le_iff_pos (by decide)).mpr
    exact (show value = value * 1 by ring1).le.trans
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : Rat.Fraction.Rational) ≤ 4)
        positive.le)
  have small := (sewing_error_le cut.sewing.budget).trans
    ((quarter (Rat.Fraction.Order.Field.div_pos_direct cut.positive (by decide))).trans (quarter cut.positive))
  exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (outerWeight_nonnegative request)

end CutAnnularReadings

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
set_option genInjectivity false in
/-- A retained cut request whose local correction and outer-occurrence allowances are paid.

The positive cut target is allocated against the original total target before sampling. Both guarantees concern the same
retained grid, domain bank and cut request. -/
structure PaidCutRequest (lifted : LiftedPuncturedGrid request.single.grid.punctured)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
      request.single.grid.faces.regulars)
    (first second : Fin genus) (target : Rat.Fraction.Rational) (floor : Nat) where
  /-- The allocated rational tolerance of the retained cut request. -/ cutTarget : Rat.Fraction.Rational
  /-- The allocated cut tolerance is strictly positive. -/ positive : 0 < cutTarget
  /-- The retained cut request at the allocated tolerance and original stage floor. -/ cut :
    Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted domains first second cutTarget floor
  /-- Twice the sum of cut tolerance and its annular correction allowance is within the total target. -/ paid : 2 *
    (cutTarget + Branches.NewtonRequestedCutComparison.CutAnnularReadings.correctionAllowance cut) ≤ target
  /-- The original outer-occurrence allowance is within the total target. -/ outer_paid :
    CutAnnularReadings.outerAllowance cut ≤ target

constructive_injectivity PaidCutRequest

namespace PaidCutRequest

variable {paidTarget : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Curves in
open Purelib.Approximation in
open Purelib.Data in
/-- Allocate one cut tolerance paying both correction and outer-occurrence bounds.

The weight combines the actual hole count with the original outer-occurrence weight. Build the retained cut request once
using the same domain bank, cuts and floor. -/
@[expose] def build (lifted : LiftedPuncturedGrid request.single.grid.punctured)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
      request.single.grid.faces.regulars)
    (cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains)
    (first second : Fin genus) (target : Rat.Fraction.Rational) (positive : 0 < target) (floor : Nat) :
    PaidCutRequest lifted domains first second target floor := by
  let count := Rational.Budget.Aggregate.countCoordinate request.single.grid.faces.holes.length
  let localWeight := 2 + 8 * count^2
  let outerWeight := CutAnnularReadings.outerWeight request
  let weight := localWeight + outerWeight
  have localNonnegative : 0 ≤ localWeight := add_nonneg (by decide)
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have outerNonnegative : 0 ≤ outerWeight := CutAnnularReadings.outerWeight_nonnegative request
  have weightNonnegative : 0 ≤ weight := add_nonneg localNonnegative outerNonnegative
  let cutTarget := Rational.Budget.Weighted.allowance target weight
  have cutPositive := Rational.Budget.Weighted.allowance_positive positive weightNonnegative
  let cut := Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.build lifted domains cuts first
    second cutTarget cutPositive floor
  have totalPaid : weight * cutTarget ≤ target :=
    Rational.Budget.Weighted.mul_allowance_le positive.le weightNonnegative
  refine ⟨cutTarget, cutPositive, cut, ?_, ?_⟩
  · have bounded := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rat.Fraction.Order.Arithmetic.add_le_add_direct (le_refl cutTarget) (CutAnnularReadings.correctionAllowance_le
        cut))
      (show (0 : Rat.Fraction.Rational) ≤ 2 by decide)
    have localPaid : localWeight * cutTarget ≤ target :=
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_right outerNonnegative) cutPositive.le).trans totalPaid
    apply bounded.trans
    apply le_trans (le_of_eq ?_) localPaid
    dsimp only [localWeight, count, -eq_self, -iff_self]
    rw [Rational.Budget.Aggregate.countCoordinate_eq]
    ring1
  · exact (CutAnnularReadings.outerAllowance_le cut).trans
      ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_left localNonnegative) cutPositive.le).trans totalPaid)

variable {excision : Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision request.single.grid
  lifted}
  {prepared :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision} {comparison :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
    prepared first second domains}
  {stage : Nat} {cache : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
    domains stage}

open Purelib.Riemann in
open Purelib.Data in
/-- The allocated cut tolerance is no greater than the paid total target. -/
theorem cutTarget_le (paid : PaidCutRequest lifted domains first second paidTarget floor) : paid.cutTarget ≤ paidTarget
  := by
  have countNonnegative := Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    request.single.grid.faces.holes.length)
  have scalarNonnegative := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    paid.cut.sewing.budget.weight_nonnegative paid.cut.sewing.budget.error_positive.le
  have correctionNonnegative : 0 ≤ Branches.NewtonRequestedCutComparison.CutAnnularReadings.correctionAllowance paid.cut
    :=
    Rat.Fraction.Order.Arithmetic.mul_nonneg_direct countNonnegative
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct countNonnegative
        (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) scalarNonnegative)))
  have sumNonnegative := add_nonneg paid.positive.le correctionNonnegative
  have double := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by decide : (1 : Rat.Fraction.Rational) ≤ 2) sumNonnegative
  rw [one_mul] at double
  exact (le_add_of_nonneg_right correctionNonnegative).trans (double.trans paid.paid)

open Purelib.Curves
open Purelib.Data
/-- The paid request bounds the cached paired cut comparison at every sufficiently late stage. -/
theorem pairing_bound (paid : PaidCutRequest lifted domains first second paidTarget floor)
    {readings : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings paid.cut cache}
    (cached : CutAnnularReadings comparison readings) (later : paid.cut.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.paired - cached.annuli.correction + cached.correction) ≤ paidTarget :=
  (cached.pairing_bound later).trans paid.paid

/-- The paid cut and annular requests bound the cached corrected remaining area.

The numerical stage respects both request indices; the strict bound retains the original annular target and the paid
total cut target. -/
theorem remaining_bound (paid : PaidCutRequest lifted domains first second paidTarget floor)
    {readings : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings paid.cut cache}
    (cached : CutAnnularReadings comparison readings)
    (cutLater : paid.cut.index ≤ stage) (annuliLater : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (cached.remaining.remainingArea + cached.correction) < 2 * (target + paidTarget)
      :=
  (cached.remaining_bound cutLater annuliLater).trans_le
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rat.Fraction.Order.Arithmetic.add_le_add_direct (le_refl target) paid.paid) (by decide))

end PaidCutRequest
end Purelib.Riemann.Branches.NewtonRequestedCutBudget
