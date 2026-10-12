module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Periods.Pairing
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.CCL.Calculus.WeightedAggregateBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodOffsets
public import Purelib.Riemann.Normalization.NewtonOrderedDeterminantRequest
import Purelib.Approximation.Budget.VanishingSamples
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Budget

open Purelib.Approximation.Rational.Budget

open Purelib.CCL.Calculus

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Periods

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.NewtonOrderedDeterminantRequest

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

public section

/-! Arbitrarily late small samples of the synchronized corrected pairing,
with geometric preparation and all witness offsets retained. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests (BilinearRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity (bilinearResidual)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodOffsets
open Purelib.Riemann.Normalization.NewtonOrderedDeterminantRequest (OrderedDeterminantRequest)
open Purelib.Curves.Hyperelliptic.Periods.Pairing (synchronizedPeriodPairingResidual
  synchronizedPeriodPairingResidual_sample)
open Purelib.Riemann.Periods.PeriodMatrix (sampledMatrix)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {prepared : Prepared paired} {preparation :
    NewtonPreparation base.bank.toBranchCellBank}
  {domains : FaceDomainBank lifted.frames
    base.faces.regulars}
  {first second : Fin genus} {error radius target : Rational} {minimum : Nat}

namespace SynchronizedZeroRequest

/-- The complete original handle-row witness error is paid by the retained bilinear request target. -/
theorem witness_paid (request : BilinearRequests.BilinearRequest prepared domains first second target minimum) :
    (genus : Fraction.Rational) * ((genus : Fraction.Rational) *
      (32 * (request.magnitude + 1) * request.budget.rowTarget)) ≤ target := by
  have nonnegative : 0 ≤ 32 * (request.magnitude + 1) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide)).le
      (add_nonneg request.budget.magnitude_nonnegative (by decide))
  have rowPaid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.budget.row_paid nonnegative).trans
    (WeightedAggregateBudget.weighted_perTerm_le request.budget.handle_positive nonnegative genus)
  have countNonnegative : (0 : Fraction.Rational) ≤ genus := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus)
  have total := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rowPaid countNonnegative) countNonnegative
  have small := total.trans_lt (Aggregate.count_mul_perTerm_lt request.budget.handle_positive genus)
  have targetLe : request.budget.handleTarget ≤ target := by
    rw [request.budget.handleTarget_eq]
    exact Fraction.Order.Field.divide_le_self request.budget.positive.le (by decide +kernel)
  exact small.le.trans targetLe

/-- The original ordered determinant geometry request using one quarter of the complete residual target. -/
@[expose] def SynchronizedGeometry (prepared : PeriodPrograms.Prepared paired) (preparation :
  BranchCellBank.NewtonPreparation base.bank.toBranchCellBank)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (first second : Fin genus)
    (error radius : Fraction.Rational) (minimum : Nat) :=
  NewtonOrderedDeterminantRequest.OrderedDeterminantRequest prepared preparation domains first second (error / 4) radius
    minimum

/-- The original four-offset schedule for every handle row, paying the retained geometry stage. -/
@[expose] def SynchronizedOffsets (geometry :
  SynchronizedGeometry prepared preparation domains
  first second error radius minimum) :=
  SynchronizedPeriodOffsets.Request prepared first second geometry.surface.budget.rowTarget geometry.stage

/-- A retained sufficiently late small sample of the original synchronized period pairing residual. -/
@[expose] def SynchronizedZeroSample (prepared : PeriodPrograms.Prepared paired) (first second : Fin genus) (error :
  Fraction.Rational) (minimum : Nat) :=
  VanishingSamples.ZeroSample (Pairing.synchronizedPeriodPairingResidual prepared.periodData first second) error minimum

end SynchronizedZeroRequest

set_option genInjectivity false in
/-- The retained geometric preparation, complete witness-offset schedule and actual small pairing sample.

The sample uses the exact chosen offset stage and preserves the original period data and external minimum. -/
structure SynchronizedZeroRequest (prepared : PeriodPrograms.Prepared paired) (preparation :
  BranchCellBank.NewtonPreparation base.bank.toBranchCellBank)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (first second : Fin genus)
    (error radius : Fraction.Rational) (minimum : Nat) where
  /-- The original ordered determinant geometry request at the retained quarter tolerance. -/ geometry :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroRequest.SynchronizedGeometry prepared preparation domains
    first second error radius minimum
  /-- The complete witness-offset schedule tied to that actual original geometry request. -/ offsets :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroRequest.SynchronizedOffsets geometry
  /-- The actual sufficiently late small sample of the original synchronized residual. -/ sample :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroRequest.SynchronizedZeroSample prepared first second error
    minimum
  /-- The retained sample stage is exactly the stage selected by the original offset schedule. -/ stage_eq :
    sample.stage = offsets.index

constructive_injectivity SynchronizedZeroRequest

namespace SynchronizedZeroRequest

/-- Read the original synchronized pairing at the retained offset stage and combine its witness and geometric error
bounds. -/
@[expose] def makeSample (geometry :
  SynchronizedGeometry prepared preparation domains
  first second error radius minimum)
    (offsets : SynchronizedOffsets geometry) :
      SynchronizedZeroSample prepared first second
      error minimum := by
  let stage := offsets.index
  let residual := BilinearIdentity.bilinearResidual prepared geometry.surface.surface.left.value
    geometry.surface.surface.right.value
  let value := FiniteSum.Fin.sumFin (fun cycle : Fin genus =>
    PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage first cycle *
      PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage second cycle -
    PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage first cycle *
      PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage second cycle)
  have comparison := geometry.surface.synchronized_determinant_close stage
    (geometry.surface_le.trans offsets.minimum_le) geometry.surface.budget.rowTarget
    geometry.surface.budget.row_positive.le geometry.surface.budget.row_le_one
    (offsets.firstA le_rfl) (offsets.secondA le_rfl) (offsets.firstB le_rfl) (offsets.secondB le_rfl)
  have quarterEq (amount : Fraction.Rational) : 2 * (amount / 4 + amount / 4) = amount :=
    (show 2 * (amount / 4 + amount / 4) = amount / 4 * 4 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  have comparisonSmall : Data.Gaussian.Norm.Basic.normSq (value - residual) < error / 4 := comparison.trans_le
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      (witness_paid geometry.surface) (le_refl _))
      (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (quarterEq (error / 4)))
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two (value - residual) residual).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      ((Fraction.Order.Arithmetic.add_lt_add_right_direct comparisonSmall _).trans
        (Fraction.Order.Arithmetic.add_lt_add_left_direct geometry.accurate _)))
  have equal : value - residual + residual = value := by ring1
  refine ⟨stage, geometry.minimum_le.trans offsets.minimum_le, value, ?_, ?_⟩
  · exact (Pairing.synchronizedPeriodPairingResidual_sample prepared.periodData first second stage).symm
  · exact ((congrArg Data.Gaussian.Norm.Basic.normSq equal).symm.trans_lt estimate).trans_eq (quarterEq error)

/-- Retain the original geometry request, prepare its complete witness offsets and cache the corresponding small
residual sample. -/
@[expose] def ofGeometry (geometry :
  SynchronizedGeometry prepared preparation domains
  first second error radius minimum) :
    SynchronizedZeroRequest prepared preparation
      domains first second error radius minimum :=
  let offsets := SynchronizedPeriodOffsets.Request.build prepared first second geometry.surface.budget.rowTarget
    geometry.surface.budget.row_positive geometry.stage
  ⟨geometry, offsets,
    makeSample geometry
    offsets, rfl⟩

/-- Prepare the original geometry at a quarter tolerance and retain the paid offset schedule and actual late small
pairing sample. -/
@[expose] def build (prepared : PeriodPrograms.Prepared paired) (preparation : BranchCellBank.NewtonPreparation
  base.bank.toBranchCellBank)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (first second : Fin genus)
    (error radius : Fraction.Rational) (positive : 0 < error) (radiusPositive : 0 < radius) (minimum : Nat) :
    SynchronizedZeroRequest prepared preparation
      domains first second error radius minimum :=
  ofGeometry
    (OrderedDeterminantRequest.build prepared preparation domains first second (error / 4) radius
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)) radiusPositive minimum)

end SynchronizedZeroRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
