module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.Newton.TerminalExteriorBound
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Riemann

public section

/-! Choose the exterior accuracy after the Newton grid is fixed. The
ordered-factor magnitude and allowance are cached with exact specifications. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
  {target radius : Fraction.Rational} {i j : Fin genus} {floor : Nat}

set_option genInjectivity false in
/-- A cached exterior-product allowance for the retained ordered factor and fixed Newton boundary.

The original two differential magnitude banks determine the weight; the allocated positive allowance pays the complete
doubled exterior estimate without exceeding the target. -/
structure TerminalExteriorBudget (paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered)
    (boundary : RootContinuation.NewtonRequestedBoundary.BoundaryPreparation preparation i j target radius floor) where
  /-- The retained first-differential magnitude bank on the fixed boundary domains. -/ first :
    Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank boundary.domains
    (Periods.PeriodMatrix.standardDifferential i)
  /-- The retained second-differential magnitude bank on the same boundary domains. -/ second :
    Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank boundary.domains
    (Periods.PeriodMatrix.standardDifferential j)
  /-- The cached exterior-product magnitude coefficient. -/ weight : Fraction.Rational
  /-- The weight is four times the maximum of the two original ordered-factor bounds. -/ weight_eq : weight = 4 * max
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) boundary.fine.family.single.grid.shrunk.included first)
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) boundary.fine.family.single.grid.shrunk.included second)
  /-- The common allocated exterior and endpoint accuracy. -/ allowance : Fraction.Rational
  /-- The allowance is the smaller of the target and one quarter of its weighted allocation. -/ allowance_eq : allowance
    = min target (Rational.Budget.Weighted.allowance target weight / 4)
  /-- The allocated exterior accuracy is strictly positive. -/ positive : 0 < allowance
  /-- The allocated accuracy does not exceed the original target. -/ allowance_le : allowance ≤ target
  /-- The cached weight times the doubled pair of allowances is at most the target. -/ paid : weight * (2 * (allowance +
    allowance)) ≤ target

constructive_injectivity TerminalExteriorBudget

namespace TerminalExteriorBudget

variable {boundary : RootContinuation.NewtonRequestedBoundary.BoundaryPreparation preparation i j target radius floor}

/-- Construct both original magnitude banks and allocate a positive accuracy paying their full exterior-product weight.

The retained boundary supplies target positivity, and the cached weight and allowance keep exact specification
equalities. -/
@[expose] def build (paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered) (boundary :
  RootContinuation.NewtonRequestedBoundary.BoundaryPreparation preparation i j target radius floor) :
    TerminalExteriorBudget paired boundary := by
  have positive : 0 < target := (Fraction.Order.Arithmetic.mul_pos_direct boundary.fine.positive (by
      decide : (0 : Fraction.Rational) < 4)).trans_eq
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  let first := Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank.build boundary.domains
    (Periods.PeriodMatrix.standardDifferential i)
  let second := Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank.build boundary.domains
    (Periods.PeriodMatrix.standardDifferential j)
  let weight := 4 * max
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) boundary.fine.family.single.grid.shrunk.included first)
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) boundary.fine.family.single.grid.shrunk.included second)
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    ((Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound_nonnegative
      (paired := paired)
      boundary.fine.family.single.grid.shrunk.included first).trans (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _
        _))
  let allowance := min target (Rational.Budget.Weighted.allowance target weight / 4)
  have allowancePositive : 0 < allowance := Purelib.Data.Rat.Fraction.Order.Basic.lt_min positive
    (Fraction.Order.Field.div_pos_direct (Rational.Budget.Weighted.allowance_positive positive weightNonnegative) (by
      decide))
  refine ⟨first, second, weight, rfl, allowance, rfl, allowancePositive,
    Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _, ?_⟩
  have small := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right target (Rational.Budget.Weighted.allowance target weight / 4))
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have small : 2 * (allowance + allowance) ≤ Rational.Budget.Weighted.allowance target weight :=
    (show 2 * (allowance + allowance) = allowance * 4 by ring1).trans_le
      (small.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small weightNonnegative).trans
    (Rational.Budget.Weighted.mul_allowance_le positive.le weightNonnegative)

end TerminalExteriorBudget
end Purelib.Curves.Hyperelliptic.Meshes.Newton
