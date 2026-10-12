module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveTotals
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! The existing area request also pays the endpoint error needed when
concatenating parents. No additional sampling or numerical request is needed. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointBudget

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index : Nat} {box : Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility

variable {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {target :
  Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

variable {minimum : Nat} {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers
  minimum}

/-- A nonnegative factor below the retained weight times its weighted tolerance is paid by the target. -/
private theorem weighted_tolerance {target weight factor tolerance : Normalization.InverseRootPolynomial.Coordinate}
    (targetNonnegative : 0 ≤ target) (factorNonnegative : 0 ≤ factor)
    (factorLe : factor ≤ weight)
    (small : tolerance ≤ Purelib.Approximation.Rational.Budget.Weighted.allowance target weight) : factor * tolerance ≤
      target :=
  open Purelib.Approximation in (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small
    factorNonnegative).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct factorLe
      (Fraction.Order.Field.div_nonneg_direct targetNonnegative
        (add_nonneg (factorNonnegative.trans factorLe) (by decide)))).trans
      (Rational.Budget.Weighted.mul_allowance_le targetNonnegative (factorNonnegative.trans factorLe)))

namespace BasisPreparedAreaRequest

variable {allowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
    {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

/-- The same allocation controls the endpoint total as well as the full area. -/
theorem endpoint_paid (budget : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest.BasisPreparedAreaRequest
  regular common allowance coefficientTarget floor) :
    2 * (budget.sourceTarget + (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
      budget.request.comparison.tolerance) ≤ allowance^2 := open Purelib.Approximation in by
  let slope := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers
  have slopeNonnegative : 0 ≤ slope :=
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative covers
  have sourceWeight : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 32 * (slope + 1) :=
    (show (1 : Normalization.InverseRootPolynomial.Coordinate) = 1 + 0 by ring1).trans_le
      ((Fraction.Order.Arithmetic.add_le_add_direct le_rfl (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by
            decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 32) slopeNonnegative)
        (by decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 31))).trans_eq (by ring1))
  have sourceSmall : budget.sourceTarget ≤ Rational.Budget.Weighted.allowance (budget.half^2) (32 * (slope + 1)) := by
    rw [budget.sourceTarget_eq]
    exact Fraction.Order.Basic.min_le_right _ _
  have sourcePaid := Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointBudget.weighted_tolerance
    (Fraction.Order.Arithmetic.sq_nonneg_direct budget.half) (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1)
    sourceWeight sourceSmall
  rw [Fraction.Field.one_mul] at sourcePaid
  let comparison := budget.request.comparison
  let n : Coordinate := common.intervals.length
  have nNonnegative : 0 ≤ n := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have squareNonnegative : 0 ≤ n^2 := Fraction.Order.Arithmetic.sq_nonneg_direct n
  have coefficient : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2 * (144 * slope + 160) :=
    (show (1 : Normalization.InverseRootPolynomial.Coordinate) = 1 + 0 by ring1).trans_le
      ((Fraction.Order.Arithmetic.add_le_add_direct le_rfl (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by
            decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 288) slopeNonnegative)
        (by decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 319))).trans_eq (by ring1))
  have first := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficient squareNonnegative
  rw [Fraction.Field.mul_one_direct] at first
  have extra : 0 ≤ 64 * n^4 * (slope + 1) := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.pow_nonneg_direct
      nNonnegative 4)) (add_nonneg slopeNonnegative (by decide))
  have weightLe : n^2 ≤ comparison.weight := by
    rw [comparison.weight_eq, comparison.slope_eq]
    exact first.trans ((show n^2 * (2 * (144 * slope + 160)) = 2 * n^2 * (144 * slope + 160) by ring1).trans_le
      (le_add_of_nonneg_right extra))
  have comparisonSmall : comparison.tolerance ≤ Rational.Budget.Weighted.allowance (budget.half^2) comparison.weight :=
    by
    rw [comparison.tolerance_eq]
    exact Fraction.Order.Basic.min_le_right _ _
  have comparisonPaid := Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointBudget.weighted_tolerance
    (Fraction.Order.Arithmetic.sq_nonneg_direct budget.half) squareNonnegative weightLe
    comparisonSmall
  have combined := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct sourcePaid comparisonPaid) (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  exact combined.trans_eq (calc
    2 * (budget.half^2 + budget.half^2) = (budget.half * 2)^2 := by ring1
    _ = allowance^2 := by rw [budget.half_eq, Fraction.Field.div_mul_cancel_of_ne allowance 2 (by decide)])

/-- The original prepared area allocation also bounds the endpoint difference between the same cached integral and
pullback paths. -/
theorem total_bounded (budget : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest.BasisPreparedAreaRequest
  regular common allowance coefficientTarget floor)
    (acquired : budget.request.Acquisition polynomials originals cells coefficients depth)
    {pairs :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
      acquired}
    (weighted :
      PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
      pairs) :
    Data.Gaussian.Norm.Basic.normSq (weighted.integral.total - acquired.area.pullback.total) ≤ allowance^2 *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Algebra in by
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  exact
    (CommonPrimitiveTotals.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted.integral_pullback_total_bound
    weighted).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointBudget.BasisPreparedAreaRequest.endpoint_paid budget)
      nonnegative)

end BasisPreparedAreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointBudget
