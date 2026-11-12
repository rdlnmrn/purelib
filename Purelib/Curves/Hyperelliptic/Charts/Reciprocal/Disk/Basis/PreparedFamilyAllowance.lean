module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Budget.Trace.Family
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationScale
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Riemann

public section

/-! Select one local allowance paying the trace loss and the complete
prepared-integral concatenation error before acquiring any samples. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance

open Basis.CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {bounds :
    ReciprocalPaddedInverse.UniformBounds regular.padded}

/-- The retained restored-total factor is nonnegative for every allowance. -/
private theorem totalBound_nonnegative (basis : ReciprocalPaddedBasisBounds.BasisBounds
  bounds) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    0 ≤
      Sample.PreparedComparison.restoredTotalBound
      (basis := basis) (allowance := allowance) := by
  unfold
    Sample.PreparedComparison.restoredTotalBound
  exact Arithmetic.mul_nonneg_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    (add_nonneg (add_nonneg (Arithmetic.sq_nonneg_direct _) (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 12))
      (Arithmetic.mul_nonneg_direct (by
          decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 64) basis.coefficient_nonnegative))

/-- The original prepared-concatenation squared-error factor is nonnegative. -/
private theorem scale_nonnegative (basis : ReciprocalPaddedBasisBounds.BasisBounds
  bounds) (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    0 ≤ CommonPreparedConcatenation.Samples.concatenationScale (basis :=
      basis) (allowance := allowance) count := by
  unfold CommonPreparedConcatenation.Samples.concatenationScale
  exact Arithmetic.mul_nonneg_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    (add_nonneg
      (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct _)
        (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
        Normalization.InverseRootPolynomial.Coordinate) ≤ 82) (Arithmetic.sq_nonneg_direct _)))
      (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤
          16) (Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))
          4))
        (Arithmetic.sq_nonneg_direct _))
          (totalBound_nonnegative basis allowance)))

/-- The prepared family's complete concatenation factor is nonnegative. -/
theorem scale_nonnegative_for_family (basis : ReciprocalPaddedBasisBounds.BasisBounds
  bounds) (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    0 ≤ CommonPreparedConcatenation.Samples.concatenationScale (basis :=
      basis) (allowance := allowance) count := by
  unfold CommonPreparedConcatenation.Samples.concatenationScale
  exact Arithmetic.mul_nonneg_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    (add_nonneg
      (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct _)
        (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
        Normalization.InverseRootPolynomial.Coordinate) ≤ 82) (Arithmetic.sq_nonneg_direct _)))
      (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤
          16) (Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))
          4))
        (Arithmetic.sq_nonneg_direct _))
          (totalBound_nonnegative basis allowance)))

/-- For an allowance between zero and one, the concatenation factor is bounded by its unit value times the squared
allowance. -/
private theorem scale_quadratic (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
  (count : Nat)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ allowance) (small : allowance ≤ 1) :
    CommonPreparedConcatenation.Samples.concatenationScale (basis := basis)
      (allowance := allowance) count ≤
      CommonPreparedConcatenation.Samples.concatenationScale (basis := basis)
        (allowance := 1) count * allowance^2 := by
  have square := Arithmetic.pow_le_pow_direct (Arithmetic.mul_nonneg_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) nonnegative)
    (Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)) 2
  have totals :
    Sample.PreparedComparison.restoredTotalBound
    (basis := basis) (allowance := allowance) ≤
    Sample.PreparedComparison.restoredTotalBound
    (basis := basis) (allowance := 1) := by
    unfold
      Sample.PreparedComparison.restoredTotalBound
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct
      (Arithmetic.add_le_add_direct square le_rfl) le_rfl)
      (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have factor : 0 ≤ 16 * (count : Normalization.InverseRootPolynomial.Coordinate)^4 * (4 * allowance)^2 :=
    Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
      (Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
        (Arithmetic.sq_nonneg_direct _)
  calc
    _ ≤ 2 * ((count : Normalization.InverseRootPolynomial.Coordinate)^2 * (82 * (4 * allowance)^2) +
        16 * (count : Normalization.InverseRootPolynomial.Coordinate)^4 * (4 * allowance)^2 *

            Sample.PreparedComparison.restoredTotalBound
          (basis := basis) (allowance := 1)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct le_rfl
        (Arithmetic.mul_le_mul_of_nonneg_left_direct totals factor))
        (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    _ = _ := by
      unfold CommonPreparedConcatenation.Samples.concatenationScale
      ring1

/-- The original initial-value ribbon factor is nonnegative. -/
private theorem ribbonScale_nonnegative (basis : ReciprocalPaddedBasisBounds.BasisBounds
  bounds)
    (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    0 ≤ 4 * (2 + 8 * basis.coefficient) * (count : Normalization.InverseRootPolynomial.Coordinate)^2 * (4 * allowance)^2
      :=
  Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)
      (add_nonneg (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
        (Arithmetic.mul_nonneg_direct (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 8) basis.coefficient_nonnegative)))
    (Arithmetic.sq_nonneg_direct _)) (Arithmetic.sq_nonneg_direct _)

/-- The complete concatenation area factor is bounded by its retained trace-comparison factor. -/
private theorem area_le_trace (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    CommonPreparedConcatenation.Samples.concatenationScale (basis := basis)
      (allowance := allowance) count ≤
      CommonPreparedConcatenation.Samples.traceComparisonScale (basis :=
        basis) (allowance := allowance) count := by
  apply Arithmetic.le_of_sub_nonneg_direct
  exact (add_nonneg (scale_nonnegative basis count
    allowance)
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
      (ribbonScale_nonnegative basis count
      allowance))).trans_eq
      (by
        unfold CommonPreparedConcatenation.Samples.traceComparisonScale
        ring1)

/-- The prepared family's concatenation factor does not exceed its trace-comparison factor. -/
theorem area_le_trace_for_family (basis : ReciprocalPaddedBasisBounds.BasisBounds
  bounds)
    (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    CommonPreparedConcatenation.Samples.concatenationScale (basis := basis)
      (allowance := allowance) count ≤
      CommonPreparedConcatenation.Samples.traceComparisonScale (basis :=
        basis) (allowance := allowance) count := by
  apply Arithmetic.le_of_sub_nonneg_direct
  exact (add_nonneg (scale_nonnegative_for_family
    basis count allowance)
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
      (ribbonScale_nonnegative basis count
      allowance))).trans_eq
      (by
        unfold CommonPreparedConcatenation.Samples.traceComparisonScale
        ring1)

/-- For a nonnegative allowance at most one, the trace-comparison factor is bounded by its unit value times the squared
allowance. -/
private theorem trace_scale_quadratic (basis : ReciprocalPaddedBasisBounds.BasisBounds
  bounds) (count : Nat)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ allowance) (small : allowance ≤ 1) :
    CommonPreparedConcatenation.Samples.traceComparisonScale (basis := basis)
      (allowance := allowance) count ≤
      CommonPreparedConcatenation.Samples.traceComparisonScale (basis :=
        basis) (allowance := 1) count * allowance^2 := by
  calc
    _ ≤ 2 * (CommonPreparedConcatenation.Samples.concatenationScale (basis :=
      basis) (allowance := 1) count * allowance^2 +
        4 * (2 + 8 * basis.coefficient) * (count : Normalization.InverseRootPolynomial.Coordinate)^2 * (4 *
          allowance)^2) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct
        (scale_quadratic basis count nonnegative
        small) le_rfl)
        (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    _ = _ := by
      unfold CommonPreparedConcatenation.Samples.traceComparisonScale
      ring1

/-- The prepared family trace factor scales quadratically below the unit allowance. -/
theorem trace_scale_quadratic_for_family (basis :
  ReciprocalPaddedBasisBounds.BasisBounds bounds) (count : Nat)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ allowance) (small : allowance ≤ 1) :
    CommonPreparedConcatenation.Samples.traceComparisonScale (basis := basis)
      (allowance := allowance) count ≤
      CommonPreparedConcatenation.Samples.traceComparisonScale (basis :=
        basis) (allowance := 1) count * allowance^2 := by
  calc
    _ ≤ 2 * (CommonPreparedConcatenation.Samples.concatenationScale (basis :=
      basis) (allowance := 1) count * allowance^2 +
        4 * (2 + 8 * basis.coefficient) * (count : Normalization.InverseRootPolynomial.Coordinate)^2 * (4 *
          allowance)^2) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct
        (scale_quadratic basis count nonnegative
        small) le_rfl)
        (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    _ = _ := by
      unfold CommonPreparedConcatenation.Samples.traceComparisonScale
      ring1

set_option genInjectivity false in
/-- One pre-acquisition allowance paying the complete prepared family, return and source-trace errors.

The allocation retains the exact parent count, positive target and source slope. Its four certificates bound the
original factors by the same squared target. -/
structure BasisPreparedFamilyAllowance (basis : ReciprocalPaddedBasisBounds.BasisBounds
  bounds)
    (parentCount : Nat) (target slope : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The retained family allocation with its original parent count and target. -/ allocation :
    Budget.Trace.Family.BasisFamilyAllowance parentCount target
  /-- The complete prepared concatenation factor is paid by the squared target. -/ paid :
    CommonPreparedConcatenation.Samples.concatenationScale (basis := basis)
    (allowance := allocation.allowance) parentCount ≤ target^2
  /-- The complete prepared trace-comparison factor is paid by the squared target. -/ trace_paid :
    CommonPreparedConcatenation.Samples.traceComparisonScale (basis := basis)
    (allowance := allocation.allowance) parentCount ≤ target^2
  /-- The actual parent-return factor is paid by the squared target. -/ return_paid :
    CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale
    (basis := basis) (allowance := allocation.allowance) ≤ target^2
  /-- The complete source-restoration trace factor is paid at the same allocation. -/ source_trace_paid :
    SourceRestorationTrace.Samples.SourceRestoration.traceScale
    (basis := basis) (allowance := allocation.allowance) parentCount slope ≤ target^2

constructive_injectivity BasisPreparedFamilyAllowance

namespace BasisPreparedFamilyAllowance

/-- Allocate one positive parent allowance paying all original concatenation, trace, return and source-restoration
factors.

A positive target and nonnegative source slope give nonnegative retained unit weights; their sum determines the common
weighted ceiling before samples are acquired. -/
@[expose] def build (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (parentCount : Nat) (target slope : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target)
      (slopeNonnegative : 0 ≤ slope) :
    BasisPreparedFamilyAllowance basis parentCount
      target slope := by
  let traceWeight := CommonPreparedConcatenation.Samples.traceComparisonScale
    (basis := basis) (allowance := 1) parentCount
  let returnWeight :=
    CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale
    (basis := basis) (allowance := 1)
  have traceNonnegative : 0 ≤ traceWeight :=
    (scale_nonnegative_for_family basis parentCount
      1).trans (area_le_trace_for_family basis
      parentCount 1)
  have returnNonnegative : 0 ≤ returnWeight :=
    Arithmetic.mul_nonneg_direct (add_nonneg (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 180)
      (Arithmetic.mul_nonneg_direct (by
          decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 64) basis.coefficient_nonnegative))
        (Arithmetic.sq_nonneg_direct _)
  let sourceWeight :=
    SourceRestorationTrace.Samples.SourceRestoration.traceScale (basis :=
    basis) (allowance := 1) parentCount slope
  have sourceNonnegative : 0 ≤ sourceWeight :=
    SourceRestorationScale.traceScale_nonnegative basis parentCount 1
      slopeNonnegative
  let weight := traceWeight + returnWeight + sourceWeight
  have weightNonnegative : 0 ≤ weight := add_nonneg (add_nonneg traceNonnegative returnNonnegative) sourceNonnegative
  have traceLe : traceWeight ≤ weight := (le_add_of_nonneg_right returnNonnegative).trans (le_add_of_nonneg_right
    sourceNonnegative)
  have returnLe : returnWeight ≤ weight := (le_add_of_nonneg_left traceNonnegative).trans (le_add_of_nonneg_right
    sourceNonnegative)
  have sourceLe : sourceWeight ≤ weight := le_add_of_nonneg_left (add_nonneg traceNonnegative returnNonnegative)
  let ceiling := min 1 (Rational.Budget.Weighted.allowance (target^2) weight)
  have ceilingPositive : 0 < ceiling := Basic.lt_min (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 1)
    (Rational.Budget.Weighted.allowance_positive (Arithmetic.pow_pos_direct positive 2)
      weightNonnegative)
  let allocation := Budget.Trace.Family.BasisFamilyAllowance.build parentCount target ceiling positive ceilingPositive
  have ceilingLe : allocation.allowance ≤ ceiling := allocation.allowance_le_ceiling
  have small : allocation.allowance ≤ 1 := ceilingLe.trans (Basic.min_le_left _ _)
  have square : allocation.allowance^2 ≤ allocation.allowance :=
    (show allocation.allowance^2 = allocation.allowance * allocation.allowance by ring1).trans_le
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct small allocation.positive.le).trans_eq
        (Fraction.Field.mul_one_direct _))
  have linear := (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (square.trans (ceilingLe.trans (Basic.min_le_right _ _))) weightNonnegative).trans
      (Rational.Budget.Weighted.mul_allowance_le (Arithmetic.sq_nonneg_direct target) weightNonnegative)
  have paid := (trace_scale_quadratic_for_family
    basis parentCount allocation.positive.le small).trans
    ((Arithmetic.mul_le_mul_of_nonneg_right_direct traceLe (Arithmetic.sq_nonneg_direct
      _)).trans linear)
  have returned :
    CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale
    (basis := basis) (allowance := allocation.allowance) ≤ target^2 :=
    (show
      CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale
      (basis := basis) (allowance := allocation.allowance) = returnWeight * allocation.allowance^2 by
      dsimp only [returnWeight,
        CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale];
        ring1).trans_le
        ((Arithmetic.mul_le_mul_of_nonneg_right_direct returnLe
          (Arithmetic.sq_nonneg_direct _)).trans linear)
  have sourcePaid := (SourceRestorationScale.traceScale_quadratic basis
    parentCount slope allocation.positive.le small).trans
    ((Arithmetic.mul_le_mul_of_nonneg_right_direct sourceLe (Arithmetic.sq_nonneg_direct
      _)).trans linear)
  exact ⟨allocation, (area_le_trace_for_family basis
    parentCount allocation.allowance).trans paid, paid, returned, sourcePaid⟩

end BasisPreparedFamilyAllowance
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance
