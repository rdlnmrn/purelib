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

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

/-- The retained restored-total factor is nonnegative for every allowance. -/
private theorem totalBound_nonnegative (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds
  bounds) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    0 ≤
      Sample.PreparedComparison.restoredTotalBound
      (basis := basis) (allowance := allowance) := by
  unfold
    Sample.PreparedComparison.restoredTotalBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    (add_nonneg (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 12))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 64) basis.coefficient_nonnegative))

/-- The original prepared-concatenation squared-error factor is nonnegative. -/
private theorem scale_nonnegative (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds
  bounds) (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale (basis :=
      basis) (allowance := allowance) count := by
  unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
        Normalization.InverseRootPolynomial.Coordinate) ≤ 82) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤
          16) (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))
          4))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))
          (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.totalBound_nonnegative basis allowance)))

/-- The prepared family's complete concatenation factor is nonnegative. -/
theorem scale_nonnegative_for_family (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds
  bounds) (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale (basis :=
      basis) (allowance := allowance) count := by
  unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
        Normalization.InverseRootPolynomial.Coordinate) ≤ 82) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤
          16) (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))
          4))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))
          (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.totalBound_nonnegative basis allowance)))

/-- For an allowance between zero and one, the concatenation factor is bounded by its unit value times the squared
allowance. -/
private theorem scale_quadratic (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
  (count : Nat)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ allowance) (small : allowance ≤ 1) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale (basis := basis)
      (allowance := allowance) count ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale (basis := basis)
        (allowance := 1) count * allowance^2 := by
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) nonnegative)
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)) 2
  have totals :
    Sample.PreparedComparison.restoredTotalBound
    (basis := basis) (allowance := allowance) ≤
    Sample.PreparedComparison.restoredTotalBound
    (basis := basis) (allowance := 1) := by
    unfold
      Sample.PreparedComparison.restoredTotalBound
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.add_le_add_direct square le_rfl) le_rfl)
      (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have factor : 0 ≤ 16 * (count : Normalization.InverseRootPolynomial.Coordinate)^4 * (4 * allowance)^2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  calc
    _ ≤ 2 * ((count : Normalization.InverseRootPolynomial.Coordinate)^2 * (82 * (4 * allowance)^2) +
        16 * (count : Normalization.InverseRootPolynomial.Coordinate)^4 * (4 * allowance)^2 *

            Sample.PreparedComparison.restoredTotalBound
          (basis := basis) (allowance := 1)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct le_rfl
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totals factor))
        (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    _ = _ := by
      unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale
      ring1

/-- The original initial-value ribbon factor is nonnegative. -/
private theorem ribbonScale_nonnegative (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds
  bounds)
    (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    0 ≤ 4 * (2 + 8 * basis.coefficient) * (count : Normalization.InverseRootPolynomial.Coordinate)^2 * (4 * allowance)^2
      :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)
      (add_nonneg (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 8) basis.coefficient_nonnegative)))
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- The complete concatenation area factor is bounded by its retained trace-comparison factor. -/
private theorem area_le_trace (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale (basis := basis)
      (allowance := allowance) count ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale (basis :=
        basis) (allowance := allowance) count := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  exact (add_nonneg (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.scale_nonnegative basis count
    allowance)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.ribbonScale_nonnegative basis count
      allowance))).trans_eq
      (by
        unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale
        ring1)

/-- The prepared family's concatenation factor does not exceed its trace-comparison factor. -/
theorem area_le_trace_for_family (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds
  bounds)
    (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale (basis := basis)
      (allowance := allowance) count ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale (basis :=
        basis) (allowance := allowance) count := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  exact (add_nonneg (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.scale_nonnegative_for_family
    basis count allowance)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.ribbonScale_nonnegative basis count
      allowance))).trans_eq
      (by
        unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale
        ring1)

/-- For a nonnegative allowance at most one, the trace-comparison factor is bounded by its unit value times the squared
allowance. -/
private theorem trace_scale_quadratic (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds
  bounds) (count : Nat)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ allowance) (small : allowance ≤ 1) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale (basis := basis)
      (allowance := allowance) count ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale (basis :=
        basis) (allowance := 1) count * allowance^2 := by
  calc
    _ ≤ 2 * (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale (basis :=
      basis) (allowance := 1) count * allowance^2 +
        4 * (2 + 8 * basis.coefficient) * (count : Normalization.InverseRootPolynomial.Coordinate)^2 * (4 *
          allowance)^2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.scale_quadratic basis count nonnegative
        small) le_rfl)
        (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    _ = _ := by
      unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale
      ring1

/-- The prepared family trace factor scales quadratically below the unit allowance. -/
theorem trace_scale_quadratic_for_family (basis :
  Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds) (count : Nat)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ allowance) (small : allowance ≤ 1) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale (basis := basis)
      (allowance := allowance) count ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale (basis :=
        basis) (allowance := 1) count * allowance^2 := by
  calc
    _ ≤ 2 * (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale (basis :=
      basis) (allowance := 1) count * allowance^2 +
        4 * (2 + 8 * basis.coefficient) * (count : Normalization.InverseRootPolynomial.Coordinate)^2 * (4 *
          allowance)^2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.scale_quadratic basis count nonnegative
        small) le_rfl)
        (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    _ = _ := by
      unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale
      ring1

set_option genInjectivity false in
/-- One pre-acquisition allowance paying the complete prepared family, return and source-trace errors.

The allocation retains the exact parent count, positive target and source slope. Its four certificates bound the
original factors by the same squared target. -/
structure BasisPreparedFamilyAllowance (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds
  bounds)
    (parentCount : Nat) (target slope : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The retained family allocation with its original parent count and target. -/ allocation :
    Budget.Trace.Family.BasisFamilyAllowance parentCount target
  /-- The complete prepared concatenation factor is paid by the squared target. -/ paid :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale (basis := basis)
    (allowance := allocation.allowance) parentCount ≤ target^2
  /-- The complete prepared trace-comparison factor is paid by the squared target. -/ trace_paid :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale (basis := basis)
    (allowance := allocation.allowance) parentCount ≤ target^2
  /-- The actual parent-return factor is paid by the squared target. -/ return_paid :
    CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale
    (basis := basis) (allowance := allocation.allowance) ≤ target^2
  /-- The complete source-restoration trace factor is paid at the same allocation. -/ source_trace_paid :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale
    (basis := basis) (allowance := allocation.allowance) parentCount slope ≤ target^2

constructive_injectivity BasisPreparedFamilyAllowance

namespace BasisPreparedFamilyAllowance

/-- Allocate one positive parent allowance paying all original concatenation, trace, return and source-restoration
factors.

A positive target and nonnegative source slope give nonnegative retained unit weights; their sum determines the common
weighted ceiling before samples are acquired. -/
@[expose] def build (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (parentCount : Nat) (target slope : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target)
      (slopeNonnegative : 0 ≤ slope) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.BasisPreparedFamilyAllowance basis parentCount
      target slope := by
  let traceWeight := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale
    (basis := basis) (allowance := 1) parentCount
  let returnWeight :=
    CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale
    (basis := basis) (allowance := 1)
  have traceNonnegative : 0 ≤ traceWeight :=
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.scale_nonnegative_for_family basis parentCount
      1).trans (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.area_le_trace_for_family basis
      parentCount 1)
  have returnNonnegative : 0 ≤ returnWeight :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (add_nonneg (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 180)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 64) basis.coefficient_nonnegative))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  let sourceWeight :=
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale (basis :=
    basis) (allowance := 1) parentCount slope
  have sourceNonnegative : 0 ≤ sourceWeight :=
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationScale.traceScale_nonnegative basis parentCount 1
      slopeNonnegative
  let weight := traceWeight + returnWeight + sourceWeight
  have weightNonnegative : 0 ≤ weight := add_nonneg (add_nonneg traceNonnegative returnNonnegative) sourceNonnegative
  have traceLe : traceWeight ≤ weight := (le_add_of_nonneg_right returnNonnegative).trans (le_add_of_nonneg_right
    sourceNonnegative)
  have returnLe : returnWeight ≤ weight := (le_add_of_nonneg_left traceNonnegative).trans (le_add_of_nonneg_right
    sourceNonnegative)
  have sourceLe : sourceWeight ≤ weight := le_add_of_nonneg_left (add_nonneg traceNonnegative returnNonnegative)
  let ceiling := min 1 (Rational.Budget.Weighted.allowance (target^2) weight)
  have ceilingPositive : 0 < ceiling := Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 1)
    (Rational.Budget.Weighted.allowance_positive (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
      weightNonnegative)
  let allocation := Budget.Trace.Family.BasisFamilyAllowance.build parentCount target ceiling positive ceilingPositive
  have ceilingLe : allocation.allowance ≤ ceiling := allocation.allowance_le_ceiling
  have small : allocation.allowance ≤ 1 := ceilingLe.trans (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _)
  have square : allocation.allowance^2 ≤ allocation.allowance :=
    (show allocation.allowance^2 = allocation.allowance * allocation.allowance by ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small allocation.positive.le).trans_eq
        (Fraction.Field.mul_one_direct _))
  have linear := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (square.trans (ceilingLe.trans (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _))) weightNonnegative).trans
      (Rational.Budget.Weighted.mul_allowance_le (Fraction.Order.Arithmetic.sq_nonneg_direct target) weightNonnegative)
  have paid := (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.trace_scale_quadratic_for_family
    basis parentCount allocation.positive.le small).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct traceLe (Fraction.Order.Arithmetic.sq_nonneg_direct
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
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct returnLe
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans linear)
  have sourcePaid := (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationScale.traceScale_quadratic basis
    parentCount slope allocation.positive.le small).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct sourceLe (Fraction.Order.Arithmetic.sq_nonneg_direct
      _)).trans linear)
  exact ⟨allocation, (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.area_le_trace_for_family basis
    parentCount allocation.allowance).trans paid, paid, returned, sourcePaid⟩

end BasisPreparedFamilyAllowance
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance
