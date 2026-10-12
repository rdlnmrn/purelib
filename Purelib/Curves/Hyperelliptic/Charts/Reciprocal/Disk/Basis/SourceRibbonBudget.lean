module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Riemann

public section

/-! Pay the source ribbon from the already allocated restoration budgets. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRibbonBudget

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

/-- The original source-ribbon factor is bounded by six times the squared target when all three retained budgets are
paid.

The source trace, prepared chart trace and actual endpoint-return factors use the same allowance, parent count and
nonnegative source slope. -/
theorem ribbon_paid (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) {slope target :
      Normalization.InverseRootPolynomial.Coordinate} (slopeNonnegative : 0 ≤ slope)
    (sourcePaid : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale
      (basis := basis) (allowance := allowance) count slope ≤ target ^ 2)
    (chartPaid : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale
      (basis := basis) (allowance := allowance) count ≤ target ^ 2)
    (returnPaid :
      CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale
      (basis := basis) (allowance := allowance) ≤ target ^ 2) :
    4 * (2 + 8 * basis.coefficient) *
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn.Samples.SourceRestoration.totalScale (allowance :=
      allowance) count ≤ 6 * target ^ 2 := open Purelib.Data.Rat in by
  have two : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2 := by decide
  have four : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4 := by decide
  have errorNonnegative : 0 ≤
    SourceRestorationBudget.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison.uniformSourceTotalError
    allowance :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
      Normalization.InverseRootPolynomial.Coordinate) ≤ 2050) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have areaNonnegative : 0 ≤
    SourceRestorationBudget.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison.uniformSourceAreaError
    allowance slope :=
    Fraction.Order.Arithmetic.mul_nonneg_direct two (add_nonneg
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by
            decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 240)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
            Normalization.InverseRootPolynomial.Coordinate) ≤ 64) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
        (Fraction.Order.Arithmetic.mul_nonneg_direct two (add_nonneg slopeNonnegative (by decide))))
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
          Normalization.InverseRootPolynomial.Coordinate) ≤ 352) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
          (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have totalNonnegative : 0 ≤
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.totalBound (basis :=
    basis) (allowance := allowance) slope :=
    slopeNonnegative.trans (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _)
  have area : 0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.areaScale
    (basis := basis) (allowance := allowance) count slope :=
    Fraction.Order.Arithmetic.mul_nonneg_direct two (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct _) areaNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
            errorNonnegative) totalNonnegative))

  have totals : 0 ≤
    CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison.restoredTotalBound
    (basis := basis) (allowance := allowance) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct two (add_nonneg (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct
      _) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 12))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 64) basis.coefficient_nonnegative))
  have chartArea : 0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale
    (basis := basis) (allowance := allowance) count :=
    Fraction.Order.Arithmetic.mul_nonneg_direct two (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
        Normalization.InverseRootPolynomial.Coordinate) ≤ 82) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)) totals))
  have scale : 4 * (2 + 8 * basis.coefficient) *
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn.Samples.SourceRestoration.totalScale (allowance :=
    allowance) count ≤
      2 *
        (CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale
        (basis := basis) (allowance := allowance) +
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale (basis :=
          basis) (allowance := allowance) count +
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale (basis :=
          basis) (allowance := allowance) count slope) := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    have residual := add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct four (add_nonneg chartArea area))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (add_nonneg (by
          decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 344)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by
            decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 64) basis.coefficient_nonnegative))
        (Fraction.Order.Arithmetic.sq_nonneg_direct (4 * allowance)))
    exact residual.trans_eq (by
      unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn.Samples.SourceRestoration.totalScale
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale
        CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale
      ring1)
  exact scale.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.add_le_add_direct returnPaid chartPaid)
      sourcePaid) two).trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRibbonBudget
