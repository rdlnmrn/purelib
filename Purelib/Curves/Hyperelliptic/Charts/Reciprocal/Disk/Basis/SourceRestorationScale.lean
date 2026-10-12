module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section

open Purelib.Curves

open Purelib.Riemann

public section

/-! A fixed pre-acquisition weight for complete source-restoration traces. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationScale

open SourceRestorationBudget.BasisCommonParentRequest.Plan.Acquisition.Sample
open CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition

open Purelib.Data.Rat.Fraction.Compatibility

open
  SourceRestorationBudget.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison
  (uniformSourceAreaError uniformSourceAreaError_le uniformSourceAreaWeight uniformSourceTotalError)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

/-- The complete source-restoration trace factor is nonnegative when the retained source slope is nonnegative. -/
theorem traceScale_nonnegative (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (count : Nat) (allowance : Normalization.InverseRootPolynomial.Coordinate) {slope :
      Normalization.InverseRootPolynomial.Coordinate} (slopeNonnegative : 0 ≤ slope) :
    0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale (basis :=
      basis) (allowance := allowance) count slope := open Purelib.Data.Rat in by
  have two : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2 := by decide
  have four : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4 := by decide
  have errorNonnegative : 0 ≤
    PreparedComparison.uniformSourceTotalError
    allowance :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
      Normalization.InverseRootPolynomial.Coordinate) ≤ 2050) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have areaNonnegative : 0 ≤
    PreparedComparison.uniformSourceAreaError
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
    slopeNonnegative.trans (Fraction.Order.Basic.le_max_right _ _)
  have area : 0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.areaScale
    (basis := basis) (allowance := allowance) count slope :=
    Fraction.Order.Arithmetic.mul_nonneg_direct two (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct _) areaNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
            errorNonnegative) totalNonnegative))
  exact Fraction.Order.Arithmetic.mul_nonneg_direct two (add_nonneg area (Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct four
      (add_nonneg two (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 8) basis.coefficient_nonnegative)))
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)) errorNonnegative))

/-- A parent allowance between zero and one bounds the complete trace factor by its unit-allowance value times the
squared allowance.

The estimate retains both the polygon of original parent totals and the initial-value ribbon contribution. -/
theorem traceScale_quadratic (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (count : Nat) (slope : Normalization.InverseRootPolynomial.Coordinate) {allowance :
      Normalization.InverseRootPolynomial.Coordinate}
    (nonnegative : 0 ≤ allowance) (small : allowance ≤ 1) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale (basis :=
      basis) (allowance := allowance) count slope ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale (basis :=
        basis) (allowance := 1) count slope * allowance^2 := open Purelib.Data.Rat in by
  have square : allowance^2 ≤ 1 := (Fraction.Order.Arithmetic.pow_le_pow_direct nonnegative small 2).trans_eq (by ring1)
  have areaSmall :
    PreparedComparison.uniformSourceAreaError
    allowance slope ≤
    PreparedComparison.uniformSourceAreaError
    1 slope * allowance^2 :=

      (PreparedComparison.uniformSourceAreaError_le
      slope square).trans_eq (by
        unfold PreparedComparison.uniformSourceAreaError
          PreparedComparison.uniformSourceAreaWeight
        ring1)
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
  have restored :
    Sample.PreparedComparison.restoredTotalBound
    (basis := basis) (allowance := allowance) ≤
    Sample.PreparedComparison.restoredTotalBound
    (basis := basis) (allowance := 1) := by
    have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.add_le_add_direct scaled (le_refl (12 :
        Normalization.InverseRootPolynomial.Coordinate))) (le_refl (64 * basis.coefficient)))
      (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    exact (show
      Sample.PreparedComparison.restoredTotalBound
      (basis := basis) (allowance := allowance) =
      2 * (16 * allowance^2 + 12 + 64 * basis.coefficient) by
        unfold Sample.PreparedComparison.restoredTotalBound
        ring1).trans_le
      (bounded.trans_eq (by
        unfold Sample.PreparedComparison.restoredTotalBound
        ring1))
  have totals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.totalBound
    (basis := basis) (allowance := allowance) slope ≤
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.totalBound (basis :=
    basis) (allowance := 1) slope :=
    Fraction.Order.Basic.max_le (restored.trans (Fraction.Order.Basic.le_max_left _ _))
      (Fraction.Order.Basic.le_max_right _ _)
  have factor : 0 ≤ 16 * (count : Normalization.InverseRootPolynomial.Coordinate)^4 *
    PreparedComparison.uniformSourceTotalError
    allowance :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
        Normalization.InverseRootPolynomial.Coordinate) ≤ 2050) (Fraction.Order.Arithmetic.sq_nonneg_direct allowance))
  have area : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.areaScale
    (basis := basis) (allowance := allowance) count slope ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.areaScale (basis :=
        basis) (allowance := 1) count slope * allowance^2 := by
    have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct areaSmall
        (Fraction.Order.Arithmetic.sq_nonneg_direct (count : Normalization.InverseRootPolynomial.Coordinate)))
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totals factor)) (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    exact bounded.trans_eq (by
      unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.areaScale
        PreparedComparison.uniformSourceTotalError
      ring1)
  have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct area
    (le_refl (4 * (2 + 8 * basis.coefficient) * (count : Normalization.InverseRootPolynomial.Coordinate)^2 *
      PreparedComparison.uniformSourceTotalError
      allowance)))
    (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  exact bounded.trans_eq (by
    unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale
      PreparedComparison.uniformSourceTotalError
    ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationScale

end
