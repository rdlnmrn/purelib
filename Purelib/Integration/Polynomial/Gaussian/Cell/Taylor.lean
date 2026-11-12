module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
public import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Finite Taylor comparison of actual constant-cell integrals

The original quadratic certificate retains independently prescribed primitive
endpoint readings. The constant cell retains its actual coefficient and
displacement. A chart tangent remainder and a separately paid coefficient
discrepancy give an explicit fourth-order error bound for that same cell.
These estimates do not define primitive endpoints from integral outputs.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Calculus.Jet
open Purelib.Polynomial.Ascending

/-- An original constant cell differs from a prescribed primitive increment by its Taylor and coefficient errors.

The original expansion and the exact displacement identify the primitive
increment. The retained constant polynomial identifies the actual cell sample;
the two errors keep their separate quadratic and first-order factors.
-/
theorem quadratic_integral_error_le {increment : Canonical} (certificate : Quadratic.Basic.Certificate increment)
    (cell : CellModel) (coefficient : Canonical) (displacement : cell.displacement = increment)
    (constant : cell.polynomial = Gaussian.Basic.constant coefficient) :
    Norm.Basic.normSq (certificate.output - certificate.base - cell.integralSample) ≤
      2 * (certificate.factor * Norm.Basic.normSq increment ^ 2 +
        Norm.Basic.normSq increment * Norm.Basic.normSq (certificate.slope - coefficient)) := by
  have remainderBound : Norm.Basic.normSq certificate.remainder ≤
      certificate.factor * Norm.Basic.normSq increment ^ 2 := by
    rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical]
    exact certificate.remainder_le
  have error : certificate.output - certificate.base - cell.integralSample =
      certificate.remainder + increment * (certificate.slope - coefficient) := by
    rewrite [cell.integralSample_constant coefficient constant, displacement, ← certificate.expansion]
    ring1
  rewrite [error]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct remainderBound
        (Norm.Basic.normSq_mul increment (certificate.slope - coefficient)).le) (by decide +kernel))

/-- Chart movement, tangent and coefficient payments bound the same original constant-cell primitive error.

The quadratic certificate is indexed by the physical spatial increment. The
cell displacement is the original chart increment, and its constant is the
original chart velocity times the supplied differential reading. The returned
bound is fourth order in chart displacement and retains all three payments.
-/
theorem charted_quadratic_integral_error_le {increment : Canonical}
    (certificate : Quadratic.Basic.Certificate increment)
    (cell : CellModel) (step velocity coefficient : Canonical)
    (displacement : cell.displacement = step)
    (constant : cell.polynomial = Gaussian.Basic.constant (velocity * coefficient))
    (movement tangent velocityBound coefficientError : Fraction.Rational)
    (coefficientError_nonnegative : 0 ≤ coefficientError)
    (movement_le : Norm.Basic.normSq increment ≤ movement * Norm.Basic.normSq step)
    (tangent_le : Norm.Basic.normSq (increment - step * velocity) ≤ tangent * Norm.Basic.normSq step ^ 2)
    (velocity_le : Norm.Basic.normSq velocity ≤ velocityBound)
    (coefficient_le : Norm.Basic.normSq (certificate.slope - coefficient) ≤
      coefficientError * Norm.Basic.normSq step) :
    Norm.Basic.normSq (certificate.output - certificate.base - cell.integralSample) ≤
      2 * (certificate.factor * movement ^ 2 +
        2 * (tangent * Norm.Basic.normSq certificate.slope + velocityBound * coefficientError)) *
          Norm.Basic.normSq step ^ 2 := by
  have remainderBound : Norm.Basic.normSq certificate.remainder ≤
      certificate.factor * movement ^ 2 * Norm.Basic.normSq step ^ 2 := by
    have original : Norm.Basic.normSq certificate.remainder ≤
        certificate.factor * Norm.Basic.normSq increment ^ 2 := by
      rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical]
      exact certificate.remainder_le
    exact original.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) movement_le 2)
      certificate.factor_nonneg).trans_eq (by ring1))
  have tangentBound : Norm.Basic.normSq ((increment - step * velocity) * certificate.slope) ≤
      tangent * Norm.Basic.normSq certificate.slope * Norm.Basic.normSq step ^ 2 := by
    rewrite [Norm.Basic.normSq_mul]
    exact (Arithmetic.mul_le_mul_of_nonneg_right_direct tangent_le
      (Norm.Basic.normSq_nonneg _)).trans_eq (by ring1)
  have coefficientBound : Norm.Basic.normSq (step * velocity * (certificate.slope - coefficient)) ≤
      velocityBound * coefficientError * Norm.Basic.normSq step ^ 2 := by
    rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
    calc
      _ ≤ Norm.Basic.normSq step * Norm.Basic.normSq velocity *
          (coefficientError * Norm.Basic.normSq step) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct coefficient_le
          (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _))
      _ = Norm.Basic.normSq velocity * (coefficientError * Norm.Basic.normSq step ^ 2) := by ring1
      _ ≤ velocityBound * (coefficientError * Norm.Basic.normSq step ^ 2) :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct velocity_le
          (Arithmetic.mul_nonneg_direct coefficientError_nonnegative
            (Arithmetic.sq_nonneg_direct _))
      _ = _ := by ring1
  have error : certificate.output - certificate.base - cell.integralSample =
      certificate.remainder + ((increment - step * velocity) * certificate.slope +
        step * velocity * (certificate.slope - coefficient)) := by
    rewrite [cell.integralSample_constant (velocity * coefficient) constant, displacement, ← certificate.expansion]
    ring1
  rewrite [error]
  calc
    _ ≤ 2 * (Norm.Basic.normSq certificate.remainder +
        Norm.Basic.normSq ((increment - step * velocity) * certificate.slope +
          step * velocity * (certificate.slope - coefficient))) := Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (certificate.factor * movement ^ 2 * Norm.Basic.normSq step ^ 2 +
        2 * (tangent * Norm.Basic.normSq certificate.slope * Norm.Basic.normSq step ^ 2 +
          velocityBound * coefficientError * Norm.Basic.normSq step ^ 2)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct remainderBound
          ((Norm.Bounds.normSq_add_le_two _ _).trans
            (Arithmetic.mul_le_mul_of_nonneg_left_direct
              (Arithmetic.add_le_add_direct tangentBound coefficientBound) (by decide +kernel))))
        (by decide +kernel)
    _ = _ := by ring1

end Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel
