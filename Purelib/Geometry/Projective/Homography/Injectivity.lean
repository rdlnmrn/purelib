module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Tactic.Ring

/-!
# Injectivity of Gaussian homographies

A nonsingular Gaussian matrix identifies affine inputs whenever both displayed
denominators are nonzero. The proof clears these denominators and cancels the
retained determinant using the canonical Gaussian field operations.
-/

namespace Purelib.Geometry.Projective.Homography.Injectivity

open Purelib.Data
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2.Matrix

/-- A nonsingular Gaussian homography is injective where its affine denominators are nonzero.

The two denominator witnesses allow the displayed images to be cross-multiplied.
The resulting difference factors through the nonzero determinant, so Gaussian
cancellation identifies the original inputs.
-/
public theorem homographic_injective
    (matrix : GaussianMatrix) {left right : Gaussian.Basic.Canonical}
    (determinant : Matrix2.determinant matrix ≠ 0)
    (leftDenominator : Homography.Basic.denominator matrix left ≠ 0)
    (rightDenominator : Homography.Basic.denominator matrix right ≠ 0)
    (images : Homography.Basic.homographic matrix left = Homography.Basic.homographic matrix right) :
    left = right := by
  have cross : Homography.Basic.numerator matrix left * Homography.Basic.denominator matrix right =
      Homography.Basic.numerator matrix right * Homography.Basic.denominator matrix left := by
    rw [show Homography.Basic.numerator matrix left =
        Homography.Basic.homographic matrix left * Homography.Basic.denominator matrix left by
      unfold Homography.Basic.homographic
      rw [_root_.mul_assoc, Gaussian.Field.inv_eq, Gaussian.Field.inv_mul _ leftDenominator,
        Gaussian.Basic.mul_one]]
    rw [show Homography.Basic.numerator matrix right =
        Homography.Basic.homographic matrix right * Homography.Basic.denominator matrix right by
      unfold Homography.Basic.homographic
      rw [_root_.mul_assoc, Gaussian.Field.inv_eq, Gaussian.Field.inv_mul _ rightDenominator,
        Gaussian.Basic.mul_one]]
    rw [images]
    ring1
  have factored :
      Matrix2.determinant matrix * (left + -right) = 0 := by
    calc
      Matrix2.determinant matrix * (left + -right) =
          Homography.Basic.numerator matrix left * Homography.Basic.denominator matrix right +
            -(Homography.Basic.numerator matrix right * Homography.Basic.denominator matrix left) := by
        unfold Matrix2.determinant Homography.Basic.numerator Homography.Basic.denominator
        rw [Gaussian.Basic.sub_eq_add_neg]
        ring1
      _ = 0 := by rw [cross]; ring1
  have differenceZero : left + -right = 0 := by
    apply Gaussian.Field.mul_right_cancel_of_ne determinant
    calc
      (left + -right) * Matrix2.determinant matrix =
          Matrix2.determinant matrix * (left + -right) := by ring1
      _ = 0 := factored
      _ = 0 * Matrix2.determinant matrix := by
        rw [Gaussian.Basic.zero_mul]
  apply Gaussian.Basic.gaussian_eq_of_sub_eq_zero
  rewrite [Gaussian.Basic.sub_eq_add_neg]
  exact differenceZero

end Purelib.Geometry.Projective.Homography.Injectivity
