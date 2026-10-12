module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Projective

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Nondegeneracy of the finite CCL boundary charts

Every active curve source is a genuine rational line or a nonzero-radius
circle transported by an invertible finite homography.  Consequently its
homogeneous denominator is a represented nonzero coordinate polynomial, and
its affine values are injective at non-pole parameters.

The final theorem uses only finitely many parameters: one denominator-safe
point in each of `natDegree + 1` disjoint unit intervals.  If both cleared
coordinates vanished identically, these points would give too many distinct
displayed roots of the original Gaussian-rational polynomial.
-/

namespace Purelib.Geometry.Projective.Homography

/-- An invertible Gaussian homography has at most one affine denominator zero.

Its retained nonzero determinant excludes a zero denominator row, and scalar cancellation identifies any two supplied
affine zeros. -/
public theorem denominator_zero_unique
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    {left right : Data.Gaussian.Basic.Canonical}
    (leftZero : Homography.Basic.denominator matrix left = 0)
    (rightZero : Homography.Basic.denominator matrix right = 0) :
    left = right := by
  by_cases lowerLeftZero : matrix.c = 0
  · have lowerRightZero : matrix.d = 0 := by
      change matrix.c * left + matrix.d = 0 at leftZero
      rw [lowerLeftZero, Data.Gaussian.Basic.zero_mul,
        Data.Gaussian.Basic.zero_add] at leftZero
      exact leftZero
    apply (determinantNonzero ?_).elim
    simp only [BoundaryAdjugate.determinant,
      Matrix2.determinant, lowerLeftZero, lowerRightZero,
      Data.Gaussian.Basic.mul_zero,
      Data.Gaussian.Basic.sub_self, -eq_self, -iff_self]
    rfl
  · have leftProduct : matrix.c * left = -matrix.d := by
      change matrix.c * left + matrix.d = 0 at leftZero
      apply Data.Gaussian.Basic.ext
      · have real := congrArg Data.Gaussian.Basic.re leftZero
        simp only [Data.Gaussian.Basic.add_re,
          Data.Gaussian.Basic.zero_re,
          Data.Gaussian.Basic.neg_re] at real ⊢
        calc
          (matrix.c * left).re =
              (matrix.c * left).re + matrix.d.re - matrix.d.re := by ring1
          _ = -matrix.d.re := by rw [real]; ring1
      · have imaginary := congrArg Data.Gaussian.Basic.im leftZero
        simp only [Data.Gaussian.Basic.add_im,
          Data.Gaussian.Basic.zero_im,
          Data.Gaussian.Basic.neg_im] at imaginary ⊢
        calc
          (matrix.c * left).im =
              (matrix.c * left).im + matrix.d.im - matrix.d.im := by ring1
          _ = -matrix.d.im := by rw [imaginary]; ring1
    have rightProduct : matrix.c * right = -matrix.d := by
      change matrix.c * right + matrix.d = 0 at rightZero
      apply Data.Gaussian.Basic.ext
      · have real := congrArg Data.Gaussian.Basic.re rightZero
        simp only [Data.Gaussian.Basic.add_re,
          Data.Gaussian.Basic.zero_re,
          Data.Gaussian.Basic.neg_re] at real ⊢
        calc
          (matrix.c * right).re =
              (matrix.c * right).re + matrix.d.re - matrix.d.re := by ring1
          _ = -matrix.d.re := by rw [real]; ring1
      · have imaginary := congrArg Data.Gaussian.Basic.im rightZero
        simp only [Data.Gaussian.Basic.add_im,
          Data.Gaussian.Basic.zero_im,
          Data.Gaussian.Basic.neg_im] at imaginary ⊢
        calc
          (matrix.c * right).im =
              (matrix.c * right).im + matrix.d.im - matrix.d.im := by ring1
          _ = -matrix.d.im := by rw [imaginary]; ring1
    apply Data.Gaussian.Field.mul_right_cancel_of_ne lowerLeftZero
    calc
      left * matrix.c = matrix.c * left :=
        Data.Gaussian.Basic.mul_comm _ _
      _ = -matrix.d := leftProduct
      _ = matrix.c * right := rightProduct.symm
      _ = right * matrix.c :=
        Data.Gaussian.Basic.mul_comm _ _

end Purelib.Geometry.Projective.Homography

end

section
@[expose] public section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

namespace Purelib.Geometry.Projective.Homography

/-- The unique affine pole when the lower-left matrix entry is nonzero. -/
def decoderPole (matrix : GaussianMatrix) :
  Data.Gaussian.Basic.Canonical :=
  (-matrix.d) * matrix.c⁻¹

/-- The displayed pole zeros the affine denominator when the lower-left entry is nonzero. -/
theorem denominator_at_decoderPole (matrix :
  GaussianMatrix)
    (lowerLeftNonzero : matrix.c ≠ 0) :
    Homography.Basic.denominator matrix (decoderPole matrix) = 0 := by
  unfold Homography.Basic.denominator decoderPole
  calc
    matrix.c * ((-matrix.d) * matrix.c⁻¹) + matrix.d =
        (-matrix.d) * (matrix.c * matrix.c⁻¹) + matrix.d := by
      apply congrArg (fun value : Data.Gaussian.Basic.Canonical => value + matrix.d)
      calc
        matrix.c * ((-matrix.d) * matrix.c⁻¹) =
            (matrix.c * (-matrix.d)) * matrix.c⁻¹ :=
          (Data.Gaussian.Basic.mul_assoc _ _ _).symm
        _ = ((-matrix.d) * matrix.c) * matrix.c⁻¹ := by
          rw [Data.Gaussian.Basic.mul_comm matrix.c (-matrix.d)]
        _ = (-matrix.d) * (matrix.c * matrix.c⁻¹) :=
          Data.Gaussian.Basic.mul_assoc _ _ _
    _ = (-matrix.d) * 1 + matrix.d := by
      rw [show matrix.c * matrix.c⁻¹ = 1 by
        exact Data.Gaussian.Basic.Canonical.mul_inv_cancel matrix.c
          lowerLeftNonzero]
    _ = -matrix.d + matrix.d := by
      rw [Data.Gaussian.Basic.mul_one]
    _ = 0 := neg_add_cancel matrix.d

/-- The denominator factors as `c` times displacement from its pole. -/
theorem denominator_eq_mul_sub_pole (matrix :
  GaussianMatrix)
    (lowerLeftNonzero : matrix.c ≠ 0) (value : Data.Gaussian.Basic.Canonical) :
    Homography.Basic.denominator matrix value =
      matrix.c * (value - decoderPole matrix) := by
  have poleZero := denominator_at_decoderPole matrix lowerLeftNonzero
  unfold Homography.Basic.denominator at poleZero ⊢
  calc
    matrix.c * value + matrix.d =
        (matrix.c * value + matrix.d) -
          (matrix.c * decoderPole matrix + matrix.d) := by
      rw [poleZero]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.zero_re,
          Data.Gaussian.Basic.zero_im] <;>
        ring1
    _ = matrix.c * (value - decoderPole matrix) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.add_re,
          Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im] <;>
        ring1
end Purelib.Geometry.Projective.Homography

end
