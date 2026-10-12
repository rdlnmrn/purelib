module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Tactic.Ring

/-!
# Composition of Gaussian homographies

The affine numerator and denominator of a retained matrix product admit exact
polynomial expansions. Supplied nonzero denominator witnesses then identify
that product action with the successive affine homographies.
-/

namespace Purelib.Geometry.Projective.Homography

open Purelib.Data
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2
open Purelib.LinearAlgebra.Coordinates2.Matrix

/-- A product of Gaussian matrices with nonzero determinants has nonzero determinant.

The determinant multiplication identity expresses the retained product determinant
as the product of the two supplied nonzero Gaussian determinants.
-/
private theorem determinant_mul_ne
    (outer inner : GaussianMatrix)
    (outerNonzero : Matrix2.determinant outer ≠ 0)
    (innerNonzero : Matrix2.determinant inner ≠ 0) :
    Matrix2.determinant (Matrix.mul outer inner) ≠ 0 := by
  rw [Matrix.det_mul]
  exact Gaussian.Field.mul_ne_zero_direct outerNonzero innerNonzero

/-- A matrix with lower row `[0,1]` preserves the lower row of its right factor.

The two retained zero and unit entries of the left factor reduce each displayed
product entry to the corresponding entry of the right factor.
-/
private theorem mul_lowerRow
    (outer inner : GaussianMatrix)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1) :
    (Matrix.mul outer inner).c = inner.c ∧
      (Matrix.mul outer inner).d = inner.d := by
  rcases outerLowerRow with ⟨lowerLeft, lowerRight⟩
  constructor
  · change outer.c * inner.a + outer.d * inner.c = inner.c
    calc
      outer.c * inner.a + outer.d * inner.c =
          0 * inner.a + 1 * inner.c := by rw [lowerLeft, lowerRight]
      _ = inner.c := by
        rw [Gaussian.Basic.zero_mul, Gaussian.Basic.one_mul,
          Gaussian.Basic.zero_add]
  · change outer.c * inner.b + outer.d * inner.d = inner.d
    calc
      outer.c * inner.b + outer.d * inner.d =
          0 * inner.b + 1 * inner.d := by rw [lowerLeft, lowerRight]
      _ = inner.d := by
        rw [Gaussian.Basic.zero_mul, Gaussian.Basic.one_mul,
          Gaussian.Basic.zero_add]
namespace Composition

/-- The lower row of a product evaluates as the outer lower row applied to the right factor's affine numerator and
denominator.

The equality expands the original matrix product at the supplied Gaussian tail.
No denominator witness is needed for this polynomial identity.
-/
public theorem denominator_mul_expanded (left right : GaussianMatrix) (tail :
  Gaussian.Basic.Canonical) :
    Homography.Basic.denominator (Matrix.mul left right) tail =
      left.c * Homography.Basic.numerator right tail + left.d * Homography.Basic.denominator right tail := by
  apply Gaussian.Basic.ext <;>
    simp only [Homography.Basic.denominator, Homography.Basic.numerator, Matrix.mul, Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;>
    ring1

/-- Once the inner denominator is nonzero, the product denominator factors through the inner homographic value.

The inner denominator witness permits cancellation in the displayed affine
value. The remaining outer denominator retains that value and the original
inner denominator as its two factors.
-/
public theorem denominator_mul (left right : GaussianMatrix) (tail : Gaussian.Basic.Canonical)
    (rightDenominator : Homography.Basic.denominator right tail ≠ 0) :
    Homography.Basic.denominator (Matrix.mul left right) tail =
      Homography.Basic.denominator left (Homography.Basic.homographic right tail) * Homography.Basic.denominator right
        tail := by
  rw [denominator_mul_expanded]
  have cancel :
      Homography.Basic.homographic right tail * Homography.Basic.denominator right tail =
        Homography.Basic.numerator right tail := by
    unfold Homography.Basic.homographic
    rw [_root_.mul_assoc, Gaussian.Field.inv_eq, Gaussian.Field.inv_mul _ rightDenominator,
      Gaussian.Basic.mul_one]
  calc
    left.c * Homography.Basic.numerator right tail + left.d * Homography.Basic.denominator right tail =
        left.c * (Homography.Basic.homographic right tail * Homography.Basic.denominator right tail) +
          left.d * Homography.Basic.denominator right tail := by rw [cancel]
    _ = Homography.Basic.denominator left (Homography.Basic.homographic right tail) *
          Homography.Basic.denominator right tail := by
      unfold Homography.Basic.denominator
      ring1

/-- The upper row has the analogous product expansion.

The original product numerator is expressed through the right factor's
affine numerator and denominator at the same supplied Gaussian tail.
-/
public theorem numerator_mul_expanded (left right : GaussianMatrix) (tail :
  Gaussian.Basic.Canonical) :
    Homography.Basic.numerator (Matrix.mul left right) tail =
      left.a * Homography.Basic.numerator right tail + left.b * Homography.Basic.denominator right tail := by
  apply Gaussian.Basic.ext <;>
    simp only [Homography.Basic.denominator, Homography.Basic.numerator, Matrix.mul, Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;>
    ring1

/-- Factor the product numerator through the inner homographic value.

The inner affine denominator must be nonzero; multiplying the outer numerator by this denominator clears the inner
division. -/
public theorem numerator_mul (left right : GaussianMatrix) (tail : Gaussian.Basic.Canonical)
    (rightDenominator : Homography.Basic.denominator right tail ≠ 0) :
    Homography.Basic.numerator (Matrix.mul left right) tail =
      Homography.Basic.numerator left (Homography.Basic.homographic right tail) * Homography.Basic.denominator right
        tail := by
  rw [numerator_mul_expanded]
  have cancel :
      Homography.Basic.homographic right tail * Homography.Basic.denominator right tail =
        Homography.Basic.numerator right tail := by
    unfold Homography.Basic.homographic
    rw [_root_.mul_assoc, Gaussian.Field.inv_eq, Gaussian.Field.inv_mul _ rightDenominator,
      Gaussian.Basic.mul_one]
  calc
    left.a * Homography.Basic.numerator right tail + left.b * Homography.Basic.denominator right tail =
        left.a * (Homography.Basic.homographic right tail * Homography.Basic.denominator right tail) +
          left.b * Homography.Basic.denominator right tail := by rw [cancel]
    _ = Homography.Basic.numerator left (Homography.Basic.homographic right tail) *
          Homography.Basic.denominator right tail := by
      unfold Homography.Basic.numerator
      ring1

/-- Exact nonvanishing transport for a product denominator.

With a nonzero inner denominator, the factored product denominator vanishes
exactly when the outer denominator at the inner affine value vanishes.
-/
public theorem denominator_mul_ne_iff (left right : GaussianMatrix) (tail :
  Gaussian.Basic.Canonical)
    (rightDenominator : Homography.Basic.denominator right tail ≠ 0) :
    Homography.Basic.denominator (Matrix.mul left right) tail ≠ 0 ↔
      Homography.Basic.denominator left (Homography.Basic.homographic right tail) ≠ 0 := by
  rw [denominator_mul left right tail rightDenominator]
  constructor
  · intro productNonzero leftZero
    apply productNonzero
    rw [leftZero, Gaussian.Basic.zero_mul]
  · intro leftNonzero
    exact Gaussian.Field.mul_ne_zero_direct leftNonzero rightDenominator

/-- Affine homographies compose in decoder-product order.

The supplied inner and outer denominator witnesses identify the affine value
of the original matrix product with the successive affine values. The proof
retains the original Gaussian inverse and multiplication operations.
-/
public theorem homographic_mul (left right : GaussianMatrix) (tail : Gaussian.Basic.Canonical)
    (rightDenominator : Homography.Basic.denominator right tail ≠ 0)
    (leftDenominator : Homography.Basic.denominator left (Homography.Basic.homographic right tail) ≠ 0) :
    Homography.Basic.homographic (Matrix.mul left right) tail =
      Homography.Basic.homographic left (Homography.Basic.homographic right tail) := by
  have productDenominator :
      Homography.Basic.denominator (Matrix.mul left right) tail ≠ 0 :=
    (denominator_mul_ne_iff left right tail rightDenominator).2
      leftDenominator
  rw [show Homography.Basic.homographic (Matrix.mul left right) tail =
      Homography.Basic.numerator (Matrix.mul left right) tail *
        (Homography.Basic.denominator (Matrix.mul left right) tail)⁻¹ by rfl]
  rw [numerator_mul left right tail rightDenominator,
    denominator_mul left right tail rightDenominator]
  rw [show Homography.Basic.homographic left (Homography.Basic.homographic right tail) =
      Homography.Basic.numerator left (Homography.Basic.homographic right tail) *
        (Homography.Basic.denominator left (Homography.Basic.homographic right tail))⁻¹ by rfl]
  let outerDenominator := Homography.Basic.denominator left (Homography.Basic.homographic right tail)
  let innerDenominator := Homography.Basic.denominator right tail
  let valueNumerator := Homography.Basic.numerator left (Homography.Basic.homographic right tail)
  have combinedNonzero : outerDenominator * innerDenominator ≠ 0 :=
    Gaussian.Field.mul_ne_zero_direct leftDenominator rightDenominator
  apply Gaussian.Field.mul_right_cancel_of_ne
    combinedNonzero
  calc
    ((valueNumerator * innerDenominator) *
          (outerDenominator * innerDenominator)⁻¹) *
        (outerDenominator * innerDenominator) =
        valueNumerator * innerDenominator := by
      rw [_root_.mul_assoc, Gaussian.Field.inv_eq, Gaussian.Field.inv_mul _ combinedNonzero,
        Gaussian.Basic.mul_one]
    _ = (valueNumerator * outerDenominator⁻¹) *
        (outerDenominator * innerDenominator) := by
      symm
      calc
        (valueNumerator * outerDenominator⁻¹) *
            (outerDenominator * innerDenominator) =
            (valueNumerator *
                (outerDenominator⁻¹ * outerDenominator)) *
              innerDenominator :=
          Gaussian.Basic.mul_pair_reassociate valueNumerator outerDenominator⁻¹
            outerDenominator innerDenominator
        _ = valueNumerator * innerDenominator := by
          rw [Gaussian.Field.inv_eq, Gaussian.Field.inv_mul _ leftDenominator,
            Gaussian.Basic.mul_one]
end Composition
end Purelib.Geometry.Projective.Homography
