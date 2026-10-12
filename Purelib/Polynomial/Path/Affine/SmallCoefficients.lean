module
import Purelib.Data.List.DropWhile.Basic
import Purelib.Tactic.Ring

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine

/-!
# Affine multiplication of short Gaussian coefficient tables

The supplied nonzero origin, direction and leading coefficient retain each
one-, two-, three- or four-entry table through normalization. Multiplying by
the line appends one degree and preserves the displayed coefficient order.
-/

public section

namespace Purelib.Polynomial.Path.Affine.SmallCoefficients

open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Polynomial

/-- The exact coefficient table after multiplying a 4-coefficient Gaussian polynomial by an affine line.

The origin, direction and leading coefficient are nonzero, so no leading coefficient is removed by normalization. -/
theorem mulLine_four_coeffs
    (origin direction a b c d : Gaussian.Basic.Canonical)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0)
    (leadingNonzero : a ≠ 0) (p : Dense.Gaussian.Basic.GaussianPolynomial)
    (coeffs : p.coeffs = [a, b, c, d]) :
    (Dense.Gaussian.Substitution.Affine.mulLine origin direction p).coeffs =
      [direction * a, direction * b + origin * a,
        direction * c + origin * b, direction * d + origin * c,
          origin * d] := by
  unfold Dense.Gaussian.Substitution.Affine.mulLine
  have normalized : p.normalize.coeffs = [a, b, c, d] := by
    rw [Dense.Basic.DensePolynomial.normalize_coeffs, coeffs]
    exact DropWhile.cons_of_false (fun value => decide (value = 0)) a
      [b, c, d] (decide_eq_false leadingNonzero)
  let originScaled : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical :=
    ⟨[origin * a, origin * b, origin * c, origin * d]⟩
  let directionScaled : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical :=
    ⟨[direction * a, direction * b, direction * c, direction * d]⟩
  have originScaleEq : Dense.Basic.DensePolynomial.scale origin p = originScaled := by
    apply Dense.Basic.DensePolynomial.ext
    rw [Dense.Basic.DensePolynomial.scale_coeffs_of_ne_zero originNonzero, normalized]
    rfl
  have directionScaleEq : Dense.Basic.DensePolynomial.scale direction p = directionScaled := by
    apply Dense.Basic.DensePolynomial.ext
    rw [Dense.Basic.DensePolynomial.scale_coeffs_of_ne_zero directionNonzero, normalized]
    rfl
  rw [originScaleEq, directionScaleEq]
  have leadingProduct : direction * a ≠ 0 :=
    Dense.Basic.DensePolynomial.mul_ne_zero_direct directionNonzero leadingNonzero
  have directionNormalized : directionScaled.normalize = directionScaled := by
    apply Dense.Basic.DensePolynomial.ext
    exact DropWhile.cons_of_false (fun value => decide (value = 0))
      (direction * a) [direction * b, direction * c, direction * d] (decide_eq_false leadingProduct)
  unfold Dense.Basic.DensePolynomial.shift
  rw [Dense.Basic.DensePolynomial.isZero, directionNormalized]
  change ([0 + direction * a, origin * a + direction * b, origin * b + direction * c, origin * c + direction * d, origin
    * d + 0].dropWhile (fun value => decide (value = 0))) = _
  rw [Gaussian.Basic.Canonical.zero_add,
    show origin * d + 0 = origin * d by ring1,
    DropWhile.cons_of_false (fun value => decide (value = 0))
      (direction * a) [origin * a + direction * b, origin * b + direction * c, origin * c + direction * d, origin * d]
      (decide_eq_false leadingProduct)]
  rw [show origin * a + direction * b =
        direction * b + origin * a by ring1,
    show origin * b + direction * c =
        direction * c + origin * b by ring1,
    show origin * c + direction * d =
        direction * d + origin * c by ring1]

/-- The exact coefficient table after multiplying a 3-coefficient Gaussian polynomial by an affine line.

The origin, direction and leading coefficient are nonzero, so no leading coefficient is removed by normalization. -/
theorem mulLine_three_coeffs
    (origin direction a b c : Gaussian.Basic.Canonical)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0)
    (leadingNonzero : a ≠ 0) (p : Dense.Gaussian.Basic.GaussianPolynomial)
    (coeffs : p.coeffs = [a, b, c]) :
    (Dense.Gaussian.Substitution.Affine.mulLine origin direction p).coeffs =
      [direction * a, direction * b + origin * a,
        direction * c + origin * b, origin * c] := by
  unfold Dense.Gaussian.Substitution.Affine.mulLine
  have normalized : p.normalize.coeffs = [a, b, c] := by
    rw [Dense.Basic.DensePolynomial.normalize_coeffs, coeffs]
    exact DropWhile.cons_of_false (fun value => decide (value = 0)) a
      [b, c] (decide_eq_false leadingNonzero)
  let originScaled : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical :=
    ⟨[origin * a, origin * b, origin * c]⟩
  let directionScaled : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical :=
    ⟨[direction * a, direction * b, direction * c]⟩
  have originScaleEq : Dense.Basic.DensePolynomial.scale origin p = originScaled := by
    apply Dense.Basic.DensePolynomial.ext
    rw [Dense.Basic.DensePolynomial.scale_coeffs_of_ne_zero originNonzero, normalized]
    rfl
  have directionScaleEq : Dense.Basic.DensePolynomial.scale direction p = directionScaled := by
    apply Dense.Basic.DensePolynomial.ext
    rw [Dense.Basic.DensePolynomial.scale_coeffs_of_ne_zero directionNonzero, normalized]
    rfl
  rw [originScaleEq, directionScaleEq]
  have leadingProduct : direction * a ≠ 0 :=
    Dense.Basic.DensePolynomial.mul_ne_zero_direct directionNonzero leadingNonzero
  have directionNormalized : directionScaled.normalize = directionScaled := by
    apply Dense.Basic.DensePolynomial.ext
    exact DropWhile.cons_of_false (fun value => decide (value = 0))
      (direction * a) [direction * b, direction * c] (decide_eq_false leadingProduct)
  unfold Dense.Basic.DensePolynomial.shift
  rw [Dense.Basic.DensePolynomial.isZero, directionNormalized]
  change ([0 + direction * a, origin * a + direction * b, origin * b + direction * c, origin * c + 0].dropWhile (fun
    value => decide (value = 0))) = _
  rw [Gaussian.Basic.Canonical.zero_add,
    show origin * c + 0 = origin * c by ring1,
    DropWhile.cons_of_false (fun value => decide (value = 0))
      (direction * a) [origin * a + direction * b, origin * b + direction * c, origin * c]
      (decide_eq_false leadingProduct)]
  rw [show origin * a + direction * b =
        direction * b + origin * a by ring1,
    show origin * b + direction * c =
        direction * c + origin * b by ring1]

/-- The exact coefficient table after multiplying a 1-coefficient Gaussian polynomial by an affine line.

The origin, direction and leading coefficient are nonzero, so no leading coefficient is removed by normalization. -/
theorem mulLine_one_coeff
    (origin direction a : Gaussian.Basic.Canonical)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0)
    (leadingNonzero : a ≠ 0) (p :
      Dense.Gaussian.Basic.ExplicitQuarticPreparedHorizontalCells.HorizontalGaussianPolynomial)
    (coeffs : p.coeffs = [a]) :
    (Dense.Gaussian.Substitution.Affine.mulLine origin direction p).coeffs =
      [direction * a, origin * a] := by
  unfold Dense.Gaussian.Substitution.Affine.mulLine
  have normalized : p.normalize.coeffs = [a] := by
    rw [Dense.Basic.DensePolynomial.normalize_coeffs, coeffs]
    exact DropWhile.cons_of_false (fun value => decide (value = 0)) a
      [] (decide_eq_false leadingNonzero)
  let originScaled : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical :=
    ⟨[origin * a]⟩
  let directionScaled : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical :=
    ⟨[direction * a]⟩
  have originScaleEq : Dense.Basic.DensePolynomial.scale origin p = originScaled := by
    apply Dense.Basic.DensePolynomial.ext
    rw [Dense.Basic.DensePolynomial.scale_coeffs_of_ne_zero originNonzero, normalized]
    rfl
  have directionScaleEq : Dense.Basic.DensePolynomial.scale direction p = directionScaled := by
    apply Dense.Basic.DensePolynomial.ext
    rw [Dense.Basic.DensePolynomial.scale_coeffs_of_ne_zero directionNonzero, normalized]
    rfl
  rw [originScaleEq, directionScaleEq]
  have leadingProduct : direction * a ≠ 0 :=
    Dense.Basic.DensePolynomial.mul_ne_zero_direct directionNonzero leadingNonzero
  have directionNormalized : directionScaled.normalize = directionScaled := by
    apply Dense.Basic.DensePolynomial.ext
    exact DropWhile.cons_of_false (fun value => decide (value = 0))
      (direction * a) [] (decide_eq_false leadingProduct)
  unfold Dense.Basic.DensePolynomial.shift
  rw [Dense.Basic.DensePolynomial.isZero, directionNormalized]
  change ([0 + direction * a, origin * a + 0].dropWhile (fun value => decide (value = 0))) = _
  rw [Gaussian.Basic.Canonical.zero_add,
    show origin * a + 0 = origin * a by ring1,
    DropWhile.cons_of_false (fun value => decide (value = 0))
      (direction * a) [origin * a]
      (decide_eq_false leadingProduct)]

/-- The exact coefficient table after multiplying a 2-coefficient Gaussian polynomial by an affine line.

The origin, direction and leading coefficient are nonzero, so no leading coefficient is removed by normalization. -/
theorem mulLine_two_coeffs
    (origin direction a b : Gaussian.Basic.Canonical)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0)
    (leadingNonzero : a ≠ 0) (p :
      Dense.Gaussian.Basic.ExplicitQuarticPreparedHorizontalCells.HorizontalGaussianPolynomial)
    (coeffs : p.coeffs = [a, b]) :
    (Dense.Gaussian.Substitution.Affine.mulLine origin direction p).coeffs =
      [direction * a, direction * b + origin * a, origin * b] := by
  unfold Dense.Gaussian.Substitution.Affine.mulLine
  have normalized : p.normalize.coeffs = [a, b] := by
    rw [Dense.Basic.DensePolynomial.normalize_coeffs, coeffs]
    exact DropWhile.cons_of_false (fun value => decide (value = 0)) a
      [b] (decide_eq_false leadingNonzero)
  let originScaled : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical :=
    ⟨[origin * a, origin * b]⟩
  let directionScaled : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical :=
    ⟨[direction * a, direction * b]⟩
  have originScaleEq : Dense.Basic.DensePolynomial.scale origin p = originScaled := by
    apply Dense.Basic.DensePolynomial.ext
    rw [Dense.Basic.DensePolynomial.scale_coeffs_of_ne_zero originNonzero, normalized]
    rfl
  have directionScaleEq : Dense.Basic.DensePolynomial.scale direction p = directionScaled := by
    apply Dense.Basic.DensePolynomial.ext
    rw [Dense.Basic.DensePolynomial.scale_coeffs_of_ne_zero directionNonzero, normalized]
    rfl
  rw [originScaleEq, directionScaleEq]
  have leadingProduct : direction * a ≠ 0 :=
    Dense.Basic.DensePolynomial.mul_ne_zero_direct directionNonzero leadingNonzero
  have directionNormalized : directionScaled.normalize = directionScaled := by
    apply Dense.Basic.DensePolynomial.ext
    exact DropWhile.cons_of_false (fun value => decide (value = 0))
      (direction * a) [direction * b] (decide_eq_false leadingProduct)
  unfold Dense.Basic.DensePolynomial.shift
  rw [Dense.Basic.DensePolynomial.isZero, directionNormalized]
  change ([0 + direction * a, origin * a + direction * b, origin * b + 0].dropWhile (fun value => decide (value = 0))) =
    _
  rw [Gaussian.Basic.Canonical.zero_add,
    show origin * b + 0 = origin * b by ring1,
    DropWhile.cons_of_false (fun value => decide (value = 0))
      (direction * a) [origin * a + direction * b, origin * b]
      (decide_eq_false leadingProduct)]
  rw [show origin * a + direction * b =
        direction * b + origin * a by ring1]

end Purelib.Polynomial.Path.Affine.SmallCoefficients
