module

public import Purelib.Polynomial.Power.Gaussian
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring

/-! # Measured imaginary separation for power polynomials -/

public section

namespace Purelib.Polynomial.Power.Gaussian.Reality

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- The original box endpoints compute a lower bound for the cubic imaginary factor. -/
@[expose] def cubicGap (box : Box) : Rational :=
  3 * box.xLower ^ 2 - max (box.yLower ^ 2) (box.yUpper ^ 2)

/-- Every point in a nonnegative real-coordinate box obeys its same computed cubic gap. -/
theorem cubicGap_le {box : Box} (nonnegative : 0 ≤ box.xLower) {point : Canonical}
    (inside : box.Contains point) : cubicGap box ≤ 3 * point.re ^ 2 - point.im ^ 2 := by
  have realSquare := Arithmetic.pow_le_pow_direct nonnegative inside.1 2
  have imaginarySquare := Box.sq_le_endpoint_max inside.2.2.1 inside.2.2.2
  exact Arithmetic.sub_le_sub_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct realSquare (by decide)) imaginarySquare

/-- A positive lower bound on the cubic imaginary factor controls distance to the actual conjugate.

The bound concerns the displayed power-polynomial evaluation at the same
Gaussian point. The positive gap permits exact rational cancellation; no
sample is assumed to be an exact root.
-/
theorem cubic_conjugate_bound (parameter : Rational) (point : Canonical) (gap : Rational)
    (positive : 0 < gap) (factor : gap ≤ 3 * point.re ^ 2 - point.im ^ 2) :
    normSq (point - point.conj) ≤ (4 / gap ^ 2) *
      normSq ((rootPolynomial ⟨parameter, 0⟩ ⟨3, by decide⟩).eval point) := by
  let value := (rootPolynomial ⟨parameter, 0⟩ ⟨3, by decide⟩).eval point
  have imaginary : value.im = point.im * (3 * point.re ^ 2 - point.im ^ 2) := by
    dsimp only [value]
    rewrite [rootPolynomial_eval]
    change (point ^ 3 - (⟨parameter, 0⟩ : Canonical)).im = _
    rewrite [pow_succ, pow_two]
    change ((point * point * point - ⟨parameter, 0⟩) : Canonical).im = _
    simp only [Purelib.Data.Gaussian.Basic.sub_im, Purelib.Data.Gaussian.Basic.mul_im,
      Purelib.Data.Gaussian.Basic.mul_re]
    ring1
  have factorSquare := Arithmetic.pow_le_pow_direct positive.le factor 2
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct factorSquare
    (Arithmetic.sq_nonneg_direct point.im)
  have imaginaryBound : point.im ^ 2 * gap ^ 2 ≤ normSq value := by
    calc
      point.im ^ 2 * gap ^ 2 ≤ point.im ^ 2 * (3 * point.re ^ 2 - point.im ^ 2) ^ 2 := scaled
      _ = value.im ^ 2 := by rewrite [imaginary]; ring1
      _ ≤ normSq value := by
        rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical]
        rewrite [pow_two]
        change value.im * value.im ≤ value.re * value.re + value.im * value.im
        have bound := Arithmetic.add_le_add_direct (Arithmetic.sq_nonneg_direct value.re)
          (le_refl (value.im ^ 2))
        rewrite [Purelib.Data.Rat.Fraction.zero_add, pow_two, pow_two] at bound
        exact bound
  have gapSquarePositive := Arithmetic.pow_pos_direct positive 2
  have gapSquareNonzero : gap ^ 2 ≠ 0 := ne_of_gt gapSquarePositive
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := gap ^ 2) _ gapSquarePositive
  calc
    normSq (point - point.conj) * gap ^ 2 = 4 * (point.im ^ 2 * gap ^ 2) := by
      rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      change ((point.re - point.re) * (point.re - point.re) +
        (point.im - -point.im) * (point.im - -point.im)) * gap ^ 2 = _
      ring1
    _ ≤ 4 * normSq value := Arithmetic.mul_le_mul_of_nonneg_left_direct imaginaryBound (by decide)
    _ = ((4 / gap ^ 2) * normSq value) * gap ^ 2 := by
      calc
        4 * normSq value = ((4 / gap ^ 2) * gap ^ 2) * normSq value := by
          rewrite [Field.div_mul_cancel_of_ne 4 (gap ^ 2) gapSquareNonzero]
          rfl
        _ = _ := by ring1

/-- A positive computed gap in the actual box gives the same cubic conjugacy bound throughout that box. -/
theorem cubic_box_conjugate_bound (parameter : Rational) (box : Box)
    (nonnegative : 0 ≤ box.xLower) (positive : 0 < cubicGap box) {point : Canonical}
    (inside : box.Contains point) : normSq (point - point.conj) ≤ (4 / cubicGap box ^ 2) *
      normSq ((rootPolynomial ⟨parameter, 0⟩ ⟨3, by decide⟩).eval point) :=
  cubic_conjugate_bound parameter point (cubicGap box) positive (cubicGap_le nonnegative inside)

/-- The original lower real endpoint computes the quadratic imaginary-factor gap. -/
@[expose] def quadraticGap (box : Box) : Rational := 2 * box.xLower

/-- Every point of the same original box satisfies its computed quadratic gap. -/
theorem quadraticGap_le {box : Box} {point : Canonical} (inside : box.Contains point) :
    quadraticGap box ≤ 2 * point.re :=
  Arithmetic.mul_le_mul_of_nonneg_left_direct inside.1 (by decide)

/-- A positive lower bound on the quadratic imaginary factor controls distance to the actual conjugate.

The bound concerns the displayed power-polynomial evaluation at the same
Gaussian point. The positive gap permits exact rational cancellation; no
sample is assumed to be an exact root.
-/
theorem quadratic_conjugate_bound (parameter : Rational) (point : Canonical) (gap : Rational)
    (positive : 0 < gap) (factor : gap ≤ 2 * point.re) :
    normSq (point - point.conj) ≤ (4 / gap ^ 2) *
      normSq ((rootPolynomial ⟨parameter, 0⟩ ⟨2, by decide⟩).eval point) := by
  let value := (rootPolynomial ⟨parameter, 0⟩ ⟨2, by decide⟩).eval point
  have imaginary : value.im = point.im * (2 * point.re) := by
    dsimp only [value]
    rewrite [rootPolynomial_eval]
    change (point ^ 2 - (⟨parameter, 0⟩ : Canonical)).im = _
    rewrite [pow_two]
    change ((point * point - ⟨parameter, 0⟩) : Canonical).im = _
    simp only [Purelib.Data.Gaussian.Basic.sub_im, Purelib.Data.Gaussian.Basic.mul_im]
    ring1
  have factorSquare := Arithmetic.pow_le_pow_direct positive.le factor 2
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct factorSquare
    (Arithmetic.sq_nonneg_direct point.im)
  have imaginaryBound : point.im ^ 2 * gap ^ 2 ≤ normSq value := by
    calc
      point.im ^ 2 * gap ^ 2 ≤ point.im ^ 2 * (2 * point.re) ^ 2 := scaled
      _ = value.im ^ 2 := by rewrite [imaginary]; ring1
      _ ≤ normSq value := by
        rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical]
        rewrite [pow_two]
        change value.im * value.im ≤ value.re * value.re + value.im * value.im
        have bound := Arithmetic.add_le_add_direct (Arithmetic.sq_nonneg_direct value.re)
          (le_refl (value.im ^ 2))
        rewrite [Purelib.Data.Rat.Fraction.zero_add, pow_two, pow_two] at bound
        exact bound
  have gapSquarePositive := Arithmetic.pow_pos_direct positive 2
  have gapSquareNonzero : gap ^ 2 ≠ 0 := ne_of_gt gapSquarePositive
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := gap ^ 2) _ gapSquarePositive
  calc
    normSq (point - point.conj) * gap ^ 2 = 4 * (point.im ^ 2 * gap ^ 2) := by
      rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      change ((point.re - point.re) * (point.re - point.re) +
        (point.im - -point.im) * (point.im - -point.im)) * gap ^ 2 = _
      ring1
    _ ≤ 4 * normSq value := Arithmetic.mul_le_mul_of_nonneg_left_direct imaginaryBound (by decide)
    _ = ((4 / gap ^ 2) * normSq value) * gap ^ 2 := by
      calc
        4 * normSq value = ((4 / gap ^ 2) * gap ^ 2) * normSq value := by
          rewrite [Field.div_mul_cancel_of_ne 4 (gap ^ 2) gapSquareNonzero]
          rfl
        _ = _ := by ring1

/-- A positive computed quadratic gap controls conjugacy throughout the same original box. -/
theorem quadratic_box_conjugate_bound (parameter : Rational) (box : Box)
    (positive : 0 < quadraticGap box) {point : Canonical} (inside : box.Contains point) :
    normSq (point - point.conj) ≤ (4 / quadraticGap box ^ 2) *
      normSq ((rootPolynomial ⟨parameter, 0⟩ ⟨2, by decide⟩).eval point) :=
  quadratic_conjugate_bound parameter point (quadraticGap box) positive (quadraticGap_le inside)

end Purelib.Polynomial.Power.Gaussian.Reality

end
