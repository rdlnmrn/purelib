module

public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Data.Rat.Interval.Arithmetic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Computed local separation for real even quartic polynomials -/

public section

namespace Purelib.Polynomial.Dense.Gaussian.EvenQuartic

open Purelib.Data.Gaussian.Basic (mul_re mul_im add_re add_im sub_re sub_im)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat (Interval)
open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- The original descending coefficients of the real even quartic `Z⁴ - a Z² + b`. -/
@[expose] def polynomial (a b : Rational) : CoefficientPolynomial :=
  ⟨[1, 0, ⟨-a, 0⟩, 0, ⟨b, 0⟩]⟩

/-- The original even quartic has degree four for every retained coefficient pair. -/
theorem degree (a b : Rational) : (polynomial a b).natDegree = 4 := by
  change ([1, 0, (⟨-a, 0⟩ : Canonical), 0, ⟨b, 0⟩].dropWhile (fun value => decide (value = 0))).length - 1 = 4
  rfl

/-- The retained coefficient table evaluates to its displayed scalar quartic. -/
theorem eval (a b : Rational) (point : Canonical) :
    (polynomial a b).eval point = point ^ 4 - ⟨a, 0⟩ * point ^ 2 + ⟨b, 0⟩ := by
  change ((((0 * point + 1) * point + 0) * point + ⟨-a, 0⟩) * point + 0) * point + ⟨b, 0⟩ = _
  have negative : (⟨-a, 0⟩ : Canonical) = -⟨a, 0⟩ := by
    change (⟨-a, 0⟩ : Canonical) = ⟨-a, -(0 : Rational)⟩
    rewrite [show -(0 : Rational) = 0 by decide]
    rfl
  rewrite [negative]
  ring1

/-- The exact divided-difference factor of the same two quartic evaluations. -/
@[expose] def factor (a : Rational) (left right : Canonical) : Canonical :=
  (left + right) * (left ^ 2 + right ^ 2 - ⟨a, 0⟩)

/-- The displayed factor multiplies the original point difference to the same polynomial difference. -/
theorem difference (a b : Rational) (left right : Canonical) :
    (polynomial a b).eval left - (polynomial a b).eval right = (left - right) * factor a left right := by
  rewrite [eval, eval]
  unfold factor
  ring1

/-- The real-coordinate interval uses the same original box endpoints. -/
@[expose] def realInterval (box : Box) : Bounds := ⟨box.xLower, box.xUpper, box.x_valid⟩

/-- The imaginary-coordinate interval uses the same original box endpoints. -/
@[expose] def imaginaryInterval (box : Box) : Bounds := ⟨box.yLower, box.yUpper, box.y_valid⟩

/-- The original box intervals compute an enclosure of the real coordinate of a squared point. -/
@[expose] def squareReal (box : Box) : Bounds :=
  Interval.Arithmetic.sub (Interval.Arithmetic.mul (realInterval box) (realInterval box))
    (Interval.Arithmetic.mul (imaginaryInterval box) (imaginaryInterval box))

/-- The original box intervals compute an enclosure of the imaginary coordinate of a squared point. -/
@[expose] def squareImaginary (box : Box) : Bounds :=
  Interval.Arithmetic.scale 2 (Interval.Arithmetic.mul (realInterval box) (imaginaryInterval box))

/-- Both actual boxes compute an interval enclosing the real divided-difference factor.

Every interval operation consumes their original rational endpoints. Its lower
endpoint is a sufficient local separation gap; failure to make it positive
asserts no polynomial collision.
-/
@[expose] def factorBounds (a : Rational) (left right : Box) : Bounds :=
  Interval.Arithmetic.sub
    (Interval.Arithmetic.mul (Interval.Arithmetic.add (realInterval left) (realInterval right))
      (Interval.Arithmetic.sub (Interval.Arithmetic.add (squareReal left) (squareReal right))
        (Interval.Arithmetic.constant a)))
    (Interval.Arithmetic.mul (Interval.Arithmetic.add (imaginaryInterval left) (imaginaryInterval right))
      (Interval.Arithmetic.add (squareImaginary left) (squareImaginary right)))

/-- Every pair in the same actual boxes obeys their computed divided-difference interval. -/
theorem factorBounds_contains (a : Rational) {leftBox rightBox : Box} {left right : Canonical}
    (leftInside : leftBox.Contains left) (rightInside : rightBox.Contains right) :
    (factorBounds a leftBox rightBox).Contains (factor a left right).re := by
  have leftReal : (realInterval leftBox).Contains left.re := ⟨leftInside.1, leftInside.2.1⟩
  have leftImaginary : (imaginaryInterval leftBox).Contains left.im := ⟨leftInside.2.2.1, leftInside.2.2.2⟩
  have rightReal : (realInterval rightBox).Contains right.re := ⟨rightInside.1, rightInside.2.1⟩
  have rightImaginary : (imaginaryInterval rightBox).Contains right.im := ⟨rightInside.2.2.1, rightInside.2.2.2⟩
  have leftSquareReal := Interval.Arithmetic.sub_contains
    (Interval.Arithmetic.mul_contains _ _ leftReal leftReal)
    (Interval.Arithmetic.mul_contains _ _ leftImaginary leftImaginary)
  have rightSquareReal := Interval.Arithmetic.sub_contains
    (Interval.Arithmetic.mul_contains _ _ rightReal rightReal)
    (Interval.Arithmetic.mul_contains _ _ rightImaginary rightImaginary)
  have leftSquareImaginary := Interval.Arithmetic.scale_contains 2 _
    (Interval.Arithmetic.mul_contains _ _ leftReal leftImaginary)
  have rightSquareImaginary := Interval.Arithmetic.scale_contains 2 _
    (Interval.Arithmetic.mul_contains _ _ rightReal rightImaginary)
  have result := Interval.Arithmetic.sub_contains
    (Interval.Arithmetic.mul_contains _ _ (Interval.Arithmetic.add_contains _ _ leftReal rightReal)
      (Interval.Arithmetic.sub_contains (Interval.Arithmetic.add_contains _ _ leftSquareReal rightSquareReal)
        (show (Interval.Arithmetic.constant a).Contains a from ⟨le_refl _, le_refl _⟩)))
    (Interval.Arithmetic.mul_contains _ _ (Interval.Arithmetic.add_contains _ _ leftImaginary rightImaginary)
      (Interval.Arithmetic.add_contains _ _ leftSquareImaginary rightSquareImaginary))
  have reading : (factor a left right).re =
      (left.re + right.re) * ((left.re * left.re - left.im * left.im) +
        (right.re * right.re - right.im * right.im) - a) -
        (left.im + right.im) * (2 * (left.re * left.im) + 2 * (right.re * right.im)) := by
    unfold factor
    rewrite [pow_two, pow_two]
    simp only [mul_re, mul_im,
      add_re, add_im,
      sub_re, sub_im]
    ring1
  rewrite [reading]
  exact result

/-- A positive computed box gap bounds the original point difference by the same quartic residual difference. -/
theorem normSq_difference_le (a b : Rational) {leftBox rightBox : Box}
    (positive : 0 < (factorBounds a leftBox rightBox).lower) {left right : Canonical}
    (leftInside : leftBox.Contains left) (rightInside : rightBox.Contains right) :
    normSq (left - right) ≤ (1 / (factorBounds a leftBox rightBox).lower ^ 2) *
      normSq ((polynomial a b).eval left - (polynomial a b).eval right) := by
  let gap := (factorBounds a leftBox rightBox).lower
  have realLower := (factorBounds_contains a leftInside rightInside).1
  have square := Arithmetic.pow_le_pow_direct positive.le realLower 2
  have factorLower : gap ^ 2 ≤ normSq (factor a left right) := by
    apply square.trans
    rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    have sum := Arithmetic.add_le_add_direct (le_refl ((factor a left right).re ^ 2))
      (Arithmetic.sq_nonneg_direct (factor a left right).im)
    have zeroSum : (factor a left right).re ^ 2 + 0 = (factor a left right).re ^ 2 := by ring1
    rewrite [zeroSum, pow_two, pow_two] at sum
    rewrite [pow_two]
    exact sum
  have multiplied := Arithmetic.mul_le_mul_of_nonneg_left_direct factorLower
    (Purelib.Data.Gaussian.Norm.Basic.normSq_nonneg (left - right))
  have gapPositive := Arithmetic.pow_pos_direct positive 2
  have gapNonzero : gap ^ 2 ≠ 0 := ne_of_gt gapPositive
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := gap ^ 2) _ gapPositive
  calc
    normSq (left - right) * gap ^ 2 ≤ normSq (left - right) * normSq (factor a left right) := multiplied
    _ = normSq ((polynomial a b).eval left - (polynomial a b).eval right) := by
      rewrite [difference, Purelib.Data.Gaussian.Norm.Basic.normSq_mul]
      rfl
    _ = ((1 / gap ^ 2) * normSq ((polynomial a b).eval left - (polynomial a b).eval right)) * gap ^ 2 := by
      calc
        _ = ((1 / gap ^ 2) * gap ^ 2) * normSq
            ((polynomial a b).eval left - (polynomial a b).eval right) := by
          rewrite [Field.div_mul_cancel_of_ne 1 (gap ^ 2) gapNonzero]
          ring1
        _ = _ := by ring1

end Purelib.Polynomial.Dense.Gaussian.EvenQuartic

end
