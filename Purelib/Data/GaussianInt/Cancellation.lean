module

import Purelib.Data.Gaussian.Field
public import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Int.Arithmetic
import Purelib.Tactic.Ring

/-!
# Cancellation in Gaussian integers

The displayed integral norm detects zero factors. The original coordinatewise
subtraction and rational embedding provide cancellation of nonzero factors.
-/

namespace Purelib.Data.GaussianInt

open Purelib.Data
open Purelib.Data.Gaussian

public section

/-- A zero product of Gaussian integers has a zero factor.

Multiplicativity and definiteness of the displayed integral norm reduce the product
equality to the corresponding property of integer multiplication. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero {z w : GaussianInt}
    (productZero : z * w = 0) : z = 0 ∨ w = 0 := by
  have normProduct : GaussianInt.normInt z * GaussianInt.normInt w = 0 := by
    rw [← normInt_mul, productZero]
    rfl
  rcases Int.Arithmetic.eq_zero_of_mul_eq_zero normProduct with leftZero | rightZero
  · exact Or.inl (normInt_eq_zero.mp leftZero)
  · exact Or.inr (normInt_eq_zero.mp rightZero)

/-- A product of two nonzero Gaussian integers is nonzero.

The zero-factor certificate would force one of the two retained factors to
vanish, contradicting its supplied nonzero evidence. -/
theorem mul_ne_zero {z w : GaussianInt} (leftNonzero : z ≠ 0)
    (rightNonzero : w ≠ 0) : z * w ≠ 0 := by
  intro productZero
  rcases eq_zero_or_eq_zero_of_mul_eq_zero productZero with
    leftZero | rightZero
  · exact leftNonzero leftZero
  · exact rightNonzero rightZero

/-- A zero Gaussian-integer difference identifies its two retained inputs.

Coordinate subtraction reduces the claim to the original integer addition laws;
no generic subtraction-group proof dictionary is needed.
-/
theorem eq_of_sub_eq_zero {left right : GaussianInt}
    (differenceZero : left - right = 0) : left = right := by
  apply GaussianInt.ext
  · have coordinateZero := congrArg (fun value => value.re) differenceZero
    change left.re - right.re = 0 at coordinateZero
    have recovered : (left.re - right.re) + right.re = left.re := by ring1
    rewrite [coordinateZero, Int.Arithmetic.zero_add] at recovered
    exact recovered.symm
  · have coordinateZero := congrArg (fun value => value.im) differenceZero
    change left.im - right.im = 0 at coordinateZero
    have recovered : (left.im - right.im) + right.im = left.im := by ring1
    rewrite [coordinateZero, Int.Arithmetic.zero_add] at recovered
    exact recovered.symm

/-- Cancel an explicitly nonzero common right factor from a Gaussian-integer equality.

The difference has zero product with the retained factor; the zero-factor property
forces both coordinates of that difference to vanish. -/
theorem mul_right_cancel_of_ne {x y z : GaussianInt} (zNonzero : z ≠ 0)
    (productsEqual : x * z = y * z) : x = y := by
  have differenceProduct : (x - y) * z = 0 := by
    rw [sub_eq_add_neg]
    calc
      (x + -y) * z = x * z + (-y) * z := by ring1
      _ = y * z + (-y) * z := by rw [productsEqual]
      _ = 0 := by ring1
  rcases eq_zero_or_eq_zero_of_mul_eq_zero differenceProduct with
    differenceZero | zZero
  · apply GaussianInt.ext
    · have coordinateZero := congrArg (fun value => value.re) differenceZero
      simp only [GaussianInt.sub_re, zero_re] at coordinateZero
      have recovered : (x.re - y.re) + y.re = x.re := by ring1
      rewrite [coordinateZero, Int.Arithmetic.zero_add] at recovered
      exact recovered.symm
    · have coordinateZero := congrArg (fun value => value.im) differenceZero
      simp only [GaussianInt.sub_im, zero_im] at coordinateZero
      have recovered : (x.im - y.im) + y.im = x.im := by ring1
      rewrite [coordinateZero, Int.Arithmetic.zero_add] at recovered
      exact recovered.symm
  · exact (zNonzero zZero).elim

namespace Cancellation

/-- Cancel a nonzero right Gaussian-integer factor using the retained coordinate product.

The original integral embedding alias names the same Gaussian-integer carrier.
Cancellation uses the zero-factor norm certificate and coordinate subtraction. -/
theorem mul_right_cancel_of_nonzero {left right factor : Embedding.Integer}
    (factorNonzero : factor ≠ 0)
    (identity : left * factor = right * factor) : left = right :=
  GaussianInt.mul_right_cancel_of_ne factorNonzero identity

/-- Cancel a nonzero left Gaussian-integer factor through its injective rational embedding.

The original embedding carries the product equation and detects the retained
nonzero factor. Rational Gaussian cancellation then identifies both inputs. -/
theorem mul_left_cancel_of_nonzero
    {factor left right : GaussianInt} (factorNonzero : factor ≠ 0)
    (identity : factor * left = factor * right) : left = right := by
  apply GaussianInt.toGaussian_injective
  have embedded := congrArg GaussianInt.toGaussian identity
  rw [GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul] at embedded
  have factorGaussianNonzero : GaussianInt.toGaussian factor ≠ 0 := by
    intro zero
    exact factorNonzero (toGaussian_eq_zero.mp zero)
  apply Gaussian.Field.mul_right_cancel_of_ne
    factorGaussianNonzero
  simpa only [Gaussian.Basic.mul_comm] using embedded

end Cancellation

end

end Purelib.Data.GaussianInt
