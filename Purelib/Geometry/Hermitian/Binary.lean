module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Int.Order
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Data

open Purelib.Data.Rat

section
@[expose] public section

/-!
# The finite Lakein inequality for Hurwitz convergents

This module closes the last exceptional coefficient case left by the elementary
Hurwitz-square geometry.  The normalized adjacent-denominator ratio is an
explicit Gaussian rational.  Its finite laws of succession keep it in
`[-3/4, 3/4]²`; that coordinate certificate excludes every quadrance-five
current coefficient paired with a diagonal previous coefficient.
-/

namespace Purelib.Geometry.Hermitian.Binary

/-- A displayed binary Hermitian form. The four scalar coefficients are rational, so transformations of the form are
finite ring calculations. -/
def hermitianForm (constant radial realCross imaginaryCross :
  Fraction.Rational)
    (value : Data.Gaussian.Basic.Canonical) : Fraction.Rational :=
  constant + radial * Data.Gaussian.Norm.Basic.normSq value +
    2 * (realCross * value.re + imaginaryCross * value.im)

/-- A rational certificate that a binary Hermitian form is nonnegative on the closed unit disc. The identity used here
is a completed-square identity, with `slack` supplied explicitly rather than selected by an existence proof. -/
theorem hermitianForm_nonnegative_of_certificate
    (constant radial realCross imaginaryCross : Fraction.Rational)
    (value : Data.Gaussian.Basic.Canonical) (slack : Fraction.Rational)
    (valueInside : Data.Gaussian.Norm.Basic.normSq value ≤ 1)
    (slackNonnegative : 0 ≤ slack)
    (scalePositive : 0 < radial + slack)
    (determinantGap :
      0 ≤ (constant - slack) * (radial + slack) -
        (realCross ^ 2 + imaginaryCross ^ 2)) :
    0 ≤ hermitianForm constant radial realCross imaginaryCross value := by
  let scale := radial + slack
  have scaleNonnegative : 0 ≤ scale := scalePositive.le
  have discGap : 0 ≤ 1 - Data.Gaussian.Norm.Basic.normSq value :=
    Fraction.Order.Arithmetic.sub_nonneg_direct valueInside
  have scaledDiscGap :
      0 ≤ scale * slack * (1 - Data.Gaussian.Norm.Basic.normSq value) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        scaleNonnegative slackNonnegative) discGap
  have realSquare :
      0 ≤ (scale * value.re + realCross) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  have imaginarySquare :
      0 ≤ (scale * value.im + imaginaryCross) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  have certificateNonnegative :
      0 ≤
        (scale * value.re + realCross) ^ 2 +
          (scale * value.im + imaginaryCross) ^ 2 +
          scale * slack * (1 - Data.Gaussian.Norm.Basic.normSq value) +
          ((constant - slack) * scale -
            (realCross ^ 2 + imaginaryCross ^ 2)) :=
    add_nonneg
      (add_nonneg (add_nonneg realSquare imaginarySquare) scaledDiscGap)
      determinantGap
  have productNonnegative :
      0 ≤ scale *
        hermitianForm constant radial realCross imaginaryCross value := by
    calc
      0 ≤
          (scale * value.re + realCross) ^ 2 +
            (scale * value.im + imaginaryCross) ^ 2 +
            scale * slack * (1 - Data.Gaussian.Norm.Basic.normSq value) +
            ((constant - slack) * scale -
              (realCross ^ 2 + imaginaryCross ^ 2)) :=
        certificateNonnegative
      _ = scale *
          hermitianForm constant radial realCross imaginaryCross value := by
        dsimp only [scale, hermitianForm, Data.Gaussian.Norm.Basic.normSq]
        ring1
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := scale) _ scalePositive
  calc
    0 * scale = 0 := by ring1
    _ ≤ scale *
        hermitianForm constant radial realCross imaginaryCross value :=
      productNonnegative
    _ = hermitianForm constant radial realCross imaginaryCross value *
        scale := by ring1

/-- Clearing one reciprocal step transforms the displayed Hermitian form by an exact coefficient calculation. -/
theorem hermitianForm_inverse_add_mul_normSq
    (constant radial realCross imaginaryCross : Fraction.Rational)
    (coefficient : Data.GaussianInt) (value : Data.Gaussian.Basic.Canonical)
    (sumNonzero : GaussianInt.toGaussian coefficient + value ≠ 0) :
    hermitianForm constant radial realCross imaginaryCross
          ((GaussianInt.toGaussian coefficient + value)⁻¹) *
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian coefficient + value) =
      hermitianForm
        (constant * (GaussianInt.normNat coefficient : Fraction.Rational) + radial +
          2 *
            (realCross * (coefficient.re : Fraction.Rational) -
              imaginaryCross * (coefficient.im : Fraction.Rational)))
        constant
        (constant * (coefficient.re : Fraction.Rational) + realCross)
        (constant * (coefficient.im : Fraction.Rational) - imaginaryCross)
        value := by
  let sum := GaussianInt.toGaussian coefficient + value
  have normNonzero : Data.Gaussian.Norm.Basic.normSq sum ≠ 0 := by
    intro normZero
    exact sumNonzero (Data.Gaussian.Norm.Basic.normSq_eq_zero.mp normZero)
  have realCancel : sum⁻¹.re * Data.Gaussian.Norm.Basic.normSq sum = sum.re := by
    rw [Data.Gaussian.Field.inv_eq]
    change (sum.re / Data.Gaussian.Norm.Basic.normSq sum) * Data.Gaussian.Norm.Basic.normSq sum =
      sum.re
    exact Fraction.Field.div_mul_cancel_of_ne _ _ normNonzero
  have imaginaryCancel : sum⁻¹.im * Data.Gaussian.Norm.Basic.normSq sum = -sum.im := by
    rw [Data.Gaussian.Field.inv_eq]
    change ((-sum.im) / Data.Gaussian.Norm.Basic.normSq sum) * Data.Gaussian.Norm.Basic.normSq sum =
      -sum.im
    exact Fraction.Field.div_mul_cancel_of_ne _ _ normNonzero
  have inverseNormCancel : Data.Gaussian.Norm.Basic.normSq sum⁻¹ * Data.Gaussian.Norm.Basic.normSq sum
    = 1 := by
    rw [Data.Gaussian.Field.inv_eq, Data.Gaussian.Field.normSq_inv sum sumNonzero]
    calc
      (Data.Gaussian.Norm.Basic.normSq sum)⁻¹ * Data.Gaussian.Norm.Basic.normSq sum =
          Data.Gaussian.Norm.Basic.normSq sum * (Data.Gaussian.Norm.Basic.normSq sum)⁻¹ :=
        Fraction.Field.mul_comm _ _
      _ = 1 :=
        Fraction.Field.mul_inv_cancel _ normNonzero
  calc
    hermitianForm constant radial realCross imaginaryCross sum⁻¹ *
          Data.Gaussian.Norm.Basic.normSq sum =
        constant * Data.Gaussian.Norm.Basic.normSq sum + radial * (Data.Gaussian.Norm.Basic.normSq
          sum⁻¹ * Data.Gaussian.Norm.Basic.normSq sum) +
          2 *
            (realCross * (sum⁻¹.re * Data.Gaussian.Norm.Basic.normSq sum) +
              imaginaryCross * (sum⁻¹.im * Data.Gaussian.Norm.Basic.normSq sum)) := by
      dsimp only [hermitianForm]
      ring1
    _ = constant * Data.Gaussian.Norm.Basic.normSq sum + radial +
          2 * (realCross * sum.re - imaginaryCross * sum.im) := by
      rw [inverseNormCancel, realCancel, imaginaryCancel]
      ring1
    _ = hermitianForm
        (constant * (GaussianInt.normNat coefficient : Fraction.Rational) + radial +
          2 *
            (realCross * (coefficient.re : Fraction.Rational) -
              imaginaryCross * (coefficient.im : Fraction.Rational)))
        constant
        (constant * (coefficient.re : Fraction.Rational) + realCross)
        (constant * (coefficient.im : Fraction.Rational) - imaginaryCross)
        value := by
      dsimp only [sum, hermitianForm]
      rw [← GaussianInt.normSq_toGaussian coefficient]
      simp only [Data.Gaussian.Norm.Basic.normSq,
        Gaussian.Basic.add_re,
        Gaussian.Basic.add_im, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      ring1

set_option genInjectivity false in
/-- Integral coefficient data for the finite Hermitian forms occurring in the Lakein recursion. -/
structure IntegralHermitianForm where
  /-- The constant integral coefficient. -/ constant : Int
  /-- The coefficient of the squared Gaussian norm. -/ radial : Int
  /-- Half the coefficient of the real coordinate. -/ realCross : Int
  /-- Half the coefficient of the imaginary coordinate. -/ imaginaryCross : Int
deriving DecidableEq

constructive_injectivity IntegralHermitianForm

/-- Evaluate the retained integral Hermitian coefficients at a Gaussian rational.

The four coefficients are cast to constructive rationals before evaluating the displayed constant, radial, and linear
terms. -/
def IntegralHermitianForm.evaluate (form :
  IntegralHermitianForm)
    (value : Data.Gaussian.Basic.Canonical) : Fraction.Rational :=
  hermitianForm (form.constant : Fraction.Rational)
    (form.radial : Fraction.Rational) (form.realCross : Fraction.Rational)
    (form.imaginaryCross : Fraction.Rational) value

/-- Exact integral pullback of a Hermitian form through `z ↦ (a+z)⁻¹`. -/
def IntegralHermitianForm.pullback (form :
  IntegralHermitianForm)
    (coefficient : Data.GaussianInt) : IntegralHermitianForm :=
  { constant :=
      form.constant * GaussianInt.normInt coefficient + form.radial +
        2 * (form.realCross * coefficient.re -
          form.imaginaryCross * coefficient.im)
    radial := form.constant
    realCross := form.constant * coefficient.re + form.realCross
    imaginaryCross := form.constant * coefficient.im - form.imaginaryCross }

/-- The integral Hermitian determinant `constant * radial - realCross² - imaginaryCross²`. -/
def IntegralHermitianForm.determinant (form :
  IntegralHermitianForm) : Int :=
  form.constant * form.radial -
    (form.realCross * form.realCross +
      form.imaginaryCross * form.imaginaryCross)

/-- Reciprocal-translation pullback preserves the integral Hermitian determinant. -/
theorem IntegralHermitianForm.pullback_determinant
    (form : IntegralHermitianForm) (coefficient : Data.GaussianInt) :
    (form.pullback coefficient).determinant = form.determinant := by
  dsimp only [Geometry.Hermitian.Binary.IntegralHermitianForm.pullback,
    Geometry.Hermitian.Binary.IntegralHermitianForm.determinant, GaussianInt.normInt]
  ring1

/-- Bound the pulled-back constant by completing two integral squares.

The lower bound uses the coefficient norm, the original radial coefficient, and the sum of squares of the two cross
coefficients. -/
theorem IntegralHermitianForm.pullback_constant_lower
    (form : IntegralHermitianForm) (coefficient : Data.GaussianInt) :
    (form.constant - 1) * GaussianInt.normInt coefficient + form.radial -
        (form.realCross * form.realCross +
          form.imaginaryCross * form.imaginaryCross) ≤
      (form.pullback coefficient).constant := by
  have realSquare := Purelib.Data.Int.Order.mul_self_nonneg
    (coefficient.re + form.realCross)
  have imaginarySquare := Purelib.Data.Int.Order.mul_self_nonneg
    (coefficient.im - form.imaginaryCross)
  have sumNonnegative :
      0 ≤ (coefficient.re + form.realCross) *
          (coefficient.re + form.realCross) +
        (coefficient.im - form.imaginaryCross) *
          (coefficient.im - form.imaginaryCross) :=
    Int.Order.add_nonneg realSquare imaginarySquare
  have differenceIdentity :
      (form.pullback coefficient).constant -
          ((form.constant - 1) * GaussianInt.normInt coefficient + form.radial -
            (form.realCross * form.realCross +
              form.imaginaryCross * form.imaginaryCross)) =
        (coefficient.re + form.realCross) *
            (coefficient.re + form.realCross) +
          (coefficient.im - form.imaginaryCross) *
            (coefficient.im - form.imaginaryCross) := by
    dsimp only [Geometry.Hermitian.Binary.IntegralHermitianForm.pullback, GaussianInt.normInt]
    ring1
  rw [← differenceIdentity] at sumNonnegative
  have shifted := Int.Order.add_le_add sumNonnegative
    (Int.Order.le_refl ((form.constant - 1) * GaussianInt.normInt coefficient + form.radial -
      (form.realCross * form.realCross +
        form.imaginaryCross * form.imaginaryCross)))
  calc
    (form.constant - 1) * GaussianInt.normInt coefficient + form.radial -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross) =
        0 + ((form.constant - 1) * GaussianInt.normInt coefficient + form.radial -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross)) := by ring1
    _ ≤ ((form.pullback coefficient).constant -
          ((form.constant - 1) * GaussianInt.normInt coefficient + form.radial -
            (form.realCross * form.realCross +
              form.imaginaryCross * form.imaginaryCross))) +
        ((form.constant - 1) * GaussianInt.normInt coefficient + form.radial -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross)) := shifted
    _ = (form.pullback coefficient).constant := by ring1

/-- Clearing the reciprocal denominator identifies evaluation with the integral pullback.

The Gaussian coefficient plus the input must be nonzero; the multiplier is its squared norm. -/
theorem IntegralHermitianForm.evaluate_pullback_mul_normSq
    (form : IntegralHermitianForm) (coefficient : Data.GaussianInt)
    (value : Data.Gaussian.Basic.Canonical) (sumNonzero : GaussianInt.toGaussian coefficient + value ≠ 0) :
    form.evaluate ((GaussianInt.toGaussian coefficient + value)⁻¹) *
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian coefficient + value) =
      (form.pullback coefficient).evaluate value := by
  have transformed := hermitianForm_inverse_add_mul_normSq
    (form.constant : Fraction.Rational) (form.radial : Fraction.Rational)
    (form.realCross : Fraction.Rational) (form.imaginaryCross : Fraction.Rational)
    coefficient value sumNonzero
  simpa only [Geometry.Hermitian.Binary.IntegralHermitianForm.evaluate,
    Geometry.Hermitian.Binary.IntegralHermitianForm.pullback, GaussianInt.Norm.Basic.normInt_eq_natCast_normNat,
    Ring.IntCast.add, Ring.IntCast.sub, Ring.IntCast.intCast_mul, Int.cast_ofNat,
    Int.cast_natCast] using transformed

/-- An explicit slack-one certificate for an integral Hermitian form. -/
theorem IntegralHermitianForm.evaluate_nonnegative_of_slack_one
    (form : IntegralHermitianForm) (value : Data.Gaussian.Basic.Canonical)
    (valueInside : Data.Gaussian.Norm.Basic.normSq value ≤ 1)
    (scalePositive : 0 < (form.radial : Fraction.Rational) + 1)
    (determinantGap :
      0 ≤ ((form.constant : Fraction.Rational) - 1) *
          ((form.radial : Fraction.Rational) + 1) -
        ((form.realCross : Fraction.Rational) ^ 2 +
          (form.imaginaryCross : Fraction.Rational) ^ 2)) :
    0 ≤ form.evaluate value := by
  exact hermitianForm_nonnegative_of_certificate
    (form.constant : Fraction.Rational) (form.radial : Fraction.Rational)
    (form.realCross : Fraction.Rational) (form.imaginaryCross : Fraction.Rational)
    value 1 valueInside (by decide) scalePositive determinantGap

/-- A determinant-minus-two form has nonnegative pullback under the stated constant gap.

On the closed unit disc, positivity of `constant + 1` and an increase of at least three in the pulled-back constant give
the slack-one certificate. -/
theorem IntegralHermitianForm.pullback_evaluate_nonnegative_of_constant_gap
    (form : IntegralHermitianForm) (coefficient : Data.GaussianInt)
    (value : Data.Gaussian.Basic.Canonical) (valueInside : Data.Gaussian.Norm.Basic.normSq value ≤ 1)
    (scalePositive : 0 < (form.constant : Fraction.Rational) + 1)
    (determinantValue : form.determinant = -2)
    (constantGap :
      form.constant + 3 ≤ (form.pullback coefficient).constant) :
    0 ≤ (form.pullback coefficient).evaluate value := by
  let pulled := form.pullback coefficient
  have pulledDeterminant : pulled.determinant = -2 := by
    dsimp only [pulled]
    rw [Geometry.Hermitian.Binary.IntegralHermitianForm.pullback_determinant, determinantValue]
  have castGap :
      (form.constant : Fraction.Rational) + 3 ≤
        (pulled.constant : Fraction.Rational) := by
    have cast :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct
        (form.constant + 3) pulled.constant).2 constantGap
    simpa only [Ring.IntCast.add, Int.cast_ofNat] using cast
  have differenceNonnegative :
      0 ≤ (pulled.constant : Fraction.Rational) -
        (form.constant : Fraction.Rational) - 3 := by
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      castGap (-(form.constant : Fraction.Rational) - 3)
    calc
      0 = (form.constant : Fraction.Rational) + 3 +
          (-(form.constant : Fraction.Rational) - 3) := by ring1
      _ ≤ (pulled.constant : Fraction.Rational) +
          (-(form.constant : Fraction.Rational) - 3) := shifted
      _ = (pulled.constant : Fraction.Rational) -
          (form.constant : Fraction.Rational) - 3 := by ring1
  apply Geometry.Hermitian.Binary.IntegralHermitianForm.evaluate_nonnegative_of_slack_one
    pulled value valueInside
  · change 0 < (form.constant : Fraction.Rational) + 1
    exact scalePositive
  · have determinantCast := congrArg
      (fun value : Int => (value : Fraction.Rational)) pulledDeterminant
    change (pulled.determinant : Fraction.Rational) = -2 at determinantCast
    calc
      0 ≤ (pulled.constant : Fraction.Rational) -
          (form.constant : Fraction.Rational) - 3 := differenceNonnegative
      _ = ((pulled.constant : Fraction.Rational) - 1) *
            ((pulled.radial : Fraction.Rational) + 1) -
          ((pulled.realCross : Fraction.Rational) ^ 2 +
            (pulled.imaginaryCross : Fraction.Rational) ^ 2) := by
        have radialIdentity : pulled.radial = form.constant := rfl
        rw [radialIdentity]
        have determinantExpanded :
            (pulled.constant : Fraction.Rational) *
                  (form.constant : Fraction.Rational) -
                ((pulled.realCross : Fraction.Rational) *
                    (pulled.realCross : Fraction.Rational) +
                    (pulled.imaginaryCross : Fraction.Rational) *
                    (pulled.imaginaryCross : Fraction.Rational)) = -2 := by
          simp only [Geometry.Hermitian.Binary.IntegralHermitianForm.determinant, Ring.IntCast.sub,
            Ring.IntCast.intCast_mul, Ring.IntCast.add] at determinantCast
          rw [radialIdentity] at determinantCast
          exact determinantCast
        rw [pow_two, pow_two]
        calc
          (pulled.constant : Fraction.Rational) -
                (form.constant : Fraction.Rational) - 3 =
              ((pulled.constant : Fraction.Rational) *
                  (form.constant : Fraction.Rational) -
                ((pulled.realCross : Fraction.Rational) *
                    (pulled.realCross : Fraction.Rational) +
                  (pulled.imaginaryCross : Fraction.Rational) *
                    (pulled.imaginaryCross : Fraction.Rational))) +
                (pulled.constant : Fraction.Rational) -
                (form.constant : Fraction.Rational) - 1 := by
            rw [determinantExpanded]
            ring1
          _ = ((pulled.constant : Fraction.Rational) - 1) *
                ((form.constant : Fraction.Rational) + 1) -
              ((pulled.realCross : Fraction.Rational) *
                  (pulled.realCross : Fraction.Rational) +
                (pulled.imaginaryCross : Fraction.Rational) *
                  (pulled.imaginaryCross : Fraction.Rational)) := by ring1
end Purelib.Geometry.Hermitian.Binary

end
