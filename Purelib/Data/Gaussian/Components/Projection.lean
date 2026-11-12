module

public import Purelib.Data.Gaussian.Components.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Embedded Gaussian coordinate projections

The original real and imaginary coordinates remain embedded Gaussian points.
Conjugation identifies their doubled values; ordered differences and
squared-norm bounds retain those same original coordinate readings.
-/

public section

namespace Purelib.Data.Gaussian.Components.Projection

open Purelib.Data.Gaussian.Basic (Canonical ext conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat

/-- The original real component retained as an embedded Gaussian rational. -/
@[expose] def realPart (value : Canonical) : Canonical := Basic.point value.re 0

/-- The original imaginary component retained as an embedded Gaussian rational. -/
@[expose] def imaginaryPart (value : Canonical) : Canonical := Basic.point 0 value.im

/-- Twice the embedded real component is the original value plus its conjugate. -/
theorem realPart_mul_two (value : Canonical) : realPart value * 2 = value + conj value := by
  apply ext
  · change value.re * 2 - 0 * 0 = value.re + value.re
    ring1
  · change value.re * 0 + 0 * 2 = value.im + -value.im
    ring1

/-- Twice the embedded imaginary component is the original value minus its conjugate. -/
theorem imaginaryPart_mul_two (value : Canonical) : imaginaryPart value * 2 = value - conj value := by
  apply ext
  · change 0 * 2 - value.im * 0 = value.re - value.re
    ring1
  · change 0 * 0 + value.im * 2 = value.im - -value.im
    ring1

/-- Taking the embedded real component preserves the original ordered difference. -/
theorem realPart_sub (first last : Canonical) : realPart (first - last) = realPart first - realPart last := by
  apply ext
  · rfl
  · change (0 : Fraction.Rational) = 0 - 0
    ring1

/-- Taking the embedded imaginary component preserves the original ordered difference. -/
theorem imaginaryPart_sub (first last : Canonical) :
    imaginaryPart (first - last) = imaginaryPart first - imaginaryPart last := by
  apply ext
  · change (0 : Fraction.Rational) = 0 - 0
    ring1
  · rfl

/-- A real Gaussian scalar commutes with taking the original embedded real component. -/
theorem realPart_mul_real (value scalar : Canonical) (real : scalar.im = 0) :
    realPart (value * scalar) = realPart value * scalar := by
  apply ext
  · change value.re * scalar.re - value.im * scalar.im = value.re * scalar.re - 0 * scalar.im
    rewrite [real]
    ring1
  · change (0 : Fraction.Rational) = value.re * scalar.im + 0 * scalar.re
    rewrite [real]
    ring1

/-- A real Gaussian scalar commutes with taking the original embedded imaginary component. -/
theorem imaginaryPart_mul_real (value scalar : Canonical) (real : scalar.im = 0) :
    imaginaryPart (value * scalar) = imaginaryPart value * scalar := by
  apply ext
  · change (0 : Fraction.Rational) = 0 * scalar.re - value.im * scalar.im
    rewrite [real]
    ring1
  · change value.re * scalar.im + value.im * scalar.re = 0 * scalar.im + value.im * scalar.re
    rewrite [real]
    ring1

/-- An imaginary scalar makes the original imaginary component determine the product's embedded real component. -/
theorem realPart_mul_imaginary (value scalar : Canonical) (imaginary : scalar.re = 0) :
    realPart (value * scalar) = imaginaryPart value * scalar := by
  apply ext
  · change value.re * scalar.re - value.im * scalar.im = 0 * scalar.re - value.im * scalar.im
    rewrite [imaginary]
    ring1
  · change (0 : Fraction.Rational) = 0 * scalar.im + value.im * scalar.re
    rewrite [imaginary]
    ring1

/-- The original embedded real component has squared norm bounded by the full original squared norm. -/
theorem normSq_realPart_le (value : Canonical) : normSq (realPart value) ≤ normSq value := by
  change value.re ^ 2 + 0 ^ 2 ≤ value.re ^ 2 + value.im ^ 2
  calc
    _ = value.re ^ 2 + 0 := by ring1
    _ ≤ _ := Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- The original embedded imaginary component has squared norm bounded by the full original squared norm. -/
theorem normSq_imaginaryPart_le (value : Canonical) : normSq (imaginaryPart value) ≤ normSq value := by
  change 0 ^ 2 + value.im ^ 2 ≤ value.re ^ 2 + value.im ^ 2
  calc
    _ = 0 + value.im ^ 2 := by ring1
    _ ≤ _ := Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Basic.le_refl _)

end Purelib.Data.Gaussian.Components.Projection
