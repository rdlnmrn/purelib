module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Components

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Selecting rational Gaussian polynomial coordinates

A leading Gaussian coefficient chooses the real coordinate unless it is
zero, in which case the imaginary coordinate is retained. Nonzeroness and
readback certificates concern that same finite normalized table.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Components.Selection

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

/-! ## A nonzero rational-coordinate eliminant -/

/-- Select the real leading-coordinate polynomial unless that leading
coordinate is zero, in which case select the imaginary coordinate.

The same normalized coefficient table supplies either its real or its
imaginary coordinate according to the displayed leading-coordinate test. -/
@[expose] def selectedCoordinate (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
  (Dense.Basic.DensePolynomial Fraction.Rational) :=
  if p.leadingCoeff.re = 0 then
    Dense.Gaussian.Components.imagPart p.normalize
  else Dense.Gaussian.Components.realPart p.normalize

/-- The selected real or imaginary coordinate polynomial is nonzero when the Gaussian polynomial is nonzero.

The nonzero Gaussian leading coefficient has a nonzero selected component.
The retained coordinate table therefore begins with that component after
its leading-zero scan. -/
theorem selectedCoordinate_nonzero (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    (Dense.Gaussian.Components.Selection.selectedCoordinate p).isZero = false := by
  have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero nonzero
  cases coefficients : p.normalize.coeffs with
  | nil =>
      change p.normalize.coeffs.headD 0 ≠ 0 at leadingNonzero
      rw [coefficients] at leadingNonzero
      exact (leadingNonzero rfl).elim
  | cons leading remaining =>
      have leadingIdentity : p.leadingCoeff = leading := by
        change p.normalize.coeffs.headD 0 = leading
        rewrite [coefficients]
        exact Eq.refl _
      by_cases realZero : p.leadingCoeff.re = 0
      · rw [Dense.Gaussian.Components.Selection.selectedCoordinate, if_pos realZero]
        have leadingRealZero : leading.re = 0 := by
          simpa only [leadingIdentity] using realZero
        have imaginaryNonzero : leading.im ≠ 0 := by
          intro imaginaryZero
          apply leadingNonzero
          rw [leadingIdentity]
          apply Gaussian.Basic.ext
          · exact leadingRealZero
          · exact imaginaryZero
        change ((p.normalize.coeffs.map
          Gaussian.Basic.im).dropWhile
            (· = 0)).isEmpty = false
        rw [coefficients]
        simp only [List.map_cons]
        have retained : decide (leading.im = 0) = false := by
          cases selected : decide (leading.im = 0) with
          | false => rfl
          | true => exact (imaginaryNonzero (of_decide_eq_true selected)).elim
        rw [Data.List.DropWhile.cons_of_false (fun value => decide (value = 0))
          leading.im (remaining.map Gaussian.Basic.im) retained]
        rfl
      · rw [Dense.Gaussian.Components.Selection.selectedCoordinate, if_neg realZero]
        have leadingRealNonzero : leading.re ≠ 0 := by
          simpa only [leadingIdentity] using realZero
        change ((p.normalize.coeffs.map
          Gaussian.Basic.re).dropWhile
            (· = 0)).isEmpty = false
        rw [coefficients]
        simp only [List.map_cons]
        have retained : decide (leading.re = 0) = false := by
          cases selected : decide (leading.re = 0) with
          | false => rfl
          | true => exact (leadingRealNonzero (of_decide_eq_true selected)).elim
        rw [Data.List.DropWhile.cons_of_false (fun value => decide (value = 0))
          leading.re (remaining.map Gaussian.Basic.re) retained]
        rfl

/-- Evaluate the coordinate selected by the Gaussian leading coefficient.

The value is the imaginary part on the real axis when the leading real coordinate is zero, and the real part otherwise.
-/
@[simp] theorem eval_selectedCoordinate (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (parameter : Fraction.Rational) :
    (Dense.Gaussian.Components.Selection.selectedCoordinate p).eval parameter =
      if p.leadingCoeff.re = 0 then
        (p.eval (Gaussian.Cast.Path.ofCoordinate parameter)).im
      else
        (p.eval (Gaussian.Cast.Path.ofCoordinate parameter)).re := by
  unfold Dense.Gaussian.Components.Selection.selectedCoordinate
  split
  · rw [Dense.Gaussian.Components.eval_imagPart,
      Dense.Basic.DensePolynomial.eval_normalize]
  · rw [Dense.Gaussian.Components.eval_realPart,
      Dense.Basic.DensePolynomial.eval_normalize]

end Purelib.Polynomial.Dense.Gaussian.Components.Selection

end
