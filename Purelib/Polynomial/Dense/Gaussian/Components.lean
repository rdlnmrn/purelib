module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Cast
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Components

/-- Real coordinate coefficient list. -/
def realPart (p :
  CoefficientPolynomial) :
  (Dense.Basic.DensePolynomial Fraction.Rational) :=
  ⟨p.coeffs.map (fun z => z.re)⟩

/-- Imaginary coordinate coefficient list. -/
def imagPart (p :
  CoefficientPolynomial) :
  (Dense.Basic.DensePolynomial Fraction.Rational) :=
  ⟨p.coeffs.map (fun z => z.im)⟩

end Purelib.Polynomial.Dense.Gaussian.Components

section
namespace Purelib.Polynomial.Dense.Gaussian.Components

/-- Real-coordinate projection commutes with Horner folding along the real axis.

The rational and Gaussian initial accumulators must have matching real coordinates. -/
private theorem foldl_map_re (t : Fraction.Rational)
  (coefficients : List Gaussian.Basic.Canonical)
    (r : Fraction.Rational) (z : Gaussian.Basic.Canonical) (hrz : r = z.re) :
    (coefficients.map (fun z => z.re)).foldl
        (fun value coefficient => value * t + coefficient) r =
      (coefficients.foldl
        (fun value coefficient => value * Gaussian.Cast.Path.ofCoordinate t + coefficient) z).re := by
  induction coefficients generalizing r z with
  | nil => exact hrz
  | cons coefficient coefficients ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      simp only [Gaussian.Basic.mul_re, Gaussian.Cast.ofCoordinate_re, Gaussian.Cast.ofCoordinate_im,
        Gaussian.Basic.add_re]
      rw [hrz]
      ring1
/-- Imaginary-coordinate projection commutes with Horner folding along the real axis.

The rational and Gaussian initial accumulators must have matching imaginary coordinates. -/
private theorem foldl_map_im (t : Fraction.Rational)
  (coefficients : List Gaussian.Basic.Canonical)
    (r : Fraction.Rational) (z : Gaussian.Basic.Canonical) (hrz : r = z.im) :
    (coefficients.map (fun z => z.im)).foldl
        (fun value coefficient => value * t + coefficient) r =
      (coefficients.foldl
        (fun value coefficient => value * Gaussian.Cast.Path.ofCoordinate t + coefficient) z).im := by
  induction coefficients generalizing r z with
  | nil => exact hrz
  | cons coefficient coefficients ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      simp only [Gaussian.Basic.mul_im, Gaussian.Cast.ofCoordinate_re, Gaussian.Cast.ofCoordinate_im,
        Gaussian.Basic.add_im]
      rw [hrz]
      ring1
end Purelib.Polynomial.Dense.Gaussian.Components
end

namespace Purelib.Polynomial.Dense.Gaussian.Components

/-- The real coefficient polynomial evaluates to the real part of the Gaussian value on the real axis. -/
@[simp] theorem eval_realPart (p :
  CoefficientPolynomial) (t : Fraction.Rational) :
    (realPart p).eval t = (p.eval (Gaussian.Cast.Path.ofCoordinate t)).re := by
  dsimp only [realPart, DensePolynomial.eval,
    DensePolynomial.evalCoeffs]
  exact foldl_map_re t p.coeffs 0 0 rfl

/-- The imaginary coefficient polynomial evaluates to the imaginary part of the Gaussian value on the real axis. -/
@[simp] theorem eval_imagPart (p :
  CoefficientPolynomial) (t : Fraction.Rational) :
    (imagPart p).eval t = (p.eval (Gaussian.Cast.Path.ofCoordinate t)).im := by
  dsimp only [imagPart, DensePolynomial.eval,
    DensePolynomial.evalCoeffs]
  exact foldl_map_im t p.coeffs 0 0 rfl
end Purelib.Polynomial.Dense.Gaussian.Components

end
