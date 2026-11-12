module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.Pair.Product
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation

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

namespace Purelib.Polynomial.Dense.Gaussian.Path.Product

/-- The real path component of a product evaluates to the real part of the product of both coordinate pairs. -/
theorem eval_pathReal_mul (p q :
  Basic.CanonicalCoefficients.CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) (t : Fraction.Rational) :
    (Components.pathReal (p * q) origin direction).eval t =
      (Rational.Pair.Product.productReal (Components.pathReal p origin direction)
        (Components.pathImag p origin direction)
        (Components.pathReal q origin direction) (Components.pathImag q origin
          direction)).eval t := by
  rw [Components.eval_pathReal, Rational.Pair.Product.eval_productReal,
    Components.eval_pathReal, Components.eval_pathImag,
    Components.eval_pathReal, Components.eval_pathImag,
      Basic.DensePolynomial.eval_mul]
  rfl

/-- The imaginary path component of a product evaluates to the imaginary part of the product of both coordinate pairs.
-/
theorem eval_pathImag_mul (p q :
  Basic.CanonicalCoefficients.CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) (t : Fraction.Rational) :
    (Components.pathImag (p * q) origin direction).eval t =
      (Rational.Pair.Product.productImag (Components.pathReal p origin direction)
        (Components.pathImag p origin direction)
        (Components.pathReal q origin direction) (Components.pathImag q origin
          direction)).eval t := by
  rw [Components.eval_pathImag, Rational.Pair.Product.eval_productImag,
    Components.eval_pathReal, Components.eval_pathImag,
    Components.eval_pathReal, Components.eval_pathImag,
      Basic.DensePolynomial.eval_mul]
  rfl

end Purelib.Polynomial.Dense.Gaussian.Path.Product

end
