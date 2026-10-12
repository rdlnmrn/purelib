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
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) (t : Fraction.Rational) :
    (Dense.Gaussian.Path.Components.pathReal (p * q) origin direction).eval t =
      (Dense.Rational.Pair.Product.productReal (Dense.Gaussian.Path.Components.pathReal p origin direction)
        (Dense.Gaussian.Path.Components.pathImag p origin direction)
        (Dense.Gaussian.Path.Components.pathReal q origin direction) (Dense.Gaussian.Path.Components.pathImag q origin
          direction)).eval t := by
  rw [Dense.Gaussian.Path.Components.eval_pathReal, Dense.Rational.Pair.Product.eval_productReal,
    Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
    Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
      Dense.Basic.DensePolynomial.eval_mul]
  rfl

/-- The imaginary path component of a product evaluates to the imaginary part of the product of both coordinate pairs.
-/
theorem eval_pathImag_mul (p q :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) (t : Fraction.Rational) :
    (Dense.Gaussian.Path.Components.pathImag (p * q) origin direction).eval t =
      (Dense.Rational.Pair.Product.productImag (Dense.Gaussian.Path.Components.pathReal p origin direction)
        (Dense.Gaussian.Path.Components.pathImag p origin direction)
        (Dense.Gaussian.Path.Components.pathReal q origin direction) (Dense.Gaussian.Path.Components.pathImag q origin
          direction)).eval t := by
  rw [Dense.Gaussian.Path.Components.eval_pathImag, Dense.Rational.Pair.Product.eval_productImag,
    Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
    Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
      Dense.Basic.DensePolynomial.eval_mul]
  rfl

end Purelib.Polynomial.Dense.Gaussian.Path.Product

end
