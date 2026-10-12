module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Affine.Reparameterization
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Extensionality
public import Purelib.Polynomial.Dense.Rational.Substitution.Affine
import Purelib.Data.Rat.Fraction.Field

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Affine reparameterization of Gaussian polynomial paths

Normalized real and imaginary path-coordinate polynomials agree with affine
substitution at the same retained rational offset and slope.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Path.Reparameterization

/-- Affine reparameterization of a Gaussian line path equals affine substitution in its normalized real coordinate
polynomial.

The new origin and direction use the supplied rational offset and slope; the equality preserves the exact normalized
coefficient representation. -/
public theorem
  pathReal_affine
  (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction : Gaussian.Basic.Canonical)
    (offset slope : Fraction.Rational) :
    (Dense.Gaussian.Path.Components.pathReal polynomial (Geometry.Rational.Affine.line origin direction offset)
      (Gaussian.Cast.Path.ofCoordinate slope * direction)).normalize =
      Dense.Rational.Substitution.Affine.subst (Dense.Gaussian.Path.Components.pathReal polynomial origin direction)
        offset slope := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (Dense.Basic.DensePolynomial.normalize_normalize _) (Dense.Rational.Substitution.Affine.subst_normalized _ _ _)
  intro point
  rw [Dense.Basic.DensePolynomial.eval_normalize, Dense.Gaussian.Path.Components.eval_pathReal,
    Dense.Rational.Substitution.Affine.subst_eval,
    Dense.Gaussian.Path.Components.eval_pathReal, Geometry.Rational.Affine.Reparameterization.line_affine]

/-- Affine reparameterization of a Gaussian line path equals affine substitution in its normalized imag coordinate
polynomial.

The new origin and direction use the supplied rational offset and slope; the equality preserves the exact normalized
coefficient representation. -/
public theorem
  pathImag_affine
  (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction : Gaussian.Basic.Canonical)
    (offset slope : Fraction.Rational) :
    (Dense.Gaussian.Path.Components.pathImag polynomial (Geometry.Rational.Affine.line origin direction offset)
      (Gaussian.Cast.Path.ofCoordinate slope * direction)).normalize =
      Dense.Rational.Substitution.Affine.subst (Dense.Gaussian.Path.Components.pathImag polynomial origin direction)
        offset slope := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (Dense.Basic.DensePolynomial.normalize_normalize _) (Dense.Rational.Substitution.Affine.subst_normalized _ _ _)
  intro point
  rw [Dense.Basic.DensePolynomial.eval_normalize, Dense.Gaussian.Path.Components.eval_pathImag,
    Dense.Rational.Substitution.Affine.subst_eval,
    Dense.Gaussian.Path.Components.eval_pathImag, Geometry.Rational.Affine.Reparameterization.line_affine]

end Purelib.Polynomial.Dense.Gaussian.Path.Reparameterization

end
