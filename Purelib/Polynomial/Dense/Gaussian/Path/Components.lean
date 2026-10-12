module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Components
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

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

namespace Purelib.Polynomial.Dense.Gaussian.Path.Components

/-- The rational real-coordinate polynomial of a Gaussian polynomial along an affine path.

Finite affine Horner substitution is followed by coefficientwise real projection. -/
def pathReal (p :
  CoefficientPolynomial) (origin
  direction : Gaussian.Basic.Canonical) :
    (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Gaussian.Components.realPart (Dense.Gaussian.Substitution.Affine.composeLine p origin direction)

/-- The rational imaginary-coordinate polynomial of a Gaussian polynomial along an affine path.

Finite affine Horner substitution is followed by coefficientwise imaginary projection. -/
def pathImag (p :
  CoefficientPolynomial) (origin
  direction : Gaussian.Basic.Canonical) :
    (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Gaussian.Components.imagPart (Dense.Gaussian.Substitution.Affine.composeLine p origin direction)

/-- Normalizing the input polynomial preserves its affine-path real-coordinate table. -/
@[simp] theorem pathReal_normalize (p :
  CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) :
    pathReal p.normalize origin direction = pathReal p
      origin direction := by
  change Dense.Gaussian.Components.realPart (Dense.Gaussian.Substitution.Affine.composeLine p.normalize origin
    direction) =
    Dense.Gaussian.Components.realPart (Dense.Gaussian.Substitution.Affine.composeLine p origin direction)
  rw [Dense.Gaussian.Substitution.Affine.composeLine_normalize]

/-- Normalizing the input polynomial preserves its affine-path imaginary-coordinate table. -/
@[simp] theorem pathImag_normalize (p :
  CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) :
    pathImag p.normalize origin direction = pathImag p
      origin direction := by
  change Dense.Gaussian.Components.imagPart (Dense.Gaussian.Substitution.Affine.composeLine p.normalize origin
    direction) =
    Dense.Gaussian.Components.imagPart (Dense.Gaussian.Substitution.Affine.composeLine p origin direction)
  rw [Dense.Gaussian.Substitution.Affine.composeLine_normalize]

/-- The real path-coordinate polynomial evaluates to the real part of the original affine-path value. -/
theorem eval_pathReal (p :
  CoefficientPolynomial)
  (origin direction : Gaussian.Basic.Canonical)
    (t : Fraction.Rational) :
    (pathReal p origin direction).eval t =
      (p.eval (Geometry.Rational.Affine.line origin direction t)).re := by
  rw [pathReal, Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Substitution.Affine.eval_composeLine]

/-- The imaginary path-coordinate polynomial evaluates to the imaginary part of the original affine-path value. -/
theorem eval_pathImag (p :
  CoefficientPolynomial)
  (origin direction : Gaussian.Basic.Canonical)
    (t : Fraction.Rational) :
    (pathImag p origin direction).eval t =
      (p.eval (Geometry.Rational.Affine.line origin direction t)).im := by
  rw [pathImag, Dense.Gaussian.Components.eval_imagPart,
    Dense.Gaussian.Substitution.Affine.eval_composeLine]
end Purelib.Polynomial.Dense.Gaussian.Path.Components

end
