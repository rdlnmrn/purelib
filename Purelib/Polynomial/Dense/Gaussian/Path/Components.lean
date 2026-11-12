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
import Purelib.Polynomial.Dense.Rational.Extensionality
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.Geometry.Rational

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
    (Basic.DensePolynomial Fraction.Rational) :=
  Components.realPart (Substitution.Affine.composeLine p origin direction)

/-- The rational imaginary-coordinate polynomial of a Gaussian polynomial along an affine path.

Finite affine Horner substitution is followed by coefficientwise imaginary projection. -/
def pathImag (p :
  CoefficientPolynomial) (origin
  direction : Gaussian.Basic.Canonical) :
    (Basic.DensePolynomial Fraction.Rational) :=
  Components.imagPart (Substitution.Affine.composeLine p origin direction)

/-- Both coordinate polynomials of one retained affine Gaussian substitution.

The original polynomial is substituted once. Its real and imaginary coefficient
projections consume that same finite Horner result.
-/
def pathParts (p : CoefficientPolynomial) (origin direction : Gaussian.Basic.Canonical) :
    Basic.DensePolynomial Fraction.Rational × Basic.DensePolynomial Fraction.Rational :=
  let image := Substitution.Affine.composeLine p origin direction
  (Components.realPart image, Components.imagPart image)

/-- Normalizing the input polynomial preserves its affine-path real-coordinate table. -/
@[simp] theorem pathReal_normalize (p :
  CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) :
    pathReal p.normalize origin direction = pathReal p
      origin direction := by
  change Components.realPart (Substitution.Affine.composeLine p.normalize origin
    direction) =
    Components.realPart (Substitution.Affine.composeLine p origin direction)
  rw [Substitution.Affine.composeLine_normalize]

/-- Normalizing the input polynomial preserves its affine-path imaginary-coordinate table. -/
@[simp] theorem pathImag_normalize (p :
  CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) :
    pathImag p.normalize origin direction = pathImag p
      origin direction := by
  change Components.imagPart (Substitution.Affine.composeLine p.normalize origin
    direction) =
    Components.imagPart (Substitution.Affine.composeLine p origin direction)
  rw [Substitution.Affine.composeLine_normalize]

/-- The real path-coordinate polynomial evaluates to the real part of the original affine-path value. -/
theorem eval_pathReal (p :
  CoefficientPolynomial)
  (origin direction : Gaussian.Basic.Canonical)
    (t : Fraction.Rational) :
    (pathReal p origin direction).eval t =
      (p.eval (Affine.line origin direction t)).re := by
  rw [pathReal, Components.eval_realPart,
    Substitution.Affine.eval_composeLine]

/-- The imaginary path-coordinate polynomial evaluates to the imaginary part of the original affine-path value. -/
theorem eval_pathImag (p :
  CoefficientPolynomial)
  (origin direction : Gaussian.Basic.Canonical)
    (t : Fraction.Rational) :
    (pathImag p origin direction).eval t =
      (p.eval (Affine.line origin direction t)).im := by
  rw [pathImag, Components.eval_imagPart,
    Substitution.Affine.eval_composeLine]
end Purelib.Polynomial.Dense.Gaussian.Path.Components

end

public section

namespace Purelib.Polynomial.Dense.Gaussian.Path.Components

/-- The retained affine coordinate pair gives both complete original coefficient views. -/
theorem pathParts_eq (p : CoefficientPolynomial) (origin direction : Gaussian.Basic.Canonical) :
    pathParts p origin direction = (pathReal p origin direction, pathImag p origin direction) := (rfl)

/-- Select one exact rational coordinate of a Gaussian value. -/
private def coordinate (imaginary : Bool) (value : Gaussian.Basic.Canonical) : Fraction.Rational :=
  if imaginary then value.im else value.re

/-- Compute only the selected coordinate of a Gaussian product. -/
private def productCoordinate (imaginary : Bool) (left right : Gaussian.Basic.Canonical) : Fraction.Rational :=
  if imaginary then left.re * right.im + left.im * right.re
  else left.re * right.re - left.im * right.im

/-- Read a normalized path coordinate, projecting before multiplication for a linear coefficient table. -/
private def normalizedCoordinate (imaginary : Bool) (polynomial : CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) : Basic.DensePolynomial Fraction.Rational :=
  match polynomial.coeffs with
  | [leading, constant] =>
      (⟨[productCoordinate imaginary leading direction,
        productCoordinate imaginary leading origin + coordinate imaginary constant]⟩ :
        Basic.DensePolynomial Fraction.Rational).normalize
  | _ =>
      (⟨(Substitution.Affine.composeLine polynomial origin direction).coeffs.map (coordinate imaginary)⟩ :
        Basic.DensePolynomial Fraction.Rational).normalize

/-- A projected linear table evaluates as the same coordinate of the original affine polynomial. -/
private theorem eval_linear_coordinate (imaginary : Bool)
    (leading constant origin direction : Gaussian.Basic.Canonical) (parameter : Fraction.Rational) :
    ((⟨[productCoordinate imaginary leading direction,
        productCoordinate imaginary leading origin + coordinate imaginary constant]⟩ :
      Basic.DensePolynomial Fraction.Rational).normalize).eval parameter =
      coordinate imaginary ((⟨[leading, constant]⟩ : CoefficientPolynomial).eval
        (Affine.line origin direction parameter)) := by
  rw [Basic.DensePolynomial.eval_normalize]
  change Basic.DensePolynomial.evalCoeffs parameter [_, _] =
    coordinate imaginary (Basic.DensePolynomial.evalCoeffs _ [leading, constant])
  rw [Basic.DensePolynomial.evalCoeffs_cons, Basic.DensePolynomial.evalCoeffs_cons]
  change productCoordinate imaginary leading direction * parameter +
      (productCoordinate imaginary leading origin + coordinate imaginary constant) =
    coordinate imaginary (leading * Affine.line origin direction parameter + constant)
  cases imaginary
  · change (leading.re * direction.re - leading.im * direction.im) * parameter +
        (leading.re * origin.re - leading.im * origin.im + constant.re) =
      (leading * Affine.line origin direction parameter + constant).re
    simp only [Affine.line, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Cast.ofCoordinate_re,
      Gaussian.Cast.ofCoordinate_im, -eq_self, -iff_self]
    ring1
  · change (leading.re * direction.im + leading.im * direction.re) * parameter +
        (leading.re * origin.im + leading.im * origin.re + constant.im) =
      (leading * Affine.line origin direction parameter + constant).im
    simp only [Affine.line, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Cast.ofCoordinate_re,
      Gaussian.Cast.ofCoordinate_im, -eq_self, -iff_self]
    ring1

/-- Projection before a linear substitution preserves the complete original normalized coordinate table. -/
private theorem normalizedCoordinate_eq (imaginary : Bool) (polynomial : CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) :
    normalizedCoordinate imaginary polynomial origin direction =
      (if imaginary then pathImag polynomial origin direction else pathReal polynomial origin direction).normalize := by
  unfold normalizedCoordinate
  split
  next leading constant table =>
    have polynomial_eq : polynomial = ⟨[leading, constant]⟩ := Basic.DensePolynomial.ext table
    cases imaginary
    · change _ = (pathReal polynomial origin direction).normalize
      apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
        (Basic.DensePolynomial.normalize_normalize _) (Basic.DensePolynomial.normalize_normalize _)
      intro parameter
      rw [eval_linear_coordinate, Basic.DensePolynomial.eval_normalize, eval_pathReal, polynomial_eq]
      rfl
    · change _ = (pathImag polynomial origin direction).normalize
      apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
        (Basic.DensePolynomial.normalize_normalize _) (Basic.DensePolynomial.normalize_normalize _)
      intro parameter
      rw [eval_linear_coordinate, Basic.DensePolynomial.eval_normalize, eval_pathImag, polynomial_eq]
      rfl
  next => cases imaginary <;> rfl

/-- The normalized real path polynomial, retaining only needed scalar products for a linear input.

Linear tables project each product before constructing the rational output.
All other tables use the original affine Horner substitution and real projection.
-/
def normalizedReal (polynomial : CoefficientPolynomial) (origin direction : Gaussian.Basic.Canonical) :
    Basic.DensePolynomial Fraction.Rational :=
  normalizedCoordinate false polynomial origin direction

/-- The normalized imaginary path polynomial, retaining only needed scalar products for a linear input.

Linear tables project each product before constructing the rational output.
All other tables use the original affine Horner substitution and imaginary projection.
-/
def normalizedImag (polynomial : CoefficientPolynomial) (origin direction : Gaussian.Basic.Canonical) :
    Basic.DensePolynomial Fraction.Rational :=
  normalizedCoordinate true polynomial origin direction

/-- The optimized real reading is exactly the complete original normalized coefficient table. -/
theorem normalizedReal_eq (polynomial : CoefficientPolynomial) (origin direction : Gaussian.Basic.Canonical) :
    normalizedReal polynomial origin direction = (pathReal polynomial origin direction).normalize :=
  normalizedCoordinate_eq false polynomial origin direction

/-- The optimized imaginary reading is exactly the complete original normalized coefficient table. -/
theorem normalizedImag_eq (polynomial : CoefficientPolynomial) (origin direction : Gaussian.Basic.Canonical) :
    normalizedImag polynomial origin direction = (pathImag polynomial origin direction).normalize :=
  normalizedCoordinate_eq true polynomial origin direction

end Purelib.Polynomial.Dense.Gaussian.Path.Components

end
