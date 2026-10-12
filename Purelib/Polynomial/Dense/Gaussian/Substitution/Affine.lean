module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
public import Purelib.Geometry.Rational.Affine
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.Ring
import Purelib.Data.List.DropWhile.Basic

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Substitution.Affine

open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Polynomial

public section

/-- Multiply a polynomial in the parameter by the affine line expression.

The supplied origin and direction scale the same polynomial. A single coefficient shift represents multiplication by the
affine parameter before adding the two retained terms. -/
@[expose] def mulLine (origin direction : Gaussian.Basic.Canonical) (p :
  Basic.CanonicalCoefficients.CoefficientPolynomial) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Basic.DensePolynomial.scale origin p + Dense.Basic.DensePolynomial.shift 1 (Dense.Basic.DensePolynomial.scale
    direction p)

/-- Multiplying by an affine line produces a normalized Gaussian polynomial.

The two retained scaled terms are combined by the original normalized sum. -/
theorem normalize_mulLine (origin direction : Gaussian.Basic.Canonical)
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    (mulLine origin direction polynomial).normalize = mulLine origin direction polynomial := by
  unfold mulLine
  exact Dense.Basic.DensePolynomial.normalize_add _ _

/-- Multiplication by the affine line sends the zero polynomial to zero.

Both retained scalings and the single shift preserve the zero polynomial. Their normalized sum is therefore zero. -/
@[simp] theorem mulLine_zero (origin direction : Gaussian.Basic.Canonical) :
    mulLine origin direction (0 : Basic.CanonicalCoefficients.CoefficientPolynomial) = 0 := by
  rw [mulLine, Dense.Basic.DensePolynomial.scale_zero_right, Dense.Basic.DensePolynomial.scale_zero_right,
    Dense.Basic.DensePolynomial.shift_zero,
    Dense.Basic.DensePolynomial.zero_add_normalize, Dense.Basic.DensePolynomial.normalize_zero]

/-- At a rational parameter, polynomial multiplication by the line agrees with affine-path multiplication.

The same polynomial and rational parameter determine both readings. Evaluation of the retained scale, shift and sum
gives the displayed affine multiplier. -/
@[simp] theorem eval_mulLine (origin direction : Gaussian.Basic.Canonical)
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (t : Fraction.Rational) :
    (mulLine origin direction p).eval (Gaussian.Cast.Path.ofCoordinate t) =
      p.eval (Gaussian.Cast.Path.ofCoordinate t) * Geometry.Rational.Affine.line origin direction t := by
  rw [mulLine, Dense.Basic.DensePolynomial.eval_add, Dense.Basic.DensePolynomial.eval_scale,
    Dense.Basic.DensePolynomial.eval_shift, Dense.Basic.DensePolynomial.eval_scale]
  apply Gaussian.Basic.ext <;>
    simp only [Geometry.Rational.Affine.line, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im, Gaussian.Cast.ofCoordinate_re,
      Gaussian.Cast.ofCoordinate_im, pow_one] <;>
    ring1

/-- At any Gaussian argument, multiplying by the line multiplies evaluation by origin plus argument times direction.

The supplied Gaussian argument evaluates the retained scale and single shift. The resulting factor uses the same origin
and direction. -/
@[simp] theorem eval_mulLineGaussian (origin direction : Gaussian.Basic.Canonical)
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (z : Gaussian.Basic.Canonical) :
    (mulLine origin direction p).eval z =
      p.eval z * (origin + z * direction) := by
  rw [mulLine, Dense.Basic.DensePolynomial.eval_add, Dense.Basic.DensePolynomial.eval_scale,
    Dense.Basic.DensePolynomial.eval_shift, Dense.Basic.DensePolynomial.eval_scale]
  change origin * p.eval z + direction * p.eval z * z ^ 1 = _
  ring1

/-- Substitute an affine line into a descending coefficient table by a finite polynomial Horner fold.

The descending coefficient list is folded from the zero polynomial. Each step multiplies the current polynomial by the
same affine line and adds the next retained coefficient. -/
@[expose] def composeLineCoeffs (origin direction : Gaussian.Basic.Canonical)
    (coefficients : List Gaussian.Basic.Canonical) : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  coefficients.foldl
    (fun accumulator coefficient =>
      mulLine origin direction accumulator + Dense.Basic.DensePolynomial.constant coefficient) 0

section
/-- Removing leading zero coefficients preserves affine Horner substitution.

The retained Boolean zero test drops exactly the leading zero coefficients.
Each dropped coefficient advances the original zero accumulator to zero, so
both finite coefficient folds produce the same polynomial. -/
private theorem composeLineCoeffs_dropWhile_zero
    (origin direction : Gaussian.Basic.Canonical) (coefficients : List Gaussian.Basic.Canonical) :
    composeLineCoeffs origin direction (coefficients.dropWhile (· = 0)) =
      composeLineCoeffs origin direction coefficients := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      by_cases coefficientZero : coefficient = 0
      · subst coefficient
        rw [Purelib.Data.List.DropWhile.cons_of_true
          (fun value : Gaussian.Basic.Canonical => decide (value = 0)) 0 coefficients
          (decide_eq_true (rfl : (0 : Gaussian.Basic.Canonical) = 0))]
        rw [inductionHypothesis]
        unfold composeLineCoeffs
        rw [List.foldl_cons]
        rw [mulLine_zero, Dense.Basic.DensePolynomial.zero_add_normalize,
          Dense.Basic.DensePolynomial.normalize_constant_zero]
      · rw [Purelib.Data.List.DropWhile.cons_of_false
          (fun value : Gaussian.Basic.Canonical => decide (value = 0)) coefficient coefficients
          (decide_eq_false coefficientZero)]
/-- Evaluate an affine Horner fold from an arbitrary polynomial accumulator at a rational parameter.

The same coefficient list and initial accumulator determine both folds. Scalar evaluation of each retained polynomial
step gives the corresponding affine-path Horner step. -/
private theorem eval_composeLineCoeffs_from
    (origin direction : Gaussian.Basic.Canonical) (t : Fraction.Rational)
    (coefficients : List Gaussian.Basic.Canonical) (accumulator : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    (coefficients.foldl
      (fun value coefficient =>
        mulLine origin direction value + Dense.Basic.DensePolynomial.constant coefficient)
      accumulator).eval (Gaussian.Cast.Path.ofCoordinate t) =
    coefficients.foldl
      (fun value coefficient => value * Geometry.Rational.Affine.line origin direction t + coefficient)
      (accumulator.eval (Gaussian.Cast.Path.ofCoordinate t)) := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons]
      rw [ih, Dense.Basic.DensePolynomial.eval_add, eval_mulLine, Dense.Basic.DensePolynomial.eval_constant]
end

/-- Executable affine substitution.

The supplied polynomial contributes its exact descending coefficient table. The retained finite Horner substitution uses
the same origin and direction without constructing a new source table. -/
@[expose] def composeLine (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
  Gaussian.Basic.Canonical) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  composeLineCoeffs origin direction p.coeffs

/-- Affine substitution ignores only the finite prefix of representation
zeros removed by normalization.

The finite normalization drops only the displayed leading zero coefficients. The original zero-start Horner fold is
unchanged by removing that prefix. -/
@[simp] theorem composeLine_normalize (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (origin direction : Gaussian.Basic.Canonical) :
    composeLine p.normalize origin direction = composeLine p origin direction := by
  unfold composeLine
  exact Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.composeLineCoeffs_dropWhile_zero origin direction p.coeffs

/-- Affine substitution evaluates to the original polynomial along the rational affine path.

The supplied rational parameter determines the same affine point on both sides. The coefficient-fold evaluation identity
transports the retained polynomial evaluation. -/
theorem eval_composeLine (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
  Gaussian.Basic.Canonical)
    (t : Fraction.Rational) :
    (composeLine p origin direction).eval (Gaussian.Cast.Path.ofCoordinate t) =
      p.eval (Geometry.Rational.Affine.line origin direction t) := by
  rw [composeLine, composeLineCoeffs, Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.eval_composeLineCoeffs_from]
  rfl

section
/-- Evaluate an affine Horner fold from an arbitrary accumulator at a Gaussian argument.

The original finite coefficient fold starts from the supplied accumulator. Evaluating each polynomial step at the same
Gaussian argument gives the displayed scalar Horner fold. -/
private theorem eval_composeLineCoeffsGaussian_from
    (origin direction z : Gaussian.Basic.Canonical) (coefficients : List Gaussian.Basic.Canonical)
    (accumulator : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    (coefficients.foldl
      (fun value coefficient =>
        mulLine origin direction value + Dense.Basic.DensePolynomial.constant coefficient)
      accumulator).eval z =
    coefficients.foldl
      (fun value coefficient =>
        value * (origin + z * direction) + coefficient)
      (accumulator.eval z) := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis, Dense.Basic.DensePolynomial.eval_add, eval_mulLineGaussian,
        Dense.Basic.DensePolynomial.eval_constant]
end

/-- Affine substitution semantics at an arbitrary Gaussian argument.

Both evaluations use the same Gaussian argument, source coefficient list, origin and direction. The finite fold identity
identifies their exact scalar readbacks. -/
theorem eval_composeLineGaussian (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (origin direction z : Gaussian.Basic.Canonical) :
    (composeLine p origin direction).eval z =
      p.eval (origin + z * direction) := by
  rw [composeLine, composeLineCoeffs,
    Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.eval_composeLineCoeffsGaussian_from]
  rfl
end

end Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
