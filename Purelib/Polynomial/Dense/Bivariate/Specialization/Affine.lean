module
import Purelib.Polynomial.Dense.Bivariate.Basic

public import Purelib.Polynomial.Dense.Bivariate.Specialization
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Multiplication.Basic
import Purelib.Tactic.Ring

/-! # Affine substitution in finite bivariate coefficient tables

Both coordinates are substituted by their actual affine scalar polynomials.
The retained dense Horner operations give an executable coefficient table
and exact pointwise evaluation laws.
-/

open Purelib.Algebra.Field
open Purelib.Polynomial

public section

namespace Purelib.Polynomial.Dense.Bivariate.Specialization.Affine

open Purelib.Polynomial.Dense.Basic (CoefficientPolynomial DensePolynomial)

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- The exact affine scalar polynomial in its original descending coefficient order. -/
private def line (origin direction : K) : CoefficientPolynomial K := ⟨[direction, origin]⟩

omit [DecidableEq K] in
/-- The retained affine table evaluates to its two original scalar factors. -/
private theorem eval_line (origin direction point : K) :
    (line origin direction).eval point = origin + point * direction := by
  change (0 * point + direction) * point + origin = origin + point * direction
  ring1

/-- Substitute the original finite affine table by the existing dense Horner operations. -/
private def compose (polynomial : CoefficientPolynomial K) (origin direction : K) :
    CoefficientPolynomial K :=
  polynomial.coeffs.foldl (fun value coefficient => value * line origin direction +
    DensePolynomial.constant coefficient) 0

/-- The retained inner Horner substitution has its exact scalar accumulator law. -/
private theorem eval_compose_from (origin direction point : K)
    (coefficients : List K) (initial : CoefficientPolynomial K) :
    (coefficients.foldl (fun value coefficient => value * line origin direction +
      DensePolynomial.constant coefficient) initial).eval point =
    coefficients.foldl (fun value coefficient => value * (origin + point * direction) + coefficient)
      (initial.eval point) := by
  induction coefficients generalizing initial with
  | nil => rfl
  | cons coefficient remaining ih =>
      change (remaining.foldl
        (fun (value : CoefficientPolynomial K) coefficient => value * line origin direction +
          DensePolynomial.constant coefficient)
        (initial * line origin direction + DensePolynomial.constant coefficient)).eval point = _
      rewrite [ih, DensePolynomial.eval_add, DensePolynomial.eval_mul,
        eval_line, DensePolynomial.eval_constant]
      rfl

/-- Inner substitution evaluates the SAME original polynomial at its exact affine argument. -/
private theorem eval_compose (polynomial : CoefficientPolynomial K) (origin direction point : K) :
    (compose polynomial origin direction).eval point = polynomial.eval (origin + point * direction) := by
  unfold compose
  rewrite [eval_compose_from]
  rfl

/-- Substitute two actual affine coordinate maps into one GIVEN finite bivariate table.

The outer descending Horner fold multiplies by its original affine table;
its next coefficient is the corresponding inner affine Horner substitution.
The supplied bivariate table and both coordinate maps remain unchanged.
-/
def composeLine (polynomial : Dense.Bivariate.Basic.DenseBivariate K)
    (outerOrigin outerDirection innerOrigin innerDirection : K) : CoefficientPolynomial K :=
  polynomial.coeffs.foldl (fun value coefficient => value * line outerOrigin outerDirection +
    compose coefficient innerOrigin innerDirection) 0

/-- Affine specialization preserves the exact two-variable Horner accumulator. -/
private theorem eval_composeLine_from
    (outerOrigin outerDirection innerOrigin innerDirection point : K)
    (coefficients : List (CoefficientPolynomial K)) (initial : CoefficientPolynomial K) :
    (coefficients.foldl (fun value coefficient => value * line outerOrigin outerDirection +
      compose coefficient innerOrigin innerDirection) initial).eval point =
    coefficients.foldl (fun value coefficient => value * (outerOrigin + point * outerDirection) +
      coefficient.eval (innerOrigin + point * innerDirection)) (initial.eval point) := by
  induction coefficients generalizing initial with
  | nil => rfl
  | cons coefficient remaining ih =>
      change (remaining.foldl
        (fun (value : CoefficientPolynomial K) coefficient => value * line outerOrigin outerDirection +
          compose coefficient innerOrigin innerDirection)
        (initial * line outerOrigin outerDirection + compose coefficient innerOrigin innerDirection)).eval point = _
      rewrite [ih, DensePolynomial.eval_add, DensePolynomial.eval_mul,
        eval_line, eval_compose]
      rfl

/-- The actual line restriction evaluates to the SAME original bivariate table at both actual affine coordinates. -/
theorem eval_composeLine (polynomial : Dense.Bivariate.Basic.DenseBivariate K)
    (outerOrigin outerDirection innerOrigin innerDirection point : K) :
    (composeLine polynomial outerOrigin outerDirection innerOrigin innerDirection).eval point =
      Dense.Bivariate.Basic.eval polynomial (outerOrigin + point * outerDirection)
        (innerOrigin + point * innerDirection) := by
  unfold composeLine
  rewrite [eval_composeLine_from]
  rfl

end Purelib.Polynomial.Dense.Bivariate.Specialization.Affine

end
