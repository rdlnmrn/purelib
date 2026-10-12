module
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field

open Purelib.Data

open Purelib.Polynomial

/-!
# Finite substitution of a coordinate power in Gaussian polynomials

Horner evaluation constructs the substituted coefficients using only shifts
and addition. The evaluation identity is proved by finite list induction.
-/

@[expose] public section

-- Retain the original public Dense/Gaussian shorthand names at the surveyed owner.

namespace Purelib.Polynomial.Dense.Gaussian.Substitution.Power

open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- Dense Gaussian rational polynomials for power substitution. -/
abbrev CoefficientPolynomial := Basic.CanonicalCoefficients.CoefficientPolynomial
/-- Canonical Gaussian rational coefficient scalars. -/
abbrev CanonicalScalar := Gaussian.Basic.Canonical

/-- Substitute a coordinate power by a finite shift-and-add Horner fold.

Each step shifts the accumulator by the supplied natural exponent and adds the next constant coefficient. -/
def substitute (polynomial : CoefficientPolynomial) (degree : Nat) : CoefficientPolynomial :=
  polynomial.coeffs.foldl (fun value coefficient => Dense.Basic.DensePolynomial.shift degree value +
    Dense.Basic.DensePolynomial.constant coefficient) 0

/-- Evaluation transports a power-substitution fold from any initial polynomial to scalar Horner evaluation. -/
private theorem eval_from (degree : Nat) (point : CanonicalScalar) (coefficients : List
  CanonicalScalar) (initial : CoefficientPolynomial) :
    (coefficients.foldl (fun value coefficient => Dense.Basic.DensePolynomial.shift degree value +
      Dense.Basic.DensePolynomial.constant coefficient) initial).eval point =
      coefficients.foldl (fun value coefficient => value * point ^ degree + coefficient) (initial.eval point) := by
  induction coefficients generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih, Dense.Basic.DensePolynomial.eval_add, Dense.Basic.DensePolynomial.eval_shift,
        Dense.Basic.DensePolynomial.eval_constant]

/-- Power substitution evaluates to the original polynomial at the corresponding power of the point. -/
theorem eval_substitute (polynomial : CoefficientPolynomial) (degree : Nat) (point :
  CanonicalScalar) :
    (Dense.Gaussian.Substitution.Power.substitute polynomial degree).eval point = polynomial.eval (point ^ degree) :=
  Dense.Gaussian.Substitution.Power.eval_from degree point polynomial.coeffs 0

end Purelib.Polynomial.Dense.Gaussian.Substitution.Power
