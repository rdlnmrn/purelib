module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Polynomial.Ascending.Rational.Monomial

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Ascending.Rational.Basic (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Polynomial.Ascending.Rational.Evaluation

/-- Evaluate an ascending rational coefficient list by finite Horner recursion. -/
def scalarEvalCoefficients (radius : Fraction.Rational) :
    List Fraction.Rational → Fraction.Rational
  | [] => 0
  | coefficient :: remaining =>
      coefficient + radius * scalarEvalCoefficients radius remaining

/-- Evaluate a retained rational polynomial at a rational argument. -/
def scalarEval (radius : Fraction.Rational) (polynomial :
  CoefficientPolynomial) : Fraction.Rational :=
  scalarEvalCoefficients radius polynomial.coefficients

/-- Scalar Horner evaluation preserves padded coefficient-list addition. -/
theorem scalarEvalCoefficients_add (radius : Fraction.Rational)
  : ∀ left right,
    scalarEvalCoefficients radius (Ascending.Rational.Basic.addCoefficients left right) =
      scalarEvalCoefficients radius left +
        scalarEvalCoefficients radius right
  | [], right => by
      rw [Ascending.Rational.Basic.addCoefficients, scalarEvalCoefficients,
        Fraction.Field.zero_add]
  | left, [] => by
      rw [Ascending.Rational.Basic.addCoefficients_nil_right, scalarEvalCoefficients]
      ring1
  | left :: leftTail, right :: rightTail => by
      rw [Ascending.Rational.Basic.addCoefficients, scalarEvalCoefficients,
        scalarEvalCoefficients, scalarEvalCoefficients,
        scalarEvalCoefficients_add radius leftTail rightTail]
      ring1

/-- Scalar evaluation preserves polynomial addition. -/
@[simp] theorem scalarEval_add (radius : Fraction.Rational)
    (left right : CoefficientPolynomial) :
    scalarEval radius (Ascending.Rational.Basic.add left right) =
      scalarEval radius left + scalarEval radius right :=
  scalarEvalCoefficients_add radius left.coefficients right.coefficients

/-- A prefixed zero block contributes the corresponding power of the evaluation argument. -/
theorem scalarEvalCoefficients_shift (radius :
  Fraction.Rational) :
    ∀ count coefficients,
      scalarEvalCoefficients radius
          (List.replicate count 0 ++ coefficients) =
        radius ^ count * scalarEvalCoefficients radius coefficients
  | 0, coefficients => by
      rw [List.replicate_zero, List.nil_append, pow_zero]
      ring1
  | count + 1, coefficients => by
      rw [List.replicate_succ, List.cons_append, scalarEvalCoefficients,
        scalarEvalCoefficients_shift radius count coefficients,
          pow_succ]
      ring1

/-- Evaluation of a shifted polynomial is the argument power times the original value. -/
@[simp] theorem scalarEval_shift (radius : Fraction.Rational)
  (count : Nat)
    (polynomial : CoefficientPolynomial) :
    scalarEval radius (Ascending.Rational.Basic.shift count polynomial) =
      radius ^ count * scalarEval radius polynomial :=
  scalarEvalCoefficients_shift radius count polynomial.coefficients

/-- Evaluation of a constant polynomial returns its rational value. -/
@[simp] theorem scalarEval_constant (radius value :
  Fraction.Rational) :
    scalarEval radius (Ascending.Rational.Basic.constant value) = value := by
  change value + radius * 0 = value
  ring1

/-- Evaluation of a monomial is its coefficient times the argument raised to its degree. -/
@[simp] theorem scalarEval_monomial (radius : Fraction.Rational)
  (degree : Nat)
    (value : Fraction.Rational) :
    scalarEval radius (Ascending.Rational.Monomial.monomial degree value) = value * radius
      ^ degree := by
  rw [Ascending.Rational.Monomial.monomial, scalarEval_shift,
    scalarEval_constant]
  ring1
end Purelib.Polynomial.Ascending.Rational.Evaluation

end
