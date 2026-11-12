module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
import Purelib.Polynomial.Ascending.Rational.Convolution
public import Purelib.Polynomial.Ascending.Rational.Monomial

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Derivatives of ascending rational tables

Removing the constant term and retaining successive natural degree weights
defines the original finite derivative procedure. Scalar readback and finite
convolution prove its addition, scale and product rules.
-/

public section
namespace Purelib.Polynomial.Ascending.Rational.Derivative

open Purelib.Algebra
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Polynomial

/-- Multiply successive coefficients by successive natural factors.

The first entry is multiplied by `factor`, the next by `factor + 1`, and so on, preserving the list length. -/
@[expose] def derivativeFrom : Nat → List Fraction.Rational → List Fraction.Rational
  | _, [] => []
  | factor, coefficient :: remaining =>
      (factor : Fraction.Rational) * coefficient ::
        Derivative.derivativeFrom (factor + 1) remaining

/-- Differentiate the finite coefficient table.

Discard the constant term and multiply the remaining coefficients by their positive original degrees. -/
@[expose] def derivative (polynomial : Basic.CoefficientPolynomial) :
  Basic.CoefficientPolynomial :=
  match polynomial.coefficients with
  | [] => Basic.zero
  | _ :: remaining => ⟨derivativeFrom 1 remaining⟩

/-- Degree-weighted table readback retains the starting factor plus degree.

The same coefficient table supplies the scalar readback. Structural recursion
increments its starting factor exactly once per retained coefficient. -/
theorem coefficientCoefficients_derivativeFrom :
    ∀ factor coefficients degree,
      Basic.coefficientCoefficients (derivativeFrom factor coefficients) degree =
        ((factor + degree : Nat) : Fraction.Rational) *
          Basic.coefficientCoefficients coefficients degree
  | factor, [], degree => by
      change 0 = ((factor + degree : Nat) : Fraction.Rational) * 0
      exact (Fraction.Field.mul_zero_direct _).symm
  | factor, coefficient :: remaining, 0 => by
      change (factor : Fraction.Rational) * coefficient =
        ((factor + 0 : Nat) : Fraction.Rational) * coefficient
      rw [Nat.add_zero]
  | factor, coefficient :: remaining, degree + 1 => by
      rw [derivativeFrom, Basic.coefficientCoefficients_cons_succ,
        Derivative.coefficientCoefficients_derivativeFrom]
      congr 1
      congr 1
      calc
        factor + 1 + degree = factor + (1 + degree) :=
          Nat.add_assoc factor 1 degree
        _ = factor + (degree + 1) :=
          congrArg (factor + ·) (Nat.add_comm 1 degree)

/-- A derivative coefficient retains the next original degree and its weight.

Removing the constant coefficient shifts readback by one. The degree-weighted
tail procedure supplies the original positive natural factor at that degree. -/
theorem coefficient_derivative (polynomial : Basic.CoefficientPolynomial) (degree : Nat) :
    Basic.coefficient (derivative polynomial) degree =
      ((degree + 1 : Nat) : Fraction.Rational) * Basic.coefficient polynomial (degree + 1) := by
  cases coefficients : polynomial.coefficients with
  | nil =>
      unfold Basic.coefficient derivative
      rw [coefficients]
      change 0 = ((degree + 1 : Nat) : Fraction.Rational) * 0
      exact (Fraction.Field.mul_zero_direct _).symm
  | cons head tail =>
      unfold Basic.coefficient
      rw [derivative, coefficients,
        coefficientCoefficients_derivativeFrom]
      rw [Basic.coefficientCoefficients_cons_succ]
      rw [Nat.add_comm 1 degree]

/-- Increasing every natural degree weight adds the retained coefficient table.

Each coefficient receives one additional copy under the same rational cast.
Structural recursion preserves the original order and unmatched finite tail. -/
theorem derivativeFrom_succ_eq_add : ∀ (factor : Nat)
    (coefficients : List Fraction.Rational),
    derivativeFrom (factor + 1) coefficients =
      Basic.addCoefficients (derivativeFrom factor coefficients) coefficients
  | factor, [] => rfl
  | factor, coefficient :: remaining => by
      rw [derivativeFrom, derivativeFrom, Basic.addCoefficients,
        Derivative.derivativeFrom_succ_eq_add (factor + 1) remaining]
      congr 1
      rw [NatCast.add]
      ring1

/-- The product rule holds at each coefficient.

The degree-weighted convolution splits into the convolution with the left derivative and the convolution with the right
derivative. -/
theorem coefficient_derivative_mul (left right : Basic.CoefficientPolynomial) (degree : Nat) :
    Basic.coefficient (derivative (Basic.mul left right)) degree =
      Basic.coefficient
        (Basic.add (Basic.mul (derivative left) right)
          (Basic.mul left (derivative right))) degree := open Purelib.Algebra in by
  rw [coefficient_derivative, Convolution.coefficient_mul, Basic.coefficient_add,
    Convolution.coefficient_mul, Convolution.coefficient_mul]
  rewrite [FiniteSum.Prefix.coordinateSum_eq_prefixSum,
    FiniteSum.Prefix.coordinateSum_eq_prefixSum, FiniteSum.Prefix.coordinateSum_eq_prefixSum,
    FiniteSum.Prefix.convolution_derivative_identity]
  apply congrArg₂ (· + ·)
  · apply FiniteSum.Prefix.prefixSum_congr
    intro index _
    rw [coefficient_derivative]
  · apply FiniteSum.Prefix.prefixSum_congr
    intro index _
    rw [coefficient_derivative]
    ring1

/-- The finite polynomial derivative satisfies the product rule coefficientwise. -/
theorem derivative_mul (left right : Basic.CoefficientPolynomial) :
    Coefficientwise.CoefficientwiseEqual (derivative (Basic.mul left right))
      (Basic.add (Basic.mul (derivative left) right)
        (Basic.mul left (derivative right))) :=
  coefficient_derivative_mul left right

/-- Differentiation preserves coefficientwise equality. -/
theorem coefficientwise_derivative {left right : Basic.CoefficientPolynomial}
    (equal : Coefficientwise.CoefficientwiseEqual left right) :
    Coefficientwise.CoefficientwiseEqual (derivative left) (derivative right) := by
  intro degree
  rw [coefficient_derivative, coefficient_derivative,
    equal (degree + 1)]

/-- The derivative of the zero polynomial is coefficientwise zero. -/
theorem derivative_zero : Coefficientwise.CoefficientwiseEqual (derivative
  Basic.zero) Basic.zero := by
  intro degree
  rw [coefficient_derivative, Coefficientwise.coefficient_zero,
    Coefficientwise.coefficient_zero,
    Fraction.Field.mul_zero_direct]

/-- The derivative of a constant polynomial is coefficientwise zero. -/
theorem derivative_constant (value : Fraction.Rational) :
    Coefficientwise.CoefficientwiseEqual (derivative (Basic.constant value))
      Basic.zero := by
  intro degree
  rw [coefficient_derivative, Coefficientwise.coefficient_zero,
    Coefficientwise.coefficient_constant]
  rw [if_neg ((fun same : degree + 1 = 0 => Nat.noConfusion same)),
    Fraction.Field.mul_zero_direct]

/-- Differentiation preserves addition coefficientwise. -/
theorem derivative_add (left right : Basic.CoefficientPolynomial) :
    Coefficientwise.CoefficientwiseEqual (derivative (Basic.add left right))
      (Basic.add (derivative left) (derivative right)) := by
  intro degree
  rw [coefficient_derivative, Basic.coefficient_add, Basic.coefficient_add,
    coefficient_derivative, coefficient_derivative]
  ring1

/-- Differentiation commutes with rational scaling coefficientwise. -/
theorem derivative_scale (factor : Fraction.Rational) (polynomial : Basic.CoefficientPolynomial) :
    Coefficientwise.CoefficientwiseEqual (derivative (Basic.scale factor
      polynomial))
      (Basic.scale factor (derivative polynomial)) := by
  intro degree
  rw [coefficient_derivative, Basic.coefficient_scale, Basic.coefficient_scale,
    coefficient_derivative]
  ring1

/-- Differentiating a positive-degree monomial lowers the degree and multiplies its coefficient by the original degree.
-/
theorem derivative_monomial_succ (degree : Nat) (value : Fraction.Rational) :
    Coefficientwise.CoefficientwiseEqual (derivative (Monomial.monomial (degree +
      1) value))
      (Monomial.monomial degree (((degree + 1 : Nat) : Fraction.Rational) * value)) := by
  intro outputDegree
  rw [coefficient_derivative, Monomial.coefficient_monomial,
    Monomial.coefficient_monomial]
  by_cases equal : outputDegree = degree
  · subst outputDegree
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg equal, if_neg ((fun same => equal (Nat.succ.inj same))),
      Fraction.Field.mul_zero_direct]

end Purelib.Polynomial.Ascending.Rational.Derivative
end
