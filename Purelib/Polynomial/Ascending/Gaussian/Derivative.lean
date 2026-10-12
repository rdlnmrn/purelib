module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Coefficient
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

import Purelib.Algebra.NatCast

/-!
# Gaussian coefficient differentiation

Finite ascending coefficient tables are differentiated using their original
natural degree weights. Readback and coefficientwise linearity concern the
same exact retained entries, including zero padding beyond the finite table.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Derivative

open Purelib.Data
open Purelib.Polynomial
open Purelib.Algebra

public section
/-- Differentiate the retained coefficient tail from its explicit degree offset.

Each original entry is multiplied by its natural degree weight. The same tail
is processed at the next offset, preserving its order and repeated entries. -/
@[expose] def derivativeFrom : Nat → List Gaussian.Basic.Canonical → List Gaussian.Basic.Canonical
  | _, [] => []
  | factor, head :: tail =>
      (factor : Gaussian.Basic.Canonical) * head :: Purelib.Polynomial.Ascending.Gaussian.Derivative.derivativeFrom
        (factor + 1) tail

/-- Differentiate the ascending Gaussian coefficient table.

Discard the constant coefficient and multiply the remaining entries by their positive original degrees. -/
@[expose] def derivative (polynomial : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨derivativeFrom 1 polynomial.coefficients.tail⟩

/-- Read a degree-weighted entry as its original coefficient times its degree weight.

The starting offset is added to the requested coefficient coordinate. The
identity includes empty tables and coordinates beyond the retained list. -/
theorem coefficientList_derivativeFrom : ∀ (factor : Nat)
    (coefficients : List Gaussian.Basic.Canonical) (degree : Nat),
    Ascending.Gaussian.Coefficient.coefficientList (derivativeFrom factor coefficients) degree =
      ((factor + degree : Nat) : Gaussian.Basic.Canonical) * Ascending.Gaussian.Coefficient.coefficientList coefficients
        degree
  | factor, [], degree => by
      change (0 : Gaussian.Basic.Canonical) = ((factor + degree : Nat) : Gaussian.Basic.Canonical) * 0
      exact (Gaussian.Basic.mul_zero _).symm
  | factor, head :: _, 0 => by
      change (factor : Gaussian.Basic.Canonical) * head = ((factor + 0 : Nat) : Gaussian.Basic.Canonical) * head
      rw [Nat.add_zero]
  | factor, _ :: tail, degree + 1 => by
      change Ascending.Gaussian.Coefficient.coefficientList (derivativeFrom (factor + 1) tail) degree = _
      rw [Purelib.Polynomial.Ascending.Gaussian.Derivative.coefficientList_derivativeFrom]
      have indices : factor + 1 + degree = factor + (degree + 1) := by omega
      rw [indices]
      rfl

/-- Read a derivative coefficient using the original entry at the next degree.

Dropping the constant entry shifts the retained coordinate by one. Its positive
natural degree weight multiplies the same original coefficient, including zero padding. -/
@[simp] theorem coefficient_derivative (polynomial : CoefficientPolynomial) (degree : Nat) :
    Ascending.Gaussian.Coefficient.coefficient (derivative polynomial) degree =
      ((degree + 1 : Nat) : Gaussian.Basic.Canonical) * Ascending.Gaussian.Coefficient.coefficient polynomial (degree +
        1) := by
  cases polynomial with
  | mk coefficients =>
      cases coefficients with
      | nil =>
          change (0 : Gaussian.Basic.Canonical) = ((degree + 1 : Nat) : Gaussian.Basic.Canonical) * 0
          exact (Gaussian.Basic.mul_zero _).symm
      | cons head tail =>
          change Ascending.Gaussian.Coefficient.coefficientList (derivativeFrom 1 tail) degree = _
          rw [coefficientList_derivativeFrom, Nat.add_comm 1 degree]
          rfl

/-- Gaussian differentiation preserves coefficientwise equality. -/
theorem coefficientwise_derivative {left right : CoefficientPolynomial}
    (equal : Ascending.Gaussian.Coefficient.CoefficientwiseEqual left right) :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (derivative left) (derivative right) := by
  intro degree
  rw [coefficient_derivative, coefficient_derivative, equal (degree + 1)]

/-- Gaussian differentiation preserves addition coefficientwise. -/
theorem derivative_add (left right : CoefficientPolynomial) :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (derivative (Ascending.Gaussian.Arithmetic.add left right))
      (Ascending.Gaussian.Arithmetic.add (derivative left) (derivative right)) := by
  intro degree
  simp only [coefficient_derivative, Ascending.Gaussian.Arithmetic.coefficient_add]
  ring1

/-- Gaussian differentiation commutes with coefficient scaling. -/
theorem derivative_scale (factor : Gaussian.Basic.Canonical) (polynomial : CoefficientPolynomial) :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (derivative (Ascending.Gaussian.Arithmetic.scale factor
      polynomial))
      (Ascending.Gaussian.Arithmetic.scale factor (derivative polynomial)) := by
  intro degree
  simp only [coefficient_derivative, Ascending.Gaussian.Arithmetic.coefficient_scale]
  ring1

/-- The derivative table of a constant Gaussian polynomial is the empty zero table. -/
theorem derivative_constant (value : Gaussian.Basic.Canonical) :
    derivative (Ascending.Gaussian.Basic.constant value) = Ascending.Gaussian.Basic.zero := rfl

/-- Differentiating the empty zero polynomial returns the empty zero polynomial. -/
theorem derivative_zero : derivative Ascending.Gaussian.Basic.zero = Ascending.Gaussian.Basic.zero := rfl

/-- Shifting a polynomial satisfies the coefficientwise derivative product rule.

The zero coefficient is the original constant entry. At each positive degree,
the natural successor weight splits into the original entry and its derivative weight. -/
theorem derivative_shift (polynomial : CoefficientPolynomial) :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (derivative (Ascending.Gaussian.Arithmetic.shift polynomial))
      (Ascending.Gaussian.Arithmetic.add polynomial (Ascending.Gaussian.Arithmetic.shift (derivative polynomial))) := by
  intro degree
  cases degree with
  | zero =>
      rw [coefficient_derivative, Ascending.Gaussian.Arithmetic.coefficient_shift_succ,
        Ascending.Gaussian.Arithmetic.coefficient_add, Ascending.Gaussian.Arithmetic.coefficient_shift_zero]
      change ((1 : Nat) : Gaussian.Basic.Canonical) * Ascending.Gaussian.Coefficient.coefficient polynomial 0 =
        Ascending.Gaussian.Coefficient.coefficient polynomial 0 + 0
      rw [Nat.cast_one, _root_.one_mul, _root_.add_zero]
  | succ degree =>
      simp only [coefficient_derivative, Ascending.Gaussian.Arithmetic.coefficient_shift_succ,
        Ascending.Gaussian.Arithmetic.coefficient_add,
        NatCast.add, Nat.cast_one]
      ring1

end

end Purelib.Polynomial.Ascending.Gaussian.Derivative
