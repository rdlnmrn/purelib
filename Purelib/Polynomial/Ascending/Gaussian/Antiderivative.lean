module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Natural.Inverse
import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Coefficient
public import Purelib.Polynomial.Ascending.Gaussian.Derivative
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Gaussian polynomial antiderivatives

Finite coefficient tables determine a zero-constant antiderivative by division
by positive natural degree weights. Coefficient readback, differentiation and
coefficientwise linearity describe this exact finite construction.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Antiderivative

open Purelib.Data
open Purelib.Polynomial

public section

/-- Divide the coefficient table by its successive positive degree weights.

The offset determines the first divisor. Each retained coefficient is divided
by its new degree, and the remaining table is integrated at the next offset. -/
@[expose] def antiderivativeCoefficients : Nat -> List Gaussian.Basic.Canonical -> List Gaussian.Basic.Canonical
  | _, [] => []
  | degree, coefficient :: remaining =>
      (coefficient / ((degree + 1 : Nat) : Gaussian.Basic.Canonical)) ::
        Purelib.Polynomial.Ascending.Gaussian.Antiderivative.antiderivativeCoefficients (degree + 1) remaining

/-- Construct the zero-constant Gaussian antiderivative.

Each original coefficient is divided by its positive new degree, then a zero constant coefficient is prepended. -/
@[expose] def antiderivative (polynomial : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨0 :: antiderivativeCoefficients 0 polynomial.coefficients⟩

/-- Read an integrated coefficient as the retained entry divided by its new degree.

The finite table starts at the supplied offset. Its entry at each degree is
weighted by that offset plus the degree plus one, including zero beyond the table. -/
theorem coefficientList_antiderivativeCoefficients : ∀ (start : Nat)
    (coefficients : List Gaussian.Basic.Canonical) (degree : Nat),
    Ascending.Gaussian.Coefficient.coefficientList (antiderivativeCoefficients start coefficients) degree =
      Ascending.Gaussian.Coefficient.coefficientList coefficients degree / ((start + degree + 1 : Nat) :
        Gaussian.Basic.Canonical)
  | start, [], degree => by
      change (0 : Gaussian.Basic.Canonical) = 0 / ((start + degree + 1 : Nat) : Gaussian.Basic.Canonical)
      exact (Purelib.Algebra.Field.ExplicitField.zero_div _).symm
  | start, head :: _, 0 => by
      change head / ((start + 1 : Nat) : Gaussian.Basic.Canonical) =
        head / ((start + 0 + 1 : Nat) : Gaussian.Basic.Canonical)
      rw [Nat.add_zero]
  | start, _ :: tail, degree + 1 => by
      change Ascending.Gaussian.Coefficient.coefficientList (antiderivativeCoefficients (start + 1) tail) degree = _
      rw [Purelib.Polynomial.Ascending.Gaussian.Antiderivative.coefficientList_antiderivativeCoefficients]
      have indices : start + 1 + degree + 1 = start + (degree + 1) + 1 := by omega
      rw [indices]
      rfl

/-- The constructed Gaussian antiderivative has zero constant coefficient. -/
@[simp] theorem coefficient_antiderivative_zero (polynomial : CoefficientPolynomial) :
    Ascending.Gaussian.Coefficient.coefficient (antiderivative polynomial) 0 = 0 := rfl

/-- An antiderivative coefficient is the preceding original coefficient divided by its new degree. -/
@[simp] theorem coefficient_antiderivative_succ (polynomial : CoefficientPolynomial) (degree : Nat) :
    Ascending.Gaussian.Coefficient.coefficient (antiderivative polynomial) (degree + 1) =
      Ascending.Gaussian.Coefficient.coefficient polynomial degree / ((degree + 1 : Nat) : Gaussian.Basic.Canonical) :=
        by
  change Ascending.Gaussian.Coefficient.coefficientList (antiderivativeCoefficients 0 polynomial.coefficients) degree =
    _
  rw [coefficientList_antiderivativeCoefficients, Nat.zero_add]
  rfl

/-- Positive natural degree weights cancel coefficient integration exactly.

The resulting Gaussian list is literally the original retained table. -/
theorem derivativeFrom_antiderivativeCoefficients : ∀ (degree : Nat)
    (coefficients : List Gaussian.Basic.Canonical),
    Ascending.Gaussian.Derivative.derivativeFrom (degree + 1) (antiderivativeCoefficients degree coefficients) =
      coefficients
  | _, [] => rfl
  | degree, head :: tail => by
      rw [antiderivativeCoefficients, Ascending.Gaussian.Derivative.derivativeFrom,
        Purelib.Data.Gaussian.Natural.Inverse.positiveDegree_cancel,
        Purelib.Polynomial.Ascending.Gaussian.Antiderivative.derivativeFrom_antiderivativeCoefficients]

/-- The generated primitive differentiates to the original finite list exactly. -/
theorem derivative_antiderivative (polynomial : CoefficientPolynomial) :
    Ascending.Gaussian.Derivative.derivative (antiderivative polynomial) = polynomial := by
  cases polynomial with
  | mk coefficients =>
      change (⟨Ascending.Gaussian.Derivative.derivativeFrom 1 (antiderivativeCoefficients 0 coefficients)⟩ :
        CoefficientPolynomial) = _
      rw [show 1 = 0 + 1 from rfl, derivativeFrom_antiderivativeCoefficients]

/-- Coefficient integration cancels matching positive natural derivative weights exactly. -/
theorem antiderivativeCoefficients_derivativeFrom : ∀ (degree : Nat)
    (coefficients : List Gaussian.Basic.Canonical),
    antiderivativeCoefficients degree (Ascending.Gaussian.Derivative.derivativeFrom (degree + 1) coefficients) =
      coefficients
  | _, [] => rfl
  | degree, head :: tail => by
      rw [Ascending.Gaussian.Derivative.derivativeFrom, antiderivativeCoefficients,
        Purelib.Data.Gaussian.Natural.Inverse.positiveDegree_div_cancel,
        antiderivativeCoefficients_derivativeFrom]

/-- The zero-constant antiderivative preserves coefficientwise equality. -/
theorem coefficientwise_antiderivative {left right : CoefficientPolynomial}
    (equal : Ascending.Gaussian.Coefficient.CoefficientwiseEqual left right) :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (antiderivative left) (antiderivative right) := by
  intro degree
  cases degree with
  | zero => rfl
  | succ degree =>
      rw [coefficient_antiderivative_succ, coefficient_antiderivative_succ, equal degree]

/-- The zero-constant Gaussian antiderivative preserves coefficientwise addition.

Both summands use the same positive degree divisor at each nonconstant entry.
The constructed constant entries are zero, so their sum is also zero. -/
theorem antiderivative_add (left right : CoefficientPolynomial) :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (antiderivative (Ascending.Gaussian.Arithmetic.add left right))
      (Ascending.Gaussian.Arithmetic.add (antiderivative left) (antiderivative right)) := open Purelib.Algebra.Field in
        by
  intro degree
  cases degree with
  | zero =>
      rw [Ascending.Gaussian.Arithmetic.coefficient_add]
      change (0 : Gaussian.Basic.Canonical) = 0 + 0
      exact (_root_.add_zero (0 : Gaussian.Basic.Canonical)).symm
  | succ degree =>
      simp only [coefficient_antiderivative_succ, Ascending.Gaussian.Arithmetic.coefficient_add,
        ExplicitField.div_eq_mul_inv]
      ring1

/-- The zero-constant Gaussian antiderivative commutes with scalar multiplication.

Each nonconstant coefficient is divided by its positive degree weight. The same
scalar therefore acts on the integrated table, while its constant remains zero. -/
theorem antiderivative_scale (factor : Gaussian.Basic.Canonical) (polynomial : CoefficientPolynomial) :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (antiderivative (Ascending.Gaussian.Arithmetic.scale factor
      polynomial))
      (Ascending.Gaussian.Arithmetic.scale factor (antiderivative polynomial)) := open Purelib.Algebra.Field in by
  intro degree
  cases degree with
  | zero =>
      rw [Ascending.Gaussian.Arithmetic.coefficient_scale]
      change (0 : Gaussian.Basic.Canonical) = factor * 0
      exact (Gaussian.Basic.mul_zero factor).symm
  | succ degree =>
      simp only [coefficient_antiderivative_succ, Ascending.Gaussian.Arithmetic.coefficient_scale,
        ExplicitField.div_eq_mul_inv]
      ring1

end

end Purelib.Polynomial.Ascending.Gaussian.Antiderivative
