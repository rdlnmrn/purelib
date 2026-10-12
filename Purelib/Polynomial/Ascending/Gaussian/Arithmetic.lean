module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Data.List.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Coefficient

/-!
# Arithmetic of ascending Gaussian coefficient tables

Addition retains unmatched coefficient tails, scaling keeps every displayed
entry, and shifting prepends zero. Scalar readback proves the same coefficient
operations for the nominal Gaussian polynomial records.
-/

public section
namespace Purelib.Polynomial.Ascending.Gaussian.Arithmetic

open Purelib.Data
open Purelib.Polynomial

/-- Add Gaussian coefficient tables, retaining the unmatched longer tail. -/
@[expose] def add (left right : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨List.Gaussian.Arithmetic.addCoefficients left.coefficients right.coefficients⟩

/-- Multiply every retained coefficient by the Gaussian factor. -/
@[expose] def scale (factor : Gaussian.Basic.Canonical) (polynomial : CoefficientPolynomial) :
  CoefficientPolynomial :=
  ⟨polynomial.coefficients.map (factor * ·)⟩

/-- Multiplication by the local indeterminate. -/
@[expose] def shift (polynomial : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨0 :: polynomial.coefficients⟩

/-- Reading padded Gaussian addition gives the sum of the two coefficients.

The same displayed degree reads each retained input table with zero padding.
Scalar identities handle an empty spine; paired heads retain the recursive tail. -/
theorem coefficientList_add : ∀ (left right : List Gaussian.Basic.Canonical) (degree : Nat),
    Ascending.Gaussian.Coefficient.coefficientList (List.Gaussian.Arithmetic.addCoefficients left right) degree =
      Ascending.Gaussian.Coefficient.coefficientList left degree + Ascending.Gaussian.Coefficient.coefficientList right
        degree
  | [], right, degree => by
      change Ascending.Gaussian.Coefficient.coefficientList right degree =
        0 + Ascending.Gaussian.Coefficient.coefficientList right degree
      exact (_root_.zero_add _).symm
  | head :: tail, [], degree => by
      change Ascending.Gaussian.Coefficient.coefficientList (head :: tail) degree =
        Ascending.Gaussian.Coefficient.coefficientList (head :: tail) degree + 0
      exact (_root_.add_zero _).symm
  | left :: leftTail, right :: rightTail, 0 => rfl
  | _ :: leftTail, _ :: rightTail, degree + 1 =>
      Purelib.Polynomial.Ascending.Gaussian.Arithmetic.coefficientList_add leftTail rightTail degree

/-- Gaussian polynomial addition adds each coefficient. -/
@[simp] theorem coefficient_add (left right : CoefficientPolynomial) (degree : Nat) :
    Ascending.Gaussian.Coefficient.coefficient (add left right) degree =
      Ascending.Gaussian.Coefficient.coefficient left degree + Ascending.Gaussian.Coefficient.coefficient right degree
        :=
  coefficientList_add left.coefficients right.coefficients degree

/-- Scaling a Gaussian table scales each zero-padded coefficient.

A present coefficient is multiplied by the same retained factor. Past the
displayed table, multiplication by zero supplies the identical padded value. -/
theorem coefficientList_scale (factor : Gaussian.Basic.Canonical) :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (degree : Nat),
      Ascending.Gaussian.Coefficient.coefficientList (coefficients.map (factor * ·)) degree =
        factor * Ascending.Gaussian.Coefficient.coefficientList coefficients degree
  | [], _ => by
      change 0 = factor * 0
      exact (Gaussian.Basic.mul_zero factor).symm
  | _ :: _, 0 => rfl
  | _ :: tail, degree + 1 => Purelib.Polynomial.Ascending.Gaussian.Arithmetic.coefficientList_scale factor tail degree

/-- Scaling a Gaussian polynomial scales every coefficient. -/
@[simp] theorem coefficient_scale (factor : Gaussian.Basic.Canonical) (polynomial : CoefficientPolynomial)
    (degree : Nat) :
    Ascending.Gaussian.Coefficient.coefficient (scale factor polynomial) degree = factor *
      Ascending.Gaussian.Coefficient.coefficient polynomial degree :=
  coefficientList_scale factor polynomial.coefficients degree

/-- A one-degree shift has zero constant coefficient. -/
@[simp] theorem coefficient_shift_zero (polynomial : CoefficientPolynomial) :
    Ascending.Gaussian.Coefficient.coefficient (shift polynomial) 0 = 0 := rfl

/-- A one-degree shift moves each original coefficient to the next degree. -/
@[simp] theorem coefficient_shift_succ (polynomial : CoefficientPolynomial) (degree : Nat) :
    Ascending.Gaussian.Coefficient.coefficient (shift polynomial) (degree + 1) =
      Ascending.Gaussian.Coefficient.coefficient polynomial degree := rfl

/-- Gaussian polynomial addition preserves coefficientwise equality in both arguments. -/
theorem coefficientwise_add {left left' right right' : CoefficientPolynomial}
    (leftEqual : Ascending.Gaussian.Coefficient.CoefficientwiseEqual left left')
    (rightEqual : Ascending.Gaussian.Coefficient.CoefficientwiseEqual right right') :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (add left right) (add left' right') := by
  intro degree
  rw [coefficient_add, coefficient_add, leftEqual degree, rightEqual degree]

/-- Gaussian scaling preserves coefficientwise equality. -/
theorem coefficientwise_scale (factor : Gaussian.Basic.Canonical) {left right : CoefficientPolynomial}
    (equal : Ascending.Gaussian.Coefficient.CoefficientwiseEqual left right) :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (scale factor left) (scale factor right) := by
  intro degree
  rw [coefficient_scale, coefficient_scale, equal degree]

/-- A one-degree shift preserves Gaussian coefficientwise equality. -/
theorem coefficientwise_shift {left right : CoefficientPolynomial}
    (equal : Ascending.Gaussian.Coefficient.CoefficientwiseEqual left right) :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (shift left) (shift right) := by
  intro degree
  cases degree with
  | zero => rfl
  | succ degree => exact equal degree

end Purelib.Polynomial.Ascending.Gaussian.Arithmetic
end
