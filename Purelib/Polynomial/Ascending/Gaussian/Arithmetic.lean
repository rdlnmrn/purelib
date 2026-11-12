module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
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
open Purelib.Algebra.FiniteSum

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

/-- Divide a finite coefficient table by an indeterminate power, retaining its literal higher-degree tail.

The operation drops the displayed number of low entries without normalization.
When those entries are zero, evaluation factors by exactly that power.
-/
@[expose] def divideByPower (degree : Nat) (polynomial : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨polynomial.coefficients.drop degree⟩

/-- Division by a displayed indeterminate power retains the actual supplied coefficient-list tail. -/
theorem divideByPower_coefficients (degree : Nat) (polynomial : CoefficientPolynomial) :
    (divideByPower degree polynomial).coefficients = polynomial.coefficients.drop degree := rfl

/-- Division by the zeroth power retains the complete original polynomial. -/
theorem divideByPower_zero (polynomial : CoefficientPolynomial) : divideByPower 0 polynomial = polynomial := rfl

/-- Reading padded Gaussian addition gives the sum of the two coefficients.

The same displayed degree reads each retained input table with zero padding.
Scalar identities handle an empty spine; paired heads retain the recursive tail. -/
theorem coefficientList_add : ∀ (left right : List Gaussian.Basic.Canonical) (degree : Nat),
    Coefficient.coefficientList (List.Gaussian.Arithmetic.addCoefficients left right) degree =
      Coefficient.coefficientList left degree + Coefficient.coefficientList right
        degree
  | [], right, degree => by
      change Coefficient.coefficientList right degree =
        0 + Coefficient.coefficientList right degree
      exact (_root_.zero_add _).symm
  | head :: tail, [], degree => by
      change Coefficient.coefficientList (head :: tail) degree =
        Coefficient.coefficientList (head :: tail) degree + 0
      exact (_root_.add_zero _).symm
  | left :: leftTail, right :: rightTail, 0 => rfl
  | _ :: leftTail, _ :: rightTail, degree + 1 =>
      Arithmetic.coefficientList_add leftTail rightTail degree

/-- Gaussian polynomial addition adds each coefficient. -/
@[simp] theorem coefficient_add (left right : CoefficientPolynomial) (degree : Nat) :
    Coefficient.coefficient (add left right) degree =
      Coefficient.coefficient left degree + Coefficient.coefficient right degree
        :=
  coefficientList_add left.coefficients right.coefficients degree

/-- Scaling a Gaussian table scales each zero-padded coefficient.

A present coefficient is multiplied by the same retained factor. Past the
displayed table, multiplication by zero supplies the identical padded value. -/
theorem coefficientList_scale (factor : Gaussian.Basic.Canonical) :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (degree : Nat),
      Coefficient.coefficientList (coefficients.map (factor * ·)) degree =
        factor * Coefficient.coefficientList coefficients degree
  | [], _ => by
      change 0 = factor * 0
      exact (Gaussian.Basic.mul_zero factor).symm
  | _ :: _, 0 => rfl
  | _ :: tail, degree + 1 => Arithmetic.coefficientList_scale factor tail degree

/-- Scaling a Gaussian polynomial scales every coefficient. -/
@[simp] theorem coefficient_scale (factor : Gaussian.Basic.Canonical) (polynomial : CoefficientPolynomial)
    (degree : Nat) :
    Coefficient.coefficient (scale factor polynomial) degree = factor *
      Coefficient.coefficient polynomial degree :=
  coefficientList_scale factor polynomial.coefficients degree

/-- A one-degree shift has zero constant coefficient. -/
@[simp] theorem coefficient_shift_zero (polynomial : CoefficientPolynomial) :
    Coefficient.coefficient (shift polynomial) 0 = 0 := rfl

/-- A one-degree shift moves each original coefficient to the next degree. -/
@[simp] theorem coefficient_shift_succ (polynomial : CoefficientPolynomial) (degree : Nat) :
    Coefficient.coefficient (shift polynomial) (degree + 1) =
      Coefficient.coefficient polynomial degree := rfl

/-- Gaussian polynomial addition preserves coefficientwise equality in both arguments. -/
theorem coefficientwise_add {left left' right right' : CoefficientPolynomial}
    (leftEqual : Coefficient.CoefficientwiseEqual left left')
    (rightEqual : Coefficient.CoefficientwiseEqual right right') :
    Coefficient.CoefficientwiseEqual (add left right) (add left' right') := by
  intro degree
  rw [coefficient_add, coefficient_add, leftEqual degree, rightEqual degree]

/-- Gaussian scaling preserves coefficientwise equality. -/
theorem coefficientwise_scale (factor : Gaussian.Basic.Canonical) {left right : CoefficientPolynomial}
    (equal : Coefficient.CoefficientwiseEqual left right) :
    Coefficient.CoefficientwiseEqual (scale factor left) (scale factor right) := by
  intro degree
  rw [coefficient_scale, coefficient_scale, equal degree]

/-- A one-degree shift preserves Gaussian coefficientwise equality. -/
theorem coefficientwise_shift {left right : CoefficientPolynomial}
    (equal : Coefficient.CoefficientwiseEqual left right) :
    Coefficient.CoefficientwiseEqual (shift left) (shift right) := by
  intro degree
  cases degree with
  | zero => rfl
  | succ degree => exact equal degree

/-- Multiply ascending Gaussian coefficient lists by the original finite convolution recursion.

Each left entry scales the same right table, and the actual retained left tail
produces the shifted remaining product. No normalization discards stored zeros. -/
@[expose] def mulCoefficients : List Gaussian.Basic.Canonical → List Gaussian.Basic.Canonical →
    List Gaussian.Basic.Canonical
  | [], _ => []
  | head :: tail, right => List.Gaussian.Arithmetic.addCoefficients (right.map (head * ·))
      (0 :: mulCoefficients tail right)

/-- Multiply original Gaussian polynomial tables without introducing another representation. -/
@[expose] def mul (left right : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨mulCoefficients left.coefficients right.coefficients⟩

/-- Multiplication with a retained left head preserves the exact original scale, shift and tail construction. -/
theorem mul_cons (head : Gaussian.Basic.Canonical) (tail : List Gaussian.Basic.Canonical)
    (right : CoefficientPolynomial) :
    mul ⟨head :: tail⟩ right = add (scale head right) (shift (mul ⟨tail⟩ right)) := rfl

/-- The actual Gaussian product coefficient is its complementary-degree finite convolution. -/
theorem coefficient_mul (left right : CoefficientPolynomial) (degree : Nat) :
    Coefficient.coefficient (mul left right) degree =
      Prefix.prefixSum (degree + 1) (fun index =>
        Coefficient.coefficient left index * Coefficient.coefficient right (degree - index)) := by
  cases left with
  | mk left =>
      induction left generalizing degree with
      | nil =>
          change 0 = Prefix.prefixSum (degree + 1) (fun index =>
            0 * Coefficient.coefficient right (degree - index))
          exact ((Prefix.prefixSum_congr (degree + 1) _ _
            (fun _ _ => Gaussian.Basic.zero_mul _)).trans
              (Prefix.prefixSum_zero_values (degree + 1))).symm
      | cons head tail inductionHypothesis =>
          rewrite [mul_cons, coefficient_add, coefficient_scale]
          cases degree with
          | zero =>
              rewrite [coefficient_shift_zero, Prefix.prefixSum_succ,
                Prefix.prefixSum_zero]
              change head * Coefficient.coefficient right 0 + 0 = head * Coefficient.coefficient right 0 + 0
              rfl
          | succ degree =>
              rewrite [coefficient_shift_succ, inductionHypothesis]
              have sameTail :
                  Prefix.prefixSum (degree + 1) (fun index =>
                    Coefficient.coefficient ⟨tail⟩ index * Coefficient.coefficient right (degree - index)) =
                  Prefix.prefixSum (degree + 1) (fun index =>
                    Coefficient.coefficient ⟨tail⟩ index *
                      Coefficient.coefficient right (degree + 1 - (index + 1))) := by
                apply Prefix.prefixSum_congr
                intro index _
                rewrite [Nat.succ_sub_succ]
                rfl
              exact congrArg (head * Coefficient.coefficient right (degree + 1) + ·) sameTail

/-- Left addition distributes through the same finite Gaussian multiplication coefficient. -/
theorem coefficient_mul_add_left (left middle right : CoefficientPolynomial) (degree : Nat) :
    Coefficient.coefficient (mul (add left middle) right) degree =
      Coefficient.coefficient (mul left right) degree + Coefficient.coefficient (mul middle right) degree := by
  rewrite [coefficient_mul, coefficient_mul, coefficient_mul]
  exact (Prefix.prefixSum_congr (degree + 1) _ _ (fun index _ => by
    rewrite [coefficient_add]
    ring1)).trans (Prefix.prefixSum_add _ _ _)

/-- Right addition distributes through the same finite Gaussian multiplication coefficient. -/
theorem coefficient_mul_add_right (left middle right : CoefficientPolynomial) (degree : Nat) :
    Coefficient.coefficient (mul left (add middle right)) degree =
      Coefficient.coefficient (mul left middle) degree + Coefficient.coefficient (mul left right) degree := by
  rewrite [coefficient_mul, coefficient_mul, coefficient_mul]
  exact (Prefix.prefixSum_congr (degree + 1) _ _ (fun index _ => by
    rewrite [coefficient_add]
    ring1)).trans (Prefix.prefixSum_add _ _ _)

/-- A retained left scalar is extracted from each coefficient of the actual product. -/
theorem coefficient_mul_scale_left (factor : Gaussian.Basic.Canonical) (left right : CoefficientPolynomial)
    (degree : Nat) : Coefficient.coefficient (mul (scale factor left) right) degree =
      factor * Coefficient.coefficient (mul left right) degree := by
  rewrite [coefficient_mul, coefficient_mul]
  exact (Prefix.prefixSum_congr (degree + 1) _ _ (fun index _ => by
    rewrite [coefficient_scale]
    ring1)).trans (Prefix.prefixSum_mul_left _ _ _)

/-- A shifted left factor contributes zero to the product's constant coordinate. -/
theorem coefficient_mul_shift_zero (left right : CoefficientPolynomial) :
    Coefficient.coefficient (mul (shift left) right) 0 = 0 := by
  rewrite [coefficient_mul, Prefix.prefixSum_succ,
    Prefix.prefixSum_zero, coefficient_shift_zero]
  ring1

/-- A shifted left factor shifts the identical retained product coefficient once. -/
theorem coefficient_mul_shift_succ (left right : CoefficientPolynomial) (degree : Nat) :
    Coefficient.coefficient (mul (shift left) right) (degree + 1) =
      Coefficient.coefficient (mul left right) degree := by
  rewrite [coefficient_mul, Prefix.prefixSum_succ,
    coefficient_shift_zero, Gaussian.Basic.zero_mul, Gaussian.Basic.zero_add, coefficient_mul]
  apply Prefix.prefixSum_congr
  intro index _
  rewrite [coefficient_shift_succ, Nat.succ_sub_succ]
  rfl

/-- Equal retained input coefficients give equal coefficients of the actual multiplication. -/
theorem coefficientwise_mul {left left' right right' : CoefficientPolynomial}
    (leftEqual : Coefficient.CoefficientwiseEqual left left')
    (rightEqual : Coefficient.CoefficientwiseEqual right right') :
    Coefficient.CoefficientwiseEqual (mul left right) (mul left' right') := by
  intro degree
  rewrite [coefficient_mul, coefficient_mul]
  apply Prefix.prefixSum_congr
  intro index _
  rewrite [leftEqual index, rightEqual (degree - index)]
  rfl

/-- Reversing complementary finite degrees proves Gaussian multiplication commutative coefficientwise. -/
theorem coefficient_mul_comm (left right : CoefficientPolynomial) (degree : Nat) :
    Coefficient.coefficient (mul left right) degree = Coefficient.coefficient (mul right left) degree := by
  rewrite [coefficient_mul, coefficient_mul, Prefix.prefixSum_reverse]
  apply Prefix.prefixSum_congr
  intro index bound
  have reverse : degree - (degree - index) = index := by omega
  rewrite [show degree + 1 - 1 - index = degree - index by omega, reverse]
  ring1

/-- The finite Gaussian table product is associative coefficientwise.

The proof follows the original left table. Its head scales the same remaining
product, and the literal retained tail contributes after the original shift. -/
theorem coefficient_mul_assoc (left middle right : CoefficientPolynomial) (degree : Nat) :
    Coefficient.coefficient (mul (mul left middle) right) degree =
      Coefficient.coefficient (mul left (mul middle right)) degree := by
  cases left with
  | mk left =>
      induction left generalizing degree with
      | nil => rfl
      | cons head tail inductionHypothesis =>
          rewrite [mul_cons, coefficient_mul_add_left, coefficient_mul_scale_left, mul_cons,
            coefficient_add, coefficient_scale]
          cases degree with
          | zero =>
              rewrite [coefficient_mul_shift_zero, coefficient_shift_zero]
              rfl
          | succ degree =>
              rewrite [coefficient_mul_shift_succ, coefficient_shift_succ, inductionHypothesis]
              rfl

/-- Interchanging the two retained final factors preserves every product coefficient. -/
theorem coefficient_mul_swap_tail (left middle right : CoefficientPolynomial) (degree : Nat) :
    Coefficient.coefficient (mul (mul left middle) right) degree =
      Coefficient.coefficient (mul (mul left right) middle) degree :=
  (coefficient_mul_assoc left middle right degree).trans
    ((coefficientwise_mul (Coefficient.coefficientwise_refl left)
      (fun index => coefficient_mul_comm middle right index) degree).trans
        (coefficient_mul_assoc left right middle degree).symm)

end Purelib.Polynomial.Ascending.Gaussian.Arithmetic
end
