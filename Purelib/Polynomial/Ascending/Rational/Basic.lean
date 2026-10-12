module

import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Ascending rational coefficient tables

Finite nominal polynomials retain their coefficient order, trailing zeros and
exact scalar entries. Direct table operations and zero-padded readback supply
addition, convolution, shifts and natural powers without normalization.
-/

public section
namespace Purelib.Polynomial.Ascending.Rational.Basic

open Purelib.Data.Rat
open Purelib.Polynomial

@[expose] public section
set_option genInjectivity false in
/-- A finite rational coefficient table in ascending degree order.

The constant coefficient comes first. Trailing zeros are retained, so distinct tables can represent the same
coefficients at every degree; `CoefficientwiseEqual` expresses that relation separately. -/
structure CoefficientPolynomial where
  /-- The retained coefficient list, starting with the constant term. -/ coefficients : List Fraction.Rational
deriving DecidableEq

constructive_injectivity CoefficientPolynomial

end

/-- The zero polynomial represented by an empty coefficient list. -/
@[expose] def zero : CoefficientPolynomial := ⟨[]⟩
/-- The constant one polynomial represented by `[1]`. -/
@[expose] def one : CoefficientPolynomial := ⟨[1]⟩
/-- The indeterminate represented by `[0, 1]`. -/
@[expose] def indeterminate : CoefficientPolynomial := ⟨[0, 1]⟩
/-- Represent a rational constant by its singleton coefficient list. -/
@[expose] def constant (value : Fraction.Rational) : CoefficientPolynomial := ⟨[value]⟩

/-- Add ascending coefficient lists, retaining any unmatched tail.

Entries beyond the shorter list are treated as zero. The operation preserves displayed trailing zeros instead of
normalizing the result. -/
@[expose] def addCoefficients : List Fraction.Rational → List Fraction.Rational → List Fraction.Rational
  | [], right => right
  | left, [] => left
  | left :: leftTail, right :: rightTail =>
      (left + right) :: Purelib.Polynomial.Ascending.Rational.Basic.addCoefficients leftTail rightTail

/-- Adding an empty coefficient list on the right preserves the original list. -/
theorem addCoefficients_nil_right : ∀ coefficients,
    addCoefficients coefficients [] = coefficients
  | [] => rfl
  | _ :: _ => rfl

/-- Add two polynomials by adding their ascending coefficient tables. -/
@[expose] def add (left right : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨addCoefficients left.coefficients right.coefficients⟩

/-- Multiply every retained coefficient by the rational factor. -/
@[expose] def scale (factor : Fraction.Rational) (polynomial : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨polynomial.coefficients.map (factor * ·)⟩

/-- Multiply by a power of the indeterminate by prepending zero coefficients. -/
@[expose] def shift (count : Nat) (polynomial : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨List.replicate count 0 ++ polynomial.coefficients⟩

/-- Multiply ascending coefficient lists by finite convolution.

Each left coefficient scales the right list, while recursion shifts the remaining product by one degree. The displayed
output is not trimmed. -/
@[expose] def mulCoefficients : List Fraction.Rational → List Fraction.Rational → List Fraction.Rational
  | [], _ => []
  | left :: leftTail, right =>
      addCoefficients (right.map (left * ·))
        (0 :: Purelib.Polynomial.Ascending.Rational.Basic.mulCoefficients leftTail right)

/-- Multiply two retained polynomials by convolution of their coefficient lists. -/
@[expose] def mul (left right : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨mulCoefficients left.coefficients right.coefficients⟩

/-- Compute a natural power by repeated multiplication, starting with the constant one polynomial. -/
@[expose] def pow : CoefficientPolynomial → Nat → CoefficientPolynomial
  | _, 0 => one
  | polynomial, exponent + 1 => mul (pow polynomial exponent) polynomial

/-- Retain the first `count` coefficients, covering degrees strictly below `count`. -/
@[expose] def truncate (count : Nat) (polynomial : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨polynomial.coefficients.take count⟩

/-- Read a coefficient from an ascending list, returning zero beyond its length. -/
@[expose] def coefficientCoefficients : List Fraction.Rational → Nat → Fraction.Rational
  | [], _ => 0
  | coefficient :: _, 0 => coefficient
  | _ :: remaining, degree + 1 =>
      Purelib.Polynomial.Ascending.Rational.Basic.coefficientCoefficients remaining degree

/-- Read the coefficient at the requested degree, using zero outside the retained table. -/
@[expose] def coefficient (polynomial : CoefficientPolynomial) (degree : Nat) : Fraction.Rational :=
  coefficientCoefficients polynomial.coefficients degree

/-- Every coefficient of an empty table is zero. -/
@[simp] theorem coefficientCoefficients_nil (degree : Nat) :
    coefficientCoefficients [] degree = 0 := by cases degree <;> rfl

/-- The degree-zero coefficient is the head of the table. -/
@[simp] theorem coefficientCoefficients_cons_zero
    (head : Fraction.Rational) (tail : List Fraction.Rational) :
    coefficientCoefficients (head :: tail) 0 = head := rfl

/-- Reading a positive degree reduces to the preceding degree in the tail. -/
@[simp] theorem coefficientCoefficients_cons_succ
    (head : Fraction.Rational) (tail : List Fraction.Rational) (degree : Nat) :
    coefficientCoefficients (head :: tail) (degree + 1) =
      coefficientCoefficients tail degree := rfl

/-- Reading an added coefficient table gives the sum of the two coefficients. -/
theorem coefficientCoefficients_add : ∀ left right degree,
    coefficientCoefficients (addCoefficients left right) degree =
      coefficientCoefficients left degree +
        coefficientCoefficients right degree
  | [], [], degree => by
      simp only [addCoefficients, coefficientCoefficients]
      exact (Fraction.Field.zero_add _).symm
  | [], _ :: _, degree => by
      rw [addCoefficients]
      exact (Fraction.Field.zero_add _).symm
  | _ :: _, [], degree => by
      rw [addCoefficients_nil_right]
      rw [coefficientCoefficients_nil]
      ring1
  | left :: leftTail, right :: rightTail, 0 => rfl
  | left :: leftTail, right :: rightTail, degree + 1 => by
      exact Purelib.Polynomial.Ascending.Rational.Basic.coefficientCoefficients_add leftTail rightTail degree

/-- Polynomial addition adds the coefficient at each degree. -/
@[simp] theorem coefficient_add (left right : CoefficientPolynomial) (degree : Nat) :
    coefficient (add left right) degree =
      coefficient left degree + coefficient right degree :=
  coefficientCoefficients_add left.coefficients right.coefficients degree

/-- Scaling a rational table scales every zero-padded coefficient.

A retained coefficient is multiplied by the supplied scalar. Outside the
finite table, the same scalar product with zero preserves the padding. -/
theorem coefficientCoefficients_map_scale (factor : Fraction.Rational) :
    ∀ coefficients degree,
      coefficientCoefficients (coefficients.map (factor * ·)) degree =
        factor * coefficientCoefficients coefficients degree
  | [], degree => by
      change 0 = factor * 0
      exact (Fraction.Field.mul_zero_direct factor).symm
  | coefficient :: remaining, 0 => rfl
  | coefficient :: remaining, degree + 1 =>
      Purelib.Polynomial.Ascending.Rational.Basic.coefficientCoefficients_map_scale factor remaining degree

/-- A scaled polynomial has the factor times each original coefficient. -/
@[simp] theorem coefficient_scale (factor : Fraction.Rational)
    (polynomial : CoefficientPolynomial) (degree : Nat) :
    coefficient (scale factor polynomial) degree =
      factor * coefficient polynomial degree :=
  coefficientCoefficients_map_scale factor polynomial.coefficients degree

/-- A prefixed zero block shifts each retained coefficient by its length.

The supplied readback degree includes the whole zero prefix. Recursion removes
that prefix while retaining the original coefficient table and relative degree. -/
theorem coefficientCoefficients_replicate_zero_append :
    ∀ count coefficients degree,
      coefficientCoefficients (List.replicate count 0 ++ coefficients)
          (count + degree) =
        coefficientCoefficients coefficients degree
  | 0, coefficients, degree => by
      change coefficientCoefficients coefficients (0 + degree) =
        coefficientCoefficients coefficients degree
      rw [Nat.zero_add]
  | count + 1, coefficients, degree => by
      rw [show count + 1 + degree = count + degree + 1 by
        calc
          count + 1 + degree = count + (1 + degree) :=
            Nat.add_assoc count 1 degree
          _ = count + (degree + 1) :=
            congrArg (count + ·) (Nat.add_comm 1 degree)
          _ = count + degree + 1 :=
            (Nat.add_assoc count degree 1).symm,
        List.replicate_succ, List.cons_append,
        coefficientCoefficients_cons_succ,
        coefficientCoefficients_replicate_zero_append count coefficients
          degree]

/-- All coefficients within a prefixed zero block vanish. -/
theorem coefficientCoefficients_replicate_zero_append_below :
    ∀ count coefficients degree, degree < count →
      coefficientCoefficients (List.replicate count 0 ++ coefficients) degree = 0
  | 0, coefficients, degree, order => (Nat.not_lt_zero degree order).elim
  | count + 1, coefficients, 0, order => rfl
  | count + 1, coefficients, degree + 1, order => by
      rw [List.replicate_succ, List.cons_append,
        coefficientCoefficients_cons_succ]
      exact coefficientCoefficients_replicate_zero_append_below
        count coefficients degree (by omega)

/-- The constant convolution coefficient multiplies the two constant entries.

An empty input contributes zero. With two retained heads, the shifted tail
product starts at positive degree and contributes no constant coefficient. -/
theorem coefficientCoefficients_mul_zero : ∀ left right,
    coefficientCoefficients (mulCoefficients left right) 0 =
      coefficientCoefficients left 0 * coefficientCoefficients right 0
  | [], right => by
      change 0 = 0 * coefficientCoefficients right 0
      exact (Fraction.Field.zero_mul_direct _).symm
  | left :: leftTail, [] => by
      change 0 = left * 0
      exact (Fraction.Field.mul_zero_direct left).symm
  | left :: leftTail, right :: rightTail => by
      change left * right + 0 = left * right
      exact _root_.add_zero _

/-- Split a positive-degree product coefficient into the head contribution and the shifted tail product. -/
theorem coefficientCoefficients_mul_cons_succ
    (left : Fraction.Rational) (leftTail right : List Fraction.Rational) (degree : Nat) :
    coefficientCoefficients
        (mulCoefficients (left :: leftTail) right) (degree + 1) =
      coefficientCoefficients (right.map (left * ·)) (degree + 1) +
        coefficientCoefficients (mulCoefficients leftTail right) degree := by
  rw [mulCoefficients, coefficientCoefficients_add]
  rfl

end Purelib.Polynomial.Ascending.Rational.Basic
end
