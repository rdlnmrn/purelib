module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Ascending.Gaussian.Basic

open Purelib.Polynomial.Ascending.Gaussian (CoefficientPolynomial)

open Purelib.Data

open Purelib.Polynomial

@[expose] public section

/-!
# Coefficient algebra for finite Gaussian polynomial integration

All equalities are proved from finite coefficient lists.  In particular,
coefficient equality is not obtained by testing a polynomial on an infinite
carrier.  This small layer supplies the algebraic FTC used by generated path
subdivisions; it adds no analytic or antiderivative certificate assumptions.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Coefficient

/-- Read a coefficient, with zero padding beyond the displayed finite list. -/
def coefficientList : List Gaussian.Basic.Canonical → Nat →
  Gaussian.Basic.Canonical
  | [], _ => 0
  | head :: _, 0 => head
  | _ :: tail, degree + 1 => coefficientList tail degree

/-- Read a Gaussian polynomial coefficient, using zero beyond its retained table. -/
def coefficient (polynomial :
  CoefficientPolynomial) (degree : Nat) : Gaussian.Basic.Canonical :=
  coefficientList polynomial.coefficients degree

/-- A relation on two finite lists, allowing redundant trailing zeros. -/
def CoefficientwiseEqual (left right :
  CoefficientPolynomial) : Prop :=
  ∀ degree, coefficient left degree = coefficient right
    degree

/-- Equality of the original finite Gaussian coefficient tables below a displayed degree count. -/
def EqualBelow (count : Nat) (left right : CoefficientPolynomial) : Prop :=
  ∀ degree, degree < count → coefficient left degree = coefficient right degree

/-- Every Gaussian polynomial is coefficientwise equal to itself. -/
theorem coefficientwise_refl (polynomial :
  CoefficientPolynomial) :
    CoefficientwiseEqual polynomial polynomial := fun _ => rfl

/-- Reverse Gaussian coefficientwise equality. -/
theorem coefficientwise_symm {left right :
  CoefficientPolynomial}
    (equal : CoefficientwiseEqual left right) :
    CoefficientwiseEqual right left := fun degree => (equal degree).symm

/-- Compose Gaussian coefficientwise equalities through the shared polynomial. -/
theorem coefficientwise_trans {first second third :
  CoefficientPolynomial}
    (firstSecond : CoefficientwiseEqual first second)
    (secondThird : CoefficientwiseEqual second third) :
    CoefficientwiseEqual first third :=
  fun degree => (firstSecond degree).trans (secondThird degree)

/-- Every coefficient of the empty zero polynomial vanishes. -/
@[simp] theorem coefficient_zero (degree : Nat) :
    coefficient Ascending.Gaussian.Basic.zero degree = 0 := rfl

/-- A constant Gaussian polynomial has its value at degree zero and zero at higher degrees. -/
@[simp] theorem coefficient_constant (value :
  Gaussian.Basic.Canonical) : ∀ degree,
    coefficient (Ascending.Gaussian.Basic.constant value) degree = if degree = 0 then
      value else 0
  | 0 => rfl
  | _ + 1 => rfl

/-- A zero-extended coefficient outside the actual finite list length is zero. -/
theorem coefficientList_eq_zero_of_length_le :
    ∀ (values : List Gaussian.Basic.Canonical) (degree : Nat),
      values.length ≤ degree → coefficientList values degree = 0
  | [], _, _ => rfl
  | _ :: _, 0, impossible => by cases impossible
  | _ :: tail, degree + 1, bound =>
      coefficientList_eq_zero_of_length_le tail degree (Nat.le_of_succ_le_succ bound)

/-- A finite list with zero at every retained occurrence has zero at every zero-extended coefficient. -/
theorem coefficientList_zero_of_all :
    ∀ (values : List Gaussian.Basic.Canonical), (∀ entry, entry ∈ values → entry = 0) →
      ∀ degree, coefficientList values degree = 0
  | [], _, _ => rfl
  | head :: _, zero, 0 => zero head (List.Mem.head _)
  | head :: tail, zero, degree + 1 =>
      coefficientList_zero_of_all tail (fun entry member => zero entry (List.Mem.tail head member)) degree

end Purelib.Polynomial.Ascending.Gaussian.Coefficient

end
