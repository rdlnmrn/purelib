module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Convolution

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Ascending.Rational.Basic (CoefficientPolynomial)

/-!
# Coefficientwise algebra of ascending rational tables

Zero-padded readback compares the retained finite polynomial records. Scalar
prefix identities and structural table recursion prove their arithmetic laws
without changing lengths, trailing zeros or coefficient order.
-/

public section
namespace Purelib.Polynomial.Ascending.Rational.Coefficientwise

open Purelib.Algebra
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Polynomial

/-- Equality of every zero-padded rational coefficient.

The relation retains the two nominal finite coefficient tables. Equal readback
at every natural degree allows distinct lengths and retained trailing zeros. -/
@[expose] def CoefficientwiseEqual (left right : CoefficientPolynomial) : Prop :=
  ∀ degree, Ascending.Rational.Basic.coefficient left degree = Ascending.Rational.Basic.coefficient right degree

/-- Every polynomial is coefficientwise equal to itself. -/
theorem coefficientwise_refl (polynomial : CoefficientPolynomial) :
    CoefficientwiseEqual polynomial polynomial := fun _ => rfl

/-- Reverse coefficientwise equality. -/
theorem coefficientwise_symm {left right : CoefficientPolynomial}
    (equal : CoefficientwiseEqual left right) :
    CoefficientwiseEqual right left := fun degree => (equal degree).symm

/-- Compose coefficientwise equalities through their shared intermediate polynomial. -/
theorem coefficientwise_trans {first second third : CoefficientPolynomial}
    (firstSecond : CoefficientwiseEqual first second)
    (secondThird : CoefficientwiseEqual second third) :
    CoefficientwiseEqual first third :=
  fun degree => (firstSecond degree).trans (secondThird degree)

/-- Every coefficient of the empty zero polynomial vanishes. -/
@[simp] theorem coefficient_zero (degree : Nat) :
    Ascending.Rational.Basic.coefficient Ascending.Rational.Basic.zero degree = 0 := by
  cases degree <;> rfl

/-- A constant polynomial has its value at degree zero and zero at every positive degree. -/
@[simp] theorem coefficient_constant (value : Fraction.Rational) : ∀ degree,
    Ascending.Rational.Basic.coefficient (Ascending.Rational.Basic.constant value) degree = if degree = 0 then value
      else 0
  | 0 => rfl
  | _ + 1 => rfl

/-- Addition preserves coefficientwise equality in both arguments. -/
theorem coefficientwise_add {left left' right right' : CoefficientPolynomial}
    (leftEqual : CoefficientwiseEqual left left')
    (rightEqual : CoefficientwiseEqual right right') :
    CoefficientwiseEqual (Ascending.Rational.Basic.add left right) (Ascending.Rational.Basic.add left' right') := by
  intro degree
  rw [Ascending.Rational.Basic.coefficient_add, Ascending.Rational.Basic.coefficient_add, leftEqual degree, rightEqual
    degree]

/-- Rational scaling preserves coefficientwise equality. -/
theorem coefficientwise_scale (factor : Fraction.Rational)
    {left right : CoefficientPolynomial} (equal : CoefficientwiseEqual left right) :
    CoefficientwiseEqual (Ascending.Rational.Basic.scale factor left) (Ascending.Rational.Basic.scale factor right) :=
      by
  intro degree
  rw [Ascending.Rational.Basic.coefficient_scale, Ascending.Rational.Basic.coefficient_scale, equal degree]

/-- Multiplication preserves coefficientwise equality in both arguments.

Each finite convolution summand uses the two supplied coefficient equalities at its complementary indices. -/
theorem coefficientwise_mul {left left' right right' : CoefficientPolynomial}
    (leftEqual : CoefficientwiseEqual left left')
    (rightEqual : CoefficientwiseEqual right right') :
    CoefficientwiseEqual (Ascending.Rational.Basic.mul left right) (Ascending.Rational.Basic.mul left' right') := by
  intro degree
  rw [Ascending.Rational.Convolution.coefficient_mul, Ascending.Rational.Convolution.coefficient_mul]
  apply FiniteSum.Prefix.coordinateSum_congr
  intro index
  rw [leftEqual index, rightEqual (degree - index)]

/-- Polynomial multiplication is commutative coefficientwise.

Reversing the finite convolution indices pairs the same products in the opposite order. -/
theorem coefficientwise_mul_comm (left right : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.mul left right) (Ascending.Rational.Basic.mul right left) := by
  intro degree
  rw [Ascending.Rational.Convolution.coefficient_mul, Ascending.Rational.Convolution.coefficient_mul,
    FiniteSum.Prefix.coordinateSum_reverse
      (fun index => Ascending.Rational.Basic.coefficient left index *
        Ascending.Rational.Basic.coefficient right (degree - index)) (degree + 1)]
  apply FiniteSum.Prefix.coordinateSum_congr_lt
  intro index order
  have indexLe : index ≤ degree := Nat.le_of_lt_succ order
  rw [Subtraction.add_sub_cancel_right,
    show degree - (degree - index) = index by omega0]
  ring1

/-- A one-degree shift has zero constant coefficient. -/
@[simp] theorem coefficient_shift_one_zero (polynomial : CoefficientPolynomial) :
    Ascending.Rational.Basic.coefficient (Ascending.Rational.Basic.shift 1 polynomial) 0 = 0 := rfl

/-- A one-degree shift moves each coefficient to the next degree. -/
@[simp] theorem coefficient_shift_one_succ (polynomial : CoefficientPolynomial)
    (degree : Nat) :
    Ascending.Rational.Basic.coefficient (Ascending.Rational.Basic.shift 1 polynomial) (degree + 1) =
      Ascending.Rational.Basic.coefficient polynomial degree := rfl

/-- A nonempty table separates into its constant head and shifted tail.

Degree zero reads the same retained head. A positive degree reads the unchanged
remaining table after one zero-prefix shift, using scalar addition by zero. -/
theorem coefficientwise_cons_decompose (head : Fraction.Rational)
    (tail : List Fraction.Rational) :
    CoefficientwiseEqual ⟨head :: tail⟩
      (Ascending.Rational.Basic.add (Ascending.Rational.Basic.constant head) (Ascending.Rational.Basic.shift 1 ⟨tail⟩))
        := by
  intro degree
  cases degree with
  | zero =>
      change head = _
      rw [Ascending.Rational.Basic.coefficient_add, coefficient_constant,
        coefficient_shift_one_zero]
      rw [if_pos rfl]
      exact (_root_.add_zero head).symm
  | succ degree =>
      change Ascending.Rational.Basic.coefficient ⟨tail⟩ degree = _
      rw [Ascending.Rational.Basic.coefficient_add, coefficient_constant,
        if_neg ((fun same : degree + 1 = 0 => Nat.noConfusion same)), coefficient_shift_one_succ,
        Fraction.Field.zero_add]

/-- Constant-polynomial multiplication equals coefficient scaling.

The finite convolution has one possibly nonzero term, at degree zero in the
constant factor. The other retained terms vanish at their positive degrees. -/
theorem coefficientwise_constant_mul (factor : Fraction.Rational)
    (polynomial : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.constant factor) polynomial)
      (Ascending.Rational.Basic.scale factor polynomial) := by
  intro degree
  rw [Ascending.Rational.Convolution.coefficient_mul, Ascending.Rational.Basic.coefficient_scale,
    FiniteSum.Prefix.coordinateSum_succ_front]
  change
    factor * Ascending.Rational.Basic.coefficient polynomial degree +
        FiniteSum.Prefix.coordinateSum
          (fun index =>
            Ascending.Rational.Basic.coefficient (Ascending.Rational.Basic.constant factor) (index + 1) *
              Ascending.Rational.Basic.coefficient polynomial (degree - (index + 1))) degree =
      factor * Ascending.Rational.Basic.coefficient polynomial degree
  rw [FiniteSum.Prefix.coordinateSum_all_zero _ (by
    intro index
    rw [coefficient_constant, if_neg ((fun same : index + 1 = 0 => Nat.noConfusion same)),
      Fraction.Field.zero_mul_direct])]
  ring1

/-- Multiplication by the zero polynomial has every coefficient zero. -/
theorem coefficientwise_mul_zero (polynomial : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.mul polynomial Ascending.Rational.Basic.zero)
      Ascending.Rational.Basic.zero := by
  intro degree
  rw [Ascending.Rational.Convolution.coefficient_mul, coefficient_zero]
  exact FiniteSum.Prefix.coordinateSum_all_zero _ (by
    intro index
    rw [coefficient_zero,
      Fraction.Field.mul_zero_direct]) (degree + 1)

/-- Scaling the left factor scales the polynomial product coefficientwise. -/
theorem coefficientwise_scale_mul (factor : Fraction.Rational)
    (left right : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.scale factor left) right)
      (Ascending.Rational.Basic.scale factor (Ascending.Rational.Basic.mul left right)) := by
  intro degree
  rw [Ascending.Rational.Convolution.coefficient_mul, Ascending.Rational.Basic.coefficient_scale,
    Ascending.Rational.Convolution.coefficient_mul,
    FiniteSum.Prefix.coordinateSum_scale_left]
  apply FiniteSum.Prefix.coordinateSum_congr
  intro index
  rw [Ascending.Rational.Basic.coefficient_scale]
  ring1

/-- Scaling by one preserves all coefficients. -/
theorem coefficientwise_scale_one (polynomial : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.scale 1 polynomial) polynomial := by
  intro degree
  rw [Ascending.Rational.Basic.coefficient_scale]
  ring1

/-- The constant one polynomial is a left multiplicative identity coefficientwise. -/
theorem coefficientwise_one_mul (polynomial : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.mul Ascending.Rational.Basic.one polynomial) polynomial :=
  coefficientwise_trans
    (coefficientwise_constant_mul 1 polynomial)
    (coefficientwise_scale_one polynomial)

/-- A one-degree shift of the left factor shifts the product coefficientwise. -/
theorem coefficientwise_shift_one_mul (left right : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.shift 1 left) right)
      (Ascending.Rational.Basic.shift 1 (Ascending.Rational.Basic.mul left right)) := by
  intro degree
  cases degree with
  | zero =>
      rw [Ascending.Rational.Convolution.coefficient_mul, FiniteSum.Prefix.coordinateSum_succ,
        FiniteSum.Prefix.coordinateSum_zero,
        coefficient_shift_one_zero, coefficient_shift_one_zero,
        Fraction.Field.zero_mul_direct,
        Fraction.Field.zero_add]
  | succ degree =>
      rw [Ascending.Rational.Convolution.coefficient_mul, FiniteSum.Prefix.coordinateSum_succ_front,
        coefficient_shift_one_zero,
        Fraction.Field.zero_mul_direct,
        Fraction.Field.zero_add,
        coefficient_shift_one_succ, Ascending.Rational.Convolution.coefficient_mul]
      apply FiniteSum.Prefix.coordinateSum_congr
      intro index
      rw [coefficient_shift_one_succ]
      rw [Nat.succ_sub_succ]

/-- A one-degree shift preserves coefficientwise equality. -/
theorem coefficientwise_shift_one {left right : CoefficientPolynomial}
    (equal : CoefficientwiseEqual left right) :
    CoefficientwiseEqual (Ascending.Rational.Basic.shift 1 left) (Ascending.Rational.Basic.shift 1 right) := by
  intro degree
  cases degree with
  | zero => rfl
  | succ degree => exact equal degree

/-- Multiplication distributes over addition in its right argument coefficientwise. -/
theorem coefficientwise_mul_add (left middle right : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.mul left (Ascending.Rational.Basic.add middle right))
      (Ascending.Rational.Basic.add (Ascending.Rational.Basic.mul left middle) (Ascending.Rational.Basic.mul left
        right)) := by
  intro degree
  rw [Ascending.Rational.Convolution.coefficient_mul, Ascending.Rational.Basic.coefficient_add,
    Ascending.Rational.Convolution.coefficient_mul, Ascending.Rational.Convolution.coefficient_mul, ←
      FiniteSum.Prefix.coordinateSum_add]
  apply FiniteSum.Prefix.coordinateSum_congr
  intro index
  rw [Ascending.Rational.Basic.coefficient_add]
  ring1

/-- Multiplication distributes over addition in its left argument coefficientwise. -/
theorem coefficientwise_add_mul (left middle right : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.add left middle) right)
      (Ascending.Rational.Basic.add (Ascending.Rational.Basic.mul left right) (Ascending.Rational.Basic.mul middle
        right)) :=
  coefficientwise_trans
    (coefficientwise_mul_comm (Ascending.Rational.Basic.add left middle) right)
    (coefficientwise_trans
      (coefficientwise_mul_add right left middle)
      (coefficientwise_add
        (coefficientwise_mul_comm right left)
        (coefficientwise_mul_comm right middle)))

/-- The zero polynomial is a left additive identity coefficientwise. -/
theorem coefficientwise_zero_add (polynomial : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.add Ascending.Rational.Basic.zero polynomial) polynomial := by
  intro degree
  rw [Ascending.Rational.Basic.coefficient_add, coefficient_zero,
    Fraction.Field.zero_add]

/-- The zero polynomial is a right additive identity coefficientwise. -/
theorem coefficientwise_add_zero (polynomial : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.add polynomial Ascending.Rational.Basic.zero) polynomial := by
  intro degree
  rw [Ascending.Rational.Basic.coefficient_add, coefficient_zero]
  ring1

/-- Addition is commutative coefficientwise. -/
theorem coefficientwise_add_comm (left right : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.add left right) (Ascending.Rational.Basic.add right left) := by
  intro degree
  rw [Ascending.Rational.Basic.coefficient_add, Ascending.Rational.Basic.coefficient_add]
  ring1

/-- Addition is associative coefficientwise. -/
theorem coefficientwise_add_assoc (left middle right : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.add (Ascending.Rational.Basic.add left middle) right)
      (Ascending.Rational.Basic.add left (Ascending.Rational.Basic.add middle right)) := by
  intro degree
  rw [Ascending.Rational.Basic.coefficient_add, Ascending.Rational.Basic.coefficient_add,
    Ascending.Rational.Basic.coefficient_add, Ascending.Rational.Basic.coefficient_add]
  ring1

/-- Exchange the middle two terms of a four-polynomial sum coefficientwise. -/
theorem coefficientwise_add_rearrange
    (first second third fourth : CoefficientPolynomial) :
    CoefficientwiseEqual (Ascending.Rational.Basic.add (Ascending.Rational.Basic.add first second)
      (Ascending.Rational.Basic.add third fourth))
      (Ascending.Rational.Basic.add (Ascending.Rational.Basic.add first third) (Ascending.Rational.Basic.add second
        fourth)) := by
  intro degree
  repeat' rw [Ascending.Rational.Basic.coefficient_add]
  ring1

/-- Embedding a sum of constants agrees coefficientwise with adding their constant polynomials. -/
theorem coefficientwise_constant_add (left right : Fraction.Rational) :
    CoefficientwiseEqual (Ascending.Rational.Basic.constant (left + right))
      (Ascending.Rational.Basic.add (Ascending.Rational.Basic.constant left) (Ascending.Rational.Basic.constant right))
        := by
  intro degree
  cases degree with
  | zero =>
      rw [coefficient_constant, if_pos rfl, Ascending.Rational.Basic.coefficient_add,
        coefficient_constant, if_pos rfl,
        coefficient_constant, if_pos rfl]
  | succ degree =>
      rw [coefficient_constant, if_neg ((fun same : degree + 1 = 0 => Nat.noConfusion same)),
        Ascending.Rational.Basic.coefficient_add, coefficient_constant,
        if_neg ((fun same : degree + 1 = 0 => Nat.noConfusion same)), coefficient_constant,
        if_neg ((fun same : degree + 1 = 0 => Nat.noConfusion same))]
      ring1

/-- Polynomial multiplication is associative coefficientwise.

Recursion decreases the displayed left-table length. Its constant head and
shifted tail retain the same untrimmed coefficient representations, and scalar
convolution transports the two inductive contributions. -/
theorem coefficientwise_mul_assoc : ∀ (left right third : CoefficientPolynomial),
    CoefficientwiseEqual (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.mul left right) third)
      (Ascending.Rational.Basic.mul left (Ascending.Rational.Basic.mul right third))
  | ⟨[]⟩, right, third => coefficientwise_refl Ascending.Rational.Basic.zero
  | ⟨head :: tail⟩, right, third => by
      let tailPolynomial : CoefficientPolynomial := ⟨tail⟩
      let decomposed := Ascending.Rational.Basic.add (Ascending.Rational.Basic.constant head)
        (Ascending.Rational.Basic.shift 1 tailPolynomial)
      have decomposition :
          CoefficientwiseEqual ⟨head :: tail⟩ decomposed :=
        coefficientwise_cons_decompose head tail
      have headPart :
          CoefficientwiseEqual
            (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.constant head) right)
              third)
            (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.constant head) (Ascending.Rational.Basic.mul right
              third)) :=
        coefficientwise_trans
          (coefficientwise_mul
            (coefficientwise_constant_mul head right)
            (coefficientwise_refl third))
          (coefficientwise_trans
            (coefficientwise_scale_mul head right third)
            (coefficientwise_symm
              (coefficientwise_constant_mul head (Ascending.Rational.Basic.mul right third))))
      have tailPart :
          CoefficientwiseEqual
            (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.shift 1
              tailPolynomial) right) third)
            (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.shift 1 tailPolynomial)
              (Ascending.Rational.Basic.mul right third)) :=
        coefficientwise_trans
          (coefficientwise_mul
            (coefficientwise_shift_one_mul tailPolynomial right)
            (coefficientwise_refl third))
          (coefficientwise_trans
            (coefficientwise_shift_one_mul (Ascending.Rational.Basic.mul tailPolynomial right) third)
            (coefficientwise_trans
              (coefficientwise_shift_one
                (coefficientwise_mul_assoc tailPolynomial right
                  third))
              (coefficientwise_symm
                (coefficientwise_shift_one_mul tailPolynomial
                  (Ascending.Rational.Basic.mul right third)))))
      exact coefficientwise_trans
        (coefficientwise_mul
          (coefficientwise_mul decomposition
            (coefficientwise_refl right))
          (coefficientwise_refl third))
        (coefficientwise_trans
          (coefficientwise_mul
            (coefficientwise_add_mul (Ascending.Rational.Basic.constant head)
              (Ascending.Rational.Basic.shift 1 tailPolynomial) right)
            (coefficientwise_refl third))
          (coefficientwise_trans
            (coefficientwise_add_mul
              (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.constant head) right)
              (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.shift 1 tailPolynomial) right) third)
            (coefficientwise_trans
              (coefficientwise_add headPart tailPart)
              (coefficientwise_trans
                (coefficientwise_symm
                  (coefficientwise_add_mul (Ascending.Rational.Basic.constant head)
                    (Ascending.Rational.Basic.shift 1 tailPolynomial) (Ascending.Rational.Basic.mul right third)))
                (coefficientwise_mul
                  (coefficientwise_symm decomposition)
                  (coefficientwise_refl (Ascending.Rational.Basic.mul right third)))))))

termination_by left _ _ => left.coefficients.length
decreasing_by
  exact Nat.lt_succ_self tail.length

/-- Multiplying a rational constant by the natural cast of one preserves its constant polynomial coefficientwise. -/
theorem coefficientwise_constant_one_mul (value : Fraction.Rational) :
    CoefficientwiseEqual
      (Ascending.Rational.Basic.constant (((1 : Nat) : Fraction.Rational) * value)) (Ascending.Rational.Basic.constant
        value) := by
  intro degree
  cases degree with
  | zero =>
      rw [coefficient_constant, if_pos rfl,
        coefficient_constant, if_pos rfl]
      ring1
  | succ degree =>
      rw [coefficient_constant, if_neg ((fun same : degree + 1 = 0 => Nat.noConfusion same)),
        coefficient_constant, if_neg ((fun same : degree + 1 = 0 => Nat.noConfusion same))]

/-- The singleton zero constant table is coefficientwise equal to the empty zero table. -/
theorem coefficientwise_constant_zero :
    CoefficientwiseEqual (Ascending.Rational.Basic.constant 0) Ascending.Rational.Basic.zero := by
  intro degree
  rw [coefficient_constant, coefficient_zero]
  split <;> rfl

/-- Group the endpoint terms and the two middle terms of a four-polynomial sum coefficientwise. -/
theorem coefficientwise_telescope_rearrange
    (first cancelledLeft cancelledRight last : CoefficientPolynomial) :
    CoefficientwiseEqual
      (Ascending.Rational.Basic.add (Ascending.Rational.Basic.add first cancelledLeft) (Ascending.Rational.Basic.add
        cancelledRight last))
      (Ascending.Rational.Basic.add (Ascending.Rational.Basic.add first last) (Ascending.Rational.Basic.add
        cancelledLeft cancelledRight)) := by
  intro degree
  repeat' rw [Ascending.Rational.Basic.coefficient_add]
  ring1

end Purelib.Polynomial.Ascending.Rational.Coefficientwise
end
