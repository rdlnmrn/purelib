module
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring
-- Public scalar signatures retain the original numeral and negation parents.
public import Purelib.Algebra.Group.Negation
public import Purelib.Data.Nat.Order

open Purelib.Algebra
open Purelib.Algebra.Field

section
open Purelib.Data
open scoped Purelib.Data.Nat
attribute [local instance 2000] Nat.successorNeZero Nat.successorAtLeastTwo
  Group.Negation.subNegZeroMonoid

@[expose] public section

/-!
# Divine Proportions, Chapter 7 field-fragment examples

The book's two complex examples need only one explicitly supplied element
`i` satisfying `i²=-1`.  Keeping that finite field fragment abstract makes the
same proofs usable in admissible finite fields and in the constructive
Gaussian rationals; no completed complex carrier is introduced.
-/

namespace Purelib.Algebra.Field.QuadraticFragment.Imaginary

section ChapterSevenFieldFragments

variable {K : Type*} [ExplicitField K]

/-- Evaluate two coordinates using the supplied imaginary element.

The value is the first coordinate plus the second coordinate times the chosen element; its square relation is required
separately. -/
def complexValue (i real imaginary : K) : K := real + imaginary
  * i

section
open Purelib.Algebra.Field.QuadraticFragment
/-- A zero imaginary coordinate evaluates to its real coordinate. -/
@[simp] private theorem complexValue_zero_imaginary (i real :
  K) :
    complexValue i real 0 = real := by
  unfold complexValue
  ring1

/-- Coordinatewise addition preserves evaluation at a fixed imaginary element. -/
@[simp] private theorem complexValue_add
    (i a b c d : K) :
    complexValue i a b + complexValue i c d =
      complexValue i (a + c) (b + d) := by
  unfold complexValue
  ring1

/-- Coordinatewise subtraction preserves evaluation at a fixed imaginary element. -/
@[simp] private theorem complexValue_sub
    (i a b c d : K) :
    complexValue i a b - complexValue i c d =
      complexValue i (a - c) (b - d) := by
  unfold complexValue
  ring1

/-- Coordinatewise negation preserves evaluation at a fixed imaginary element. -/
@[simp] private theorem complexValue_neg (i a b : K) :
    -complexValue i a b = complexValue i (-a) (-b) := by
  unfold complexValue
  ring1

/-- Multiply evaluated coordinate pairs using an element whose square is negative one.

The real coordinate is the difference of the diagonal products and the imaginary coordinate is the sum of the cross
products. -/
@[simp] public theorem complexValue_mul
    (i a b c d : K) (iSquare : i ^ 2 = -1) :
    complexValue i a b * complexValue i c d =
      complexValue i (a * c - b * d) (a * d + b * c) := by
  calc
    complexValue i a b * complexValue i c d =
        complexValue i (a * c - b * d) (a * d + b * c) +
          b * d * (i ^ 2 + 1) := by
            unfold complexValue
            ring1
    _ = complexValue i (a * c - b * d) (a * d + b * c) := by
      rw [iSquare]
      ring1

/-- Square an evaluated coordinate pair using an element whose square is negative one.

The real coordinate becomes the difference of squares and the imaginary coordinate becomes twice the coordinate product.
-/
@[simp] public theorem complexValue_square
    (i a b : K) (iSquare : i ^ 2 = -1) :
    complexValue i a b ^ 2 =
      complexValue i (a ^ 2 - b ^ 2) (2 * a * b) := open Purelib.Algebra.Field.QuadraticFragment in by
  rw [pow_two, complexValue_mul i a b a b iSquare]
  congr 1 <;> ring1

end

/-- An element squaring to negative one is nonzero in a nontrivial explicit field. -/
public theorem i_nonzero [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1) : i ≠ 0 := by
  intro iZero
  have negativeOneZero : (-1 : K) = 0 := by
    calc
      (-1 : K) = i ^ 2 := iSquare.symm
      _ = 0 := by rw [iZero]; ring1
  exact one_ne_zero (by
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [negativeOneZero]; ring1)

open Purelib.Algebra.Field.QuadraticFragment in
/-- Division by a nonzero scalar commutes with evaluation of the two coordinates.

Both coordinates are divided by the same supplied denominator; no square relation on the imaginary element is required.
-/

public theorem complexValue_div
    (i a b denominator : K) (denominatorNonzero : denominator ≠ 0) :
    complexValue i a b / denominator =
      complexValue i (a / denominator) (b / denominator) := by
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  calc
    (complexValue i a b / denominator) * denominator = complexValue i a b :=
      ExplicitField.div_mul_cancel _ denominatorNonzero
    _ = complexValue i (a / denominator) (b / denominator) * denominator := by
      symm
      unfold complexValue
      calc
        (a / denominator + b / denominator * i) * denominator =
            (a / denominator) * denominator +
              (b / denominator) * denominator * i := by ring1
        _ = a + b * i := by
          rw [ExplicitField.div_mul_cancel a denominatorNonzero,
            ExplicitField.div_mul_cancel b denominatorNonzero]

end ChapterSevenFieldFragments

end Purelib.Algebra.Field.QuadraticFragment.Imaginary

end
