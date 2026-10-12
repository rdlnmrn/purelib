module
public import Purelib.Algebra.Field.ExplicitField
-- Exposed characteristic certificates retain these original scalar parents.
public import Purelib.Algebra.Group.Negation
public import Purelib.Data.Nat.Order

import Purelib.Tactic.Ring

open Purelib.Algebra.Field
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

section
@[expose] public section

/-!
# Divine Proportions, Chapter 26: Platonic solids

All five face-spread computations are recorded by one denominator-cleared
isosceles-triangle certificate.  Exercise 26.1 is proved directly from three
displayed edge vectors.  Exercise 26.4 uses a uniformly scaled standard
icosahedron, so its coordinates are polynomial in a supplied witness
`root²=5` and contain no selected irrational or completed field.
-/

namespace Purelib.Algebra.Field.Characteristic.Nonzero.Golden

variable {K : Type*} [ExplicitField K]

/-- Sixty-four is nonzero when two is nonzero in the explicit field.

The displayed product factorization reduces the claim to powers of two. -/
public theorem sixtyFour_ne_zero (twoNonzero : (2 : K) ≠ 0)
  :
    (64 : K) ≠ 0 := by
  rw [show (64 : K) = 2 * 2 * 2 * 2 * 2 * 2 by ring1]
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero twoNonzero twoNonzero)
          twoNonzero) twoNonzero) twoNonzero) twoNonzero

end Purelib.Algebra.Field.Characteristic.Nonzero.Golden

end

section
@[expose] public section

/-!
# Divine Proportions, Exercise 8.11

This module proves the book's finite prime-residue inner-product calculation.
Every sum runs over the displayed natural labels `0, ..., p-1`; no ambient
field carrier, primitive root, completed polynomial space, or infinite
orthogonality argument is used.
-/

namespace Purelib.Algebra.Field.Characteristic.Nonzero

variable {K : Type*} [ExplicitField K]

section ExerciseEightEleven

/-- One is nonzero whenever two is nonzero.

A zero value for one would make its sum with itself zero, contradicting the supplied certificate. -/
public theorem one_ne_zero_of_two_ne_zero
    (twoNonzero : (2 : K) ≠ 0) : (1 : K) ≠ 0 := by
  intro oneEqualsZero
  apply twoNonzero
  rw [show (2 : K) = 1 + 1 by ring1, oneEqualsZero, zero_add]

/-- Sixteen is nonzero when two is nonzero in the explicit field.

The displayed product factorization reduces the claim to powers of two. -/
public theorem sixteen_ne_zero (twoNonzero : (2 : K) ≠ 0) :
    (16 : K) ≠ 0 := by
  rw [show (16 : K) = (2 * 2) * (2 * 2) by ring1]
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero twoNonzero twoNonzero)
    (ExplicitField.mul_ne_zero twoNonzero twoNonzero)

end ExerciseEightEleven

end Purelib.Algebra.Field.Characteristic.Nonzero

end

section
/-!
# Divine Proportions, Exercises 6.3--6.6

The common spread ratio and the two null-triangle formulas are finite
consequences of the Quadrea-spread identity.  The rational triangle inequality
is the statement that the coordinate-determinant square is nonnegative; no
absolute value, square root, compactness, or extremum is introduced.
-/

@[expose] public section

namespace formalisations.DivineProportions.Chapters.Trigonometry.ChapterSixQuadreaExercises

variable {K : Type*} [ExplicitField K]

end formalisations.DivineProportions.Chapters.Trigonometry.ChapterSixQuadreaExercises

end

end

section
@[expose] public section
variable {K : Type*} [ExplicitField K]

end

section
open Purelib
open Purelib.Algebra.Field
open scoped Purelib.Data.Nat
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid
public section
namespace Purelib.Algebra.Field.Characteristic.Nonzero

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A nonzero value of eight forces four to be nonzero. -/
public theorem four_ne_zero_of_eight_ne_zero
    (eightNonzero : (8 : K) ≠ 0) : (4 : K) ≠ 0 := by
  intro fourZero
  apply eightNonzero
  calc
    (8 : K) = 2 * 4 := by ring1
    _ = 0 := by rw [fourZero]; ring1

/-- Negative two is nonzero whenever two is nonzero. -/
public theorem negative_two_nonzero (twoNonzero : (2 : K) ≠ 0) :
    (-2 : K) ≠ 0 := by
  intro negativeTwoZero
  apply twoNonzero
  calc
    (2 : K) = -(-2) := by ring1
    _ = -0 := by rw [negativeTwoZero]
    _ = 0 := neg_zero

/-- Eight is nonzero when two is nonzero in the explicit field.

The finite product factorization reduces the claim to the supplied nonzero certificate for two. -/
public theorem eight_ne_zero (twoNonzero : (2 : K) ≠ 0) : (8 : K) ≠ 0 := by
  rw [show (8 : K) = 2 * 2 * 2 by ring1]
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero twoNonzero twoNonzero) twoNonzero

end Purelib.Algebra.Field.Characteristic.Nonzero
end

end

section
public section
namespace Purelib.Algebra.Field.Characteristic.Nonzero

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Cancel two from a zero product when two is nonzero. -/
public theorem eq_zero_of_two_mul_eq_zero (twoNonzero : (2 : K) ≠ 0)
    (value : K) (twiceZero : 2 * value = 0) : value = 0 := by
  have cancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  calc
    value = 1 * value := by rw [one_mul]
    _ = (2 * (2 : K)⁻¹) * value := by rw [cancel]
    _ = (2 * value) * (2 : K)⁻¹ := by ring1
    _ = 0 := by rw [twiceZero, zero_mul]

/-- A supplied nonzero scalar implies that one is nonzero. -/
public theorem one_ne_zero_of_nonzero {value : K}
  (nonzero : value ≠ 0) :
    (1 : K) ≠ 0 := by
  intro oneZero
  apply nonzero
  calc
    value = value * 1 := by rw [mul_one]
    _ = value * 0 := by rw [oneZero]
    _ = 0 := by rw [mul_zero]

/-- Cancel nonzero two from an equality of doubled scalars. -/
public theorem
  eq_of_two_mul_eq_two_mul
  (twoNonzero : (2 : K) ≠ 0)
    {left right : K} (equal : 2 * left = 2 * right) : left = right := by
  have cancel := Algebra.Field.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  calc
    left = (2 * (2 : K)⁻¹) * left := by rw [cancel, one_mul]
    _ = (2 * left) * (2 : K)⁻¹ := by ring1
    _ = (2 * right) * (2 : K)⁻¹ := by rw [equal]
    _ = (2 * (2 : K)⁻¹) * right := by ring1
    _ = right := by rw [cancel, one_mul]

/-- Four is nonzero when two is nonzero in the explicit field.

Factoring four as the product of two with itself transfers the supplied nonzero certificate. -/
public theorem four_ne_zero (twoNonzero : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  rw [show (4 : K) = 2 * 2 by ring1]
  exact ExplicitField.mul_ne_zero twoNonzero twoNonzero

end Purelib.Algebra.Field.Characteristic.Nonzero
end

end

section
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace Purelib.Algebra.Field.Characteristic.Nonzero
/-- A nonzero parameter pair with zero sum has nonzero difference when two is nonzero. -/
public theorem
  difference_nonzero_of_sum_zero
    (twoNonzero : (2 : K) ≠ 0) (first second : K)
    (parametersNonzero : first ≠ 0 ∨ second ≠ 0)
    (sumZero : first + second = 0) : first - second ≠ 0 := by
  intro differenceZero
  have twiceFirst : 2 * first = 0 := by
    calc
      2 * first = (first + second) + (first - second) := by ring1
      _ = 0 := by rw [sumZero, differenceZero, add_zero]
  have twiceSecond : 2 * second = 0 := by
    calc
      2 * second = (first + second) - (first - second) := by ring1
      _ = 0 := by rw [sumZero, differenceZero]; ring1
  have firstZero :=
    ExplicitField.eq_zero_of_mul_eq_zero_left
    twoNonzero twiceFirst
  have secondZero :=
    ExplicitField.eq_zero_of_mul_eq_zero_left
    twoNonzero twiceSecond
  rcases parametersNonzero with firstNonzero | secondNonzero
  · exact firstNonzero firstZero
  · exact secondNonzero secondZero
end Purelib.Algebra.Field.Characteristic.Nonzero
end
