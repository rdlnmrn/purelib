module
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
public section

/-! Data Rat Geometric Bounds and its finite structural certificates. -/

namespace Purelib.Data.Rat.Geometric.Bounds

open Purelib.Algebra.Semiring.Normalization (product_pow)

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- The displayed even-index power bound equals the quarter-radius sequence with initial scale sixteen. -/
public theorem even_cauchy_bound_identity (index : Nat) :
    (2 : Fraction.Rational) ^ (2 * index + 2 + 2) *
        (4 * (1 / 4 : Fraction.Rational) ^ (2 * index + 2 - 1)) =
      Geometric.Basic.quarterRadius 16 index := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow]
  rw [show 2 * index + 2 + 2 = 4 + 2 * index by
      calc
        2 * index + 2 + 2 = 2 * index + 4 := by rw [Nat.add_assoc]
        _ = 4 + 2 * index := Nat.add_comm _ _,
    show 2 * index + 2 - 1 = 2 * index + 1 by
      exact Purelib.Data.Nat.Subtraction.add_sub_cancel_right (2 * index + 1) 1,
    pow_add, pow_add, pow_mul, pow_mul]
  rw [show (2 : Fraction.Rational) ^ 4 = 16 by decide,
    show (2 : Fraction.Rational) ^ 2 = 4 by decide,
    show (1 / 4 : Fraction.Rational) ^ 2 = 1 / 16 by decide,
    show (1 / 4 : Fraction.Rational) ^ 1 = 1 / 4 by decide]
  calc
    (16 * (4 : Fraction.Rational) ^ index) *
        (4 * ((1 / 16 : Fraction.Rational) ^ index * (1 / 4))) =
      (16 * ((4 : Fraction.Rational) ^ index *
        (1 / 16 : Fraction.Rational) ^ index)) * (4 * (1 / 4)) := by ring1
    _ = 16 * ((4 : Fraction.Rational) ^ index *
        (1 / 16 : Fraction.Rational) ^ index) := by
      rw [show (4 : Fraction.Rational) * (1 / 4) = 1 by decide,
        Fraction.Field.mul_one_direct]
    _ = 16 * ((4 : Fraction.Rational) * (1 / 16 : Fraction.Rational)) ^ index := by
      rw [Purelib.Algebra.Semiring.Normalization.product_pow]
    _ = 16 * (1 / 4 : Fraction.Rational) ^ index := by
      rw [show (4 : Fraction.Rational) * (1 / 16) = 1 / 4 by decide]

end Purelib.Data.Rat.Geometric.Bounds

end

section
public section

/-! Data Rat Geometric Bounds and its finite structural certificates. -/

namespace Purelib.Data.Rat.Geometric.Bounds

open Purelib.Algebra.Semiring.Normalization (product_pow)

open Purelib.Data.Rat
/-- Dividing the successor power of four thirds by the current power of two gives twice the successor power of two
thirds. -/
theorem fourThird_div_twoPow (index : Nat) :
    (4 / 3 : Fraction.Rational) ^ (index + 1) /
        (2 : Fraction.Rational) ^ index =
      2 * (2 / 3 : Fraction.Rational) ^ (index + 1) := by
  have denominatorPositive : 0 < (2 : Fraction.Rational) ^ index :=
    Fraction.Order.Arithmetic.pow_pos_direct (by decide) index
  apply Fraction.Field.mul_right_cancel_of_ne
    denominatorPositive.ne'
  calc
    ((4 / 3 : Fraction.Rational) ^ (index + 1) /
          (2 : Fraction.Rational) ^ index) * (2 : Fraction.Rational) ^ index =
        (4 / 3 : Fraction.Rational) ^ (index + 1) :=
      Fraction.Field.div_mul_cancel_of_ne _ _
        denominatorPositive.ne'
    _ = (2 * (2 / 3 : Fraction.Rational) ^ (index + 1)) *
          (2 : Fraction.Rational) ^ index := by
      rw [show (4 / 3 : Fraction.Rational) = 2 * (2 / 3) by decide,
        product_pow, pow_succ]
      ring1

/-- Separate the one-ninth geometric square factor into a four-ninth power and a halved-coordinate square. -/
theorem highTail_power_identity (count : Nat) (tail : Fraction.Rational) :
    (1 / 9 : Fraction.Rational) ^ count * (2 * tail ^ 2) =
      2 * (4 / 9 : Fraction.Rational) ^ count *
        (((1 / 2 : Fraction.Rational) ^ count * tail) ^ 2) := by
  have halfSquare :
      ((1 / 2 : Fraction.Rational) ^ count) ^ 2 =
        (1 / 4 : Fraction.Rational) ^ count := by
    rw [pow_two, ← product_pow]
    congr 1
  calc
    (1 / 9 : Fraction.Rational) ^ count * (2 * tail ^ 2) =
        2 * (1 / 9 : Fraction.Rational) ^ count * tail ^ 2 := by ring1
    _ = 2 * (((4 / 9 : Fraction.Rational) * (1 / 4)) ^ count) *
          tail ^ 2 := by
      rw [show (4 / 9 : Fraction.Rational) * (1 / 4) = 1 / 9 by decide]
    _ = 2 * ((4 / 9 : Fraction.Rational) ^ count *
          (1 / 4 : Fraction.Rational) ^ count) * tail ^ 2 := by
      rw [Purelib.Algebra.Semiring.Normalization.product_pow]
    _ = 2 * (4 / 9 : Fraction.Rational) ^ count *
          (((1 / 2 : Fraction.Rational) ^ count) ^ 2 * tail ^ 2) := by
      rw [halfSquare]
      ring1
    _ = 2 * (4 / 9 : Fraction.Rational) ^ count *
          (((1 / 2 : Fraction.Rational) ^ count * tail) ^ 2) := by ring1

/-- The four-ninth power at exponent twice the depth plus three is at most the quarter power at that depth. -/
theorem fourNinth_depth_bound : ∀ depth,
    (4 / 9 : Fraction.Rational) ^ (2 * depth + 3) ≤
      (1 / 4 : Fraction.Rational) ^ depth
  | 0 => by decide
  | depth + 1 => by
      rw [show 2 * (depth + 1) + 3 = (2 * depth + 3) + 2 by ring1,
        pow_add, pow_succ]
      calc
        (4 / 9 : Fraction.Rational) ^ (2 * depth + 3) *
            ((4 / 9 : Fraction.Rational) ^ 1 * (4 / 9)) ≤
          (1 / 4 : Fraction.Rational) ^ depth * (1 / 4) :=
        Fraction.Order.Arithmetic.mul_le_mul_direct
          (Purelib.Data.Rat.Geometric.Bounds.fourNinth_depth_bound depth) (by decide)
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            (Fraction.Order.Arithmetic.pow_nonneg_direct
              (by decide : (0 : Fraction.Rational) ≤ 4 / 9) 1)
            (by decide : (0 : Fraction.Rational) ≤ 4 / 9))
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            (by decide : (0 : Fraction.Rational) ≤ 1 / 4) depth)
        _ = (1 / 4 : Fraction.Rational) ^ (depth + 1) := (pow_succ _ _).symm
end Purelib.Data.Rat.Geometric.Bounds

end
