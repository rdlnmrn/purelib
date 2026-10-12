module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Int.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Order of canonical rational casts

Natural and integer casts preserve and reflect the retained scalar order.
The sign and nonzero certificates use the original canonical numerator and
denominator operations.
-/

public section
namespace Purelib.Data.Rat.Fraction.Cast.Order

open Purelib.Data
open Purelib.Data.Rat

/-- Casting a positive natural gives a positive canonical rational.

The supplied strict natural bound certifies positivity of the retained integer numerator of its canonical cast. -/
theorem natCast_pos_direct {n : Nat} (hn : 0 < n) :
    (0 : Rat.Fraction.Rational) < (n : Rat.Fraction.Rational) := by
  apply (Rat.Fraction.Order.Basic.zero_lt_iff_num_pos _).mpr
  rw [Rat.Fraction.Cast.natCast_eq_fromInt]
  exact Int.Order.natCast_pos hn

/-- Natural strict comparison is preserved by canonical rational casts.

The two canonical natural casts have unit denominators, so their cross-product comparison retains the original strict
natural bound. -/
theorem natCast_lt_direct {m n : Nat} (hmn : m < n) :
    (m : Rat.Fraction.Rational) < (n : Rat.Fraction.Rational) := by
  apply (Rat.Fraction.Order.Basic.lt_iff_cross _ _).mpr
  rw [Rat.Fraction.Cast.natCast_eq_fromInt, Rat.Fraction.Cast.natCast_eq_fromInt]
  change (m : Int) * 1 < (n : Int) * 1
  rw [Int.Arithmetic.mul_one, Int.Arithmetic.mul_one]
  exact Int.Order.natCast_lt_iff.mpr hmn

/-- Natural weak comparison is preserved by canonical rational casts.

The unit denominators reduce cross-product order to the original weak natural comparison after the exact integer cast.
-/
theorem natCast_le_direct {m n : Nat} (hmn : m ≤ n) :
    (m : Rat.Fraction.Rational) ≤ (n : Rat.Fraction.Rational) := by
  change
    (m : Rat.Fraction.Rational).num * ((n : Rat.Fraction.Rational).den : Int) ≤
      (n : Rat.Fraction.Rational).num * ((m : Rat.Fraction.Rational).den : Int)
  rw [Rat.Fraction.Cast.natCast_eq_fromInt, Rat.Fraction.Cast.natCast_eq_fromInt]
  change (m : Int) * 1 ≤ (n : Int) * 1
  rw [Int.Arithmetic.mul_one, Int.Arithmetic.mul_one]
  exact Int.Order.natCast_le_iff.mpr hmn

/-- Canonical rational casts preserve and reflect strict natural comparison.

The forward implication reads the retained unit-denominator cross-products; the reverse implication preserves the
original strict natural comparison. -/
theorem natCast_lt_iff_direct {left right : Nat} :
    (left : Rat.Fraction.Rational) < (right : Rat.Fraction.Rational) ↔ left < right := by
  constructor
  · intro less
    have cross := (Rat.Fraction.Order.Basic.lt_iff_cross _ _).mp less
    rw [Rat.Fraction.Cast.natCast_eq_fromInt, Rat.Fraction.Cast.natCast_eq_fromInt] at cross
    change (left : Int) * 1 < (right : Int) * 1 at cross
    rw [Int.Arithmetic.mul_one, Int.Arithmetic.mul_one] at cross
    exact Int.Order.natCast_lt_iff.mp cross
  · exact Rat.Fraction.Cast.Order.natCast_lt_direct

/-- Canonical rational casts preserve and reflect weak natural comparison.

Both implications retain the original natural operands and compare their canonical unit-denominator displays. -/
theorem natCast_le_iff_direct {left right : Nat} :
    (left : Rat.Fraction.Rational) ≤ (right : Rat.Fraction.Rational) ↔ left ≤ right := by
  constructor
  · intro lessEqual
    change
      (left : Rat.Fraction.Rational).num * ((right : Rat.Fraction.Rational).den : Int) ≤
        (right : Rat.Fraction.Rational).num * ((left : Rat.Fraction.Rational).den : Int) at lessEqual
    rw [Rat.Fraction.Cast.natCast_eq_fromInt, Rat.Fraction.Cast.natCast_eq_fromInt] at lessEqual
    change (left : Int) * 1 ≤ (right : Int) * 1 at lessEqual
    rw [Int.Arithmetic.mul_one, Int.Arithmetic.mul_one] at lessEqual
    exact Int.Order.natCast_le_iff.mp lessEqual
  · exact Rat.Fraction.Cast.Order.natCast_le_direct

/-- The canonical rational cast preserves a strict integer comparison.

The canonical casts have the supplied integers as numerators and unit denominators, so their cross-products preserve the
strict bound. -/
theorem intCast_lt_direct {left right : Int} (less : left < right) :
    (left : Rat.Fraction.Rational) < (right : Rat.Fraction.Rational) := by
  apply (Rat.Fraction.Order.Basic.lt_iff_cross _ _).mpr
  rw [Rat.Fraction.Cast.intCast_eq_fromInt, Rat.Fraction.Cast.intCast_eq_fromInt]
  change left * 1 < right * 1
  rw [Int.Arithmetic.mul_one, Int.Arithmetic.mul_one]
  exact less

/-- Canonical rational casts preserve and reflect weak integer comparison.

The exact unit-denominator displays preserve both integer operands and reflect the same weak comparison. -/
theorem intCast_le_intCast_iff_direct (left right : Int) :
    (left : Rat.Fraction.Rational) ≤ (right : Rat.Fraction.Rational) ↔ left ≤ right := by
  rw [Rat.Fraction.Cast.intCast_eq_fromInt, Rat.Fraction.Cast.intCast_eq_fromInt]
  change left * 1 ≤ right * 1 ↔ left ≤ right
  rw [Int.Arithmetic.mul_one, Int.Arithmetic.mul_one]

/-- Nonnegative integers cast to nonnegative canonical rationals.

Apply weak cast comparison to zero and the supplied integer, retaining the original nonnegative bound. -/
theorem cast_int_nonnegative {value : Int} (nonnegative : 0 ≤ value) :
    (0 : Fraction.Rational) ≤ (value : Fraction.Rational) := by
  have bound := (Fraction.Cast.Order.intCast_le_intCast_iff_direct 0 value).mpr nonnegative
  change (0 : Fraction.Rational) ≤ (value : Fraction.Rational) at bound
  exact bound

/-- Positive integers cast to positive canonical rationals.

Strict cast comparison retains the supplied positive integer bound against the canonical zero display. -/
theorem cast_int_positive {value : Int} (positive : 0 < value) :
    (0 : Fraction.Rational) < (value : Fraction.Rational) := by
  have bound := Fraction.Cast.Order.intCast_lt_direct positive
  change (0 : Fraction.Rational) < (value : Fraction.Rational) at bound
  exact bound

/-- Nonpositive integers cast to nonpositive canonical rationals.

The original upper bound by zero is preserved by the exact canonical integer cast. -/
theorem cast_int_nonpositive {value : Int} (nonpositive : value ≤ 0) :
    (value : Fraction.Rational) ≤ 0 := by
  have bound := (Fraction.Cast.Order.intCast_le_intCast_iff_direct value 0).mpr nonpositive
  change (value : Fraction.Rational) ≤ (0 : Fraction.Rational) at bound
  exact bound

/-- Negative integers cast to negative canonical rationals.

The original strict upper bound by zero is preserved by the exact canonical integer cast. -/
theorem cast_int_negative {value : Int} (negative : value < 0) :
    (value : Fraction.Rational) < 0 := by
  have bound := Fraction.Cast.Order.intCast_lt_direct negative
  change (value : Fraction.Rational) < (0 : Fraction.Rational) at bound
  exact bound

/-- Canonical rational casts preserve and reflect strict integer comparison.

The original unit-denominator cross-products preserve and reflect the strict comparison of the two supplied integer
numerators. -/
theorem intCast_lt_intCast_iff_direct (m n : Int) :
    ((m : Int) : Rat.Fraction.Rational) < (n : Rat.Fraction.Rational) ↔ m < n := by
  constructor
  · intro less
    have cross := (Rat.Fraction.Order.Basic.lt_iff_cross _ _).mp less
    rw [Rat.Fraction.Cast.intCast_eq_fromInt, Rat.Fraction.Cast.intCast_eq_fromInt] at cross
    change m * 1 < n * 1 at cross
    rw [Int.Arithmetic.mul_one, Int.Arithmetic.mul_one] at cross
    exact cross
  · exact Rat.Fraction.Cast.Order.intCast_lt_direct

/-- The canonical rational cast of a positive natural number is nonzero.

The supplied positive natural bound makes the exact canonical cast positive; equality with zero would contradict that
retained strict bound. -/
theorem rationalNatCastNonzero {value : Nat}
    (valuePositive : 0 < value) : (value : Fraction.Rational) ≠ 0 := by
  intro castZero
  have castPositive : (0 : Fraction.Rational) < (value : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct valuePositive
  rw [castZero] at castPositive
  exact (lt_irrefl 0) castPositive

end Purelib.Data.Rat.Fraction.Cast.Order
