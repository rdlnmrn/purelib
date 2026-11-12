module

public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Exact normalized fractions in an original retained proper interval -/

public section

namespace Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval

open Purelib
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- Normalize a parameter using the original interval's strictly positive width. -/
@[expose] def fraction (interval : Interval) (parameter : Rational) : Rational :=
  (parameter - interval.lower) / (interval.upper - interval.lower)

/-- A parameter in the original interval gives a normalized fraction in the closed unit interval. -/
theorem fraction_inside (interval : Interval) {parameter : Rational}
    (inside : interval.lower ≤ parameter ∧ parameter ≤ interval.upper) :
    0 ≤ interval.fraction parameter ∧ interval.fraction parameter ≤ 1 :=
  Order.Field.fraction_inside interval.ordered inside

/-- Interpolating the exact original endpoints by the normalized fraction recovers the supplied parameter. -/
theorem fraction_eq (interval : Interval) (parameter : Rational) :
    interval.lower + interval.fraction parameter * (interval.upper - interval.lower) = parameter := by
  have product := Field.div_mul_cancel_of_ne (parameter - interval.lower)
    (interval.upper - interval.lower) (ne_of_gt (Order.Arithmetic.sub_pos_direct interval.ordered))
  change interval.lower +
    ((parameter - interval.lower) / (interval.upper - interval.lower)) *
      (interval.upper - interval.lower) = parameter
  rewrite [product]
  ring1

/-- Strict original parameter order gives strict order of the same interval's normalized fractions. -/
theorem fraction_lt (interval : Interval) {first last : Rational} (ordered : first < last) :
    interval.fraction first < interval.fraction last := by
  apply Order.Arithmetic.lt_of_not_ge_direct
  intro reverse
  have product := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct reverse
    (Order.Arithmetic.sub_pos_direct interval.ordered).1
  have shifted := Order.Arithmetic.add_le_add_right_direct product interval.lower
  have lastEq : interval.fraction last * (interval.upper - interval.lower) + interval.lower = last := by
    rewrite [add_comm]
    exact interval.fraction_eq last
  have firstEq : interval.fraction first * (interval.upper - interval.lower) + interval.lower = first := by
    rewrite [add_comm]
    exact interval.fraction_eq first
  change interval.fraction last * (interval.upper - interval.lower) + interval.lower ≤
    interval.fraction first * (interval.upper - interval.lower) + interval.lower at shifted
  rewrite [lastEq, firstEq] at shifted
  exact ordered.2 shifted

end Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval

end
