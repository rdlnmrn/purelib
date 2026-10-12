module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-! Finite affine segments between two points of a rational rectangle. -/

namespace Purelib.Geometry.Rational.Box

open Purelib.Data.Rat in
/-- A convex combination of two contained rationals remains between the same retained endpoints. -/
public theorem coordinate_between {lower upper first last
  parameter : Fraction.Rational}
    (firstInside : lower ≤ first ∧ first ≤ upper) (lastInside : lower ≤ last ∧ last ≤ upper)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    lower ≤ first + parameter * (last - first) ∧ first + parameter * (last - first) ≤ upper := by
  have complement := Fraction.Order.Arithmetic.sub_nonneg_direct inside.2
  constructor
  · calc
      _ = (1 - parameter) * lower + parameter * lower := by ring1
      _ ≤ (1 - parameter) * first + parameter * last := add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstInside.1 complement)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lastInside.1 inside.1)
      _ = _ := by ring1
  · calc
      _ = (1 - parameter) * first + parameter * last := by ring1
      _ ≤ (1 - parameter) * upper + parameter * upper := add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstInside.2 complement)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lastInside.2 inside.1)
      _ = _ := by ring1

end Purelib.Geometry.Rational.Box

end
