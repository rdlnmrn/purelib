module

public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Coordinate enlargements of original rational boxes

A retained nonnegative margin expands the four original endpoints. A
centered square whose center remains in the original box and whose radius
pays that margin refines this same enlargement.
-/

public section

namespace Purelib.Geometry.Rational.Box

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational.Box.Square.Centered

/-- Expand the original four box endpoints by one nonnegative coordinate margin.

This is an original rational Box with the same endpoint orientation. Its
validity uses only the original endpoint ordering and the displayed margin;
no root owner, sample or polynomial is selected.
-/
@[expose] def enlarge (box : Box) (margin : Rational) (nonnegative : 0 ≤ margin) : Box where
  xLower := box.xLower - margin
  xUpper := box.xUpper + margin
  yLower := box.yLower - margin
  yUpper := box.yUpper + margin
  x_valid := by
    have nonnegativeTwice := Order.Arithmetic.mul_nonneg_direct
      (by decide +kernel : (0 : Rational) ≤ 2) nonnegative
    have difference := Order.Arithmetic.sub_nonneg_direct box.x_valid
    apply Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 = 0 + 0 := by ring1
      _ ≤ (box.xUpper - box.xLower) + 2 * margin :=
        Order.Arithmetic.add_le_add_direct difference nonnegativeTwice
      _ = (box.xUpper + margin) - (box.xLower - margin) := by ring1
  y_valid := by
    have nonnegativeTwice := Order.Arithmetic.mul_nonneg_direct
      (by decide +kernel : (0 : Rational) ≤ 2) nonnegative
    have difference := Order.Arithmetic.sub_nonneg_direct box.y_valid
    apply Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 = 0 + 0 := by ring1
      _ ≤ (box.yUpper - box.yLower) + 2 * margin :=
        Order.Arithmetic.add_le_add_direct difference nonnegativeTwice
      _ = (box.yUpper + margin) - (box.yLower - margin) := by ring1

/-- A centered square refines the original box enlarged by a bound on its radius.

The retained center lies in the original box. Each lower endpoint is
bounded by subtracting the actual radius and each upper endpoint by
adding it, preserving both the original center and the original box.
-/
theorem centeredBox_refines_enlarge {box : Box} {center : Canonical}
    (inside : box.Contains center) {radius margin : Rational}
    (radiusNonnegative : 0 ≤ radius) (marginNonnegative : 0 ≤ margin) (radiusBound : radius ≤ margin) :
    (BoxTransport.centeredBox center radius radiusNonnegative).Refines
      (box.enlarge margin marginNonnegative) :=
  ⟨Order.Arithmetic.sub_le_sub_direct inside.1 radiusBound,
    Order.Arithmetic.add_le_add_direct inside.2.1 radiusBound,
    Order.Arithmetic.sub_le_sub_direct inside.2.2.1 radiusBound,
    Order.Arithmetic.add_le_add_direct inside.2.2.2 radiusBound⟩

end Purelib.Geometry.Rational.Box

end
