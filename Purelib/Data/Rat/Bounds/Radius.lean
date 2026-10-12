module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Strict rational displacement bounds for positive radii

A positive rational radius gives strict displacement comparisons about the
same retained centre. Doubling that radius gives the corresponding strict
outer comparisons by direct scalar translation.
-/

open Purelib.Data.Rat
open Fraction.Order

namespace Purelib.Data.Rat.Bounds.Radius

/-- A positive rational radius is strictly smaller than twice itself.

The original positive radius is translated by itself. The resulting
strict sum is twice that same rational radius. -/
public theorem radius_lt_twice {r : Fraction.Rational} (positive : 0 < r) :
    r < 2 * r := by
  calc
    r = 0 + r := by ring1
    _ < r + r :=
      Arithmetic.add_lt_add_right_direct positive r
    _ = 2 * r := by ring1

/-- Subtracting twice a positive radius gives a smaller rational than subtracting that radius once.

Negating the original doubling comparison orders the two negative
displacements. Translating by the same centre preserves their
strict endpoint comparison. -/
public theorem sub_twice_lt_sub {c r : Fraction.Rational} (positive : 0 < r) :
    c - 2 * r < c - r := by
  have negative := Arithmetic.neg_lt_neg_direct
    (radius_lt_twice positive)
  calc
    c - 2 * r = -(2 * r) + c := by ring1
    _ < -r + c :=
      Arithmetic.add_lt_add_right_direct negative c
    _ = c - r := by ring1

/-- Adding a positive radius gives a smaller rational than adding twice that radius.

The original doubling comparison is translated by the displayed
centre. Its two endpoints retain one radius and twice that same
radius as their respective displacements. -/
public theorem add_lt_add_twice {c r : Fraction.Rational} (positive : 0 < r) :
    c + r < c + 2 * r := by
  have enlarged := Arithmetic.add_lt_add_right_direct
    (radius_lt_twice positive) c
  simpa only [Fraction.Field.add_comm] using enlarged

/-- Subtracting a positive rational radius gives a point strictly below its center.

Negating the supplied positive radius gives a strictly negative displacement.
Direct translation by the original center preserves that strict comparison. -/
public theorem sub_lt_center {c r : Fraction.Rational} (positive : 0 < r) :
    c - r < c := by
  have negative : -r < 0 := by
    calc
      -r < -(0 : Fraction.Rational) := Arithmetic.neg_lt_neg_direct positive
      _ = 0 := by decide
  calc
    c - r = -r + c := by ring1
    _ < 0 + c := Arithmetic.add_lt_add_right_direct negative c
    _ = c := by ring1

/-- Adding a positive rational radius gives a point strictly above its center.

The original positive radius is translated by the displayed center.
Direct strict addition order preserves that displacement and its endpoint. -/
public theorem center_lt_add {c r : Fraction.Rational} (positive : 0 < r) :
    c < c + r := by
  have enlarged := Arithmetic.add_lt_add_right_direct positive c
  calc
    c = 0 + c := by ring1
    _ < r + c := enlarged
    _ = c + r := by ring1

end Purelib.Data.Rat.Bounds.Radius
