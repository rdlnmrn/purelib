module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Rounding.Floor
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# Exact rational floor and reciprocal-ceiling bounds

Integer bounds identify the floor of the original rational. A positive
rational width also determines a finite reciprocal-ceiling mesh count whose
reciprocal is strictly below that width.
-/

namespace Purelib.Data.Rat.Rounding.Floor.Bounds

open Purelib.Data.Rat in
/-- A rational between an integer and its successor has that integer as its computed floor. -/
theorem floor_eq_of_bounds (integer : Int) (value : Fraction.Rational)
    (lower : Fraction.Cast.fromInt integer ≤ value)
    (upper : value < Fraction.Cast.fromInt (integer + 1)) :
    Rounding.Floor.floor value = integer := by
  have below : integer ≤ Rounding.Floor.floor value :=
    (Rounding.Floor.intCast_le_iff_floor integer value).mp (by
      simpa only [Fraction.Cast.intCast_eq_fromInt] using lower)
  have notAbove : ¬ integer + 1 ≤ Rounding.Floor.floor value := by
    intro above
    have bound := (Rounding.Floor.intCast_le_iff_floor (integer + 1) value).mpr above
    rw [Fraction.Cast.intCast_eq_fromInt] at bound
    exact (not_lt_of_ge bound) upper
  omega

/-- The reciprocal of the computed ceiling-plus-one count is below a positive rational width.

The count is the successor of the natural ceiling of the reciprocal width.
Its exact positive cast and the original ceiling bound provide the strict
comparison without an unbounded search or a caller-supplied sufficient count. -/
theorem reciprocal_ceilNat_lt (width : Fraction.Rational) (positive : 0 < width) :
    1 / ((Rounding.Floor.ceilNat (1 / width) + 1 : Nat) : Fraction.Rational) < width := by
  have countPositive : 0 < ((Rounding.Floor.ceilNat (1 / width) + 1 : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ _)
  have ceiling := Rounding.Floor.le_natCast_ceilNat_of_nonneg
    (Fraction.Order.Field.div_pos_direct (by decide : (0 : Fraction.Rational) < 1) positive).1
  have increased : (Rounding.Floor.ceilNat (1 / width) : Fraction.Rational) <
      ((Rounding.Floor.ceilNat (1 / width) + 1 : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_lt_direct (Nat.lt_succ_self _)
  have strict : 1 / width < ((Rounding.Floor.ceilNat (1 / width) + 1 : Nat) : Fraction.Rational) :=
    ⟨Fraction.Order.Basic.le_trans _ _ _ ceiling increased.1,
      fun reverse => increased.2 (Fraction.Order.Basic.le_trans _ _ _ reverse ceiling)⟩
  have paid := (Fraction.Order.Field.div_lt_iff_pos positive).mp strict
  apply (Fraction.Order.Field.div_lt_iff_pos countPositive).mpr
  rw [Fraction.Field.mul_comm]
  exact paid
end Purelib.Data.Rat.Rounding.Floor.Bounds

end
