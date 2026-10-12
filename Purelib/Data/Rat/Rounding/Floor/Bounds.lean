module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Rounding.Floor
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# Checked replay of bounded Newton proposal traces

Saved integer grid coordinates are checked by multiplication and inequalities;
saved Newton updates are checked by multiplication.  Replay does not call the
floor or Newton proposal generators.  The starting proposal is explicit, so
diameter preparation can supply its checked warm-up result while ordinary
refinement supplies the box midpoint.  The existing finite candidate acceptance
check is retained, including its safe-side selection and winding.
All imports are already audited finite dependencies of checked shrinking.
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
end Purelib.Data.Rat.Rounding.Floor.Bounds

end
