module
import Purelib.Algebra.NatCast
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

section
@[expose] public section

/-!
# Finite layer-cake identities

For a natural-valued observable, truncation at a displayed finite height is
the sum of its Boolean upper-level indicators.  Integrating this pointwise
identity gives an exact finite tail-sum, or layer-cake, formula.  There is no
infinite series and no improper integral.
-/

namespace Purelib.Measure

/-- Select payloads whose natural-valued observation is strictly above the supplied height. -/
def natAboveEvent {α : Type} (height : Nat) (value : α → Nat) : α → Bool :=
  fun item => decide (height < value item)

section Content

open Purelib.Data.Rat in
open Purelib.Algebra in
/-- Increasing a natural truncation height by one adds precisely the indicator that the observed value exceeds the old
height. -/
public theorem cast_min_succ_eq_cast_min_add_indicator {α : Type}
    (value : α → Nat) (height : Nat) (item : α) :
    ((min (value item) (height + 1) : Nat) : Fraction.Rational) =
      ((min (value item) height : Nat) : Fraction.Rational) +
        Distribution.indicator (natAboveEvent height value) item := by
  by_cases above : height < value item
  · have naturalIdentity :
        min (value item) (height + 1) = min (value item) height + 1 := by
      change (if value item ≤ height + 1 then value item else height + 1) =
        (if value item ≤ height then value item else height) + 1
      rewrite [if_neg (Nat.not_le_of_lt above)]
      by_cases atMostSuccessor : value item ≤ height + 1
      · rewrite [if_pos atMostSuccessor]
        exact Nat.le_antisymm atMostSuccessor (Nat.succ_le_of_lt above)
      · exact if_neg atMostSuccessor
    rewrite [naturalIdentity, NatCast.add, Nat.cast_one]
    unfold Distribution.indicator natAboveEvent
    rewrite [decide_eq_true above]
    rfl
  · have valueLeHeight : value item ≤ height := Nat.le_of_not_gt above
    have naturalIdentity :
        min (value item) (height + 1) = min (value item) height := by
      change (if value item ≤ height + 1 then value item else height + 1) =
        (if value item ≤ height then value item else height)
      rewrite [if_pos (valueLeHeight.trans (Nat.le_succ height)),
        if_pos valueLeHeight]
      rfl
    rewrite [naturalIdentity]
    unfold Distribution.indicator natAboveEvent
    rewrite [decide_eq_false above]
    exact (add_zero ((min (value item) height : Nat) : Fraction.Rational)).symm

end Content

end Purelib.Measure

end
