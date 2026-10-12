module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Squaring retained rational intervals
-/

namespace Purelib.Data.Rat.Interval

open Purelib.Data
open Purelib.Data.Rat

public section

/-- Construct a rational interval containing the squares of all original contained values.

If the original interval contains zero, use zero as the new lower bound; otherwise use the smaller endpoint square. In
both cases the larger endpoint square is the upper bound, with an explicit retained proof of endpoint order. -/
@[expose] def square (bound : Rat.Interval) : Rat.Interval :=
  if bound.lower ≤ 0 ∧ 0 ≤ bound.upper then
    { lower := 0
      upper := max (bound.lower ^ 2) (bound.upper ^ 2)
      valid := (Fraction.Order.Arithmetic.sq_nonneg_direct bound.lower).trans
        (Fraction.Order.Basic.le_max_left _ _) }
  else
    { lower := min (bound.lower ^ 2) (bound.upper ^ 2)
      upper := max (bound.lower ^ 2) (bound.upper ^ 2)
      valid := (Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.le_max_left _ _) }

/-- An interval containing zero has squared-interval lower endpoint zero. -/
theorem square_lower_of_crossesZero (bound : Rat.Interval)
    (crosses : bound.lower ≤ 0 ∧ 0 ≤ bound.upper) :
    bound.square.lower = 0 := by
  unfold Interval.square
  rw [if_pos crosses]

/-- For an interval excluding zero, the squared-interval lower endpoint is the smaller endpoint square. -/
theorem square_lower_of_not_crossesZero (bound : Rat.Interval)
    (notCrosses : ¬(bound.lower ≤ 0 ∧ 0 ≤ bound.upper)) :
    bound.square.lower = min (bound.lower ^ 2) (bound.upper ^ 2) := by
  unfold Interval.square
  rw [if_neg notCrosses]

/-- The squared-interval upper endpoint is always the larger original endpoint square. -/
@[simp] theorem square_upper (bound : Rat.Interval) :
    bound.square.upper = max (bound.lower ^ 2) (bound.upper ^ 2) := by
  unfold Interval.square
  split <;> rfl

/-- A rational between two endpoints has square at most the larger endpoint square. -/
private theorem sq_le_endpoint_max {bound : Rat.Interval} {value : Fraction.Rational}
    (inside : bound.Contains value) :
    value ^ 2 ≤ max (bound.lower ^ 2) (bound.upper ^ 2) := by
  by_cases nonnegative : 0 ≤ value
  · have upperNonnegative : 0 ≤ bound.upper := nonnegative.trans inside.2
    have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
      nonnegative inside.2 2
    exact powered.trans (Fraction.Order.Basic.le_max_right _ _)
  · have valueNegative : value < 0 :=
      Fraction.Order.Arithmetic.lt_of_not_ge_direct nonnegative
    have negValueNonnegative : 0 ≤ -value := by
      have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct
        valueNegative.le
      simpa only [neg_zero] using reversed
    have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct inside.1
    have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
      negValueNonnegative reversed 2
    calc
      value ^ 2 = (-value) ^ 2 := by ring1
      _ ≤ (-bound.lower) ^ 2 := powered
      _ = bound.lower ^ 2 := by ring1
      _ ≤ max (bound.lower ^ 2) (bound.upper ^ 2) := Fraction.Order.Basic.le_max_left _ _

/-- The squared interval contains the square of every value contained in the original interval. -/
theorem square_contains {bound : Rat.Interval} {value : Fraction.Rational}
    (inside : bound.Contains value) :
    bound.square.Contains (value ^ 2) := by
  constructor
  · by_cases crosses : bound.lower ≤ 0 ∧ 0 ≤ bound.upper
    · rw [bound.square_lower_of_crossesZero crosses]
      exact Fraction.Order.Arithmetic.sq_nonneg_direct value
    · rw [bound.square_lower_of_not_crossesZero crosses]
      by_cases lowerNonpositive : bound.lower ≤ 0
      · have upperNotNonnegative : ¬0 ≤ bound.upper := by
          intro upperNonnegative
          exact crosses ⟨lowerNonpositive, upperNonnegative⟩
        have upperNegative : bound.upper < 0 :=
          Fraction.Order.Arithmetic.lt_of_not_ge_direct upperNotNonnegative
        have negUpperNonnegative : 0 ≤ -bound.upper := by
          have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct
            upperNegative.le
          simpa only [neg_zero] using reversed
        have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct inside.2
        have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
          negUpperNonnegative reversed 2
        exact (Fraction.Order.Basic.min_le_right _ _).trans (by
          calc
            bound.upper ^ 2 = (-bound.upper) ^ 2 := by ring1
            _ ≤ (-value) ^ 2 := powered
            _ = value ^ 2 := by ring1)
      · have lowerPositive : 0 < bound.lower :=
          Fraction.Order.Arithmetic.lt_of_not_ge_direct lowerNonpositive
        have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
          lowerPositive.le inside.1 2
        exact (Fraction.Order.Basic.min_le_left _ _).trans powered
  · rw [Interval.square_upper]
    exact Interval.sq_le_endpoint_max inside

/-- Squaring both rational intervals preserves endpoint refinement. -/
theorem Refines.square {inner outer : Rat.Interval}
    (refines : Interval.Refines inner outer) :
    Interval.Refines inner.square outer.square := by
  have innerLowerInside : outer.Contains inner.lower :=
    ⟨refines.lower, inner.valid.trans refines.upper⟩
  have innerUpperInside : outer.Contains inner.upper :=
    ⟨refines.lower.trans inner.valid, refines.upper⟩
  constructor
  · by_cases innerCrosses : inner.lower ≤ 0 ∧ 0 ≤ inner.upper
    · have outerCrosses : outer.lower ≤ 0 ∧ 0 ≤ outer.upper :=
        ⟨refines.lower.trans innerCrosses.1,
          innerCrosses.2.trans refines.upper⟩
      rw [inner.square_lower_of_crossesZero innerCrosses,
        outer.square_lower_of_crossesZero outerCrosses]
    · rw [inner.square_lower_of_not_crossesZero innerCrosses]
      exact Fraction.Order.Basic.le_min
        (outer.square_contains innerLowerInside).1
        (outer.square_contains innerUpperInside).1
  · rw [Interval.square_upper]
    exact Fraction.Order.Basic.max_le
      (outer.square_contains innerLowerInside).2
      (outer.square_contains innerUpperInside).2

end

end Purelib.Data.Rat.Interval
