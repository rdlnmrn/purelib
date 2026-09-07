import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Bounds

/-!
# Constructive squaring of rational enclosures

Squaring a displayed rational interval is an exact finite case split.  If the
interval contains zero the least square is zero; otherwise it is the smaller
endpoint square.  The greatest square is always the larger endpoint square.
-/

namespace FiniteMeasure

namespace Bound

/-- Exact rational enclosure of the squares of all values admitted by a
displayed rational bound. -/
def square (bound : Bound) : Bound :=
  if bound.lower ≤ 0 ∧ 0 ≤ bound.upper then
    { lower := 0
      upper := max (bound.lower ^ 2) (bound.upper ^ 2)
      valid := (RFAP.ConstructiveFraction.sq_nonneg_direct bound.lower).trans
        (le_max_left _ _) }
  else
    { lower := min (bound.lower ^ 2) (bound.upper ^ 2)
      upper := max (bound.lower ^ 2) (bound.upper ^ 2)
      valid := (min_le_left _ _).trans (le_max_left _ _) }

theorem square_lower_of_crossesZero (bound : Bound)
    (crosses : bound.lower ≤ 0 ∧ 0 ≤ bound.upper) :
    bound.square.lower = 0 := by
  simp only [square, if_pos crosses]

theorem square_lower_of_not_crossesZero (bound : Bound)
    (notCrosses : ¬(bound.lower ≤ 0 ∧ 0 ≤ bound.upper)) :
    bound.square.lower = min (bound.lower ^ 2) (bound.upper ^ 2) := by
  simp only [square, if_neg notCrosses]

@[simp] theorem square_upper (bound : Bound) :
    bound.square.upper = max (bound.lower ^ 2) (bound.upper ^ 2) := by
  unfold square
  split <;> rfl

private theorem sq_le_endpoint_max {bound : Bound} {value : Coordinate}
    (inside : bound.Contains value) :
    value ^ 2 ≤ max (bound.lower ^ 2) (bound.upper ^ 2) := by
  by_cases nonnegative : 0 ≤ value
  · have upperNonnegative : 0 ≤ bound.upper := nonnegative.trans inside.2
    have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
      nonnegative inside.2 2
    exact powered.trans (le_max_right _ _)
  · have valueNegative : value < 0 :=
      RFAP.ConstructiveFraction.lt_of_not_ge_direct nonnegative
    have negValueNonnegative : 0 ≤ -value := by
      have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct
        valueNegative.le
      simpa only [neg_zero] using reversed
    have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct inside.1
    have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
      negValueNonnegative reversed 2
    calc
      value ^ 2 = (-value) ^ 2 := by ring1
      _ ≤ (-bound.lower) ^ 2 := powered
      _ = bound.lower ^ 2 := by ring1
      _ ≤ max (bound.lower ^ 2) (bound.upper ^ 2) := le_max_left _ _

/-- Squaring preserves membership in the exact squared enclosure. -/
theorem square_contains {bound : Bound} {value : Coordinate}
    (inside : bound.Contains value) :
    bound.square.Contains (value ^ 2) := by
  constructor
  · by_cases crosses : bound.lower ≤ 0 ∧ 0 ≤ bound.upper
    · rw [bound.square_lower_of_crossesZero crosses]
      exact RFAP.ConstructiveFraction.sq_nonneg_direct value
    · rw [bound.square_lower_of_not_crossesZero crosses]
      by_cases lowerNonpositive : bound.lower ≤ 0
      · have upperNotNonnegative : ¬0 ≤ bound.upper := by
          intro upperNonnegative
          exact crosses ⟨lowerNonpositive, upperNonnegative⟩
        have upperNegative : bound.upper < 0 :=
          RFAP.ConstructiveFraction.lt_of_not_ge_direct upperNotNonnegative
        have negUpperNonnegative : 0 ≤ -bound.upper := by
          have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct
            upperNegative.le
          simpa only [neg_zero] using reversed
        have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct inside.2
        have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
          negUpperNonnegative reversed 2
        exact (min_le_right _ _).trans (by
          calc
            bound.upper ^ 2 = (-bound.upper) ^ 2 := by ring1
            _ ≤ (-value) ^ 2 := powered
            _ = value ^ 2 := by ring1)
      · have lowerPositive : 0 < bound.lower :=
          RFAP.ConstructiveFraction.lt_of_not_ge_direct lowerNonpositive
        have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
          lowerPositive.le inside.1 2
        exact (min_le_left _ _).trans powered
  · rw [square_upper]
    exact sq_le_endpoint_max inside

/-- Narrowing a rational enclosure also narrows its exact squared
enclosure. -/
theorem Refines.square {inner outer : Bound}
    (refines : Refines inner outer) :
    Refines inner.square outer.square := by
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
      exact le_min
        (outer.square_contains innerLowerInside).1
        (outer.square_contains innerUpperInside).1
  · rw [square_upper]
    exact max_le
      (outer.square_contains innerLowerInside).2
      (outer.square_contains innerUpperInside).2

end Bound

end FiniteMeasure
