module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Order.MinMax

section
public section

/-!
# Stability of finite cumulative laws

Total variation controls every executable lower-ray event, hence every exact
rational cumulative probability.  A displayed finite threshold grid packages
these pointwise bounds as the constructive finite replacement for a uniform
CDF comparison.  No supremum over all thresholds or limiting law is formed.
-/

namespace Purelib.Measure

open Purelib.Data.List

namespace Distribution

section
open Purelib.Data.Rat
/-- Compute the maximum cumulative-probability separation over the supplied finite threshold list, starting at zero.

The scan retains the exact two distributions and evaluates only the listed cuts; it does not assume that the list covers
their supports. -/
@[expose] def cumulativeGridDistance (left right : Distribution Fraction.Rational) :
    List Fraction.Rational → Fraction.Rational
  | [] => 0
  | threshold :: remaining =>
      max (Distance.rationalSeparation (left.cumulative threshold)
        (right.cumulative threshold))
        (cumulativeGridDistance left right remaining)

/-- Every finite cumulative grid distance is nonnegative. -/
theorem cumulativeGridDistance_nonnegative
  (left right : Distribution Fraction.Rational) :
    ∀ thresholds, 0 ≤ left.cumulativeGridDistance right thresholds
  | [] => le_rfl
  | threshold :: _ =>
      (Distance.rationalSeparation_nonneg
        (left.cumulative threshold) (right.cumulative threshold)).trans
        (Fraction.Order.Basic.le_max_left _ _)

/-- The cumulative separation at a listed cut is bounded by the exact grid distance. -/
theorem cumulative_separation_le_cumulativeGridDistance
    (left right : Distribution Fraction.Rational) (threshold : Fraction.Rational) :
    ∀ {thresholds : List Fraction.Rational}, threshold ∈ thresholds →
      Distance.rationalSeparation (left.cumulative threshold)
          (right.cumulative threshold) ≤
        left.cumulativeGridDistance right thresholds
  | [], member => (List.not_mem_nil member).elim
  | head :: remaining, member => by
      rcases Membership.mem_cons.mp member with equal | tailMember
      · subst threshold
        exact Fraction.Order.Basic.le_max_left _ _
      · exact (cumulative_separation_le_cumulativeGridDistance left right
          threshold tailMember).trans (Fraction.Order.Basic.le_max_right _ _)

/-- A nonnegative bound on separation at every listed cut bounds the grid distance. -/
theorem cumulativeGridDistance_le
    (left right : Distribution Fraction.Rational)
    (thresholds : List Fraction.Rational) (bound : Fraction.Rational)
    (boundNonnegative : 0 ≤ bound)
    (pointwise : ∀ threshold, threshold ∈ thresholds →
      Distance.rationalSeparation (left.cumulative threshold)
        (right.cumulative threshold) ≤ bound) :
    left.cumulativeGridDistance right thresholds ≤ bound := by
  induction thresholds with
  | nil => exact boundNonnegative
  | cons threshold remaining inductionHypothesis =>
      unfold cumulativeGridDistance
      apply Fraction.Order.Basic.max_le
      · exact pointwise threshold List.mem_cons_self
      · apply inductionHypothesis
        intro candidate member
        exact pointwise candidate (List.mem_cons_of_mem threshold member)

/-- Reversing the two original laws preserves their distance on the same threshold grid. -/
theorem cumulativeGridDistance_symm
    (left right : Distribution Fraction.Rational) :
    ∀ thresholds,
      left.cumulativeGridDistance right thresholds =
        right.cumulativeGridDistance left thresholds
  | [] => rfl
  | threshold :: remaining => by
      unfold cumulativeGridDistance
      rw [Distance.rationalSeparation_symm,
        cumulativeGridDistance_symm left right remaining]

/-- A law has zero cumulative grid distance from itself. -/
@[simp] theorem cumulativeGridDistance_refl
    (distribution : Distribution Fraction.Rational) (thresholds : List Fraction.Rational) :
    distribution.cumulativeGridDistance distribution thresholds = 0 := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · apply distribution.cumulativeGridDistance_le distribution thresholds 0
      le_rfl
    intro threshold member
    exact ((Distance.rationalSeparation_eq_zero_iff _ _).mpr rfl).le
  · exact distribution.cumulativeGridDistance_nonnegative distribution
      thresholds

/-- Cumulative grid distance satisfies the triangle inequality through a third law on the same exact grid. -/
theorem cumulativeGridDistance_triangle
    (left middle right : Distribution Fraction.Rational)
    (thresholds : List Fraction.Rational) :
    left.cumulativeGridDistance right thresholds ≤
      left.cumulativeGridDistance middle thresholds +
        middle.cumulativeGridDistance right thresholds := by
  apply left.cumulativeGridDistance_le right thresholds
  · exact add_nonneg
      (left.cumulativeGridDistance_nonnegative middle thresholds)
      (middle.cumulativeGridDistance_nonnegative right thresholds)
  · intro threshold member
    calc
      Distance.rationalSeparation (left.cumulative threshold)
          (right.cumulative threshold) ≤
        Distance.rationalSeparation (left.cumulative threshold)
            (middle.cumulative threshold) +
          Distance.rationalSeparation (middle.cumulative threshold)
            (right.cumulative threshold) :=
        Distance.rationalSeparation_triangle _ _ _
      _ ≤ left.cumulativeGridDistance middle thresholds +
          middle.cumulativeGridDistance right thresholds :=
        add_le_add
          (left.cumulative_separation_le_cumulativeGridDistance middle
            threshold member)
          (middle.cumulative_separation_le_cumulativeGridDistance right
            threshold member)

/-- Grid distance vanishes exactly when the original cumulative functions agree at every listed cut. -/
theorem cumulativeGridDistance_eq_zero_iff
    (left right : Distribution Fraction.Rational) (thresholds : List Fraction.Rational) :
    left.cumulativeGridDistance right thresholds = 0 ↔
      ∀ threshold, threshold ∈ thresholds →
        left.cumulative threshold = right.cumulative threshold := by
  constructor
  · intro distanceZero threshold member
    apply (Distance.rationalSeparation_eq_zero_iff _ _).mp
    apply Fraction.Order.Basic.Compatibility.le_antisymm
    · rw [← distanceZero]
      exact left.cumulative_separation_le_cumulativeGridDistance right
        threshold member
    · exact Distance.rationalSeparation_nonneg _ _
  · intro equal
    apply Fraction.Order.Basic.Compatibility.le_antisymm
    · apply left.cumulativeGridDistance_le right thresholds 0 le_rfl
      intro threshold member
      exact ((Distance.rationalSeparation_eq_zero_iff _ _).mpr
        (equal threshold member)).le
    · exact left.cumulativeGridDistance_nonnegative right thresholds

/-- Require cumulative-probability separation below the tolerance at every cut in the exact finite grid. -/
@[expose] def CumulativeGridClose (left right : Distribution Fraction.Rational)
    (thresholds : List Fraction.Rational) (tolerance : Fraction.Rational) : Prop :=
  ∀ threshold, threshold ∈ thresholds →
    Distance.rationalSeparation (left.cumulative threshold)
      (right.cumulative threshold) < tolerance

/-- For positive tolerance, strict grid-distance control is equivalent to strict separation control at every listed cut.
-/
theorem cumulativeGridDistance_lt_iff
    (left right : Distribution Fraction.Rational)
    (thresholds : List Fraction.Rational) (tolerance : Fraction.Rational)
    (tolerancePositive : 0 < tolerance) :
    left.cumulativeGridDistance right thresholds < tolerance ↔
      CumulativeGridClose left right thresholds tolerance := by
  constructor
  · intro distanceSmall threshold member
    exact (left.cumulative_separation_le_cumulativeGridDistance right
      threshold member).trans_lt distanceSmall
  · intro close
    induction thresholds with
    | nil => exact tolerancePositive
    | cons threshold remaining inductionHypothesis =>
        unfold cumulativeGridDistance
        apply Fraction.Order.Basic.max_lt
        · exact close threshold List.mem_cons_self
        · exact
          inductionHypothesis (by
            intro candidate member
            exact close candidate
              (List.mem_cons_of_mem threshold member))
end

end Distribution

end Purelib.Measure

end
