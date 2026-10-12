module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Algebra.Group.Negation
import Purelib.Tactic.Ring

/-!
# Positive and negative parts of a rational

The two parts retain the maxima of the original value and its negation with
zero. Their difference recovers the signed value, and their sum its exact
rational separation from zero.
-/

namespace Purelib.Data.Rat

open Fraction.Order

/-- Take the nonnegative part of a rational as its maximum with zero.

The original rational and zero are the two retained inputs to the executable
maximum. Nonpositive values select zero; nonnegative values select themselves. -/
@[expose] public def positiveWeight (weight : Fraction.Rational) : Fraction.Rational := max weight 0

/-- Take the magnitude of the nonpositive part as the maximum of its negation with zero.

The executable maximum compares the original rational's negation with zero.
This retains its exact magnitude when nonpositive and returns zero otherwise. -/
@[expose] public def negativeWeight (weight : Fraction.Rational) : Fraction.Rational := max (-weight) 0

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

/-- The positive part of a rational is nonnegative.

The retained maximum is at least its original zero argument. Its other
argument retains the original rational, with no sign assumption. -/
public theorem positiveWeight_nonneg (weight : Fraction.Rational) :
    0 ≤ positiveWeight weight :=
  Basic.le_max_right _ _

/-- The negative-part magnitude of a rational is nonnegative.

The retained maximum is at least its original zero argument. The other
argument is the original rational's negation, with no sign assumption. -/
public theorem negativeWeight_nonneg (weight : Fraction.Rational) :
    0 ≤ negativeWeight weight :=
  Basic.le_max_right _ _

/-- The positive part of a nonnegative rational is that rational itself.

The supplied comparison bounds zero by the original value. The retained
maximum therefore identifies its selected input with that original value. -/
public theorem positiveWeight_eq_self_of_nonneg {weight : Fraction.Rational}
    (nonnegative : 0 ≤ weight) : positiveWeight weight = weight :=
  Basic.max_eq_left nonnegative

/-- The positive part of a nonpositive rational is zero.

The supplied comparison selects zero in the original maximum. Equality
holds also when the displayed rational itself is zero. -/
public theorem positiveWeight_eq_zero_of_nonpos {weight : Fraction.Rational}
    (nonpositive : weight ≤ 0) : positiveWeight weight = 0 :=
  Basic.max_eq_right nonpositive

/-- The negative-part magnitude of a nonnegative rational is zero.

Direct negation reverses the original nonnegative comparison. Its zero
endpoint is unchanged, so the retained maximum selects zero. -/
public theorem negativeWeight_eq_zero_of_nonneg {weight : Fraction.Rational}
    (nonnegative : 0 ≤ weight) : negativeWeight weight = 0 := by
  have negativeNonpositive : -weight ≤ 0 := by
    calc
      -weight ≤ -(0 : Fraction.Rational) := Arithmetic.neg_le_neg_direct nonnegative
      _ = 0 := by decide
  exact Basic.max_eq_right negativeNonpositive

/-- The negative-part magnitude of a nonpositive rational is its negation.

Direct negation reverses the original nonpositive comparison. The original
negated rational bounds zero and is therefore the retained maximum. -/
public theorem negativeWeight_eq_neg_of_nonpos {weight : Fraction.Rational}
    (nonpositive : weight ≤ 0) : negativeWeight weight = -weight := by
  have negativeNonnegative : 0 ≤ -weight := by
    calc
      0 = -(0 : Fraction.Rational) := by decide
      _ ≤ -weight := Arithmetic.neg_le_neg_direct nonpositive
  exact Basic.max_eq_left negativeNonnegative

/-- Every rational is its positive part minus its negative-part magnitude.

The original comparison with zero identifies one part as zero and the
other as the retained signed value or its negation. Direct scalar cancellation
recovers that same original rational in either case. -/
public theorem positiveWeight_sub_negativeWeight (weight : Fraction.Rational) :
    positiveWeight weight - negativeWeight weight = weight := by
  by_cases nonnegative : 0 ≤ weight
  · rw [positiveWeight_eq_self_of_nonneg nonnegative,
      negativeWeight_eq_zero_of_nonneg nonnegative]
    ring1
  · have nonpositive : weight ≤ 0 := (Arithmetic.lt_of_not_ge_direct nonnegative).le
    rw [positiveWeight_eq_zero_of_nonpos nonpositive,
      negativeWeight_eq_neg_of_nonpos nonpositive]
    ring1

/-- The rational distance to zero is the sum of its positive and negative-part magnitudes.

The original sign comparison identifies the larger directed difference as
the contributing part. The other retained part is zero, giving the exact sum. -/
public theorem rationalSeparation_zero_eq_parts (weight : Fraction.Rational) :
    Distance.rationalSeparation weight 0 = positiveWeight weight + negativeWeight weight := by
  have forward : weight - 0 = weight := by ring1
  have reverse : (0 : Fraction.Rational) - weight = -weight := by ring1
  by_cases nonnegative : 0 ≤ weight
  · have negativeNonpositive : -weight ≤ 0 := by
      calc
        -weight ≤ -(0 : Fraction.Rational) := Arithmetic.neg_le_neg_direct nonnegative
        _ = 0 := by decide
    have negativeLeWeight : -weight ≤ weight := negativeNonpositive.trans nonnegative
    calc
      Distance.rationalSeparation weight 0 = max weight (-weight) := by
        unfold Distance.rationalSeparation
        rw [forward, reverse]
      _ = weight := Basic.max_eq_left negativeLeWeight
      _ = positiveWeight weight + negativeWeight weight := by
        rw [positiveWeight_eq_self_of_nonneg nonnegative,
          negativeWeight_eq_zero_of_nonneg nonnegative]
        ring1
  · have nonpositive : weight ≤ 0 := (Arithmetic.lt_of_not_ge_direct nonnegative).le
    have negativeNonnegative : 0 ≤ -weight := by
      calc
        0 = -(0 : Fraction.Rational) := by decide
        _ ≤ -weight := Arithmetic.neg_le_neg_direct nonpositive
    have weightLeNegative : weight ≤ -weight := nonpositive.trans negativeNonnegative
    calc
      Distance.rationalSeparation weight 0 = max weight (-weight) := by
        unfold Distance.rationalSeparation
        rw [forward, reverse]
      _ = -weight := Basic.max_eq_right weightLeNegative
      _ = positiveWeight weight + negativeWeight weight := by
        rw [positiveWeight_eq_zero_of_nonpos nonpositive,
          negativeWeight_eq_neg_of_nonpos nonpositive]
        ring1

end Purelib.Data.Rat
