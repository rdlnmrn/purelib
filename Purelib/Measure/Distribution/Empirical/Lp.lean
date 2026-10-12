module
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Empirical.Basic
public import Purelib.Measure.Distribution.Empirical.Histogram
import Purelib.Measure.Distribution.Lp.Equivalence
import Purelib.Measure.Sampling.Statistic
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Lp quantities of explicit empirical distributions

A nonempty displayed sample produces exact finite sample averages for every
natural-powered magnitude and distance.  Its executable essential maximum is
the recursively computed maximum over the displayed sample rows.
-/

namespace Purelib.Measure

open Purelib.Data.Rat
/-- The empirical powered-Lp value equals the original sample's magnitude-power sum divided by its length. -/
theorem empiricalDistribution_poweredLp {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (exponent : Nat) (value : α → Fraction.Rational) :
    (empiricalDistribution samples positiveLength).poweredLp exponent value =
      sumValues samples (fun item =>
        Distance.rationalSeparation (value item) 0 ^ exponent) /
          (samples.length : Fraction.Rational) := by
  change (empiricalDistribution samples positiveLength).expectation
    (fun item => Distance.rationalSeparation (value item) 0 ^ exponent) = _
  exact empiricalDistribution_expectation samples positiveLength _

/-- The empirical powered-Lp distance equals the original sample's separation-power sum divided by its length. -/
theorem empiricalDistribution_poweredLpDistance {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (exponent : Nat) (left right : α → Fraction.Rational) :
    (empiricalDistribution samples positiveLength).poweredLpDistance
        exponent left right =
      sumValues samples (fun item =>
        Distance.rationalSeparation (left item) (right item) ^ exponent) /
          (samples.length : Fraction.Rational) := by
  change (empiricalDistribution samples positiveLength).expectation
    (fun item =>
      Distance.rationalSeparation (left item) (right item) ^ exponent) = _
  exact empiricalDistribution_expectation samples positiveLength _

/-- The empirical L1 magnitude equals the original sample's magnitude sum divided by its length. -/
theorem empiricalDistribution_poweredL1 {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Fraction.Rational) :
    (empiricalDistribution samples positiveLength).poweredL1 value =
      sumValues samples (fun item => Distance.rationalSeparation (value item) 0) /
        (samples.length : Fraction.Rational) := by
  calc
    (empiricalDistribution samples positiveLength).poweredL1 value =
        (empiricalDistribution samples positiveLength).poweredLp 1 value :=
      ((empiricalDistribution samples positiveLength).poweredLp_one value).symm
    _ = sumValues samples (fun item =>
          Distance.rationalSeparation (value item) 0 ^ 1) /
        (samples.length : Fraction.Rational) :=
      empiricalDistribution_poweredLp samples positiveLength 1 value
    _ = sumValues samples (fun item => Distance.rationalSeparation (value item) 0) /
        (samples.length : Fraction.Rational) :=
      congrArg (fun total => total / (samples.length : Fraction.Rational))
        (sumValues_congr samples _ _ (fun item => pow_one _))

/-- The empirical L1 distance equals the original sample's pointwise separation sum divided by its length. -/
theorem empiricalDistribution_l1Distance {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (left right : α → Fraction.Rational) :
    (empiricalDistribution samples positiveLength).l1Distance left right =
      sumValues samples (fun item =>
        Distance.rationalSeparation (left item) (right item)) /
          (samples.length : Fraction.Rational) := by
  calc
    (empiricalDistribution samples positiveLength).l1Distance left right =
        (empiricalDistribution samples positiveLength).poweredLpDistance
          1 left right :=
      ((empiricalDistribution samples positiveLength)
        |>.poweredLpDistance_one left right).symm
    _ = sumValues samples (fun item =>
          Distance.rationalSeparation (left item) (right item) ^ 1) /
        (samples.length : Fraction.Rational) :=
      empiricalDistribution_poweredLpDistance samples positiveLength
        1 left right
    _ = sumValues samples (fun item =>
          Distance.rationalSeparation (left item) (right item)) /
        (samples.length : Fraction.Rational) :=
      congrArg (fun total => total / (samples.length : Fraction.Rational))
        (sumValues_congr samples _ _ (fun item => pow_one _))

/-- The empirical second moment equals the original sample's square sum divided by its length. -/
theorem empiricalDistribution_poweredL2 {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Fraction.Rational) :
    (empiricalDistribution samples positiveLength).poweredL2 value =
      sumValues samples (fun item => value item ^ 2) /
        (samples.length : Fraction.Rational) := by
  calc
    (empiricalDistribution samples positiveLength).poweredL2 value =
        (empiricalDistribution samples positiveLength).poweredLp 2 value :=
      ((empiricalDistribution samples positiveLength).poweredLp_two value).symm
    _ = sumValues samples (fun item =>
          Distance.rationalSeparation (value item) 0 ^ 2) /
        (samples.length : Fraction.Rational) :=
      empiricalDistribution_poweredLp samples positiveLength 2 value
    _ = sumValues samples (fun item => value item ^ 2) /
        (samples.length : Fraction.Rational) :=
      congrArg (fun total => total / (samples.length : Fraction.Rational))
        (sumValues_congr samples _ _ (fun item => by
          rw [Distance.NaturalLp.rationalSeparation_sq]
          ring1))

/-- The exact consolidated histogram preserves the original sample-average magnitude power. -/
theorem empiricalHistogram_poweredLp {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length)
    (exponent : Nat) (value : α → Fraction.Rational) :
    (empiricalHistogram samples positiveLength).poweredLp exponent value =
      sumValues samples (fun item =>
        Distance.rationalSeparation (value item) 0 ^ exponent) /
          (samples.length : Fraction.Rational) := by
  calc
    (empiricalHistogram samples positiveLength).poweredLp exponent value =
        (empiricalDistribution samples positiveLength).poweredLp
          exponent value :=
      Distribution.EvaluationEquivalent.poweredLp_eq
        (empiricalHistogram_evaluationEquivalent samples positiveLength)
        exponent value
    _ = _ := empiricalDistribution_poweredLp samples positiveLength
      exponent value

/-- The exact consolidated histogram preserves the original sample-average separation power. -/
theorem empiricalHistogram_poweredLpDistance
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length)
    (exponent : Nat) (left right : α → Fraction.Rational) :
    (empiricalHistogram samples positiveLength).poweredLpDistance
        exponent left right =
      sumValues samples (fun item =>
        Distance.rationalSeparation (left item) (right item) ^ exponent) /
          (samples.length : Fraction.Rational) := by
  calc
    (empiricalHistogram samples positiveLength).poweredLpDistance
        exponent left right =
      (empiricalDistribution samples positiveLength).poweredLpDistance
        exponent left right :=
      Distribution.EvaluationEquivalent.poweredLpDistance_eq
        (empiricalHistogram_evaluationEquivalent samples positiveLength)
        exponent left right
    _ = _ := empiricalDistribution_poweredLpDistance samples positiveLength
      exponent left right
end Purelib.Measure

end
