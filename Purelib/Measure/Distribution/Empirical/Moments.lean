module
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Empirical.Basic
public import Purelib.Measure.Distribution.Empirical.Operations
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Mixture.Basic
import Purelib.Measure.Sampling.Statistic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# Finite counting and empirical measures

A displayed sample list gives an exact rational counting content.  When its
length is explicitly positive, uniform normalization gives an exact empirical
distribution.  Probabilities are selected natural counts divided by the
displayed finite sample size.
-/

namespace Purelib.Measure

open Purelib.Data.Rat in
/-- Empirical variance equals the original sample mean of squared deviations from that empirical law's expectation. -/
theorem empiricalDistribution_variance_eq_sampleMean {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Fraction.Rational) :
    (empiricalDistribution samples positiveLength).variance value =
      Distribution.sampleMean samples.length
        (fun item =>
          (value item -
            (empiricalDistribution samples positiveLength).expectation value) ^ 2)
        samples := by
  unfold Distribution.variance Distribution.varianceAround
  exact empiricalDistribution_expectation_eq_sampleMean samples positiveLength _

open Purelib.Data.Rat in
open Purelib.Data.List in
/-- Variance of the exact appended sample splits into weighted component variances and a squared component-mean
difference.

The coefficients come from the two original sample lengths, and both component means and variances use those same
original empirical laws. -/
theorem empiricalDistribution_append_variance {α : Type}
    (left right : List α) (leftPositive : 0 < left.length)
    (rightPositive : 0 < right.length) (value : α → Fraction.Rational) :
    (empiricalDistribution (left ++ right) (by
        rewrite [Append.length_append]
        omega)).variance value =
      let weight := empiricalAppendWeight
        left right leftPositive rightPositive
      weight.coefficient *
          (empiricalDistribution left leftPositive).variance value +
        weight.complement *
          (empiricalDistribution right rightPositive).variance value +
        weight.coefficient * weight.complement *
          ((empiricalDistribution left leftPositive).expectation value -
            (empiricalDistribution right rightPositive).expectation value) ^ 2 := by
  let weight := empiricalAppendWeight left right leftPositive rightPositive
  have equivalent := empiricalDistribution_append_mixture
    left right leftPositive rightPositive
  calc
    (empiricalDistribution (left ++ right) (by
        rewrite [Append.length_append]
        omega)).variance value =
        ((empiricalDistribution left leftPositive).mixture
          (empiricalDistribution right rightPositive) weight).variance value :=
      equivalent.variance_eq value
    _ = weight.coefficient *
          (empiricalDistribution left leftPositive).variance value +
        weight.complement *
          (empiricalDistribution right rightPositive).variance value +
        weight.coefficient * weight.complement *
          ((empiricalDistribution left leftPositive).expectation value -
            (empiricalDistribution right rightPositive).expectation value) ^ 2 :=
      (empiricalDistribution left leftPositive).mixture_variance
        (empiricalDistribution right rightPositive) weight value

end Purelib.Measure

end
