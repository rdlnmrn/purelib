module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Counting
import Purelib.Measure.Content.Counting.EssentialMaximum
import Purelib.Measure.Content.Operations
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Distribution.Empirical.Basic
public import Purelib.Measure.Distribution.Empirical.Histogram
import Purelib.Measure.Distribution.EssentialMaximum.Equivalence
public import Purelib.Measure.Sampling.Maximum
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.Content.EssentialMaximum.Operations
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.EventAlgebra.Basic
import Mathlib.Order.Basic

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
/-- The empirical law's essential magnitude maximum is exactly the maximum computed on the original sample list. -/
theorem empiricalDistribution_essentialMaximumMagnitude {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Fraction.Rational) :
    Distribution.essentialMaximumMagnitude
        (empiricalDistribution samples positiveLength) value =
      sampleEssentialMaximumMagnitude value samples := by
  let factor : Fraction.Rational := 1 / (samples.length : Fraction.Rational)
  have lengthPositive : (0 : Fraction.Rational) < (samples.length : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct positiveLength
  have factorPositive : 0 < factor :=
    Fraction.Order.Field.div_pos_direct (by decide) lengthPositive
  have factorNonnegative : 0 ≤ factor := factorPositive.le
  change Content.essentialMaximumMagnitude
      ((countingContent samples).scale factor factorNonnegative) value =
        sampleEssentialMaximumMagnitude value samples
  rw [(countingContent samples).scale_essentialMaximumMagnitude_of_ne
    factor factorNonnegative factorPositive.ne' value]
  exact countingContent_essentialMaximumMagnitude samples value

/-- The empirical law's essential distance maximum is exactly the distance maximum computed on the original sample list.
-/
theorem empiricalDistribution_essentialMaximumDistance {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (left right : α → Fraction.Rational) :
    Distribution.essentialMaximumDistance
        (empiricalDistribution samples positiveLength) left right =
      sampleEssentialMaximumDistance left right samples := by
  unfold Distribution.essentialMaximumDistance
    Content.essentialMaximumDistance sampleEssentialMaximumDistance
  exact empiricalDistribution_essentialMaximumMagnitude
    samples positiveLength (fun item => left item - right item)

/-- Consolidating the empirical law preserves the original sample's exact essential magnitude maximum. -/
theorem empiricalHistogram_essentialMaximumMagnitude
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Fraction.Rational) :
    Distribution.essentialMaximumMagnitude
        (empiricalHistogram samples positiveLength) value =
      sampleEssentialMaximumMagnitude value samples := by
  calc
    Distribution.essentialMaximumMagnitude
          (empiricalHistogram samples positiveLength) value =
        Distribution.essentialMaximumMagnitude
          (empiricalDistribution samples positiveLength) value :=
      Distribution.EvaluationEquivalent.essentialMaximumMagnitude_eq
        (empiricalHistogram_evaluationEquivalent samples positiveLength)
        value
    _ = _ := empiricalDistribution_essentialMaximumMagnitude
      samples positiveLength value

/-- Consolidating the empirical law preserves the original sample's exact essential distance maximum. -/
theorem empiricalHistogram_essentialMaximumDistance
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length)
    (left right : α → Fraction.Rational) :
    Distribution.essentialMaximumDistance
        (empiricalHistogram samples positiveLength) left right =
      sampleEssentialMaximumDistance left right samples := by
  calc
    Distribution.essentialMaximumDistance
          (empiricalHistogram samples positiveLength) left right =
        Distribution.essentialMaximumDistance
          (empiricalDistribution samples positiveLength) left right :=
      Distribution.EvaluationEquivalent.essentialMaximumDistance_eq
        (empiricalHistogram_evaluationEquivalent samples positiveLength)
        left right
    _ = _ := empiricalDistribution_essentialMaximumDistance
      samples positiveLength left right

end Purelib.Measure

end
