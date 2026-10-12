module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Counting
public import Purelib.Measure.Sampling.Maximum
import Purelib.Measure.Weighted.Unit
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
public import Purelib.Measure.Content.EssentialMaximum.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.EssentialMaximum
import Purelib.Measure.EventAlgebra.Basic

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
/-- The essential maximum under exact sample counting content equals the finite sample magnitude maximum. -/
theorem countingContent_essentialMaximumMagnitude {α : Type}
    (samples : List α) (value : α → Fraction.Rational) :
    (countingContent samples).essentialMaximumMagnitude value =
      sampleEssentialMaximumMagnitude value samples := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      unfold countingContent Content.essentialMaximumMagnitude
      simp only [-eq_self, -iff_self, unitAtoms, essentialMaximumMagnitudeOn]
      have oneNonzero : (1 : Fraction.Rational) ≠ 0 := by decide
      rewrite [if_neg oneNonzero]
      change max (Distance.rationalSeparation (value item) 0)
          ((countingContent remaining).essentialMaximumMagnitude value) = _
      rw [inductionHypothesis]
      rfl

/-- The essential maximum distance under exact sample counting content equals the finite sample distance maximum. -/
theorem countingContent_essentialMaximumDistance {α : Type}
    (samples : List α) (left right : α → Fraction.Rational) :
    (countingContent samples).essentialMaximumDistance left right =
      sampleEssentialMaximumDistance left right samples := by
  unfold Content.essentialMaximumDistance
    sampleEssentialMaximumDistance
  exact countingContent_essentialMaximumMagnitude samples
    (fun item => left item - right item)
end Purelib.Measure

end
