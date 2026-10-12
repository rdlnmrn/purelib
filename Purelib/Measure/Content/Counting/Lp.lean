module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.Content.Counting
import Purelib.Measure.Sampling.Statistic
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
public import Purelib.Measure.Content.Lp.Natural
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

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
/-- A powered magnitude integral under exact sample counting content is the corresponding finite sample-value sum. -/
theorem countingContent_poweredLp {α : Type} (samples : List α)
    (exponent : Nat) (value : α → Fraction.Rational) :
    (countingContent samples).poweredLp exponent value =
      sumValues samples (fun item =>
        Distance.rationalSeparation (value item) 0 ^ exponent) :=
  countingContent_integral samples _

/-- A powered distance integral under exact sample counting content is the corresponding finite sample separation sum.
-/
theorem countingContent_poweredLpDistance {α : Type}
    (samples : List α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    (countingContent samples).poweredLpDistance exponent left right =
      sumValues samples (fun item =>
        Distance.rationalSeparation (left item) (right item) ^ exponent) :=
  countingContent_integral samples _
end Purelib.Measure

end
