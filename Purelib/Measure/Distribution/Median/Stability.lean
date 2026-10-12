module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Quantile.Stability
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
public import Purelib.Measure.Distribution.Median.Basic
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Quantile.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic

section
@[expose] public section

/-!
# Uniform stability of constructive finite quantiles

Finite lower quantiles are stable under a displayed uniform rational
perturbation of the source observable.  The proof compares the two executable
cumulative events atom by atom and applies the exact finite generalized-inverse
law.  No infimum, limiting distribution, or completed metric space occurs.
-/

namespace Purelib.Measure

namespace Distribution
namespace EvaluationEquivalent
end EvaluationEquivalent

open Purelib in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Occurrence-wise closeness of two observables bounds separation of their exact pushforward lower medians by the same
radius. -/
theorem map_median_rationalSeparation_le {α : Type}
    (source : Measure.Distribution α) (left right : α → Fraction.Rational)
    (radius : Fraction.Rational)
    (close : ∀ atom, atom ∈ source.atoms →
      Distance.rationalSeparation (left atom.item) (right atom.item) ≤ radius) :
    Distance.rationalSeparation (source.map left).median (source.map right).median ≤
      radius := by
  simpa only [Distribution.median] using
    source.map_lowerQuantile_rationalSeparation_le left right radius close
      (1 / 2) (by decide) (by decide)

end Distribution

end Purelib.Measure

end
