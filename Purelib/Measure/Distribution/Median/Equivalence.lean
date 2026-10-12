module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Quantile.Equivalence
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
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

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

open Purelib in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Evaluation-equivalent original rational laws have equal computed lower medians. -/
theorem median_eq
    {left right : Measure.Distribution Fraction.Rational}
    (equivalent : EvaluationEquivalent left right) :
    left.median = right.median := by
  simpa only [Distribution.median] using
    equivalent.lowerQuantile_eq (1 / 2) (by decide) (by decide)

end EvaluationEquivalent
end Distribution

end Purelib.Measure

end
