module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Partition.Interval
public import Purelib.Integration.Partition.Unit.Basic
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
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field

section
@[expose] public section

/-!
# Observed, cached exponential polynomial cells

Every cell retains its generated affine coefficient restriction and exact
integral sample.  The observations are actual later finite exponential
readings at displayed rational parameters; they are not evidence about an
unspecified integrand.  Endpoint observations make each generated list
nonempty, and the general constructor supports every displayed unit parameter.
-/

namespace Purelib.Integration.Partition.QuadraticWeight

section
open Purelib.Data.Rat
open Purelib.Integration.Partition
/-- The square of the retained interval's signed endpoint difference. -/
def intervalWeight (interval : Integration.Partition.Interval) :
  Fraction.Rational :=
  (interval.finish - interval.start) ^ 2

/-- Every squared interval weight is nonnegative. -/
theorem intervalWeight_nonnegative (interval :
  Integration.Partition.Interval) :
  0 ≤ intervalWeight interval :=
  Fraction.Order.Arithmetic.sq_nonneg_direct _

/-- Sum squared endpoint differences over the retained ordered interval occurrences. -/
def weightSum : List Integration.Partition.Interval →
  Fraction.Rational
  | [] => 0
  | interval :: tail => intervalWeight interval +
    weightSum tail

/-- Every finite list has nonnegative total squared interval weight. -/
theorem weightSum_nonnegative : ∀ intervals : List
  Integration.Partition.Interval, 0 ≤ weightSum intervals
  | [] => le_rfl
  | interval :: tail => by
      change 0 ≤ intervalWeight interval + weightSum tail
      calc
        0 = (0 : Fraction.Rational) + 0 := by decide
        _ ≤ intervalWeight interval + weightSum tail :=
          add_le_add (intervalWeight_nonnegative interval)
            (weightSum_nonnegative tail)

/-- Multiply the retained partition interval count by its exact sum of squared widths. -/
def amplification (partition :
  Integration.Partition.Unit.Normalized) :
  Fraction.Rational :=
  (partition.intervals.length : Fraction.Rational) * weightSum partition.intervals

/-- The exact partition amplification factor is nonnegative. -/
theorem amplification_nonnegative (partition :
  Integration.Partition.Unit.Normalized) : 0 ≤ amplification partition :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
    (weightSum_nonnegative partition.intervals)
end

end Purelib.Integration.Partition.QuadraticWeight

end
