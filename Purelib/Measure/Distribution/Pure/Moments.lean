module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Explicit finite repeated sampling

An `iidSamples` table contains lists of exactly a supplied natural number of
draws from one displayed rational distribution.  The construction uses only
finite products and pushforwards.  Sample sums and means then have exact
rational expectation and variance formulas, giving a one-shot finite
Chebyshev estimate with the familiar reciprocal sample-count factor.

No infinite product, sequence of random variables, or asymptotic law is
constructed.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib.Data.Rat in
/-- Every observable has zero variance under a pure distribution. -/
theorem pure_variance {α : Type} (item : α)
    (value : α → Fraction.Rational) :
    (Distribution.pure item).variance value = 0 := by
  rw [(Distribution.pure item).variance_eq_secondMoment_sub_sq,
    Distribution.pure_expectation, Distribution.pure_expectation]
  ring1
end Distribution

end Purelib.Measure

end
