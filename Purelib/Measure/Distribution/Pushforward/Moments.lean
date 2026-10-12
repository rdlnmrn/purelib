module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.Distribution.Moments.Basic

section
@[expose] public section

/-!
# Finite rational convolution

Convolution is the finite pushforward of an explicit product distribution by
rational addition.  Its event, expectation, and variance identities are
finite Fubini and independent-moment calculations.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat in
/-- An observable's variance under a pushforward equals its pullback variance under the exact original law. -/
theorem map_variance {α β : Type} (source : Distribution α)
    (function : α → β) (value : β → Fraction.Rational) :
    (source.map function).variance value =
      source.variance (fun item => value (function item)) := by
  rw [(source.map function).variance_eq_secondMoment_sub_sq,
    source.variance_eq_secondMoment_sub_sq,
    source.map_expectation function (fun item => value item ^ 2),
    source.map_expectation function value]
end Distribution

end Purelib.Measure

end
