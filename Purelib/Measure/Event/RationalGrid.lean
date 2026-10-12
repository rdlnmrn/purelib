module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Event.RationalOrder
import Purelib.Data.Rat.Fraction

section
/-!
# Simultaneous finite event-frequency sampling

One explicit finite iid sample can estimate every event probability in a
displayed finite event list.  The requested failure budget is split over
`events.length + 1`, each event uses the uniform Bernoulli variance bound, and
finite subadditivity controls the union of all deviation events.

This is the finite constructive core of a uniform empirical-frequency bound;
there is no infinite event class, supremum, or asymptotic empirical process.
-/

@[expose] public section

namespace Purelib.Measure

section Distribution

/-! ## Finite empirical cumulative grids -/

open Purelib.Data.Rat in
/-- Map the exact threshold list to rational lower-tail events, retaining its order and repeated thresholds. -/
def cumulativeEventGrid (thresholds : List Fraction.Rational) :
    List (Fraction.Rational → Bool) :=
  thresholds.map atMostEvent
end Distribution

end Purelib.Measure

end
