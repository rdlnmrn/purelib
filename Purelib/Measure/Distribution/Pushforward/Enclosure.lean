module
import Purelib.Data.Rat.Interval.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Enclosure.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Content.Density.Aligned

section
@[expose] public section

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib in
open Purelib.Data.Rat in
/-- Enclosing ranges under the exact pushforward equals enclosing their pullback under the original distribution. -/
theorem enclosedExpectation_map {α β : Type}
    (source : Distribution α) (function : α → β) (ranges : β → Data.Rat.Interval) :
    (source.map function).enclosedExpectation ranges =
      source.enclosedExpectation (fun item => ranges (function item)) := by
  apply Interval.ext
  · rw [enclosedExpectation_lower, source.map_expectation,
      enclosedExpectation_lower]
  · rw [enclosedExpectation_upper, source.map_expectation,
      enclosedExpectation_upper]
end Distribution

end Purelib.Measure

end
