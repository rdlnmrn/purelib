module
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Measure.Distribution.Enclosure.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
public import Purelib.Measure.Distribution.Kernel.Basic

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
open Purelib.Measure in
/-- A pure distribution's enclosed expectation is the original range at its sole payload. -/
theorem enclosedExpectation_pure {α : Type} (item : α)
    (ranges : α → Data.Rat.Interval) :
    (Distribution.pure item).enclosedExpectation ranges = ranges item := by
  apply Interval.ext
  · rw [Distribution.enclosedExpectation_lower, Distribution.pure_expectation]
  · rw [Distribution.enclosedExpectation_upper, Distribution.pure_expectation]
end Distribution

end Purelib.Measure

end
