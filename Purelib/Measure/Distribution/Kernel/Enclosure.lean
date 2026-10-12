module
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Measure.Distribution.Enclosure.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Density.Aligned
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction

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
/-- Enclosing expectation after a kernel bind equals enclosing the exact transition expectations under the original
source law. -/
theorem enclosedExpectation_bind {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (ranges : β → Data.Rat.Interval) :
    (source.bind transition).enclosedExpectation ranges =
      source.enclosedExpectation (fun item =>
        (transition item).enclosedExpectation ranges) := by
  apply Interval.ext
  · rw [(source.bind transition).enclosedExpectation_lower,
      source.bind_expectation, source.enclosedExpectation_lower]
    exact source.expectation_congr _ _ (fun item =>
      ((transition item).enclosedExpectation_lower ranges).symm)
  · rw [(source.bind transition).enclosedExpectation_upper,
      source.bind_expectation, source.enclosedExpectation_upper]
    exact source.expectation_congr _ _ (fun item =>
      ((transition item).enclosedExpectation_upper ranges).symm)

open Purelib in
open Purelib.Measure in
/-- The bound width after a kernel bind equals the original expectation of its exact transition bound widths. -/
theorem enclosedExpectation_bind_width {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (ranges : β → Data.Rat.Interval) :
    ((source.bind transition).enclosedExpectation ranges).width =
      source.expectation (fun item =>
        ((transition item).enclosedExpectation ranges).width) := by
  rw [Distribution.enclosedExpectation_width, source.bind_expectation]
  exact source.expectation_congr _ _ (fun item =>
    ((transition item).enclosedExpectation_width ranges).symm)
end Distribution

end Purelib.Measure

end
