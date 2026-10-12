module
import Purelib.Data.Rat.Interval.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Mixture.Basic
public import Purelib.Measure.Distribution.Enclosure.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
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
/-- A mixture's enclosed expectation is the sum of the original enclosures scaled by their retained mixing coefficients.
-/
theorem enclosedExpectation_mixture {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (ranges : α → Data.Rat.Interval) :
    (left.mixture right weight).enclosedExpectation ranges =
      ((left.enclosedExpectation ranges).scale
        weight.coefficient weight.nonnegative).add
      ((right.enclosedExpectation ranges).scale
        weight.complement weight.complement_nonnegative) := by
  apply Interval.ext
  · rw [enclosedExpectation_lower,
      left.mixture_expectation right weight]
    change weight.coefficient * left.expectation (fun item =>
        (ranges item).lower) +
      weight.complement * right.expectation (fun item =>
        (ranges item).lower) =
      weight.coefficient * (left.enclosedExpectation ranges).lower +
        weight.complement * (right.enclosedExpectation ranges).lower
    rw [left.enclosedExpectation_lower, right.enclosedExpectation_lower]
  · rw [enclosedExpectation_upper,
      left.mixture_expectation right weight]
    change weight.coefficient * left.expectation (fun item =>
        (ranges item).upper) +
      weight.complement * right.expectation (fun item =>
        (ranges item).upper) =
      weight.coefficient * (left.enclosedExpectation ranges).upper +
        weight.complement * (right.enclosedExpectation ranges).upper
    rw [left.enclosedExpectation_upper, right.enclosedExpectation_upper]

open Purelib in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- A mixture's enclosed-expectation width is the corresponding weighted sum of the original widths. -/
theorem enclosedExpectation_mixture_width {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (ranges : α → Data.Rat.Interval) :
    ((left.mixture right weight).enclosedExpectation ranges).width =
      weight.coefficient * (left.enclosedExpectation ranges).width +
        weight.complement * (right.enclosedExpectation ranges).width := by
  rw [Distribution.enclosedExpectation_mixture, Interval.add_width,
    Interval.scale_width, Interval.scale_width]
end Distribution

end Purelib.Measure

end
