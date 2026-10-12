module
import Purelib.Data.Rat.Interval.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Enclosure.Basic
import Purelib.Measure.Distribution.Expectation

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
/-- The product-law interval enclosure equals successive enclosures under the original left and right laws. -/
theorem enclosedExpectation_product {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (ranges : α × β → Data.Rat.Interval) :
    (left.product right).enclosedExpectation ranges =
      left.enclosedExpectation (fun leftItem =>
        right.enclosedExpectation (fun rightItem =>
          ranges (leftItem, rightItem))) := by
  apply Interval.ext
  · rw [enclosedExpectation_lower, left.product_expectation_iterated,
      enclosedExpectation_lower]
    exact left.expectation_congr _ _ (fun item =>
      (right.enclosedExpectation_lower
        (fun rightItem => ranges (item, rightItem))).symm)
  · rw [enclosedExpectation_upper, left.product_expectation_iterated,
      enclosedExpectation_upper]
    exact left.expectation_congr _ _ (fun item =>
      (right.enclosedExpectation_upper
        (fun rightItem => ranges (item, rightItem))).symm)
end Distribution

end Purelib.Measure

end
