module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Moments of explicit finite product distributions

The product distribution is a displayed finite atom list.  Coordinate
expectations and variances therefore factor by exact rational arithmetic,
giving the usual zero covariance and variance-addition laws without any
abstract product measure.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- A left-coordinate observable's product expectation equals its original left-law expectation. -/
theorem product_expectation_left {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : α → Fraction.Rational) :
    (left.product right).expectation (fun pair => value pair.1) =
      left.expectation value := by
  calc
    (left.product right).expectation (fun pair => value pair.1) =
        left.expectation (fun leftItem =>
          right.expectation (fun _ => value leftItem)) :=
      left.product_expectation_iterated right _
    _ = left.expectation value :=
      left.expectation_congr _ _ (fun leftItem =>
        right.expectation_constant (value leftItem))

/-- A right-coordinate observable's product expectation equals its original right-law expectation. -/
theorem product_expectation_right {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : β → Fraction.Rational) :
    (left.product right).expectation (fun pair => value pair.2) =
      right.expectation value := by
  calc
    (left.product right).expectation (fun pair => value pair.2) =
        left.expectation (fun _ => right.expectation value) :=
      left.product_expectation_iterated right _
    _ = right.expectation value :=
      left.expectation_constant (right.expectation value)
end Distribution

end Purelib.Measure

end
