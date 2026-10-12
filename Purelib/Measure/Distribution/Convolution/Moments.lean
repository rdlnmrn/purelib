module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Data.Rat.Fraction

public import Purelib.Measure.Distribution.Convolution.Basic
import Purelib.Measure.Distribution.Product.Expectation
import Purelib.Measure.Distribution.Product.Moments
import Purelib.Measure.Distribution.Pushforward.Moments
import Purelib.Data.Rat.Fraction.Arithmetic

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

open Purelib.Data.Rat
/-- The coordinate expectation of the exact convolution is the sum of the two original coordinate expectations. -/
theorem convolve_expectation (left right : Distribution Fraction.Rational) :
    (left.convolve right).expectation (fun value => value) =
      left.expectation (fun value => value) +
        right.expectation (fun value => value) := by
  rw [convolve, map_expectation]
  change (left.product right).expectation
      (fun pair => pair.1 + pair.2) = _
  rw [(left.product right).expectation_add]
  exact congrArg₂ (fun leftMean rightMean => leftMean + rightMean)
    (left.product_expectation_left right (fun value => value))
    (left.product_expectation_right right (fun value => value))

/-- The coordinate variance of the exact convolution is the sum of the two original coordinate variances. -/
theorem convolve_variance (left right : Distribution Fraction.Rational) :
    (left.convolve right).variance (fun value => value) =
      left.variance (fun value => value) +
        right.variance (fun value => value) := by
  rw [convolve, map_variance]
  exact left.product_variance_add_coordinates right
    (fun value => value) (fun value => value)

end Distribution

end Purelib.Measure

end
