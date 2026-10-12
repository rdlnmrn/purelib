module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Endpoint.Resolution
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Resolution
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Common product partition thresholds

The same factor clearances and product coordinate identities retain the
interior and endpoint radii, their common squared-radius cap, and the width cap.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Partition.Bounds

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Product

/-- The common squared-radius threshold for interior and both outer endpoint leaves.

The exact nested minimum retains the interior resolution radius and the
two endpoint radii at the original interval endpoints. Both factor
clearances and the real and imaginary product identities are unchanged. -/
@[expose] public def completeProductResolutionRadiusSq
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) : Fraction.Rational :=
  min (Resolution.localProductResolutionRadiusSq left right realIdentity imagIdentity)
    (min
      (Endpoint.Resolution.endpointProductResolutionRadiusSq left right realIdentity imagIdentity
        root.lower)
      (Endpoint.Resolution.endpointProductResolutionRadiusSq left right realIdentity imagIdentity
        root.upper))

/-- The common product resolution radius square is strictly positive.

The supplied factor clearances certify the original interior and two
endpoint radii as positive. Direct rational minimum positivity certifies
the same common threshold without changing any retained radius. -/
public theorem completeProductResolutionRadiusSq_pos
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    0 < completeProductResolutionRadiusSq left right
      realIdentity imagIdentity := by
  unfold completeProductResolutionRadiusSq
  exact Fraction.Order.Basic.lt_min
    (Resolution.localProductResolutionRadiusSq_pos left right realIdentity imagIdentity)
    (Fraction.Order.Basic.lt_min
      (Endpoint.Resolution.endpointProductResolutionRadiusSq_pos left right
        realIdentity imagIdentity root.lower)
      (Endpoint.Resolution.endpointProductResolutionRadiusSq_pos left right
        realIdentity imagIdentity root.upper))

/-- The width threshold capped by one and the common product radius square.

The original common radius square is capped by one using the same rational
minimum. A strictly smaller positive interval width is therefore below
one and gives the required strict squared-width bound. -/
@[expose] public def completeProductLeafWidth
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) : Fraction.Rational :=
  min 1 (completeProductResolutionRadiusSq left right
    realIdentity imagIdentity)

/-- The complete product leaf-width threshold is strictly positive.

The original common radius square is positive for the supplied factor
clearances and product identities. Its retained minimum with one is
positive under the same original rational comparison operation. -/
public theorem completeProductLeafWidth_pos
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    0 < completeProductLeafWidth left right realIdentity imagIdentity :=
  Fraction.Order.Basic.lt_min (by decide)
    (completeProductResolutionRadiusSq_pos left right
      realIdentity imagIdentity)

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Partition.Bounds
