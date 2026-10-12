module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Resolution
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Degenerate product width thresholds

The original local resolution radius square and its cap by one retain the
factor clearances and coordinate identities of each degenerate product cell.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Bounds

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Product

/-- The width threshold capped by one and the degenerate cell resolution radius square.

The same local product resolution radius square is capped by one. A
strict width bound then supplies a squared-radius bound for the original
factor clearances and real and imaginary product identities. -/
@[expose] public def degenerateProductLeafWidth
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root) (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) : Fraction.Rational :=
  min 1 (Resolution.localProductResolutionRadiusSq left right
    realIdentity imagIdentity)

/-- The degenerate product leaf-width threshold is strictly positive.

The supplied factor clearances and product identities certify the same
local product resolution radius square as positive. Its original rational
minimum with one retains a strictly positive width threshold. -/
public theorem degenerateProductLeafWidth_pos
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root) (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    0 < degenerateProductLeafWidth left right
      realIdentity imagIdentity :=
  Fraction.Order.Basic.lt_min (by decide)
    (Resolution.localProductResolutionRadiusSq_pos left right
      realIdentity imagIdentity)

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Bounds
