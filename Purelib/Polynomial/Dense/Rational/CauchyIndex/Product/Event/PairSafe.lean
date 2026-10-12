module

import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.CauchyIndex.Endpoint
import Purelib.Data.Rat.Sign.ComplexProduct
import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Sign.CauchyIndex.EventProduct
import Purelib.Data.Sign.ComplexProduct
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained pair-safe local product events

The original finite-chain records retain their actual polynomial pairs and
interval. Exact endpoint multiplication equalities and formal sign certificates
identify their original three index readings with both endpoint corrections.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Event.PairSafe

open Purelib.Data.Rat
open _root_.Purelib.Data.Rat.Interval renaming Bounds -> RatInterval
open _root_.Purelib.Data renaming Sign -> FiniteSign
open Purelib.Polynomial.Dense.Rational.Basic renaming CoordinatePolynomial -> Dense
open Purelib.Polynomial.Dense.Rational.CauchyIndex
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Product

@[expose] public section

set_option genInjectivity false in
/-- Retain three finite Cauchy events with nonzero factor pairs at both endpoints.

Each endpoint has a nonzero coordinate in each factor pair. Individual displayed
coordinates may vanish identically. Four retained scalar equalities identify
the product coordinates with complex multiplication at the same endpoints. -/
structure PairSafeLocalEventData
    (A B C D E H : Dense) (interval : RatInterval) where
  /-- The retained Cauchy event for the first factor. -/ left : Events.Signs.CauchyEventSigns A B interval
  /-- The retained Cauchy event for the second factor. -/ right : Events.Signs.CauchyEventSigns C D interval
  /-- The retained Cauchy event for the product. -/ product : Events.Signs.CauchyEventSigns E H interval
  /-- The retained formal center signs satisfy complex-product compatibility. -/ centersCompatible :
    FiniteSign.ComplexProductCompatible
    left.numerator left.denominator right.numerator right.denominator
    product.numerator product.denominator
  /-- At least one coordinate of the first factor is nonzero at the lower endpoint. -/ factorLeftLower : A.eval
    interval.lower ≠ 0 ∨
    B.eval interval.lower ≠ 0
  /-- At least one coordinate of the second factor is nonzero at the lower endpoint. -/ factorRightLower : C.eval
    interval.lower ≠ 0 ∨
    D.eval interval.lower ≠ 0
  /-- At least one coordinate of the first factor is nonzero at the upper endpoint. -/ factorLeftUpper : A.eval
    interval.upper ≠ 0 ∨
    B.eval interval.upper ≠ 0
  /-- At least one coordinate of the second factor is nonzero at the upper endpoint. -/ factorRightUpper : C.eval
    interval.upper ≠ 0 ∨
    D.eval interval.upper ≠ 0
  /-- The product real coordinate obeys complex multiplication at the lower endpoint. -/ productRealLowerEq : E.eval
    interval.lower =
    A.eval interval.lower * C.eval interval.lower -
      B.eval interval.lower * D.eval interval.lower
  /-- The product imaginary coordinate obeys complex multiplication at the lower endpoint. -/ productImagLowerEq :
    H.eval interval.lower =
    A.eval interval.lower * D.eval interval.lower +
      B.eval interval.lower * C.eval interval.lower
  /-- The product real coordinate obeys complex multiplication at the upper endpoint. -/ productRealUpperEq : E.eval
    interval.upper =
    A.eval interval.upper * C.eval interval.upper -
      B.eval interval.upper * D.eval interval.upper
  /-- The product imaginary coordinate obeys complex multiplication at the upper endpoint. -/ productImagUpperEq :
    H.eval interval.upper =
    A.eval interval.upper * D.eval interval.upper +
      B.eval interval.upper * C.eval interval.upper

constructive_injectivity PairSafeLocalEventData

end

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Event.PairSafe

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Event.PairSafe.PairSafeLocalEventData

open Purelib.Data.Rat
open _root_.Purelib.Data.Rat.Interval renaming Bounds -> RatInterval
open _root_.Purelib.Data renaming Sign -> FiniteSign
open Purelib.Polynomial.Dense.Rational.Basic renaming CoordinatePolynomial -> Dense
open Purelib.Polynomial.Dense.Rational.CauchyIndex
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Product

/-- The retained finite event records satisfy the auxiliary product formula.

Both endpoint readings use the original interval and polynomial pairs. Their
finite sign identity and exact scalar product equalities retain the two
correction terms and the three original doubled Cauchy indices. -/
public theorem auxiliaryProductFormula
    {A B C D E H : Dense} {interval : RatInterval}
    (data : PairSafeLocalEventData A B C D E H interval) :
    Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have table := FiniteSign.localProductEventTable_of_endpoint_pairs_nonzero
    data.left.numerator data.left.denominator
    data.right.numerator data.right.denominator
    data.product.numerator data.product.denominator
    (FiniteSign.ofCoordinate (A.eval interval.lower))
    (FiniteSign.ofCoordinate (B.eval interval.lower))
    (FiniteSign.ofCoordinate (C.eval interval.lower))
    (FiniteSign.ofCoordinate (D.eval interval.lower))
    (FiniteSign.ofCoordinate (E.eval interval.lower))
    (FiniteSign.ofCoordinate (H.eval interval.lower))
    (FiniteSign.ofCoordinate (A.eval interval.upper))
    (FiniteSign.ofCoordinate (B.eval interval.upper))
    (FiniteSign.ofCoordinate (C.eval interval.upper))
    (FiniteSign.ofCoordinate (D.eval interval.upper))
    (FiniteSign.ofCoordinate (E.eval interval.upper))
    (FiniteSign.ofCoordinate (H.eval interval.upper))
    data.left.nonzero data.right.nonzero
    (by
      rcases data.factorLeftLower with realNonzero | imaginaryNonzero
      · exact Or.inl (FiniteSign.ofCoordinate_ne_zero_iff.mpr realNonzero)
      · exact Or.inr (FiniteSign.ofCoordinate_ne_zero_iff.mpr imaginaryNonzero))
    (by
      rcases data.factorRightLower with realNonzero | imaginaryNonzero
      · exact Or.inl (FiniteSign.ofCoordinate_ne_zero_iff.mpr realNonzero)
      · exact Or.inr (FiniteSign.ofCoordinate_ne_zero_iff.mpr imaginaryNonzero))
    (by
      rcases data.factorLeftUpper with realNonzero | imaginaryNonzero
      · exact Or.inl (FiniteSign.ofCoordinate_ne_zero_iff.mpr realNonzero)
      · exact Or.inr (FiniteSign.ofCoordinate_ne_zero_iff.mpr imaginaryNonzero))
    (by
      rcases data.factorRightUpper with realNonzero | imaginaryNonzero
      · exact Or.inl (FiniteSign.ofCoordinate_ne_zero_iff.mpr realNonzero)
      · exact Or.inr (FiniteSign.ofCoordinate_ne_zero_iff.mpr imaginaryNonzero))
    data.left.numeratorLowerStable data.left.denominatorLowerStable
    data.right.numeratorLowerStable data.right.denominatorLowerStable
    data.product.numeratorLowerStable data.product.denominatorLowerStable
    data.left.numeratorUpperStable data.left.denominatorUpperStable
    data.right.numeratorUpperStable data.right.denominatorUpperStable
    data.product.numeratorUpperStable data.product.denominatorUpperStable
    data.centersCompatible
    (by
      rw [data.productRealLowerEq, data.productImagLowerEq]
      exact Sign.ComplexProduct.sign_complexProductCompatible
        (A.eval interval.lower) (B.eval interval.lower)
        (C.eval interval.lower) (D.eval interval.lower))
    (by
      rw [data.productRealUpperEq, data.productImagUpperEq]
      exact Sign.ComplexProduct.sign_complexProductCompatible
        (A.eval interval.upper) (B.eval interval.upper)
        (C.eval interval.upper) (D.eval interval.upper))
  unfold FiniteSign.LocalEventProductIdentity at table
  rw [Sign.CauchyIndex.Endpoint.sign_productCorrection2_ofCoordinate,
    Sign.CauchyIndex.Endpoint.sign_productCorrection2_ofCoordinate] at table
  unfold Basic.AuxiliaryProductFormula Basic.auxiliaryEndpointCorrection2
  rw [data.left.index, data.right.index, data.product.index]
  exact table

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Event.PairSafe.PairSafeLocalEventData
