module

import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.CauchyIndex.Endpoint
import Purelib.Data.Rat.Sign.ComplexProduct
import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Sign.Basic
import Purelib.Data.Sign.CauchyIndex.EventProduct
import Purelib.Data.Sign.CauchyIndex.Product
import Purelib.Data.Sign.ComplexProduct
import Purelib.Data.Sign.Stability
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Sign.CauchyIndex.Event
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained local Cauchy product events

The original finite-chain records retain their actual polynomial pairs and
interval. Exact endpoint multiplication equalities and formal sign certificates
identify their original three index readings with both endpoint corrections.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Event

open Purelib.Data.Rat
open _root_.Purelib.Data.Rat.Interval renaming Bounds -> RatInterval
open _root_.Purelib.Data renaming Sign -> FiniteSign
open Purelib.Polynomial.Dense.Rational.Basic renaming CoordinatePolynomial -> Dense
open Purelib.Polynomial.Dense.Rational.CauchyIndex
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Product

@[expose] public section

set_option genInjectivity false in
/-- Retain three finite Cauchy events with coordinated formal product signs.

The original polynomial pairs and interval index all three event records.
Imaginary coordinates are nonzero at both endpoints, and four retained scalar
equalities identify the product coordinates with complex multiplication. -/
structure LocalEventData
    (A B C D E H : Dense) (interval : RatInterval) where
  /-- The retained Cauchy event for the first factor. -/ left : Events.Signs.CauchyEventSigns A B interval
  /-- The retained Cauchy event for the second factor. -/ right : Events.Signs.CauchyEventSigns C D interval
  /-- The retained Cauchy event for the product. -/ product : Events.Signs.CauchyEventSigns E H interval
  /-- The retained formal center signs satisfy complex-product compatibility. -/ centersCompatible :
    FiniteSign.ComplexProductCompatible
    left.numerator left.denominator right.numerator right.denominator
    product.numerator product.denominator
  /-- The first factor imaginary coordinate is nonzero at the lower endpoint. -/ leftImagLower : B.eval interval.lower ≠
    0
  /-- The second factor imaginary coordinate is nonzero at the lower endpoint. -/ rightImagLower : D.eval interval.lower
    ≠ 0
  /-- The product imaginary coordinate is nonzero at the lower endpoint. -/ productImagLower : H.eval interval.lower ≠ 0
  /-- The first factor imaginary coordinate is nonzero at the upper endpoint. -/ leftImagUpper : B.eval interval.upper ≠
    0
  /-- The second factor imaginary coordinate is nonzero at the upper endpoint. -/ rightImagUpper : D.eval interval.upper
    ≠ 0
  /-- The product imaginary coordinate is nonzero at the upper endpoint. -/ productImagUpper : H.eval interval.upper ≠ 0
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

constructive_injectivity LocalEventData

end

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Event

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Event.LocalEventData

open Purelib.Data.Rat
open _root_.Purelib.Data.Rat.Interval renaming Bounds -> RatInterval
open _root_.Purelib.Data renaming Sign -> FiniteSign
open Purelib.Polynomial.Dense.Rational.Basic renaming CoordinatePolynomial -> Dense
open Purelib.Polynomial.Dense.Rational.CauchyIndex
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Product

/-- Re-center three original Cauchy events at admissible retained factor signs.

The supplied centers are nonzero and stable against the same actual endpoint
observations. The displayed product choices and scalar multiplication identities
retain all three input events, their polynomial owners and interval bounds. -/
@[expose] public def ofRecenteredFactors
    {A B C D E H : Dense} {interval : RatInterval}
    (leftBase : Events.Signs.CauchyEventSigns A B interval)
    (rightBase : Events.Signs.CauchyEventSigns C D interval)
    (productBase : Events.Signs.CauchyEventSigns E H interval)
    (factorLeftReal factorLeftImag factorRightReal factorRightImag :
      Data.Sign)
    (leftCenter : FiniteSign.EventCenterAdmissible
      factorLeftReal factorLeftImag
      (FiniteSign.ofCoordinate (A.eval interval.lower))
      (FiniteSign.ofCoordinate (B.eval interval.lower))
      (FiniteSign.ofCoordinate (A.eval interval.upper))
      (FiniteSign.ofCoordinate (B.eval interval.upper)))
    (rightCenter : FiniteSign.EventCenterAdmissible
      factorRightReal factorRightImag
      (FiniteSign.ofCoordinate (C.eval interval.lower))
      (FiniteSign.ofCoordinate (D.eval interval.lower))
      (FiniteSign.ofCoordinate (C.eval interval.upper))
      (FiniteSign.ofCoordinate (D.eval interval.upper)))
    (productCenter : FiniteSign.EventCenterAdmissible
      (FiniteSign.productRealChoice factorLeftReal factorLeftImag
        factorRightReal factorRightImag)
      (FiniteSign.productImagChoice factorLeftReal factorLeftImag
        factorRightReal factorRightImag)
      (FiniteSign.ofCoordinate (E.eval interval.lower))
      (FiniteSign.ofCoordinate (H.eval interval.lower))
      (FiniteSign.ofCoordinate (E.eval interval.upper))
      (FiniteSign.ofCoordinate (H.eval interval.upper)))
    (leftImagLower : B.eval interval.lower ≠ 0)
    (rightImagLower : D.eval interval.lower ≠ 0)
    (productImagLower : H.eval interval.lower ≠ 0)
    (leftImagUpper : B.eval interval.upper ≠ 0)
    (rightImagUpper : D.eval interval.upper ≠ 0)
    (productImagUpper : H.eval interval.upper ≠ 0)
    (productRealLowerEq : E.eval interval.lower =
      A.eval interval.lower * C.eval interval.lower -
        B.eval interval.lower * D.eval interval.lower)
    (productImagLowerEq : H.eval interval.lower =
      A.eval interval.lower * D.eval interval.lower +
        B.eval interval.lower * C.eval interval.lower)
    (productRealUpperEq : E.eval interval.upper =
      A.eval interval.upper * C.eval interval.upper -
        B.eval interval.upper * D.eval interval.upper)
    (productImagUpperEq : H.eval interval.upper =
      A.eval interval.upper * D.eval interval.upper +
        B.eval interval.upper * C.eval interval.upper) :
    LocalEventData A B C D E H interval := by
  let left := leftBase.recenter
    factorLeftReal factorLeftImag leftCenter.1
    leftCenter.2.1 leftCenter.2.2.1
    leftCenter.2.2.2.1 leftCenter.2.2.2.2
  let right := rightBase.recenter
    factorRightReal factorRightImag rightCenter.1
    rightCenter.2.1 rightCenter.2.2.1
    rightCenter.2.2.2.1 rightCenter.2.2.2.2
  let product := productBase.recenter
    (FiniteSign.productRealChoice factorLeftReal factorLeftImag
      factorRightReal factorRightImag)
    (FiniteSign.productImagChoice factorLeftReal factorLeftImag
      factorRightReal factorRightImag)
    productCenter.1 productCenter.2.1 productCenter.2.2.1
    productCenter.2.2.2.1 productCenter.2.2.2.2
  exact
    { left := left
      right := right
      product := product
      centersCompatible := by
        simpa only [left, right, product, Events.Signs.CauchyEventSigns.recenter] using
          FiniteSign.productChoices_compatible
            factorLeftReal factorLeftImag factorRightReal factorRightImag
      leftImagLower := leftImagLower
      rightImagLower := rightImagLower
      productImagLower := productImagLower
      leftImagUpper := leftImagUpper
      rightImagUpper := rightImagUpper
      productImagUpper := productImagUpper
      productRealLowerEq := productRealLowerEq
      productImagLowerEq := productImagLowerEq
      productRealUpperEq := productRealUpperEq
      productImagUpperEq := productImagUpperEq }

/-- The retained lower-endpoint signs satisfy local product admissibility.

Original nonzero imaginary-coordinate certificates give nonzero formal signs.
The three retained event records supply stability, and the exact product
coordinate equalities supply compatibility at that same lower endpoint. -/
private theorem lowerAdmissible
    {A B C D E H : Dense} {interval : RatInterval}
    (data : LocalEventData A B C D E H interval) :
    FiniteSign.LocalProductAdmissible
      data.left.numerator data.left.denominator
      data.right.numerator data.right.denominator
      data.product.numerator data.product.denominator
      (FiniteSign.ofCoordinate (A.eval interval.lower))
      (FiniteSign.ofCoordinate (B.eval interval.lower))
      (FiniteSign.ofCoordinate (C.eval interval.lower))
      (FiniteSign.ofCoordinate (D.eval interval.lower))
      (FiniteSign.ofCoordinate (E.eval interval.lower))
      (FiniteSign.ofCoordinate (H.eval interval.lower)) := by
  refine ⟨data.left.nonzero, data.right.nonzero, ?_, ?_, ?_,
    data.left.numeratorLowerStable, data.left.denominatorLowerStable,
    data.right.numeratorLowerStable, data.right.denominatorLowerStable,
    data.product.numeratorLowerStable, data.product.denominatorLowerStable,
    data.centersCompatible, ?_⟩
  · exact FiniteSign.ofCoordinate_ne_zero_iff.mpr data.leftImagLower
  · exact FiniteSign.ofCoordinate_ne_zero_iff.mpr data.rightImagLower
  · exact FiniteSign.ofCoordinate_ne_zero_iff.mpr data.productImagLower
  · rw [data.productRealLowerEq, data.productImagLowerEq]
    exact Sign.ComplexProduct.sign_complexProductCompatible
      (A.eval interval.lower) (B.eval interval.lower)
      (C.eval interval.lower) (D.eval interval.lower)

/-- The retained upper-endpoint signs satisfy local product admissibility.

Original nonzero imaginary-coordinate certificates give nonzero formal signs.
The three retained event records supply stability, and the exact product
coordinate equalities supply compatibility at that same upper endpoint. -/
private theorem upperAdmissible
    {A B C D E H : Dense} {interval : RatInterval}
    (data : LocalEventData A B C D E H interval) :
    FiniteSign.LocalProductAdmissible
      data.left.numerator data.left.denominator
      data.right.numerator data.right.denominator
      data.product.numerator data.product.denominator
      (FiniteSign.ofCoordinate (A.eval interval.upper))
      (FiniteSign.ofCoordinate (B.eval interval.upper))
      (FiniteSign.ofCoordinate (C.eval interval.upper))
      (FiniteSign.ofCoordinate (D.eval interval.upper))
      (FiniteSign.ofCoordinate (E.eval interval.upper))
      (FiniteSign.ofCoordinate (H.eval interval.upper)) := by
  refine ⟨data.left.nonzero, data.right.nonzero, ?_, ?_, ?_,
    data.left.numeratorUpperStable, data.left.denominatorUpperStable,
    data.right.numeratorUpperStable, data.right.denominatorUpperStable,
    data.product.numeratorUpperStable, data.product.denominatorUpperStable,
    data.centersCompatible, ?_⟩
  · exact FiniteSign.ofCoordinate_ne_zero_iff.mpr data.leftImagUpper
  · exact FiniteSign.ofCoordinate_ne_zero_iff.mpr data.rightImagUpper
  · exact FiniteSign.ofCoordinate_ne_zero_iff.mpr data.productImagUpper
  · rw [data.productRealUpperEq, data.productImagUpperEq]
    exact Sign.ComplexProduct.sign_complexProductCompatible
      (A.eval interval.upper) (B.eval interval.upper)
      (C.eval interval.upper) (D.eval interval.upper)

/-- The retained finite event records satisfy the auxiliary product formula.

Both endpoint readings use the original interval and polynomial pairs. Their
finite sign identity and exact scalar product equalities retain the two
correction terms and the three original doubled Cauchy indices. -/
public theorem auxiliaryProductFormula
    {A B C D E H : Dense} {interval : RatInterval}
    (data : LocalEventData A B C D E H interval) :
    Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have table := FiniteSign.localProductEventTable
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
    data.lowerAdmissible data.upperAdmissible
  unfold FiniteSign.LocalEventProductIdentity at table
  rw [Sign.CauchyIndex.Endpoint.sign_productCorrection2_ofCoordinate,
    Sign.CauchyIndex.Endpoint.sign_productCorrection2_ofCoordinate] at table
  unfold Basic.AuxiliaryProductFormula Basic.auxiliaryEndpointCorrection2
  rw [data.left.index, data.right.index, data.product.index]
  exact table

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Event.LocalEventData
