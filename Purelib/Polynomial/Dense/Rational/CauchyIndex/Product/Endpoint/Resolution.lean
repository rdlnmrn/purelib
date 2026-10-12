module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Product
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Endpoint
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Endpoint.Bounds
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius
import Purelib.Data.Rat.Interval.Radius
public import Purelib.Polynomial.Clearance.Pair.Product
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Pair.Operations
import Purelib.Polynomial.Dense.Evaluation

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Endpoint.Resolution

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational

/-- One positive squared radius covers the three event scanners and the six
component stabilities needed at a possibly axis-aligned outer endpoint.

The original product clearance combines the two supplied factor certificates.
Three swapped signed-chain bounds and the six-coordinate endpoint threshold
are retained in the same displayed nested rational minimum. -/
@[expose] public def endpointProductResolutionRadiusSq
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (endpoint : Fraction.Rational) : Fraction.Rational :=
  let product := Clearance.Pair.Basic.Certificate.complexProduct left right realIdentity imagIdentity
  min (SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq B A left.swap)
    (min (SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq D C right.swap)
      (min (SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq H E product.swap)
        (CauchyIndex.Product.Endpoint.Bounds.endpointStabilitiesRadiusSq A B C D E H root endpoint)))

/-- The combined endpoint product resolution radius is strictly positive.

Each of the three signed-chain thresholds and the endpoint stability threshold is positive for the retained clearance
certificates. -/
public theorem endpointProductResolutionRadiusSq_pos
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (endpoint : Fraction.Rational) :
    0 < endpointProductResolutionRadiusSq left right
      realIdentity imagIdentity endpoint := by
  let product := Clearance.Pair.Basic.Certificate.complexProduct left right realIdentity imagIdentity
  unfold endpointProductResolutionRadiusSq
  apply Fraction.Order.Basic.lt_min
  · exact SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_pos B A left.swap
  · apply Fraction.Order.Basic.lt_min
    · exact SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_pos D C right.swap
    · apply Fraction.Order.Basic.lt_min
      · exact SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_pos H E product.swap
      · exact CauchyIndex.Product.Endpoint.Bounds.endpointStabilitiesRadiusSq_pos A B C D E H root endpoint

/-- A refined left-endpoint cell satisfies the doubled auxiliary Cauchy-product formula.

Both factor pairs may meet coordinate axes at the starting endpoint, while
the three stopping denominator values are nonzero. The retained scanner
records and six oriented endpoint stabilities provide the displayed formula. -/
public theorem auxiliaryProductFormula_of_leftEndpoint_refined_radiusSq
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      endpointProductResolutionRadiusSq left right
        realIdentity imagIdentity interval.lower)
    (leftStart : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightStart : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftImagStop : B.eval interval.upper ≠ 0)
    (rightImagStop : D.eval interval.upper ≠ 0)
    (productImagStop : H.eval interval.upper ≠ 0) :
    CauchyIndex.Product.Basic.AuxiliaryProductFormula
      A B C D E H interval.lower interval.upper := by
  let product := Clearance.Pair.Basic.Certificate.complexProduct left right realIdentity imagIdentity
  have leftRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq B A left.swap :=
    radius.trans_le (Fraction.Order.Basic.min_le_left _ _)
  have rightRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq D C right.swap :=
    radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
  have productRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq H E product.swap :=
    radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))
  have stabilityRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      CauchyIndex.Product.Endpoint.Bounds.endpointStabilitiesRadiusSq A B C D E H root interval.lower :=
    radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans (le_refl _))))
  let leftEvent := CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq
    left.swap refines leftRadius
  let rightEvent := CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq
    right.swap refines rightRadius
  let productEvent := CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq
    product.swap refines productRadius
  have stabilities := CauchyIndex.Product.Endpoint.Bounds.endpointStabilities_of_refined_radiusSq refines
    (Or.inl ⟨rfl, rfl⟩) stabilityRadius
  have productStart : E.eval interval.lower ≠ 0 ∨
      H.eval interval.lower ≠ 0 :=
    Gaussian.Components.Product.complexProductPair_ne_zero
      (A.eval interval.lower) (B.eval interval.lower)
      (C.eval interval.lower) (D.eval interval.lower)
      (E.eval interval.lower) (H.eval interval.lower)
      leftStart rightStart (realIdentity interval.lower)
      (imagIdentity interval.lower)
  apply CauchyIndex.Product.Endpoint.auxiliaryProductFormula_of_localEndpointData
  exact
    { leftIndex := leftEvent.index_eq_leftEndpointIndex2
        leftStart stabilities.leftReal stabilities.leftImag
      rightIndex := rightEvent.index_eq_leftEndpointIndex2
        rightStart stabilities.rightReal stabilities.rightImag
      productIndex := productEvent.index_eq_leftEndpointIndex2
        productStart stabilities.productReal stabilities.productImag
      factorLeftStart := leftStart
      factorRightStart := rightStart
      leftImagStop := leftImagStop
      rightImagStop := rightImagStop
      productImagStop := productImagStop
      leftRealStable := stabilities.leftReal
      leftImagStable := stabilities.leftImag
      rightRealStable := stabilities.rightReal
      rightImagStable := stabilities.rightImag
      productRealStable := stabilities.productReal
      productImagStable := stabilities.productImag
      productRealStart := realIdentity interval.lower
      productImagStart := imagIdentity interval.lower
      productRealStop := realIdentity interval.upper
      productImagStopEq := imagIdentity interval.upper }

/-- A refined right-endpoint cell satisfies the doubled auxiliary Cauchy-product formula.

The same factor clearances and scanner records are centered at the right
endpoint. Their reversed indices and the six reverse-oriented coordinate
stabilities certify the formula in the original interval orientation. -/
public theorem auxiliaryProductFormula_of_rightEndpoint_refined_radiusSq
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      endpointProductResolutionRadiusSq left right
        realIdentity imagIdentity interval.upper)
    (leftStart : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightStart : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (leftImagStop : B.eval interval.lower ≠ 0)
    (rightImagStop : D.eval interval.lower ≠ 0)
    (productImagStop : H.eval interval.lower ≠ 0) :
    CauchyIndex.Product.Basic.AuxiliaryProductFormula
      A B C D E H interval.lower interval.upper := by
  let product := Clearance.Pair.Basic.Certificate.complexProduct left right realIdentity imagIdentity
  have leftRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq B A left.swap :=
    radius.trans_le (Fraction.Order.Basic.min_le_left _ _)
  have rightRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq D C right.swap :=
    radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
  have productRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq H E product.swap :=
    radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))
  have stabilityRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      CauchyIndex.Product.Endpoint.Bounds.endpointStabilitiesRadiusSq A B C D E H root interval.upper :=
    radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans (le_refl _))))
  let leftEvent := CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq
    left.swap refines leftRadius
  let rightEvent := CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq
    right.swap refines rightRadius
  let productEvent := CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq
    product.swap refines productRadius
  have stabilities := CauchyIndex.Product.Endpoint.Bounds.endpointStabilities_of_refined_radiusSq refines
    (Or.inr ⟨rfl, rfl⟩) stabilityRadius
  have productStart : E.eval interval.upper ≠ 0 ∨
      H.eval interval.upper ≠ 0 :=
    Gaussian.Components.Product.complexProductPair_ne_zero
      (A.eval interval.upper) (B.eval interval.upper)
      (C.eval interval.upper) (D.eval interval.upper)
      (E.eval interval.upper) (H.eval interval.upper)
      leftStart rightStart (realIdentity interval.upper)
      (imagIdentity interval.upper)
  have reversed :
      CauchyIndex.Product.Basic.AuxiliaryProductFormula
        A B C D E H interval.upper interval.lower := by
    apply CauchyIndex.Product.Endpoint.auxiliaryProductFormula_of_localEndpointData
    exact
      { leftIndex := leftEvent.reverseIndex_eq_leftEndpointIndex2
          leftStart stabilities.leftReal stabilities.leftImag
        rightIndex := rightEvent.reverseIndex_eq_leftEndpointIndex2
          rightStart stabilities.rightReal stabilities.rightImag
        productIndex := productEvent.reverseIndex_eq_leftEndpointIndex2
          productStart stabilities.productReal stabilities.productImag
        factorLeftStart := leftStart
        factorRightStart := rightStart
        leftImagStop := leftImagStop
        rightImagStop := rightImagStop
        productImagStop := productImagStop
        leftRealStable := stabilities.leftReal
        leftImagStable := stabilities.leftImag
        rightRealStable := stabilities.rightReal
        rightImagStable := stabilities.rightImag
        productRealStable := stabilities.productReal
        productImagStable := stabilities.productImag
        productRealStart := realIdentity interval.upper
        productImagStart := imagIdentity interval.upper
        productRealStop := realIdentity interval.lower
        productImagStopEq := imagIdentity interval.lower }
  exact reversed.reverse

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Endpoint.Resolution
