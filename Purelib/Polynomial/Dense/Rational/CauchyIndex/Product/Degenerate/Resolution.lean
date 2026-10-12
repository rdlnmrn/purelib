module
import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Cases
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Resolution
import Purelib.Polynomial.Dense.Rational.Pair.Turn.Bounds
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Resolution

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational

/-- Every sufficiently narrow refined cell with at least one identically-zero
coordinate is solved by the corresponding explicit axis-event theorem.

One of the six displayed coordinates has a true structural zero test.
The retained three event records, two narrow turns and factor-pair endpoint
nonzero conditions supply the corresponding axis case of the formula. -/
public theorem auxiliaryProductFormula_of_degenerate_refined_radiusSq
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq
      interval interval.lower <
      CauchyIndex.Product.Resolution.localProductResolutionRadiusSq
        left right realIdentity imagIdentity)
    (degenerate : B.isZero = true ∨ D.isZero = true ∨
      A.isZero = true ∨ C.isZero = true ∨
      H.isZero = true ∨ E.isZero = true) :
    CauchyIndex.Product.Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  let product := left.complexProduct right realIdentity imagIdentity
  have leftRadius : Interval.Radius.sampleRadiusSq
      interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq
        B A left.swap :=
    radius.trans_le (by
      unfold CauchyIndex.Product.Resolution.localProductResolutionRadiusSq
      exact Fraction.Order.Basic.min_le_left _ _)
  have rightRadius : Interval.Radius.sampleRadiusSq
      interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq
        D C right.swap :=
    radius.trans_le (by
      unfold CauchyIndex.Product.Resolution.localProductResolutionRadiusSq
      exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
  have productRadius : Interval.Radius.sampleRadiusSq
      interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq
        H E product.swap :=
    radius.trans_le (by
      unfold CauchyIndex.Product.Resolution.localProductResolutionRadiusSq
      exact (Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))
  have leftTurnRadius : Interval.Radius.sampleRadiusSq
      interval interval.lower <
      Pair.Turn.Bounds.narrowTurnResolutionRadiusSq left :=
    radius.trans_le (by
      unfold CauchyIndex.Product.Resolution.localProductResolutionRadiusSq
      exact (Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))))
  have rightTurnRadius : Interval.Radius.sampleRadiusSq
      interval interval.lower <
      Pair.Turn.Bounds.narrowTurnResolutionRadiusSq right :=
    radius.trans_le (by
      unfold CauchyIndex.Product.Resolution.localProductResolutionRadiusSq
      exact (Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))))
  let leftEvent :=
    CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq
      left.swap refines leftRadius
  let rightEvent :=
    CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq
      right.swap refines rightRadius
  let productEvent :=
    CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq
      product.swap refines productRadius
  have leftNarrow :=
    Pair.Turn.Bounds.narrowComplexTurn_of_refined_radiusSq
      left refines leftTurnRadius
  have rightNarrow :=
    Pair.Turn.Bounds.narrowComplexTurn_of_refined_radiusSq
      right refines rightTurnRadius
  have leftLower := left.eval_ne_zero
    ⟨refines.1, interval.valid.trans refines.2⟩
  have rightLower := right.eval_ne_zero
    ⟨refines.1, interval.valid.trans refines.2⟩
  have leftUpper := left.eval_ne_zero
    ⟨refines.1.trans interval.valid, refines.2⟩
  have rightUpper := right.eval_ne_zero
    ⟨refines.1.trans interval.valid, refines.2⟩
  rcases degenerate with BZero | DZero | AZero | CZero | HZero | EZero
  · exact CauchyIndex.Product.Degenerate.Cases.auxiliaryProductFormula_of_leftImaginary_zero_events
      BZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper leftNarrow
      realIdentity imagIdentity
  · exact CauchyIndex.Product.Degenerate.Cases.auxiliaryProductFormula_of_rightImaginary_zero_events
      DZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper rightNarrow
      realIdentity imagIdentity
  · exact CauchyIndex.Product.Degenerate.Cases.auxiliaryProductFormula_of_leftReal_zero_events
      AZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper leftNarrow
      realIdentity imagIdentity
  · exact CauchyIndex.Product.Degenerate.Cases.auxiliaryProductFormula_of_rightReal_zero_events
      CZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper rightNarrow
      realIdentity imagIdentity
  · exact CauchyIndex.Product.Degenerate.Cases.auxiliaryProductFormula_of_productImaginary_zero_events
      HZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper leftNarrow rightNarrow
      realIdentity imagIdentity
  · exact CauchyIndex.Product.Degenerate.Cases.auxiliaryProductFormula_of_productReal_zero_events
      EZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper leftNarrow rightNarrow
      realIdentity imagIdentity

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Resolution
