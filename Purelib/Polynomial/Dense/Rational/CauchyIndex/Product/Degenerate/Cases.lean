module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Product
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.Basic
import Purelib.Data.Rat.Sign.ComplexProduct.Axis
import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Sign.Basic
import Purelib.Data.Sign.ComplexProduct
import Purelib.Data.Sign.Stability
public import Purelib.Geometry.Rational.Plane.Turn.Basic
import Purelib.Geometry.Rational.Plane.Turn.Product
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Event.PairSafe
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Sign.CauchyIndex.Event
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs (CauchyEventSigns)
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Event.PairSafe (PairSafeLocalEventData)

/-!
# Coordinate-axis scenarios for retained local Cauchy product events

An original identically-zero polynomial coordinate selects one of six axis
scenarios. Nonzero endpoint pairs, retained narrow turns and exact product
evaluation identities coordinate the same three finite Cauchy event records.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Cases

open Purelib.Data.Rat
open _root_.Purelib.Data.Rat.Interval renaming Bounds -> RatInterval
open _root_.Purelib.Data renaming Sign -> FiniteSign
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Basic renaming CoordinatePolynomial -> Dense
open Purelib.Polynomial.Dense.Rational.CauchyIndex
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Product
open Purelib.Geometry.Rational.Plane

/-- An identically zero first imaginary coordinate gives the auxiliary product formula.

The original factor pairs are nonzero at both endpoints, and the first factor
satisfies its retained narrow-turn bound. Its fixed real sign scales the second
event's original center signs, preserving the four product evaluation identities. -/
public theorem auxiliaryProductFormula_of_leftImaginary_zero_events
    {A B C D E H : Dense} {interval : RatInterval}
    (BZero : B.isZero = true)
    (leftEvent : Events.Signs.CauchyEventSigns A B interval)
    (rightEvent : Events.Signs.CauchyEventSigns C D interval)
    (productEvent : Events.Signs.CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (leftNarrow : Turn.Basic.NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper))
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have BLower : B.eval interval.lower = 0 :=
    DensePolynomial.eval_eq_zero_of_isZero BZero interval.lower
  have BUpper : B.eval interval.upper = 0 :=
    DensePolynomial.eval_eq_zero_of_isZero BZero interval.upper
  have ALowerNonzero : A.eval interval.lower ≠ 0 := by
    rcases leftLower with nonzero | contradiction
    · exact nonzero
    · exact (contradiction BLower).elim
  have AUpperNonzero : A.eval interval.upper ≠ 0 := by
    rcases leftUpper with nonzero | contradiction
    · exact nonzero
    · exact (contradiction BUpper).elim
  have AProductPositive :
      0 < A.eval interval.lower * A.eval interval.upper := by
    have dotPositive := Turn.Basic.complexDot_pos_of_narrowComplexTurn leftNarrow
    simpa only [BLower, BUpper, zero_mul, add_zero] using dotPositive
  let aCenter := FiniteSign.ofCoordinate (A.eval interval.lower)
  have aCenterNonzero : aCenter ≠ .zero := by
    exact FiniteSign.ofCoordinate_ne_zero_iff.mpr ALowerNonzero
  have aUpperStable : FiniteSign.Stable aCenter
      (FiniteSign.ofCoordinate (A.eval interval.upper)) := by
    apply Or.inr
    apply FiniteSign.value_injective
    simp only [aCenter, FiniteSign.value_ofCoordinate]
    exact Sign.Basic.sign_eq_of_mul_pos AProductPositive
  let eCenter := FiniteSign.mul aCenter rightEvent.numerator
  let hCenter := FiniteSign.mul aCenter rightEvent.denominator
  have productCenterNonzero : eCenter ≠ .zero ∨ hCenter ≠ .zero := by
    rcases rightEvent.nonzero with numeratorNonzero | denominatorNonzero
    · exact Or.inl (FiniteSign.mul_ne_zero aCenterNonzero numeratorNonzero)
    · exact Or.inr (FiniteSign.mul_ne_zero aCenterNonzero denominatorNonzero)
  have productRealLowerSign :
      FiniteSign.ofCoordinate (E.eval interval.lower) =
        FiniteSign.mul aCenter
          (FiniteSign.ofCoordinate (C.eval interval.lower)) := by
    rw [realIdentity interval.lower, BLower, zero_mul, Fraction.Arithmetic.sub_eq_add_neg_direct, neg_zero, add_zero,
      FiniteSign.ofCoordinate_mul]
  have productImagLowerSign :
      FiniteSign.ofCoordinate (H.eval interval.lower) =
        FiniteSign.mul aCenter
          (FiniteSign.ofCoordinate (D.eval interval.lower)) := by
    rw [imagIdentity interval.lower, BLower, zero_mul, add_zero,
      FiniteSign.ofCoordinate_mul]
  have productRealUpperSign :
      FiniteSign.ofCoordinate (E.eval interval.upper) =
        FiniteSign.mul
          (FiniteSign.ofCoordinate (A.eval interval.upper))
          (FiniteSign.ofCoordinate (C.eval interval.upper)) := by
    rw [realIdentity interval.upper, BUpper, zero_mul, Fraction.Arithmetic.sub_eq_add_neg_direct, neg_zero, add_zero,
      FiniteSign.ofCoordinate_mul]
  have productImagUpperSign :
      FiniteSign.ofCoordinate (H.eval interval.upper) =
        FiniteSign.mul
          (FiniteSign.ofCoordinate (A.eval interval.upper))
          (FiniteSign.ofCoordinate (D.eval interval.upper)) := by
    rw [imagIdentity interval.upper, BUpper, zero_mul, add_zero,
      FiniteSign.ofCoordinate_mul]
  let leftCentered := leftEvent.recenter aCenter .zero
    (Or.inl aCenterNonzero)
    (Or.inr rfl)
    (by
        simpa only [BLower, FiniteSign.ofCoordinate_zero]
          using (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
    aUpperStable
    (by
        simpa only [BUpper, FiniteSign.ofCoordinate_zero]
          using (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
  have productRealLowerStable : FiniteSign.Stable eCenter
      (FiniteSign.ofCoordinate (E.eval interval.lower)) := by
    rw [productRealLowerSign]
    exact (show FiniteSign.Stable aCenter aCenter from Or.inr rfl).mul
      rightEvent.numeratorLowerStable
  have productImagLowerStable : FiniteSign.Stable hCenter
      (FiniteSign.ofCoordinate (H.eval interval.lower)) := by
    rw [productImagLowerSign]
    exact (show FiniteSign.Stable aCenter aCenter from Or.inr rfl).mul
      rightEvent.denominatorLowerStable
  have productRealUpperStable : FiniteSign.Stable eCenter
      (FiniteSign.ofCoordinate (E.eval interval.upper)) := by
    rw [productRealUpperSign]
    exact aUpperStable.mul rightEvent.numeratorUpperStable
  have productImagUpperStable : FiniteSign.Stable hCenter
      (FiniteSign.ofCoordinate (H.eval interval.upper)) := by
    rw [productImagUpperSign]
    exact aUpperStable.mul rightEvent.denominatorUpperStable
  let productCentered := productEvent.recenter eCenter hCenter
    productCenterNonzero productRealLowerStable productImagLowerStable
    productRealUpperStable productImagUpperStable
  apply PairSafeLocalEventData.auxiliaryProductFormula
  exact
    { left := leftCentered
      right := rightEvent
      product := productCentered
      centersCompatible := by
        simpa only [leftCentered, productCentered,
          CauchyEventSigns.recenter, eCenter, hCenter] using
          FiniteSign.complexProductCompatible_left_imag_zero
            aCenter rightEvent.numerator rightEvent.denominator
      factorLeftLower := leftLower
      factorRightLower := rightLower
      factorLeftUpper := leftUpper
      factorRightUpper := rightUpper
      productRealLowerEq := realIdentity interval.lower
      productImagLowerEq := imagIdentity interval.lower
      productRealUpperEq := realIdentity interval.upper
      productImagUpperEq := imagIdentity interval.upper }

/-- An identically zero first real coordinate gives the auxiliary product formula.

The original factor pairs are nonzero at both endpoints, and the first factor
satisfies its retained narrow-turn bound. Its fixed imaginary sign swaps the
second event's center coordinates and negates the retained real product sign. -/
public theorem auxiliaryProductFormula_of_leftReal_zero_events
    {A B C D E H : Dense} {interval : RatInterval}
    (AZero : A.isZero = true)
    (leftEvent : Events.Signs.CauchyEventSigns A B interval)
    (rightEvent : Events.Signs.CauchyEventSigns C D interval)
    (productEvent : Events.Signs.CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (leftNarrow : Turn.Basic.NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper))
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have ALower : A.eval interval.lower = 0 :=
    DensePolynomial.eval_eq_zero_of_isZero AZero interval.lower
  have AUpper : A.eval interval.upper = 0 :=
    DensePolynomial.eval_eq_zero_of_isZero AZero interval.upper
  have BLowerNonzero : B.eval interval.lower ≠ 0 := by
    rcases leftLower with contradiction | nonzero
    · exact (contradiction ALower).elim
    · exact nonzero
  have BUpperNonzero : B.eval interval.upper ≠ 0 := by
    rcases leftUpper with contradiction | nonzero
    · exact (contradiction AUpper).elim
    · exact nonzero
  have BProductPositive :
      0 < B.eval interval.lower * B.eval interval.upper := by
    have dotPositive := Turn.Basic.complexDot_pos_of_narrowComplexTurn leftNarrow
    simpa only [ALower, AUpper, zero_mul, zero_add] using dotPositive
  let bCenter := FiniteSign.ofCoordinate (B.eval interval.lower)
  have bCenterNonzero : bCenter ≠ .zero := by
    exact FiniteSign.ofCoordinate_ne_zero_iff.mpr BLowerNonzero
  have bUpperStable : FiniteSign.Stable bCenter
      (FiniteSign.ofCoordinate (B.eval interval.upper)) := by
    apply Or.inr
    apply FiniteSign.value_injective
    simp only [bCenter, FiniteSign.value_ofCoordinate]
    exact Sign.Basic.sign_eq_of_mul_pos BProductPositive
  let eCenter := FiniteSign.neg
    (FiniteSign.mul bCenter rightEvent.denominator)
  let hCenter := FiniteSign.mul bCenter rightEvent.numerator
  have productCenterNonzero : eCenter ≠ .zero ∨ hCenter ≠ .zero := by
    rcases rightEvent.nonzero with numeratorNonzero | denominatorNonzero
    · exact Or.inr (FiniteSign.mul_ne_zero bCenterNonzero numeratorNonzero)
    · exact Or.inl (FiniteSign.neg_ne_zero
        (FiniteSign.mul_ne_zero bCenterNonzero denominatorNonzero))
  have productRealLowerSign :
      FiniteSign.ofCoordinate (E.eval interval.lower) =
        FiniteSign.neg (FiniteSign.mul bCenter
          (FiniteSign.ofCoordinate (D.eval interval.lower))) := by
    rw [realIdentity interval.lower, ALower, zero_mul, zero_sub,
      FiniteSign.ofCoordinate_neg, FiniteSign.ofCoordinate_mul]
  have productImagLowerSign :
      FiniteSign.ofCoordinate (H.eval interval.lower) =
        FiniteSign.mul bCenter
          (FiniteSign.ofCoordinate (C.eval interval.lower)) := by
    rw [imagIdentity interval.lower, ALower, zero_mul, zero_add,
      FiniteSign.ofCoordinate_mul]
  have productRealUpperSign :
      FiniteSign.ofCoordinate (E.eval interval.upper) =
        FiniteSign.neg (FiniteSign.mul
          (FiniteSign.ofCoordinate (B.eval interval.upper))
          (FiniteSign.ofCoordinate (D.eval interval.upper))) := by
    rw [realIdentity interval.upper, AUpper, zero_mul, zero_sub,
      FiniteSign.ofCoordinate_neg, FiniteSign.ofCoordinate_mul]
  have productImagUpperSign :
      FiniteSign.ofCoordinate (H.eval interval.upper) =
        FiniteSign.mul
          (FiniteSign.ofCoordinate (B.eval interval.upper))
          (FiniteSign.ofCoordinate (C.eval interval.upper)) := by
    rw [imagIdentity interval.upper, AUpper, zero_mul, zero_add,
      FiniteSign.ofCoordinate_mul]
  let leftCentered := leftEvent.recenter .zero bCenter
    (Or.inr bCenterNonzero)
    (by
        simpa only [ALower, FiniteSign.ofCoordinate_zero]
          using (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
    (Or.inr rfl)
    (by
        simpa only [AUpper, FiniteSign.ofCoordinate_zero]
          using (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
    bUpperStable
  have productRealLowerStable : FiniteSign.Stable eCenter
      (FiniteSign.ofCoordinate (E.eval interval.lower)) := by
    rw [productRealLowerSign]
    exact ((show FiniteSign.Stable bCenter bCenter from Or.inr rfl).mul
      rightEvent.denominatorLowerStable).neg
  have productImagLowerStable : FiniteSign.Stable hCenter
      (FiniteSign.ofCoordinate (H.eval interval.lower)) := by
    rw [productImagLowerSign]
    exact (show FiniteSign.Stable bCenter bCenter from Or.inr rfl).mul
      rightEvent.numeratorLowerStable
  have productRealUpperStable : FiniteSign.Stable eCenter
      (FiniteSign.ofCoordinate (E.eval interval.upper)) := by
    rw [productRealUpperSign]
    exact (bUpperStable.mul rightEvent.denominatorUpperStable).neg
  have productImagUpperStable : FiniteSign.Stable hCenter
      (FiniteSign.ofCoordinate (H.eval interval.upper)) := by
    rw [productImagUpperSign]
    exact bUpperStable.mul rightEvent.numeratorUpperStable
  let productCentered := productEvent.recenter eCenter hCenter
    productCenterNonzero productRealLowerStable productImagLowerStable
    productRealUpperStable productImagUpperStable
  apply PairSafeLocalEventData.auxiliaryProductFormula
  exact
    { left := leftCentered
      right := rightEvent
      product := productCentered
      centersCompatible := by
        simpa only [leftCentered, productCentered,
          CauchyEventSigns.recenter, eCenter, hCenter] using
          FiniteSign.complexProductCompatible_left_real_zero
            bCenter rightEvent.numerator rightEvent.denominator
      factorLeftLower := leftLower
      factorRightLower := rightLower
      factorLeftUpper := leftUpper
      factorRightUpper := rightUpper
      productRealLowerEq := realIdentity interval.lower
      productImagLowerEq := imagIdentity interval.lower
      productRealUpperEq := realIdentity interval.upper
      productImagUpperEq := imagIdentity interval.upper }

/-- An identically zero second imaginary coordinate gives the auxiliary product formula.

The same endpoint pair certificates and the second factor's narrow turn permit
the original symmetric first-factor scenario. Swapping the retained factor
records preserves the exact real and imaginary evaluation identities. -/
public theorem auxiliaryProductFormula_of_rightImaginary_zero_events
    {A B C D E H : Dense} {interval : RatInterval}
    (DZero : D.isZero = true)
    (leftEvent : Events.Signs.CauchyEventSigns A B interval)
    (rightEvent : Events.Signs.CauchyEventSigns C D interval)
    (productEvent : Events.Signs.CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (rightNarrow : Turn.Basic.NarrowComplexTurn
      (C.eval interval.lower) (D.eval interval.lower)
      (C.eval interval.upper) (D.eval interval.upper))
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have swappedReal : ∀ x : Fraction.Rational,
      E.eval x = C.eval x * A.eval x - D.eval x * B.eval x := by
    intro x
    rw [realIdentity x]
    ring1
  have swappedImag : ∀ x : Fraction.Rational,
      H.eval x = C.eval x * B.eval x + D.eval x * A.eval x := by
    intro x
    rw [imagIdentity x]
    ring1
  exact (auxiliaryProductFormula_of_leftImaginary_zero_events
    DZero rightEvent leftEvent productEvent
    rightLower leftLower rightUpper leftUpper rightNarrow
    swappedReal swappedImag).swap

/-- An identically zero second real coordinate gives the auxiliary product formula.

The same endpoint pair certificates and the second factor's narrow turn permit
the original symmetric first-factor scenario. Swapping the retained factor
records preserves the exact real and imaginary evaluation identities. -/
public theorem auxiliaryProductFormula_of_rightReal_zero_events
    {A B C D E H : Dense} {interval : RatInterval}
    (CZero : C.isZero = true)
    (leftEvent : Events.Signs.CauchyEventSigns A B interval)
    (rightEvent : Events.Signs.CauchyEventSigns C D interval)
    (productEvent : Events.Signs.CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (rightNarrow : Turn.Basic.NarrowComplexTurn
      (C.eval interval.lower) (D.eval interval.lower)
      (C.eval interval.upper) (D.eval interval.upper))
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have swappedReal : ∀ x : Fraction.Rational,
      E.eval x = C.eval x * A.eval x - D.eval x * B.eval x := by
    intro x
    rw [realIdentity x]
    ring1
  have swappedImag : ∀ x : Fraction.Rational,
      H.eval x = C.eval x * B.eval x + D.eval x * A.eval x := by
    intro x
    rw [imagIdentity x]
    ring1
  exact (auxiliaryProductFormula_of_leftReal_zero_events
    CZero rightEvent leftEvent productEvent
    rightLower leftLower rightUpper leftUpper rightNarrow
    swappedReal swappedImag).swap

/-- An identically zero product imaginary coordinate gives the auxiliary product formula.

Both original factor turns are narrow and their endpoint pairs are nonzero.
The product's fixed real sign and the first event's retained center determine
the same conjugated second center through the exact product identities. -/
public theorem auxiliaryProductFormula_of_productImaginary_zero_events
    {A B C D E H : Dense} {interval : RatInterval}
    (HZero : H.isZero = true)
    (leftEvent : Events.Signs.CauchyEventSigns A B interval)
    (rightEvent : Events.Signs.CauchyEventSigns C D interval)
    (productEvent : Events.Signs.CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (leftNarrow : Turn.Basic.NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper))
    (rightNarrow : Turn.Basic.NarrowComplexTurn
      (C.eval interval.lower) (D.eval interval.lower)
      (C.eval interval.upper) (D.eval interval.upper))
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := open Purelib.Data in by
  have HLower : H.eval interval.lower = 0 :=
    DensePolynomial.eval_eq_zero_of_isZero HZero interval.lower
  have HUpper : H.eval interval.upper = 0 :=
    DensePolynomial.eval_eq_zero_of_isZero HZero interval.upper
  have productLower := Gaussian.Components.Product.complexProductPair_ne_zero
    (A.eval interval.lower) (B.eval interval.lower)
    (C.eval interval.lower) (D.eval interval.lower)
    (E.eval interval.lower) (H.eval interval.lower)
    leftLower rightLower (realIdentity interval.lower)
    (imagIdentity interval.lower)
  have productUpper := Gaussian.Components.Product.complexProductPair_ne_zero
    (A.eval interval.upper) (B.eval interval.upper)
    (C.eval interval.upper) (D.eval interval.upper)
    (E.eval interval.upper) (H.eval interval.upper)
    leftUpper rightUpper (realIdentity interval.upper)
    (imagIdentity interval.upper)
  have ELowerNonzero : E.eval interval.lower ≠ 0 := by
    rcases productLower with nonzero | contradiction
    · exact nonzero
    · exact (contradiction HLower).elim
  have EUpperNonzero : E.eval interval.upper ≠ 0 := by
    rcases productUpper with nonzero | contradiction
    · exact nonzero
    · exact (contradiction HUpper).elim
  have EProductPositive :
      0 < E.eval interval.lower * E.eval interval.upper := by
    have dotPositive := Turn.Product.productComplexDot_pos_of_narrowTurns
      leftNarrow rightNarrow
    rw [← realIdentity interval.lower, ← imagIdentity interval.lower,
      ← realIdentity interval.upper, ← imagIdentity interval.upper,
      HLower, HUpper, zero_mul, add_zero] at dotPositive
    exact dotPositive
  let eCenter := FiniteSign.ofCoordinate (E.eval interval.lower)
  have eCenterNonzero : eCenter ≠ .zero := by
    exact FiniteSign.ofCoordinate_ne_zero_iff.mpr ELowerNonzero
  have eUpperStable : FiniteSign.Stable eCenter
      (FiniteSign.ofCoordinate (E.eval interval.upper)) := by
    apply Or.inr
    apply FiniteSign.value_injective
    simp only [eCenter, FiniteSign.value_ofCoordinate]
    exact Sign.Basic.sign_eq_of_mul_pos EProductPositive
  let cCenter := FiniteSign.mul eCenter leftEvent.numerator
  let dCenter := FiniteSign.neg
    (FiniteSign.mul eCenter leftEvent.denominator)
  have rightCenterNonzero : cCenter ≠ .zero ∨ dCenter ≠ .zero := by
    rcases leftEvent.nonzero with numeratorNonzero | denominatorNonzero
    · exact Or.inl (FiniteSign.mul_ne_zero eCenterNonzero numeratorNonzero)
    · exact Or.inr (FiniteSign.neg_ne_zero
        (FiniteSign.mul_ne_zero eCenterNonzero denominatorNonzero))
  have rightLowerSigns := Sign.ComplexProduct.Axis.rightSigns_of_productImag_zero
    (A.eval interval.lower) (B.eval interval.lower)
    (C.eval interval.lower) (D.eval interval.lower)
    (E.eval interval.lower) leftLower (realIdentity interval.lower)
    (HLower.symm.trans (imagIdentity interval.lower))
  have rightUpperSigns := Sign.ComplexProduct.Axis.rightSigns_of_productImag_zero
    (A.eval interval.upper) (B.eval interval.upper)
    (C.eval interval.upper) (D.eval interval.upper)
    (E.eval interval.upper) leftUpper (realIdentity interval.upper)
    (HUpper.symm.trans (imagIdentity interval.upper))
  have cLowerStable : FiniteSign.Stable cCenter
      (FiniteSign.ofCoordinate (C.eval interval.lower)) := by
    rw [rightLowerSigns.1]
    exact (show FiniteSign.Stable eCenter eCenter from Or.inr rfl).mul
      leftEvent.numeratorLowerStable
  have dLowerStable : FiniteSign.Stable dCenter
      (FiniteSign.ofCoordinate (D.eval interval.lower)) := by
    rw [rightLowerSigns.2]
    exact ((show FiniteSign.Stable eCenter eCenter from Or.inr rfl).mul
      leftEvent.denominatorLowerStable).neg
  have cUpperStable : FiniteSign.Stable cCenter
      (FiniteSign.ofCoordinate (C.eval interval.upper)) := by
    rw [rightUpperSigns.1]
    exact eUpperStable.mul leftEvent.numeratorUpperStable
  have dUpperStable : FiniteSign.Stable dCenter
      (FiniteSign.ofCoordinate (D.eval interval.upper)) := by
    rw [rightUpperSigns.2]
    exact (eUpperStable.mul leftEvent.denominatorUpperStable).neg
  let rightCentered := rightEvent.recenter cCenter dCenter
    rightCenterNonzero cLowerStable dLowerStable cUpperStable dUpperStable
  let productCentered := productEvent.recenter eCenter .zero
    (Or.inl eCenterNonzero)
    (Or.inr rfl)
    (by
        simpa only [HLower, FiniteSign.ofCoordinate_zero]
          using (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
    eUpperStable
    (by
        simpa only [HUpper, FiniteSign.ofCoordinate_zero]
          using (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
  apply PairSafeLocalEventData.auxiliaryProductFormula
  exact
    { left := leftEvent
      right := rightCentered
      product := productCentered
      centersCompatible := by
        simpa only [rightCentered, productCentered,
          CauchyEventSigns.recenter, cCenter, dCenter] using
          FiniteSign.complexProductCompatible_product_imag_zero
            leftEvent.numerator leftEvent.denominator eCenter
            leftEvent.nonzero eCenterNonzero
      factorLeftLower := leftLower
      factorRightLower := rightLower
      factorLeftUpper := leftUpper
      factorRightUpper := rightUpper
      productRealLowerEq := realIdentity interval.lower
      productImagLowerEq := imagIdentity interval.lower
      productRealUpperEq := realIdentity interval.upper
      productImagUpperEq := imagIdentity interval.upper }

/-- An identically zero product real coordinate gives the auxiliary product formula.

Both original factor turns are narrow and their endpoint pairs are nonzero.
The product's fixed imaginary sign determines the same swapped second center
through the original real and imaginary product evaluation identities. -/
public theorem auxiliaryProductFormula_of_productReal_zero_events
    {A B C D E H : Dense} {interval : RatInterval}
    (EZero : E.isZero = true)
    (leftEvent : Events.Signs.CauchyEventSigns A B interval)
    (rightEvent : Events.Signs.CauchyEventSigns C D interval)
    (productEvent : Events.Signs.CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (leftNarrow : Turn.Basic.NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper))
    (rightNarrow : Turn.Basic.NarrowComplexTurn
      (C.eval interval.lower) (D.eval interval.lower)
      (C.eval interval.upper) (D.eval interval.upper))
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := open Purelib.Data in by
  have ELower : E.eval interval.lower = 0 :=
    DensePolynomial.eval_eq_zero_of_isZero EZero interval.lower
  have EUpper : E.eval interval.upper = 0 :=
    DensePolynomial.eval_eq_zero_of_isZero EZero interval.upper
  have productLower := Gaussian.Components.Product.complexProductPair_ne_zero
    (A.eval interval.lower) (B.eval interval.lower)
    (C.eval interval.lower) (D.eval interval.lower)
    (E.eval interval.lower) (H.eval interval.lower)
    leftLower rightLower (realIdentity interval.lower)
    (imagIdentity interval.lower)
  have productUpper := Gaussian.Components.Product.complexProductPair_ne_zero
    (A.eval interval.upper) (B.eval interval.upper)
    (C.eval interval.upper) (D.eval interval.upper)
    (E.eval interval.upper) (H.eval interval.upper)
    leftUpper rightUpper (realIdentity interval.upper)
    (imagIdentity interval.upper)
  have HLowerNonzero : H.eval interval.lower ≠ 0 := by
    rcases productLower with contradiction | nonzero
    · exact (contradiction ELower).elim
    · exact nonzero
  have HUpperNonzero : H.eval interval.upper ≠ 0 := by
    rcases productUpper with contradiction | nonzero
    · exact (contradiction EUpper).elim
    · exact nonzero
  have HProductPositive :
      0 < H.eval interval.lower * H.eval interval.upper := by
    have dotPositive := Turn.Product.productComplexDot_pos_of_narrowTurns
      leftNarrow rightNarrow
    rw [← realIdentity interval.lower, ← imagIdentity interval.lower,
      ← realIdentity interval.upper, ← imagIdentity interval.upper,
      ELower, EUpper, zero_mul, zero_add] at dotPositive
    exact dotPositive
  let hCenter := FiniteSign.ofCoordinate (H.eval interval.lower)
  have hCenterNonzero : hCenter ≠ .zero := by
    exact FiniteSign.ofCoordinate_ne_zero_iff.mpr HLowerNonzero
  have hUpperStable : FiniteSign.Stable hCenter
      (FiniteSign.ofCoordinate (H.eval interval.upper)) := by
    apply Or.inr
    apply FiniteSign.value_injective
    simp only [hCenter, FiniteSign.value_ofCoordinate]
    exact Sign.Basic.sign_eq_of_mul_pos HProductPositive
  let cCenter := FiniteSign.mul hCenter leftEvent.denominator
  let dCenter := FiniteSign.mul hCenter leftEvent.numerator
  have rightCenterNonzero : cCenter ≠ .zero ∨ dCenter ≠ .zero := by
    rcases leftEvent.nonzero with numeratorNonzero | denominatorNonzero
    · exact Or.inr (FiniteSign.mul_ne_zero hCenterNonzero numeratorNonzero)
    · exact Or.inl (FiniteSign.mul_ne_zero hCenterNonzero denominatorNonzero)
  have rightLowerSigns := Sign.ComplexProduct.Axis.rightSigns_of_productReal_zero
    (A.eval interval.lower) (B.eval interval.lower)
    (C.eval interval.lower) (D.eval interval.lower)
    (H.eval interval.lower) leftLower
    (ELower.symm.trans (realIdentity interval.lower))
    (imagIdentity interval.lower)
  have rightUpperSigns := Sign.ComplexProduct.Axis.rightSigns_of_productReal_zero
    (A.eval interval.upper) (B.eval interval.upper)
    (C.eval interval.upper) (D.eval interval.upper)
    (H.eval interval.upper) leftUpper
    (EUpper.symm.trans (realIdentity interval.upper))
    (imagIdentity interval.upper)
  have cLowerStable : FiniteSign.Stable cCenter
      (FiniteSign.ofCoordinate (C.eval interval.lower)) := by
    rw [rightLowerSigns.1]
    exact (show FiniteSign.Stable hCenter hCenter from Or.inr rfl).mul
      leftEvent.denominatorLowerStable
  have dLowerStable : FiniteSign.Stable dCenter
      (FiniteSign.ofCoordinate (D.eval interval.lower)) := by
    rw [rightLowerSigns.2]
    exact (show FiniteSign.Stable hCenter hCenter from Or.inr rfl).mul
      leftEvent.numeratorLowerStable
  have cUpperStable : FiniteSign.Stable cCenter
      (FiniteSign.ofCoordinate (C.eval interval.upper)) := by
    rw [rightUpperSigns.1]
    exact hUpperStable.mul leftEvent.denominatorUpperStable
  have dUpperStable : FiniteSign.Stable dCenter
      (FiniteSign.ofCoordinate (D.eval interval.upper)) := by
    rw [rightUpperSigns.2]
    exact hUpperStable.mul leftEvent.numeratorUpperStable
  let rightCentered := rightEvent.recenter cCenter dCenter
    rightCenterNonzero cLowerStable dLowerStable cUpperStable dUpperStable
  let productCentered := productEvent.recenter .zero hCenter
    (Or.inr hCenterNonzero)
    (by
        simpa only [ELower, FiniteSign.ofCoordinate_zero]
          using (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
    (Or.inr rfl)
    (by
        simpa only [EUpper, FiniteSign.ofCoordinate_zero]
          using (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
    hUpperStable
  apply PairSafeLocalEventData.auxiliaryProductFormula
  exact
    { left := leftEvent
      right := rightCentered
      product := productCentered
      centersCompatible := by
        simpa only [rightCentered, productCentered,
          CauchyEventSigns.recenter, cCenter, dCenter] using
          FiniteSign.complexProductCompatible_product_real_zero
            leftEvent.numerator leftEvent.denominator hCenter
            leftEvent.nonzero hCenterNonzero
      factorLeftLower := leftLower
      factorRightLower := rightLower
      factorLeftUpper := leftUpper
      factorRightUpper := rightUpper
      productRealLowerEq := realIdentity interval.lower
      productImagLowerEq := imagIdentity interval.lower
      productRealUpperEq := realIdentity interval.upper
      productImagUpperEq := imagIdentity interval.upper }

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Cases
