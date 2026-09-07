import mathlib.Tactic.QuotientFreeRing
import RFAP.Cauchy.Resolution
import RFAP.Isolation.SafeCandidates

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

namespace RFAP.CauchyDegenerate

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.Sturm
open RFAP.CauchyProductSigns
open RFAP.CauchyCells
open RFAP.CauchyProduct
open RFAP.CauchyProductCells
open RFAP.PathClearance
open RFAP.IntervalSign
open RFAP.CauchyResolution
open RFAP.SafeCandidates

private theorem sq_pos_of_ne_zero {x : Coordinate} (nonzero : x ≠ 0) :
    0 < x ^ 2 := by
  have squareNonzero : x ^ 2 ≠ 0 := by
    intro zero
    exact nonzero ((RFAP.ConstructiveFraction.sq_eq_zero_direct x).mp zero)
  exact lt_of_le_of_ne (RFAP.ConstructiveFraction.sq_nonneg_direct x)
    (Ne.symm squareNonzero)

private theorem normSq_pos {A B : Coordinate}
    (nonzero : A ≠ 0 ∨ B ≠ 0) : 0 < A ^ 2 + B ^ 2 := by
  rcases nonzero with ANonzero | BNonzero
  · have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      (sq_pos_of_ne_zero ANonzero) (B ^ 2)
    have lower := RFAP.ConstructiveFraction.sq_nonneg_direct B
    exact lower.trans_lt (by
      simpa only [zero_add, add_zero, add_comm] using shifted)
  · have shifted := RFAP.ConstructiveFraction.add_lt_add_left_direct
      (sq_pos_of_ne_zero BNonzero) (A ^ 2)
    have lower := RFAP.ConstructiveFraction.sq_nonneg_direct A
    exact lower.trans_lt (by simpa only [add_zero] using shifted)

private theorem ofCoordinate_mul_pos_left
    (scale x : Coordinate) (positive : 0 < scale) :
    FiniteSign.ofCoordinate (scale * x) = FiniteSign.ofCoordinate x := by
  rw [FiniteSign.ofCoordinate_mul,
    FiniteSign.ofCoordinate_of_pos positive]
  cases FiniteSign.ofCoordinate x <;> rfl

private theorem eq_neg_of_eq_neg {x y : FiniteSign}
    (equal : x = FiniteSign.neg y) : y = FiniteSign.neg x := by
  cases x <;> cases y <;> simp_all [FiniteSign.neg]

/-- Endpoint sign relations forced by a nonzero purely-real product. -/
private theorem rightSigns_of_productImag_zero
    (A B C D E : Coordinate)
    (leftNonzero : A ≠ 0 ∨ B ≠ 0)
    (realIdentity : E = A * C - B * D)
    (imaginaryZero : 0 = A * D + B * C) :
    FiniteSign.ofCoordinate C =
        FiniteSign.mul (FiniteSign.ofCoordinate E)
          (FiniteSign.ofCoordinate A) ∧
      FiniteSign.ofCoordinate D =
        FiniteSign.neg (FiniteSign.mul (FiniteSign.ofCoordinate E)
          (FiniteSign.ofCoordinate B)) := by
  let normSq := A ^ 2 + B ^ 2
  have normPositive : 0 < normSq := by
    simpa only [normSq] using normSq_pos leftNonzero
  have ADRelation : A * D = -(B * C) := by
    calc
      A * D = (A * D + B * C) - B * C := by ring1
      _ = 0 - B * C := by rw [← imaginaryZero]
      _ = -(B * C) := by ring1
  have BCRelation : B * C = -(A * D) := by
    calc
      B * C = (A * D + B * C) - A * D := by ring1
      _ = 0 - A * D := by rw [← imaginaryZero]
      _ = -(A * D) := by ring1
  have realScale : E * A = normSq * C := by
    rw [realIdentity]
    calc
      (A * C - B * D) * A = A ^ 2 * C - B * (A * D) := by ring1
      _ = A ^ 2 * C - B * (-(B * C)) := by rw [ADRelation]
      _ = normSq * C := by
        dsimp only [normSq]
        ring1
  have imagScale : E * B = -(normSq * D) := by
    rw [realIdentity]
    calc
      (A * C - B * D) * B = A * (B * C) - B ^ 2 * D := by ring1
      _ = A * (-(A * D)) - B ^ 2 * D := by rw [BCRelation]
      _ = -(normSq * D) := by
        dsimp only [normSq]
        ring1
  constructor
  · rw [← ofCoordinate_mul_pos_left normSq C normPositive,
      ← realScale, FiniteSign.ofCoordinate_mul]
  · have scaled := ofCoordinate_mul_pos_left normSq D normPositive
    have signEquation := congrArg FiniteSign.ofCoordinate imagScale
    rw [FiniteSign.ofCoordinate_mul, FiniteSign.ofCoordinate_neg,
      scaled] at signEquation
    exact eq_neg_of_eq_neg signEquation

/-- Endpoint sign relations forced by a nonzero purely-imaginary product. -/
private theorem rightSigns_of_productReal_zero
    (A B C D H : Coordinate)
    (leftNonzero : A ≠ 0 ∨ B ≠ 0)
    (realZero : 0 = A * C - B * D)
    (imagIdentity : H = A * D + B * C) :
    FiniteSign.ofCoordinate C =
        FiniteSign.mul (FiniteSign.ofCoordinate H)
          (FiniteSign.ofCoordinate B) ∧
      FiniteSign.ofCoordinate D =
        FiniteSign.mul (FiniteSign.ofCoordinate H)
          (FiniteSign.ofCoordinate A) := by
  let normSq := A ^ 2 + B ^ 2
  have normPositive : 0 < normSq := by
    simpa only [normSq] using normSq_pos leftNonzero
  have ACRelation : A * C = B * D := by
    calc
      A * C = (A * C - B * D) + B * D := by ring1
      _ = 0 + B * D := by rw [← realZero]
      _ = B * D := by ring1
  have BDRelation : B * D = A * C := ACRelation.symm
  have realScale : H * B = normSq * C := by
    rw [imagIdentity]
    calc
      (A * D + B * C) * B = A * (B * D) + B ^ 2 * C := by ring1
      _ = A * (A * C) + B ^ 2 * C := by rw [BDRelation]
      _ = normSq * C := by
        dsimp only [normSq]
        ring1
  have imagScale : H * A = normSq * D := by
    rw [imagIdentity]
    calc
      (A * D + B * C) * A = A ^ 2 * D + B * (A * C) := by ring1
      _ = A ^ 2 * D + B * (B * D) := by rw [ACRelation]
      _ = normSq * D := by
        dsimp only [normSq]
        ring1
  constructor
  · rw [← ofCoordinate_mul_pos_left normSq C normPositive,
      ← realScale, FiniteSign.ofCoordinate_mul]
  · rw [← ofCoordinate_mul_pos_left normSq D normPositive,
      ← imagScale, FiniteSign.ofCoordinate_mul]

/-- If the first imaginary coordinate is identically zero, use its fixed
real sign to scale the independently certified center signs of the second
factor.  The resulting product center is compatible by construction. -/
theorem auxiliaryProductFormula_of_leftImaginary_zero_events
    {A B C D E H : Polynomial} {interval : Interval}
    (BZero : B.isZero = true)
    (leftEvent : CauchyEventSigns A B interval)
    (rightEvent : CauchyEventSigns C D interval)
    (productEvent : CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (leftNarrow : NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper))
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have BLower : B.eval interval.lower = 0 :=
    eval_eq_zero_of_isZero BZero interval.lower
  have BUpper : B.eval interval.upper = 0 :=
    eval_eq_zero_of_isZero BZero interval.upper
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
    have dotPositive := complexDot_pos_of_narrowComplexTurn leftNarrow
    simpa only [BLower, BUpper, zero_mul, add_zero] using dotPositive
  let aCenter := FiniteSign.ofCoordinate (A.eval interval.lower)
  have aCenterNonzero : aCenter ≠ .zero := by
    simpa only [aCenter, FiniteSign.ofCoordinate_ne_zero_iff] using
      ALowerNonzero
  have aUpperStable : FiniteSign.Stable aCenter
      (FiniteSign.ofCoordinate (A.eval interval.upper)) := by
    apply Or.inr
    apply FiniteSign.value_injective
    simp only [aCenter, FiniteSign.value_ofCoordinate]
    exact sign_eq_of_mul_pos AProductPositive
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
    rw [realIdentity interval.lower, BLower, zero_mul, sub_zero,
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
    rw [realIdentity interval.upper, BUpper, zero_mul, sub_zero,
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
    (by simpa only [BLower, FiniteSign.ofCoordinate_zero] using
      (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
    aUpperStable
    (by simpa only [BUpper, FiniteSign.ofCoordinate_zero] using
      (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
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

/-- The analogous explicit re-centering when the first real coordinate is
identically zero.  Multiplication by the remaining imaginary sign swaps the
second factor coordinates and negates the new real coordinate. -/
theorem auxiliaryProductFormula_of_leftReal_zero_events
    {A B C D E H : Polynomial} {interval : Interval}
    (AZero : A.isZero = true)
    (leftEvent : CauchyEventSigns A B interval)
    (rightEvent : CauchyEventSigns C D interval)
    (productEvent : CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (leftNarrow : NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper))
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have ALower : A.eval interval.lower = 0 :=
    eval_eq_zero_of_isZero AZero interval.lower
  have AUpper : A.eval interval.upper = 0 :=
    eval_eq_zero_of_isZero AZero interval.upper
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
    have dotPositive := complexDot_pos_of_narrowComplexTurn leftNarrow
    simpa only [ALower, AUpper, zero_mul, zero_add] using dotPositive
  let bCenter := FiniteSign.ofCoordinate (B.eval interval.lower)
  have bCenterNonzero : bCenter ≠ .zero := by
    simpa only [bCenter, FiniteSign.ofCoordinate_ne_zero_iff] using
      BLowerNonzero
  have bUpperStable : FiniteSign.Stable bCenter
      (FiniteSign.ofCoordinate (B.eval interval.upper)) := by
    apply Or.inr
    apply FiniteSign.value_injective
    simp only [bCenter, FiniteSign.value_ofCoordinate]
    exact sign_eq_of_mul_pos BProductPositive
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
    (by simpa only [ALower, FiniteSign.ofCoordinate_zero] using
      (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
    (Or.inr rfl)
    (by simpa only [AUpper, FiniteSign.ofCoordinate_zero] using
      (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
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

/-- Symmetric coordinate-axis row for an identically-zero second imaginary
coordinate. -/
theorem auxiliaryProductFormula_of_rightImaginary_zero_events
    {A B C D E H : Polynomial} {interval : Interval}
    (DZero : D.isZero = true)
    (leftEvent : CauchyEventSigns A B interval)
    (rightEvent : CauchyEventSigns C D interval)
    (productEvent : CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (rightNarrow : NarrowComplexTurn
      (C.eval interval.lower) (D.eval interval.lower)
      (C.eval interval.upper) (D.eval interval.upper))
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have swappedReal : ∀ x : Coordinate,
      E.eval x = C.eval x * A.eval x - D.eval x * B.eval x := by
    intro x
    rw [realIdentity x]
    ring1
  have swappedImag : ∀ x : Coordinate,
      H.eval x = C.eval x * B.eval x + D.eval x * A.eval x := by
    intro x
    rw [imagIdentity x]
    ring1
  exact (auxiliaryProductFormula_of_leftImaginary_zero_events
    DZero rightEvent leftEvent productEvent
    rightLower leftLower rightUpper leftUpper rightNarrow
    swappedReal swappedImag).swap

/-- Symmetric coordinate-axis row for an identically-zero second real
coordinate. -/
theorem auxiliaryProductFormula_of_rightReal_zero_events
    {A B C D E H : Polynomial} {interval : Interval}
    (CZero : C.isZero = true)
    (leftEvent : CauchyEventSigns A B interval)
    (rightEvent : CauchyEventSigns C D interval)
    (productEvent : CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (rightNarrow : NarrowComplexTurn
      (C.eval interval.lower) (D.eval interval.lower)
      (C.eval interval.upper) (D.eval interval.upper))
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have swappedReal : ∀ x : Coordinate,
      E.eval x = C.eval x * A.eval x - D.eval x * B.eval x := by
    intro x
    rw [realIdentity x]
    ring1
  have swappedImag : ∀ x : Coordinate,
      H.eval x = C.eval x * B.eval x + D.eval x * A.eval x := by
    intro x
    rw [imagIdentity x]
    ring1
  exact (auxiliaryProductFormula_of_leftReal_zero_events
    CZero rightEvent leftEvent productEvent
    rightLower leftLower rightUpper leftUpper rightNarrow
    swappedReal swappedImag).swap

/-- If the product imaginary coordinate is identically zero, its fixed real
sign and the first factor's certified center determine the second factor's
center by conjugation. -/
theorem auxiliaryProductFormula_of_productImaginary_zero_events
    {A B C D E H : Polynomial} {interval : Interval}
    (HZero : H.isZero = true)
    (leftEvent : CauchyEventSigns A B interval)
    (rightEvent : CauchyEventSigns C D interval)
    (productEvent : CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (leftNarrow : NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper))
    (rightNarrow : NarrowComplexTurn
      (C.eval interval.lower) (D.eval interval.lower)
      (C.eval interval.upper) (D.eval interval.upper))
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have HLower : H.eval interval.lower = 0 :=
    eval_eq_zero_of_isZero HZero interval.lower
  have HUpper : H.eval interval.upper = 0 :=
    eval_eq_zero_of_isZero HZero interval.upper
  have productLower := RFAP.CauchyResolution.complexProductPair_ne_zero
    (A.eval interval.lower) (B.eval interval.lower)
    (C.eval interval.lower) (D.eval interval.lower)
    (E.eval interval.lower) (H.eval interval.lower)
    leftLower rightLower (realIdentity interval.lower)
    (imagIdentity interval.lower)
  have productUpper := RFAP.CauchyResolution.complexProductPair_ne_zero
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
    have dotPositive := productComplexDot_pos_of_narrowTurns
      leftNarrow rightNarrow
    rw [← realIdentity interval.lower, ← imagIdentity interval.lower,
      ← realIdentity interval.upper, ← imagIdentity interval.upper,
      HLower, HUpper, zero_mul, add_zero] at dotPositive
    exact dotPositive
  let eCenter := FiniteSign.ofCoordinate (E.eval interval.lower)
  have eCenterNonzero : eCenter ≠ .zero := by
    simpa only [eCenter, FiniteSign.ofCoordinate_ne_zero_iff] using
      ELowerNonzero
  have eUpperStable : FiniteSign.Stable eCenter
      (FiniteSign.ofCoordinate (E.eval interval.upper)) := by
    apply Or.inr
    apply FiniteSign.value_injective
    simp only [eCenter, FiniteSign.value_ofCoordinate]
    exact sign_eq_of_mul_pos EProductPositive
  let cCenter := FiniteSign.mul eCenter leftEvent.numerator
  let dCenter := FiniteSign.neg
    (FiniteSign.mul eCenter leftEvent.denominator)
  have rightCenterNonzero : cCenter ≠ .zero ∨ dCenter ≠ .zero := by
    rcases leftEvent.nonzero with numeratorNonzero | denominatorNonzero
    · exact Or.inl (FiniteSign.mul_ne_zero eCenterNonzero numeratorNonzero)
    · exact Or.inr (FiniteSign.neg_ne_zero
        (FiniteSign.mul_ne_zero eCenterNonzero denominatorNonzero))
  have rightLowerSigns := rightSigns_of_productImag_zero
    (A.eval interval.lower) (B.eval interval.lower)
    (C.eval interval.lower) (D.eval interval.lower)
    (E.eval interval.lower) leftLower (realIdentity interval.lower)
    (HLower.symm.trans (imagIdentity interval.lower))
  have rightUpperSigns := rightSigns_of_productImag_zero
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
    (by simpa only [HLower, FiniteSign.ofCoordinate_zero] using
      (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
    eUpperStable
    (by simpa only [HUpper, FiniteSign.ofCoordinate_zero] using
      (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
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

/-- If the product real coordinate is identically zero, its fixed imaginary
sign determines the swapped center coordinates of the second factor. -/
theorem auxiliaryProductFormula_of_productReal_zero_events
    {A B C D E H : Polynomial} {interval : Interval}
    (EZero : E.isZero = true)
    (leftEvent : CauchyEventSigns A B interval)
    (rightEvent : CauchyEventSigns C D interval)
    (productEvent : CauchyEventSigns E H interval)
    (leftLower : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightLower : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftUpper : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightUpper : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (leftNarrow : NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper))
    (rightNarrow : NarrowComplexTurn
      (C.eval interval.lower) (D.eval interval.lower)
      (C.eval interval.upper) (D.eval interval.upper))
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have ELower : E.eval interval.lower = 0 :=
    eval_eq_zero_of_isZero EZero interval.lower
  have EUpper : E.eval interval.upper = 0 :=
    eval_eq_zero_of_isZero EZero interval.upper
  have productLower := RFAP.CauchyResolution.complexProductPair_ne_zero
    (A.eval interval.lower) (B.eval interval.lower)
    (C.eval interval.lower) (D.eval interval.lower)
    (E.eval interval.lower) (H.eval interval.lower)
    leftLower rightLower (realIdentity interval.lower)
    (imagIdentity interval.lower)
  have productUpper := RFAP.CauchyResolution.complexProductPair_ne_zero
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
    have dotPositive := productComplexDot_pos_of_narrowTurns
      leftNarrow rightNarrow
    rw [← realIdentity interval.lower, ← imagIdentity interval.lower,
      ← realIdentity interval.upper, ← imagIdentity interval.upper,
      ELower, EUpper, zero_mul, zero_add] at dotPositive
    exact dotPositive
  let hCenter := FiniteSign.ofCoordinate (H.eval interval.lower)
  have hCenterNonzero : hCenter ≠ .zero := by
    simpa only [hCenter, FiniteSign.ofCoordinate_ne_zero_iff] using
      HLowerNonzero
  have hUpperStable : FiniteSign.Stable hCenter
      (FiniteSign.ofCoordinate (H.eval interval.upper)) := by
    apply Or.inr
    apply FiniteSign.value_injective
    simp only [hCenter, FiniteSign.value_ofCoordinate]
    exact sign_eq_of_mul_pos HProductPositive
  let cCenter := FiniteSign.mul hCenter leftEvent.denominator
  let dCenter := FiniteSign.mul hCenter leftEvent.numerator
  have rightCenterNonzero : cCenter ≠ .zero ∨ dCenter ≠ .zero := by
    rcases leftEvent.nonzero with numeratorNonzero | denominatorNonzero
    · exact Or.inr (FiniteSign.mul_ne_zero hCenterNonzero numeratorNonzero)
    · exact Or.inl (FiniteSign.mul_ne_zero hCenterNonzero denominatorNonzero)
  have rightLowerSigns := rightSigns_of_productReal_zero
    (A.eval interval.lower) (B.eval interval.lower)
    (C.eval interval.lower) (D.eval interval.lower)
    (H.eval interval.lower) leftLower
    (ELower.symm.trans (realIdentity interval.lower))
    (imagIdentity interval.lower)
  have rightUpperSigns := rightSigns_of_productReal_zero
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
    (by simpa only [ELower, FiniteSign.ofCoordinate_zero] using
      (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
    (Or.inr rfl)
    (by simpa only [EUpper, FiniteSign.ofCoordinate_zero] using
      (show FiniteSign.Stable (.zero : FiniteSign) .zero from Or.inl rfl))
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

/-- Every sufficiently narrow refined cell with at least one identically-zero
coordinate is solved by the corresponding explicit axis-event theorem. -/
theorem auxiliaryProductFormula_of_degenerate_refined_radiusSq
    {A B C D E H : Polynomial} {root interval : Interval}
    (left : RFAP.PathClearance.Certificate A B root)
    (right : RFAP.PathClearance.Certificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (radius : RFAP.IntervalSign.sampleRadiusSq
      interval interval.lower <
      RFAP.CauchyResolution.localProductResolutionRadiusSq
        left right realIdentity imagIdentity)
    (degenerate : B.isZero = true ∨ D.isZero = true ∨
      A.isZero = true ∨ C.isZero = true ∨
      H.isZero = true ∨ E.isZero = true) :
    AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  let product := left.complexProduct right realIdentity imagIdentity
  have leftRadius : RFAP.IntervalSign.sampleRadiusSq
      interval interval.lower <
      RFAP.CauchyResolution.signedChainResolutionRadiusSq
        B A left.swap :=
    radius.trans_le (by
      unfold RFAP.CauchyResolution.localProductResolutionRadiusSq
      exact min_le_left _ _)
  have rightRadius : RFAP.IntervalSign.sampleRadiusSq
      interval interval.lower <
      RFAP.CauchyResolution.signedChainResolutionRadiusSq
        D C right.swap :=
    radius.trans_le (by
      unfold RFAP.CauchyResolution.localProductResolutionRadiusSq
      exact (min_le_right _ _).trans (min_le_left _ _))
  have productRadius : RFAP.IntervalSign.sampleRadiusSq
      interval interval.lower <
      RFAP.CauchyResolution.signedChainResolutionRadiusSq
        H E product.swap :=
    radius.trans_le (by
      unfold RFAP.CauchyResolution.localProductResolutionRadiusSq
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have leftTurnRadius : RFAP.IntervalSign.sampleRadiusSq
      interval interval.lower <
      RFAP.CauchyResolution.narrowTurnResolutionRadiusSq left :=
    radius.trans_le (by
      unfold RFAP.CauchyResolution.localProductResolutionRadiusSq
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
  have rightTurnRadius : RFAP.IntervalSign.sampleRadiusSq
      interval interval.lower <
      RFAP.CauchyResolution.narrowTurnResolutionRadiusSq right :=
    radius.trans_le (by
      unfold RFAP.CauchyResolution.localProductResolutionRadiusSq
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _))))
  let leftEvent :=
    RFAP.CauchyResolution.cauchyEventSignsOfRefinedRadiusSq
      left.swap refines leftRadius
  let rightEvent :=
    RFAP.CauchyResolution.cauchyEventSignsOfRefinedRadiusSq
      right.swap refines rightRadius
  let productEvent :=
    RFAP.CauchyResolution.cauchyEventSignsOfRefinedRadiusSq
      product.swap refines productRadius
  have leftNarrow :=
    RFAP.CauchyResolution.narrowComplexTurn_of_refined_radiusSq
      left refines leftTurnRadius
  have rightNarrow :=
    RFAP.CauchyResolution.narrowComplexTurn_of_refined_radiusSq
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
  · exact auxiliaryProductFormula_of_leftImaginary_zero_events
      BZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper leftNarrow
      realIdentity imagIdentity
  · exact auxiliaryProductFormula_of_rightImaginary_zero_events
      DZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper rightNarrow
      realIdentity imagIdentity
  · exact auxiliaryProductFormula_of_leftReal_zero_events
      AZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper leftNarrow
      realIdentity imagIdentity
  · exact auxiliaryProductFormula_of_rightReal_zero_events
      CZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper rightNarrow
      realIdentity imagIdentity
  · exact auxiliaryProductFormula_of_productImaginary_zero_events
      HZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper leftNarrow rightNarrow
      realIdentity imagIdentity
  · exact auxiliaryProductFormula_of_productReal_zero_events
      EZero leftEvent rightEvent productEvent
      leftLower rightLower leftUpper rightUpper leftNarrow rightNarrow
      realIdentity imagIdentity

/-- Width threshold which implies the squared-radius bound for a degenerate
event cell. -/
def degenerateProductLeafWidth
    {A B C D E H : Polynomial} {root : Interval}
    (left : Certificate A B root) (right : Certificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) : Coordinate :=
  min 1 (localProductResolutionRadiusSq left right
    realIdentity imagIdentity)

theorem degenerateProductLeafWidth_pos
    {A B C D E H : Polynomial} {root : Interval}
    (left : Certificate A B root) (right : Certificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    0 < degenerateProductLeafWidth left right
      realIdentity imagIdentity :=
  lt_min (by decide)
    (localProductResolutionRadiusSq_pos left right
      realIdentity imagIdentity)

private theorem radius_lt_of_width_lt
    {interval : Interval} (proper : interval.lower < interval.upper)
    {radiusBound : Coordinate}
    (widthSmall : interval.upper - interval.lower < min 1 radiusBound) :
    sampleRadiusSq interval interval.lower < radiusBound := by
  let width := interval.upper - interval.lower
  have widthPositive : 0 < width :=
    RFAP.ConstructiveFraction.sub_pos_direct proper
  have widthBelowOne : width < 1 :=
    widthSmall.trans_le (min_le_left _ _)
  have widthBelowRadius : width < radiusBound :=
    widthSmall.trans_le (min_le_right _ _)
  have squareBelowWidth : width ^ 2 < width := by
    have multiplied :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        widthBelowOne widthPositive
    simpa only [pow_two, one_mul] using multiplied
  rw [sampleRadiusSq_lower_eq_widthSq]
  exact squareBelowWidth.trans widthBelowRadius

private def unitGuard : Polynomial := constant 1

private theorem unitGuard_nonzero : unitGuard.isZero = false := by decide

/-- Fixed-depth central-third subdivision for every degenerate coordinate
branch.  Since pair-level event data permits axis endpoints, the cuts need
not avoid any individual coordinate roots. -/
theorem auxiliaryProductFormulaAtDepth
    {A B C D E H : Polynomial} {root : Interval}
    (left : Certificate A B root) (right : Certificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (degenerate : B.isZero = true ∨ D.isZero = true ∨
      A.isZero = true ∨ C.isZero = true ∨
      H.isZero = true ∨ E.isZero = true)
    (fuel : Nat) (interval : Interval)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (sufficient : (2 / 3 : Coordinate) ^ fuel *
      (interval.upper - interval.lower) <
        degenerateProductLeafWidth left right
          realIdentity imagIdentity) :
    AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  induction fuel generalizing interval with
  | zero =>
      have widthSmall : interval.upper - interval.lower <
          degenerateProductLeafWidth left right
            realIdentity imagIdentity := by
        simpa only [pow_zero, one_mul] using sufficient
      have radius : sampleRadiusSq interval interval.lower <
          localProductResolutionRadiusSq left right
            realIdentity imagIdentity := by
        apply radius_lt_of_width_lt proper
        simpa only [degenerateProductLeafWidth] using widthSmall
      exact auxiliaryProductFormula_of_degenerate_refined_radiusSq
        left right realIdentity imagIdentity refines radius degenerate
  | succ fuel inductionHypothesis =>
      let cut := centralSearchValue unitGuard unitGuard.natDegree proper
        unitGuard_nonzero le_rfl
      have cutSpec : interval.lower < cut ∧ cut < interval.upper := by
        have specification := centralSearchValue_spec unitGuard
          unitGuard.natDegree proper unitGuard_nonzero le_rfl
        exact specification.2
      have contraction : cut - interval.lower <
            (2 / 3 : Coordinate) *
              (interval.upper - interval.lower) ∧
          interval.upper - cut <
            (2 / 3 : Coordinate) *
              (interval.upper - interval.lower) := by
        simpa only [cut] using centralSearchValue_contraction unitGuard
          unitGuard.natDegree proper unitGuard_nonzero le_rfl
      let leftInterval : Interval :=
        { lower := interval.lower
          upper := cut
          valid := cutSpec.1.le }
      let rightInterval : Interval :=
        { lower := cut
          upper := interval.upper
          valid := cutSpec.2.le }
      have leftRefines : leftInterval.Refines root :=
        ⟨refines.1, cutSpec.2.le.trans refines.2⟩
      have rightRefines : rightInterval.Refines root :=
        ⟨refines.1.trans cutSpec.1.le, refines.2⟩
      have powerPositive : 0 < (2 / 3 : Coordinate) ^ fuel :=
        RFAP.ConstructiveFraction.pow_pos_direct (by decide) fuel
      have leftSufficient : (2 / 3 : Coordinate) ^ fuel *
          (leftInterval.upper - leftInterval.lower) <
            degenerateProductLeafWidth left right
              realIdentity imagIdentity := by
        calc
          (2 / 3 : Coordinate) ^ fuel *
              (leftInterval.upper - leftInterval.lower) <
              (2 / 3 : Coordinate) ^ fuel *
                ((2 / 3 : Coordinate) *
                  (interval.upper - interval.lower)) :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              powerPositive
              (by simpa only [leftInterval] using contraction.1)
          _ = (2 / 3 : Coordinate) ^ Nat.succ fuel *
              (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < degenerateProductLeafWidth left right
              realIdentity imagIdentity := sufficient
      have rightSufficient : (2 / 3 : Coordinate) ^ fuel *
          (rightInterval.upper - rightInterval.lower) <
            degenerateProductLeafWidth left right
              realIdentity imagIdentity := by
        calc
          (2 / 3 : Coordinate) ^ fuel *
              (rightInterval.upper - rightInterval.lower) <
              (2 / 3 : Coordinate) ^ fuel *
                ((2 / 3 : Coordinate) *
                  (interval.upper - interval.lower)) :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              powerPositive
              (by simpa only [rightInterval] using contraction.2)
          _ = (2 / 3 : Coordinate) ^ Nat.succ fuel *
              (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < degenerateProductLeafWidth left right
              realIdentity imagIdentity := sufficient
      have leftFormula := inductionHypothesis leftInterval leftRefines
        (by simpa only [leftInterval] using cutSpec.1) leftSufficient
      have rightFormula := inductionHypothesis rightInterval rightRefines
        (by simpa only [rightInterval] using cutSpec.2) rightSufficient
      exact leftFormula.add rightFormula

/-- Complete auxiliary product formula for the union of all six decidable
coordinate-degenerate branches. -/
theorem auxiliaryProductFormula_of_degenerate_coordinates
    {A B C D E H : Polynomial} {root : Interval}
    (proper : root.lower < root.upper)
    (left : Certificate A B root) (right : Certificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (degenerate : B.isZero = true ∨ D.isZero = true ∨
      A.isZero = true ∨ C.isZero = true ∨
      H.isZero = true ∨ E.isZero = true) :
    AuxiliaryProductFormula A B C D E H root.lower root.upper := by
  let leafWidth := degenerateProductLeafWidth
    left right realIdentity imagIdentity
  have leafWidthPositive : 0 < leafWidth := by
    simpa only [leafWidth] using
      degenerateProductLeafWidth_pos left right realIdentity imagIdentity
  let depth := geometricDepth (root.upper - root.lower) (leafWidth / 2)
  have geometric : (2 / 3 : Coordinate) ^ depth *
      (root.upper - root.lower) ≤ leafWidth / 2 := by
    simpa only [depth] using
      (geometricDepth_sufficient
        (width := root.upper - root.lower) (epsilon := leafWidth / 2)
        (show 0 ≤ root.upper - root.lower from
          (RFAP.ConstructiveFraction.sub_pos_direct proper).le)
        (RFAP.ConstructiveFraction.div_pos_direct leafWidthPositive
          (show (0 : Coordinate) < 2 by decide)))
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Coordinate) < 1 by decide) leafWidthPositive
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Coordinate)⁻¹ = 1 / 2 := by
      rw [RFAP.ExplicitField.div_eq_mul_inv]
      exact (RFAP.ConstructiveFraction.one_mul _).symm
    rw [halfInverse]
    simpa only [RFAP.ConstructiveFraction.mul_comm, one_mul] using scaled
  have sufficient : (2 / 3 : Coordinate) ^ depth *
      (root.upper - root.lower) < leafWidth :=
    geometric.trans_lt halfBelow
  exact auxiliaryProductFormulaAtDepth
    left right realIdentity imagIdentity degenerate depth root
    ⟨le_rfl, le_rfl⟩ proper
    (by simpa only [leafWidth] using sufficient)

end RFAP.CauchyDegenerate
