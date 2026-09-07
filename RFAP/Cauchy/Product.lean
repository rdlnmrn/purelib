import mathlib.Tactic.QuotientFreeRing
import RFAP.Cauchy.Cells

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

namespace RFAP.CauchyProduct

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.Sturm
open RFAP.CauchyProductSigns
open RFAP.CauchyCells

def auxiliaryEndpointCorrection2
    (B D H : Polynomial) (x : Coordinate) : Nat :=
  signJump 1 (H.eval x * (B.eval x * D.eval x))

def AuxiliaryProductFormula
    (A B C D E H : Polynomial) (a b : Coordinate) : Prop :=
  cauchyIndex2 E H a b =
    cauchyIndex2 A B a b + cauchyIndex2 C D a b -
      (auxiliaryEndpointCorrection2 B D H a : Int) +
      auxiliaryEndpointCorrection2 B D H b

/-- Auxiliary product formulas compose under exact interval subdivision. -/
theorem AuxiliaryProductFormula.add
    {A B C D E H : Polynomial} {a b c : Coordinate}
    (left : AuxiliaryProductFormula A B C D E H a b)
    (right : AuxiliaryProductFormula A B C D E H b c) :
    AuxiliaryProductFormula A B C D E H a c := by
  unfold AuxiliaryProductFormula at left right ⊢
  rw [cauchyIndex2_add E H a b c,
    cauchyIndex2_add A B a b c,
    cauchyIndex2_add C D a b c]
  rw [left, right]
  ring1

/-- Reversing an interval reverses its auxiliary product formula. -/
theorem AuxiliaryProductFormula.reverse
    {A B C D E H : Polynomial} {a b : Coordinate}
    (formula : AuxiliaryProductFormula A B C D E H a b) :
    AuxiliaryProductFormula A B C D E H b a := by
  unfold AuxiliaryProductFormula at formula ⊢
  rw [cauchyIndex2_reverse E H a b,
    cauchyIndex2_reverse A B a b,
    cauchyIndex2_reverse C D a b]
  rw [formula]
  ring1

/-- The auxiliary identity is symmetric in its two displayed complex
factors. -/
theorem AuxiliaryProductFormula.swap
    {A B C D E H : Polynomial} {a b : Coordinate}
    (formula : AuxiliaryProductFormula A B C D E H a b) :
    AuxiliaryProductFormula C D A B E H a b := by
  have correction : ∀ x : Coordinate,
      auxiliaryEndpointCorrection2 D B H x =
        auxiliaryEndpointCorrection2 B D H x := by
    intro x
    unfold auxiliaryEndpointCorrection2
    rw [mul_comm (D.eval x) (B.eval x)]
  unfold AuxiliaryProductFormula at formula ⊢
  rw [correction a, correction b]
  rw [formula]
  ring1

/-- All finite facts needed on one resolved one-sided event cell. -/
structure LocalEndpointData
    (A B C D E H : Polynomial) (a b : Coordinate) : Prop where
  leftIndex : cauchyIndex2 A B a b =
    leftEndpointIndex2 (A.eval a) (B.eval a) (A.eval b) (B.eval b)
  rightIndex : cauchyIndex2 C D a b =
    leftEndpointIndex2 (C.eval a) (D.eval a) (C.eval b) (D.eval b)
  productIndex : cauchyIndex2 E H a b =
    leftEndpointIndex2 (E.eval a) (H.eval a) (E.eval b) (H.eval b)
  factorLeftStart : A.eval a ≠ 0 ∨ B.eval a ≠ 0
  factorRightStart : C.eval a ≠ 0 ∨ D.eval a ≠ 0
  leftImagStop : B.eval b ≠ 0
  rightImagStop : D.eval b ≠ 0
  productImagStop : H.eval b ≠ 0
  leftRealStable : A.eval a = 0 ∨ 0 < A.eval a * A.eval b
  leftImagStable : B.eval a = 0 ∨ 0 < B.eval a * B.eval b
  rightRealStable : C.eval a = 0 ∨ 0 < C.eval a * C.eval b
  rightImagStable : D.eval a = 0 ∨ 0 < D.eval a * D.eval b
  productRealStable : E.eval a = 0 ∨ 0 < E.eval a * E.eval b
  productImagStable : H.eval a = 0 ∨ 0 < H.eval a * H.eval b
  productRealStart : E.eval a =
    A.eval a * C.eval a - B.eval a * D.eval a
  productImagStart : H.eval a =
    A.eval a * D.eval a + B.eval a * C.eval a
  productRealStop : E.eval b =
    A.eval b * C.eval b - B.eval b * D.eval b
  productImagStopEq : H.eval b =
    A.eval b * D.eval b + B.eval b * C.eval b

/-- The finite local endpoint data implies the complete doubled product
identity on that cell. -/
theorem auxiliaryProductFormula_of_localEndpointData
    {A B C D E H : Polynomial} {a b : Coordinate}
    (data : LocalEndpointData A B C D E H a b) :
    AuxiliaryProductFormula A B C D E H a b := by
  unfold AuxiliaryProductFormula auxiliaryEndpointCorrection2
  rw [data.leftIndex, data.rightIndex, data.productIndex,
    data.productRealStart, data.productImagStart,
    data.productRealStop, data.productImagStopEq]
  exact coordinateLocalProductTable
    (A.eval a) (B.eval a) (C.eval a) (D.eval a)
    (A.eval b) (B.eval b) (C.eval b) (D.eval b)
    data.factorLeftStart data.factorRightStart
    data.leftImagStop data.rightImagStop
    (by simpa only [← data.productImagStopEq] using data.productImagStop)
    data.leftRealStable data.leftImagStable
    data.rightRealStable data.rightImagStable
    (by simpa only [← data.productRealStart, ← data.productRealStop]
      using data.productRealStable)
    (by simpa only [← data.productImagStart, ← data.productImagStopEq]
      using data.productImagStable)

/-- Three exact finite-chain event records with coordinated formal center
signs.  Only endpoint nonvanishing and the four displayed multiplication
identities are added; no intermediate root or parameter is represented. -/
structure LocalEventData
    (A B C D E H : Polynomial) (interval : Interval) where
  left : CauchyEventSigns A B interval
  right : CauchyEventSigns C D interval
  product : CauchyEventSigns E H interval
  centersCompatible : FiniteSign.ComplexProductCompatible
    left.numerator left.denominator right.numerator right.denominator
    product.numerator product.denominator
  leftImagLower : B.eval interval.lower ≠ 0
  rightImagLower : D.eval interval.lower ≠ 0
  productImagLower : H.eval interval.lower ≠ 0
  leftImagUpper : B.eval interval.upper ≠ 0
  rightImagUpper : D.eval interval.upper ≠ 0
  productImagUpper : H.eval interval.upper ≠ 0
  productRealLowerEq : E.eval interval.lower =
    A.eval interval.lower * C.eval interval.lower -
      B.eval interval.lower * D.eval interval.lower
  productImagLowerEq : H.eval interval.lower =
    A.eval interval.lower * D.eval interval.lower +
      B.eval interval.lower * C.eval interval.lower
  productRealUpperEq : E.eval interval.upper =
    A.eval interval.upper * C.eval interval.upper -
      B.eval interval.upper * D.eval interval.upper
  productImagUpperEq : H.eval interval.upper =
    A.eval interval.upper * D.eval interval.upper +
      B.eval interval.upper * C.eval interval.upper

namespace LocalEventData

/-- Re-center three independently certified Cauchy events at four proposed
factor signs and the conservative finite signs of their complex product. -/
def ofRecenteredFactors
    {A B C D E H : Polynomial} {interval : Interval}
    (leftBase : CauchyEventSigns A B interval)
    (rightBase : CauchyEventSigns C D interval)
    (productBase : CauchyEventSigns E H interval)
    (factorLeftReal factorLeftImag factorRightReal factorRightImag :
      FiniteSign)
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
        simpa only [left, right, product, CauchyEventSigns.recenter] using
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

private theorem lowerAdmissible
    {A B C D E H : Polynomial} {interval : Interval}
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
  · simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using data.leftImagLower
  · simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using data.rightImagLower
  · simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using data.productImagLower
  · rw [data.productRealLowerEq, data.productImagLowerEq]
    exact finiteSign_complexProductCompatible
      (A.eval interval.lower) (B.eval interval.lower)
      (C.eval interval.lower) (D.eval interval.lower)

private theorem upperAdmissible
    {A B C D E H : Polynomial} {interval : Interval}
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
  · simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using data.leftImagUpper
  · simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using data.rightImagUpper
  · simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using data.productImagUpper
  · rw [data.productRealUpperEq, data.productImagUpperEq]
    exact finiteSign_complexProductCompatible
      (A.eval interval.upper) (B.eval interval.upper)
      (C.eval interval.upper) (D.eval interval.upper)

/-- The coordinated two-sided event table proves the complete auxiliary
product formula on one resolved interval. -/
theorem auxiliaryProductFormula
    {A B C D E H : Polynomial} {interval : Interval}
    (data : LocalEventData A B C D E H interval) :
    AuxiliaryProductFormula A B C D E H
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
  rw [finiteSign_productCorrection2_ofCoordinate,
    finiteSign_productCorrection2_ofCoordinate] at table
  unfold AuxiliaryProductFormula auxiliaryEndpointCorrection2
  rw [data.left.index, data.right.index, data.product.index]
  exact table

end LocalEventData

/-- Two-sided local event data with pair-level endpoint safety.  Unlike
`LocalEventData`, this record permits an identically-zero displayed
coordinate; only the two Gaussian factor pairs must remain nonzero. -/
structure PairSafeLocalEventData
    (A B C D E H : Polynomial) (interval : Interval) where
  left : CauchyEventSigns A B interval
  right : CauchyEventSigns C D interval
  product : CauchyEventSigns E H interval
  centersCompatible : FiniteSign.ComplexProductCompatible
    left.numerator left.denominator right.numerator right.denominator
    product.numerator product.denominator
  factorLeftLower : A.eval interval.lower ≠ 0 ∨
    B.eval interval.lower ≠ 0
  factorRightLower : C.eval interval.lower ≠ 0 ∨
    D.eval interval.lower ≠ 0
  factorLeftUpper : A.eval interval.upper ≠ 0 ∨
    B.eval interval.upper ≠ 0
  factorRightUpper : C.eval interval.upper ≠ 0 ∨
    D.eval interval.upper ≠ 0
  productRealLowerEq : E.eval interval.lower =
    A.eval interval.lower * C.eval interval.lower -
      B.eval interval.lower * D.eval interval.lower
  productImagLowerEq : H.eval interval.lower =
    A.eval interval.lower * D.eval interval.lower +
      B.eval interval.lower * C.eval interval.lower
  productRealUpperEq : E.eval interval.upper =
    A.eval interval.upper * C.eval interval.upper -
      B.eval interval.upper * D.eval interval.upper
  productImagUpperEq : H.eval interval.upper =
    A.eval interval.upper * D.eval interval.upper +
      B.eval interval.upper * C.eval interval.upper

namespace PairSafeLocalEventData

/-- The generalized finite event table proves the complete auxiliary product
formula from pair-safe endpoint data, including coordinate-axis rows. -/
theorem auxiliaryProductFormula
    {A B C D E H : Polynomial} {interval : Interval}
    (data : PairSafeLocalEventData A B C D E H interval) :
    AuxiliaryProductFormula A B C D E H
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
    (by simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using
      data.factorLeftLower)
    (by simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using
      data.factorRightLower)
    (by simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using
      data.factorLeftUpper)
    (by simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using
      data.factorRightUpper)
    data.left.numeratorLowerStable data.left.denominatorLowerStable
    data.right.numeratorLowerStable data.right.denominatorLowerStable
    data.product.numeratorLowerStable data.product.denominatorLowerStable
    data.left.numeratorUpperStable data.left.denominatorUpperStable
    data.right.numeratorUpperStable data.right.denominatorUpperStable
    data.product.numeratorUpperStable data.product.denominatorUpperStable
    data.centersCompatible
    (by
      rw [data.productRealLowerEq, data.productImagLowerEq]
      exact finiteSign_complexProductCompatible
        (A.eval interval.lower) (B.eval interval.lower)
        (C.eval interval.lower) (D.eval interval.lower))
    (by
      rw [data.productRealUpperEq, data.productImagUpperEq]
      exact finiteSign_complexProductCompatible
        (A.eval interval.upper) (B.eval interval.upper)
        (C.eval interval.upper) (D.eval interval.upper))
  unfold FiniteSign.LocalEventProductIdentity at table
  rw [finiteSign_productCorrection2_ofCoordinate,
    finiteSign_productCorrection2_ofCoordinate] at table
  unfold AuxiliaryProductFormula auxiliaryEndpointCorrection2
  rw [data.left.index, data.right.index, data.product.index]
  exact table

end PairSafeLocalEventData

end RFAP.CauchyProduct
