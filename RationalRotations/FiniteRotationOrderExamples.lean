import RationalRotations.FiniteRotationOrder

/-!
# Checked examples for the five rational finite orders

Each example is one displayed rational proportion.  Its certificate stores
the requested identity power and proves every smaller positive power
nonidentity by a finite case split.  Evaluating the common classifier then
recovers each of the five table rows.
-/

namespace RationalRotations

namespace FiniteRotationOrderExamples

open FiniteRotationOrder

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def axis : Vector Scalar := ⟨1, 0, 0⟩

def diagonalAxis : Vector Scalar := ⟨1, 1, 1⟩

def orderOneProportion : NonNullProportion Scalar where
  scalar := 1
  vector := Vector.zero
  normNonzero := by
    change (1 : Scalar) ≠ 0
    decide

def orderTwoProportion : NonNullProportion Scalar where
  scalar := 0
  vector := axis
  normNonzero := by
    change (1 : Scalar) ≠ 0
    decide

def orderThreeProportion : NonNullProportion Scalar where
  scalar := 1
  vector := diagonalAxis
  normNonzero := by
    change (4 : Scalar) ≠ 0
    decide

def orderFourProportion : NonNullProportion Scalar where
  scalar := 1
  vector := axis
  normNonzero := by
    change (2 : Scalar) ≠ 0
    decide

def orderSixProportion : NonNullProportion Scalar where
  scalar := 3
  vector := diagonalAxis
  normNonzero := by
    change (12 : Scalar) ≠ 0
    decide

abbrev orderOneRotation : Rotation Scalar := orderOneProportion.rotation

abbrev orderTwoRotation : Rotation Scalar := orderTwoProportion.rotation

abbrev orderThreeRotation : Rotation Scalar := orderThreeProportion.rotation

abbrev orderFourRotation : Rotation Scalar := orderFourProportion.rotation

abbrev orderSixRotation : Rotation Scalar := orderSixProportion.rotation

def orderOneCertificate :
    ExactFiniteOrderCertificate orderOneRotation 1 where
  orderPositive := by decide
  power := rotationPow orderOneRotation 1
  power_eq := rfl
  power_identity := by decide
  smallerPowers := (List.range 1).map (rotationPow orderOneRotation)
  smallerPowers_eq := rfl
  smaller_nonidentity := by
    intro exponent positive smaller
    omega

def orderTwoCertificate :
    ExactFiniteOrderCertificate orderTwoRotation 2 where
  orderPositive := by decide
  power := rotationPow orderTwoRotation 2
  power_eq := rfl
  power_identity := by decide
  smallerPowers := (List.range 2).map (rotationPow orderTwoRotation)
  smallerPowers_eq := rfl
  smaller_nonidentity := by
    intro exponent positive smaller
    have exponentOne : exponent = 1 := by omega
    subst exponent
    decide

def orderThreeCertificate :
    ExactFiniteOrderCertificate orderThreeRotation 3 where
  orderPositive := by decide
  power := rotationPow orderThreeRotation 3
  power_eq := rfl
  power_identity := by decide
  smallerPowers := (List.range 3).map (rotationPow orderThreeRotation)
  smallerPowers_eq := rfl
  smaller_nonidentity := by
    intro exponent positive smaller
    have exponentCases : exponent = 1 ∨ exponent = 2 := by omega
    rcases exponentCases with exponentOne | exponentTwo
    · subst exponent
      decide
    · subst exponent
      decide

def orderFourCertificate :
    ExactFiniteOrderCertificate orderFourRotation 4 where
  orderPositive := by decide
  power := rotationPow orderFourRotation 4
  power_eq := rfl
  power_identity := by decide
  smallerPowers := (List.range 4).map (rotationPow orderFourRotation)
  smallerPowers_eq := rfl
  smaller_nonidentity := by
    intro exponent positive smaller
    have exponentCases : exponent = 1 ∨ exponent = 2 ∨ exponent = 3 := by
      omega
    rcases exponentCases with exponentOne | exponentTwo | exponentThree
    · subst exponent
      decide
    · subst exponent
      decide
    · subst exponent
      decide

def orderSixCertificate :
    ExactFiniteOrderCertificate orderSixRotation 6 where
  orderPositive := by decide
  power := rotationPow orderSixRotation 6
  power_eq := rfl
  power_identity := by decide
  smallerPowers := (List.range 6).map (rotationPow orderSixRotation)
  smallerPowers_eq := rfl
  smaller_nonidentity := by
    intro exponent positive smaller
    have exponentCases : exponent = 1 ∨ exponent = 2 ∨ exponent = 3 ∨
        exponent = 4 ∨ exponent = 5 := by omega
    rcases exponentCases with exponentOne | exponentTwo | exponentThree |
        exponentFour | exponentFive
    · subst exponent
      decide
    · subst exponent
      decide
    · subst exponent
      decide
    · subst exponent
      decide
    · subst exponent
      decide

/-- A small executable projection used to regression-check the classifier's
constructor choice. -/
def classificationOrder {rotation : Rotation Scalar} {order : Nat} :
    Classification rotation order → Nat
  | .orderOne .. => 1
  | .orderTwo .. => 2
  | .orderThree .. => 3
  | .orderFour .. => 4
  | .orderSix .. => 6

theorem orderOne_classification :
    classificationOrder (classify orderOneCertificate) = 1 := by decide

theorem orderTwo_classification :
    classificationOrder (classify orderTwoCertificate) = 2 := by decide

theorem orderThree_classification :
    classificationOrder (classify orderThreeCertificate) = 3 := by decide

theorem orderFour_classification :
    classificationOrder (classify orderFourCertificate) = 4 := by decide

theorem orderSix_classification :
    classificationOrder (classify orderSixCertificate) = 6 := by decide

end FiniteRotationOrderExamples

end RationalRotations
