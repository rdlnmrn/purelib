module
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Coordinates3.Vector

import Purelib.Algebra.Quaternion.Projective.Basic

import Purelib.Geometry.Rotations.Basic
public import Purelib.Geometry.Rotations.Rational.Order
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Algebra.Quaternion.Projective.SquareClass
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.NumberTheory.SquareClass.Rational.Signature
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

@[expose] public section

/-!
# Checked examples for the five rational finite orders

Each example is one displayed rational proportion.  Its certificate stores
the requested identity power and proves every smaller positive power
nonidentity by a finite case split.  Evaluating the common classifier then
recovers each of the five table rows.
-/

namespace formalisations.RationalRotations.Chapters

open Purelib.Geometry.Rotations.Basic
open Purelib.LinearAlgebra.Coordinates3

namespace RotationOrderExamples

open Purelib.Geometry.Rotations.Rational.Order.RotationOrder

/-- The canonical constructive rational coefficient type for the finite-order rotations. -/
abbrev Scalar := Fraction.Rational

/-- The coordinate axis (1, 0, 0). -/
def axis : Vector3 Fraction.Rational := ⟨1, 0, 0⟩

/-- The diagonal axis (1, 1, 1). -/
def diagonalAxis : Vector3 Fraction.Rational := ⟨1, 1, 1⟩

/-- The projective identity proportion (1:0:0:0). -/
def orderOneProportion : Algebra.Quaternion.Projective.Basic.NonNullProportion Fraction.Rational where
  scalar := 1
  vector := Vector3.zero
  normNonzero := by
    change (1 : Fraction.Rational) ≠ 0
    decide

/-- The coordinate half-turn proportion (0:1:0:0). -/
def orderTwoProportion : Algebra.Quaternion.Projective.Basic.NonNullProportion Fraction.Rational where
  scalar := 0
  vector := axis
  normNonzero := by
    change (1 : Fraction.Rational) ≠ 0
    decide

/-- The diagonal-axis order-three proportion (1:1:1:1). -/
def orderThreeProportion : Algebra.Quaternion.Projective.Basic.NonNullProportion Fraction.Rational where
  scalar := 1
  vector := RotationOrderExamples.diagonalAxis
  normNonzero := by
    change (4 : Fraction.Rational) ≠ 0
    decide

/-- The coordinate quarter-turn proportion (1:1:0:0). -/
def orderFourProportion : Algebra.Quaternion.Projective.Basic.NonNullProportion Fraction.Rational where
  scalar := 1
  vector := axis
  normNonzero := by
    change (2 : Fraction.Rational) ≠ 0
    decide

/-- The diagonal-axis order-six proportion (3:1:1:1). -/
def orderSixProportion : Algebra.Quaternion.Projective.Basic.NonNullProportion Fraction.Rational where
  scalar := 3
  vector := RotationOrderExamples.diagonalAxis
  normNonzero := by
    change (12 : Fraction.Rational) ≠ 0
    decide

/-- The rational rotation represented by the identity proportion. -/
abbrev orderOneRotation : Rotations.Basic.Rotation Fraction.Rational :=
  (Rotations.Projective.Action.NonNullProportion.rotation RotationOrderExamples.orderOneProportion)

/-- The rational rotation represented by the coordinate half-turn proportion. -/
abbrev orderTwoRotation : Rotations.Basic.Rotation Fraction.Rational :=
  (Rotations.Projective.Action.NonNullProportion.rotation RotationOrderExamples.orderTwoProportion)

/-- The rational rotation represented by the diagonal-axis order-three proportion. -/
abbrev orderThreeRotation : Rotations.Basic.Rotation Fraction.Rational :=
  (Rotations.Projective.Action.NonNullProportion.rotation RotationOrderExamples.orderThreeProportion)

/-- The rational rotation represented by the coordinate quarter-turn proportion. -/
abbrev orderFourRotation : Rotations.Basic.Rotation Fraction.Rational :=
  (Rotations.Projective.Action.NonNullProportion.rotation RotationOrderExamples.orderFourProportion)

/-- The rational rotation represented by the diagonal-axis order-six proportion. -/
abbrev orderSixRotation : Rotations.Basic.Rotation Fraction.Rational :=
  (Rotations.Projective.Action.NonNullProportion.rotation RotationOrderExamples.orderSixProportion)

/-- A certificate that the displayed identity rotation has exact order one.

Retain its computed identity power and the bounded list of smaller powers with their nonidentity obligation. -/
def orderOneCertificate :
    Rotations.Rational.Order.RotationOrder.ExactOrderCertificate RotationOrderExamples.orderOneRotation 1 where
  orderPositive := by decide
  power := rotationPow RotationOrderExamples.orderOneRotation 1
  power_eq := rfl
  power_identity := by decide
  smallerPowers := (List.range 1).map (rotationPow RotationOrderExamples.orderOneRotation)
  smallerPowers_eq := rfl
  smaller_nonidentity := by
    intro exponent positive smaller
    omega

/-- A certificate that the coordinate half-turn has exact order two.

Retain its computed square and exclude every smaller positive exponent by finite evaluation. -/
def orderTwoCertificate :
    Rotations.Rational.Order.RotationOrder.ExactOrderCertificate RotationOrderExamples.orderTwoRotation 2 where
  orderPositive := by decide
  power := rotationPow RotationOrderExamples.orderTwoRotation 2
  power_eq := rfl
  power_identity := by decide
  smallerPowers := (List.range 2).map (rotationPow RotationOrderExamples.orderTwoRotation)
  smallerPowers_eq := rfl
  smaller_nonidentity := by
    intro exponent positive smaller
    have exponentOne : exponent = 1 := by omega
    subst exponent
    decide

/-- A certificate that the displayed diagonal-axis rotation has exact order three.

Retain its computed cube and exclude exponents one and two by finite evaluation. -/
def orderThreeCertificate :
    Rotations.Rational.Order.RotationOrder.ExactOrderCertificate RotationOrderExamples.orderThreeRotation 3 where
  orderPositive := by decide
  power := rotationPow RotationOrderExamples.orderThreeRotation 3
  power_eq := rfl
  power_identity := by decide
  smallerPowers := (List.range 3).map (rotationPow RotationOrderExamples.orderThreeRotation)
  smallerPowers_eq := rfl
  smaller_nonidentity := by
    intro exponent positive smaller
    have exponentCases : exponent = 1 ∨ exponent = 2 := by omega
    rcases exponentCases with exponentOne | exponentTwo
    · subst exponent
      decide
    · subst exponent
      decide

/-- A certificate that the coordinate quarter-turn has exact order four.

Retain its computed fourth power and exclude exponents one through three by finite evaluation. -/
def orderFourCertificate :
    Rotations.Rational.Order.RotationOrder.ExactOrderCertificate RotationOrderExamples.orderFourRotation 4 where
  orderPositive := by decide
  power := rotationPow RotationOrderExamples.orderFourRotation 4
  power_eq := rfl
  power_identity := by decide
  smallerPowers := (List.range 4).map (rotationPow RotationOrderExamples.orderFourRotation)
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

/-- A certificate that the displayed diagonal-axis rotation has exact order six.

Retain its computed sixth power and exclude exponents one through five by finite evaluation. -/
def orderSixCertificate :
    Rotations.Rational.Order.RotationOrder.ExactOrderCertificate RotationOrderExamples.orderSixRotation 6 where
  orderPositive := by decide
  power := rotationPow RotationOrderExamples.orderSixRotation 6
  power_eq := rfl
  power_identity := by decide
  smallerPowers := (List.range 6).map (rotationPow RotationOrderExamples.orderSixRotation)
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
def classificationOrder {rotation : Rotations.Basic.Rotation Fraction.Rational} {order : Nat} :
    Classification rotation order → Nat
  | .orderOne .. => 1
  | .orderTwo .. => 2
  | .orderThree .. => 3
  | .orderFour .. => 4
  | .orderSix .. => 6

/-- The finite-order classifier selects the order-one branch for the identity certificate. -/
theorem orderOne_classification :
    RotationOrderExamples.classificationOrder (classify RotationOrderExamples.orderOneCertificate) = 1 := by decide

/-- The finite-order classifier selects the order-two branch for the half-turn certificate. -/
theorem orderTwo_classification :
    RotationOrderExamples.classificationOrder (classify RotationOrderExamples.orderTwoCertificate) = 2 := by decide

/-- The finite-order classifier selects the order-three branch for the diagonal-axis certificate. -/
theorem orderThree_classification :
    RotationOrderExamples.classificationOrder (classify RotationOrderExamples.orderThreeCertificate) = 3 := by decide

/-- The finite-order classifier selects the order-four branch for the quarter-turn certificate. -/
theorem orderFour_classification :
    RotationOrderExamples.classificationOrder (classify RotationOrderExamples.orderFourCertificate) = 4 := by decide

/-- The finite-order classifier selects the order-six branch for the final diagonal-axis certificate. -/
theorem orderSix_classification :
    RotationOrderExamples.classificationOrder (classify RotationOrderExamples.orderSixCertificate) = 6 := by decide

end RotationOrderExamples

end formalisations.RationalRotations.Chapters
