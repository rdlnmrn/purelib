module
public import Purelib.Data.Rat.Additive.TriangleBounds
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.PositiveMul
import Purelib.Geometry.Plane.Line.Affine
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Circumcenter.Affine
import Purelib.Geometry.Triangles.Circumcenter.Basic
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Additive.TriangleBounds

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Triangles.Circumcenter

section
@[expose] public section

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

namespace Purelib.Geometry.Triangles.Circumcenter.Rational.Containment

section

/-- A point lies on the closed triangle when it has displayed nonnegative barycentric weights. -/
def LiesOnTriangle
    (point first second third : Geometry.Plane.Point Fraction.Rational) : Prop :=
  ∃ firstWeight secondWeight thirdWeight : Fraction.Rational,
    0 ≤ firstWeight ∧ 0 ≤ secondWeight ∧ 0 ≤ thirdWeight ∧
      firstWeight + secondWeight + thirdWeight = 1 ∧
      Affine.affineCombinationThree firstWeight first secondWeight second
        thirdWeight third = point

/-- A circumcenter weight with positive opposite quadrance and positive quadrea is nonnegative exactly when that
quadrance is at most the sum of the other two. -/
theorem affineCircumcenterWeight_nonnegative_iff
    (opposite adjacentOne adjacentTwo area : Fraction.Rational)
    (oppositePositive : 0 < opposite) (areaPositive : 0 < area) :
    0 ≤ Affine.affineCircumcenterWeight opposite adjacentOne adjacentTwo area ↔
      opposite ≤ adjacentOne + adjacentTwo := by
  have areaNonzero : area ≠ 0 := Fraction.Order.rational_ne_zero_of_positive areaPositive
  constructor
  · intro weightNonnegative
    have productNonnegative :
        0 ≤ Affine.affineCircumcenterWeight opposite adjacentOne adjacentTwo area *
          area :=
      Fraction.Order.Arithmetic.mul_nonneg_direct weightNonnegative
        (Fraction.Order.Arithmetic.le_of_lt_direct areaPositive)
    unfold Affine.affineCircumcenterWeight at productNonnegative
    rw [Algebra.Field.ExplicitField.div_mul_cancel _ areaNonzero]
      at productNonnegative
    have differenceNonnegative :=
      (Fraction.Order.PositiveMul.nonnegative_mul_iff_of_positive opposite
        (adjacentOne + adjacentTwo - opposite) oppositePositive).1
        productNonnegative
    exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      differenceNonnegative
  · intro bound
    have differenceNonnegative :
        0 ≤ adjacentOne + adjacentTwo - opposite :=
      Fraction.Order.Arithmetic.sub_nonneg_direct bound
    unfold Affine.affineCircumcenterWeight
    exact Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.le_of_lt_direct oppositePositive)
        differenceNonnegative)
      (Fraction.Order.Arithmetic.le_of_lt_direct areaPositive)

/-- The rational circumcenter lies in the closed triangle exactly when the three weak quadrance bounds hold.

The triangle is noncollinear, with positive side quadrances and positive quadrea; barycentric uniqueness identifies the
displayed nonnegative weights. -/
theorem problem_2
    (first second third : Geometry.Plane.Point Fraction.Rational)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (firstQuadrancePositive : 0 < Quadrance.quadrance second third)
    (secondQuadrancePositive : 0 < Quadrance.quadrance first third)
    (thirdQuadrancePositive : 0 < Quadrance.quadrance first second)
    (areaPositive : 0 < Quadrea.Basic.quadrea first second third) :
    LiesOnTriangle
        (Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear)
        first second third ↔
      TriangleSpreadRules.AcuteQuadranceBounds
        (Quadrance.quadrance second third)
        (Quadrance.quadrance first third)
        (Quadrance.quadrance first second) := by
  let q₁ := Quadrance.quadrance second third
  let q₂ := Quadrance.quadrance first third
  let q₃ := Quadrance.quadrance first second
  let area := Quadrea.Basic.quadrea first second third
  let firstWeight := Affine.affineCircumcenterWeight q₁ q₂ q₃ area
  let secondWeight := Affine.affineCircumcenterWeight q₂ q₃ q₁ area
  let thirdWeight := Affine.affineCircumcenterWeight q₃ q₁ q₂ area
  have weightsSum : firstWeight + secondWeight + thirdWeight = 1 := by
    unfold firstWeight secondWeight thirdWeight q₁ q₂ q₃ area Quadrea.Basic.quadrea
    exact Affine.affine_circumcenter_weights_sum _ _ _
      (Fraction.Order.rational_ne_zero_of_positive areaPositive)
  have circumcenterFormula := Affine.affine_circumcenter first second third
    firstThirdDistinct secondThirdDistinct notCollinear
    (by decide : (2 : Fraction.Rational) ≠ 0)
  have firstWeightCriterion : 0 ≤ firstWeight ↔ q₁ ≤ q₂ + q₃ := by
    unfold firstWeight
    exact affineCircumcenterWeight_nonnegative_iff q₁ q₂ q₃ area
      firstQuadrancePositive areaPositive
  have secondWeightCriterion : 0 ≤ secondWeight ↔ q₂ ≤ q₃ + q₁ := by
    unfold secondWeight
    exact affineCircumcenterWeight_nonnegative_iff q₂ q₃ q₁ area
      secondQuadrancePositive areaPositive
  have thirdWeightCriterion : 0 ≤ thirdWeight ↔ q₃ ≤ q₁ + q₂ := by
    unfold thirdWeight
    exact affineCircumcenterWeight_nonnegative_iff q₃ q₁ q₂ area
      thirdQuadrancePositive areaPositive
  constructor
  · rintro ⟨otherFirstWeight, otherSecondWeight, otherThirdWeight,
      otherFirstNonnegative, otherSecondNonnegative,
      otherThirdNonnegative, otherWeightsSum, pointEquation⟩
    have canonicalPoint :
        Affine.affineCombinationThree firstWeight first secondWeight second
            thirdWeight third =
          Affine.affineCircumcenterPoint first second third := by
      rfl
    have pointsEqual :
        Affine.affineCombinationThree firstWeight first secondWeight second
            thirdWeight third =
          Affine.affineCombinationThree otherFirstWeight first
            otherSecondWeight second otherThirdWeight third := by
      calc
        Affine.affineCombinationThree firstWeight first secondWeight second
            thirdWeight third =
            Affine.affineCircumcenterPoint first second third := canonicalPoint
        _ = Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
              secondThirdDistinct notCollinear := circumcenterFormula.symm
        _ = Affine.affineCombinationThree otherFirstWeight first
              otherSecondWeight second otherThirdWeight third :=
            pointEquation.symm
    have weightsEqual := Affine.affineCombinationThree_weights_unique
      first second third notCollinear weightsSum otherWeightsSum pointsEqual
    have firstNonnegative : 0 ≤ firstWeight := by
      rw [weightsEqual.1]
      exact otherFirstNonnegative
    have secondNonnegative : 0 ≤ secondWeight := by
      rw [weightsEqual.2.1]
      exact otherSecondNonnegative
    have thirdNonnegative : 0 ≤ thirdWeight := by
      rw [weightsEqual.2.2]
      exact otherThirdNonnegative
    unfold TriangleSpreadRules.AcuteQuadranceBounds
    change q₃ ≤ q₁ + q₂ ∧ q₁ ≤ q₂ + q₃ ∧ q₂ ≤ q₃ + q₁
    exact ⟨thirdWeightCriterion.1 thirdNonnegative,
      firstWeightCriterion.1 firstNonnegative,
      secondWeightCriterion.1 secondNonnegative⟩
  · intro acute
    unfold TriangleSpreadRules.AcuteQuadranceBounds at acute
    change q₃ ≤ q₁ + q₂ ∧ q₁ ≤ q₂ + q₃ ∧ q₂ ≤ q₃ + q₁ at acute
    have firstNonnegative : 0 ≤ firstWeight :=
      firstWeightCriterion.2 acute.2.1
    have secondNonnegative : 0 ≤ secondWeight :=
      secondWeightCriterion.2 acute.2.2
    have thirdNonnegative : 0 ≤ thirdWeight :=
      thirdWeightCriterion.2 acute.1
    refine ⟨firstWeight, secondWeight, thirdWeight, firstNonnegative,
      secondNonnegative, thirdNonnegative, weightsSum, ?_⟩
    calc
      Affine.affineCombinationThree firstWeight first secondWeight second
          thirdWeight third = Affine.affineCircumcenterPoint first second third := rfl
      _ = Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear := circumcenterFormula.symm
end
end Purelib.Geometry.Triangles.Circumcenter.Rational.Containment

end
