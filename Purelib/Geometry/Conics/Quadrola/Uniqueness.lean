module

import Purelib.Algebra.Field.Characteristic.Nonzero
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
import Purelib.Curves.Plane.Conic.Center
public import Purelib.Curves.Plane.Conic.Scale
public import Purelib.Geometry.Conics.Quadrola.Basic
import Purelib.Geometry.Conics.Quadrola.Center
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Purelib.LinearAlgebra.Coordinates2.QuadraticParameters
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib
open Purelib.Algebra.Field
open Purelib.Algebra.Field.Squares
open Purelib.Curves.Plane.Conic
open Purelib.Curves.Plane (Conic)
open Purelib.Geometry
open Purelib.Geometry.Conics.Quadrola
open Purelib.Geometry.Conics.Quadrola
open Purelib.Geometry.Plane.Point
open Purelib.Geometry.Plane.Point.Affine
open Purelib.LinearAlgebra

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

section

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Conics.Quadrola.Uniqueness

/-- Exercise 15.10 (Quadrola uniqueness). When `-1` has no square root, two valid focal presentations of the same
displayed conic proportion have the same associated quadrance and the same unordered pair of foci. Equality of conic
proportions is carried by the explicit nonzero coefficient scale. -/
theorem exercise_15_10 [DecidableEq K]
    (firstFocus₁ firstFocus₂ secondFocus₁ secondFocus₂ : Plane.Point K)
    (firstAssociated secondAssociated : K)
    (firstPresentation :
      Quadrola.Presentation firstFocus₁ firstFocus₂ firstAssociated)
    (secondPresentation :
      Quadrola.Presentation secondFocus₁ secondFocus₂ secondAssociated)
    (eightNonzero : (8 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (noNegativeOneSquare : Squares.NoSquareRootOfNegativeOne (K := K))
    (scale : K) (scaleNonzero : scale ≠ 0)
    (sameConic :
      Scale.CoefficientScale
        (Quadrola.conic firstFocus₁ firstFocus₂ firstAssociated
          firstPresentation.associatedNonzero eightNonzero)
        (Quadrola.conic secondFocus₁ secondFocus₂ secondAssociated
          secondPresentation.associatedNonzero eightNonzero)
        scale) :
    firstAssociated = secondAssociated ∧
      ((firstFocus₁ = secondFocus₁ ∧ firstFocus₂ = secondFocus₂) ∨
        (firstFocus₁ = secondFocus₂ ∧ firstFocus₂ = secondFocus₁)) := by
  let firstConic :=
    Quadrola.conic firstFocus₁ firstFocus₂ firstAssociated
      firstPresentation.associatedNonzero eightNonzero
  let secondConic :=
    Quadrola.conic secondFocus₁ secondFocus₂ secondAssociated
      secondPresentation.associatedNonzero eightNonzero
  let firstMidpoint := Affine.midpoint firstFocus₁ firstFocus₂
  let secondMidpoint := Affine.midpoint secondFocus₁ secondFocus₂
  have firstDiscriminantNonzero : firstConic.centerDiscriminant ≠ 0 := by
    unfold firstConic
    exact Purelib.Geometry.Conics.Quadrola.Center.conic_discriminant_nonzero firstFocus₁ firstFocus₂ firstAssociated
      firstPresentation eightNonzero
  have secondDiscriminantNonzero : secondConic.centerDiscriminant ≠ 0 := by
    unfold secondConic
    exact Purelib.Geometry.Conics.Quadrola.Center.conic_discriminant_nonzero secondFocus₁ secondFocus₂
      secondAssociated secondPresentation eightNonzero
  have firstCenter : firstConic.IsCenter firstMidpoint := by
    unfold firstConic firstMidpoint
    exact Purelib.Geometry.Conics.Quadrola.Center.conic_midpoint_isCenter firstFocus₁ firstFocus₂ firstAssociated
      firstPresentation.associatedNonzero eightNonzero twoNonzero
  have secondCenter : secondConic.IsCenter secondMidpoint := by
    unfold secondConic secondMidpoint
    exact Purelib.Geometry.Conics.Quadrola.Center.conic_midpoint_isCenter secondFocus₁ secondFocus₂ secondAssociated
      secondPresentation.associatedNonzero eightNonzero twoNonzero
  have secondCenterForFirst : firstConic.IsCenter secondMidpoint :=
    sameConic.isCenter secondMidpoint secondCenter
  have firstCenterFormula := Conic.center_eq_centerPoint firstConic firstMidpoint
    firstDiscriminantNonzero firstCenter
  have secondCenterFormula := Conic.center_eq_centerPoint firstConic secondMidpoint
    firstDiscriminantNonzero secondCenterForFirst
  have midpointsEqual : firstMidpoint = secondMidpoint :=
    firstCenterFormula.trans secondCenterFormula.symm
  have firstCanonical :
      firstConic.centerDiscriminant =
        64 * firstConic.evaluate firstMidpoint := by
    unfold firstConic firstMidpoint
    rw [Purelib.Geometry.Conics.Quadrola.Center.conic_centerDiscriminant firstFocus₁ firstFocus₂ firstAssociated
        firstPresentation.associatedNonzero eightNonzero,
      Purelib.Geometry.Conics.Quadrola.Center.conic_evaluate_midpoint firstFocus₁ firstFocus₂ firstAssociated
        firstPresentation.associatedNonzero eightNonzero twoNonzero]
    ring1
  have secondCanonical :
      secondConic.centerDiscriminant =
        64 * secondConic.evaluate secondMidpoint := by
    unfold secondConic secondMidpoint
    rw [Purelib.Geometry.Conics.Quadrola.Center.conic_centerDiscriminant secondFocus₁ secondFocus₂ secondAssociated
        secondPresentation.associatedNonzero eightNonzero,
      Purelib.Geometry.Conics.Quadrola.Center.conic_evaluate_midpoint secondFocus₁ secondFocus₂ secondAssociated
        secondPresentation.associatedNonzero eightNonzero twoNonzero]
    ring1
  have discriminantScale := sameConic.discriminant
  have evaluationScale := sameConic.evaluate secondMidpoint
  have scaleDiscriminants :
      scale ^ 2 * secondConic.centerDiscriminant =
        scale * secondConic.centerDiscriminant := by
    calc
      scale ^ 2 * secondConic.centerDiscriminant =
          firstConic.centerDiscriminant := discriminantScale.symm
      _ = 64 * firstConic.evaluate firstMidpoint := firstCanonical
      _ = 64 * firstConic.evaluate secondMidpoint := by rw [midpointsEqual]
      _ = 64 * (scale * secondConic.evaluate secondMidpoint) := by
        rw [evaluationScale]
      _ = scale * (64 * secondConic.evaluate secondMidpoint) := by ring1
      _ = scale * secondConic.centerDiscriminant := by rw [secondCanonical]
  have discriminantTimesScaleDifference :
      secondConic.centerDiscriminant * (scale ^ 2 - scale) = 0 := by
    calc
      secondConic.centerDiscriminant * (scale ^ 2 - scale) =
          scale ^ 2 * secondConic.centerDiscriminant -
            scale * secondConic.centerDiscriminant := by ring1
      _ = 0 := by rw [scaleDiscriminants]; ring1
  have scalePolynomialZero := Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left
    secondDiscriminantNonzero discriminantTimesScaleDifference
  have scaleTimesDifference : scale * (scale - 1) = 0 := by
    calc
      scale * (scale - 1) = scale ^ 2 - scale := by ring1
      _ = 0 := scalePolynomialZero
  have scaleDifferenceZero :=
    Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left scaleNonzero scaleTimesDifference
  have scaleOne : scale = 1 := by
    calc
      scale = (scale - 1) + 1 := by ring1
      _ = 1 := by rw [scaleDifferenceZero]; ring1
  have dCoefficient : firstConic.d = secondConic.d := by
    calc
      firstConic.d = scale * secondConic.d := sameConic.d
      _ = secondConic.d := by rw [scaleOne]; ring1
  have eCoefficient : firstConic.e = secondConic.e := by
    calc
      firstConic.e = scale * secondConic.e := sameConic.e
      _ = secondConic.e := by rw [scaleOne]; ring1
  have fCoefficient : firstConic.f = secondConic.f := by
    calc
      firstConic.f = scale * secondConic.f := sameConic.f
      _ = secondConic.f := by rw [scaleOne]; ring1
  let firstX := firstFocus₂.x - firstFocus₁.x
  let firstY := firstFocus₂.y - firstFocus₁.y
  let secondX := secondFocus₂.x - secondFocus₁.x
  let secondY := secondFocus₂.y - secondFocus₁.y
  have fourNonzero := Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero_of_eight_ne_zero eightNonzero
  have negativeEightNonzero : (-8 : K) ≠ 0 := by
    intro negativeEightZero
    apply eightNonzero
    calc
      (8 : K) = -(-8) := by ring1
      _ = 0 := by rw [negativeEightZero]; ring1
  have dProductZero :
      (4 : K) * ((firstAssociated - firstX ^ 2) -
        (secondAssociated - secondX ^ 2)) = 0 := by
    calc
      (4 : K) * ((firstAssociated - firstX ^ 2) -
          (secondAssociated - secondX ^ 2)) =
        firstConic.d - secondConic.d := by
          unfold firstConic secondConic firstX secondX Quadrola.conic Quadrola.conicD
          ring1
      _ = 0 := by rw [dCoefficient]; ring1
  have eProductZero :
      (-8 : K) * (firstX * firstY - secondX * secondY) = 0 := by
    calc
      (-8 : K) * (firstX * firstY - secondX * secondY) =
        firstConic.e - secondConic.e := by
          unfold firstConic secondConic firstX firstY secondX secondY Quadrola.conic
            Quadrola.conicE
          ring1
      _ = 0 := by rw [eCoefficient]; ring1
  have fProductZero :
      (4 : K) * ((firstAssociated - firstY ^ 2) -
        (secondAssociated - secondY ^ 2)) = 0 := by
    calc
      (4 : K) * ((firstAssociated - firstY ^ 2) -
          (secondAssociated - secondY ^ 2)) =
        firstConic.f - secondConic.f := by
          unfold firstConic secondConic firstY secondY Quadrola.conic Quadrola.conicF
          ring1
      _ = 0 := by rw [fCoefficient]; ring1
  have dDifferenceZero :=
    Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left fourNonzero dProductZero
  have mixedDifferenceZero :=
    Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left negativeEightNonzero eProductZero
  have fDifferenceZero :=
    Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left fourNonzero fProductZero
  have dEqual :
      firstAssociated - firstX ^ 2 = secondAssociated - secondX ^ 2 := by
    calc
      firstAssociated - firstX ^ 2 =
          ((firstAssociated - firstX ^ 2) -
            (secondAssociated - secondX ^ 2)) +
              (secondAssociated - secondX ^ 2) := by ring1
      _ = secondAssociated - secondX ^ 2 := by
        rw [dDifferenceZero]
        ring1
  have mixedEqual : firstX * firstY = secondX * secondY := by
    calc
      firstX * firstY =
          (firstX * firstY - secondX * secondY) + secondX * secondY := by
        ring1
      _ = secondX * secondY := by rw [mixedDifferenceZero]; ring1
  have fEqual :
      firstAssociated - firstY ^ 2 = secondAssociated - secondY ^ 2 := by
    calc
      firstAssociated - firstY ^ 2 =
          ((firstAssociated - firstY ^ 2) -
            (secondAssociated - secondY ^ 2)) +
              (secondAssociated - secondY ^ 2) := by ring1
      _ = secondAssociated - secondY ^ 2 := by
        rw [fDifferenceZero]
        ring1
  have parameterUniqueness := Coordinates2.QuadraticParameters.Quadrola.parameters_unique_of_quadratic_coefficients
    firstX firstY secondX secondY firstAssociated secondAssociated
      noNegativeOneSquare dEqual mixedEqual fEqual
  refine ⟨parameterUniqueness.1, ?_⟩
  apply endpoint_pairs_of_midpoint_and_difference firstFocus₁ firstFocus₂
    secondFocus₁ secondFocus₂ twoNonzero midpointsEqual
  exact parameterUniqueness.2

end Purelib.Geometry.Conics.Quadrola.Uniqueness

end

end

end

end
