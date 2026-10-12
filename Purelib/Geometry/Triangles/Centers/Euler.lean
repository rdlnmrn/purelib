module
import Purelib.Algebra.Group.Basic
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Affine
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Line.PerpendicularBisector
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Circumcenter.Affine
import Purelib.Geometry.Triangles.Circumcenter.Basic
import Purelib.Geometry.Triangles.Circumcenter.Formula
public import Purelib.Geometry.Triangles.Equilateral.Basic
import Purelib.Geometry.Triangles.Median.Affine
public import Purelib.Geometry.Triangles.Orthocenter.Affine
import Purelib.Geometry.Triangles.Orthocenter.Basic
import Purelib.Geometry.Triangles.Orthocenter.Formula
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.LinearAlgebra.Alternating.Bracket.Fin3
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
public import Purelib.Geometry.Plane.Medians
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Geometry
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Point
open Purelib.Geometry.Plane.Point.Affine
open Purelib.Geometry.Triangles
open Purelib.Geometry.Triangles.Circumcenter
open Purelib.Geometry.Triangles.Orthocenter
open Purelib.Geometry.Trigonometry
open Purelib.LinearAlgebra.Alternating.Bracket

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
public section

/-!
# Divine Proportions, Theorem 116: the Euler line

The centroid is an explicit finite affine combination.  The key identity is
the source's relation `G = (2/3)C + (1/3)O`, proved first for the already
formalized affine circumcenter and orthocenter weights and then transferred to
the geometric center constructions.  No completed line or infinite locus is
introduced: collinearity is the finite three-point determinant relation.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Triangles.Centers.Euler

/-- Each pair of the affine center weights satisfies `2αᵢ+βᵢ=1`, the coefficient identity behind the Euler relation. -/
theorem euler_center_weight_identity
    (q₁ q₂ q₃ : K)
    (areaNonzero : QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ ≠ 0) :
    2 * Affine.affineCircumcenterWeight q₁ q₂ q₃
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) +
        Affine.affineOrthocenterWeight q₁ q₂ q₃
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) = 1 := by
  have areaCancel :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ areaNonzero
  unfold Affine.affineCircumcenterWeight Affine.affineOrthocenterWeight
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    2 * (q₁ * (q₂ + q₃ - q₁) *
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹) +
        (q₃ + q₁ - q₂) * (q₁ + q₂ - q₃) *
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ =
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
        (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ := by
          unfold QuadTriple.Basic.archimedesFunction
          ring1
    _ = 1 := areaCancel

/-- The affine relation among the three finite center formulas. -/
theorem euler_affine_center_relation
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    Affine.affineCombination ((2 : K) / 3)
        (Affine.affineCircumcenterPoint first second third)
        ((1 : K) / 3)
        (Affine.affineOrthocenterPoint first second third) =
      centroidPoint first second third := by
  let q₁ := Quadrance.quadrance second third
  let q₂ := Quadrance.quadrance first third
  let q₃ := Quadrance.quadrance first second
  let area := Quadrea.Basic.quadrea first second third
  let c₁ := Affine.affineCircumcenterWeight q₁ q₂ q₃ area
  let c₂ := Affine.affineCircumcenterWeight q₂ q₃ q₁ area
  let c₃ := Affine.affineCircumcenterWeight q₃ q₁ q₂ area
  let o₁ := Affine.affineOrthocenterWeight q₁ q₂ q₃ area
  let o₂ := Affine.affineOrthocenterWeight q₂ q₃ q₁ area
  let o₃ := Affine.affineOrthocenterWeight q₃ q₁ q₂ area
  have areaNonzero : area ≠ 0 :=
    (Quadrea.Basic.quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  have firstWeight : 2 * c₁ + o₁ = 1 := by
    unfold c₁ o₁ area Quadrea.Basic.quadrea q₁ q₂ q₃
    exact Geometry.Triangles.Centers.Euler.euler_center_weight_identity
      (Quadrance.quadrance second third) (Quadrance.quadrance first third)
      (Quadrance.quadrance first second) areaNonzero
  have secondWeight : 2 * c₂ + o₂ = 1 := by
    unfold c₂ o₂ area Quadrea.Basic.quadrea q₁ q₂ q₃
    have rotatedArea :
        QuadTriple.Basic.archimedesFunction (Quadrance.quadrance first third)
            (Quadrance.quadrance first second) (Quadrance.quadrance second third) =
          QuadTriple.Basic.archimedesFunction (Quadrance.quadrance second third)
            (Quadrance.quadrance first third) (Quadrance.quadrance first second) := by
      unfold QuadTriple.Basic.archimedesFunction
      ring1
    have rotatedAreaNonzero :
        QuadTriple.Basic.archimedesFunction (Quadrance.quadrance first third)
          (Quadrance.quadrance first second) (Quadrance.quadrance second third) ≠ 0 := by
      rw [rotatedArea]
      exact areaNonzero
    have result := Geometry.Triangles.Centers.Euler.euler_center_weight_identity
      (Quadrance.quadrance first third) (Quadrance.quadrance first second)
      (Quadrance.quadrance second third) rotatedAreaNonzero
    rw [rotatedArea] at result
    exact result
  have thirdWeight : 2 * c₃ + o₃ = 1 := by
    unfold c₃ o₃ area Quadrea.Basic.quadrea q₁ q₂ q₃
    have rotatedArea :
        QuadTriple.Basic.archimedesFunction (Quadrance.quadrance first second)
            (Quadrance.quadrance second third) (Quadrance.quadrance first third) =
          QuadTriple.Basic.archimedesFunction (Quadrance.quadrance second third)
            (Quadrance.quadrance first third) (Quadrance.quadrance first second) := by
      unfold QuadTriple.Basic.archimedesFunction
      ring1
    have rotatedAreaNonzero :
        QuadTriple.Basic.archimedesFunction (Quadrance.quadrance first second)
          (Quadrance.quadrance second third) (Quadrance.quadrance first third) ≠ 0 := by
      rw [rotatedArea]
      exact areaNonzero
    have result := Geometry.Triangles.Centers.Euler.euler_center_weight_identity
      (Quadrance.quadrance first second) (Quadrance.quadrance second third)
      (Quadrance.quadrance first third) rotatedAreaNonzero
    rw [rotatedArea] at result
    exact result
  apply Plane.Point.ext
  · change
      (2 / 3 : K) * (c₁ * first.x + c₂ * second.x + c₃ * third.x) +
          (1 / 3 : K) *
            (o₁ * first.x + o₂ * second.x + o₃ * third.x) =
        (first.x + second.x + third.x) / 3
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      2 * (3 : K)⁻¹ *
            (c₁ * first.x + c₂ * second.x + c₃ * third.x) +
          (1 * (3 : K)⁻¹) *
            (o₁ * first.x + o₂ * second.x + o₃ * third.x) =
        (3 : K)⁻¹ *
          ((2 * c₁ + o₁) * first.x +
            (2 * c₂ + o₂) * second.x +
            (2 * c₃ + o₃) * third.x) := by ring1
      _ = (3 : K)⁻¹ * (first.x + second.x + third.x) := by
        rw [firstWeight, secondWeight, thirdWeight]
        ring1
      _ = (first.x + second.x + third.x) * (3 : K)⁻¹ := by ring1
  · change
      (2 / 3 : K) * (c₁ * first.y + c₂ * second.y + c₃ * third.y) +
          (1 / 3 : K) *
            (o₁ * first.y + o₂ * second.y + o₃ * third.y) =
        (first.y + second.y + third.y) / 3
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      2 * (3 : K)⁻¹ *
            (c₁ * first.y + c₂ * second.y + c₃ * third.y) +
          (1 * (3 : K)⁻¹) *
            (o₁ * first.y + o₂ * second.y + o₃ * third.y) =
        (3 : K)⁻¹ *
          ((2 * c₁ + o₁) * first.y +
            (2 * c₂ + o₂) * second.y +
            (2 * c₃ + o₃) * third.y) := by ring1
      _ = (3 : K)⁻¹ * (first.y + second.y + third.y) := by
        rw [firstWeight, secondWeight, thirdWeight]
        ring1
      _ = (first.y + second.y + third.y) * (3 : K)⁻¹ := by ring1

/-- The source's affine Euler relation for the actual constructed centers. -/
theorem euler_center_relation
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    Affine.affineCombination ((2 : K) / 3)
        (Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear)
        ((1 : K) / 3)
        (Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear) =
      centroidPoint first second third := by
  rw [Affine.affine_circumcenter first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero]
  rw [Affine.affine_orthocenter first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero]
  exact Geometry.Triangles.Centers.Euler.euler_affine_center_relation first second third notCollinear
    twoNonzero

/-- The denominator-cleared coordinate form `2C+O=A₁+A₂+A₃`. Unlike the divided centroid relation, this identity remains
meaningful in characteristic three. -/
theorem euler_center_cleared_coordinates
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    let circumcenter :=
      Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    let orthocenter :=
      Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    2 * circumcenter.x + orthocenter.x = first.x + second.x + third.x ∧
      2 * circumcenter.y + orthocenter.y = first.y + second.y + third.y := by
  dsimp only
  rw [Formula.circumcenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero]
  rw [Formula.orthocenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear]
  let denominator := Fin3.antisymmetricTripleProduct
    first.x second.x third.x first.y second.y third.y
  let circumcenterX := Formula.circumcenterXNumerator first second third
  let circumcenterY := Formula.circumcenterYNumerator first second third
  let orthocenterX := Formula.orthocenterXNumerator first second third
  let orthocenterY := Formula.orthocenterYNumerator first second third
  have denominatorEqualsDeterminant :
      denominator = Incidence.pointDeterminant first second third := by
    exact (Incidence.pointDeterminant_eq_antisymmetricTripleProduct
      first second third).symm
  have denominatorNonzero : denominator ≠ 0 := by
    rw [denominatorEqualsDeterminant]
    intro determinantZero
    apply notCollinear
    exact (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
      determinantZero
  have twiceDenominatorNonzero : 2 * denominator ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero twoNonzero denominatorNonzero
  constructor
  · change 2 * (circumcenterX / (2 * denominator)) +
        orthocenterX / denominator = first.x + second.x + third.x
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right twiceDenominatorNonzero
    calc
      (2 * (circumcenterX / (2 * denominator)) +
          orthocenterX / denominator) * (2 * denominator) =
        2 * ((circumcenterX / (2 * denominator)) * (2 * denominator)) +
          2 * ((orthocenterX / denominator) * denominator) := by ring1
      _ = 2 * circumcenterX + 2 * orthocenterX := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel circumcenterX
            twiceDenominatorNonzero,
          Algebra.Field.ExplicitField.div_mul_cancel orthocenterX denominatorNonzero]
      _ = (first.x + second.x + third.x) * (2 * denominator) := by
        unfold circumcenterX orthocenterX denominator
          Formula.circumcenterXNumerator Formula.orthocenterXNumerator
          Fin3.antisymmetricTripleProduct
        ring1
  · change 2 * (circumcenterY / (2 * denominator)) +
        orthocenterY / denominator = first.y + second.y + third.y
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right twiceDenominatorNonzero
    calc
      (2 * (circumcenterY / (2 * denominator)) +
          orthocenterY / denominator) * (2 * denominator) =
        2 * ((circumcenterY / (2 * denominator)) * (2 * denominator)) +
          2 * ((orthocenterY / denominator) * denominator) := by ring1
      _ = 2 * circumcenterY + 2 * orthocenterY := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel circumcenterY
            twiceDenominatorNonzero,
          Algebra.Field.ExplicitField.div_mul_cancel orthocenterY denominatorNonzero]
      _ = (first.y + second.y + third.y) * (2 * denominator) := by
        unfold circumcenterY orthocenterY denominator
          Formula.circumcenterYNumerator Formula.orthocenterYNumerator
          Fin3.antisymmetricTripleProduct
        ring1

/-- Theorem 116 (Euler line): outside characteristics two and three, the circumcenter, orthocenter, and centroid of a
noncollinear triangle are collinear. -/
theorem euler_line
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (threeNonzero : (3 : K) ≠ 0) :
    Incidence.Collinear
      (Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear)
      (Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear)
      (centroidPoint first second third) := by
  have weightsSum : (2 / 3 : K) + 1 / 3 = 1 := by
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right threeNonzero
    calc
      ((2 / 3 : K) + 1 / 3) * 3 =
          (2 / 3 : K) * 3 + (1 / 3 : K) * 3 := by ring1
      _ = 2 + 1 := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel 2 threeNonzero,
          Algebra.Field.ExplicitField.div_mul_cancel 1 threeNonzero]
      _ = 1 * 3 := by ring1
  have centersCollinear := Affine.collinear_affineCombination
    (Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear)
    (Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear)
    ((2 : K) / 3) ((1 : K) / 3) weightsSum
  rw [Geometry.Triangles.Centers.Euler.euler_center_relation first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero] at centersCollinear
  exact centersCollinear

open Purelib.Geometry.Triangles.Circumcenter.Basic Purelib.Geometry.Triangles.Orthocenter.Basic in
/-- Exercise 18.1: the centroid, circumcenter, and orthocenter coincide precisely for an equilateral noncollinear
triangle. -/
theorem exercise_18_1
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (threeNonzero : (3 : K) ≠ 0) :
    let centroid := centroidPoint first second third
    let circumcenter :=
      Basic.circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    let orthocenter :=
      Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    (centroid = circumcenter ∧ centroid = orthocenter) ↔
      Equilateral.Basic.IsEquilateralTriangle first second third := by
  dsimp only
  let centroid := centroidPoint first second third
  let circumcenter :=
    Basic.circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
  let orthocenter :=
    Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
  have centerFacts := Circumcenter.Basic.circumcenter first second third firstSecondDistinct
    firstThirdDistinct secondThirdDistinct notCollinear twoNonzero
  dsimp only at centerFacts
  constructor
  · rintro ⟨centroidIsCircumcenter, _centroidIsOrthocenter⟩
    have firstSecondRadii :
        Quadrance.quadrance centroid first = Quadrance.quadrance centroid second := by
      unfold centroid
      rw [centroidIsCircumcenter]
      exact centerFacts.2.2.2.1
    have secondThirdRadii :
        Quadrance.quadrance centroid second = Quadrance.quadrance centroid third := by
      unfold centroid
      rw [centroidIsCircumcenter]
      exact centerFacts.2.2.2.2
    have firstDifference :=
      Median.Affine.centroid_quadrance_difference_first_second first second third
        threeNonzero
    have secondDifference :=
      Median.Affine.centroid_quadrance_difference_second_third first second third
        threeNonzero
    have firstQuadrances :
        Quadrance.quadrance first third = Quadrance.quadrance second third := by
      apply Purelib.Algebra.Group.eq_of_sub_eq_zero
      calc
        Quadrance.quadrance first third - Quadrance.quadrance second third =
            3 * (Quadrance.quadrance centroid first - Quadrance.quadrance centroid second) :=
          firstDifference.symm
        _ = 0 := by rw [firstSecondRadii]; ring1
    have secondQuadrances :
        Quadrance.quadrance first second = Quadrance.quadrance first third := by
      apply Purelib.Algebra.Group.eq_of_sub_eq_zero
      calc
        Quadrance.quadrance first second - Quadrance.quadrance first third =
            3 * (Quadrance.quadrance centroid second - Quadrance.quadrance centroid third) :=
          secondDifference.symm
        _ = 0 := by rw [secondThirdRadii]; ring1
    exact ⟨firstQuadrances.symm, secondQuadrances.symm⟩
  · intro equilateral
    have firstDifference :=
      Median.Affine.centroid_quadrance_difference_first_second first second third
        threeNonzero
    have secondDifference :=
      Median.Affine.centroid_quadrance_difference_second_third first second third
        threeNonzero
    have firstDifferenceZero :
        Quadrance.quadrance centroid first - Quadrance.quadrance centroid second = 0 := by
      apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left threeNonzero
      calc
        3 * (Quadrance.quadrance centroid first - Quadrance.quadrance centroid second) =
            Quadrance.quadrance first third - Quadrance.quadrance second third := firstDifference
        _ = 0 := by rw [equilateral.1]; ring1
    have secondDifferenceZero :
        Quadrance.quadrance centroid second - Quadrance.quadrance centroid third = 0 := by
      apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left threeNonzero
      calc
        3 * (Quadrance.quadrance centroid second - Quadrance.quadrance centroid third) =
            Quadrance.quadrance first second - Quadrance.quadrance first third := secondDifference
        _ = 0 := by rw [← equilateral.2]; ring1
    have firstSecondRadii :
        Quadrance.quadrance centroid first = Quadrance.quadrance centroid second :=
      Purelib.Algebra.Group.eq_of_sub_eq_zero firstDifferenceZero
    have secondThirdRadii :
        Quadrance.quadrance centroid second = Quadrance.quadrance centroid third :=
      Purelib.Algebra.Group.eq_of_sub_eq_zero secondDifferenceZero
    have onSecondThird :
        (PerpendicularBisector.perpendicularBisector second third secondThirdDistinct).Contains
          centroid :=
      (PerpendicularBisector.equal_quadrance_iff_perpendicularBisector_contains second third
        centroid secondThirdDistinct twoNonzero).1 secondThirdRadii
    have onFirstThird :
        (PerpendicularBisector.perpendicularBisector first third firstThirdDistinct).Contains
          centroid :=
      (PerpendicularBisector.equal_quadrance_iff_perpendicularBisector_contains first third
        centroid firstThirdDistinct twoNonzero).1
        (firstSecondRadii.trans secondThirdRadii)
    have centroidIsCircumcenter : centroid = circumcenter := by
      unfold circumcenter Basic.circumcenterPoint
      exact Intersection.lineIntersection_unique
        (PerpendicularBisector.perpendicularBisector second third secondThirdDistinct)
        (PerpendicularBisector.perpendicularBisector first third firstThirdDistinct)
        (Circumcenter.Basic.circumcenter_bisectors_not_parallel first second third
          firstThirdDistinct secondThirdDistinct notCollinear)
        centroid onSecondThird onFirstThird
    have relation := Geometry.Triangles.Centers.Euler.euler_center_relation first second third
      firstThirdDistinct secondThirdDistinct notCollinear twoNonzero
    change Affine.affineCombination ((2 : K) / 3) circumcenter ((1 : K) / 3)
      orthocenter = centroid at relation
    rw [← centroidIsCircumcenter] at relation
    have centroidIsOrthocenter : centroid = orthocenter :=
      points_equal_of_euler_affine_fixed centroid orthocenter threeNonzero
        relation
    exact ⟨centroidIsCircumcenter, centroidIsOrthocenter⟩

end Purelib.Geometry.Triangles.Centers.Euler

end

end

end
