module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Ratio
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Circumcenter.Formula
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.LinearAlgebra.Alternating.Bracket.Fin3

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Triangles.Circumcenter.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Algebra.Field
open Purelib.Geometry
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Point
open Purelib.Geometry.Triangles
open Purelib.Geometry.Triangles.Circumcenter
open Purelib.Geometry.Trigonometry
open Purelib.LinearAlgebra.Alternating.Bracket

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

public section

/-!
# Divine Proportions, §12.2: the affine circumcenter

The three weights below are exactly the cyclic quadrance expressions printed
in Theorem 84.  Their normalization is a finite Archimedes-polynomial
identity.  Coordinate cross-multiplication then identifies the weighted point
with the antisymmetric formula of Theorem 83.
-/

section

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Triangles.Circumcenter.Affine

/-- One cyclic weight `Qᵢ(Qⱼ+Qₖ-Qᵢ)/𝒜` from Theorem 84. -/
@[expose] def affineCircumcenterWeight
    (opposite adjacentOne adjacentTwo area : K) : K :=
  opposite * (adjacentOne + adjacentTwo - opposite) / area

/-- The three weights sum to one; this is also the content of the source's Exercise 5.14 specialized to the triangle
quadrea. -/
theorem affine_circumcenter_weights_sum
    [Nontrivial K]
    (q₁ q₂ q₃ : K)
    (areaNonzero : QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ ≠ 0) :
    Affine.affineCircumcenterWeight q₁ q₂ q₃
        (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) +
      Affine.affineCircumcenterWeight q₂ q₃ q₁
        (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) +
      Affine.affineCircumcenterWeight q₃ q₁ q₂
        (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) = 1 := by
  have areaCancel :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ areaNonzero
  unfold Affine.affineCircumcenterWeight
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    q₁ * (q₂ + q₃ - q₁) * (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ +
          q₂ * (q₃ + q₁ - q₂) * (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ +
          q₃ * (q₁ + q₂ - q₃) * (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ =
        QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ := by
            unfold QuadTriple.Basic.archimedesFunction
            ring1
    _ = 1 := areaCancel

/-- The affine combination of the vertices with cyclic circumcenter weights.

Each weight is computed from the opposite side quadrance and the triangle quadrea; nonzero quadrea is required by the
subsequent normalization theorem. -/
@[expose] def affineCircumcenterPoint (first second third : Plane.Point K) : Plane.Point K :=
  let q₁ := Quadrance.quadrance second third
  let q₂ := Quadrance.quadrance first third
  let q₃ := Quadrance.quadrance first second
  let area := Quadrea.Basic.quadrea first second third
  Affine.affineCombinationThree
    (Geometry.Triangles.Circumcenter.Affine.affineCircumcenterWeight q₁ q₂ q₃ area) first
    (Geometry.Triangles.Circumcenter.Affine.affineCircumcenterWeight q₂ q₃ q₁ area) second
    (Geometry.Triangles.Circumcenter.Affine.affineCircumcenterWeight q₃ q₁ q₂ area) third

/-- The weights defining `affineCircumcenterPoint` really are affine. -/
theorem affineCircumcenterPoint_weights_sum
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    let q₁ := Quadrance.quadrance second third
    let q₂ := Quadrance.quadrance first third
    let q₃ := Quadrance.quadrance first second
    let area := Quadrea.Basic.quadrea first second third
    Geometry.Triangles.Circumcenter.Affine.affineCircumcenterWeight q₁ q₂ q₃ area +
      Geometry.Triangles.Circumcenter.Affine.affineCircumcenterWeight q₂ q₃ q₁ area +
      Geometry.Triangles.Circumcenter.Affine.affineCircumcenterWeight q₃ q₁ q₂ area = 1 := by
  dsimp only
  have areaNonzero : Quadrea.Basic.quadrea first second third ≠ 0 :=
    (Quadrea.Basic.quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  unfold Quadrea.Basic.quadrea at areaNonzero ⊢
  exact Geometry.Triangles.Circumcenter.Affine.affine_circumcenter_weights_sum
    (Quadrance.quadrance second third) (Quadrance.quadrance first third)
    (Quadrance.quadrance first second) areaNonzero

/-- The geometric circumcenter equals its explicit affine combination of the three vertices.

The triangle is noncollinear and two is nonzero, so its quadrea and the coordinate-formula denominators may be
cancelled. -/
theorem affine_circumcenter
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear =
      Affine.affineCircumcenterPoint first second third := by
  rw [Formula.circumcenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero]
  let determinant := Incidence.pointDeterminant first second third
  let xNumerator := Formula.circumcenterXNumerator first second third
  let yNumerator := Formula.circumcenterYNumerator first second third
  let q₁ := Quadrance.quadrance second third
  let q₂ := Quadrance.quadrance first third
  let q₃ := Quadrance.quadrance first second
  let area := Quadrea.Basic.quadrea first second third
  let weightedX :=
    q₁ * (q₂ + q₃ - q₁) * first.x +
      q₂ * (q₃ + q₁ - q₂) * second.x +
      q₃ * (q₁ + q₂ - q₃) * third.x
  let weightedY :=
    q₁ * (q₂ + q₃ - q₁) * first.y +
      q₂ * (q₃ + q₁ - q₂) * second.y +
      q₃ * (q₁ + q₂ - q₃) * third.y
  have determinantNonzero : determinant ≠ 0 := by
    intro determinantZero
    apply notCollinear
    exact (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
      determinantZero
  have areaNonzero : area ≠ 0 :=
    (Quadrea.Basic.quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  have antisymmetricDenominator :
      Fin3.antisymmetricTripleProduct
          first.x second.x third.x first.y second.y third.y =
        determinant := by
    exact (Incidence.pointDeterminant_eq_antisymmetricTripleProduct
      first second third).symm
  have formulaDenominatorNonzero :
      2 * Fin3.antisymmetricTripleProduct
          first.x second.x third.x first.y second.y third.y ≠ 0 := by
    rw [antisymmetricDenominator]
    exact Algebra.Field.ExplicitField.mul_ne_zero twoNonzero determinantNonzero
  have affineX : (Affine.affineCircumcenterPoint first second third).x =
      weightedX / area := by
    unfold Affine.affineCircumcenterPoint Affine.affineCombinationThree
      Geometry.Triangles.Circumcenter.Affine.affineCircumcenterWeight weightedX q₁ q₂ q₃ area
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1
  have affineY : (Affine.affineCircumcenterPoint first second third).y =
      weightedY / area := by
    unfold Affine.affineCircumcenterPoint Affine.affineCombinationThree
      Geometry.Triangles.Circumcenter.Affine.affineCircumcenterWeight weightedY q₁ q₂ q₃ area
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1
  have xCross :
      xNumerator * area =
        weightedX *
          (2 * Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) := by
    rw [antisymmetricDenominator]
    unfold area
    rw [Quadrea.Basic.quadrea_coordinate_formula first second third]
    unfold weightedX xNumerator Formula.circumcenterXNumerator
      Fin3.antisymmetricTripleProduct q₁ q₂ q₃ Quadrance.quadrance determinant
      Incidence.pointDeterminant
    ring1
  have yCross :
      yNumerator * area =
        weightedY *
          (2 * Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) := by
    rw [antisymmetricDenominator]
    unfold area
    rw [Quadrea.Basic.quadrea_coordinate_formula first second third]
    unfold weightedY yNumerator Formula.circumcenterYNumerator
      Fin3.antisymmetricTripleProduct q₁ q₂ q₃ Quadrance.quadrance determinant
      Incidence.pointDeterminant
    ring1
  apply Plane.Point.ext
  · change
      xNumerator /
          (2 * Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) =
        (Affine.affineCircumcenterPoint first second third).x
    rw [affineX]
    exact Ratio.ratio_eq_of_cross_product formulaDenominatorNonzero areaNonzero
      xCross
  · change
      yNumerator /
          (2 * Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) =
        (Affine.affineCircumcenterPoint first second third).y
    rw [affineY]
    exact Ratio.ratio_eq_of_cross_product formulaDenominatorNonzero areaNonzero
      yCross

end Purelib.Geometry.Triangles.Circumcenter.Affine

end

end
