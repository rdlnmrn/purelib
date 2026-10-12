module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Ratio
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Orthocenter.Formula
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.LinearAlgebra.Alternating.Bracket.Fin3

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Triangles.Orthocenter.Basic
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
open Purelib.Geometry.Triangles.Orthocenter
open Purelib.Geometry.Trigonometry
open Purelib.LinearAlgebra.Alternating.Bracket

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

public section

/-!
# Divine Proportions, §12.4: the affine orthocenter

The cyclic beta weights are executable rational expressions in the three
quadrances and quadrea.  Their sum-to-one identity is proved separately, then
coordinate cross-products identify their affine combination with the
orthocenter formula of Theorem 86.
-/

section

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Triangles.Orthocenter.Affine

/-- One cyclic weight `(Qₖ+Qᵢ-Qⱼ)(Qᵢ+Qⱼ-Qₖ)/𝒜` from Theorem 87. -/
@[expose] def affineOrthocenterWeight
    (current next previous area : K) : K :=
  (previous + current - next) * (current + next - previous) / area

/-- The three beta weights sum to one. This is also the specialization of the source's Exercise 5.15 used in the printed
proof. -/
theorem affine_orthocenter_weights_sum
    [Nontrivial K]
    (q₁ q₂ q₃ : K)
    (areaNonzero : QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ ≠ 0) :
    Affine.affineOrthocenterWeight q₁ q₂ q₃
        (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) +
      Affine.affineOrthocenterWeight q₂ q₃ q₁
        (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) +
      Affine.affineOrthocenterWeight q₃ q₁ q₂
        (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) = 1 := by
  have areaCancel :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ areaNonzero
  unfold Affine.affineOrthocenterWeight
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    (q₃ + q₁ - q₂) * (q₁ + q₂ - q₃) *
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ +
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) *
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ +
        (q₂ + q₃ - q₁) * (q₃ + q₁ - q₂) *
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ =
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
        (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)⁻¹ := by
          unfold QuadTriple.Basic.archimedesFunction
          ring1
    _ = 1 := areaCancel

/-- The affine combination of the vertices with cyclic orthocenter weights.

Each weight is the product of two signed quadrance sums divided by quadrea. -/
@[expose] def affineOrthocenterPoint (first second third : Plane.Point K) : Plane.Point K :=
  let q₁ := Quadrance.quadrance second third
  let q₂ := Quadrance.quadrance first third
  let q₃ := Quadrance.quadrance first second
  let area := Quadrea.Basic.quadrea first second third
  Affine.affineCombinationThree
    (Geometry.Triangles.Orthocenter.Affine.affineOrthocenterWeight q₁ q₂ q₃ area) first
    (Geometry.Triangles.Orthocenter.Affine.affineOrthocenterWeight q₂ q₃ q₁ area) second
    (Geometry.Triangles.Orthocenter.Affine.affineOrthocenterWeight q₃ q₁ q₂ area) third

/-- The weights defining `affineOrthocenterPoint` really are affine. -/
theorem affineOrthocenterPoint_weights_sum
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    let q₁ := Quadrance.quadrance second third
    let q₂ := Quadrance.quadrance first third
    let q₃ := Quadrance.quadrance first second
    let area := Quadrea.Basic.quadrea first second third
    Geometry.Triangles.Orthocenter.Affine.affineOrthocenterWeight q₁ q₂ q₃ area +
      Geometry.Triangles.Orthocenter.Affine.affineOrthocenterWeight q₂ q₃ q₁ area +
      Geometry.Triangles.Orthocenter.Affine.affineOrthocenterWeight q₃ q₁ q₂ area = 1 := by
  dsimp only
  have areaNonzero : Quadrea.Basic.quadrea first second third ≠ 0 :=
    (Quadrea.Basic.quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  unfold Quadrea.Basic.quadrea at areaNonzero ⊢
  exact Geometry.Triangles.Orthocenter.Affine.affine_orthocenter_weights_sum
    (Quadrance.quadrance second third) (Quadrance.quadrance first third)
    (Quadrance.quadrance first second) areaNonzero

/-- The geometric orthocenter equals its explicit affine combination of the three vertices.

The triangle is noncollinear and two is nonzero, so the quadrea and coordinate determinant are nonzero. -/
theorem affine_orthocenter
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear =
      Affine.affineOrthocenterPoint first second third := by
  rw [Formula.orthocenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear]
  let determinant := Incidence.pointDeterminant first second third
  let xNumerator := Formula.orthocenterXNumerator first second third
  let yNumerator := Formula.orthocenterYNumerator first second third
  let q₁ := Quadrance.quadrance second third
  let q₂ := Quadrance.quadrance first third
  let q₃ := Quadrance.quadrance first second
  let area := Quadrea.Basic.quadrea first second third
  let weightedX :=
    (q₃ + q₁ - q₂) * (q₁ + q₂ - q₃) * first.x +
      (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) * second.x +
      (q₂ + q₃ - q₁) * (q₃ + q₁ - q₂) * third.x
  let weightedY :=
    (q₃ + q₁ - q₂) * (q₁ + q₂ - q₃) * first.y +
      (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) * second.y +
      (q₂ + q₃ - q₁) * (q₃ + q₁ - q₂) * third.y
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
      Fin3.antisymmetricTripleProduct
          first.x second.x third.x first.y second.y third.y ≠ 0 := by
    rw [antisymmetricDenominator]
    exact determinantNonzero
  have affineX : (Affine.affineOrthocenterPoint first second third).x =
      weightedX / area := by
    unfold Affine.affineOrthocenterPoint Affine.affineCombinationThree
      Geometry.Triangles.Orthocenter.Affine.affineOrthocenterWeight weightedX q₁ q₂ q₃ area
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1
  have affineY : (Affine.affineOrthocenterPoint first second third).y =
      weightedY / area := by
    unfold Affine.affineOrthocenterPoint Affine.affineCombinationThree
      Geometry.Triangles.Orthocenter.Affine.affineOrthocenterWeight weightedY q₁ q₂ q₃ area
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1
  have xCross :
      xNumerator * area =
        weightedX *
          Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y := by
    rw [antisymmetricDenominator]
    unfold area
    rw [Quadrea.Basic.quadrea_coordinate_formula first second third]
    unfold weightedX xNumerator Formula.orthocenterXNumerator
      Fin3.antisymmetricTripleProduct q₁ q₂ q₃ Quadrance.quadrance determinant
      Incidence.pointDeterminant
    ring1
  have yCross :
      yNumerator * area =
        weightedY *
          Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y := by
    rw [antisymmetricDenominator]
    unfold area
    rw [Quadrea.Basic.quadrea_coordinate_formula first second third]
    unfold weightedY yNumerator Formula.orthocenterYNumerator
      Fin3.antisymmetricTripleProduct q₁ q₂ q₃ Quadrance.quadrance determinant
      Incidence.pointDeterminant
    ring1
  apply Plane.Point.ext
  · change
      xNumerator /
          Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y =
        (Affine.affineOrthocenterPoint first second third).x
    rw [affineX]
    exact Ratio.ratio_eq_of_cross_product formulaDenominatorNonzero areaNonzero
      xCross
  · change
      yNumerator /
          Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y =
        (Affine.affineOrthocenterPoint first second third).y
    rw [affineY]
    exact Ratio.ratio_eq_of_cross_product formulaDenominatorNonzero areaNonzero
      yCross

end Purelib.Geometry.Triangles.Orthocenter.Affine

end

end
