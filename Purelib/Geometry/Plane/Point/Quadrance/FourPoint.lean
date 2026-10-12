module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
public import Purelib.LinearAlgebra.Coordinates4.Determinant
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Quadrilaterals.Basic

open Purelib.Geometry.Trigonometry

section
public section

/-!
# Divine Proportions, Theorem 115: the Four point relation

The Euler function is the explicitly expanded three-by-three determinant from
the source.  Its coordinate proof is a direct polynomial identity for four
displayed points in a two-dimensional plane.  Exercises 17.3--17.6 record the
alternative expansion, the finite Cayley--Menger determinant, the quadratic
form of the relation, and the circumquadrance deduction.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [ExplicitField K]

section

/-- The Euler function `E(Q₁,Q₂,Q₃,P₁,P₂,P₃)`, written as the explicit three-by-three determinant displayed before
Theorem 115. -/
@[expose] def eulerFunction (q₁ q₂ q₃ p₁ p₂ p₃ : K) : K :=
  Quadrilateral.determinantThree
    (2 * p₁) (p₁ + p₂ - q₃) (p₁ + p₃ - q₂)
    (p₁ + p₂ - q₃) (2 * p₂) (p₂ + p₃ - q₁)
    (p₁ + p₃ - q₂) (p₂ + p₃ - q₁) (2 * p₃)

/-- The coordinate polynomial underlying the Four point relation. The point called `base` is translated to the origin in
the source proof; expanding the quadrances performs that finite translation algebraically. -/
theorem euler_coordinate_identity
    (first second third base : Plane.Point K) :
    eulerFunction
      (Quadrance.quadrance second third)
      (Quadrance.quadrance first third)
      (Quadrance.quadrance first second)
      (Quadrance.quadrance first base)
      (Quadrance.quadrance second base)
      (Quadrance.quadrance third base) = 0 := by
  unfold eulerFunction Quadrilateral.determinantThree Quadrance.quadrance
  ring1

/-- The six quadrances between four planar points satisfy Euler's determinant equation.

The relation holds over the displayed field without distinctness or nonzero-denominator assumptions. -/
theorem four_point_relation
    (first second third base : Plane.Point K) :
    eulerFunction
      (Quadrance.quadrance second third)
      (Quadrance.quadrance first third)
      (Quadrance.quadrance first second)
      (Quadrance.quadrance first base)
      (Quadrance.quadrance second base)
      (Quadrance.quadrance third base) = 0 :=
  euler_coordinate_identity first second third base

/-- The explicit symmetric polynomial expansion of Euler's four-point determinant. -/
theorem exercise_17_3 (q₁ q₂ q₃ p₁ p₂ p₃ : K) :
    eulerFunction q₁ q₂ q₃ p₁ p₂ p₃ =
      2 * (4 * p₁ * p₂ * p₃ +
        (p₁ + p₂ - q₃) * (p₁ + p₃ - q₂) *
          (p₂ + p₃ - q₁) -
        p₁ * (p₂ + p₃ - q₁) ^ 2 -
        p₂ * (p₁ + p₃ - q₂) ^ 2 -
        p₃ * (p₁ + p₂ - q₃) ^ 2) := by
  unfold eulerFunction Quadrilateral.determinantThree
  ring1

/-- The explicitly expanded five-by-five Cayley--Menger determinant displayed in Exercise 17.4. -/
@[expose] def fourPointCayleyMenger (q₁ q₂ q₃ p₁ p₂ p₃ : K) :
  K :=
  -p₁ * Quadrilateral.determinantFour
      p₁ q₃ q₂ 1
      p₂ 0 q₁ 1
      p₃ q₁ 0 1
      1 1 1 0 +
    p₂ * Quadrilateral.determinantFour
      p₁ 0 q₂ 1
      p₂ q₃ q₁ 1
      p₃ q₂ 0 1
      1 1 1 0 -
    p₃ * Quadrilateral.determinantFour
      p₁ 0 q₃ 1
      p₂ q₃ 0 1
      p₃ q₂ q₁ 1
      1 1 1 0 +
    Quadrilateral.determinantFour
      p₁ 0 q₃ q₂
      p₂ q₃ 0 q₁
      p₃ q₂ q₁ 0
      1 1 1 1

/-- Euler's three-by-three four-point determinant equals the displayed five-by-five Cayley–Menger determinant. -/
theorem exercise_17_4 (q₁ q₂ q₃ p₁ p₂ p₃ : K) :
    eulerFunction q₁ q₂ q₃ p₁ p₂ p₃ =
      fourPointCayleyMenger q₁ q₂ q₃ p₁ p₂ p₃ := by
  unfold eulerFunction fourPointCayleyMenger Quadrilateral.determinantFour
    Quadrilateral.determinantThree
  ring1

/-- The numerator obtained by multiplying Exercise 17.5's centered quadratic expression by `Q₃`. -/
@[expose] def fourPointQuadraticNumerator
    (q₁ q₂ q₃ p₁ p₂ p₃ : K) : K :=
  q₃ * (2 * p₃ - p₁ - p₂ + q₃ - q₁ - q₂) +
    (q₁ - q₂) * (p₂ - p₁)

/-- The denominator-cleared polynomial identity behind Exercise 17.5. -/
theorem fourPoint_quadratic_identity
    (q₁ q₂ q₃ p₁ p₂ p₃ : K) :
    fourPointQuadraticNumerator q₁ q₂ q₃ p₁ p₂ p₃ ^ 2 -
        QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
          QuadTriple.Basic.archimedesFunction p₁ p₂ q₃ =
      -2 * q₃ * eulerFunction q₁ q₂ q₃ p₁ p₂ p₃ := by
  unfold fourPointQuadraticNumerator eulerFunction Quadrilateral.determinantThree
    QuadTriple.Basic.archimedesFunction
  ring1

/-- Exercise 17.5, corrected: the printed left side omits the factor `2` before `P₃` and the division of the whole
parenthesis by `2`. With those corrections, the Four point relation has the asserted quadratic form. -/
theorem exercise_17_5
    (q₁ q₂ q₃ p₁ p₂ p₃ : K)
    (twoNonzero : (2 : K) ≠ 0)
    (q₃Nonzero : q₃ ≠ 0)
    (relation : eulerFunction q₁ q₂ q₃ p₁ p₂ p₃ = 0) :
    ((2 * p₃ - p₁ - p₂ + q₃ - q₁ - q₂ +
        (q₁ - q₂) * (p₂ - p₁) / q₃) / 2) ^ 2 =
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
          QuadTriple.Basic.archimedesFunction p₁ p₂ q₃ / (4 * q₃ ^ 2) := by
  let offset := 2 * p₃ - p₁ - p₂ + q₃ - q₁ - q₂
  let cross := (q₁ - q₂) * (p₂ - p₁)
  let rawCentered := offset + cross / q₃
  let centered := rawCentered / 2
  let numerator := fourPointQuadraticNumerator q₁ q₂ q₃ p₁ p₂ p₃
  let denominator := 4 * q₃ ^ 2
  have crossCancel : (cross / q₃) * q₃ = cross :=
    ExplicitField.div_mul_cancel cross q₃Nonzero
  have rawCenteredCleared : rawCentered * q₃ = numerator := by
    calc
      rawCentered * q₃ = offset * q₃ + (cross / q₃) * q₃ := by
        unfold rawCentered
        ring1
      _ = offset * q₃ + cross := by rw [crossCancel]
      _ = numerator := by
        unfold numerator fourPointQuadraticNumerator offset cross
        ring1
  have centeredCleared : centered * 2 = rawCentered := by
    exact ExplicitField.div_mul_cancel rawCentered twoNonzero
  have factored :=
    fourPoint_quadratic_identity q₁ q₂ q₃ p₁ p₂ p₃
  have numeratorEquation :
      numerator ^ 2 =
        QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
          QuadTriple.Basic.archimedesFunction p₁ p₂ q₃ := by
    apply Group.eq_of_sub_eq_zero
    calc
      numerator ^ 2 -
          QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
            QuadTriple.Basic.archimedesFunction p₁ p₂ q₃ =
        -2 * q₃ * eulerFunction q₁ q₂ q₃ p₁ p₂ p₃ :=
          factored
      _ = 0 := by rw [relation]; ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    intro fourZero
    apply (ExplicitField.mul_ne_zero twoNonzero twoNonzero)
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  have q₃SquaredNonzero : q₃ ^ 2 ≠ 0 := by
    intro squareZero
    apply (ExplicitField.mul_ne_zero q₃Nonzero q₃Nonzero)
    calc
      q₃ * q₃ = q₃ ^ 2 := by ring1
      _ = 0 := squareZero
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero q₃SquaredNonzero
  change centered ^ 2 =
    (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
      QuadTriple.Basic.archimedesFunction p₁ p₂ q₃) / denominator
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  calc
    centered ^ 2 * denominator =
        ((centered * 2) * q₃) ^ 2 := by
      unfold denominator
      ring1
    _ = (rawCentered * q₃) ^ 2 := by rw [centeredCleared]
    _ = numerator ^ 2 := by rw [rawCenteredCleared]
    _ = QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
        QuadTriple.Basic.archimedesFunction p₁ p₂ q₃ := numeratorEquation
    _ = (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
          QuadTriple.Basic.archimedesFunction p₁ p₂ q₃) / denominator *
        denominator := by
      exact (ExplicitField.div_mul_cancel _ denominatorNonzero).symm
end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end

end
