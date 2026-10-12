module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Rat.Additive.TriangleBounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Additive.TriangleBounds

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, Chapter 22: three-dimensional problems

The source explicitly describes its three-dimensional treatment as informal.
Here every assertion is split into finite Cartesian dot-product algebra and
the scalar identities used in the printed solutions.  Algebraic roots and
distances are supplied as witnesses; no completed real-number construction is
introduced.
-/

namespace Purelib.Geometry.Space.Tetrahedron.Right.Quadrances

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Problem 12, the three-dimensional Pythagoras theorem for quadrea. The three pairwise perpendicular leg quadrances
are `P₁,P₂,P₃`; expanding Archimedes' formula gives the sum of the three right-face quadreas. -/
theorem problem_12 (P₁ P₂ P₃ : K) :
    QuadTriple.Basic.archimedesFunction (P₂ + P₃) (P₁ + P₃) (P₁ + P₂) =
      4 * P₂ * P₃ + 4 * P₁ * P₃ + 4 * P₁ * P₂ := by
  unfold QuadTriple.Basic.archimedesFunction
  ring1

/-- The side-quadrance equations of a right tetrahedron. -/
def RightTetrahedronQuadrances
    (Q₁ Q₂ Q₃ P₁ P₂ P₃ : K) : Prop :=
  Q₁ = P₂ + P₃ ∧ Q₂ = P₁ + P₃ ∧ Q₃ = P₁ + P₂

/-- The three perpendicular-leg quadrances are uniquely recovered by finite linear combinations of the face quadrances.
-/
theorem rightTetrahedronQuadrances_recovered
    (Q₁ Q₂ Q₃ P₁ P₂ P₃ : K)
    (relations : RightTetrahedronQuadrances Q₁ Q₂ Q₃ P₁ P₂ P₃) :
    2 * P₁ = Q₂ + Q₃ - Q₁ ∧
      2 * P₂ = Q₁ + Q₃ - Q₂ ∧
      2 * P₃ = Q₁ + Q₂ - Q₃ := by
  rcases relations with ⟨r₁, r₂, r₃⟩
  rw [r₁, r₂, r₃]
  constructor
  · ring1
  constructor <;> ring1

/-- The first assertion of Exercise 22.3: positive perpendicular-leg quadrances force the opposite face to satisfy all
three acute inequalities. -/
theorem exercise_22_3_acute
    (Q₁ Q₂ Q₃ P₁ P₂ P₃ : Fraction.Rational)
    (relations : RightTetrahedronQuadrances Q₁ Q₂ Q₃ P₁ P₂ P₃)
    (firstPositive : 0 < P₁) (secondPositive : 0 < P₂)
    (thirdPositive : 0 < P₃) :
    TriangleSpreadRules.AcuteQuadranceBounds Q₁ Q₂ Q₃ := by
  rcases relations with ⟨r₁, r₂, r₃⟩
  have firstNonnegative :=
    Fraction.Order.Arithmetic.le_of_lt_direct firstPositive
  have secondNonnegative :=
    Fraction.Order.Arithmetic.le_of_lt_direct secondPositive
  have thirdNonnegative :=
    Fraction.Order.Arithmetic.le_of_lt_direct thirdPositive
  unfold TriangleSpreadRules.AcuteQuadranceBounds
  rw [r₁, r₂, r₃]
  constructor
  · have doubledThird : (0 : Fraction.Rational) ≤ P₃ + P₃ :=
      Fraction.Order.Arithmetic.add_le_add_direct
        thirdNonnegative thirdNonnegative
    calc
      P₁ + P₂ = 0 + (P₁ + P₂) := by ring1
      _ ≤ (P₃ + P₃) + (P₁ + P₂) :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          doubledThird (P₁ + P₂)
      _ = (P₂ + P₃) + (P₁ + P₃) := by ring1
  constructor
  · have doubledFirst : (0 : Fraction.Rational) ≤ P₁ + P₁ :=
      Fraction.Order.Arithmetic.add_le_add_direct
        firstNonnegative firstNonnegative
    calc
      P₂ + P₃ = 0 + (P₂ + P₃) := by ring1
      _ ≤ (P₁ + P₁) + (P₂ + P₃) :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          doubledFirst (P₂ + P₃)
      _ = (P₁ + P₃) + (P₁ + P₂) := by ring1
  · have doubledSecond : (0 : Fraction.Rational) ≤ P₂ + P₂ :=
      Fraction.Order.Arithmetic.add_le_add_direct
        secondNonnegative secondNonnegative
    calc
      P₁ + P₃ = 0 + (P₁ + P₃) := by ring1
      _ ≤ (P₂ + P₂) + (P₁ + P₃) :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          doubledSecond (P₁ + P₃)
      _ = (P₁ + P₂) + (P₂ + P₃) := by ring1
end
end Purelib.Geometry.Space.Tetrahedron.Right.Quadrances

end
