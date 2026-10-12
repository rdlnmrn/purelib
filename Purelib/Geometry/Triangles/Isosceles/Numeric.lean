module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10: isosceles triangles

The scalar forms isolate the finite cancellations used by the geometric
statements.  They apply uniformly to ratios obtained from rational triangles
or from triangles over explicit finite fields.
-/

namespace Purelib.Geometry.Triangles.Isosceles.Numeric

variable {K : Type*} [ExplicitField K]

/-- Under the spread law, equality of two nonzero side quadrances is equivalent to equality of the opposite spreads.

The first spread is nonzero, so the reverse implication admits cancellation. -/
theorem pons_asinorum
    (q₁ q₂ s₁ s₂ : K)
    (q₁Nonzero : q₁ ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (s₁Nonzero : s₁ ≠ 0)
    (spreadLaw : s₁ / q₁ = s₂ / q₂) :
    q₁ = q₂ ↔ s₁ = s₂ := by
  have crossProduct : s₁ * q₂ = s₂ * q₁ := by
    calc
      s₁ * q₂ = ((s₁ / q₁) * q₁) * q₂ := by
        rw [ExplicitField.div_mul_cancel s₁ q₁Nonzero]
      _ = (s₁ / q₁) * (q₁ * q₂) := by ring1
      _ = (s₂ / q₂) * (q₁ * q₂) := by rw [spreadLaw]
      _ = ((s₂ / q₂) * q₂) * q₁ := by ring1
      _ = s₂ * q₁ := by
        rw [ExplicitField.div_mul_cancel s₂ q₂Nonzero]
  constructor
  · intro quadrancesEqual
    apply ExplicitField.eq_of_mul_eq_mul_right q₂Nonzero
    calc
      s₁ * q₂ = s₂ * q₁ := crossProduct
      _ = s₂ * q₂ := by rw [quadrancesEqual]
  · intro spreadsEqual
    apply ExplicitField.eq_of_mul_eq_mul_left s₁Nonzero
    calc
      s₁ * q₁ = s₂ * q₁ := by rw [spreadsEqual]
      _ = s₁ * q₂ := crossProduct.symm

/-- The unequal side quadrance and opposite spread of an isosceles triangle.

The spread law and equal-spread identity determine both formulas when the displayed quadrances, equal spread and two are
nonzero. -/
theorem isosceles_triangle
    (q q₃ s s₃ : K)
    (qNonzero : q ≠ 0) (q₃Nonzero : q₃ ≠ 0)
    (sNonzero : s ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (spreadLaw : s / q = s₃ / q₃)
    (equalSpreads : s₃ = 4 * s * (1 - s)) :
    q₃ = 4 * q * (1 - s) ∧
      s₃ = (q₃ / q) * (1 - q₃ / (4 * q)) := by
  have crossProduct : s * q₃ = s₃ * q := by
    calc
      s * q₃ = ((s / q) * q) * q₃ := by
        rw [ExplicitField.div_mul_cancel s qNonzero]
      _ = (s / q) * (q * q₃) := by ring1
      _ = (s₃ / q₃) * (q * q₃) := by rw [spreadLaw]
      _ = ((s₃ / q₃) * q₃) * q := by ring1
      _ = s₃ * q := by
        rw [ExplicitField.div_mul_cancel s₃ q₃Nonzero]
  have thirdQuadrance : q₃ = 4 * q * (1 - s) := by
    apply ExplicitField.eq_of_mul_eq_mul_left sNonzero
    calc
      s * q₃ = s₃ * q := crossProduct
      _ = (4 * s * (1 - s)) * q := by rw [equalSpreads]
      _ = s * (4 * q * (1 - s)) := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have fourQNonzero : (4 : K) * q ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero qNonzero
  have firstRatio : q₃ / q = 4 * (1 - s) := by
    apply ExplicitField.eq_of_mul_eq_mul_right qNonzero
    calc
      (q₃ / q) * q = q₃ :=
        ExplicitField.div_mul_cancel q₃ qNonzero
      _ = 4 * q * (1 - s) := thirdQuadrance
      _ = (4 * (1 - s)) * q := by ring1
  have secondRatio : q₃ / (4 * q) = 1 - s := by
    apply ExplicitField.eq_of_mul_eq_mul_right fourQNonzero
    calc
      (q₃ / (4 * q)) * (4 * q) = q₃ :=
        ExplicitField.div_mul_cancel q₃ fourQNonzero
      _ = 4 * q * (1 - s) := thirdQuadrance
      _ = (1 - s) * (4 * q) := by ring1
  constructor
  · exact thirdQuadrance
  · rw [firstRatio, secondRatio, equalSpreads]
    ring1

/-- The base quadrance is four times the reflected spread and equal-side quadrance.

The spread-ratio and midpoint-quadrance equations hold, and the equal-side quadrance and two are nonzero. -/
theorem isosceles_reflection
    (q q₃ r midpointQuadrance : K)
    (qNonzero : q ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (spreadRatio : r = midpointQuadrance / q)
    (midpointValue : midpointQuadrance = q₃ / 4) :
    q₃ = 4 * r * q := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have ratioCleared : r * q = midpointQuadrance := by
    rw [spreadRatio]
    exact ExplicitField.div_mul_cancel midpointQuadrance qNonzero
  have midpointCleared : midpointQuadrance * 4 = q₃ := by
    rw [midpointValue]
    exact ExplicitField.div_mul_cancel q₃ fourNonzero
  calc
    q₃ = midpointQuadrance * 4 := midpointCleared.symm
    _ = (r * q) * 4 := by rw [ratioCleared]
    _ = 4 * r * q := by ring1

/-- Two factorizations of the isosceles quadrea agree under the base-quadrance equation. -/
theorem exercise_10_2
    (q q₃ s : K) (thirdQuadrance : q₃ = 4 * q * (1 - s)) :
    16 * q ^ 2 * s * (1 - s) = q₃ * (4 * q - q₃) := by
  rw [thirdQuadrance]
  ring1
end Purelib.Geometry.Triangles.Isosceles.Numeric

end
