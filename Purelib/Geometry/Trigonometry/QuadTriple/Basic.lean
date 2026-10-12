module
public import Purelib.Algebra.Field.ExplicitField
-- Exposed scalar polynomials and proof bodies retain these original parents.
public import Purelib.Algebra.Group.Negation
public import Purelib.Data.Nat.Order
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

open Purelib
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

section
@[expose] public section

/-!
# Divine Proportions, Chapter 5: quadrance

Quadrance is a polynomial, so its basic geometry works uniformly over the
constructive rationals and finite fields.  The few exclusions below are
stated explicitly: midpoint and Triple-quad arguments require `2 ≠ 0`.
-/

namespace Purelib.Geometry.Trigonometry.QuadTriple.Basic

variable {K : Type*} [ExplicitField K]

section

/-- Archimedes' symmetric polynomial. -/
def archimedesFunction (a b c : K) : K :=
  (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2)

end

end Purelib.Geometry.Trigonometry.QuadTriple.Basic

end

end

section
@[expose] public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

namespace Purelib.Geometry.Trigonometry.QuadTriple.Basic.Quadrola

section

variable {K : Type*} [ExplicitField K]

/-- The Archimedes polynomial in a form where quartic cancellation is visible. -/
theorem archimedes_difference_identity (first second
  third : K) :
    archimedesFunction first second third =
      -(first - second) ^ 2 + 2 * third * (first + second) - third ^ 2 := by
  unfold archimedesFunction
  ring1
end

end Purelib.Geometry.Trigonometry.QuadTriple.Basic.Quadrola

end

section
/-!
# Divine Proportions, §§5.5–5.7: quadrea and four-point identities

These results are polynomial identities over arbitrary constructive explicit
fields.  Characteristic two is excluded only when a zero square factor must
be cancelled or when the source divides by two.
-/

@[expose] public section

namespace Purelib.Geometry.Trigonometry

variable {K : Type*} [ExplicitField K]

namespace QuadTriple.Basic

/-- Theorem 27 (Right quadrea): the quadrea of a Pythagorean triple is four times the product of the two perpendicular
quadrances. -/
theorem right_quadrea (q₁ q₂ q₃ : K) (pythagoras : q₁ + q₂ = q₃) :
    archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₂ := by
  unfold archimedesFunction
  rw [← pythagoras]
  ring1

/-- Theorem 29 (Archimedes' formula), as a universal polynomial identity. -/
theorem archimedes_formula (d₁ d₂ d₃ : K) :
    archimedesFunction (d₁ ^ 2) (d₂ ^ 2) (d₃ ^ 2) =
      (d₁ + d₂ + d₃) * (d₁ + d₂ - d₃) *
        (d₂ + d₃ - d₁) * (d₃ + d₁ - d₂) := by
  unfold archimedesFunction
  ring1

end QuadTriple.Basic

section

/-- A triple of scalars satisfying Archimedes' polynomial. -/
def QuadTriple (a b c : K) : Prop :=
  Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction a b c = 0

end

namespace QuadTriple.Basic

/-- The centered-square form of the quad-triple relation. -/
theorem quadTriple_iff_centered_square (a b x : K) :
    QuadTriple a b x ↔ (x - (a + b)) ^ 2 = 4 * a * b := by
  have identity : archimedesFunction a b x =
      4 * a * b - (x - (a + b)) ^ 2 := by
    unfold archimedesFunction
    ring1
  unfold QuadTriple
  rw [identity]
  constructor <;> intro equation
  · calc
      (x - (a + b)) ^ 2 =
          4 * a * b - (4 * a * b - (x - (a + b)) ^ 2) := by ring1
      _ = 4 * a * b := by rw [equation]; ring1
  · rw [equation]
    ring1

end QuadTriple.Basic

end Purelib.Geometry.Trigonometry

end

end
