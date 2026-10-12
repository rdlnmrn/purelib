module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10: isosceles triangles

The scalar forms isolate the finite cancellations used by the geometric
statements.  They apply uniformly to ratios obtained from rational triangles
or from triangles over explicit finite fields.
-/

namespace Purelib.Geometry.Triangles.Isosceles.Null

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Theorem 64 (Null isosceles), for the displayed equal pair `Q₁ = Q₂`. The two alternatives say respectively that
exactly those two sides are null, or that no side is null. -/
theorem null_isosceles [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (equalQuadrances :
      Quadrance.quadrance second third = Quadrance.quadrance first third) :
    (Quadrance.quadrance second third = 0 ∧
        Quadrance.quadrance first third = 0 ∧ Quadrance.quadrance first second ≠ 0) ∨
      (Quadrance.quadrance second third ≠ 0 ∧
        Quadrance.quadrance first third ≠ 0 ∧ Quadrance.quadrance first second ≠ 0) := by
  have quadreaNonzero : Quadrea.Basic.quadrea first second third ≠ 0 :=
    (Quadrea.Basic.quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  have thirdQuadranceNonzero : Quadrance.quadrance first second ≠ 0 := by
    intro thirdZero
    apply quadreaNonzero
    unfold Quadrea.Basic.quadrea
    rw [equalQuadrances, thirdZero]
    unfold Trigonometry.QuadTriple.Basic.archimedesFunction
    ring1
  by_cases firstEqualQuadranceZero : Quadrance.quadrance second third = 0
  · left
    exact ⟨firstEqualQuadranceZero,
      equalQuadrances.symm.trans firstEqualQuadranceZero,
      thirdQuadranceNonzero⟩
  · right
    have secondEqualQuadranceNonzero : Quadrance.quadrance first third ≠ 0 := by
      intro secondZero
      exact firstEqualQuadranceZero (equalQuadrances.trans secondZero)
    exact ⟨firstEqualQuadranceZero, secondEqualQuadranceNonzero,
      thirdQuadranceNonzero⟩

/-- Exercise 10.3's finite content. If the equal pair of an isosceles triangle is null, the remaining side is
necessarily non-null and the quadrea is the negative square of its quadrance. In particular the spread-based conclusions
of the preceding theorems are not defined on the two null sides. -/
theorem exercise_10_3 [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (equalQuadrances :
      Quadrance.quadrance second third = Quadrance.quadrance first third)
    (firstNull : Quadrance.quadrance second third = 0) :
    Quadrance.quadrance second third = 0 ∧
      Quadrance.quadrance first third = 0 ∧
      Quadrance.quadrance first second ≠ 0 ∧
      Quadrea.Basic.quadrea first second third = -(Quadrance.quadrance first second) ^ 2 := by
  have secondNull : Quadrance.quadrance first third = 0 :=
    equalQuadrances.symm.trans firstNull
  have alternatives := null_isosceles first second third notCollinear
    twoNonzero equalQuadrances
  have thirdNonNull : Quadrance.quadrance first second ≠ 0 := by
    rcases alternatives with nullPair | nonNullTriple
    · exact nullPair.2.2
    · exact False.elim (nonNullTriple.1 firstNull)
  refine ⟨firstNull, secondNull, thirdNonNull, ?_⟩
  unfold Quadrea.Basic.quadrea Trigonometry.QuadTriple.Basic.archimedesFunction
  rw [firstNull, secondNull]
  ring1

end Purelib.Geometry.Triangles.Isosceles.Null

end
