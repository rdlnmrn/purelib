module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Algebra.Field

section
public section

/-!
# Divine Proportions, Chapter 27: rational spherical coordinates

This module formalizes the finite algebra beneath the source's coordinate
changes: squared-coordinate reconstruction, the two-, three-, and
four-dimensional Jacobian determinants, squared density identities, the
lemniscate conversion, and a witness-based finite polygon-refinement step.

The chapter's improper integrals, exponentials, Gamma/Beta integrals, `π`, and
limit assertions are intentionally not introduced.  Their finite endpoint
polynomial simplifications are retained at the end of the module.
-/

namespace Purelib.Algebra.Recurrence.NestedRadical

section RationalSphericalCoordinates

variable {K : Type*} [ExplicitField K]

/-! ## §27.2 and Exercise 27.2: finite polygon refinement -/

/-- Retain one algebraic step of the nested-radical area recurrence.

The data include a square root of the scale, a next root squaring to two plus the current root, and the current and next
scaled area expressions. -/
@[expose] def PolygonAreaRefinementStep
    (scale scaleRoot root nextRoot current next : K) : Prop :=
  scaleRoot ^ 2 = scale ∧
    current = scale * (2 - root) ∧
    nextRoot ^ 2 = 2 + root ∧
    next = 4 * scale * (2 - nextRoot)

open Purelib.Algebra.Recurrence in
/-- A retained nested-radical step satisfies its squared witness and area recurrence.

The product of the scale root and next root supplies the explicit square witness for four times the scale minus the
current value. -/
theorem exercise_27_2_step
    (scale scaleRoot root nextRoot current next : K)
    (step : PolygonAreaRefinementStep
      scale scaleRoot root nextRoot current next) :
    (scaleRoot * nextRoot) ^ 2 = 4 * scale - current ∧
      next = 8 * scale -
        (4 * scaleRoot) * (scaleRoot * nextRoot) := by
  rcases step with ⟨scaleSquare, currentValue, nextRootSquare, nextValue⟩
  constructor
  · rw [currentValue]
    apply Group.eq_of_sub_eq_zero
    calc
      (scaleRoot * nextRoot) ^ 2 -
          (4 * scale - scale * (2 - root)) =
        scaleRoot ^ 2 * nextRoot ^ 2 -
          scale * (2 + root) := by ring1
      _ = 0 := by rw [scaleSquare, nextRootSquare]; ring1
  · rw [nextValue]
    apply Group.eq_of_sub_eq_zero
    calc
      4 * scale * (2 - nextRoot) -
          (8 * scale -
            (4 * scaleRoot) * (scaleRoot * nextRoot)) =
        4 * nextRoot * (scaleRoot ^ 2 - scale) := by ring1
      _ = 0 := by rw [scaleSquare]; ring1
end RationalSphericalCoordinates
end Purelib.Algebra.Recurrence.NestedRadical

end

end
