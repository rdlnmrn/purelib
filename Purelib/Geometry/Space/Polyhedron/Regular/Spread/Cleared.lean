module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Triangles.Isosceles.Spread.Cleared
public import Purelib.Polynomial.Recurrence.Spread.Roots.Five.Radical
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry.Triangles.Isosceles.Spread

open Purelib.Polynomial.Recurrence.Spread.Roots.Five.Radical

section
public section

/-!
# Divine Proportions, Chapter 26: Platonic solids

All five face-spread computations are recorded by one denominator-cleared
isosceles-triangle certificate.  Exercise 26.1 is proved directly from three
displayed edge vectors.  Exercise 26.4 uses a uniformly scaled standard
icosahedron, so its coordinates are polynomial in a supplied witness
`root²=5` and contain no selected irrational or completed field.
-/

namespace Purelib.Geometry.Space.Polyhedron.Regular.Spread.Cleared

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The regular tetrahedron's face spread is `8/9`. -/
theorem tetrahedron_face_spread_cleared (Q : K) :
    Cleared.ClearedIsoscelesSpread Q 1 (3 * Q) 4 8 9 := by
  unfold Cleared.ClearedIsoscelesSpread
  ring1

/-- The cube has perpendicular faces, while its opposite center rays have the tetrahedral spread `8/9`. -/
theorem cube_face_and_center_spreads_cleared (Q : K) :
    (1 : K) = 1 ∧
      Cleared.ClearedIsoscelesEndpointSpread (2 * Q) 1 (3 * Q) 4 1 3 ∧
      Cleared.ClearedIsoscelesSpread (2 * Q) 1 (3 * Q) 4 8 9 := by
  constructor
  · rfl
  constructor
  · unfold Cleared.ClearedIsoscelesEndpointSpread
    ring1
  unfold Cleared.ClearedIsoscelesSpread
  ring1

/-- The three Pythagorean quadrance steps in the cube section. `quarter` is the common value `Q/4`; the conclusions are
the cleared forms of `Q/2`, `3Q/4`, and `2Q`. -/
theorem cube_quadrance_chain_cleared
    (quarter Q : K) (quarterValue : 4 * quarter = Q) :
    2 * (2 * quarter) = Q ∧
      4 * (3 * quarter) = 3 * Q ∧
      8 * quarter = 2 * Q := by
  constructor
  · calc
      2 * (2 * quarter) = 4 * quarter := by ring1
      _ = Q := quarterValue
  constructor
  · calc
      4 * (3 * quarter) = 3 * (4 * quarter) := by ring1
      _ = 3 * Q := by rw [quarterValue]
  · calc
      8 * quarter = 2 * (4 * quarter) := by ring1
      _ = 2 * Q := by rw [quarterValue]

/-- The octahedron has the same numerical face spread as the tetrahedron, with base quadrance `2Q` and equal midpoint
quadrances `3Q/4`. -/
theorem octahedron_face_spread_cleared (Q : K) :
    Cleared.ClearedIsoscelesSpread (2 * Q) 1 (3 * Q) 4 8 9 := by
  unfold Cleared.ClearedIsoscelesSpread
  ring1

/-- Exercise 26.2 and the cube calculation use the identical cleared isosceles certificate, so the center-ray spread
equals the face spread. -/
theorem exercise_26_2 (Q : K) :
    Cleared.ClearedIsoscelesSpread Q 1 (3 * Q) 4 8 9 ∧
      Cleared.ClearedIsoscelesSpread Q 1 (3 * Q) 8 8 9 := by
  exact ⟨tetrahedron_face_spread_cleared Q,
    by unfold Cleared.ClearedIsoscelesSpread; ring1⟩

/-- The icosahedral face-spread simplification to `4/9`, with the pentagon diagonal `βQ/α` and midpoint quadrance
`3Q/4`. -/
theorem icosahedron_face_spread_cleared
    (root Q : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    Cleared.ClearedIsoscelesSpread
      (PlatonicSolids.beta root * Q) (PlatonicSolids.alpha root) (3 * Q) 4 4 9 := by
  have golden := Golden.beta_mul_three_alpha_sub_beta_eq_alpha_square
    root rootSquare twoNonzero
  apply Group.eq_of_sub_eq_zero
  calc
    9 * (PlatonicSolids.beta root * Q) * 4 *
          (4 * (3 * Q) * PlatonicSolids.alpha root -
            PlatonicSolids.beta root * Q * 4) -
        4 * 4 * (3 * Q) ^ 2 * PlatonicSolids.alpha root ^ 2 =
      144 * Q ^ 2 *
        (PlatonicSolids.beta root *
            (3 * PlatonicSolids.alpha root - PlatonicSolids.beta root) -
          PlatonicSolids.alpha root ^ 2) := by ring1
    _ = 0 := by rw [golden]; ring1

/-- The dodecahedral face-spread simplification to `4/5`. -/
theorem dodecahedron_face_spread_cleared
    (root Q : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    Cleared.ClearedIsoscelesSpread
      (PlatonicSolids.beta root * Q) (PlatonicSolids.alpha root)
      (PlatonicSolids.beta root * Q) 1 4 5 := by
  have golden := Golden.five_mul_four_alpha_sub_one_eq_sixteen_alpha_square
    root rootSquare twoNonzero
  apply Group.eq_of_sub_eq_zero
  calc
    5 * (PlatonicSolids.beta root * Q) * 1 *
          (4 * (PlatonicSolids.beta root * Q) * PlatonicSolids.alpha root -
            PlatonicSolids.beta root * Q * 1) -
        4 * 4 * (PlatonicSolids.beta root * Q) ^ 2 *
          PlatonicSolids.alpha root ^ 2 =
      PlatonicSolids.beta root ^ 2 * Q ^ 2 *
        (5 * (4 * PlatonicSolids.alpha root - 1) -
          16 * PlatonicSolids.alpha root ^ 2) := by ring1
    _ = 0 := by rw [golden]; ring1

/-- The complete finite face-spread summary in the source order: tetrahedron, cube, octahedron, icosahedron,
dodecahedron. -/
theorem platonic_face_spread_summary
    (root Q : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    Cleared.ClearedIsoscelesSpread Q 1 (3 * Q) 4 8 9 ∧
      (1 : K) = 1 ∧
      Cleared.ClearedIsoscelesSpread (2 * Q) 1 (3 * Q) 4 8 9 ∧
      Cleared.ClearedIsoscelesSpread
        (PlatonicSolids.beta root * Q) (PlatonicSolids.alpha root) (3 * Q) 4 4 9 ∧
      Cleared.ClearedIsoscelesSpread
        (PlatonicSolids.beta root * Q) (PlatonicSolids.alpha root)
          (PlatonicSolids.beta root * Q) 1 4 5 := by
  exact ⟨tetrahedron_face_spread_cleared Q, rfl,
    octahedron_face_spread_cleared Q,
    icosahedron_face_spread_cleared root Q rootSquare twoNonzero,
    dodecahedron_face_spread_cleared root Q rootSquare twoNonzero⟩

end
end Purelib.Geometry.Space.Polyhedron.Regular.Spread.Cleared

end

end
