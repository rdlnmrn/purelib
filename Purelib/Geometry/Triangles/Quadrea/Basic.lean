module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, Chapter 5: quadrance

Quadrance is a polynomial, so its basic geometry works uniformly over the
constructive rationals and finite fields.  The few exclusions below are
stated explicitly: midpoint and Triple-quad arguments require `2 ≠ 0`.
-/

namespace Purelib.Geometry.Triangles.Quadrea.Basic

variable {K : Type*} [ExplicitField K]

/-- The coordinate identity underlying the Triple quad formula. -/
theorem archimedes_quadrance_identity
    (first second third : Plane.Point K) :
    QuadTriple.Basic.archimedesFunction
        (Quadrance.quadrance second third)
        (Quadrance.quadrance first third)
        (Quadrance.quadrance first second) =
      4 * Incidence.pointDeterminant first second third ^ 2 := by
  unfold QuadTriple.Basic.archimedesFunction Quadrance.quadrance Incidence.pointDeterminant
  ring1

/-- Theorem 22 (Triple quad formula), valid over every explicit field of characteristic other than two. -/
theorem triple_quad_formula [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    QuadTriple.Basic.archimedesFunction
        (Quadrance.quadrance second third)
        (Quadrance.quadrance first third)
        (Quadrance.quadrance first second) = 0 ↔
      Incidence.Collinear first second third := by
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
  constructor
  · intro tripleQuad
    apply (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
    by_cases determinantZero : Incidence.pointDeterminant first second third = 0
    · exact determinantZero
    · have squareNonzero : Incidence.pointDeterminant first second third ^ 2 ≠ 0 := by
        simpa [pow_two] using
          ExplicitField.mul_ne_zero determinantZero determinantZero
      have productNonzero :=
        ExplicitField.mul_ne_zero fourNonzero squareNonzero
      apply False.elim
      apply productNonzero
      calc
        4 * Incidence.pointDeterminant first second third ^ 2 =
            QuadTriple.Basic.archimedesFunction
              (Quadrance.quadrance second third)
              (Quadrance.quadrance first third)
              (Quadrance.quadrance first second) :=
                (archimedes_quadrance_identity first second third).symm
        _ = 0 := tripleQuad
  · intro collinear
    have determinantZero :=
      (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).1 collinear
    rw [archimedes_quadrance_identity, determinantZero]
    ring1
end Purelib.Geometry.Triangles.Quadrea.Basic

end

end

section
/-!
# Divine Proportions, §§5.5–5.7: quadrea and four-point identities

These results are polynomial identities over arbitrary constructive explicit
fields.  Characteristic two is excluded only when a zero square factor must
be cancelled or when the source divides by two.
-/

@[expose] public section

namespace Purelib.Geometry.Triangles.Quadrea.Basic

variable {K : Type*} [ExplicitField K]

/-- The symmetric quadrea of three points. -/
def quadrea (first second third : Plane.Point K) : K :=
  QuadTriple.Basic.archimedesFunction
    (Quadrance.quadrance second third)
    (Quadrance.quadrance first third)
    (Quadrance.quadrance first second)

/-- Theorem 26 (Quadrea): quadrea is four times the square of the coordinate determinant. -/
theorem quadrea_coordinate_formula (first second third :
  Plane.Point K) :
    quadrea first second third =
      4 * Incidence.pointDeterminant first second third ^ 2 :=
  archimedes_quadrance_identity first second third

/-- The nonzero clause of Theorem 26: outside characteristic two, nonzero quadrea is exactly noncollinearity. -/
theorem quadrea_ne_zero_iff_not_collinear [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrea first second third ≠ 0 ↔ ¬ Incidence.Collinear first second third := by
  exact not_congr (triple_quad_formula first second third twoNonzero)
end Purelib.Geometry.Triangles.Quadrea.Basic

end

end

section
@[expose] public section

/-!
# Divine Proportions, §§6.4–6.7: triangle ratio theorems

The book's quotient identities are retained exactly.  Every cancellation is
backed by a displayed non-null side or a characteristic hypothesis.
-/

namespace Purelib.Geometry.Triangles.Quadrea.Basic

variable {K : Type*} [ExplicitField K]

/-- Quadrea is invariant under cyclic permutation of the three vertices. -/
theorem quadrea_cyclic (first second third : Plane.Point K)
  :
    quadrea second third first = quadrea first second third := by
  unfold quadrea
  rw [Quadrance.quadrance_symm second first, Quadrance.quadrance_symm third first]
  unfold QuadTriple.Basic.archimedesFunction
  ring1

/-- Swapping the first two vertices preserves quadrea. -/
theorem quadrea_swap_first_second (first second third :
  Plane.Point K) :
    quadrea second first third = quadrea first second third := by
  unfold quadrea
  rw [Quadrance.quadrance_symm second first]
  unfold QuadTriple.Basic.archimedesFunction
  ring1

/-- Swapping the last two vertices preserves quadrea. -/
theorem quadrea_swap_second_third (first second third :
  Plane.Point K) :
    quadrea first third second = quadrea first second third := by
  unfold quadrea
  rw [Quadrance.quadrance_symm third second, Quadrance.quadrance_symm first second,
    Quadrance.quadrance_symm first third]
  unfold QuadTriple.Basic.archimedesFunction
  ring1
end Purelib.Geometry.Triangles.Quadrea.Basic

end
