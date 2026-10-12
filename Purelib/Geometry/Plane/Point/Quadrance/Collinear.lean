module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
public import Purelib.Geometry.Trigonometry.QuadTriple.Quadruple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Trigonometry

open Purelib.Geometry.Trigonometry.QuadTriple

/-!
# Divine Proportions, §§5.5–5.7: quadrea and four-point identities

These results are polynomial identities over arbitrary constructive explicit
fields.  Characteristic two is excluded only when a zero square factor must
be cancelled or when the source divides by two.
-/

@[expose] public section

namespace Purelib.Geometry.Plane.Point.Quadrance.Collinear

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Theorem 31 (Quadruple quad formula), including both conditional diagonal formulas from the source. -/
theorem quadruple_quad_formula [Nontrivial K] [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (collinear : Incidence.FourCollinear first second third fourth) :
    Quadruple.quadrupleQuadFunction
        (Quadrance.quadrance first second) (Quadrance.quadrance second third)
        (Quadrance.quadrance third fourth) (Quadrance.quadrance first fourth) = 0 ∧
      (Quadrance.quadrance first second + Quadrance.quadrance second third ≠
          Quadrance.quadrance third fourth + Quadrance.quadrance first fourth →
        Quadrance.quadrance first third =
          ((Quadrance.quadrance first second - Quadrance.quadrance second third) ^ 2 -
            (Quadrance.quadrance third fourth - Quadrance.quadrance first fourth) ^ 2) /
          (2 * (Quadrance.quadrance first second + Quadrance.quadrance second third -
            Quadrance.quadrance third fourth - Quadrance.quadrance first fourth))) ∧
      (Quadrance.quadrance second third + Quadrance.quadrance third fourth ≠
          Quadrance.quadrance first second + Quadrance.quadrance first fourth →
        Quadrance.quadrance second fourth =
          ((Quadrance.quadrance second third - Quadrance.quadrance third fourth) ^ 2 -
            (Quadrance.quadrance first second - Quadrance.quadrance first fourth) ^ 2) /
          (2 * (Quadrance.quadrance second third + Quadrance.quadrance third fourth -
            Quadrance.quadrance first second - Quadrance.quadrance first fourth))) := by
  rcases collinear with
    ⟨line, containsFirst, containsSecond, containsThird, containsFourth⟩
  have collinear123 : Incidence.Collinear first second third :=
    ⟨line, containsFirst, containsSecond, containsThird⟩
  have collinear134 : Incidence.Collinear first third fourth :=
    ⟨line, containsFirst, containsThird, containsFourth⟩
  have collinear234 : Incidence.Collinear second third fourth :=
    ⟨line, containsSecond, containsThird, containsFourth⟩
  have collinear241 : Incidence.Collinear second fourth first :=
    ⟨line, containsSecond, containsFourth, containsFirst⟩
  have triple123Raw :=
    (Quadrea.Basic.triple_quad_formula first second third twoNonzero).2 collinear123
  have triple134 : Trigonometry.QuadTriple
      (Quadrance.quadrance third fourth) (Quadrance.quadrance first fourth)
      (Quadrance.quadrance first third) :=
    (Quadrea.Basic.triple_quad_formula first third fourth twoNonzero).2 collinear134
  have triple123 : Trigonometry.QuadTriple
      (Quadrance.quadrance first second) (Quadrance.quadrance second third)
      (Quadrance.quadrance first third) := by
    unfold Trigonometry.QuadTriple
    calc
      Basic.archimedesFunction
          (Quadrance.quadrance first second) (Quadrance.quadrance second third)
          (Quadrance.quadrance first third) =
        Basic.archimedesFunction
          (Quadrance.quadrance second third) (Quadrance.quadrance first third)
          (Quadrance.quadrance first second) := by
            unfold Basic.archimedesFunction
            ring1
      _ = 0 := triple123Raw
  have triple234Raw :=
    (Quadrea.Basic.triple_quad_formula second third fourth twoNonzero).2 collinear234
  have triple234 : Trigonometry.QuadTriple
      (Quadrance.quadrance second third) (Quadrance.quadrance third fourth)
      (Quadrance.quadrance second fourth) := by
    unfold Trigonometry.QuadTriple
    calc
      Basic.archimedesFunction
          (Quadrance.quadrance second third) (Quadrance.quadrance third fourth)
          (Quadrance.quadrance second fourth) =
        Basic.archimedesFunction
          (Quadrance.quadrance third fourth) (Quadrance.quadrance second fourth)
          (Quadrance.quadrance second third) := by
            unfold Basic.archimedesFunction
            ring1
      _ = 0 := triple234Raw
  have triple241 : Trigonometry.QuadTriple
      (Quadrance.quadrance first second) (Quadrance.quadrance first fourth)
      (Quadrance.quadrance second fourth) := by
    have raw :=
      (Quadrea.Basic.triple_quad_formula second fourth first twoNonzero).2 collinear241
    unfold Trigonometry.QuadTriple
    calc
      Basic.archimedesFunction
          (Quadrance.quadrance first second) (Quadrance.quadrance first fourth)
          (Quadrance.quadrance second fourth) =
        Basic.archimedesFunction
          (Quadrance.quadrance second first) (Quadrance.quadrance fourth first)
          (Quadrance.quadrance second fourth) := by
            rw [Quadrance.quadrance_symm first fourth, Quadrance.quadrance_symm first second]
      _ =
        Basic.archimedesFunction
          (Quadrance.quadrance fourth first) (Quadrance.quadrance second first)
          (Quadrance.quadrance second fourth) := by
            unfold Basic.archimedesFunction
            ring1
      _ = 0 := raw
  refine ⟨Quadruple.two_quad_triples _ _ _ _ _ triple123 triple134, ?_, ?_⟩
  · intro denominatorNonzero
    exact Quadruple.two_quad_triples_common_value _ _ _ _ _ twoNonzero
      denominatorNonzero triple123 triple134
  · intro denominatorNonzero
    exact Quadruple.two_quad_triples_common_value _ _ _ _ _ twoNonzero
      denominatorNonzero triple234 triple241
end Purelib.Geometry.Plane.Point.Quadrance.Collinear

end
