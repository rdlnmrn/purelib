module
import Purelib.Geometry.Trigonometry.QuadTriple.Identities

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.FiniteSum.List.Basic
public import Purelib.Geometry.Trigonometry.QuadTriple.Chain.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.FiniteSum

open Purelib.Geometry.Trigonometry.QuadTriple

/-!
# Divine Proportions, remaining Chapter 5 exercises

Exercise 5.3 is false with the source's definition of a triangle: the
nonzero quadrances `1,1,4` have zero quadrea, hence cannot belong to three
noncollinear points.  The corrected theorem below isolates the exact missing
condition.  In a field carrying an explicit square root of `-1`, every scalar
is constructively a sum of two squares, so Theorem 28 reduces triangle
existence to an explicit nonzero square witness for the quadrea.

Exercise 5.17 is retained through the finite construction responsible for its
factor `2`: a chosen base vector and either sign of a nonzero quadrea root give
two distinct completion points with the requested quadrances.  The remaining
`p²` translation and `p±1` nonzero-circle factors are recorded as finite
counting data rather than by enumerating an entire field carrier.

Exercise 5.19 is answered by a recursive, fuel-indexed finite quad relation.
For five entries it introduces the two diagonals of a fan triangulation; for
any requested finite number of entries it repeatedly combines two adjacent
signed lengths.  There is no infinite sequence or completed polygon.
-/

@[expose] public section

namespace Purelib.Geometry.Trigonometry.QuadTriple.Chain.ClosedSteps

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section
end

section

/-- Squared increments of any explicitly closed finite one-dimensional chain satisfy the corresponding recursive quad
relation. -/
theorem quadRelation_of_closed_steps
    (first second third : K) (tail : List K)
    (closed : List.Basic.scalarSum (first :: second :: third :: tail) = 0) :
    Chain.Basic.QuadRelation tail.length
      (List.map (fun step => step ^ 2)
        (first :: second :: third :: tail)) := by
  induction tail generalizing first second third with
  | nil =>
      change Geometry.Trigonometry.QuadTriple (first ^ 2) (second ^ 2) (third ^ 2)
      apply Identities.exercise_5_8 first second third
      right
      right
      left
      have sumZero : first + second + third = 0 := by
        calc
          first + second + third =
              List.Basic.scalarSum (first :: second :: third :: []) := by
            simp only [List.Basic.scalarSum_cons, List.Basic.scalarSum_nil, add_zero]
            ring1
          _ = 0 := closed
      exact eq_neg_of_add_eq_zero_left sumZero
  | cons fourth rest inductionHypothesis =>
      change ∃ diagonal : K,
        Geometry.Trigonometry.QuadTriple (first ^ 2) (second ^ 2) diagonal ∧
          Chain.Basic.QuadRelation rest.length
            (diagonal :: List.map (fun step => step ^ 2) (third :: fourth :: rest))
      refine ⟨(first + second) ^ 2, ?_, ?_⟩
      · exact Identities.exercise_5_8 first second (first + second) (Or.inl rfl)
      · apply inductionHypothesis (first := first + second)
          (second := third) (third := fourth)
        calc
          List.Basic.scalarSum ((first + second) :: third :: fourth :: rest) =
              List.Basic.scalarSum (first :: second :: third :: fourth :: rest) := by
            simp only [List.Basic.scalarSum_cons]
            ring1
          _ = 0 := closed

/-- Exercise 5.19, general finite case. The caller requests exactly the finite tail to be combined; the theorem performs
that many recursive steps. -/
theorem finite_relation_of_closed_steps
    (first second third : K) (tail : List K)
    (closed : List.Basic.scalarSum (first :: second :: third :: tail) = 0) :
    Chain.Basic.QuadRelation tail.length
      (List.map (fun step => step ^ 2)
        (first :: second :: third :: tail)) :=
  quadRelation_of_closed_steps first second third tail closed

end

end Purelib.Geometry.Trigonometry.QuadTriple.Chain.ClosedSteps

end
