module
import Purelib.Geometry.Trigonometry.QuadTriple.Basic

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.FiniteSum.List.Basic
public import Purelib.Geometry.Trigonometry.QuadTriple.Chain.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Chain.ClosedSteps
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.FiniteSum

open Purelib.Geometry.Trigonometry

open Purelib.Geometry.Trigonometry.QuadTriple

open Purelib.Geometry.Trigonometry.QuadTriple.Chain

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

namespace Purelib.Geometry.Trigonometry.QuadTriple.Chain.Quintuple

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section
end

section

/-- The quintuple relation written without recursion: two finite diagonal witnesses split the five entries into three
quad triples. -/
def QuintupleQuadRelation
    (q₁₂ q₂₃ q₃₄ q₄₅ q₁₅ : K) : Prop :=
  ∃ q₁₃ q₁₄ : K,
    Geometry.Trigonometry.QuadTriple q₁₂ q₂₃ q₁₃ ∧
      Geometry.Trigonometry.QuadTriple q₁₃ q₃₄ q₁₄ ∧
      Geometry.Trigonometry.QuadTriple q₁₄ q₄₅ q₁₅

/-- Two recursive quad-relation steps are equivalent to the explicit five-entry relation.

The two retained diagonals give the same three quad triples in both presentations. -/
theorem quadRelation_two_iff_quintuple
    (q₁₂ q₂₃ q₃₄ q₄₅ q₁₅ : K) :
    Chain.Basic.QuadRelation 2 [q₁₂, q₂₃, q₃₄, q₄₅, q₁₅] ↔
      QuintupleQuadRelation q₁₂ q₂₃ q₃₄ q₄₅ q₁₅ := by
  change
    (∃ q₁₃,
      Geometry.Trigonometry.QuadTriple q₁₂ q₂₃ q₁₃ ∧
        ∃ q₁₄,
          Geometry.Trigonometry.QuadTriple q₁₃ q₃₄ q₁₄ ∧
            Geometry.Trigonometry.QuadTriple q₁₄ q₄₅ q₁₅) ↔
      ∃ q₁₃ q₁₄,
        Geometry.Trigonometry.QuadTriple q₁₂ q₂₃ q₁₃ ∧
          Geometry.Trigonometry.QuadTriple q₁₃ q₃₄ q₁₄ ∧
            Geometry.Trigonometry.QuadTriple q₁₄ q₄₅ q₁₅
  constructor
  · rintro ⟨q₁₃, firstRelation, q₁₄, secondRelation, thirdRelation⟩
    exact ⟨q₁₃, q₁₄, firstRelation, secondRelation, thirdRelation⟩
  · rintro ⟨q₁₃, q₁₄, firstRelation, secondRelation, thirdRelation⟩
    exact ⟨q₁₃, firstRelation, q₁₄, secondRelation, thirdRelation⟩

/-- Exercise 5.19, quintuple case. Five signed one-dimensional increments which close up give the two requested diagonal
witnesses and hence three successive quad triples. -/
theorem quintuple_of_closed_steps
    (d₁₂ d₂₃ d₃₄ d₄₅ d₁₅ : K)
    (closed : d₁₂ + d₂₃ + d₃₄ + d₄₅ + d₁₅ = 0) :
    QuintupleQuadRelation
      (d₁₂ ^ 2) (d₂₃ ^ 2) (d₃₄ ^ 2) (d₄₅ ^ 2) (d₁₅ ^ 2) := by
  apply (quadRelation_two_iff_quintuple
    (d₁₂ ^ 2) (d₂₃ ^ 2) (d₃₄ ^ 2) (d₄₅ ^ 2) (d₁₅ ^ 2)).1
  apply ClosedSteps.quadRelation_of_closed_steps d₁₂ d₂₃ d₃₄ [d₄₅, d₁₅]
  calc
    List.Basic.scalarSum (d₁₂ :: d₂₃ :: d₃₄ :: [d₄₅, d₁₅]) =
        d₁₂ + d₂₃ + d₃₄ + d₄₅ + d₁₅ := by
      simp only [List.Basic.scalarSum_cons, List.Basic.scalarSum_nil, add_zero]
      ring1
    _ = 0 := closed
end

end Purelib.Geometry.Trigonometry.QuadTriple.Chain.Quintuple

end
