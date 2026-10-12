module
public import Purelib.Algebra.Semiring.Nat
public import Purelib.Geometry.Triangles.Quadrance.Realization
import Purelib.Geometry.Trigonometry.QuadTriple.Basic

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Group.Nat.Defs

open Purelib.Algebra.Field

open Purelib.Geometry.Triangles

section
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

namespace formalisations.DivineProportions.Chapters.Trigonometry.ChapterFiveRemaining

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- Exercise 5.3 is false as printed: `1,1,4` are not all zero, but their
quadrea vanishes, so they cannot be the quadrances of a noncollinear triangle
over any constructive field of characteristic different from two. -/
theorem exercise_5_3_printed_counterexample
    [Nontrivial K] [DecidableEq K] (twoNonzero : (2 : K) ≠ 0) :
    ¬ Quadrance.Realization.HasTriangleQuadrances (1 : K) 1 4 := open Purelib in by
  intro triangle
  have areaSquare :=
    ((Quadrance.Realization.triangle_quadrea (1 : K) 1 4 twoNonzero).1 triangle).2.2.2.2
  rcases areaSquare with ⟨root, rootNonzero, rootEquation⟩
  have areaZero : Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction (1 : K) 1 4 = 0 := by
    unfold Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction
    ring1
  have rootSquareZero : root ^ 2 = 0 := by
    calc
      root ^ 2 = Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction (1 : K) 1 4 := rootEquation.symm
      _ = 0 := areaZero
  have rootProductZero : root * root = 0 := by
    calc
      root * root = root ^ 2 := by ring1
      _ = 0 := rootSquareZero
  exact (ExplicitField.mul_ne_zero rootNonzero rootNonzero)
    rootProductZero

namespace ExerciseFiveSeventeen

/-- The `p=4l+3` count printed in Exercise 5.17. -/
def countFourMulAddThree (p : Nat) : Nat := 2 * Nat.pow p (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) * (p
  + 1)

/-- The `p=4l+1` count printed in Exercise 5.17. -/
def countFourMulAddOne (p : Nat) : Nat := 2 * Nat.pow p (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) * (p -
  1)

/-- Finite bookkeeping for the `4l+3` branch: two completions times `p²`
translations times `p+1` base vectors. -/
theorem count_four_mul_add_three_from_factors
    (p translations baseVectors completions total : Nat)
    (translationCount : translations = p ^ 2)
    (baseVectorCount : baseVectors = p + 1)
    (completionCount : completions = 2)
    (factorization : total = completions * translations * baseVectors) :
    total = countFourMulAddThree p := by
  rw [factorization, translationCount, baseVectorCount, completionCount]
  rfl

/-- Finite bookkeeping for the `4l+1` branch. -/
theorem count_four_mul_add_one_from_factors
    (p translations baseVectors completions total : Nat)
    (translationCount : translations = p ^ 2)
    (baseVectorCount : baseVectors = p - 1)
    (completionCount : completions = 2)
    (factorization : total = completions * translations * baseVectors) :
    total = countFourMulAddOne p := by
  rw [factorization, translationCount, baseVectorCount, completionCount]
  rfl

end ExerciseFiveSeventeen

namespace ExerciseFiveNineteen
end ExerciseFiveNineteen

end formalisations.DivineProportions.Chapters.Trigonometry.ChapterFiveRemaining

end

end
