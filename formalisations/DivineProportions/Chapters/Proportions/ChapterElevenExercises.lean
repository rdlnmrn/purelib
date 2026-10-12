module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic

import Purelib.Geometry.Trigonometry.QuadTriple.Operations
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11 exercises

This module begins the reader problems following the Two-struts theorem.  All
normalizations are retained as finite polynomial equalities.  In particular,
Example 11.1 is checked by scaling the two quad triples by the displayed
factor `256`; no quadratic formula or selected root is used.
-/

namespace formalisations.DivineProportions.Chapters.Proportions.ChapterElevenExercises

variable {K : Type*} [Field.ExplicitField K]

/-- The first factorization in Example 11.1.  The hypotheses `4p=1` and
`64r=9` are the denominator-free forms of `p=1/4` and `r=9/64`. -/
private theorem example_11_1_first_factorization
    (p r m : K) (pValue : 4 * p = 1) (rValue : 64 * r = 9)
    (triple : Geometry.Trigonometry.QuadTriple r (r * p) (m * p)) :
    (64 * m - 9) * (64 * m - 81) = 0 := by
  have scaled := Geometry.Trigonometry.QuadTriple.Operations.quadTriple_scale r (r * p) (m * p) 256 triple
  have firstValue : 256 * r = (36 : K) := by
    calc
      256 * r = 4 * (64 * r) := by ring1
      _ = 4 * 9 := by rw [rValue]
      _ = 36 := by ring1
  have secondValue : 256 * (r * p) = (9 : K) := by
    calc
      256 * (r * p) = (64 * r) * (4 * p) := by ring1
      _ = 9 * 1 := by rw [rValue, pValue]
      _ = 9 := by ring1
  have thirdValue : 256 * (m * p) = 64 * m := by
    calc
      256 * (m * p) = (64 * m) * (4 * p) := by ring1
      _ = 64 * m := by rw [pValue, mul_one]
  rw [firstValue, secondValue, thirdValue] at scaled
  unfold Geometry.Trigonometry.QuadTriple
    Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction at scaled
  calc
    (64 * m - 9) * (64 * m - 81) =
        -((36 + 9 + 64 * m) ^ 2 -
          2 * (36 ^ 2 + 9 ^ 2 + (64 * m) ^ 2)) := by ring1
    _ = 0 := by rw [scaled]; exact neg_zero

/-- The second factorization in Example 11.1. -/
private theorem example_11_1_second_factorization
    (p r n : K) (pValue : 4 * p = 1) (rValue : 64 * r = 9)
    (triple : Geometry.Trigonometry.QuadTriple p (r * p) (n * r)) :
    (36 * n - 25) * (36 * n - 121) = 0 := by
  have scaled := Geometry.Trigonometry.QuadTriple.Operations.quadTriple_scale p (r * p) (n * r) 256 triple
  have firstValue : 256 * p = (64 : K) := by
    calc
      256 * p = 64 * (4 * p) := by ring1
      _ = 64 := by rw [pValue, mul_one]
  have secondValue : 256 * (r * p) = (9 : K) := by
    calc
      256 * (r * p) = (64 * r) * (4 * p) := by ring1
      _ = 9 * 1 := by rw [rValue, pValue]
      _ = 9 := by ring1
  have thirdValue : 256 * (n * r) = 36 * n := by
    calc
      256 * (n * r) = 4 * (64 * r) * n := by ring1
      _ = 4 * 9 * n := by rw [rValue]
      _ = 36 * n := by ring1
  rw [firstValue, secondValue, thirdValue] at scaled
  unfold Geometry.Trigonometry.QuadTriple
    Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction at scaled
  calc
    (36 * n - 25) * (36 * n - 121) =
        -((64 + 9 + 36 * n) ^ 2 -
          2 * (64 ^ 2 + 9 ^ 2 + (36 * n) ^ 2)) := by ring1
    _ = 0 := by rw [scaled]; exact neg_zero

/-- Example 11.1.  The two quad triples supplied by Two struts at
`p=1/4`, `r=9/64` give exactly the two printed factored equations. -/
theorem example_11_1
    (p r m n : K) (pValue : 4 * p = 1) (rValue : 64 * r = 9)
    (strutTriples :
      Geometry.Trigonometry.QuadTriple r (r * p) (m * p) ∧
        Geometry.Trigonometry.QuadTriple p (r * p) (n * r)) :
    (64 * m - 9) * (64 * m - 81) = 0 ∧
      (36 * n - 25) * (36 * n - 121) = 0 :=
  ⟨example_11_1_first_factorization p r m pValue rValue
      strutTriples.1,
    example_11_1_second_factorization p r n pValue rValue
      strutTriples.2⟩
end formalisations.DivineProportions.Chapters.Proportions.ChapterElevenExercises

end
