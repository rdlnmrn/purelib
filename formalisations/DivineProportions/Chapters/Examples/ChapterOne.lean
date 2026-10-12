module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Ratio
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.Tactic.Ring

section
/-!
# Divine Proportions, Chapter 1 finite calculation

The introductory `4,5,7` triangle is recorded entirely through its three
quadrances.  Its Archimedes value is the common numerator in the three spread
ratios, so Exercise 1.1 reduces to two exact finite fraction calculations.
Exercise 1.2 asks the reader to inspect other books; it makes no mathematical
claim to encode in Lean.
-/

@[expose] public section

namespace formalisations.DivineProportions.Chapters.Examples.ChapterOne

namespace ChapterOneExamples

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

open Purelib.Geometry.Trigonometry.QuadTriple in
/-- The `4,5,7` triangle has the exact denominator-free quadrea `1536`. -/
theorem introductory_quadrea :
    Basic.archimedesFunction (25 : K) 16 49 = 1536 := by
  unfold Basic.archimedesFunction
  ring1

open Purelib.Algebra.Field in
open Purelib.Geometry.Trigonometry.QuadTriple in
/-- Compute the three spread values from quadrances twenty-five, sixteen and forty-nine.

The quadrea quotients are respectively `384/1225`, `24/25` and `24/49`; nonzero two, five and seven certify the required
denominators (Exercise 1.1). -/
theorem exercise_1_1
    (twoNonzero : (2 : K) ≠ 0)
    (fiveNonzero : (5 : K) ≠ 0)
    (sevenNonzero : (7 : K) ≠ 0) :
    let area := Basic.archimedesFunction (25 : K) 16 49
    area / (4 * 25 * 49) = 384 / 1225 ∧
      area / (4 * 25 * 16) = 24 / 25 ∧
      area / (4 * 49 * 16) = 24 / 49 := by
  dsimp only
  rw [introductory_quadrea]
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by ring1]
    exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have sixteenNonzero : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 4 * 4 by ring1]
    exact ExplicitField.mul_ne_zero fourNonzero fourNonzero
  have twentyFiveNonzero : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 * 5 by ring1]
    exact ExplicitField.mul_ne_zero fiveNonzero fiveNonzero
  have fortyNineNonzero : (49 : K) ≠ 0 := by
    rw [show (49 : K) = 7 * 7 by ring1]
    exact ExplicitField.mul_ne_zero sevenNonzero sevenNonzero
  have twelveTwentyFiveNonzero : (1225 : K) ≠ 0 := by
    rw [show (1225 : K) = 25 * 49 by ring1]
    exact ExplicitField.mul_ne_zero twentyFiveNonzero fortyNineNonzero
  have firstDenominatorNonzero : (4 * 25 * 49 : K) ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero fourNonzero twentyFiveNonzero)
      fortyNineNonzero
  have secondDenominatorNonzero : (4 * 25 * 16 : K) ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero fourNonzero twentyFiveNonzero)
      sixteenNonzero
  have thirdDenominatorNonzero : (4 * 49 * 16 : K) ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero fourNonzero fortyNineNonzero)
      sixteenNonzero
  constructor
  · apply Ratio.ratio_eq_of_cross_product firstDenominatorNonzero
      twelveTwentyFiveNonzero
    ring1
  constructor
  · apply Ratio.ratio_eq_of_cross_product secondDenominatorNonzero twentyFiveNonzero
    ring1
  · apply Ratio.ratio_eq_of_cross_product thirdDenominatorNonzero fortyNineNonzero
    ring1

end ChapterOneExamples
end formalisations.DivineProportions.Chapters.Examples.ChapterOne

end

end
