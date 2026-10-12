module
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Group.Basic
import Purelib.Data.Int.Order
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Literal
public import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.Geometry.Trigonometry.SpreadTriple.Quadratic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.SignedFraction.Basic

open Purelib.Algebra.Field
open Purelib.Algebra

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Data.Int

section
@[expose] public section

/-!
# Divine Proportions, Exercise 10.12

The source's complex calculation uses only exact Gaussian-rational arithmetic.
Each value here is therefore represented by a finite pair
`Rational × Rational`, equipped with the project-owned constructive field
operations; no completed complex object is introduced.
-/

namespace formalisations.DivineProportions.Chapters.Triangles.ChapterTenGaussian

namespace ExerciseTenTwelve

/-- The fixed Gaussian quadrance −3 in Exercise 10.12. -/
def q₃ : Gaussian.Basic.Canonical :=
  ⟨(Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨(-3), Int.ofNat 1,
      Order.natCast_pos (by decide)⟩), (Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨0, Int.ofNat 1,
      Order.natCast_pos (by decide)⟩)⟩
/-- The first fixed Gaussian spread, (4 + 2i)/15. -/
def s₁ : Gaussian.Basic.Canonical :=
  ⟨(Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨4, Int.ofNat 15,
      Order.natCast_pos (by decide)⟩), (Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨2, Int.ofNat 15,
      Order.natCast_pos (by decide)⟩)⟩
/-- The second fixed Gaussian spread, (1 + 7i)/24. -/
def s₂ : Gaussian.Basic.Canonical :=
  ⟨(Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨1, Int.ofNat 24,
      Order.natCast_pos (by decide)⟩), (Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨7, Int.ofNat 24,
      Order.natCast_pos (by decide)⟩)⟩

/-- The two roots of the Triple-spread equation, retained internally so that
the two quadrance pairs can be recovered without selecting a square root. -/
def firstThirdSpread : Gaussian.Basic.Canonical :=
  ⟨(Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨(-1), Int.ofNat 40,
      Order.natCast_pos (by decide)⟩),
    (Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨(-3), Int.ofNat 40,
      Order.natCast_pos (by decide)⟩)⟩

/-- The second third-spread root, 271/360 + (71/120)i. -/
def secondThirdSpread : Gaussian.Basic.Canonical :=
  ⟨(Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨271, Int.ofNat 360,
      Order.natCast_pos (by decide)⟩),
    (Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨71, Int.ofNat 120,
      Order.natCast_pos (by decide)⟩)⟩

/-- The first quadrance in the first solution, 8 − 8i. -/
def firstQ₁ : Gaussian.Basic.Canonical :=
  ⟨(Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨8, Int.ofNat 1,
      Order.natCast_pos (by decide)⟩), (Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨(-8), Int.ofNat 1,
      Order.natCast_pos (by decide)⟩)⟩
/-- The second quadrance in the first solution, 11 + 2i. -/
def firstQ₂ : Gaussian.Basic.Canonical :=
  ⟨(Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨11, Int.ofNat 1,
      Order.natCast_pos (by decide)⟩), (Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨2, Int.ofNat 1,
      Order.natCast_pos (by decide)⟩)⟩

/-- The corrected first quadrance in the second solution, (−10872 + 2232i)/11881. -/
def secondQ₁ : Gaussian.Basic.Canonical :=
  ⟨(Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨(-10872), Int.ofNat 11881,
      Order.natCast_pos (by decide)⟩),
    (Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨2232, Int.ofNat 11881,
      Order.natCast_pos (by decide)⟩)⟩

/-- The corrected second quadrance in the second solution, (−7929 − 7578i)/11881. -/
def secondQ₂ : Gaussian.Basic.Canonical :=
  ⟨(Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨(-7929), Int.ofNat 11881,
      Order.natCast_pos (by decide)⟩),
    (Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨(-7578), Int.ofNat 11881,
      Order.natCast_pos (by decide)⟩)⟩

/-- The false second pair printed in the source, retained for the executable
countercheck below. -/
def printedSecondQ₁ : Gaussian.Basic.Canonical :=
  ⟨(Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨10872, Int.ofNat 11881,
      Order.natCast_pos (by decide)⟩),
    (Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨2232, Int.ofNat 11881,
      Order.natCast_pos (by decide)⟩)⟩

/-- The source's uncorrected second quadrance, (7929 − 7578i)/11881. -/
def printedSecondQ₂ : Gaussian.Basic.Canonical :=
  ⟨(Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨7929, Int.ofNat 11881,
      Order.natCast_pos (by decide)⟩),
    (Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨(-7578), Int.ofNat 11881,
      Order.natCast_pos (by decide)⟩)⟩

/-- The three fixed inputs, in the source's ordinary fraction notation. -/
theorem input_values :
    q₃ = ⟨-3, 0⟩ ∧
      s₁ = ⟨(4 : Fraction.Rational) / 15, (2 : Fraction.Rational) / 15⟩ ∧
      s₂ = ⟨(1 : Fraction.Rational) / 24, (7 : Fraction.Rational) / 24⟩ := by
  constructor
  · apply Gaussian.Basic.ext
    · change Fraction.Literal.rationalLiteral (-3) 1 (by decide) = (-3 : Fraction.Rational)
      exact Fraction.Literal.rationalLiteral_denominator_one (-3)
    · change Fraction.Literal.rationalLiteral 0 1 (by decide) = (0 : Fraction.Rational)
      exact Fraction.Literal.rationalLiteral_denominator_one 0
  constructor
  · apply Gaussian.Basic.ext
    · exact Fraction.Literal.rationalLiteral_eq_div 4 15 (by decide)
    · exact Fraction.Literal.rationalLiteral_eq_div 2 15 (by decide)
  · apply Gaussian.Basic.ext
    · exact Fraction.Literal.rationalLiteral_eq_div 1 24 (by decide)
    · exact Fraction.Literal.rationalLiteral_eq_div 7 24 (by decide)

/-- The two third-spread roots in ordinary fraction notation. -/
theorem third_spread_values :
    firstThirdSpread =
        ⟨(-1 : Fraction.Rational) / 40, (-3 : Fraction.Rational) / 40⟩ ∧
      secondThirdSpread =
        ⟨(271 : Fraction.Rational) / 360, (71 : Fraction.Rational) / 120⟩ := by
  constructor
  · apply Gaussian.Basic.ext
    · exact Fraction.Literal.rationalLiteral_eq_div (-1) 40 (by decide)
    · exact Fraction.Literal.rationalLiteral_eq_div (-3) 40 (by decide)
  · apply Gaussian.Basic.ext
    · exact Fraction.Literal.rationalLiteral_eq_div 271 360 (by decide)
    · exact Fraction.Literal.rationalLiteral_eq_div 71 120 (by decide)

/-- The two corrected quadrance pairs in ordinary fraction notation. -/
theorem quadrance_values :
    (firstQ₁ = ⟨8, -8⟩ ∧ firstQ₂ = ⟨11, 2⟩) ∧
      (secondQ₁ =
          ⟨((-10872 : Int) : Fraction.Rational) / 11881,
            (2232 : Fraction.Rational) / 11881⟩ ∧
        secondQ₂ =
          ⟨((-7929 : Int) : Fraction.Rational) / 11881,
            ((-7578 : Int) : Fraction.Rational) / 11881⟩) := by
  constructor
  · constructor
    · apply Gaussian.Basic.ext
      · exact Fraction.Literal.rationalLiteral_denominator_one 8
      · exact Fraction.Literal.rationalLiteral_denominator_one (-8)
    · apply Gaussian.Basic.ext
      · exact Fraction.Literal.rationalLiteral_denominator_one 11
      · exact Fraction.Literal.rationalLiteral_denominator_one 2
  · constructor
    · apply Gaussian.Basic.ext
      · exact Fraction.Literal.rationalLiteral_eq_div (-10872) 11881 (by decide)
      · exact Fraction.Literal.rationalLiteral_eq_div 2232 11881 (by decide)
    · apply Gaussian.Basic.ext
      · exact Fraction.Literal.rationalLiteral_eq_div (-7929) 11881 (by decide)
      · exact Fraction.Literal.rationalLiteral_eq_div (-7578) 11881 (by decide)

/-- The source's uncorrected second pair, in ordinary fraction notation. -/
theorem printed_quadrance_values :
    printedSecondQ₁ =
        ⟨(10872 : Fraction.Rational) / 11881, (2232 : Fraction.Rational) / 11881⟩ ∧
      printedSecondQ₂ =
        ⟨(7929 : Fraction.Rational) / 11881,
          ((-7578 : Int) : Fraction.Rational) / 11881⟩ := by
  constructor
  · apply Gaussian.Basic.ext
    · exact Fraction.Literal.rationalLiteral_eq_div 10872 11881 (by decide)
    · exact Fraction.Literal.rationalLiteral_eq_div 2232 11881 (by decide)
  · apply Gaussian.Basic.ext
    · exact Fraction.Literal.rationalLiteral_eq_div 7929 11881 (by decide)
    · exact Fraction.Literal.rationalLiteral_eq_div (-7578) 11881 (by decide)

/-- The sum of the two retained third-spread roots is 2(s₁ + s₂) − 4s₁s₂. -/
private theorem root_sum :
    firstThirdSpread + secondThirdSpread =
      2 * (s₁ + s₂) - 4 * s₁ * s₂ := by
  apply Gaussian.Basic.ext <;> decide

/-- The constant term of the triple-spread quadratic is minus the product of the two retained roots. -/
private theorem root_product :
    (s₁ + s₂) ^ 2 - 2 * (s₁ ^ 2 + s₂ ^ 2) =
      -(firstThirdSpread * secondThirdSpread) := by
  apply Gaussian.Basic.ext <;> decide

/-- The first retained third-spread root is nonzero. -/
private theorem firstThirdSpreadNonzero : firstThirdSpread ≠ 0 := by
  intro zero
  have realZero := congrArg Gaussian.Basic.re zero
  exact (by decide : firstThirdSpread.re ≠ 0) realZero

/-- The second retained third-spread root is nonzero. -/
private theorem secondThirdSpreadNonzero : secondThirdSpread ≠ 0 := by
  intro zero
  have realZero := congrArg Gaussian.Basic.re zero
  exact (by decide : secondThirdSpread.re ≠ 0) realZero

/-- The first quadrance pair satisfies both denominator-cleared spread-law equations. -/
private theorem first_solution_products :
    firstThirdSpread * firstQ₁ = s₁ * q₃ ∧
      firstThirdSpread * firstQ₂ = s₂ * q₃ := by
  constructor <;>
    apply Gaussian.Basic.ext <;> decide

/-- The corrected second quadrance pair satisfies both denominator-cleared spread-law equations. -/
private theorem second_solution_products :
    secondThirdSpread * secondQ₁ = s₁ * q₃ ∧
      secondThirdSpread * secondQ₂ = s₂ * q₃ := by
  constructor <;>
    apply Gaussian.Basic.ext <;> decide +kernel

/-- The Triple-spread equation is exactly a quadratic with the two displayed
Gaussian-rational roots. -/
theorem triple_spread_factorization (thirdSpread : Gaussian.Basic.Canonical) :
    Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple s₁ s₂ thirdSpread ↔
      (thirdSpread - firstThirdSpread) *
        (thirdSpread - secondThirdSpread) = 0 := by
  have identity :
      Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction s₁ s₂ thirdSpread =
        -((thirdSpread - firstThirdSpread) *
          (thirdSpread - secondThirdSpread)) :=
    Geometry.Trigonometry.SpreadTriple.Quadratic.factorization_identity s₁ s₂ firstThirdSpread secondThirdSpread
      thirdSpread root_sum root_product
  constructor
  · intro spreadTriple
    unfold Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple at spreadTriple
    have negativeProductZero :
        -((thirdSpread - firstThirdSpread) *
          (thirdSpread - secondThirdSpread)) = 0 := by
      calc
        -((thirdSpread - firstThirdSpread) *
            (thirdSpread - secondThirdSpread)) =
          Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction s₁ s₂ thirdSpread := identity.symm
        _ = 0 := spreadTriple
    exact Group.eq_zero_of_neg_eq_zero negativeProductZero
  · intro productZero
    unfold Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple
    calc
      Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction s₁ s₂ thirdSpread =
          -((thirdSpread - firstThirdSpread) *
            (thirdSpread - secondThirdSpread)) := identity
      _ = 0 := by rw [productZero]; exact neg_zero

/-- The two possible third spreads, obtained by direct finite factor
elimination rather than a selected quadratic root. -/
theorem third_spread_alternatives (thirdSpread : Gaussian.Basic.Canonical)
    (spreadTriple : Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple s₁ s₂ thirdSpread) :
    thirdSpread = firstThirdSpread ∨
      thirdSpread = secondThirdSpread := by
  have factored := (triple_spread_factorization thirdSpread).1 spreadTriple
  by_cases firstFactorZero : thirdSpread - firstThirdSpread = 0
  · exact Or.inl (Group.eq_of_sub_eq_zero firstFactorZero)
  · have secondFactorZero : thirdSpread - secondThirdSpread = 0 := by
      by_cases zero : thirdSpread - secondThirdSpread = 0
      · exact zero
      · exact False.elim
          ((ExplicitField.mul_ne_zero firstFactorZero zero) factored)
    exact Or.inr (Group.eq_of_sub_eq_zero secondFactorZero)

/-- Exercise 10.12.  The two premises are the denominator-free Spread-law
relations with the printed `Q₃`, `s₁`, and `s₂`.  They force exactly the first
quadrance pair in the source and the sign-corrected second pair. -/
theorem exercise_10_12
    (q₁ q₂ thirdSpread : Gaussian.Basic.Canonical)
    (spreadTriple : Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple s₁ s₂ thirdSpread)
    (firstSpreadLaw : s₁ * q₃ = thirdSpread * q₁)
    (secondSpreadLaw : s₂ * q₃ = thirdSpread * q₂) :
    (q₁ = firstQ₁ ∧ q₂ = firstQ₂) ∨
      (q₁ = secondQ₁ ∧ q₂ = secondQ₂) := by
  rcases third_spread_alternatives thirdSpread spreadTriple with
    firstRoot | secondRoot
  · rw [firstRoot] at firstSpreadLaw secondSpreadLaw
    apply Or.inl
    constructor
    · apply Purelib.Data.Gaussian.Field.eq_of_mul_eq_mul_left firstThirdSpreadNonzero
      calc
        firstThirdSpread * q₁ = s₁ * q₃ := firstSpreadLaw.symm
        _ = firstThirdSpread * firstQ₁ := first_solution_products.1.symm
    · apply Purelib.Data.Gaussian.Field.eq_of_mul_eq_mul_left firstThirdSpreadNonzero
      calc
        firstThirdSpread * q₂ = s₂ * q₃ := secondSpreadLaw.symm
        _ = firstThirdSpread * firstQ₂ := first_solution_products.2.symm
  · rw [secondRoot] at firstSpreadLaw secondSpreadLaw
    apply Or.inr
    constructor
    · apply Purelib.Data.Gaussian.Field.eq_of_mul_eq_mul_left secondThirdSpreadNonzero
      calc
        secondThirdSpread * q₁ = s₁ * q₃ := firstSpreadLaw.symm
        _ = secondThirdSpread * secondQ₁ :=
          second_solution_products.1.symm
    · apply Purelib.Data.Gaussian.Field.eq_of_mul_eq_mul_left secondThirdSpreadNonzero
      calc
        secondThirdSpread * q₂ = s₂ * q₃ := secondSpreadLaw.symm
        _ = secondThirdSpread * secondQ₂ :=
          second_solution_products.2.symm

/-- Both corrected pairs really satisfy the Triple-spread and Spread-law data. -/
theorem displayed_solutions :
    (Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple s₁ s₂ firstThirdSpread ∧
      s₁ * q₃ = firstThirdSpread * firstQ₁ ∧
      s₂ * q₃ = firstThirdSpread * firstQ₂) ∧
    (Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple s₁ s₂ secondThirdSpread ∧
      s₁ * q₃ = secondThirdSpread * secondQ₁ ∧
      s₂ * q₃ = secondThirdSpread * secondQ₂) := by
  constructor
  · refine ⟨(triple_spread_factorization firstThirdSpread).2 ?_,
      first_solution_products.1.symm, first_solution_products.2.symm⟩
    rw [Gaussian.Basic.sub_self,
      Gaussian.Basic.zero_mul]
  · refine ⟨(triple_spread_factorization secondThirdSpread).2 ?_,
      second_solution_products.1.symm, second_solution_products.2.symm⟩
    rw [Gaussian.Basic.sub_self,
      Gaussian.Basic.mul_zero]

/-- The source's second pair has both real-part signs wrong.  Already its
first displayed Spread-law cross-product fails. -/
theorem printed_second_pair_counterexample :
    ¬ (s₁ * q₃ = secondThirdSpread * printedSecondQ₁ ∧
      s₂ * q₃ = secondThirdSpread * printedSecondQ₂) := by
  rintro ⟨firstPrintedLaw, _⟩
  have realPartsEqual :=
    congrArg Gaussian.Basic.re firstPrintedLaw
  exact (by
      decide : (s₁ * q₃).re ≠ (secondThirdSpread * printedSecondQ₁).re) realPartsEqual

end ExerciseTenTwelve

end formalisations.DivineProportions.Chapters.Triangles.ChapterTenGaussian

end
