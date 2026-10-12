module
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Group.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Eleven
import Purelib.Algebra.Field.SquareObstruction.Frobenius
import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Normalized
import Purelib.Geometry.Plane.Line.Nullity
import Purelib.Geometry.Plane.Reflection.Iteration.Line
import Purelib.Geometry.Plane.Reflection.Line
import Purelib.Geometry.Plane.Reflection.Line.Normalized
import Purelib.Geometry.Stars.Regular.OrderFive.Basic
public import Purelib.Geometry.Stars.Regular.OrderFive.Construction
import Purelib.Geometry.Stars.Regular.OrderSeven.Basic
public import Purelib.Geometry.Stars.Regular.OrderSeven.Construction
import Purelib.Geometry.Stars.Regular.OrderThree.Basic
import Purelib.Geometry.Stars.Regular.OrderThree.Classification
public import Purelib.Geometry.Stars.Regular.OrderThree.Construction
public import Purelib.Geometry.Trigonometry.Spread.Number.Basic
import Purelib.Geometry.Trigonometry.SpreadNumber.Obstruction
import Purelib.NumberTheory.SquareClass.Rational.Nonsquare
import Purelib.Polynomial.Ascending.Integer.Basic
import Purelib.Polynomial.Ascending.Integer.Bezout
import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Roots.Five
import Purelib.Polynomial.Recurrence.Spread.Values
public import Purelib.Algebra.Field.Finite.Nineteen
import Purelib.Data.Rat.Fraction.Compatibility

import Purelib.Geometry.Plane.Reflection.Iteration
public import Purelib.Algebra.Field.Finite.Thirteen
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Ring.Defs
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.Geometry.Plane

open Purelib

open Purelib.Algebra

section
@[expose] public section

/-!
# Divine Proportions, Theorem 95: regular stars of order three

The three-line star is finite data.  Its cyclic rule stores the three
reflection-lineation equations explicitly, and mutual nonparallelism replaces
any appeal to a global collection of lines.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFourteen

variable {K : Type*} [ExplicitField K]

/-- Example 14.2: `5² = 3` in `F₁₁`, yielding the printed regular star with
line parameters `0`, `5`, and `6 = -5`. -/
theorem example_14_2_fieldEleven :
    Nonempty (Geometry.Stars.Regular.OrderThree.Basic.RegularThreeStar Finite.Eleven.Element) := by
  apply (Geometry.Stars.Regular.OrderThree.Classification.order_three_star (K := Finite.Eleven.Element) (by decide)).2
  exact ⟨5, by decide, by decide⟩

end formalisations.DivineProportions.Chapters.Examples.ChapterFourteen

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 14 examples

The prime-field exclusions are stated through the exact finite Frobenius law
used by Euler's square test.  This avoids enumerating a carrier or searching
globally for roots.  The positive examples retain the literal source lines.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFourteen

namespace ChapterFourteenExamples
namespace ExampleFourteenOne

variable {K : Type*} [ExplicitField K] [Nontrivial K] [DecidableEq K]

/-- Failure of three to be a nonzero square excludes every regular order-three star when two is nonzero. -/
private theorem no_star_of_not_square
    (twoNonzero : (2 : K) ≠ 0) (notSquare : ¬ Purelib.Algebra.Field.Squares.IsNonzeroSquare (3 : K)) :
    ¬ Nonempty (Geometry.Stars.Regular.OrderThree.Basic.RegularThreeStar K) := by
  intro star
  exact notSquare ((Geometry.Stars.Regular.OrderThree.Classification.order_three_star twoNonzero).1 star)

/-- The `F₃` clause: here the scalar `3` itself vanishes. -/
theorem field_three
    (threeZero : (3 : K) = 0) (twoNonzero : (2 : K) ≠ 0) :
    ¬ Nonempty (Geometry.Stars.Regular.OrderThree.Basic.RegularThreeStar K) := by
  apply no_star_of_not_square twoNonzero
  rintro ⟨root, rootNonzero, threeSquare⟩
  have squareZero : root ^ 2 = 0 := threeSquare.symm.trans threeZero
  have squareNonzero : root ^ 2 ≠ 0 := by
    simpa [pow_two] using
      ExplicitField.mul_ne_zero rootNonzero rootNonzero
  exact squareNonzero squareZero

/-- The `F₅` clause, using `3²=-1` and `x⁵=x`. -/
theorem field_five
    (fiveZero : (5 : K) = 0) (frobenius : ∀ value : K, value ^ 5 = value) :
    ¬ Nonempty (Geometry.Stars.Regular.OrderThree.Basic.RegularThreeStar K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 3 * 2 - 5 := by ring1
      _ = 0 := by rw [twoZero, fiveZero]; ring1
  apply no_star_of_not_square twoNonzero
  apply SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg 3 2 twoNonzero
  · calc
      (3 : K) ^ 2 = -1 + 2 * 5 := by ring1
      _ = -1 := by rw [fiveZero]; ring1
  · simpa only using frobenius

/-- The `F₇` clause, using `3³=-1` and `x⁷=x`. -/
theorem field_seven
    (sevenZero : (7 : K) = 0)
    (frobenius : ∀ value : K, value ^ 7 = value) :
    ¬ Nonempty (Geometry.Stars.Regular.OrderThree.Basic.RegularThreeStar K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 4 * 2 - 7 := by ring1
      _ = 0 := by rw [twoZero, sevenZero]; ring1
  apply no_star_of_not_square twoNonzero
  apply SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg 3 3 twoNonzero
  · calc
      (3 : K) ^ 3 = -1 + 4 * 7 := by ring1
      _ = -1 := by rw [sevenZero]; ring1
  · simpa only using frobenius

/-- The `F₁₇` clause, using `3⁸=-1` and `x¹⁷=x`. -/
theorem field_seventeen
    (seventeenZero : (17 : K) = 0)
    (frobenius : ∀ value : K, value ^ 17 = value) :
    ¬ Nonempty (Geometry.Stars.Regular.OrderThree.Basic.RegularThreeStar K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 9 * 2 - 17 := by ring1
      _ = 0 := by rw [twoZero, seventeenZero]; ring1
  apply no_star_of_not_square twoNonzero
  apply SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg 3 8 twoNonzero
  · calc
      (3 : K) ^ 8 = -1 + 386 * 17 := by ring1
      _ = -1 := by rw [seventeenZero]; ring1
  · simpa only using frobenius

/-- The `F₁₉` clause, using `3⁹=-1` and `x¹⁹=x`. -/
theorem field_nineteen
    (nineteenZero : (19 : K) = 0)
    (frobenius : ∀ value : K, value ^ 19 = value) :
    ¬ Nonempty (Geometry.Stars.Regular.OrderThree.Basic.RegularThreeStar K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 10 * 2 - 19 := by ring1
      _ = 0 := by rw [twoZero, nineteenZero]; ring1
  apply no_star_of_not_square twoNonzero
  apply SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg 3 9 twoNonzero
  · calc
      (3 : K) ^ 9 = -1 + 1036 * 19 := by ring1
      _ = -1 := by rw [nineteenZero]; ring1
  · simpa only using frobenius

end ExampleFourteenOne

namespace ExampleFourteenThree

/-- The source's literal `F₁₃` star from the square root `4²=3`. -/
def star : Geometry.Stars.Regular.OrderThree.Basic.RegularThreeStar Finite.Thirteen.Element :=
  Geometry.Stars.Regular.OrderThree.Construction.orderThreeStar 4 (by decide) (by decide) (by decide)

/-- The characteristic-thirteen star has normalized line coefficients (0, 1), (4, 1) and (9, 1). -/
theorem example_14_3 :
    star.line₀.a = 0 ∧ star.line₀.b = 1 ∧
      star.line₁.a = 4 ∧ star.line₁.b = 1 ∧
      star.line₂.a = 9 ∧ star.line₂.b = 1 := by
  decide

end ExampleFourteenThree

namespace ExampleFourteenFour

/-- The rational clause of Example 14.4: the exact reduced-fraction
certificate excludes a square root of three and hence an order-three star. -/
theorem example_14_4 : ¬ Nonempty (Geometry.Stars.Regular.OrderThree.Basic.RegularThreeStar Fraction.Rational) := by
  intro star
  have twoNonzero : (2 : Fraction.Rational) ≠ 0 := by decide
  have rationalNontrivial : Nontrivial Fraction.Rational := by
    constructor
    refine ⟨0, 1, ?_⟩
    intro zeroOne
    apply twoNonzero
    calc
      (2 : Fraction.Rational) = 1 + 1 := by ring1
      _ = 0 + 0 := by rw [← zeroOne]
      _ = 0 := by ring1
  rcases (Geometry.Stars.Regular.OrderThree.Classification.order_three_star (K := Fraction.Rational) twoNonzero).1 star
    with
    ⟨root, _rootNonzero, threeSquare⟩
  exact NumberTheory.SquareClass.Rational.Nonsquare.square_ne_three root threeSquare.symm

end ExampleFourteenFour
namespace ExampleFourteenFive

variable {K : Type*} [ExplicitField K] [Nontrivial K] [DecidableEq K]

/-- The `F₃` order-five polynomial has no nonzero root. -/
theorem field_three
    (threeZero : (3 : K) = 0)
    (frobenius : ∀ value : K, value ^ 3 = value)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 5 value = 0) :
    value = 0 := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 2 * 2 - 3 := by ring1
      _ = 0 := by rw [twoZero, threeZero]; ring1
  have fiveNonzero : (5 : K) ≠ 0 := by
    intro fiveZero
    apply twoNonzero
    calc
      (2 : K) = 5 - 3 := by ring1
      _ = 0 := by rw [fiveZero, threeZero]; ring1
  apply Polynomial.Recurrence.Spread.Roots.Five.only_zero_of_five_nonsquare fiveNonzero
  apply SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg 5 1 twoNonzero
  · calc
      (5 : K) ^ 1 = -1 + 2 * 3 := by ring1
      _ = -1 := by rw [threeZero]; ring1
  · simpa only using frobenius
  · exact polynomialZero

omit [Nontrivial K] in
/-- In characteristic five the displayed polynomial is exactly `s⁵`, so
again its only root is zero. -/
theorem field_five
    (fiveZero : (5 : K) = 0)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 5 value = 0) :
    value = 0 := by
  have factorAsSquare :
      5 - 20 * value + 16 * value ^ 2 = value ^ 2 := by
    calc
      5 - 20 * value + 16 * value ^ 2 =
          value ^ 2 + (1 - 4 * value + 3 * value ^ 2) * 5 := by ring1
      _ = value ^ 2 := by rw [fiveZero]; ring1
  rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_five_formula, factorAsSquare] at polynomialZero
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa [pow_two] using ExplicitField.mul_ne_zero
        valueZero valueZero
    have fourthNonzero := ExplicitField.mul_ne_zero
      squareNonzero squareNonzero
    apply False.elim
    exact (ExplicitField.mul_ne_zero valueZero (by
      simpa [pow_two] using fourthNonzero)) polynomialZero

/-- The `F₇` order-five polynomial has no nonzero root. -/
theorem field_seven
    (sevenZero : (7 : K) = 0)
    (frobenius : ∀ value : K, value ^ 7 = value)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 5 value = 0) :
    value = 0 := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 4 * 2 - 7 := by ring1
      _ = 0 := by rw [twoZero, sevenZero]; ring1
  have fiveNonzero : (5 : K) ≠ 0 := by
    intro fiveZero
    apply twoNonzero
    calc
      (2 : K) = 7 - 5 := by ring1
      _ = 0 := by rw [sevenZero, fiveZero]; ring1
  apply Polynomial.Recurrence.Spread.Roots.Five.only_zero_of_five_nonsquare fiveNonzero
  apply SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg 5 3 twoNonzero
  · calc
      (5 : K) ^ 3 = -1 + 18 * 7 := by ring1
      _ = -1 := by rw [sevenZero]; ring1
  · simpa only using frobenius
  · exact polynomialZero

/-- The `F₁₃` order-five polynomial has no nonzero root. -/
theorem field_thirteen
    (thirteenZero : (13 : K) = 0)
    (frobenius : ∀ value : K, value ^ 13 = value)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 5 value = 0) :
    value = 0 := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 7 * 2 - 13 := by ring1
      _ = 0 := by rw [twoZero, thirteenZero]; ring1
  have fiveNonzero : (5 : K) ≠ 0 := by
    intro fiveZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 2 * 13 - 5 * 5 := by ring1
      _ = 0 := by rw [thirteenZero, fiveZero]; ring1
  apply Polynomial.Recurrence.Spread.Roots.Five.only_zero_of_five_nonsquare fiveNonzero
  apply SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg 5 6 twoNonzero
  · calc
      (5 : K) ^ 6 = -1 + 1202 * 13 := by ring1
      _ = -1 := by rw [thirteenZero]; ring1
  · simpa only using frobenius
  · exact polynomialZero

/-- The `F₁₇` order-five polynomial has no nonzero root. -/
theorem field_seventeen
    (seventeenZero : (17 : K) = 0)
    (frobenius : ∀ value : K, value ^ 17 = value)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 5 value = 0) :
    value = 0 := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 9 * 2 - 17 := by ring1
      _ = 0 := by rw [twoZero, seventeenZero]; ring1
  have fiveNonzero : (5 : K) ≠ 0 := by
    intro fiveZero
    apply twoNonzero
    calc
      (2 : K) = 17 - 3 * 5 := by ring1
      _ = 0 := by rw [seventeenZero, fiveZero]; ring1
  apply Polynomial.Recurrence.Spread.Roots.Five.only_zero_of_five_nonsquare fiveNonzero
  apply SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg 5 8 twoNonzero
  · calc
      (5 : K) ^ 8 = -1 + 22978 * 17 := by ring1
      _ = -1 := by rw [seventeenZero]; ring1
  · simpa only using frobenius
  · exact polynomialZero

end ExampleFourteenFive

namespace ExampleFourteenSix

variable {K : Type*} [ExplicitField K] [Nontrivial K] [DecidableEq K]

/-- Over the prime-field arithmetic of characteristic eleven, the only
roots of `S₅` are the printed values `0`, `7`, and `8`. -/
theorem root_classification
    (elevenZero : (11 : K) = 0) (value : K) :
    Polynomial.Recurrence.Spread.Basic.spreadPolynomial 5 value = 0 ↔
      value = 0 ∨ value = 7 ∨ value = 8 := by
  rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_five_formula]
  constructor
  · intro productZero
    by_cases valueZero : value = 0
    · exact Or.inl valueZero
    · right
      have factorSquareZero :
          (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0 := by
        by_cases zero : (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0
        · exact zero
        · exact False.elim
            ((ExplicitField.mul_ne_zero valueZero zero) productZero)
      have factorZero := (fun {K : Type _} [ExplicitField K] [DecidableEq K] {value : K}
        (squareZero : value ^ 2 = 0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value
        squareZero : value = 0)) factorSquareZero
      have factored : (5 : K) * (value - 7) * (value - 8) = 0 := by
        calc
          (5 : K) * (value - 7) * (value - 8) =
              (5 - 20 * value + 16 * value ^ 2) +
                (25 - 5 * value - value ^ 2) * 11 := by ring1
          _ = 0 := by rw [factorZero, elevenZero]; ring1
      have fiveNonzero : (5 : K) ≠ 0 := by
        intro fiveZero
        apply (one_ne_zero : (1 : K) ≠ 0)
        calc
          (1 : K) = 11 - 2 * 5 := by ring1
          _ = 0 := by rw [elevenZero, fiveZero]; ring1
      by_cases firstZero : value - 7 = 0
      · exact Or.inl (Group.eq_of_sub_eq_zero firstZero)
      · right
        apply Group.eq_of_sub_eq_zero
        by_cases secondZero : value - 8 = 0
        · exact secondZero
        · exact False.elim
            ((ExplicitField.mul_ne_zero
              (ExplicitField.mul_ne_zero fiveNonzero firstZero)
              secondZero) factored)
  · intro alternatives
    rcases alternatives with valueZero | valueSeven | valueEight
    · rw [valueZero]; ring1
    · rw [valueSeven]
      calc
        (7 : K) * (5 - 20 * 7 + 16 * 7 ^ 2) ^ 2 =
            7 * (59 * 11) ^ 2 := by ring1
        _ = 0 := by rw [elevenZero]; ring1
    · rw [valueEight]
      calc
        (8 : K) * (5 - 20 * 8 + 16 * 8 ^ 2) ^ 2 =
            8 * (79 * 11) ^ 2 := by ring1
        _ = 0 := by rw [elevenZero]; ring1

/-- The two nonzero roots `7` and `8` are not spread numbers in `F₁₁`;
the finite obstructions are respectively that `2` and `-1` are nonsquares. -/
theorem nonzero_roots_not_spread
    (elevenZero : (11 : K) = 0)
    (frobenius : ∀ value : K, value ^ 11 = value) :
    ¬ Geometry.Trigonometry.Spread.Number.Basic.IsSpreadNumber (7 : K) ∧ ¬
      Geometry.Trigonometry.Spread.Number.Basic.IsSpreadNumber (8 : K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 6 * 2 - 11 := by ring1
      _ = 0 := by rw [twoZero, elevenZero]; ring1
  have twoNotSquare :=
    SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg (2 : K) 5 twoNonzero (by
      calc
        (2 : K) ^ 5 = -1 + 3 * 11 := by ring1
        _ = -1 := by rw [elevenZero]; ring1) (by simpa only using frobenius)
  have negativeOneNotSquare :=
    SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg (-1 : K) 5 twoNonzero (by
      ring1) (by simpa only using frobenius)
  constructor
  · rintro ⟨root, rootSquare⟩
    apply twoNotSquare
    have radicand : (7 : K) * (1 - 7) = 2 := by
      calc
        (7 : K) * (1 - 7) = 2 - 4 * 11 := by ring1
        _ = 2 := by rw [elevenZero]; ring1
    have rootNonzero : root ≠ 0 := by
      intro rootZero
      apply twoNonzero
      calc
        (2 : K) = 7 * (1 - 7) := radicand.symm
        _ = root ^ 2 := rootSquare
        _ = 0 := by rw [rootZero]; ring1
    exact ⟨root, rootNonzero, radicand.symm.trans rootSquare⟩
  · rintro ⟨root, rootSquare⟩
    apply negativeOneNotSquare
    have radicand : (8 : K) * (1 - 8) = -1 := by
      calc
        (8 : K) * (1 - 8) = -1 - 5 * 11 := by ring1
        _ = -1 := by rw [elevenZero]; ring1
    have rootNonzero : root ≠ 0 := by
      intro rootZero
      apply (one_ne_zero : (1 : K) ≠ 0)
      calc
        (1 : K) = -((8 : K) * (1 - 8)) := by rw [radicand]; ring1
        _ = -(root ^ 2) := by rw [rootSquare]
        _ = 0 := by rw [rootZero]; ring1
    exact ⟨root, rootNonzero, radicand.symm.trans rootSquare⟩

end ExampleFourteenSix

namespace ExampleFourteenSeven

/-- The source's literal `F₁₉` star is the order-five construction
with `r=9` and `v=7`, normalized to slopes `0,2,5,-5,-2`. -/
def star : Geometry.Stars.Regular.OrderFive.Basic.RegularFiveStar Finite.Nineteen.Element :=
  Geometry.Stars.Regular.OrderFive.Construction.orderFiveStar 9 7 (by decide) (by decide) (by decide) (by decide)

/-- The characteristic-nineteen line with coefficients (slope, 1, 0). -/
private def printedLine (slope : Finite.Nineteen.Element) : Geometry.Plane.Line Finite.Nineteen.Element where
  a := slope
  b := 1
  c := 0
  direction_nonzero := Or.inr (by decide)

/-- The five constructed star lines are equivalent to the displayed slopes 0, 2, 5, −5 and −2. -/
theorem example_14_7_lines :
    star.line₀.Equivalent
        { a := 0, b := 1, c := 0, direction_nonzero := Or.inr (by decide) } ∧
      star.line₁.Equivalent
        { a := 2, b := 1, c := 0, direction_nonzero := Or.inr (by decide) } ∧
      star.line₂.Equivalent
        { a := 5, b := 1, c := 0, direction_nonzero := Or.inr (by decide) } ∧
      star.line₃.Equivalent
        { a := -5, b := 1, c := 0, direction_nonzero := Or.inr (by decide) } ∧
      star.line₄.Equivalent
        { a := -2, b := 1, c := 0, direction_nonzero := Or.inr (by decide) } := by
  change star.line₀.Equivalent (printedLine 0) ∧
    star.line₁.Equivalent (printedLine 2) ∧
    star.line₂.Equivalent (printedLine 5) ∧
    star.line₃.Equivalent (printedLine (-5)) ∧
    star.line₄.Equivalent (printedLine (-2))
  unfold Geometry.Plane.Line.Equivalent star Geometry.Stars.Regular.OrderFive.Construction.orderFiveStar printedLine
    Line.Basic.xAxis
    Geometry.Stars.Regular.OrderFive.Construction.orderFiveLine₁
      Geometry.Stars.Regular.OrderFive.Construction.orderFiveLine₂
      Geometry.Stars.Regular.OrderFive.Construction.orderFiveLine₃
      Geometry.Stars.Regular.OrderFive.Construction.orderFiveLine₄
  decide

/-- The two printed nonzero roots and their spread-number witnesses. -/
theorem example_14_7_values :
    Polynomial.Recurrence.Spread.Basic.spreadPolynomial 5 (9 : Finite.Nineteen.Element) = 0 ∧
      Polynomial.Recurrence.Spread.Basic.spreadPolynomial 5 (16 : Finite.Nineteen.Element) = 0 ∧
      Geometry.Trigonometry.Spread.Number.Basic.IsSpreadNumber (9 : Finite.Nineteen.Element) ∧
        Geometry.Trigonometry.Spread.Number.Basic.IsSpreadNumber (16 : Finite.Nineteen.Element) := by
  refine ⟨by decide, by decide, ⟨2, by decide⟩, ⟨8, by decide⟩⟩

end ExampleFourteenSeven

namespace ExampleFourteenEight

namespace Certificate

/-- Ascending integer coefficients of the cubic factor in `S₇`. -/
private def cubic : List Int := [7, -56, 112, -64]

/-- Evaluation of the retained cubic coefficient list gives 7 − 56s + 112s² − 64s³. -/
private theorem eval_cubic
    {K : Type*} [ExplicitField K] (value : K) :
    Purelib.Polynomial.Ascending.Integer.Basic.eval cubic value =
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 := by
  simp only [cubic, Polynomial.Ascending.Integer.Basic.eval_cons, Polynomial.Ascending.Integer.Basic.eval_nil]
  ring1

/-- Literal finite Bezout certificate modulo three. -/
private def three : Purelib.Polynomial.Ascending.Integer.Bezout.BezoutCertificate 3 cubic where
  left := [1, 0, 1]
  right := [1, -1, 1]
  correction := [2, -19, 40, -40, 37, -21]
  identity := by decide

/-- Literal finite Bezout certificate modulo five. -/
private def five : Purelib.Polynomial.Ascending.Integer.Bezout.BezoutCertificate 5 cubic where
  left := [-2, -1, 2, 1, -1]
  right := [0, 1, 1]
  correction := [-3, 21, -31, -18, 45, 8, -35, 13]
  identity := by decide

/-- Literal finite Bezout certificate modulo eleven. -/
private def eleven : Purelib.Polynomial.Ascending.Integer.Bezout.BezoutCertificate 11 cubic where
  left := [-3, -3, -5, 5, 3, 2, -2, 3, 2, 0, -3]
  right := [4, -5, -5]
  correction :=
    [-2, 13, -18, 16, -57, 66, -10, 15, -46, 32, 1, 4, -31, 17]
  identity := by decide

/-- Literal finite Bezout certificate modulo seventeen. -/
private def seventeen : Purelib.Polynomial.Ascending.Integer.Bezout.BezoutCertificate 17 cubic where
  left := [5, -8, -3, 6, 1, 6, -3, -4, -2, 6, 7, 0, 6, -7, 1, 0, 5]
  right := [4, 1, -3]
  correction :=
    [2, -20, 58, -59, -9, 50, -37, 44, -30, -6,
      -15, 24, 26, -49, 63, -72, 35, -20, 33, -19]
  identity := by decide

/-- Literal finite Bezout certificate modulo nineteen. -/
private def nineteen : Purelib.Polynomial.Ascending.Integer.Bezout.BezoutCertificate 19 cubic where
  left :=
    [-8, -7, 1, -5, -6, -5, -6, 7, -5, -6, 1, 4, -9, -2, -1,
      -4, 1, -5, -3]
  right := [0, -3, -2]
  correction :=
    [-3, 21, -26, -19, 42, -17, -6, 11, -41, 74, -35,
      -20, 11, 46, -61, 20, 13, -25, 33, -24, -1, 10]
  identity := by decide

/-- Literal finite Bezout certificate modulo twenty-three. -/
private def twentyThree : Purelib.Polynomial.Ascending.Integer.Bezout.BezoutCertificate 23 cubic where
  left :=
    [10, 11, -4, -7, 10, 1, -9, 10, -10, 3, 6, -6, 5, -3, -11,
      9, 7, 2, 6, 11, 7, -6, 3]
  right := [0, -7, 8]
  correction :=
    [3, -21, 21, 33, -30, -47, 63, 2, -74, 99, -82, 26, 37,
      -59, 45, 1, -65, 58, 6, -21, -1, 18, 19, -56, 31, -8]
  identity := by decide

/-- A finite Bezout certificate and the supplied Frobenius law force every root of the seventh spread polynomial to be
zero.

The modulus vanishes in the explicit field, so the certificate excludes roots of the cubic factor without enumerating
the carrier. -/
private theorem only_zero_of_certificate
    {K : Type*} [ExplicitField K] [Nontrivial K] [DecidableEq K]
    {modulus : Nat} (certificate : Purelib.Polynomial.Ascending.Integer.Bezout.BezoutCertificate modulus cubic)
    (modulusZero : (modulus : K) = 0)
    (frobeniusLaw : ∀ value : K, value ^ modulus = value)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 7 value = 0) :
    value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have cubicNonzero :
        7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 ≠ 0 := by
      intro cubicZero
      apply Polynomial.Ascending.Integer.Bezout.no_common_root certificate modulusZero value
      · rw [eval_cubic]
        exact cubicZero
      · exact frobeniusLaw value
    have cubicSquareNonzero :
        (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 ≠ 0 := by
      simpa [pow_two] using
        ExplicitField.mul_ne_zero cubicNonzero cubicNonzero
    rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula] at polynomialZero
    exact False.elim
      ((ExplicitField.mul_ne_zero valueZero cubicSquareNonzero)
        polynomialZero)

end Certificate

variable {K : Type*} [ExplicitField K] [Nontrivial K] [DecidableEq K]

/-- The characteristic-three clause of Example 14.8. -/
theorem field_three
    (threeZero : (3 : K) = 0)
    (frobenius : ∀ value : K, value ^ 3 = value)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.three threeZero
    frobenius value polynomialZero

/-- The characteristic-five clause of Example 14.8. -/
theorem field_five
    (fiveZero : (5 : K) = 0)
    (frobenius : ∀ value : K, value ^ 5 = value)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.five fiveZero
    frobenius value polynomialZero

omit [Nontrivial K] in
/-- In characteristic seven the cubic factor is `-s³`, so the seventh
spread polynomial again has only its zero root. -/
theorem field_seven
    (sevenZero : (7 : K) = 0)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 7 value = 0) :
    value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have valueSquareNonzero : value ^ 2 ≠ 0 := by
      simpa [pow_two] using
        ExplicitField.mul_ne_zero valueZero valueZero
    have valueCubeNonzero : value ^ 3 ≠ 0 := by
      simpa [pow_succ] using
        ExplicitField.mul_ne_zero valueSquareNonzero valueZero
    have cubicEq :
        7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
          -(value ^ 3) := by
      calc
        7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
            -(value ^ 3) +
              (1 - 8 * value + 16 * value ^ 2 - 9 * value ^ 3) * 7 := by
          ring1
        _ = -(value ^ 3) := by rw [sevenZero]; ring1
    have cubicNonzero :
        7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 ≠ 0 := by
      rw [cubicEq]
      exact Group.neg_ne_zero valueCubeNonzero
    have cubicSquareNonzero :
        (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 ≠ 0 := by
      simpa [pow_two] using
        ExplicitField.mul_ne_zero cubicNonzero cubicNonzero
    rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula] at polynomialZero
    exact False.elim
      ((ExplicitField.mul_ne_zero valueZero cubicSquareNonzero)
        polynomialZero)

/-- The characteristic-eleven clause of Example 14.8. -/
theorem field_eleven
    (elevenZero : (11 : K) = 0)
    (frobenius : ∀ value : K, value ^ 11 = value)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.eleven elevenZero
    frobenius value polynomialZero

/-- The characteristic-seventeen clause of Example 14.8. -/
theorem field_seventeen
    (seventeenZero : (17 : K) = 0)
    (frobenius : ∀ value : K, value ^ 17 = value)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.seventeen seventeenZero
    frobenius value polynomialZero

/-- The characteristic-nineteen clause of Example 14.8. -/
theorem field_nineteen
    (nineteenZero : (19 : K) = 0)
    (frobenius : ∀ value : K, value ^ 19 = value)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.nineteen nineteenZero
    frobenius value polynomialZero

/-- The characteristic-twenty-three clause of Example 14.8. -/
theorem field_twentyThree
    (twentyThreeZero : (23 : K) = 0)
    (frobenius : ∀ value : K, value ^ 23 = value)
    (value : K) (polynomialZero : Polynomial.Recurrence.Spread.Basic.spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.twentyThree
    twentyThreeZero frobenius value polynomialZero

omit [Nontrivial K] in
/-- In characteristic thirteen the cubic factor has exactly the three
printed roots. -/
theorem cubic_root_classification
    (thirteenZero : (13 : K) = 0) (value : K) :
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 = 0 ↔
      value = 2 ∨ value = 5 ∨ value = 11 := by
  have factored :
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
        (value - 2) * (value - 5) * (value - 11) := by
    calc
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
          (value - 2) * (value - 5) * (value - 11) +
            (9 - 11 * value + 10 * value ^ 2 - 5 * value ^ 3) * 13 := by
        ring1
      _ = (value - 2) * (value - 5) * (value - 11) := by
        rw [thirteenZero]
        ring1
  rw [factored]
  constructor
  · intro productZero
    by_cases firstZero : value - 2 = 0
    · exact Or.inl (Group.eq_of_sub_eq_zero firstZero)
    · right
      by_cases secondZero : value - 5 = 0
      · exact Or.inl (Group.eq_of_sub_eq_zero secondZero)
      · right
        apply Group.eq_of_sub_eq_zero
        by_cases thirdZero : value - 11 = 0
        · exact thirdZero
        · exact False.elim
            ((ExplicitField.mul_ne_zero
              (ExplicitField.mul_ne_zero firstZero secondZero)
              thirdZero) productZero)
  · rintro (valueTwo | valueFive | valueEleven)
    · rw [valueTwo]
      ring1
    · rw [valueFive]
      ring1
    · rw [valueEleven]
      ring1

omit [Nontrivial K] in
/-- The complete `S₇` root classification in characteristic thirteen. -/
theorem field_thirteen_roots
    (thirteenZero : (13 : K) = 0) (value : K) :
    Polynomial.Recurrence.Spread.Basic.spreadPolynomial 7 value = 0 ↔
      value = 0 ∨ value = 2 ∨ value = 5 ∨ value = 11 := by
  constructor
  · intro polynomialZero
    rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula] at polynomialZero
    by_cases valueZero : value = 0
    · exact Or.inl valueZero
    · right
      have cubicSquareZero :
          (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 = 0 := by
        by_cases squareZero :
            (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 = 0
        · exact squareZero
        · exact False.elim
            ((ExplicitField.mul_ne_zero valueZero squareZero)
              polynomialZero)
      exact (cubic_root_classification thirteenZero value).1
        ((fun {K : Type _} [ExplicitField K] [DecidableEq K] {value : K} (squareZero : value ^ 2 =
          0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value squareZero : value = 0))
          cubicSquareZero)
  · rintro (valueZero | valueTwo | valueFive | valueEleven)
    · rw [valueZero, Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula]
      ring1
    · rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula,
        (cubic_root_classification thirteenZero value).2 (Or.inl valueTwo)]
      ring1
    · rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula,
        (cubic_root_classification thirteenZero value).2
          (Or.inr (Or.inl valueFive))]
      ring1
    · rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula,
        (cubic_root_classification thirteenZero value).2
          (Or.inr (Or.inr valueEleven))]
      ring1

/-- The three nonzero `S₇` roots in characteristic thirteen are not spread
numbers, exactly as asserted in Example 14.8. -/
theorem field_thirteen_roots_not_spread
    (thirteenZero : (13 : K) = 0)
    (frobenius : ∀ value : K, value ^ 13 = value) :
    ¬ Geometry.Trigonometry.Spread.Number.Basic.IsSpreadNumber (2 : K) ∧
      ¬ Geometry.Trigonometry.Spread.Number.Basic.IsSpreadNumber (5 : K) ∧ ¬
        Geometry.Trigonometry.Spread.Number.Basic.IsSpreadNumber (11 : K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 7 * 2 - 13 := by ring1
      _ = 0 := by rw [twoZero, thirteenZero]; ring1
  have elevenNonzero : (11 : K) ≠ 0 := by
    intro elevenZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 6 * 13 - 7 * 11 := by ring1
      _ = 0 := by rw [thirteenZero, elevenZero]; ring1
  have sixNonzero : (6 : K) ≠ 0 := by
    intro sixZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 13 - 2 * 6 := by ring1
      _ = 0 := by rw [thirteenZero, sixZero]; ring1
  have sevenNonzero : (7 : K) ≠ 0 := by
    intro sevenZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 2 * 7 - 13 := by ring1
      _ = 0 := by rw [sevenZero, thirteenZero]; ring1
  have elevenNotSquare :=
    SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg (11 : K) 6 twoNonzero (by
      calc
        (11 : K) ^ 6 = -1 + 136274 * 13 := by ring1
        _ = -1 := by rw [thirteenZero]; ring1)
      (by simpa only using frobenius)
  have sixNotSquare :=
    SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg (6 : K) 6 twoNonzero (by
      calc
        (6 : K) ^ 6 = -1 + 3589 * 13 := by ring1
        _ = -1 := by rw [thirteenZero]; ring1)
      (by simpa only using frobenius)
  have sevenNotSquare :=
    SquareObstruction.Frobenius.not_nonzeroSquare_of_frobenius_neg (7 : K) 6 twoNonzero (by
      calc
        (7 : K) ^ 6 = -1 + 9050 * 13 := by ring1
        _ = -1 := by rw [thirteenZero]; ring1)
      (by simpa only using frobenius)
  have radicandTwo : (2 : K) * (1 - 2) = 11 := by
    calc
      (2 : K) * (1 - 2) = 11 - 13 := by ring1
      _ = 11 := by rw [thirteenZero]; ring1
  have radicandFive : (5 : K) * (1 - 5) = 6 := by
    calc
      (5 : K) * (1 - 5) = 6 - 2 * 13 := by ring1
      _ = 6 := by rw [thirteenZero]; ring1
  have radicandEleven : (11 : K) * (1 - 11) = 7 := by
    calc
      (11 : K) * (1 - 11) = 7 - 9 * 13 := by ring1
      _ = 7 := by rw [thirteenZero]; ring1
  refine ⟨Geometry.Trigonometry.SpreadNumber.Obstruction.not_spread_of_radicand_nonsquare 2 ?_ ?_,
    Geometry.Trigonometry.SpreadNumber.Obstruction.not_spread_of_radicand_nonsquare 5 ?_ ?_,
    Geometry.Trigonometry.SpreadNumber.Obstruction.not_spread_of_radicand_nonsquare 11 ?_ ?_⟩
  · rw [radicandTwo]
    exact elevenNonzero
  · rw [radicandTwo]
    exact elevenNotSquare
  · rw [radicandFive]
    exact sixNonzero
  · rw [radicandFive]
    exact sixNotSquare
  · rw [radicandEleven]
    exact sevenNonzero
  · rw [radicandEleven]
    exact sevenNotSquare

end ExampleFourteenEight

namespace ExampleFourteenNine

variable {K : Type*} [ExplicitField K] [Nontrivial K] [DecidableEq K]

omit [DecidableEq K] in
/-- Two is nonzero in a nontrivial explicit field where twenty-nine vanishes. -/
private theorem twoNonzero (twentyNineZero : (29 : K) = 0) :
    (2 : K) ≠ 0 := by
  intro twoZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = 15 * 2 - 29 := by ring1
    _ = 0 := by rw [twoZero, twentyNineZero]; ring1

omit [DecidableEq K] in
/-- Six is nonzero in a nontrivial explicit field where twenty-nine vanishes. -/
private theorem sixNonzero (twentyNineZero : (29 : K) = 0) :
    (6 : K) ≠ 0 := by
  intro sixZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = 5 * 6 - 29 := by ring1
    _ = 0 := by rw [sixZero, twentyNineZero]; ring1

omit [Nontrivial K] [DecidableEq K] in
/-- Six is a root of the order-seven cubic factor when twenty-nine vanishes. -/
private theorem cubicSixZero (twentyNineZero : (29 : K) = 0) :
    7 - 56 * (6 : K) + 112 * (6 : K) ^ 2 - 64 * (6 : K) ^ 3 = 0 := by
  calc
    7 - 56 * (6 : K) + 112 * (6 : K) ^ 2 - 64 * (6 : K) ^ 3 =
        -349 * 29 := by ring1
    _ = 0 := by rw [twentyNineZero]; ring1

omit [Nontrivial K] [DecidableEq K] in
/-- Twelve squares to 6(1 − 6) when twenty-nine vanishes, certifying six as a spread number. -/
private theorem twelveSpreadSquare (twentyNineZero : (29 : K) = 0) :
    (12 : K) ^ 2 = 6 * (1 - 6) := by
  calc
    (12 : K) ^ 2 = 6 * (1 - 6) + 6 * 29 := by ring1
    _ = 6 * (1 - 6) := by rw [twentyNineZero]; ring1

/-- The source's characteristic-twenty-nine star, constructed from the
spread `6` and the finite square witness `12²=6(1-6)`. -/
def star (twentyNineZero : (29 : K) = 0) : Geometry.Stars.Regular.OrderSeven.Basic.RegularSevenStar K :=
  Geometry.Stars.Regular.OrderSeven.Construction.orderSevenStar 6 12
    (by
      intro sixZero
      apply (one_ne_zero : (1 : K) ≠ 0)
      calc
        (1 : K) = 5 * 6 - 29 := by ring1
        _ = 0 := by rw [sixZero, twentyNineZero]; ring1)
    (by
      calc
        7 - 56 * (6 : K) + 112 * (6 : K) ^ 2 - 64 * (6 : K) ^ 3 =
            -349 * 29 := by ring1
        _ = 0 := by rw [twentyNineZero]; ring1)
    (by
      calc
        (12 : K) ^ 2 = 6 * (1 - 6) + 6 * 29 := by ring1
        _ = 6 * (1 - 6) := by rw [twentyNineZero]; ring1)
    (by
      intro twoZero
      apply (one_ne_zero : (1 : K) ≠ 0)
      calc
        (1 : K) = 15 * 2 - 29 := by ring1
        _ = 0 := by rw [twoZero, twentyNineZero]; ring1)

/-- The characteristic-twenty-nine star retains the initial pair constructed from spread six and square witness twelve.
-/
private theorem star_initial (twentyNineZero : (29 : K) = 0) :
    (star twentyNineZero).initial =
      Geometry.Stars.Regular.OrderSeven.Construction.orderSevenInitialPair 6 12 (sixNonzero twentyNineZero)
        (twelveSpreadSquare twentyNineZero) := rfl

/-- The characteristic-twenty-nine cubic factor has exactly the three
printed roots `6`, `7`, and `25`. -/
theorem cubic_root_classification
    (twentyNineZero : (29 : K) = 0) (value : K) :
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 = 0 ↔
      value = 6 ∨ value = 7 ∨ value = 25 := by
  have negativeSixNonzero : (-6 : K) ≠ 0 :=
    Group.neg_ne_zero (sixNonzero twentyNineZero)
  have factored :
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
        -6 * ((value - 6) * (value - 7) * (value - 25)) := by
    calc
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
          -6 * ((value - 6) * (value - 7) * (value - 25)) +
            (-217 + 74 * value - 4 * value ^ 2 - 2 * value ^ 3) * 29 := by
        ring1
      _ = -6 * ((value - 6) * (value - 7) * (value - 25)) := by
        rw [twentyNineZero]
        ring1
  rw [factored]
  constructor
  · intro scaledProductZero
    have productZero : (value - 6) * (value - 7) * (value - 25) = 0 := by
      by_cases productZero :
          (value - 6) * (value - 7) * (value - 25) = 0
      · exact productZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero negativeSixNonzero productZero)
            scaledProductZero)
    by_cases firstZero : value - 6 = 0
    · exact Or.inl (Group.eq_of_sub_eq_zero firstZero)
    · right
      by_cases secondZero : value - 7 = 0
      · exact Or.inl (Group.eq_of_sub_eq_zero secondZero)
      · right
        apply Group.eq_of_sub_eq_zero
        by_cases thirdZero : value - 25 = 0
        · exact thirdZero
        · exact False.elim
            ((ExplicitField.mul_ne_zero
              (ExplicitField.mul_ne_zero firstZero secondZero)
              thirdZero) productZero)
  · rintro (valueSix | valueSeven | valueTwentyFive)
    · rw [valueSix]
      ring1
    · rw [valueSeven]
      ring1
    · rw [valueTwentyFive]
      ring1

/-- The complete root classification of `S₇` in characteristic twenty-nine. -/
theorem roots
    (twentyNineZero : (29 : K) = 0) (value : K) :
    Polynomial.Recurrence.Spread.Basic.spreadPolynomial 7 value = 0 ↔
      value = 0 ∨ value = 6 ∨ value = 7 ∨ value = 25 := by
  constructor
  · intro polynomialZero
    rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula] at polynomialZero
    by_cases valueZero : value = 0
    · exact Or.inl valueZero
    · right
      have cubicSquareZero :
          (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 = 0 := by
        by_cases squareZero :
            (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 = 0
        · exact squareZero
        · exact False.elim
            ((ExplicitField.mul_ne_zero valueZero squareZero)
              polynomialZero)
      exact (cubic_root_classification twentyNineZero value).1
        ((fun {K : Type _} [ExplicitField K] [DecidableEq K] {value : K} (squareZero : value ^ 2 =
          0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value squareZero : value = 0))
          cubicSquareZero)
  · rintro (valueZero | valueSix | valueSeven | valueTwentyFive)
    · rw [valueZero, Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula]
      ring1
    · rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula,
        (cubic_root_classification twentyNineZero value).2 (Or.inl valueSix)]
      ring1
    · rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula,
        (cubic_root_classification twentyNineZero value).2
          (Or.inr (Or.inl valueSeven))]
      ring1
    · rw [Polynomial.Recurrence.Spread.Values.spreadPolynomial_seven_formula,
        (cubic_root_classification twentyNineZero value).2
          (Or.inr (Or.inr valueTwentyFive))]
      ring1

omit [Nontrivial K] [DecidableEq K] in
/-- All three nonzero roots are spread numbers, with the literal finite
square witnesses `12`, `4`, and `3`. -/
theorem values_are_spread (twentyNineZero : (29 : K) = 0) :
    Geometry.Trigonometry.Spread.Number.Basic.IsSpreadNumber (6 : K) ∧
      Geometry.Trigonometry.Spread.Number.Basic.IsSpreadNumber (7 : K) ∧
      Geometry.Trigonometry.Spread.Number.Basic.IsSpreadNumber (25 : K) := by
  refine ⟨⟨12, ?_⟩, ⟨4, ?_⟩, ⟨3, ?_⟩⟩
  · exact (twelveSpreadSquare twentyNineZero).symm
  · calc
      (7 : K) * (1 - 7) = 4 ^ 2 - 2 * 29 := by ring1
      _ = 4 ^ 2 := by rw [twentyNineZero]; ring1
  · calc
      (25 : K) * (1 - 25) = 3 ^ 2 - 21 * 29 := by ring1
      _ = 3 ^ 2 := by rw [twentyNineZero]; ring1

/-- The seven lines of the constructed star normalize to the literal source
slopes `0,15,11,20,9,18,14`. -/
theorem lines (twentyNineZero : (29 : K) = 0) :
    (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 0).Equivalent
        { a := 0, b := 1, c := 0,
          direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0) } ∧
      (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 1).Equivalent
        { a := 15, b := 1, c := 0,
          direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0) } ∧
      (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 2).Equivalent
        { a := 11, b := 1, c := 0,
          direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0) } ∧
      (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 3).Equivalent
        { a := 20, b := 1, c := 0,
          direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0) } ∧
      (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 4).Equivalent
        { a := 9, b := 1, c := 0,
          direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0) } ∧
      (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 5).Equivalent
        { a := 18, b := 1, c := 0,
          direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0) } ∧
      (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 6).Equivalent
        { a := 14, b := 1, c := 0,
          direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0) } := by
  change (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 0).Equivalent
      (Line.Normalized.printedLine 0) ∧
    (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 1).Equivalent
      (Line.Normalized.printedLine 15) ∧
    (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 2).Equivalent
      (Line.Normalized.printedLine 11) ∧
    (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 3).Equivalent
      (Line.Normalized.printedLine 20) ∧
    (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 4).Equivalent
      (Line.Normalized.printedLine 9) ∧
    (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 5).Equivalent
      (Line.Normalized.printedLine 18) ∧
    (Reflection.Iteration.reflectionLineAt (star twentyNineZero).initial 6).Equivalent
      (Line.Normalized.printedLine 14)
  let initial := (star twentyNineZero).initial
  have initialEq :
      initial = Geometry.Stars.Regular.OrderSeven.Construction.orderSevenInitialPair 6 12 (sixNonzero twentyNineZero)
        (twelveSpreadSquare twentyNineZero) := by
    unfold initial
    exact star_initial twentyNineZero
  have lineZero :
      (Reflection.Iteration.reflectionLineAt initial 0).Equivalent (Line.Normalized.printedLine 0) := by
    rw [initialEq]
    change (Line.Basic.xAxis (K := K)).Equivalent (Line.Normalized.printedLine 0)
    unfold Geometry.Plane.Line.Equivalent Line.Basic.xAxis Line.Normalized.printedLine
    exact ⟨by ring1, by ring1, by ring1⟩
  have lineOne :
      (Reflection.Iteration.reflectionLineAt initial 1).Equivalent (Line.Normalized.printedLine 15) := by
    rw [initialEq]
    change (Geometry.Stars.Regular.OrderSeven.Construction.orderSevenLine₁ (K := K) 6 12
      (sixNonzero twentyNineZero)).Equivalent (Line.Normalized.printedLine 15)
    unfold Geometry.Plane.Line.Equivalent Geometry.Stars.Regular.OrderSeven.Construction.orderSevenLine₁
      Line.Normalized.printedLine
    constructor
    · calc
        (6 : K) * 1 = 15 * 12 - 6 * 29 := by ring1
        _ = 15 * 12 := by rw [twentyNineZero]; ring1
    · constructor <;> ring1
  have printedFifteenNonNull : ¬ (Line.Normalized.printedLine (15 : K)).IsNull :=
    Line.Nullity.printedLine_nonNull_of_equivalent
      (Reflection.Iteration.reflectionLineAt initial 1) (Line.Normalized.printedLine 15) lineOne
      (Reflection.Iteration.reflectionLineAt_nonNull initial 1)
  have stepEleven :
      (Reflection.Line.reflectLine (Line.Normalized.printedLine (15 : K)) (Line.Normalized.printedLine 0)
        printedFifteenNonNull).Equivalent (Line.Normalized.printedLine 11) := by
    apply Reflection.Line.Normalized.reflect_printedLine
    calc
      ((15 : K) ^ 2 - 1) * 0 + 2 * 15 =
          11 * (2 * 15 * 0 - ((15 : K) ^ 2 - 1)) + 86 * 29 := by ring1
      _ = 11 * (2 * 15 * 0 - ((15 : K) ^ 2 - 1)) := by
        rw [twentyNineZero]
        ring1
  have lineTwo :
      (Reflection.Iteration.reflectionLineAt initial 2).Equivalent (Line.Normalized.printedLine 11) :=
    Reflection.Iteration.Line.next_equivalent initial 0 (Line.Normalized.printedLine 0)
      (Line.Normalized.printedLine 15)
      (Line.Normalized.printedLine 11) lineZero lineOne printedFifteenNonNull stepEleven
  have printedElevenNonNull : ¬ (Line.Normalized.printedLine (11 : K)).IsNull :=
    Line.Nullity.printedLine_nonNull_of_equivalent
      (Reflection.Iteration.reflectionLineAt initial 2) (Line.Normalized.printedLine 11) lineTwo
      (Reflection.Iteration.reflectionLineAt_nonNull initial 2)
  have stepTwenty :
      (Reflection.Line.reflectLine (Line.Normalized.printedLine (11 : K)) (Line.Normalized.printedLine 15)
        printedElevenNonNull).Equivalent (Line.Normalized.printedLine 20) := by
    apply Reflection.Line.Normalized.reflect_printedLine
    calc
      ((11 : K) ^ 2 - 1) * 15 + 2 * 11 =
          20 * (2 * 11 * 15 - ((11 : K) ^ 2 - 1)) - 82 * 29 := by ring1
      _ = 20 * (2 * 11 * 15 - ((11 : K) ^ 2 - 1)) := by
        rw [twentyNineZero]
        ring1
  have lineThree :
      (Reflection.Iteration.reflectionLineAt initial 3).Equivalent (Line.Normalized.printedLine 20) :=
    Reflection.Iteration.Line.next_equivalent initial 1 (Line.Normalized.printedLine 15)
      (Line.Normalized.printedLine 11)
      (Line.Normalized.printedLine 20) lineOne lineTwo printedElevenNonNull stepTwenty
  have printedTwentyNonNull : ¬ (Line.Normalized.printedLine (20 : K)).IsNull :=
    Line.Nullity.printedLine_nonNull_of_equivalent
      (Reflection.Iteration.reflectionLineAt initial 3) (Line.Normalized.printedLine 20) lineThree
      (Reflection.Iteration.reflectionLineAt_nonNull initial 3)
  have stepNine :
      (Reflection.Line.reflectLine (Line.Normalized.printedLine (20 : K)) (Line.Normalized.printedLine 11)
        printedTwentyNonNull).Equivalent (Line.Normalized.printedLine 9) := by
    apply Reflection.Line.Normalized.reflect_printedLine
    calc
      ((20 : K) ^ 2 - 1) * 11 + 2 * 20 =
          9 * (2 * 20 * 11 - ((20 : K) ^ 2 - 1)) + 140 * 29 := by ring1
      _ = 9 * (2 * 20 * 11 - ((20 : K) ^ 2 - 1)) := by
        rw [twentyNineZero]
        ring1
  have lineFour :
      (Reflection.Iteration.reflectionLineAt initial 4).Equivalent (Line.Normalized.printedLine 9) :=
    Reflection.Iteration.Line.next_equivalent initial 2 (Line.Normalized.printedLine 11)
      (Line.Normalized.printedLine 20)
      (Line.Normalized.printedLine 9) lineTwo lineThree printedTwentyNonNull stepNine
  have printedNineNonNull : ¬ (Line.Normalized.printedLine (9 : K)).IsNull :=
    Line.Nullity.printedLine_nonNull_of_equivalent
      (Reflection.Iteration.reflectionLineAt initial 4) (Line.Normalized.printedLine 9) lineFour
      (Reflection.Iteration.reflectionLineAt_nonNull initial 4)
  have stepEighteen :
      (Reflection.Line.reflectLine (Line.Normalized.printedLine (9 : K)) (Line.Normalized.printedLine 20)
        printedNineNonNull).Equivalent (Line.Normalized.printedLine 18) := by
    apply Reflection.Line.Normalized.reflect_printedLine
    calc
      ((9 : K) ^ 2 - 1) * 20 + 2 * 9 =
          18 * (2 * 9 * 20 - ((9 : K) ^ 2 - 1)) - 118 * 29 := by ring1
      _ = 18 * (2 * 9 * 20 - ((9 : K) ^ 2 - 1)) := by
        rw [twentyNineZero]
        ring1
  have lineFive :
      (Reflection.Iteration.reflectionLineAt initial 5).Equivalent (Line.Normalized.printedLine 18) :=
    Reflection.Iteration.Line.next_equivalent initial 3 (Line.Normalized.printedLine 20)
      (Line.Normalized.printedLine 9)
      (Line.Normalized.printedLine 18) lineThree lineFour printedNineNonNull stepEighteen
  have printedEighteenNonNull : ¬ (Line.Normalized.printedLine (18 : K)).IsNull :=
    Line.Nullity.printedLine_nonNull_of_equivalent
      (Reflection.Iteration.reflectionLineAt initial 5) (Line.Normalized.printedLine 18) lineFive
      (Reflection.Iteration.reflectionLineAt_nonNull initial 5)
  have stepFourteen :
      (Reflection.Line.reflectLine (Line.Normalized.printedLine (18 : K)) (Line.Normalized.printedLine 9)
        printedEighteenNonNull).Equivalent (Line.Normalized.printedLine 14) := by
    apply Reflection.Line.Normalized.reflect_printedLine
    calc
      ((18 : K) ^ 2 - 1) * 9 + 2 * 18 =
          14 * (2 * 18 * 9 - ((18 : K) ^ 2 - 1)) + 101 * 29 := by ring1
      _ = 14 * (2 * 18 * 9 - ((18 : K) ^ 2 - 1)) := by
        rw [twentyNineZero]
        ring1
  have lineSix :
      (Reflection.Iteration.reflectionLineAt initial 6).Equivalent (Line.Normalized.printedLine 14) :=
    Reflection.Iteration.Line.next_equivalent initial 4 (Line.Normalized.printedLine 9)
      (Line.Normalized.printedLine 18)
      (Line.Normalized.printedLine 14) lineFour lineFive printedEighteenNonNull stepFourteen
  exact ⟨lineZero, lineOne, lineTwo, lineThree, lineFour, lineFive, lineSix⟩

end ExampleFourteenNine

end ChapterFourteenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterFourteen

end
