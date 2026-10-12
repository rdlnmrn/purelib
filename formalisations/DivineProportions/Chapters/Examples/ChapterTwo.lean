module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Quadratic.CommonRoot.Centered
public import Purelib.Polynomial.Quadratic.CommonRoot.General
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib

section
/-!
# Divine Proportions, §2.2–2.3: proportions and identities

The source's elementary identities are stated directly over constructive
commutative rings.  Its three-index antisymmetrization is an explicit six-term
operation, so none of these declarations uses permutations, finite sums, or a
global enumeration.
-/

@[expose] public section

namespace formalisations.DivineProportions.Chapters.Examples.ChapterTwo

variable {K : Type*}

/-- Example 2.6: the rational proportion `3:7=(12/7):4`, recorded through
its quotient-free cross-product equation. -/
theorem example_2_6 [ExplicitField K]
    (sevenNonzero : (7 : K) ≠ 0) :
    (3 : K) * 4 - (12 / 7) * 7 = 0 := by
  rw [ExplicitField.div_mul_cancel 12 sevenNonzero]
  ring1

end formalisations.DivineProportions.Chapters.Examples.ChapterTwo

end

end

section
public section

/-!
# Divine Proportions, §2.6: pairs of quadratic equations

This file begins the numbered theorem sequence in *Divine Proportions*.  The
source's theorem has a genuine degenerate-case omission: when the two centres
are equal, its displayed polynomial condition merely says that the two
equations are identical; it does not prove that the common equation has a
solution in the field.  The exact arbitrary-field result is therefore split
into the distinct-centre theorem proved by the source's calculation and a
separate same-centre characterization.

Everything is parameterized by the project's explicit, choice-free field-law
interface.  The only characteristic assumption used below is the displayed
witness that `2` is nonzero.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterTwo

variable {K : Type*} [ExplicitField K]

/-- Example 2.19: `7` is the displayed common solution of the two equations.
The calculation is valid in every commutative ring. -/
theorem example_2_19 (K : Type*) [CommRing K] :
    ((7 : K) - 4) ^ 2 = 9 ∧ ((7 : K) - 6) ^ 2 = 1 := by
  constructor <;> ring1

end formalisations.DivineProportions.Chapters.Examples.ChapterTwo

end

section
@[expose] public section

/-!
# Divine Proportions, Exercises 2.8–2.9

Both printed exercises omit genuine degenerate cases.  The determinant formula
in Exercise 2.8 is sufficient only when its displayed root denominator is
nonzero.  Exercise 2.9 uses `±2q` where the valid root-free condition is
`(p₁-p₂)²=4q`, and coincident equations still require `q` to be a square.
The corrected constructive statements and explicit rational counterexamples
are given below.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterTwo

variable {K : Type*} [ExplicitField K]

/-- Counterexample to the degenerate wording of Exercise 2.8: over the
constructive rationals, the identical equations `x²+1=0` satisfy the printed
determinant identity but have no common root. -/
theorem exercise_2_8_printed_counterexample :
    let R := Fraction.Rational
    Polynomial.Quadratic.CommonRoot.General.generalQuadraticCompatibilityIdentity
        (1 : R) 0 1 1 0 1 ∧
      ¬ Polynomial.Quadratic.CommonRoot.General.GeneralQuadraticsCompatible (1 : R) 0 1 1 0 1 := by
  dsimp only
  constructor
  · unfold Polynomial.Quadratic.CommonRoot.General.generalQuadraticCompatibilityIdentity
    ring1
  · rintro ⟨root, firstEquation, _⟩
    have squareEqualsNegativeOne : root ^ 2 = (-1 :
        Fraction.Rational) := by
      calc
        root ^ 2 = (1 * root ^ 2 + 0 * root + 1) - 1 := by ring1
        _ = -1 := by rw [firstEquation]; ring1
    have squareNonnegative :=
      Fraction.Order.Arithmetic.sq_nonneg_direct root
    rw [squareEqualsNegativeOne] at squareNonnegative
    exact (by decide : ¬ ((0 : Fraction.Rational) ≤ -1))
      squareNonnegative

/-- Concrete refutation of Exercise 2.9 as printed: the compatible rational
equations `(x-0)²=4` and `(x-4)²=4` have center difference `-4`, not `±8`. -/
theorem exercise_2_9_printed_counterexample :
    let R := Fraction.Rational
    Polynomial.Quadratic.CommonRoot.Centered.QuadraticsCompatible (0 : R) 4 4 4 ∧
      ¬ ((0 : R) = 4 ∨ 0 - 4 = 2 * 4 ∨ 0 - 4 = -(2 * 4)) := by
  dsimp only
  constructor
  · exact ⟨2, by ring1, by ring1⟩
  · decide

end formalisations.DivineProportions.Chapters.Examples.ChapterTwo

end

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 2 finite-field examples

The source's characteristic-seven arithmetic and characteristic-nineteen
polynomial data are recorded by exact finite calculations.  The `S₅` table is
a literal list evaluation, not a claim that a list enumerates an ambient
carrier.  The characteristic-nineteen factorization is proved as a direct
polynomial identity; no carrier enumeration or root search is used.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterTwo

namespace ChapterTwoExamples

variable {K : Type*} [ExplicitField K] [Nontrivial K]

/-- Example 2.1: the three displayed calculations in characteristic seven,
including the fraction sum with both denominator certificates explicit. -/
theorem example_2_1 (sevenZero : (7 : K) = 0) :
    (3 : K) + 5 = 1 ∧
      (3 : K) * 6 = 4 ∧
      (34 : K) / 53 + 19 / 17 = 2 := by
  have fiftyThreeNonzero : (53 : K) ≠ 0 := by
    intro fiftyThreeZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 2 * 53 - 15 * 7 := by ring1
      _ = 0 := by rw [fiftyThreeZero, sevenZero]; ring1
  have seventeenNonzero : (17 : K) ≠ 0 := by
    intro seventeenZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 5 * 7 - 2 * 17 := by ring1
      _ = 0 := by rw [seventeenZero, sevenZero]; ring1
  have fiftyThreeCancel : (53 : K) * (53 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 53 fiftyThreeNonzero
  have seventeenCancel : (17 : K) * (17 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 17 seventeenNonzero
  have numeratorEquation :
      (34 : K) * 17 + 19 * 53 = 2 * (53 * 17) := by
    calc
      (34 : K) * 17 + 19 * 53 =
          2 * (53 * 17) - 31 * 7 := by ring1
      _ = 2 * (53 * 17) := by rw [sevenZero]; ring1
  constructor
  · calc
      (3 : K) + 5 = 1 + 7 := by ring1
      _ = 1 := by rw [sevenZero]; ring1
  constructor
  · calc
      (3 : K) * 6 = 4 + 2 * 7 := by ring1
      _ = 4 := by rw [sevenZero]; ring1
  · simp only [ExplicitField.div_eq_mul_inv]
    calc
      (34 : K) * (53 : K)⁻¹ + 19 * (17 : K)⁻¹ =
          34 * (53 : K)⁻¹ * (17 * (17 : K)⁻¹) +
            19 * (17 : K)⁻¹ * (53 * (53 : K)⁻¹) := by
              rw [fiftyThreeCancel, seventeenCancel]
              ring1
      _ = (34 * 17 + 19 * 53) *
          ((53 : K)⁻¹ * (17 : K)⁻¹) := by ring1
      _ = 2 * (53 * 17) * ((53 : K)⁻¹ * (17 : K)⁻¹) := by
        rw [numeratorEquation]
      _ = 2 * (53 * (53 : K)⁻¹) * (17 * (17 : K)⁻¹) := by ring1
      _ = 2 := by rw [fiftyThreeCancel, seventeenCancel]; ring1
namespace ExampleTwoSeventeen

/-- Residue labels used in the literal value table from Example 2.17. -/
abbrev Element := Fin 19

/-- Nineteen is nonzero, providing the modulus certificate for the displayed residue labels. -/
instance instNeZeroNineteen : NeZero 19 := ⟨by decide⟩

/-- The nineteen input labels printed in the source table. -/
def inputs : List Element :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- The nineteen output labels printed below those inputs. -/
def outputs : List Element :=
  [0, 1, 10, 13, 1, 5, 17, 6, 10, 0, 10, 1, 10, 14, 3, 15, 0, 7, 10]

/-- The same literal quintic expression, specialized to the kernel's modular
operations on the nineteen displayed residue labels. -/
def tableExpression (value : Element) : Element :=
  value * (16 * value ^ 2 - 20 * value + 5) ^ 2

/-- Example 2.17: direct kernel evaluation of the source's literal `S₅`
table.  This theorem checks exactly the displayed labels and makes no claim
that `inputs` is a global enumeration of a carrier. -/
theorem example_2_17 :
    List.map tableExpression inputs = outputs := by
  decide

end ExampleTwoSeventeen
end ChapterTwoExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterTwo

end
