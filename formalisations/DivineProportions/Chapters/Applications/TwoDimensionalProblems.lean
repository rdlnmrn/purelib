module
import Purelib.Algebra.Group.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Plane.Point.Quadrance.FourPoint
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
public import Purelib.Geometry.Trigonometry.Spread.Triple.Cleared
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Tactic.Ring
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Algebra

section
@[expose] public section

/-!
# Divine Proportions, Chapter 21: two-dimensional problems

The applications are separated into their finite metric identities and the
geometric incidence arguments that supply those identities.  Denominators are
always accompanied by explicit nonzero certificates.
-/

namespace formalisations.DivineProportions.Chapters.Applications

namespace TwoDimensionalProblems

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## Problem 5: overlapping triangles -/

/-- The selected third-spread numerator as a linear expression in the supplied radical. -/
def problem5ThirdSpreadNumerator (root : K) : K :=
  487568 + 31584 * root

/-- The retained numerator of the A-to-E quadrance over denominator 525625. -/
def problem5QuadranceAENumerator (root : K) : K :=
  34556382 - 2238516 * root

/-- The retained numerator of the B-to-E quadrance over denominator 525625. -/
def problem5QuadranceBENumerator (root : K) : K :=
  56649307 - 3669666 * root

/-- The retained numerator of the C-to-E quadrance over denominator 525625. -/
def problem5QuadranceCENumerator (root : K) : K :=
  111662307 - 7758666 * root

/-- The retained numerator of the D-to-E quadrance over denominator 525625. -/
def problem5QuadranceDENumerator (root : K) : K :=
  18789082 + 1476384 * root

/-- The selected third spread with denominator 950625 and the supplied radical witness. -/
def problem5ThirdSpread (root : K) : K :=
  problem5ThirdSpreadNumerator root / 950625

/-- The retained exact A-to-E quadrance with denominator 525625. -/
def problem5QuadranceAE (root : K) : K :=
  problem5QuadranceAENumerator root / 525625

/-- The retained exact B-to-E quadrance with denominator 525625. -/
def problem5QuadranceBE (root : K) : K :=
  problem5QuadranceBENumerator root / 525625

/-- The retained exact C-to-E quadrance with denominator 525625. -/
def problem5QuadranceCE (root : K) : K :=
  problem5QuadranceCENumerator root / 525625

/-- The retained exact D-to-E quadrance with denominator 525625. -/
def problem5QuadranceDE (root : K) : K :=
  problem5QuadranceDENumerator root / 525625

open Purelib.Algebra.Field in
/-- Multiplication by the two nonzero retained denominators recovers all five coefficient numerators. -/
theorem problem_5_value_definitions
    (root : K) (spreadDenominatorNonzero : (950625 : K) ≠ 0)
    (quadranceDenominatorNonzero : (525625 : K) ≠ 0) :
    problem5ThirdSpread root * 950625 =
        problem5ThirdSpreadNumerator root ∧
      problem5QuadranceAE root * 525625 =
        problem5QuadranceAENumerator root ∧
      problem5QuadranceBE root * 525625 =
        problem5QuadranceBENumerator root ∧
      problem5QuadranceCE root * 525625 =
        problem5QuadranceCENumerator root ∧
      problem5QuadranceDE root * 525625 =
        problem5QuadranceDENumerator root := by
  unfold problem5ThirdSpread problem5QuadranceAE problem5QuadranceBE
    problem5QuadranceCE problem5QuadranceDE
  exact ⟨ExplicitField.div_mul_cancel _ spreadDenominatorNonzero,
    ExplicitField.div_mul_cancel _ quadranceDenominatorNonzero,
    ExplicitField.div_mul_cancel _ quadranceDenominatorNonzero,
    ExplicitField.div_mul_cancel _ quadranceDenominatorNonzero,
    ExplicitField.div_mul_cancel _ quadranceDenominatorNonzero⟩

/-- The two initial spread values satisfy their exact denominator-cleared cross-law equations. -/
theorem problem_5_initial_spread_certificates :
    (176 : K) * (4 * 25 * 81) =
        225 * (4 * 25 * 81 - (81 + 25 - 64) ^ 2) ∧
      (2016 : K) * (4 * 169 * 25) =
        4225 * (4 * 169 * 25 - (169 + 25 - 100) ^ 2) := by
  constructor <;> ring1

/-- The retained first two spreads have sum strictly greater than one. -/
theorem problem_5_spread_sum_above_one :
    950625 < 176 * 4225 + 2016 * 225 := by decide

/-- A root squaring to 154 makes the selected third-spread numerator satisfy its exact quadratic. -/
theorem problem_5_quadratic_cleared
    (root : K) (rootSquare : root ^ 2 = 154) :
    problem5ThirdSpreadNumerator root ^ 2 -
        975136 * problem5ThirdSpreadNumerator root +
        215296 * 390625 = 0 := by
  calc
    problem5ThirdSpreadNumerator root ^ 2 -
          975136 * problem5ThirdSpreadNumerator root +
          215296 * 390625 =
        997549056 * (root ^ 2 - 154) := by
          unfold problem5ThirdSpreadNumerator
          ring1
    _ = 0 := by rw [rootSquare]; ring1

/-- The three retained spread numerators satisfy the common-denominator triple-spread relation.

The supplied radical squares to 154, and all three spreads use denominator 950625. -/
theorem problem_5_triple_spread_cleared
    (root : K) (rootSquare : root ^ 2 = 154) :
    let firstNumerator : K := 176 * 4225
    let secondNumerator : K := 2016 * 225
    let thirdNumerator := problem5ThirdSpreadNumerator root
    950625 *
          ((firstNumerator + secondNumerator + thirdNumerator) ^ 2 -
            2 * (firstNumerator ^ 2 + secondNumerator ^ 2 +
              thirdNumerator ^ 2)) -
        4 * firstNumerator * secondNumerator * thirdNumerator = 0 := by
  dsimp only
  calc
    950625 *
          (((176 * 4225 : K) + 2016 * 225 +
              problem5ThirdSpreadNumerator root) ^ 2 -
            2 * ((176 * 4225 : K) ^ 2 + (2016 * 225 : K) ^ 2 +
              problem5ThirdSpreadNumerator root ^ 2)) -
        4 * (176 * 4225 : K) * (2016 * 225) *
          problem5ThirdSpreadNumerator root =
        -948295071360000 * (root ^ 2 - 154) := by
          unfold problem5ThirdSpreadNumerator
          ring1
    _ = 0 := by rw [rootSquare]; ring1

/-- The retained spread and quadrance numerators satisfy all three cleared spread-law equalities. -/
theorem problem_5_spread_law_cleared
    (root : K) (rootSquare : root ^ 2 = 154) :
    let firstNumerator : K := 176 * 4225
    let secondNumerator : K := 2016 * 225
    let thirdNumerator := problem5ThirdSpreadNumerator root
    let qAENumerator := problem5QuadranceAENumerator root
    let qBENumerator := problem5QuadranceBENumerator root
    firstNumerator * qAENumerator = secondNumerator * qBENumerator ∧
      25 * firstNumerator * 525625 = thirdNumerator * qBENumerator ∧
      25 * secondNumerator * 525625 = thirdNumerator * qAENumerator := by
  dsimp only
  constructor
  · unfold problem5QuadranceAENumerator problem5QuadranceBENumerator
    ring1
  constructor
  · have differenceZero :
        (25 : K) * (176 * 4225) * 525625 -
            problem5ThirdSpreadNumerator root *
              problem5QuadranceBENumerator root = 0 := by
      calc
        (25 : K) * (176 * 4225) * 525625 -
              problem5ThirdSpreadNumerator root *
                problem5QuadranceBENumerator root =
            115902730944 * (root ^ 2 - 154) := by
              unfold problem5ThirdSpreadNumerator
                problem5QuadranceBENumerator
              ring1
        _ = 0 := by rw [rootSquare]; ring1
    exact Group.eq_of_sub_eq_zero differenceZero
  · have differenceZero :
        (25 : K) * (2016 * 225) * 525625 -
            problem5ThirdSpreadNumerator root *
              problem5QuadranceAENumerator root = 0 := by
      calc
        (25 : K) * (2016 * 225) * 525625 -
              problem5ThirdSpreadNumerator root *
                problem5QuadranceAENumerator root =
            70701289344 * (root ^ 2 - 154) := by
              unfold problem5ThirdSpreadNumerator
                problem5QuadranceAENumerator
              ring1
        _ = 0 := by rw [rootSquare]; ring1
    exact Group.eq_of_sub_eq_zero differenceZero

open Purelib.Geometry.Trigonometry.QuadTriple in
/-- Both retained final quadrance triples satisfy the collinear quad-triple relation.

The shared denominator 525625 scales each triple, and the supplied radical-square equation determines the exact
identities. -/
theorem problem_5_collinear_quadrances_cleared
    (root : K) (rootSquare : root ^ 2 = 154) :
    Purelib.Geometry.Trigonometry.QuadTriple (81 * 525625)
        (problem5QuadranceAENumerator root)
        (problem5QuadranceCENumerator root) ∧
      Purelib.Geometry.Trigonometry.QuadTriple (169 * 525625)
        (problem5QuadranceBENumerator root)
        (problem5QuadranceDENumerator root) := by
  constructor
  · unfold Purelib.Geometry.Trigonometry.QuadTriple Basic.archimedesFunction
    calc
      ((81 * 525625 : K) + problem5QuadranceAENumerator root +
            problem5QuadranceCENumerator root) ^ 2 -
          2 * ((81 * 525625 : K) ^ 2 +
            problem5QuadranceAENumerator root ^ 2 +
            problem5QuadranceCENumerator root ^ 2) =
          -30472056022500 * (root ^ 2 - 154) := by
            unfold problem5QuadranceAENumerator
              problem5QuadranceCENumerator
            ring1
      _ = 0 := by rw [rootSquare]; ring1
  · unfold Purelib.Geometry.Trigonometry.QuadTriple Basic.archimedesFunction
    calc
      ((169 * 525625 : K) + problem5QuadranceBENumerator root +
            problem5QuadranceDENumerator root) ^ 2 -
          2 * ((169 * 525625 : K) ^ 2 +
            problem5QuadranceBENumerator root ^ 2 +
            problem5QuadranceDENumerator root ^ 2) =
          -26481830602500 * (root ^ 2 - 154) := by
            unfold problem5QuadranceBENumerator
              problem5QuadranceDENumerator
            ring1
      _ = 0 := by rw [rootSquare]; ring1

/-! ## Problem 7: the quadrilateral problem -/

open Purelib.Geometry.Quadrilaterals.Basic in
/-- The retained six-quadrance Euler expression factors as the displayed centered quadratic. -/
theorem problem_7_euler_reduction (unknown : K) :
    Quadrilateral.eulerFunction 100 65 49 61 26 unknown =
      -98 * ((unknown - 114) ^ 2 - 80 ^ 2) := by
  unfold Quadrilateral.eulerFunction Quadrilateral.determinantThree
  ring1

open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Quadrilaterals.Basic in
/-- Four points with the six specified quadrances satisfy the retained Euler relation. -/
theorem problem_7_four_point_relation
    (a₁ a₂ a₃ a₄ : Purelib.Geometry.Plane.Point K) (unknown : K)
    (q₂₄ : Quadrance.quadrance a₄ a₂ = 100)
    (q₁₂ : Quadrance.quadrance a₁ a₂ = 65)
    (q₁₄ : Quadrance.quadrance a₁ a₄ = 49)
    (q₁₃ : Quadrance.quadrance a₁ a₃ = 61)
    (q₃₄ : Quadrance.quadrance a₄ a₃ = 26)
    (q₂₃ : Quadrance.quadrance a₂ a₃ = unknown) :
    Quadrilateral.eulerFunction 100 65 49 61 26 unknown = 0 := by
  have relation := Quadrilateral.four_point_relation a₁ a₄ a₂ a₃
  rw [q₂₄, q₁₂, q₁₄, q₁₃, q₃₄, q₂₃] at relation
  exact relation

open Purelib.Algebra.Field in
open Purelib.Geometry.Quadrilaterals.Basic in
/-- The retained Euler equation has only the two candidate values 34 and 194.

The explicit field has decidable equality and the scalar 98 is nonzero, allowing constructive factor cancellation. -/
theorem problem_7_euler_roots [DecidableEq K]
    (unknown : K) (ninetyEightNonzero : (98 : K) ≠ 0)
    (relation :
      Quadrilateral.eulerFunction 100 65 49 61 26 unknown = 0) :
    unknown = 34 ∨ unknown = 194 := by
  have negativeNinetyEightNonzero : (-98 : K) ≠ 0 := by
    intro negativeZero
    apply ninetyEightNonzero
    calc
      (98 : K) = -(-98) := by ring1
      _ = 0 := by rw [negativeZero]; ring1
  have scaledFactorZero :
      (-98 : K) * ((unknown - 34) * (unknown - 194)) = 0 := by
    calc
      (-98 : K) * ((unknown - 34) * (unknown - 194)) =
          Quadrilateral.eulerFunction 100 65 49 61 26 unknown := by
            rw [problem_7_euler_reduction]
            ring1
      _ = 0 := relation
  have factorZero : (unknown - 34) * (unknown - 194) = 0 := by
    by_cases zero : (unknown - 34) * (unknown - 194) = 0
    · exact zero
    · exact False.elim
        ((ExplicitField.mul_ne_zero negativeNinetyEightNonzero zero)
          scaledFactorZero)
  by_cases firstZero : unknown - 34 = 0
  · exact Or.inl (Group.eq_of_sub_eq_zero firstZero)
  · by_cases secondZero : unknown - 194 = 0
    · exact Or.inr (Group.eq_of_sub_eq_zero secondZero)
    · exact False.elim
        ((ExplicitField.mul_ne_zero firstZero secondZero) factorZero)

open Purelib.Data.Rat in
open Purelib.Data.Rat.Fraction.Cast in
open Purelib.Geometry.Quadrilaterals.Basic in
/-- The retained rational Euler equation and strict bound below 194 select the value 34. -/
theorem problem_7_solution_one
    (unknown : Fraction.Rational)
    (relation :
      Quadrilateral.eulerFunction 100 65 49 61 26 unknown = 0)
    (belowAlternate : unknown < 194) : unknown = 34 := by
  have ninetyEightPositive :
      (0 : Fraction.Rational) < 98 :=
    Order.natCast_pos_direct (by decide)
  have ninetyEightNonzero : (98 : Fraction.Rational) ≠ 0 := by
    intro zero
    rw [zero] at ninetyEightPositive
    exact (lt_irrefl 0 ninetyEightPositive).elim
  rcases problem_7_euler_roots unknown
      ninetyEightNonzero relation with
    correct | alternate
  · exact correct
  · rw [← alternate] at belowAlternate
    exfalso
    exact lt_irrefl unknown belowAlternate

section
open Purelib.Data.Rat
/-- The selected auxiliary spread, 1521 over 1525. -/
def problem7AuxiliarySpread : Fraction.Rational := 1521 / 1525

/-- The selected sector spread, 1849 over 3965. -/
def problem7SectorSpread : Fraction.Rational := 1849 / 3965

end

open Purelib.Geometry.Trigonometry.Spread.Triple in
/-- The three retained cleared spread triples and auxiliary square equation hold exactly. -/
theorem problem_7_spread_certificates :
    Cleared.clearedSpreadTriple (1525 : K) 625 976 1521 = 0 ∧
      Cleared.clearedSpreadTriple (99125 : K) 46225 98865 47824 = 0 ∧
      Cleared.clearedSpreadTriple (3965 : K) 1849 1625 3904 = 0 ∧
      ((1521 : K) - 801) ^ 2 = 720 ^ 2 := by
  unfold Cleared.clearedSpreadTriple
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- The retained integer comparisons select the auxiliary spread and classify the sector as acute. -/
theorem problem_7_spread_comparisons :
    1525 < 625 + 976 ∧ 1849 ≤ 1625 + 3904 := by decide

/-- The cleared two-spread-triples quotient has the retained value 1849 over 3965. -/
theorem problem_7_two_spread_triples_value :
    let denominator : K := 99125
    let first : K := 98865
    let second : K := 47824
    let third : K := 40625
    let fourth : K := 97600
    3965 * ((first - second) ^ 2 - (third - fourth) ^ 2) =
      1849 * 2 *
        (denominator * (first + second - third - fourth) -
          2 * first * second + 2 * third * fourth) := by
  dsimp only
  ring1

/-- The retained upper bound 126 is strictly below both rejected candidates 194 and 218. -/
theorem problem_7_candidate_bound_certificates :
    (126 : Nat) < 194 ∧ (126 : Nat) < 218 := by decide

open Purelib.Geometry.Quadrilaterals.Basic in
/-- The selected value 34 satisfies both independent quadrance equations. -/
theorem problem_7_selected_value_certificates :
    Quadrilateral.eulerFunction (100 : K) 65 49 61 26 34 = 0 ∧
      ((34 : K) - 126) ^ 2 = 92 ^ 2 := by
  constructor
  · rw [problem_7_euler_reduction]
    ring1
  · ring1

open Purelib.Algebra.Field in
open Purelib.Data.Rat in
/-- The retained cross-law square equation and strict bound below 218 select the value 34. -/
theorem problem_7_solution_two
    (unknown : Fraction.Rational)
    (crossLaw : (unknown - 126) ^ 2 = 92 ^ 2)
    (belowAlternate : unknown < 218) : unknown = 34 := by
  have factorZero :
      (unknown - 34) * (unknown - 218) = 0 := by
    calc
      (unknown - 34) * (unknown - 218) =
          (unknown - 126) ^ 2 - 92 ^ 2 := by ring1
      _ = 0 := by rw [crossLaw]; ring1
  by_cases firstZero : unknown - 34 = 0
  · exact Group.eq_of_sub_eq_zero firstZero
  · by_cases secondZero : unknown - 218 = 0
    · have alternate : unknown = 218 := Group.eq_of_sub_eq_zero secondZero
      rw [← alternate] at belowAlternate
      exfalso
      exact lt_irrefl unknown belowAlternate
    · exact False.elim
        ((ExplicitField.mul_ne_zero firstZero secondZero) factorZero)

end TwoDimensionalProblems
end formalisations.DivineProportions.Chapters.Applications

end
