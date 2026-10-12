module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Space.Box.Metric
public import Purelib.Geometry.Space.Pyramid.Regular.Seven.Roof
import Purelib.Polynomial.Recurrence.Spread.Roots.Seven.Cubic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, Chapter 22: three-dimensional problems

The source explicitly describes its three-dimensional treatment as informal.
Here every assertion is split into finite Cartesian dot-product algebra and
the scalar identities used in the printed solutions.  Algebraic roots and
distances are supplied as witnesses; no completed real-number construction is
introduced.
-/

namespace formalisations.DivineProportions.Chapters.Applications

namespace ThreeDimensionalProblems

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

open Purelib.Data.Rat in
/-- The displayed box diagonals, center quadrance and three diagonal spreads have their exact rational values. -/
theorem problem_8 :
    ((3 : Fraction.Rational) + 4 = 7) ∧
    ((7 : Fraction.Rational) + 5 = 12) ∧
    ((5 : Fraction.Rational) / 12 = 5 / 12) ∧
    ((12 : Fraction.Rational) / 4 = 3) ∧
    ((4 * 3 * (4 + 5) / 12 ^ 2 : Fraction.Rational) = 3 / 4) ∧
    ((4 * 4 * (5 + 3) / 12 ^ 2 : Fraction.Rational) = 8 / 9) ∧
    ((4 * 5 * (3 + 4) / 12 ^ 2 : Fraction.Rational) = 35 / 36) := by
  decide

open Purelib.Data.Rat in
open Purelib.Geometry.Space.Box in
/-- The retained box-center plane-line spread is exactly twenty over twenty-seven. -/
theorem exercise_22_2 :
    Metric.boxCenterPlaneLineSpread (3 : Fraction.Rational) 4 5 = 20 / 27 := by
  decide

section
open Purelib.Data.Rat
/-- The first retained pole-observation spread, three twenty-fifths. -/
def problem9FirstSpread : Fraction.Rational := 3 / 25
/-- The second retained pole-observation spread, nineteen hundredths. -/
def problem9SecondSpread : Fraction.Rational := 19 / 100
/-- The exact pole quadrance, 7350 over 11. -/
def problem9PoleQuadrance : Fraction.Rational := 7350 / 11
/-- The exact westward quadrance, 595350 over 209. -/
def problem9WestQuadrance : Fraction.Rational := 595350 / 209
/-- The exact resulting quadrance, 1619450 over 209. -/
def problem9AnswerQuadrance : Fraction.Rational := 1619450 / 209

end

/-- The five cleared integer equations determine the retained pole and final quadrances. -/
theorem problem_9_exact :
    (25 - 3 = 22) ∧
    (22 * 7350 = 3 * 4900 * 11) ∧
    (100 - 19 = 81) ∧
    (595350 = 81 * 7350) ∧
    (1619450 = 4900 * 209 + 595350) := by
  decide

open Purelib.Algebra.Field in
/-- The supplied radical and distance witnesses give the exact final quadrance.

The root squares to 276298, the cleared distance equation is 209 times distance equals 35 times root, and 209 is nonzero
in the explicit field. -/
theorem problem_9_distance_witness
    (root distance : K) (twoHundredNineNonzero : (209 : K) ≠ 0)
    (rootSquare : root ^ 2 = 276298)
    (distanceValue : 209 * distance = 35 * root) :
    209 * distance ^ 2 = 1619450 := by
  apply ExplicitField.eq_of_mul_eq_mul_right twoHundredNineNonzero
  calc
    (209 * distance ^ 2) * 209 = (209 * distance) ^ 2 := by ring1
    _ = (35 * root) ^ 2 := by rw [distanceValue]
    _ = 35 ^ 2 * root ^ 2 := by ring1
    _ = 35 ^ 2 * 276298 := by rw [rootSquare]
    _ = 1619450 * 209 := by ring1

/-- The exact final quadrance lies strictly between the squares of 88.02 and 88.03.

Positive-denominator integer comparisons certify the bracket without constructing a real square root. -/
theorem problem_9_decimal_bracket :
    4401 ^ 2 * 209 < 1619450 * 50 ^ 2 ∧
      1619450 * 100 ^ 2 < 8803 ^ 2 * 209 := by
  decide

/-- The displayed integer identities verify the two exact spread calculations. -/
theorem problem_10 :
    (10 + 10 = 20) ∧
    (20 = 4 * 5) ∧
    (5 + 18 = 23) ∧
    (4 * 5 * 18 = 360) ∧
    (23 ^ 2 = 529) ∧
    (10 * (4 * 23 - 10) = 4 * 205) ∧
    (20 * 23 * (4 * 205 - 20 * 23) * 1681 =
      1656 * 205 * (4 * 205)) := by
  decide

open Purelib.Polynomial.Recurrence.Spread.Roots.Seven in
/-- The seventh-spread cubic changes sign at the retained rational interval endpoints.

The finite evaluations certify opposite signs at 0.611259 and 0.611261 without asserting an intermediate-value theorem.
-/
theorem problem_13_central_root_certificate :
    Cubic.seventhSpreadFactorNumerator 611259 1000000 < 0 ∧
      0 < Cubic.seventhSpreadFactorNumerator 611261 1000000 := by
  decide

/-- Exact cross products certify the retained radial-quadrance and spread decimal intervals. -/
theorem problem_13_decimal_certificates :
    611260 * 200000 ^ 2 <
        (4 * 162349 * (200000 - 162349)) * 1000000 ∧
    (4 * 162349 * (200000 - 162349)) * 1000000 <
        611261 * 200000 ^ 2 ∧
    26559 * 61126 < 162349 * 10000 ∧
    162349 * 10000 < 26560 * 61126 ∧
    36559 * 61126 < 223475 * 10000 ∧
    223475 * 10000 < 36560 * 61126 ∧
    86323 * 223475 < 192912 * 100000 ∧
    192912 * 100000 < 86324 * 223475 ∧
    47223 * 223475 ^ 2 <
      (4 * 192912 * 30563) * 100000 ∧
    (4 * 192912 * 30563) * 100000 < 47224 * 223475 ^ 2 := by
  decide

open Purelib.Geometry.Space.Pyramid.Regular.Seven in
/-- The retained rational pagoda plane spread lies strictly between 0.2243 and 0.2245. -/
theorem exercise_22_4_decimal_certificate :
    let pair := Roof.pagodaPlaneSpreadIntegerPair 26559 10000 81175 100000
    2243 * pair.2 < 10000 * pair.1 ∧
      10000 * pair.1 < 2245 * pair.2 := by
  decide

end ThreeDimensionalProblems
end formalisations.DivineProportions.Chapters.Applications

end
