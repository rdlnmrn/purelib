module
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Plane.Sector.Spread.Cleared
public import Purelib.Geometry.Trigonometry.Spread.Cross.Cleared
public import Purelib.Geometry.Trigonometry.Spread.Triple.Cleared
public import Purelib.Geometry.Trigonometry.Spread.Triple.Ratio.Cleared.Int
public import Purelib.Geometry.Trigonometry.Spread.Triple.Two.Cleared
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, Chapter 25: resection and Hansen's problem

The large rational calculations are represented by common-denominator
integer certificates.  The general resection theorem is proved from the
denominator-free Four-point polynomial, so neither a root search nor a
completed coordinate field is used.
-/

namespace formalisations.DivineProportions.Chapters.Applications

namespace ResectionApplications

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

open Purelib.Geometry.Trigonometry.Spread.Cross in
/-- Exact cleared arithmetic certificates for both displayed resection candidates.

The simultaneous integer identities verify the candidate square equations, cross-spread equations and selected quadrance
ratios over the supplied explicit field. -/
theorem example_25_1_certificates :
    (33320 : K) * 925 * 169 = 6253 * 196 * 17 * 250 ∧
    (34425 : K) * 370 * 169 = 6253 * 81 * 17 * 250 ∧
    ((13456 : K) - 46216) ^ 2 = (2520 * 13) ^ 2 ∧
    ((78976 : K) - 46216) ^ 2 = (2520 * 13) ^ 2 ∧
    Cleared.clearedCrossSpread (6253 : K) 33320 13456 8 169 170 = 0 ∧
    Cleared.clearedCrossSpread (6253 : K) 34425 13456 13 169 425 = 0 ∧
    (169 : K) * 17 * 250 = 25 * 170 * 169 ∧
    (169 : K) * 17 * 250 = 10 * 425 * 169 ∧
    Cleared.clearedCrossSpread (6253 : K) 33320 78976 8 33124 52445 = 0 ∧
    Cleared.clearedCrossSpread (6253 : K) 34425 78976 13 474721 524450 = 0 ∧
    33124 * 17 * 250 * 617 = 9800 * 52445 * 169 ∧
    474721 * 17 * 250 * 617 = 14045 * 524450 * 169 := by
  unfold Cleared.clearedCrossSpread
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Plane.Sector.Spread in
open Purelib.Algebra in
attribute [local instance high] SubNegMonoid.toNeg in
/-- The selected point with coordinates four and five satisfies the three exact sector-spread readings. -/
theorem example_25_1_direct_reading_certificates :
    Cleared.MatchesSectorSpread
        (⟨4, 5⟩ : Purelib.Geometry.Plane.Point K) ⟨5, 2⟩ ⟨3, -1⟩ 81 370 ∧
      Cleared.MatchesSectorSpread
        (⟨4, 5⟩ : Purelib.Geometry.Plane.Point K) ⟨1, 1⟩ ⟨3, -1⟩ 196 925 ∧
      Cleared.MatchesSectorSpread
        (⟨4, 5⟩ : Purelib.Geometry.Plane.Point K) ⟨1, 1⟩ ⟨5, 2⟩ 169 250 := by
  letI : SubNegZeroMonoid K := Group.Negation.subNegZeroMonoid
  unfold Cleared.MatchesSectorSpread Cleared.sectorSpreadNumerator Quadrance.quadrance
  constructor
  · ring1
  constructor <;> ring1

open Purelib.Geometry.Trigonometry.Spread.Triple in
/-- The exact triangle-spread equations distinguish the selected lower-root sector pattern.

Common-denominator natural inequalities certify the two obtuse sectors for the lower root and rule out that pattern for
the upper root. -/
theorem exercise_25_1_triangle_rule_selection :
    Cleared.clearedSpreadTriple (6290 : K) 1682 4165 6253 = 0 ∧
      Cleared.clearedSpreadTriple (204425 : K) 13456 34425 81289 = 0 ∧
      Cleared.clearedSpreadTriple (1940465 : K) 1934912 816340 1225588 = 0 ∧
      Cleared.clearedSpreadTriple (252260450 : K)
        221843584 96699825 228340801 = 0 ∧
      (1682 + 4165 : Nat) ≤ 6253 ∧
      (13456 + 34425 : Nat) ≤ 81289 ∧
      ¬ (1934912 + 816340 : Nat) ≤ 1225588 ∧
      ¬ (221843584 + 96699825 : Nat) ≤ 228340801 := by
  unfold Cleared.clearedSpreadTriple
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  decide

open Purelib.Geometry.Trigonometry.Spread.Triple in
open Purelib.Geometry.Trigonometry.Spread.Triple.Two in
/-- The five displayed triangle-spread and two-spread-triples expressions vanish exactly. -/
theorem problem_25_spread_certificates :
    Cleared.clearedSpreadTriple (4250 : K) 3610 2873 3025 = 0 ∧
    Cleared.clearedSpreadTriple (6970 : K) 4410 2057 6929 = 0 ∧
    Cleared.clearedSpreadTriple (10250 : K) 6929 3025 10240 = 0 ∧
    Cleared.clearedTwoSpreadTriplesValue (34850 : K)
      34816 29602 24805 10285 121 697 = 0 ∧
    Cleared.clearedTwoSpreadTriplesValue (174250 : K)
      174080 110250 117793 173225 169 425 = 0 := by
  unfold Cleared.clearedSpreadTriple Cleared.clearedTwoSpreadTriplesValue
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- The displayed alternate-spreads ratio has the stated exact square witnesses. -/
theorem problem_25_ratio_certificates :
    (441 * 169 * 121 * 425 * 410 * 425 * 14801 : K) =
      11025 * (697 * 250 * 697) * (169 * 121 * 361) ∧
    11025 * 1 * 606841 = 441 * 14801 * 1025 ∧
    606841 = 779 ^ 2 ∧
    441 = 21 ^ 2 := by
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- The two cleared integer equations for a retained signed spread-ratio candidate.

The explicit numerator, denominator and sign inputs retain the selected algebraic branch without numerical root
approximation. -/
def spreadFromRatioCandidateCertificate
    (xNumerator xDenominator yNumerator yDenominator sign : Int) : Prop :=
  14801 * xNumerator * yDenominator =
      11025 * yNumerator * xDenominator ∧
    yNumerator *
        (11025 * 779 + 14801 * 779 + sign * 42 * 14801) * 1025 =
      1024 * yDenominator * 14801 * 779

/-- Both displayed rational candidate pairs satisfy the exact signed spread-ratio equations. -/
theorem problem_25_spread_candidates :
    spreadFromRatioCandidateCertificate 441 1066 361 650 1 ∧
      spreadFromRatioCandidateCertificate
        112896 256537 92416 156425 (-1) := by
  unfold spreadFromRatioCandidateCertificate
  decide

/-- The selected candidate satisfies the four required quadrance ratios and exact coordinate checks. -/
theorem problem_25_final_quadrances :
    (361 * 650 * 17 : Int) = 361 * 425 * 26 ∧
    (441 * 1066 * 17 : Int) = 441 * 697 * 26 ∧
    (121 * 170 * 41 : Int) = 121 * 410 * 17 ∧
    (169 * 170 * 25 : Int) = 169 * 250 * 17 ∧
    ((1 : Int) ^ 2 + 5 ^ 2 = 26) ∧
    ((5 : Int) ^ 2 + 4 ^ 2 = 41) ∧
    (((5 : Int) - 1) ^ 2 + (4 - 5) ^ 2 = 17) ∧
    ((4 : Int) ^ 2 + 1 ^ 2 = 17) ∧
    (((4 : Int) - 1) ^ 2 + (1 - 5) ^ 2 = 25) := by
  decide

/-! ## Exercise 25.3 -/

open Purelib.Geometry.Trigonometry.Spread.Triple in
/-- The three cleared triangle-spread equations for the retained measured and crossing spreads hold. -/
theorem exercise_25_3_triangle_spread_certificates :
    Cleared.clearedSpreadTriple (10730 : K) 2809 3712 9065 = 0 ∧
      Cleared.clearedSpreadTriple (4930 : K) 1568 1421 4165 = 0 ∧
      Cleared.clearedSpreadTriple (6290 : K) 1813 2176 5445 = 0 := by
  unfold Cleared.clearedSpreadTriple
  constructor
  · ring1
  constructor <;> ring1

open Purelib.Geometry.Trigonometry.Spread.Triple.Two in
/-- Both displayed two-spread-triples equations hold at their retained common denominator. -/
theorem exercise_25_3_two_spread_certificates :
    Cleared.clearedTwoSpreadTriplesValue (182410 : K)
        157905 47753 154105 52577 2401 2465 = 0 ∧
      Cleared.clearedTwoSpreadTriplesValue (182410 : K)
        157905 58016 63104 154105 10201 10730 = 0 := by
  unfold Cleared.clearedTwoSpreadTriplesValue
  constructor <;> ring1

/-- The retained alternate-spreads ratio and both explicit squared-root witnesses agree exactly. -/
theorem exercise_25_3_ratio_certificates :
    ((784 * 64 * 2401) * (10730 * 170 * 10730) * 487128353 : K) =
        727752704 * (2465 * 185 * 2465) * (10201 * 49 * 2809) ∧
      (727752704 * 169 * 8281182001 : K) =
        1662029824 * 487128353 * 1258 ∧
      (1662029824 : K) = 40768 ^ 2 ∧
      (8281182001 : K) = 91001 ^ 2 := by
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

open Purelib.Geometry.Trigonometry.Spread.Triple.Ratio.Cleared in
/-- The displayed rational answer satisfies the positive signed candidate equation and lies strictly between zero and
one.

Exact integer inequalities certify both proper spreads alongside the cleared algebraic relation. -/
theorem exercise_25_3_answer_certificates :
    Int.clearedSpreadFromRatioCandidate
        727752704 487128353 1089 1258 40768 91001
        9834496 25778545 28654609 112212490 1 ∧
      0 < 9834496 ∧ 9834496 < 25778545 ∧
      0 < 28654609 ∧ 28654609 < 112212490 := by
  unfold Int.clearedSpreadFromRatioCandidate
  decide

end ResectionApplications
end formalisations.DivineProportions.Chapters.Applications

end
