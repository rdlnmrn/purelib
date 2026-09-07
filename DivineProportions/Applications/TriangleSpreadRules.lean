import DivineProportions.Centers.AffineCircumcenter
import DivineProportions.Trigonometry.TripleSpread
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

namespace DivineProportions
namespace TriangleSpreadRules

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- The squared height ratio used to mark a spread ruler. -/
def spreadRulerRatio (spread : Rational) : Rational :=
  spread / (1 - spread)

/-- Complementary spread marks have reciprocal squared height ratios away
from the two endpoints. -/
theorem spreadRulerRatio_complementary
    (spread : Rational) (spreadNonzero : spread ≠ 0)
    (complementNonzero : 1 - spread ≠ 0) :
    spreadRulerRatio spread * spreadRulerRatio (1 - spread) = 1 := by
  have spreadCancel : spread * spread⁻¹ = (1 : Rational) :=
    RFAP.ExplicitField.mul_inv_cancel spread spreadNonzero
  have complementCancel :
      (1 - spread) * (1 - spread)⁻¹ = (1 : Rational) :=
    RFAP.ExplicitField.mul_inv_cancel (1 - spread) complementNonzero
  unfold spreadRulerRatio
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [show 1 - (1 - spread) = spread by ring1]
  calc
    spread * (1 - spread)⁻¹ * ((1 - spread) * spread⁻¹) =
        (spread * (1 - spread)⁻¹) *
          (spread⁻¹ * (1 - spread)) := by
            rw [mul_comm (1 - spread) spread⁻¹]
    _ = (spread * spread⁻¹) *
        ((1 - spread)⁻¹ * (1 - spread)) :=
      RFAP.ConstructiveFraction.mul_pair_swap _ _ _ _
    _ = (spread * spread⁻¹) *
        ((1 - spread) * (1 - spread)⁻¹) := by
          rw [mul_comm (1 - spread)⁻¹ (1 - spread)]
    _ = 1 := by rw [spreadCancel, complementCancel, one_mul]

/-- Exercise 20.1: every spread-ruler mark in `[0,1]` is represented either
by itself or by its complementary mark in `[0,1/2]`. -/
theorem exercise_20_1 (spread : Rational) :
    spread ≤ (1 : Rational) / 2 ∨
      1 - spread ≤ (1 : Rational) / 2 := by
  by_cases lowerHalf : spread ≤ (1 : Rational) / 2
  · exact Or.inl lowerHalf
  · right
    have halfBelow : (1 : Rational) / 2 < spread :=
      RFAP.ConstructiveFraction.lt_of_not_ge_direct lowerHalf
    have halfAtMost : (1 : Rational) / 2 ≤ spread :=
      RFAP.ConstructiveFraction.le_of_lt_direct halfBelow
    have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct halfAtMost
    calc
      1 - spread = -spread + 1 := by ring1
      _ ≤ -((1 : Rational) / 2) + 1 :=
        RFAP.ConstructiveFraction.add_le_add_right_direct reversed 1
      _ = (1 : Rational) / 2 := by decide

/-- Replace a ray's displayed second point by a positive affine point on the
same ray. -/
def rayRepresentative (base point : Point Rational) (scale : Rational) :
    Point Rational :=
  affineCombination (1 - scale) base scale point

/-- The scalar whose sign defines the book's acute/obtuse sector type. -/
def sectorTypeScalar
    (base first second : Point Rational) : Rational :=
  quadrance base first + quadrance base second - quadrance first second

/-- Changing the displayed point on either ray by positive scaling multiplies
the type scalar by the product of those scales. -/
theorem sectorTypeScalar_rayRepresentative
    (base first second : Point Rational) (firstScale secondScale : Rational) :
    sectorTypeScalar base
        (rayRepresentative base first firstScale)
        (rayRepresentative base second secondScale) =
      firstScale * secondScale * sectorTypeScalar base first second := by
  unfold sectorTypeScalar rayRepresentative quadrance affineCombination
  ring1

private theorem nonnegative_mul_iff_of_positive
    (factor value : Rational) (factorPositive : 0 < factor) :
    0 ≤ factor * value ↔ 0 ≤ value := by
  constructor
  · intro productNonnegative
    by_cases valueNonnegative : 0 ≤ value
    · exact valueNonnegative
    · have valueNegative : value < 0 :=
        RFAP.ConstructiveFraction.lt_of_not_ge_direct valueNonnegative
      have productNegative :=
        RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
          factorPositive valueNegative
      exact ((not_lt_of_ge productNonnegative) productNegative).elim
  · intro valueNonnegative
    exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.le_of_lt_direct factorPositive)
      valueNonnegative

private theorem nonpositive_mul_iff_of_positive
    (factor value : Rational) (factorPositive : 0 < factor) :
    factor * value ≤ 0 ↔ value ≤ 0 := by
  constructor
  · intro productNonpositive
    by_cases valueNonpositive : value ≤ 0
    · exact valueNonpositive
    · have valuePositive : 0 < value :=
        RFAP.ConstructiveFraction.lt_of_not_ge_direct valueNonpositive
      have productPositive :=
        RFAP.ConstructiveFraction.mul_pos_direct factorPositive valuePositive
      exact ((not_lt_of_ge productNonpositive) productPositive).elim
  · intro valueNonpositive
    have negativeValueNonnegative : 0 ≤ -value := by
      have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct
        valueNonpositive
      simpa only [neg_zero] using reversed
    have negativeProductNonnegative : 0 ≤ factor * (-value) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.le_of_lt_direct factorPositive)
        negativeValueNonnegative
    have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct
      negativeProductNonnegative
    calc
      factor * value = -(factor * (-value)) := by ring1
      _ ≤ 0 := by simpa only [neg_zero] using reversed

/-- Exercise 20.2: the acute and obtuse tests do not depend on which positive
representative point is chosen on either bounding ray. -/
theorem exercise_20_2
    (base first second : Point Rational)
    (firstScale secondScale : Rational)
    (firstScalePositive : 0 < firstScale)
    (secondScalePositive : 0 < secondScale) :
    (0 ≤ sectorTypeScalar base
        (rayRepresentative base first firstScale)
        (rayRepresentative base second secondScale) ↔
      0 ≤ sectorTypeScalar base first second) ∧
    (sectorTypeScalar base
        (rayRepresentative base first firstScale)
        (rayRepresentative base second secondScale) ≤ 0 ↔
      sectorTypeScalar base first second ≤ 0) := by
  have productPositive : 0 < firstScale * secondScale :=
    RFAP.ConstructiveFraction.mul_pos_direct firstScalePositive
      secondScalePositive
  rw [sectorTypeScalar_rayRepresentative,
    nonnegative_mul_iff_of_positive _ _ productPositive,
    nonpositive_mul_iff_of_positive _ _ productPositive]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The two additive inequalities encoded by
`first ≥ |second-third|`. -/
def SpreadDifferenceBound
    (first second third : Rational) : Prop :=
  second ≤ first + third ∧ third ≤ first + second

/-- All three additive acuteness inequalities for a triangle's spread
triple. -/
def AcuteSpreadBounds (first second third : Rational) : Prop :=
  third ≤ first + second ∧
    first ≤ second + third ∧
    second ≤ third + first

/-- Exercise 20.3: any two of the three absolute-difference bounds imply the
third and all three acuteness bounds.  The theorem packages all three choices
of the supplied pair. -/
theorem exercise_20_3 (first second third : Rational) :
    (SpreadDifferenceBound first second third ∧
        SpreadDifferenceBound second third first →
      SpreadDifferenceBound third first second ∧
        AcuteSpreadBounds first second third) ∧
    (SpreadDifferenceBound second third first ∧
        SpreadDifferenceBound third first second →
      SpreadDifferenceBound first second third ∧
        AcuteSpreadBounds first second third) ∧
    (SpreadDifferenceBound third first second ∧
        SpreadDifferenceBound first second third →
      SpreadDifferenceBound second third first ∧
        AcuteSpreadBounds first second third) := by
  unfold SpreadDifferenceBound AcuteSpreadBounds
  constructor
  · rintro ⟨⟨secondBound, thirdBound⟩, ⟨_thirdBound, firstBound⟩⟩
    exact ⟨⟨by simpa only [add_comm] using firstBound,
        by simpa only [add_comm] using secondBound⟩,
      ⟨thirdBound, firstBound, by simpa only [add_comm] using secondBound⟩⟩
  constructor
  · rintro ⟨⟨thirdBound, firstBound⟩, ⟨_firstBound, secondBound⟩⟩
    exact ⟨⟨by simpa only [add_comm] using secondBound,
        by simpa only [add_comm] using thirdBound⟩,
      ⟨by simpa only [add_comm] using thirdBound,
        firstBound, secondBound⟩⟩
  · rintro ⟨⟨firstBound, secondBound⟩, ⟨_secondBound, thirdBound⟩⟩
    exact ⟨⟨by simpa only [add_comm] using thirdBound,
        by simpa only [add_comm] using firstBound⟩,
      ⟨thirdBound, by simpa only [add_comm] using firstBound,
        secondBound⟩⟩

/-- The sector opposite `first` is obtuse in the source's quadrance
criterion. -/
def ObtuseAtFirst (first second third : Rational) : Prop :=
  second + third ≤ first

private theorem not_two_obtuse
    (first second third : Rational)
    (thirdPositive : 0 < third)
    (firstObtuse : ObtuseAtFirst first second third)
    (secondObtuse : ObtuseAtFirst second first third) : False := by
  have thirdNonnegative : (0 : Rational) ≤ third :=
    RFAP.ConstructiveFraction.le_of_lt_direct thirdPositive
  have secondAtMostFirst : second ≤ first := by
    calc
      second = 0 + second := by ring1
      _ ≤ third + second :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          thirdNonnegative second
      _ = second + third := by ring1
      _ ≤ first := firstObtuse
  have sumAtMostFirst : first + third ≤ first :=
    secondObtuse.trans secondAtMostFirst
  have firstBelowSum : first < first + third := by
    calc
      first = 0 + first := by ring1
      _ < third + first :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct thirdPositive first
      _ = first + third := by ring1
  exact (not_lt_of_ge sumAtMostFirst firstBelowSum).elim

/-- Exercise 20.4: for three positive quadrances, no two sectors can both be
obtuse.  The three conjuncts cover the three possible pairs. -/
theorem exercise_20_4 (first second third : Rational)
    (firstPositive : 0 < first) (secondPositive : 0 < second)
    (thirdPositive : 0 < third) :
    ¬ (ObtuseAtFirst first second third ∧
        ObtuseAtFirst second first third) ∧
    ¬ (ObtuseAtFirst second third first ∧
        ObtuseAtFirst third second first) ∧
    ¬ (ObtuseAtFirst third first second ∧
        ObtuseAtFirst first third second) := by
  constructor
  · rintro ⟨firstObtuse, secondObtuse⟩
    exact not_two_obtuse first second third thirdPositive
      firstObtuse secondObtuse
  constructor
  · rintro ⟨secondObtuse, thirdObtuse⟩
    exact not_two_obtuse second third first firstPositive
      secondObtuse thirdObtuse
  · rintro ⟨thirdObtuse, firstObtuse⟩
    exact not_two_obtuse third first second secondPositive
      thirdObtuse firstObtuse

/-- A point lies on the closed triangle when it has displayed nonnegative
barycentric weights. -/
def LiesOnTriangle
    (point first second third : Point Rational) : Prop :=
  ∃ firstWeight secondWeight thirdWeight : Rational,
    0 ≤ firstWeight ∧ 0 ≤ secondWeight ∧ 0 ≤ thirdWeight ∧
      firstWeight + secondWeight + thirdWeight = 1 ∧
      affineCombinationThree firstWeight first secondWeight second
        thirdWeight third = point

/-- The three quadrance inequalities defining an acute triangle. -/
def AcuteQuadranceBounds
    (first second third : Rational) : Prop :=
  third ≤ first + second ∧
    first ≤ second + third ∧
    second ≤ third + first

theorem rational_ne_zero_of_positive {value : Rational}
    (positive : 0 < value) : value ≠ 0 := by
  intro valueZero
  apply positive.2
  rw [valueZero]

theorem affineCircumcenterWeight_nonnegative_iff
    (opposite adjacentOne adjacentTwo area : Rational)
    (oppositePositive : 0 < opposite) (areaPositive : 0 < area) :
    0 ≤ affineCircumcenterWeight opposite adjacentOne adjacentTwo area ↔
      opposite ≤ adjacentOne + adjacentTwo := by
  have areaNonzero : area ≠ 0 := rational_ne_zero_of_positive areaPositive
  constructor
  · intro weightNonnegative
    have productNonnegative :
        0 ≤ affineCircumcenterWeight opposite adjacentOne adjacentTwo area *
          area :=
      RFAP.ConstructiveFraction.mul_nonneg_direct weightNonnegative
        (RFAP.ConstructiveFraction.le_of_lt_direct areaPositive)
    unfold affineCircumcenterWeight at productNonnegative
    rw [RFAP.ExplicitField.div_mul_cancel _ areaNonzero]
      at productNonnegative
    have differenceNonnegative :=
      (nonnegative_mul_iff_of_positive opposite
        (adjacentOne + adjacentTwo - opposite) oppositePositive).1
        productNonnegative
    exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      differenceNonnegative
  · intro bound
    have differenceNonnegative :
        0 ≤ adjacentOne + adjacentTwo - opposite :=
      RFAP.ConstructiveFraction.sub_nonneg_direct bound
    unfold affineCircumcenterWeight
    exact RFAP.ConstructiveFraction.div_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.le_of_lt_direct oppositePositive)
        differenceNonnegative)
      (RFAP.ConstructiveFraction.le_of_lt_direct areaPositive)

/-- Problem 2: a nondegenerate constructive-rational triangle is acute
exactly when its circumcenter has nonnegative barycentric weights, hence lies
on the closed triangle. -/
theorem problem_2
    (first second third : Point Rational)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (firstQuadrancePositive : 0 < quadrance second third)
    (secondQuadrancePositive : 0 < quadrance first third)
    (thirdQuadrancePositive : 0 < quadrance first second)
    (areaPositive : 0 < quadrea first second third) :
    LiesOnTriangle
        (circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear)
        first second third ↔
      AcuteQuadranceBounds
        (quadrance second third)
        (quadrance first third)
        (quadrance first second) := by
  let q₁ := quadrance second third
  let q₂ := quadrance first third
  let q₃ := quadrance first second
  let area := quadrea first second third
  let firstWeight := affineCircumcenterWeight q₁ q₂ q₃ area
  let secondWeight := affineCircumcenterWeight q₂ q₃ q₁ area
  let thirdWeight := affineCircumcenterWeight q₃ q₁ q₂ area
  have weightsSum : firstWeight + secondWeight + thirdWeight = 1 := by
    unfold firstWeight secondWeight thirdWeight q₁ q₂ q₃ area quadrea
    exact affine_circumcenter_weights_sum _ _ _
      (rational_ne_zero_of_positive areaPositive)
  have circumcenterFormula := affine_circumcenter first second third
    firstThirdDistinct secondThirdDistinct notCollinear
    (by decide : (2 : Rational) ≠ 0)
  have firstWeightCriterion : 0 ≤ firstWeight ↔ q₁ ≤ q₂ + q₃ := by
    unfold firstWeight
    exact affineCircumcenterWeight_nonnegative_iff q₁ q₂ q₃ area
      firstQuadrancePositive areaPositive
  have secondWeightCriterion : 0 ≤ secondWeight ↔ q₂ ≤ q₃ + q₁ := by
    unfold secondWeight
    exact affineCircumcenterWeight_nonnegative_iff q₂ q₃ q₁ area
      secondQuadrancePositive areaPositive
  have thirdWeightCriterion : 0 ≤ thirdWeight ↔ q₃ ≤ q₁ + q₂ := by
    unfold thirdWeight
    exact affineCircumcenterWeight_nonnegative_iff q₃ q₁ q₂ area
      thirdQuadrancePositive areaPositive
  constructor
  · rintro ⟨otherFirstWeight, otherSecondWeight, otherThirdWeight,
      otherFirstNonnegative, otherSecondNonnegative,
      otherThirdNonnegative, otherWeightsSum, pointEquation⟩
    have canonicalPoint :
        affineCombinationThree firstWeight first secondWeight second
            thirdWeight third =
          affineCircumcenterPoint first second third := by
      rfl
    have pointsEqual :
        affineCombinationThree firstWeight first secondWeight second
            thirdWeight third =
          affineCombinationThree otherFirstWeight first
            otherSecondWeight second otherThirdWeight third := by
      calc
        affineCombinationThree firstWeight first secondWeight second
            thirdWeight third =
            affineCircumcenterPoint first second third := canonicalPoint
        _ = circumcenterPoint first second third firstThirdDistinct
              secondThirdDistinct notCollinear := circumcenterFormula.symm
        _ = affineCombinationThree otherFirstWeight first
              otherSecondWeight second otherThirdWeight third :=
            pointEquation.symm
    have weightsEqual := affineCombinationThree_weights_unique
      first second third notCollinear weightsSum otherWeightsSum pointsEqual
    have firstNonnegative : 0 ≤ firstWeight := by
      rw [weightsEqual.1]
      exact otherFirstNonnegative
    have secondNonnegative : 0 ≤ secondWeight := by
      rw [weightsEqual.2.1]
      exact otherSecondNonnegative
    have thirdNonnegative : 0 ≤ thirdWeight := by
      rw [weightsEqual.2.2]
      exact otherThirdNonnegative
    unfold AcuteQuadranceBounds
    change q₃ ≤ q₁ + q₂ ∧ q₁ ≤ q₂ + q₃ ∧ q₂ ≤ q₃ + q₁
    exact ⟨thirdWeightCriterion.1 thirdNonnegative,
      firstWeightCriterion.1 firstNonnegative,
      secondWeightCriterion.1 secondNonnegative⟩
  · intro acute
    unfold AcuteQuadranceBounds at acute
    change q₃ ≤ q₁ + q₂ ∧ q₁ ≤ q₂ + q₃ ∧ q₂ ≤ q₃ + q₁ at acute
    have firstNonnegative : 0 ≤ firstWeight :=
      firstWeightCriterion.2 acute.2.1
    have secondNonnegative : 0 ≤ secondWeight :=
      secondWeightCriterion.2 acute.2.2
    have thirdNonnegative : 0 ≤ thirdWeight :=
      thirdWeightCriterion.2 acute.1
    refine ⟨firstWeight, secondWeight, thirdWeight, firstNonnegative,
      secondNonnegative, thirdNonnegative, weightsSum, ?_⟩
    calc
      affineCombinationThree firstWeight first secondWeight second
          thirdWeight third = affineCircumcenterPoint first second third := rfl
      _ = circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear := circumcenterFormula.symm

/-- The finite ordered-field content of being a nonzero triangle spread. -/
def PositiveUnitSpread (spread : Rational) : Prop :=
  0 < spread ∧ spread ≤ 1

/-- An explicit nonnegative square root for the discriminant in the normal
form of the Triple spread formula.  This replaces any completed square-root
operation by finite rational data. -/
def SpreadRootWitness
    (first second root : Rational) : Prop :=
  0 ≤ root ∧
    root ^ 2 = first * second * (1 - first) * (1 - second)

/-- The lower of the two displayed roots in §20.5, relative to an explicit
rational square-root witness. -/
def littleSpread (first second root : Rational) : Rational :=
  first + second - 2 * first * second - 2 * root

/-- The upper of the two displayed roots in §20.5, relative to an explicit
rational square-root witness. -/
def bigSpread (first second root : Rational) : Rational :=
  first + second - 2 * first * second + 2 * root

private theorem add_nonnegative
    {left right : Rational} (leftNonnegative : 0 ≤ left)
    (rightNonnegative : 0 ≤ right) : 0 ≤ left + right := by
  calc
    0 = 0 + 0 := by ring1
    _ ≤ left + right :=
      RFAP.ConstructiveFraction.add_le_add_direct leftNonnegative
        rightNonnegative

/-- The Triple spread equation has exactly the two displayed finite roots
once a square-root witness is supplied. -/
theorem spreadTriple_eq_little_or_big
    (first second third root : Rational)
    (triple : SpreadTriple first second third)
    (rootWitness : SpreadRootWitness first second root) :
    third = littleSpread first second root ∨
      third = bigSpread first second root := by
  have normalForm := (exercise_7_6 triple).2.2.2.2
  have equalSquares :
      (third - (first + second - 2 * first * second)) ^ 2 =
        (2 * root) ^ 2 := by
    calc
      (third - (first + second - 2 * first * second)) ^ 2 =
          4 * first * second * (1 - first) * (1 - second) := normalForm
      _ = 4 * (first * second * (1 - first) * (1 - second)) := by
        ring1
      _ = 4 * root ^ 2 := by rw [← rootWitness.2]
      _ = (2 * root) ^ 2 := by ring1
  have factorProduct :
      (third - (first + second - 2 * first * second) - 2 * root) *
          (third - (first + second - 2 * first * second) + 2 * root) =
        0 := by
    calc
      (third - (first + second - 2 * first * second) - 2 * root) *
            (third - (first + second - 2 * first * second) + 2 * root) =
          (third - (first + second - 2 * first * second)) ^ 2 -
            (2 * root) ^ 2 := by ring1
      _ = 0 := by rw [equalSquares]; ring1
  by_cases upperRoot :
      third - (first + second - 2 * first * second) - 2 * root = 0
  · right
    unfold bigSpread
    apply sub_eq_zero.mp
    calc
      third - (first + second - 2 * first * second + 2 * root) =
          third - (first + second - 2 * first * second) - 2 * root := by
            ring1
      _ = 0 := upperRoot
  · by_cases lowerRoot :
        third - (first + second - 2 * first * second) + 2 * root = 0
    · left
      unfold littleSpread
      apply sub_eq_zero.mp
      calc
        third - (first + second - 2 * first * second - 2 * root) =
            third - (first + second - 2 * first * second) + 2 * root := by
              ring1
        _ = 0 := lowerRoot
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero upperRoot lowerRoot) factorProduct)

/-- The big root automatically makes the first two sectors acute. -/
theorem bigSpread_first_second_acute
    (first second root : Rational)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second)
    (firstAtMostOne : first ≤ 1) (secondAtMostOne : second ≤ 1)
    (rootNonnegative : 0 ≤ root) :
    first ≤ bigSpread first second root + second ∧
      second ≤ bigSpread first second root + first := by
  have twoNonnegative : (0 : Rational) ≤ 2 := by decide
  have firstComplementNonnegative : 0 ≤ 1 - first :=
    RFAP.ConstructiveFraction.sub_nonneg_direct firstAtMostOne
  have secondComplementNonnegative : 0 ≤ 1 - second :=
    RFAP.ConstructiveFraction.sub_nonneg_direct secondAtMostOne
  have firstTermNonnegative :
      0 ≤ 2 * second * (1 - first) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct twoNonnegative
        secondNonnegative)
      firstComplementNonnegative
  have secondTermNonnegative :
      0 ≤ 2 * first * (1 - second) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct twoNonnegative
        firstNonnegative)
      secondComplementNonnegative
  have rootTermNonnegative : 0 ≤ 2 * root :=
    RFAP.ConstructiveFraction.mul_nonneg_direct twoNonnegative
      rootNonnegative
  constructor
  · apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      bigSpread first second root + second - first =
          2 * second * (1 - first) + 2 * root := by
            unfold bigSpread
            ring1
      _ ≥ 0 := add_nonnegative firstTermNonnegative rootTermNonnegative
  · apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      bigSpread first second root + first - second =
          2 * first * (1 - second) + 2 * root := by
            unfold bigSpread
            ring1
      _ ≥ 0 := add_nonnegative secondTermNonnegative rootTermNonnegative

/-- Triangle spread rule 1: among the two finite roots of the Triple spread
formula, the third spread is the big root exactly when the first two sectors
are acute.  The hypotheses state explicitly the positivity and unit bounds
that come from a nondegenerate rational triangle. -/
theorem triangle_spread_rule_1
    (first second third root : Rational)
    (firstRange : PositiveUnitSpread first)
    (secondRange : PositiveUnitSpread second)
    (thirdRange : PositiveUnitSpread third)
    (triple : SpreadTriple first second third)
    (rootWitness : SpreadRootWitness first second root) :
    third = bigSpread first second root ↔
      first ≤ third + second ∧ second ≤ third + first := by
  have firstNonnegative : 0 ≤ first :=
    RFAP.ConstructiveFraction.le_of_lt_direct firstRange.1
  have secondNonnegative : 0 ≤ second :=
    RFAP.ConstructiveFraction.le_of_lt_direct secondRange.1
  have firstComplementNonnegative : 0 ≤ 1 - first :=
    RFAP.ConstructiveFraction.sub_nonneg_direct firstRange.2
  have secondComplementNonnegative : 0 ≤ 1 - second :=
    RFAP.ConstructiveFraction.sub_nonneg_direct secondRange.2
  constructor
  · intro thirdBig
    rw [thirdBig]
    exact bigSpread_first_second_acute first second root firstNonnegative
      secondNonnegative firstRange.2 secondRange.2 rootWitness.1
  · rintro ⟨firstAcute, secondAcute⟩
    rcases spreadTriple_eq_little_or_big first second third root triple
      rootWitness with thirdLittle | thirdBig
    · by_cases rootZero : root = 0
      · calc
          third = littleSpread first second root := thirdLittle
          _ = bigSpread first second root := by
            unfold littleSpread bigSpread
            rw [rootZero]
            ring1
      · have rootPositive : 0 < root :=
          lt_of_le_of_ne rootWitness.1 (Ne.symm rootZero)
        have rootSquareProduct :
            root ^ 2 =
              (second * (1 - first)) * (first * (1 - second)) := by
          calc
            root ^ 2 =
                first * second * (1 - first) * (1 - second) :=
              rootWitness.2
            _ = (second * (1 - first)) *
                (first * (1 - second)) := by ring1
        have firstArmNonnegative : 0 ≤ second * (1 - first) :=
          RFAP.ConstructiveFraction.mul_nonneg_direct secondNonnegative
            firstComplementNonnegative
        have secondArmNonnegative : 0 ≤ first * (1 - second) :=
          RFAP.ConstructiveFraction.mul_nonneg_direct firstNonnegative
            secondComplementNonnegative
        have rootSquarePositive : 0 < root ^ 2 :=
          RFAP.ConstructiveFraction.pow_pos_direct rootPositive 2
        have armProductPositive :
            0 < (second * (1 - first)) * (first * (1 - second)) := by
          rw [← rootSquareProduct]
          exact rootSquarePositive
        have secondArmPositive : 0 < first * (1 - second) :=
          RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
            armProductPositive firstArmNonnegative
        have firstArmPositive : 0 < second * (1 - first) := by
          exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
            (by simpa only [mul_comm] using armProductPositive)
            secondArmNonnegative
        have rootLeFirstArm : root ≤ second * (1 - first) := by
          apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
            (c := (2 : Rational))
          · have acuteDifference : 0 ≤ third + second - first :=
              RFAP.ConstructiveFraction.sub_nonneg_direct firstAcute
            have scaled :
                root * 2 ≤ (second * (1 - first)) * 2 := by
              apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
              calc
                (second * (1 - first)) * 2 - root * 2 =
                    third + second - first := by
                      rw [thirdLittle]
                      unfold littleSpread
                      ring1
                _ ≥ 0 := acuteDifference
            exact scaled
          · decide
        have rootLeSecondArm : root ≤ first * (1 - second) := by
          apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
            (c := (2 : Rational))
          · have acuteDifference : 0 ≤ third + first - second :=
              RFAP.ConstructiveFraction.sub_nonneg_direct secondAcute
            have scaled :
                root * 2 ≤ (first * (1 - second)) * 2 := by
              apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
              calc
                (first * (1 - second)) * 2 - root * 2 =
                    third + first - second := by
                      rw [thirdLittle]
                      unfold littleSpread
                      ring1
                _ ≥ 0 := acuteDifference
            exact scaled
          · decide
        have rootSquareLeFirstArmSquare :
            root ^ 2 ≤ (second * (1 - first)) ^ 2 :=
          RFAP.ConstructiveFraction.pow_le_pow_direct rootWitness.1
            rootLeFirstArm 2
        have rootSquareLeSecondArmSquare :
            root ^ 2 ≤ (first * (1 - second)) ^ 2 :=
          RFAP.ConstructiveFraction.pow_le_pow_direct rootWitness.1
            rootLeSecondArm 2
        have secondArmLeFirstArm :
            first * (1 - second) ≤ second * (1 - first) := by
          apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
            (c := second * (1 - first))
          · calc
              (first * (1 - second)) * (second * (1 - first)) =
                  root ^ 2 := by rw [mul_comm, rootSquareProduct]
              _ ≤ (second * (1 - first)) ^ 2 :=
                rootSquareLeFirstArmSquare
              _ = (second * (1 - first)) *
                  (second * (1 - first)) := by ring1
          · exact firstArmPositive
        have firstArmLeSecondArm :
            second * (1 - first) ≤ first * (1 - second) := by
          apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
            (c := first * (1 - second))
          · calc
              (second * (1 - first)) * (first * (1 - second)) =
                  root ^ 2 := rootSquareProduct.symm
              _ ≤ (first * (1 - second)) ^ 2 :=
                rootSquareLeSecondArmSquare
              _ = (first * (1 - second)) *
                  (first * (1 - second)) := by ring1
          · exact secondArmPositive
        have armsEqual :
            second * (1 - first) = first * (1 - second) :=
          le_antisymm firstArmLeSecondArm secondArmLeFirstArm
        have firstEqualsSecond : first = second := by
          apply sub_eq_zero.mp
          calc
            first - second =
                first * (1 - second) - second * (1 - first) := by ring1
            _ = 0 := by rw [← armsEqual]; ring1
        have firstArmSquareEqualsRootSquare :
            (second * (1 - first)) ^ 2 = root ^ 2 := by
          calc
            (second * (1 - first)) ^ 2 =
                (second * (1 - first)) * (first * (1 - second)) := by
                  rw [armsEqual]
                  ring1
            _ = root ^ 2 := rootSquareProduct.symm
        have firstArmLeRoot : second * (1 - first) ≤ root :=
          RFAP.ConstructiveFraction.le_of_sq_le_sq_direct rootWitness.1
            (by rw [firstArmSquareEqualsRootSquare])
        have rootEqualsFirstArm : root = second * (1 - first) :=
          le_antisymm rootLeFirstArm firstArmLeRoot
        have thirdZero : third = 0 := by
          calc
            third = littleSpread first second root := thirdLittle
            _ = 0 := by
              unfold littleSpread
              rw [rootEqualsFirstArm, firstEqualsSecond]
              ring1
        exact False.elim
          ((rational_ne_zero_of_positive thirdRange.1) thirdZero)
    · exact thirdBig

/-- Comparing the explicit square root with `s₁s₂` is equivalent to comparing
`s₁+s₂` with one.  This is the finite algebraic sign calculation underlying
the second Triangle spread rule. -/
theorem spreadRoot_product_le_iff_sum_le_one
    (first second root : Rational)
    (firstRange : PositiveUnitSpread first)
    (secondRange : PositiveUnitSpread second)
    (rootWitness : SpreadRootWitness first second root) :
    first * second ≤ root ↔ first + second ≤ 1 := by
  have firstNonnegative : 0 ≤ first :=
    RFAP.ConstructiveFraction.le_of_lt_direct firstRange.1
  have secondNonnegative : 0 ≤ second :=
    RFAP.ConstructiveFraction.le_of_lt_direct secondRange.1
  have productPositive : 0 < first * second :=
    RFAP.ConstructiveFraction.mul_pos_direct firstRange.1 secondRange.1
  have productNonnegative : 0 ≤ first * second :=
    RFAP.ConstructiveFraction.le_of_lt_direct productPositive
  constructor
  · intro productLeRoot
    have squareOrder :
        (first * second) ^ 2 ≤ root ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct productNonnegative
        productLeRoot 2
    have factoredNonnegative :
        0 ≤ (first * second) * (1 - (first + second)) := by
      calc
        (first * second) * (1 - (first + second)) =
            root ^ 2 - (first * second) ^ 2 := by
              rw [rootWitness.2]
              ring1
        _ ≥ 0 := RFAP.ConstructiveFraction.sub_nonneg_direct squareOrder
    have complementNonnegative : 0 ≤ 1 - (first + second) :=
      (nonnegative_mul_iff_of_positive (first * second)
        (1 - (first + second)) productPositive).1 factoredNonnegative
    exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      complementNonnegative
  · intro sumLeOne
    have complementNonnegative : 0 ≤ 1 - (first + second) :=
      RFAP.ConstructiveFraction.sub_nonneg_direct sumLeOne
    have factoredNonnegative :
        0 ≤ (first * second) * (1 - (first + second)) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct productNonnegative
        complementNonnegative
    have squareOrder : (first * second) ^ 2 ≤ root ^ 2 := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        root ^ 2 - (first * second) ^ 2 =
            (first * second) * (1 - (first + second)) := by
              rw [rootWitness.2]
              ring1
        _ ≥ 0 := factoredNonnegative
    exact RFAP.ConstructiveFraction.le_of_sq_le_sq_direct rootWitness.1
      squareOrder

/-- For the big root, being at least `s₁+s₂` is equivalent to
`s₁+s₂≤1`. -/
theorem bigSpread_obtuse_iff_sum_le_one
    (first second root : Rational)
    (firstRange : PositiveUnitSpread first)
    (secondRange : PositiveUnitSpread second)
    (rootWitness : SpreadRootWitness first second root) :
    first + second ≤ bigSpread first second root ↔
      first + second ≤ 1 := by
  have twoPositive : (0 : Rational) < 2 := by decide
  have rootComparison := spreadRoot_product_le_iff_sum_le_one
    first second root firstRange secondRange rootWitness
  constructor
  · intro bigObtuse
    apply rootComparison.1
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (2 : Rational))
    · apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        root * 2 - (first * second) * 2 =
            bigSpread first second root - (first + second) := by
              unfold bigSpread
              ring1
        _ ≥ 0 := RFAP.ConstructiveFraction.sub_nonneg_direct bigObtuse
    · exact twoPositive
  · intro sumLeOne
    have productLeRoot := rootComparison.2 sumLeOne
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      bigSpread first second root - (first + second) =
          (root - first * second) * 2 := by
            unfold bigSpread
            ring1
      _ ≥ 0 :=
        RFAP.ConstructiveFraction.mul_nonneg_direct
          (RFAP.ConstructiveFraction.sub_nonneg_direct productLeRoot)
          (RFAP.ConstructiveFraction.le_of_lt_direct twoPositive)

/-- Triangle spread rule 2: the third sector is obtuse exactly when the first
two are acute and their spreads sum to at most one. -/
theorem triangle_spread_rule_2
    (first second third root : Rational)
    (firstRange : PositiveUnitSpread first)
    (secondRange : PositiveUnitSpread second)
    (thirdRange : PositiveUnitSpread third)
    (triple : SpreadTriple first second third)
    (rootWitness : SpreadRootWitness first second root) :
    first + second ≤ third ↔
      (first ≤ third + second ∧ second ≤ third + first) ∧
        first + second ≤ 1 := by
  have noTwoObtuse := exercise_20_4 first second third
    firstRange.1 secondRange.1 thirdRange.1
  have ruleOne := triangle_spread_rule_1 first second third root
    firstRange secondRange thirdRange triple rootWitness
  have bigCriterion := bigSpread_obtuse_iff_sum_le_one
    first second root firstRange secondRange rootWitness
  constructor
  · intro thirdObtuseBound
    have thirdObtuse : ObtuseAtFirst third first second :=
      thirdObtuseBound
    have firstAcute : first ≤ third + second := by
      by_cases acute : first ≤ third + second
      · exact acute
      · have strictObtuse : third + second < first :=
          RFAP.ConstructiveFraction.lt_of_not_ge_direct acute
        have firstObtuse : ObtuseAtFirst first third second :=
          RFAP.ConstructiveFraction.le_of_lt_direct strictObtuse
        exact False.elim (noTwoObtuse.2.2 ⟨thirdObtuse, firstObtuse⟩)
    have secondAcute : second ≤ third + first := by
      by_cases acute : second ≤ third + first
      · exact acute
      · have strictObtuse : third + first < second :=
          RFAP.ConstructiveFraction.lt_of_not_ge_direct acute
        have secondObtuse : ObtuseAtFirst second third first :=
          RFAP.ConstructiveFraction.le_of_lt_direct strictObtuse
        have reorderedThirdObtuse : ObtuseAtFirst third second first := by
          unfold ObtuseAtFirst at thirdObtuse ⊢
          simpa only [add_comm] using thirdObtuse
        exact False.elim
          (noTwoObtuse.2.1 ⟨secondObtuse, reorderedThirdObtuse⟩)
    have thirdBig : third = bigSpread first second root :=
      ruleOne.2 ⟨firstAcute, secondAcute⟩
    have bigObtuseBound :
        first + second ≤ bigSpread first second root := by
      calc
        first + second ≤ third := thirdObtuseBound
        _ = bigSpread first second root := thirdBig
    exact ⟨⟨firstAcute, secondAcute⟩, bigCriterion.1 bigObtuseBound⟩
  · rintro ⟨⟨firstAcute, secondAcute⟩, sumLeOne⟩
    have thirdBig : third = bigSpread first second root :=
      ruleOne.2 ⟨firstAcute, secondAcute⟩
    have bigObtuseBound :
        first + second ≤ bigSpread first second root :=
      bigCriterion.2 sumLeOne
    calc
      first + second ≤ bigSpread first second root := bigObtuseBound
      _ = third := thirdBig.symm

end TriangleSpreadRules
end DivineProportions
