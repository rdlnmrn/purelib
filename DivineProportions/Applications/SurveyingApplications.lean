import DivineProportions.Proportions.Stewart
import DivineProportions.Trigonometry.TripleSpread
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 24: surveying

Every construction is expressed by its finite quadrance/spread equations.
Decimal readings are retained as exact integer coefficient pairs, with
integer interval certificates for the source's numerical approximations.
-/

namespace DivineProportions
namespace SurveyingApplications

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

private theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel rightDenominator rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

/-! ## Problems 17--19: heights -/

/-- Problem 17: the complementary Spread-law equation gives the vertical
quadrance `Q=sP/(1-s)`. -/
theorem problem_17 (spread horizontalQuadrance verticalQuadrance : K)
    (complementNonzero : 1 - spread ≠ 0)
    (spreadLawCleared :
      verticalQuadrance * (1 - spread) = spread * horizontalQuadrance) :
    verticalQuadrance = spread * horizontalQuadrance / (1 - spread) := by
  apply eq_of_mul_eq_mul_right complementNonzero
  calc
    verticalQuadrance * (1 - spread) =
        spread * horizontalQuadrance := spreadLawCleared
    _ = (spread * horizontalQuadrance / (1 - spread)) *
        (1 - spread) :=
      (RFAP.ExplicitField.div_mul_cancel
        (spread * horizontalQuadrance) complementNonzero).symm

/-- Example 24.1: the exact answer is `58700/413`, strictly between
`142.130` and `142.131`. -/
theorem example_24_1 :
    587 * 100 = 58700 ∧
      142130 * 413 < 58700 * 1000 ∧
      58700 * 1000 < 142131 * 413 := by
  decide

/-- Problem 18.  Once a selected third spread satisfies the Triple-spread
equation, two Spread-law steps give the inaccessible height. -/
theorem problem_18
    (firstSpread secondSpread thirdSpread knownQuadrance
      slopingQuadrance verticalQuadrance : K)
    (thirdSpreadNonzero : thirdSpread ≠ 0)
    (_spreadTriple : SpreadTriple firstSpread secondSpread thirdSpread)
    (firstSpreadLaw :
      thirdSpread * slopingQuadrance = firstSpread * knownQuadrance)
    (rightTriangle : verticalQuadrance = secondSpread * slopingQuadrance) :
    verticalQuadrance =
      firstSpread * secondSpread * knownQuadrance / thirdSpread := by
  apply eq_of_mul_eq_mul_right thirdSpreadNonzero
  calc
    verticalQuadrance * thirdSpread =
        secondSpread * (thirdSpread * slopingQuadrance) := by
          rw [rightTriangle]
          ring1
    _ = secondSpread * (firstSpread * knownQuadrance) := by
      rw [firstSpreadLaw]
    _ = (firstSpread * secondSpread * knownQuadrance / thirdSpread) *
        thirdSpread := by
      rw [RFAP.ExplicitField.div_mul_cancel
        (firstSpread * secondSpread * knownQuadrance) thirdSpreadNonzero]
      ring1

/-- The common-denominator Triple-spread quadratic at `z=c/d`, when the two
measured spreads are `a/d,b/d`. -/
def surveyingTripleRootNumerator
    (a b c denominator : Int) : Int :=
  (c * denominator - a * denominator - b * denominator + 2 * a * b) ^ 2 -
    4 * a * b * (denominator - a) * (denominator - b)

/-- Example 24.2's selected small root lies between `0.02790` and `0.02791`.
The ensuing exact-input brackets are `210.6<Q₁<210.8` and
`82.1<Q<82.2`, exposing the source's much coarser `211.5,82.4`. -/
theorem example_24_2_corrected_certificates :
    0 < surveyingTripleRootNumerator 23520 38970 2790 100000 ∧
    surveyingTripleRootNumerator 23520 38970 2791 100000 < 0 ∧
    2106 * 2791 * 10000 < 10 * 100000 * 2352 * 25 ∧
    10 * 100000 * 2352 * 25 < 2108 * 2790 * 10000 ∧
    821 * 1000 * 2791 < 10 * (3897 * 2352 * 25) ∧
    10 * (3897 * 2352 * 25) < 822 * 1000 * 2790 := by
  decide

/-- Problem 19's two right-triangle substitutions and the final collinear
quad triple, all with their denominators cleared. -/
theorem problem_19
    (firstSpread secondSpread thirdSpread lowerSpread knownQuadrance
      slopingQuadrance upperHeight lowerHeight totalHeight : K)
    (firstSpreadLaw :
      thirdSpread * slopingQuadrance = firstSpread * knownQuadrance)
    (upperRightTriangle : upperHeight = secondSpread * slopingQuadrance)
    (horizontalRightTriangle :
      lowerSpread * (1 - secondSpread) * slopingQuadrance =
        (1 - lowerSpread) * lowerHeight)
    (heightQuadTriple : QuadTriple totalHeight lowerHeight upperHeight) :
    thirdSpread * upperHeight =
        firstSpread * secondSpread * knownQuadrance ∧
      thirdSpread * (1 - lowerSpread) * lowerHeight =
        firstSpread * (1 - secondSpread) * lowerSpread * knownQuadrance ∧
      QuadTriple totalHeight lowerHeight upperHeight := by
  constructor
  · calc
      thirdSpread * upperHeight =
          secondSpread * (thirdSpread * slopingQuadrance) := by
            rw [upperRightTriangle]
            ring1
      _ = secondSpread * (firstSpread * knownQuadrance) := by
        rw [firstSpreadLaw]
      _ = firstSpread * secondSpread * knownQuadrance := by ring1
  constructor
  · calc
      thirdSpread * (1 - lowerSpread) * lowerHeight =
          thirdSpread * ((1 - lowerSpread) * lowerHeight) := by ring1
      _ = thirdSpread *
          (lowerSpread * (1 - secondSpread) * slopingQuadrance) := by
            rw [← horizontalRightTriangle]
      _ = thirdSpread * lowerSpread * (1 - secondSpread) *
          slopingQuadrance := by ring1
      _ = lowerSpread * (1 - secondSpread) *
          (thirdSpread * slopingQuadrance) := by ring1
      _ = firstSpread * (1 - secondSpread) * lowerSpread *
          knownQuadrance := by rw [firstSpreadLaw]; ring1
  · exact heightQuadTriple

/-! ## Problem 20: Regiomontanus' problem -/

def regiomontanusSpread (P Q Q₁ Q₂ : K) : K :=
  Q * P / ((P + Q₁) * (P + Q₂))

def regiomontanusReducedDenominator (P Q₁ Q₂ : K) : K :=
  Q₁ + Q₂ + P + Q₁ * Q₂ / P

/-- The two displayed forms of the window spread are equal. -/
theorem regiomontanus_spread_rewrite
    (P Q Q₁ Q₂ : K)
    (PNonzero : P ≠ 0)
    (firstDenominatorNonzero : (P + Q₁) * (P + Q₂) ≠ 0)
    (secondDenominatorNonzero :
      regiomontanusReducedDenominator P Q₁ Q₂ ≠ 0) :
    regiomontanusSpread P Q Q₁ Q₂ =
      Q / regiomontanusReducedDenominator P Q₁ Q₂ := by
  unfold regiomontanusSpread
  apply div_eq_div_of_cross_mul firstDenominatorNonzero
    secondDenominatorNonzero
  unfold regiomontanusReducedDenominator
  have quotientCancel :=
    RFAP.ExplicitField.div_mul_cancel (Q₁ * Q₂) PNonzero
  calc
    (Q * P) * (Q₁ + Q₂ + P + Q₁ * Q₂ / P) =
        Q * ((P + Q₁) * (P + Q₂)) +
          Q * ((Q₁ * Q₂ / P) * P - Q₁ * Q₂) := by ring1
    _ = Q * ((P + Q₁) * (P + Q₂)) := by
      rw [quotientCancel]
      ring1

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- The AM--GM step in Problem 20, proved from one explicit square. -/
theorem regiomontanus_denominator_bound
    (P mean : Rational) (PPositive : 0 < P) :
    2 * mean ≤ P + mean ^ 2 / P := by
  have PNonzero : P ≠ 0 := by
    intro PZero
    rw [PZero] at PPositive
    exact (lt_irrefl 0 PPositive).elim
  have squareNonnegative : (0 : Rational) ≤ (P - mean) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct (P - mean)
  have quotientNonnegative : (0 : Rational) ≤ (P - mean) ^ 2 / P :=
    RFAP.ConstructiveFraction.div_nonneg_direct squareNonnegative
      (RFAP.ConstructiveFraction.le_of_lt_direct PPositive)
  have differenceIdentity :
      P + mean ^ 2 / P - 2 * mean = (P - mean) ^ 2 / P := by
    apply eq_of_mul_eq_mul_right PNonzero
    calc
      (P + mean ^ 2 / P - 2 * mean) * P =
          P ^ 2 + (mean ^ 2 / P) * P - 2 * mean * P := by ring1
      _ = P ^ 2 + mean ^ 2 - 2 * mean * P := by
        rw [RFAP.ExplicitField.div_mul_cancel (mean ^ 2) PNonzero]
      _ = (P - mean) ^ 2 := by ring1
      _ = ((P - mean) ^ 2 / P) * P :=
        (RFAP.ExplicitField.div_mul_cancel ((P - mean) ^ 2) PNonzero).symm
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  rw [differenceIdentity]
  exact quotientNonnegative

/-- Problem 20: when `mean²=Q₁Q₂`, the variable denominator is
minimized at the displayed geometric-mean witness `P=mean`. -/
theorem problem_20 (P mean Q₁ Q₂ : Rational)
    (PPositive : 0 < P) (meanSquare : mean ^ 2 = Q₁ * Q₂) :
    2 * mean ≤ P + Q₁ * Q₂ / P ∧
      mean + Q₁ * Q₂ / mean = 2 * mean := by
  constructor
  · rw [← meanSquare]
    exact regiomontanus_denominator_bound P mean PPositive
  · rw [← meanSquare]
    by_cases meanZero : mean = 0
    · rw [meanZero, pow_two, zero_mul,
          RFAP.ExplicitField.zero_div]
      ring1
    ·
      have quotientValue : mean ^ 2 / mean = mean := by
        apply eq_of_mul_eq_mul_right meanZero
        calc
          (mean ^ 2 / mean) * mean = mean ^ 2 :=
            RFAP.ExplicitField.div_mul_cancel (mean ^ 2) meanZero
          _ = mean * mean := by ring1
      rw [quotientValue]
      ring1

/-! ## Problems 21--23 and spherical Pythagoras -/

private theorem complement_div (spread : K) (spreadNonzero : spread ≠ 0) :
    (1 - spread) / spread = 1 / spread - 1 := by
  apply eq_of_mul_eq_mul_right spreadNonzero
  calc
    ((1 - spread) / spread) * spread = 1 - spread :=
      RFAP.ExplicitField.div_mul_cancel (1 - spread) spreadNonzero
    _ = (1 / spread) * spread - 1 * spread := by
      rw [RFAP.ExplicitField.div_mul_cancel 1 spreadNonzero]
      ring1
    _ = (1 / spread - 1) * spread := by ring1

private theorem scaled_complement_div
    (spread H : K) (spreadNonzero : spread ≠ 0) :
    (1 - spread) * H / spread = (1 / spread - 1) * H := by
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  have relation := complement_div spread spreadNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv] at relation
  calc
    (1 - spread) * H * spread⁻¹ =
        ((1 - spread) * spread⁻¹) * H := by ring1
    _ = (1 * spread⁻¹ - 1) * H := by rw [relation]

/-- Problem 21: substituting the three right-triangle height formulas into
Stewart's relation gives the printed quadratic equation for `H`. -/
theorem problem_21
    (P₁ P₂ H r₁ r₂ r₃ Q₁ Q₂ P₃ : K)
    (r₁Nonzero : r₁ ≠ 0) (r₂Nonzero : r₂ ≠ 0)
    (r₃Nonzero : r₃ ≠ 0)
    (Q₂Value : Q₂ = (1 - r₁) * H / r₁)
    (Q₁Value : Q₁ = (1 - r₂) * H / r₂)
    (P₃Value : P₃ = (1 - r₃) * H / r₃)
    (stewartRelation :
      P₂ * (P₃ + P₁ - Q₂) ^ 2 =
        P₁ * (P₃ + P₂ - Q₁) ^ 2) :
    P₂ * (H * (1 / r₃ - 1 / r₁) + P₁) ^ 2 =
      P₁ * (H * (1 / r₃ - 1 / r₂) + P₂) ^ 2 := by
  rw [P₃Value, Q₂Value, Q₁Value] at stewartRelation
  rw [scaled_complement_div r₁ H r₁Nonzero,
    scaled_complement_div r₂ H r₂Nonzero,
    scaled_complement_div r₃ H r₃Nonzero] at stewartRelation
  calc
    P₂ * (H * (1 / r₃ - 1 / r₁) + P₁) ^ 2 =
        P₂ * ((1 / r₃ - 1) * H + P₁ -
          (1 / r₁ - 1) * H) ^ 2 := by ring1
    _ = P₁ * ((1 / r₃ - 1) * H + P₂ -
          (1 / r₂ - 1) * H) ^ 2 := stewartRelation
    _ = P₁ * (H * (1 / r₃ - 1 / r₂) + P₂) ^ 2 := by
      ring1

/-- Problem 22's denominator-free vertical/horizontal spread relation. -/
theorem problem_22_cleared
    (s₁ s₂ r₁ r₂ Q₁ Q₂ H : K)
    (HNonzero : H ≠ 0)
    (horizontalSpreadLaw : s₁ * Q₂ = s₂ * Q₁)
    (firstVertical : r₁ * Q₂ = (1 - r₁) * H)
    (secondVertical : r₂ * Q₁ = (1 - r₂) * H) :
    s₁ * (1 - r₁) * r₂ = s₂ * (1 - r₂) * r₁ := by
  apply eq_of_mul_eq_mul_right HNonzero
  calc
    (s₁ * (1 - r₁) * r₂) * H =
        s₁ * (r₁ * Q₂) * r₂ := by rw [firstVertical]; ring1
    _ = (s₁ * Q₂) * r₁ * r₂ := by ring1
    _ = (s₂ * Q₁) * r₁ * r₂ := by rw [horizontalSpreadLaw]
    _ = s₂ * (r₂ * Q₁) * r₁ := by ring1
    _ = (s₂ * (1 - r₂) * r₁) * H := by rw [secondVertical]; ring1

/-- Problem 22's final displayed quotient form. -/
theorem problem_22
    (s₁ s₂ r₁ r₂ : K)
    (r₁Nonzero : r₁ ≠ 0) (r₂Nonzero : r₂ ≠ 0)
    (cleared :
      s₁ * (1 - r₁) * r₂ = s₂ * (1 - r₂) * r₁) :
    s₁ / r₁ - s₂ / r₂ = s₁ - s₂ := by
  have productNonzero : r₁ * r₂ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero r₁Nonzero r₂Nonzero
  apply eq_of_mul_eq_mul_right productNonzero
  have firstTerm : (s₁ / r₁) * (r₁ * r₂) = s₁ * r₂ := by
    calc
      (s₁ / r₁) * (r₁ * r₂) =
          ((s₁ / r₁) * r₁) * r₂ := by ring1
      _ = s₁ * r₂ := by
        rw [RFAP.ExplicitField.div_mul_cancel s₁ r₁Nonzero]
  have secondTerm : (s₂ / r₂) * (r₁ * r₂) = s₂ * r₁ := by
    calc
      (s₂ / r₂) * (r₁ * r₂) =
          ((s₂ / r₂) * r₂) * r₁ := by ring1
      _ = s₂ * r₁ := by
        rw [RFAP.ExplicitField.div_mul_cancel s₂ r₂Nonzero]
  calc
    (s₁ / r₁ - s₂ / r₂) * (r₁ * r₂) =
        (s₁ / r₁) * (r₁ * r₂) -
          (s₂ / r₂) * (r₁ * r₂) := by ring1
    _ = s₁ * r₂ - s₂ * r₁ := by rw [firstTerm, secondTerm]
    _ =
        (s₁ - s₂) * (r₁ * r₂) +
          (s₁ * (1 - r₁) * r₂ -
            s₂ * (1 - r₂) * r₁) := by ring1
    _ = (s₁ - s₂) * (r₁ * r₂) := by rw [cleared]; ring1

/-- Problem 23: the Cross law over a horizontal right triangle yields
`1-s=r₁r₂`. -/
theorem problem_23
    (Q₁ Q₂ H spread r₁ r₂ : K)
    (firstTotalNonzero : Q₁ + H ≠ 0)
    (secondTotalNonzero : Q₂ + H ≠ 0)
    (crossLawCleared :
      4 * H ^ 2 = 4 * (Q₁ + H) * (Q₂ + H) * (1 - spread))
    (firstVertical : r₁ * (Q₂ + H) = H)
    (secondVertical : r₂ * (Q₁ + H) = H)
    (fourNonzero : (4 : K) ≠ 0) :
    1 - spread = r₁ * r₂ := by
  have denominatorNonzero :
      4 * ((Q₁ + H) * (Q₂ + H)) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero
      (RFAP.ExplicitField.mul_ne_zero firstTotalNonzero secondTotalNonzero)
  have verticalProduct :
      (r₁ * r₂) * ((Q₁ + H) * (Q₂ + H)) = H ^ 2 := by
    calc
      (r₁ * r₂) * ((Q₁ + H) * (Q₂ + H)) =
          (r₂ * (Q₁ + H)) * (r₁ * (Q₂ + H)) := by ring1
      _ = H * H := by rw [firstVertical, secondVertical]
      _ = H ^ 2 := by ring1
  apply eq_of_mul_eq_mul_right denominatorNonzero
  calc
    (1 - spread) * (4 * ((Q₁ + H) * (Q₂ + H))) =
        4 * (Q₁ + H) * (Q₂ + H) * (1 - spread) := by ring1
    _ = 4 * H ^ 2 := crossLawCleared.symm
    _ = (r₁ * r₂) * (4 * ((Q₁ + H) * (Q₂ + H))) := by
      rw [show (r₁ * r₂) *
          (4 * ((Q₁ + H) * (Q₂ + H))) =
        4 * ((r₁ * r₂) * ((Q₁ + H) * (Q₂ + H))) by ring1,
        verticalProduct]

/-- Exercise 24.1, reduced to the common normalized dot ratio `t`. -/
theorem exercise_24_1 (q S t : K)
    (lineSpread : q = 1 - t ^ 2)
    (planeSpreadCleared : S * (1 + t) ^ 2 = 1 + 2 * t) :
    (1 - S * q) ^ 2 = 4 * (1 - S) * (1 - q) := by
  have complementPlane : (1 - S) * (1 + t) ^ 2 = t ^ 2 := by
    calc
      (1 - S) * (1 + t) ^ 2 =
          (1 + t) ^ 2 - S * (1 + t) ^ 2 := by ring1
      _ = (1 + t) ^ 2 - (1 + 2 * t) := by rw [planeSpreadCleared]
      _ = t ^ 2 := by ring1
  have mixedRelation : S * t ^ 2 = (1 - S) * (1 + 2 * t) := by
    calc
      S * t ^ 2 = S * (1 + t) ^ 2 - S * (1 + 2 * t) := by ring1
      _ = (1 + 2 * t) - S * (1 + 2 * t) := by rw [planeSpreadCleared]
      _ = (1 - S) * (1 + 2 * t) := by ring1
  rw [lineSpread]
  calc
    (1 - S * (1 - t ^ 2)) ^ 2 = ((1 - S) + S * t ^ 2) ^ 2 := by ring1
    _ = ((1 - S) + (1 - S) * (1 + 2 * t)) ^ 2 := by rw [mixedRelation]
    _ = 4 * (1 - S) * ((1 - S) * (1 + t) ^ 2) := by ring1
    _ = 4 * (1 - S) * t ^ 2 := by rw [complementPlane]
    _ = 4 * (1 - S) * (1 - (1 - t ^ 2)) := by ring1

/-- The spherical analogue of Pythagoras following Problem 23. -/
theorem spherical_pythagoras (q q₁ q₂ : K)
    (complementProduct : 1 - q = (1 - q₁) * (1 - q₂)) :
    q = q₁ + q₂ - q₁ * q₂ := by
  calc
    q = 1 - (1 - q) := by ring1
    _ = 1 - (1 - q₁) * (1 - q₂) := by rw [complementProduct]
    _ = q₁ + q₂ - q₁ * q₂ := by ring1

end SurveyingApplications
end DivineProportions
