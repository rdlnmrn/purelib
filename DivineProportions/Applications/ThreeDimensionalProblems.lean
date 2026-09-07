import DivineProportions.Applications.TriangleSpreadRules
import DivineProportions.Space.Metric

/-!
# Divine Proportions, Chapter 22: three-dimensional problems

The source explicitly describes its three-dimensional treatment as informal.
Here every assertion is split into finite Cartesian dot-product algebra and
the scalar identities used in the printed solutions.  Algebraic roots and
distances are supplied as witnesses; no completed real-number construction is
introduced.
-/

namespace DivineProportions
namespace ThreeDimensionalProblems

open Vector3

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

private theorem directionSpread_metric_formula
    (first second : Vector3 K) (metric dotValue : K)
    (metricNonzero : metric ≠ 0)
    (firstMetric : Vector3.quadrance first = metric)
    (secondMetric : Vector3.quadrance second = metric)
    (dotMetric : Vector3.dot first second = dotValue) :
    directionSpread first second
        (by rw [firstMetric]; exact metricNonzero)
        (by rw [secondMetric]; exact metricNonzero) =
      (metric ^ 2 - dotValue ^ 2) / metric ^ 2 := by
  have denominatorNonzero : metric * metric ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero metricNonzero metricNonzero
  apply eq_of_mul_eq_mul_right denominatorNonzero
  unfold directionSpread
  rw [firstMetric, secondMetric, dotMetric]
  have leftCancel :=
    RFAP.ExplicitField.div_mul_cancel (dotValue ^ 2) denominatorNonzero
  have rightCancel :=
    RFAP.ExplicitField.div_mul_cancel
      (metric ^ 2 - dotValue ^ 2) denominatorNonzero
  calc
    (1 - dotValue ^ 2 / (metric * metric)) * (metric * metric) =
        metric ^ 2 -
          (dotValue ^ 2 / (metric * metric)) * (metric * metric) := by
            ring1
    _ = metric ^ 2 - dotValue ^ 2 := by rw [leftCancel]
    _ = ((metric ^ 2 - dotValue ^ 2) / metric ^ 2) *
          (metric * metric) := by
            simpa only [pow_two] using rightCancel.symm

def boxLongDiagonal (first second third : Vector3 K) : Vector3 K :=
  add (add first second) third

def boxOppositeFirstDiagonal
    (first second third : Vector3 K) : Vector3 K :=
  add (add (neg first) second) third

def boxOppositeSecondDiagonal
    (first second third : Vector3 K) : Vector3 K :=
  add (add first (neg second)) third

def boxOppositeThirdDiagonal
    (first second third : Vector3 K) : Vector3 K :=
  add (add first second) (neg third)

/-- The finite dot-product calculation behind a rectangular box: all four
long diagonals have quadrance `P+Q+R`, and their three possible dot products
with a fixed diagonal are obtained by changing one sign. -/
theorem box_long_diagonal_metrics
    (first second third : Vector3 K) (P Q R : K)
    (firstQuadrance : Vector3.quadrance first = P)
    (secondQuadrance : Vector3.quadrance second = Q)
    (thirdQuadrance : Vector3.quadrance third = R)
    (firstSecond : Vector3.Orthogonal first second)
    (firstThird : Vector3.Orthogonal first third)
    (secondThird : Vector3.Orthogonal second third) :
    Vector3.quadrance (boxLongDiagonal first second third) = P + Q + R ∧
    Vector3.quadrance (boxOppositeFirstDiagonal first second third) = P + Q + R ∧
    Vector3.quadrance (boxOppositeSecondDiagonal first second third) = P + Q + R ∧
    Vector3.quadrance (boxOppositeThirdDiagonal first second third) = P + Q + R ∧
    Vector3.dot (boxLongDiagonal first second third)
        (boxOppositeFirstDiagonal first second third) = -P + Q + R ∧
    Vector3.dot (boxLongDiagonal first second third)
        (boxOppositeSecondDiagonal first second third) = P - Q + R ∧
    Vector3.dot (boxLongDiagonal first second third)
        (boxOppositeThirdDiagonal first second third) = P + Q - R := by
  have secondFirst : dot second first = 0 := by
    rw [dot_comm]
    exact firstSecond
  have thirdFirst : dot third first = 0 := by
    rw [dot_comm]
    exact firstThird
  have thirdSecond : dot third second = 0 := by
    rw [dot_comm]
    exact secondThird
  change dot first first = P at firstQuadrance
  change dot second second = Q at secondQuadrance
  change dot third third = R at thirdQuadrance
  unfold boxLongDiagonal boxOppositeFirstDiagonal
    boxOppositeSecondDiagonal boxOppositeThirdDiagonal Vector3.quadrance
  simp only [dot_add_left, dot_add_right, dot_neg_left, dot_neg_right]
  rw [firstQuadrance, secondQuadrance, thirdQuadrance,
    firstSecond, firstThird, secondThird,
    secondFirst, thirdFirst, thirdSecond]
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

/-- Exercise 22.1.  These are exactly the three spreads formed by pairs of
long diagonals of a rectangular box with edge quadrances `P,Q,R`. -/
theorem exercise_22_1
    (first second third : Vector3 K) (P Q R : K)
    (firstQuadrance : Vector3.quadrance first = P)
    (secondQuadrance : Vector3.quadrance second = Q)
    (thirdQuadrance : Vector3.quadrance third = R)
    (firstSecond : Vector3.Orthogonal first second)
    (firstThird : Vector3.Orthogonal first third)
    (secondThird : Vector3.Orthogonal second third)
    (totalNonzero : P + Q + R ≠ 0) :
    directionSpread
        (boxLongDiagonal first second third)
        (boxOppositeFirstDiagonal first second third)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).1]
          exact totalNonzero)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).2.1]
          exact totalNonzero) =
      4 * P * (Q + R) / (P + Q + R) ^ 2 ∧
    directionSpread
        (boxLongDiagonal first second third)
        (boxOppositeSecondDiagonal first second third)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).1]
          exact totalNonzero)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).2.2.1]
          exact totalNonzero) =
      4 * Q * (R + P) / (P + Q + R) ^ 2 ∧
    directionSpread
        (boxLongDiagonal first second third)
        (boxOppositeThirdDiagonal first second third)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).1]
          exact totalNonzero)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).2.2.2.1]
          exact totalNonzero) =
      4 * R * (P + Q) / (P + Q + R) ^ 2 := by
  let metrics := box_long_diagonal_metrics first second third P Q R
    firstQuadrance secondQuadrance thirdQuadrance firstSecond firstThird
    secondThird
  have firstFormula := directionSpread_metric_formula
    (boxLongDiagonal first second third)
    (boxOppositeFirstDiagonal first second third)
    (P + Q + R) (-P + Q + R) totalNonzero metrics.1 metrics.2.1
    metrics.2.2.2.2.1
  have secondFormula := directionSpread_metric_formula
    (boxLongDiagonal first second third)
    (boxOppositeSecondDiagonal first second third)
    (P + Q + R) (P - Q + R) totalNonzero metrics.1 metrics.2.2.1
    metrics.2.2.2.2.2.1
  have thirdFormula := directionSpread_metric_formula
    (boxLongDiagonal first second third)
    (boxOppositeThirdDiagonal first second third)
    (P + Q + R) (P + Q - R) totalNonzero metrics.1 metrics.2.2.2.1
    metrics.2.2.2.2.2.2
  constructor
  · calc
      directionSpread _ _ _ _ =
          ((P + Q + R) ^ 2 - (-P + Q + R) ^ 2) /
            (P + Q + R) ^ 2 := firstFormula
      _ = 4 * P * (Q + R) / (P + Q + R) ^ 2 := by
        congr 1
        ring1
  constructor
  · calc
      directionSpread _ _ _ _ =
          ((P + Q + R) ^ 2 - (P - Q + R) ^ 2) /
            (P + Q + R) ^ 2 := secondFormula
      _ = 4 * Q * (R + P) / (P + Q + R) ^ 2 := by
        congr 1
        ring1
  · calc
      directionSpread _ _ _ _ =
          ((P + Q + R) ^ 2 - (P + Q - R) ^ 2) /
            (P + Q + R) ^ 2 := thirdFormula
      _ = 4 * R * (P + Q) / (P + Q + R) ^ 2 := by
        congr 1
        ring1

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- Problem 8's exact scalar results: face diagonal `7`, long diagonal `12`,
base spread `5/12`, center quadrance `3`, and the three diagonal spreads. -/
theorem problem_8 :
    ((3 : Rational) + 4 = 7) ∧
    ((7 : Rational) + 5 = 12) ∧
    ((5 : Rational) / 12 = 5 / 12) ∧
    ((12 : Rational) / 4 = 3) ∧
    ((4 * 3 * (4 + 5) / 12 ^ 2 : Rational) = 3 / 4) ∧
    ((4 * 4 * (5 + 3) / 12 ^ 2 : Rational) = 8 / 9) ∧
    ((4 * 5 * (3 + 4) / 12 ^ 2 : Rational) = 35 / 36) := by
  decide

/-- The scalar reduction of Exercise 22.2.  The normal to `ABP` has squared
quadrance `QR(Q+R)`, while a direction of `PF` has quadrance `P+Q+R` and
dot product `-2QR`; hence the line-plane spread has this value. -/
def boxCenterPlaneLineSpread (P Q R : K) : K :=
  4 * Q * R / ((P + Q + R) * (Q + R))

def boxCenterToOppositeDirection
    (first second third : Vector3 K) : Vector3 K :=
  add (add first (neg second)) third

def boxCenterPlaneNormal
    (second third : Vector3 K) (Q R : K) : Vector3 K :=
  add (scale R second) (neg (scale Q third))

def boxCenterToOppositeLine
    (first second third : Vector3 K) : Line3 K :=
  ⟨⟨0, 0, 0⟩, boxCenterToOppositeDirection first second third⟩

def boxCenterPlane
    (second third : Vector3 K) (Q R : K) : Plane3 K :=
  ⟨boxCenterPlaneNormal second third Q R, 0⟩

/-- The three metric values used in Exercise 22.2.  Multiplying the midpoint
directions by two removes every coordinate denominator. -/
theorem box_center_plane_line_metrics
    (first second third : Vector3 K) (P Q R : K)
    (firstQuadrance : Vector3.quadrance first = P)
    (secondQuadrance : Vector3.quadrance second = Q)
    (thirdQuadrance : Vector3.quadrance third = R)
    (firstSecond : Vector3.Orthogonal first second)
    (firstThird : Vector3.Orthogonal first third)
    (secondThird : Vector3.Orthogonal second third) :
    Vector3.quadrance
        (boxCenterToOppositeDirection first second third) = P + Q + R ∧
      Vector3.quadrance (boxCenterPlaneNormal second third Q R) =
        Q * R * (Q + R) ∧
      Vector3.dot (boxCenterToOppositeDirection first second third)
          (boxCenterPlaneNormal second third Q R) = -2 * Q * R := by
  have secondFirst : Vector3.dot second first = 0 := by
    rw [Vector3.dot_comm]
    exact firstSecond
  have thirdFirst : Vector3.dot third first = 0 := by
    rw [Vector3.dot_comm]
    exact firstThird
  have thirdSecond : Vector3.dot third second = 0 := by
    rw [Vector3.dot_comm]
    exact secondThird
  change Vector3.dot first first = P at firstQuadrance
  change Vector3.dot second second = Q at secondQuadrance
  change Vector3.dot third third = R at thirdQuadrance
  unfold boxCenterToOppositeDirection boxCenterPlaneNormal Vector3.quadrance
  simp only [Vector3.dot_add_left, Vector3.dot_add_right,
    Vector3.dot_neg_left, Vector3.dot_neg_right,
    Vector3.dot_scale_left, Vector3.dot_scale_right]
  rw [firstQuadrance, secondQuadrance, thirdQuadrance,
    firstSecond, firstThird, secondThird,
    secondFirst, thirdFirst, thirdSecond]
  constructor
  · ring1
  constructor <;> ring1

/-- Exercise 22.2 in spatial coordinates.  The displayed normal is
`R·BC-Q·CG`; the displayed line direction is twice `PF`. -/
theorem exercise_22_2_geometric
    (first second third : Vector3 K) (P Q R : K)
    (firstQuadrance : Vector3.quadrance first = P)
    (secondQuadrance : Vector3.quadrance second = Q)
    (thirdQuadrance : Vector3.quadrance third = R)
    (firstSecond : Vector3.Orthogonal first second)
    (firstThird : Vector3.Orthogonal first third)
    (secondThird : Vector3.Orthogonal second third)
    (totalNonzero : P + Q + R ≠ 0)
    (QNonzero : Q ≠ 0) (RNonzero : R ≠ 0)
    (sumNonzero : Q + R ≠ 0)
    (lineNonNull :
      ¬ (boxCenterToOppositeLine first second third).IsNull)
    (planeNonNull : ¬ (boxCenterPlane second third Q R).IsNull) :
    linePlaneSpread
        (boxCenterToOppositeLine first second third)
        (boxCenterPlane second third Q R)
        lineNonNull planeNonNull = boxCenterPlaneLineSpread P Q R := by
  let metrics := box_center_plane_line_metrics first second third P Q R
    firstQuadrance secondQuadrance thirdQuadrance firstSecond firstThird
    secondThird
  have QRNonzero : Q * R ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero QNonzero RNonzero
  have normalMetricNonzero : Q * R * (Q + R) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero QRNonzero sumNonzero
  have leftDenominatorNonzero :
      (P + Q + R) * (Q * R * (Q + R)) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero totalNonzero normalMetricNonzero
  have rightDenominatorNonzero :
      (P + Q + R) * (Q + R) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero totalNonzero sumNonzero
  unfold linePlaneSpread boxCenterToOppositeLine boxCenterPlane
  change
    Vector3.dot (boxCenterToOppositeDirection first second third)
          (boxCenterPlaneNormal second third Q R) ^ 2 /
        (Vector3.quadrance
            (boxCenterToOppositeDirection first second third) *
          Vector3.quadrance (boxCenterPlaneNormal second third Q R)) = _
  rw [metrics.1, metrics.2.1, metrics.2.2]
  unfold boxCenterPlaneLineSpread
  apply div_eq_div_of_cross_mul
    leftDenominatorNonzero rightDenominatorNonzero
  ring1

theorem exercise_22_2 :
    boxCenterPlaneLineSpread (3 : Rational) 4 5 = 20 / 27 := by
  decide

def problem9FirstSpread : Rational := 3 / 25
def problem9SecondSpread : Rational := 19 / 100
def problem9PoleQuadrance : Rational := 7350 / 11
def problem9WestQuadrance : Rational := 595350 / 209
def problem9AnswerQuadrance : Rational := 1619450 / 209

/-- Problem 9 through the exact quadrance answer, before taking any square
root or decimal approximation.  Each fraction is represented by its numerator
and denominator, so the certificate is pure integer arithmetic. -/
theorem problem_9_exact :
    (25 - 3 = 22) ∧
    (22 * 7350 = 3 * 4900 * 11) ∧
    (100 - 19 = 81) ∧
    (595350 = 81 * 7350) ∧
    (1619450 = 4900 * 209 + 595350) := by
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- Problem 9's printed radical is retained as one finite witness.  The
equation `209d=35r` is the quotient-free meaning of `d=35r/209`. -/
theorem problem_9_distance_witness
    (root distance : K) (twoHundredNineNonzero : (209 : K) ≠ 0)
    (rootSquare : root ^ 2 = 276298)
    (distanceValue : 209 * distance = 35 * root) :
    209 * distance ^ 2 = 1619450 := by
  apply eq_of_mul_eq_mul_right twoHundredNineNonzero
  calc
    (209 * distance ^ 2) * 209 = (209 * distance) ^ 2 := by ring1
    _ = (35 * root) ^ 2 := by rw [distanceValue]
    _ = 35 ^ 2 * root ^ 2 := by ring1
    _ = 35 ^ 2 * 276298 := by rw [rootSquare]
    _ = 1619450 * 209 := by ring1

/-- The printed (truncated) `88.02` approximation is justified without
defining a real square root: these integer comparisons are exactly the
positive-denominator clearings of
`88.02² < 1619450/209 < 88.03²`. -/
theorem problem_9_decimal_bracket :
    4401 ^ 2 * 209 < 1619450 * 50 ^ 2 ∧
      1619450 * 100 ^ 2 < 8803 ^ 2 * 209 := by
  decide

/-- Problem 10's two exact spread calculations. -/
theorem problem_10 :
    (10 + 10 = 20) ∧
    (20 = 4 * 5) ∧
    (5 + 18 = 23) ∧
    (4 * 5 * 18 = 360) ∧
    (23 ^ 2 = 529) ∧
    (10 * (4 * 23 - 10) = 4 * 205) ∧
    (20 * 23 * (4 * 205 - 20 * 23) * 1681 =
      1656 * 205 * (4 * 205)) := by
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

/-- Problem 11.  The three quotient-free equations are respectively the
maximum-slope right triangle, the turn by spread `r`, and the final
line-to-horizontal spread. -/
theorem problem_11
    (S r maximumPath insectPath answer : K)
    (insectPathNonzero : insectPath ≠ 0)
    (maximumSlope : S * maximumPath = 1)
    (pathTurn : (1 - r) * insectPath = maximumPath)
    (answerSpread : answer * insectPath = 1) :
    answer = S * (1 - r) := by
  apply eq_of_mul_eq_mul_right insectPathNonzero
  calc
    answer * insectPath = 1 := answerSpread
    _ = S * maximumPath := maximumSlope.symm
    _ = (S * (1 - r)) * insectPath := by rw [← pathTurn]; ring1

/-- Problem 12, the three-dimensional Pythagoras theorem for quadrea.  The
three pairwise perpendicular leg quadrances are `P₁,P₂,P₃`; expanding
Archimedes' formula gives the sum of the three right-face quadreas. -/
theorem problem_12 (P₁ P₂ P₃ : K) :
    archimedesFunction (P₂ + P₃) (P₁ + P₃) (P₁ + P₂) =
      4 * P₂ * P₃ + 4 * P₁ * P₃ + 4 * P₁ * P₂ := by
  unfold archimedesFunction
  ring1

/-- The side-quadrance equations of a right tetrahedron. -/
def RightTetrahedronQuadrances
    (Q₁ Q₂ Q₃ P₁ P₂ P₃ : K) : Prop :=
  Q₁ = P₂ + P₃ ∧ Q₂ = P₁ + P₃ ∧ Q₃ = P₁ + P₂

/-- The three perpendicular-leg quadrances are uniquely recovered by finite
linear combinations of the face quadrances. -/
theorem rightTetrahedronQuadrances_recovered
    (Q₁ Q₂ Q₃ P₁ P₂ P₃ : K)
    (relations : RightTetrahedronQuadrances Q₁ Q₂ Q₃ P₁ P₂ P₃) :
    2 * P₁ = Q₂ + Q₃ - Q₁ ∧
      2 * P₂ = Q₁ + Q₃ - Q₂ ∧
      2 * P₃ = Q₁ + Q₂ - Q₃ := by
  rcases relations with ⟨r₁, r₂, r₃⟩
  rw [r₁, r₂, r₃]
  constructor
  · ring1
  constructor <;> ring1

/-- The first assertion of Exercise 22.3: positive perpendicular-leg
quadrances force the opposite face to satisfy all three acute inequalities. -/
theorem exercise_22_3_acute
    (Q₁ Q₂ Q₃ P₁ P₂ P₃ : Rational)
    (relations : RightTetrahedronQuadrances Q₁ Q₂ Q₃ P₁ P₂ P₃)
    (firstPositive : 0 < P₁) (secondPositive : 0 < P₂)
    (thirdPositive : 0 < P₃) :
    TriangleSpreadRules.AcuteQuadranceBounds Q₁ Q₂ Q₃ := by
  rcases relations with ⟨r₁, r₂, r₃⟩
  have firstNonnegative :=
    RFAP.ConstructiveFraction.le_of_lt_direct firstPositive
  have secondNonnegative :=
    RFAP.ConstructiveFraction.le_of_lt_direct secondPositive
  have thirdNonnegative :=
    RFAP.ConstructiveFraction.le_of_lt_direct thirdPositive
  unfold TriangleSpreadRules.AcuteQuadranceBounds
  rw [r₁, r₂, r₃]
  constructor
  · have doubledThird : (0 : Rational) ≤ P₃ + P₃ :=
      RFAP.ConstructiveFraction.add_le_add_direct
        thirdNonnegative thirdNonnegative
    calc
      P₁ + P₂ = 0 + (P₁ + P₂) := by ring1
      _ ≤ (P₃ + P₃) + (P₁ + P₂) :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          doubledThird (P₁ + P₂)
      _ = (P₂ + P₃) + (P₁ + P₃) := by ring1
  constructor
  · have doubledFirst : (0 : Rational) ≤ P₁ + P₁ :=
      RFAP.ConstructiveFraction.add_le_add_direct
        firstNonnegative firstNonnegative
    calc
      P₂ + P₃ = 0 + (P₂ + P₃) := by ring1
      _ ≤ (P₁ + P₁) + (P₂ + P₃) :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          doubledFirst (P₂ + P₃)
      _ = (P₁ + P₃) + (P₁ + P₂) := by ring1
  · have doubledSecond : (0 : Rational) ≤ P₂ + P₂ :=
      RFAP.ConstructiveFraction.add_le_add_direct
        secondNonnegative secondNonnegative
    calc
      P₁ + P₃ = 0 + (P₁ + P₃) := by ring1
      _ ≤ (P₂ + P₂) + (P₁ + P₃) :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          doubledSecond (P₁ + P₃)
      _ = (P₁ + P₂) + (P₂ + P₃) := by ring1

def IsSignedHeight (height candidate : K) : Prop :=
  candidate ^ 2 = height ^ 2

/-- Once the planar foot and a nonzero height-square witness have been
constructed, the only two possible normal coordinates are `h` and `-h`.
This is the finite algebraic content of the second assertion in Exercise
22.3; existence of the square-root witness remains explicit. -/
theorem exercise_22_3_two_completions [DecidableEq K]
    (height : K) (heightNonzero : height ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    IsSignedHeight height height ∧
      IsSignedHeight height (-height) ∧
      height ≠ -height ∧
      ∀ candidate : K,
        IsSignedHeight height candidate →
          candidate = height ∨ candidate = -height := by
  have signsDistinct : height ≠ -height := by
    intro signsEqual
    have productZero : (2 : K) * height = 0 := by
      calc
        2 * height = height + height := by ring1
        _ = -height + height := congrArg (fun value => value + height) signsEqual
        _ = 0 := by ring1
    exact (RFAP.ExplicitField.mul_ne_zero twoNonzero heightNonzero) productZero
  refine ⟨rfl, ?_, signsDistinct, ?_⟩
  · unfold IsSignedHeight
    ring1
  · intro candidate candidateSquare
    unfold IsSignedHeight at candidateSquare
    have productZero : (candidate - height) * (candidate + height) = 0 := by
      calc
        (candidate - height) * (candidate + height) =
            candidate ^ 2 - height ^ 2 := by ring1
        _ = 0 := by rw [candidateSquare]; ring1
    by_cases firstFactor : candidate - height = 0
    · left
      calc
        candidate = (candidate - height) + height := by ring1
        _ = height := by rw [firstFactor]; ring1
    · right
      have secondFactor : candidate + height = 0 := by
        by_cases secondZero : candidate + height = 0
        · exact secondZero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero firstFactor secondZero)
              productZero)
      calc
        candidate = (candidate + height) - height := by ring1
        _ = -height := by rw [secondFactor]; ring1

/-! ## Problem 13: the seven-sided pagoda -/

/-- The nonzero factor in the seventh spread polynomial. -/
def seventhSpreadFactor (spread : K) : K :=
  7 - 56 * spread + 112 * spread ^ 2 - 64 * spread ^ 3

/-- The source's exact `S₇(s)` expression. -/
def seventhSpreadValue (spread : K) : K :=
  spread * seventhSpreadFactor spread ^ 2

/-- The radial quadrance recovered by the Spread law from base-side
quadrance `2`, central spread `s`, and equal base-sector spread `r`. -/
def pagodaRadialQuadrance (centralSpread baseSectorSpread : K) : K :=
  2 * baseSectorSpread / centralSpread

def pagodaSlopingQuadrance (centralSpread baseSectorSpread : K) : K :=
  pagodaRadialQuadrance centralSpread baseSectorSpread + 1

/-- The equal base-sector spread in one triangular roof face. -/
def pagodaFaceBaseSpread (centralSpread baseSectorSpread : K) : K :=
  1 - 1 / (2 * pagodaSlopingQuadrance centralSpread baseSectorSpread)

/-- The vertex spread of one triangular roof face. -/
def pagodaFaceVertexSpread (centralSpread baseSectorSpread : K) : K :=
  4 * pagodaFaceBaseSpread centralSpread baseSectorSpread *
    (1 - pagodaFaceBaseSpread centralSpread baseSectorSpread)

/-- Problem 13's exact finite calculation.  The chosen roots `s` and `r`
remain explicit data, just as a square-root witness does elsewhere in the
formalization. -/
theorem problem_13
    (centralSpread baseSectorSpread : K)
    (centralSpreadNonzero : centralSpread ≠ 0)
    (slopingQuadranceNonzero :
      pagodaSlopingQuadrance centralSpread baseSectorSpread ≠ 0)
    (seventhFactor : seventhSpreadFactor centralSpread = 0)
    (baseIsosceles :
      centralSpread = 4 * baseSectorSpread * (1 - baseSectorSpread)) :
    seventhSpreadValue centralSpread = 0 ∧
      (2 * baseSectorSpread - 1) ^ 2 = 1 - centralSpread ∧
      pagodaRadialQuadrance centralSpread baseSectorSpread * centralSpread =
        2 * baseSectorSpread ∧
      pagodaSlopingQuadrance centralSpread baseSectorSpread =
        pagodaRadialQuadrance centralSpread baseSectorSpread + 1 ∧
      4 * pagodaSlopingQuadrance centralSpread baseSectorSpread *
          (1 - pagodaFaceBaseSpread centralSpread baseSectorSpread) = 2 ∧
      pagodaFaceVertexSpread centralSpread baseSectorSpread =
        4 * pagodaFaceBaseSpread centralSpread baseSectorSpread *
          (1 - pagodaFaceBaseSpread centralSpread baseSectorSpread) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    have fourZero : (4 : K) = 0 := by rw [show (4 : K) = 2 * 2 by ring1, twoZero]; ring1
    have baseZero : centralSpread = 0 := by
      calc
        centralSpread = 4 * baseSectorSpread * (1 - baseSectorSpread) :=
          baseIsosceles
        _ = 0 := by rw [fourZero]; ring1
    exact centralSpreadNonzero baseZero
  have denominatorNonzero :
      2 * pagodaSlopingQuadrance centralSpread baseSectorSpread ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero slopingQuadranceNonzero
  have denominatorCancel :=
    RFAP.ExplicitField.div_mul_cancel (1 : K) denominatorNonzero
  constructor
  · unfold seventhSpreadValue
    rw [seventhFactor]
    ring1
  constructor
  · rw [baseIsosceles]
    ring1
  constructor
  · unfold pagodaRadialQuadrance
    exact RFAP.ExplicitField.div_mul_cancel
      (2 * baseSectorSpread) centralSpreadNonzero
  constructor
  · rfl
  constructor
  · unfold pagodaFaceBaseSpread
    calc
      4 * pagodaSlopingQuadrance centralSpread baseSectorSpread *
          (1 - (1 - 1 /
            (2 * pagodaSlopingQuadrance centralSpread baseSectorSpread))) =
          2 * ((1 /
            (2 * pagodaSlopingQuadrance centralSpread baseSectorSpread)) *
              (2 * pagodaSlopingQuadrance centralSpread baseSectorSpread)) := by
                ring1
      _ = 2 := by rw [denominatorCancel]; ring1
  · rfl

/-- A denominator-free altitude to a shared edge.  Scaling by `L` avoids
introducing the projection quotient `D/L`. -/
def scaledFaceAltitude
    (shared other : Vector3 K) (L D : K) : Vector3 K :=
  add (scale L other) (neg (scale D shared))

/-- Gram calculation for the two scaled altitudes used to measure a
dihedral spread. -/
theorem scaledFaceAltitude_metrics
    (shared first second : Vector3 K) (L D E : K)
    (sharedQuadrance : Vector3.quadrance shared = L)
    (firstQuadrance : Vector3.quadrance first = L)
    (secondQuadrance : Vector3.quadrance second = L)
    (sharedFirst : Vector3.dot shared first = D)
    (sharedSecond : Vector3.dot shared second = D)
    (firstSecond : Vector3.dot first second = E) :
    Vector3.quadrance (scaledFaceAltitude shared first L D) =
        L * (L ^ 2 - D ^ 2) ∧
      Vector3.quadrance (scaledFaceAltitude shared second L D) =
        L * (L ^ 2 - D ^ 2) ∧
      Vector3.dot (scaledFaceAltitude shared first L D)
          (scaledFaceAltitude shared second L D) =
        L * (E * L - D ^ 2) := by
  have firstShared : Vector3.dot first shared = D := by
    rw [Vector3.dot_comm]
    exact sharedFirst
  have secondShared : Vector3.dot second shared = D := by
    rw [Vector3.dot_comm]
    exact sharedSecond
  change Vector3.dot shared shared = L at sharedQuadrance
  change Vector3.dot first first = L at firstQuadrance
  change Vector3.dot second second = L at secondQuadrance
  unfold scaledFaceAltitude Vector3.quadrance
  simp only [Vector3.dot_add_left, Vector3.dot_add_right,
    Vector3.dot_neg_left, Vector3.dot_neg_right,
    Vector3.dot_scale_left, Vector3.dot_scale_right]
  rw [sharedQuadrance, firstQuadrance, secondQuadrance,
    sharedFirst, sharedSecond, firstShared, secondShared, firstSecond]
  constructor
  · ring1
  constructor <;> ring1

/-- The exact adjacent-roof-plane spread as a finite Gram quotient. -/
def pagodaAdjacentPlaneSpread (radius baseSectorSpread : K) : K :=
  let L := radius + 1
  let gram := L ^ 2 - radius ^ 2
  let mixed := (radius + 1 - 4 * baseSectorSpread) * L - radius ^ 2
  ((L * gram) ^ 2 - (L * mixed) ^ 2) / (L * gram) ^ 2

/-- Exercise 22.4 before decimal evaluation.  The three vectors point from
the apex to three consecutive base vertices.  The hypotheses are their exact
Gram data; the scaled altitudes are perpendicular to the common roof edge,
so their direction spread is the spread between the adjacent planes. -/
theorem exercise_22_4_exact
    (shared first second : Vector3 K) (radius baseSectorSpread : K)
    (slopingNonzero : radius + 1 ≠ 0)
    (gramNonzero : (radius + 1) ^ 2 - radius ^ 2 ≠ 0)
    (sharedQuadrance : Vector3.quadrance shared = radius + 1)
    (firstQuadrance : Vector3.quadrance first = radius + 1)
    (secondQuadrance : Vector3.quadrance second = radius + 1)
    (sharedFirst : Vector3.dot shared first = radius)
    (sharedSecond : Vector3.dot shared second = radius)
    (firstSecond :
      Vector3.dot first second = radius + 1 - 4 * baseSectorSpread) :
    directionSpread
        (scaledFaceAltitude shared first (radius + 1) radius)
        (scaledFaceAltitude shared second (radius + 1) radius)
        (by
          rw [(scaledFaceAltitude_metrics shared first second
            (radius + 1) radius (radius + 1 - 4 * baseSectorSpread)
            sharedQuadrance firstQuadrance secondQuadrance sharedFirst
            sharedSecond firstSecond).1]
          exact RFAP.ExplicitField.mul_ne_zero slopingNonzero gramNonzero)
        (by
          rw [(scaledFaceAltitude_metrics shared first second
            (radius + 1) radius (radius + 1 - 4 * baseSectorSpread)
            sharedQuadrance firstQuadrance secondQuadrance sharedFirst
            sharedSecond firstSecond).2.1]
          exact RFAP.ExplicitField.mul_ne_zero slopingNonzero gramNonzero) =
      pagodaAdjacentPlaneSpread radius baseSectorSpread := by
  let metrics := scaledFaceAltitude_metrics shared first second
    (radius + 1) radius (radius + 1 - 4 * baseSectorSpread)
    sharedQuadrance firstQuadrance secondQuadrance sharedFirst sharedSecond
    firstSecond
  have metricNonzero :
      (radius + 1) * ((radius + 1) ^ 2 - radius ^ 2) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero slopingNonzero gramNonzero
  have formula := directionSpread_metric_formula
    (scaledFaceAltitude shared first (radius + 1) radius)
    (scaledFaceAltitude shared second (radius + 1) radius)
    ((radius + 1) * ((radius + 1) ^ 2 - radius ^ 2))
    ((radius + 1) *
      ((radius + 1 - 4 * baseSectorSpread) * (radius + 1) - radius ^ 2))
    metricNonzero metrics.1 metrics.2.1 metrics.2.2
  exact formula

/-- Integer numerator of the cubic factor at the rational label `n/d`.
Multiplication by `d³` preserves its sign when `d>0`. -/
def seventhSpreadFactorNumerator (numerator denominator : Int) : Int :=
  7 * denominator ^ 3 - 56 * numerator * denominator ^ 2 +
    112 * numerator ^ 2 * denominator - 64 * numerator ^ 3

/-- A finite isolating sign certificate for the central root printed as
`0.611260`.  No intermediate-value or completed-real theorem is asserted. -/
theorem problem_13_central_root_certificate :
    seventhSpreadFactorNumerator 611259 1000000 < 0 ∧
      0 < seventhSpreadFactorNumerator 611261 1000000 := by
  decide

/-- The remaining printed decimals in Problem 13 are certified as rational
interval arithmetic.  The fine label `0.811745` is the one actually used in
the source's radial-quadrance calculation. -/
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

/-- Common-denominator numerator and denominator for the adjacent-plane
spread computed from rational labels `qNum/qDen` and `rNum/rDen`. -/
def pagodaPlaneSpreadIntegerPair
    (qNumerator qDenominator rNumerator rDenominator : Int) : Int × Int :=
  let gramNumerator := (2 * qNumerator + qDenominator) * rDenominator
  let mixedNumerator :=
    gramNumerator - 4 * rNumerator * (qNumerator + qDenominator)
  (gramNumerator ^ 2 - mixedNumerator ^ 2, gramNumerator ^ 2)

/-- Exercise 22.4's `0.2244`: using the displayed `q≈2.6559` and
`r≈0.81175`, the exact rational spread lies strictly between `0.2243`
and `0.2245`. -/
theorem exercise_22_4_decimal_certificate :
    let pair := pagodaPlaneSpreadIntegerPair 26559 10000 81175 100000
    2243 * pair.2 < 10000 * pair.1 ∧
      10000 * pair.1 < 2245 * pair.2 := by
  decide

end ThreeDimensionalProblems
end DivineProportions
