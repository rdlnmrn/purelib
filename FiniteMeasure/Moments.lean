import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Stability

/-!
# Finite rational moment identities

Variance and covariance are exact rational weighted sums on displayed finite
distributions.  Their algebraic identities need only finite linearity and
direct polynomial calculations.
-/

namespace FiniteMeasure

namespace Distribution

/-- Finite variance is second moment minus the square of the exact rational
mean. -/
theorem variance_eq_secondMoment_sub_sq {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.variance value =
      distribution.expectation (fun item => value item ^ 2) -
        distribution.expectation value ^ 2 := by
  unfold variance varianceAround
  calc
    distribution.expectation (fun item =>
        (value item - distribution.expectation value) ^ 2) =
        distribution.expectation (fun item =>
          (value item ^ 2 -
            (2 * distribution.expectation value) * value item) +
            distribution.expectation value ^ 2) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item => value item ^ 2) -
          distribution.expectation value ^ 2 := by
      rw [distribution.expectation_add,
        distribution.expectation_sub, distribution.expectation_scale,
        distribution.expectation_constant]
      ring1

/-- Exact Bernoulli variance of a finite event indicator. -/
theorem variance_indicator {α : Type}
    (distribution : Distribution α) (event : α → Bool) :
    distribution.variance (indicator event) =
      distribution.probability event *
        (1 - distribution.probability event) := by
  rw [distribution.variance_eq_secondMoment_sub_sq,
    distribution.expectation_indicator]
  have indicatorSquare : distribution.expectation
        (fun item => indicator event item ^ 2) =
      distribution.expectation (indicator event) :=
    distribution.expectation_congr _ _ (fun item => by
      cases selected : event item <;>
        simp only [indicator, selected] <;> ring1)
  rw [indicatorSquare, distribution.expectation_indicator]
  ring1

/-- Every finite Boolean event indicator has variance at most `1/4`. -/
theorem variance_indicator_le_quarter {α : Type}
    (distribution : Distribution α) (event : α → Bool) :
    distribution.variance (indicator event) ≤ 1 / 4 := by
  rw [distribution.variance_indicator]
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ (distribution.probability event - 1 / 2) ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct _
    _ = (1 / 2) ^ 2 - distribution.probability event *
        (2 * (1 / 2) - distribution.probability event) := by ring1
    _ = (1 / 2) ^ 2 - distribution.probability event *
        (1 - distribution.probability event) := by
      rw [show (2 : Coordinate) * (1 / 2) = 1 by decide]
    _ = 1 / 4 - distribution.probability event *
        (1 - distribution.probability event) := by
      rw [show ((1 / 2 : Coordinate) ^ 2) = 1 / 4 by decide]

/-- Every displayed constant observable has zero finite variance. -/
theorem variance_constant {α : Type}
    (distribution : Distribution α) (constant : Coordinate) :
    distribution.variance (fun _ => constant) = 0 := by
  rw [distribution.variance_eq_secondMoment_sub_sq,
    distribution.expectation_constant, distribution.expectation_constant]
  ring1

/-- Square of the exact rational mean is at most the finite second moment. -/
theorem expectation_sq_le_secondMoment {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.expectation value ^ 2 ≤
      distribution.expectation (fun item => value item ^ 2) := by
  have nonnegative := distribution.variance_nonneg value
  rw [distribution.variance_eq_secondMoment_sub_sq] at nonnegative
  exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct nonnegative

/-- Exact least-squares decomposition around an arbitrary displayed rational
center. -/
theorem varianceAround_eq_variance_add_mean_sub_sq {α : Type}
    (distribution : Distribution α) (value : α → Coordinate)
    (center : Coordinate) :
    distribution.varianceAround value center =
      distribution.variance value +
        (distribution.expectation value - center) ^ 2 := by
  rw [distribution.variance_eq_secondMoment_sub_sq]
  unfold varianceAround
  calc
    distribution.expectation (fun item => (value item - center) ^ 2) =
        distribution.expectation (fun item =>
          value item ^ 2 - (2 * center) * value item + center ^ 2) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item => value item ^ 2) -
          distribution.expectation value ^ 2 +
            (distribution.expectation value - center) ^ 2 := by
      rw [distribution.expectation_add,
        distribution.expectation_sub, distribution.expectation_scale,
        distribution.expectation_constant]
      ring1

/-- The exact rational expectation is a least-squares center for every
displayed finite distribution. -/
theorem variance_le_varianceAround {α : Type}
    (distribution : Distribution α) (value : α → Coordinate)
    (center : Coordinate) :
    distribution.variance value ≤
      distribution.varianceAround value center := by
  rw [distribution.varianceAround_eq_variance_add_mean_sub_sq]
  calc
    distribution.variance value = distribution.variance value + 0 := by
      ring1
    _ ≤ distribution.variance value +
        (distribution.expectation value - center) ^ 2 :=
      RFAP.ConstructiveFraction.add_le_add_direct le_rfl
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)

/-- The exact rational expectation is the unique least-squares center:
equality with the minimum variance occurs exactly at that center. -/
theorem varianceAround_eq_variance_iff_center_eq_expectation {α : Type}
    (distribution : Distribution α) (value : α → Coordinate)
    (center : Coordinate) :
    distribution.varianceAround value center = distribution.variance value ↔
      center = distribution.expectation value := by
  constructor
  · intro equality
    rw [distribution.varianceAround_eq_variance_add_mean_sub_sq]
      at equality
    have squareZero :
        (distribution.expectation value - center) ^ 2 = 0 := by
      apply add_left_cancel (a := distribution.variance value)
      simpa only [add_zero] using equality
    have differenceZero : distribution.expectation value - center = 0 :=
      (RFAP.ConstructiveFraction.sq_eq_zero_direct _).mp squareZero
    exact (sub_eq_zero.mp differenceZero).symm
  · intro centerEqual
    rw [distribution.varianceAround_eq_variance_add_mean_sub_sq,
      centerEqual, sub_self]
    ring1

/-- Variance is at most the raw second moment. -/
theorem variance_le_secondMoment {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.variance value ≤
      distribution.expectation (fun item => value item ^ 2) := by
  rw [distribution.variance_eq_secondMoment_sub_sq]
  have meanSquareNonnegative :=
    RFAP.ConstructiveFraction.sq_nonneg_direct
      (distribution.expectation value)
  have negativeMeanSquareNonpositive :
      -(distribution.expectation value ^ 2) ≤ 0 := by
    simpa only [neg_zero] using
      RFAP.ConstructiveFraction.neg_le_neg_direct meanSquareNonnegative
  calc
    distribution.expectation (fun item => value item ^ 2) -
          distribution.expectation value ^ 2 ≤
        distribution.expectation (fun item => value item ^ 2) + 0 := by
      change distribution.expectation (fun item => value item ^ 2) +
          -(distribution.expectation value ^ 2) ≤
        distribution.expectation (fun item => value item ^ 2) + 0
      exact RFAP.ConstructiveFraction.add_le_add_direct le_rfl
        negativeMeanSquareNonpositive
    _ = distribution.expectation (fun item => value item ^ 2) := by ring1

/-- Translating every displayed value by a rational constant preserves
variance exactly. -/
theorem variance_add_constant {α : Type}
    (distribution : Distribution α) (value : α → Coordinate)
    (constant : Coordinate) :
    distribution.variance (fun item => value item + constant) =
      distribution.variance value := by
  have mean :
      distribution.expectation (fun item => value item + constant) =
        distribution.expectation value + constant := by
    rw [distribution.expectation_add,
      distribution.expectation_constant]
  unfold variance varianceAround
  rw [mean]
  exact distribution.expectation_congr _ _ (fun item => by ring1)

/-- Rational scaling squares the variance scale. -/
theorem variance_scale {α : Type}
    (distribution : Distribution α) (factor : Coordinate)
    (value : α → Coordinate) :
    distribution.variance (fun item => factor * value item) =
      factor ^ 2 * distribution.variance value := by
  have mean :
      distribution.expectation (fun item => factor * value item) =
        factor * distribution.expectation value :=
    distribution.expectation_scale factor value
  unfold variance varianceAround
  rw [mean]
  calc
    distribution.expectation (fun item =>
        (factor * value item - factor * distribution.expectation value) ^ 2) =
        distribution.expectation (fun item => factor ^ 2 *
          (value item - distribution.expectation value) ^ 2) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = factor ^ 2 * distribution.expectation (fun item =>
          (value item - distribution.expectation value) ^ 2) :=
      distribution.expectation_scale _ _

/-- Exact finite rational covariance. -/
def covariance {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) : Coordinate :=
  distribution.expectation fun item =>
    (left item - distribution.expectation left) *
      (right item - distribution.expectation right)

theorem covariance_self {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
    distribution.covariance value value = distribution.variance value := by
  unfold covariance variance varianceAround
  exact distribution.expectation_congr _ _ (fun item => by rw [pow_two])

theorem covariance_symm {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
    distribution.covariance left right =
      distribution.covariance right left := by
  unfold covariance
  exact distribution.expectation_congr _ _ (fun item => by ring1)

/-- Covariance is mixed second moment minus the product of rational means. -/
theorem covariance_eq_productMoment_sub_means {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.covariance left right =
      distribution.expectation (fun item => left item * right item) -
        distribution.expectation left * distribution.expectation right := by
  unfold covariance
  calc
    distribution.expectation (fun item =>
        (left item - distribution.expectation left) *
          (right item - distribution.expectation right)) =
        distribution.expectation (fun item =>
          ((left item * right item -
              distribution.expectation left * right item) -
            distribution.expectation right * left item) +
              distribution.expectation left *
                distribution.expectation right) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item => left item * right item) -
          distribution.expectation left * distribution.expectation right := by
      rw [distribution.expectation_add,
        distribution.expectation_sub, distribution.expectation_sub,
        distribution.expectation_scale, distribution.expectation_scale,
        distribution.expectation_constant]
      ring1

/-- Exact variance formula for the pointwise sum of two displayed rational
observables. -/
theorem variance_add {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
    distribution.variance (fun item => left item + right item) =
      distribution.variance left + distribution.variance right +
        2 * distribution.covariance left right := by
  rw [distribution.variance_eq_secondMoment_sub_sq,
    distribution.variance_eq_secondMoment_sub_sq,
    distribution.variance_eq_secondMoment_sub_sq,
    distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_add]
  have squareExpansion : distribution.expectation
        (fun item => (left item + right item) ^ 2) =
      distribution.expectation (fun item =>
        (left item ^ 2 + right item ^ 2) +
          2 * (left item * right item)) :=
    distribution.expectation_congr _ _ (fun item => by ring1)
  rw [squareExpansion, distribution.expectation_add,
    distribution.expectation_add, distribution.expectation_scale]
  ring1

/-- Covariance is homogeneous in its left observable. -/
theorem covariance_scale_left {α : Type}
    (distribution : Distribution α) (factor : Coordinate)
    (left right : α → Coordinate) :
    distribution.covariance (fun item => factor * left item) right =
      factor * distribution.covariance left right := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_scale]
  have productPointwise : distribution.expectation
        (fun item => (factor * left item) * right item) =
      distribution.expectation
        (fun item => factor * (left item * right item)) :=
    distribution.expectation_congr _ _ (fun item => by ring1)
  rw [productPointwise, distribution.expectation_scale]
  ring1

/-- Covariance is homogeneous in its right observable. -/
theorem covariance_scale_right {α : Type}
    (distribution : Distribution α) (factor : Coordinate)
    (left right : α → Coordinate) :
    distribution.covariance left (fun item => factor * right item) =
      factor * distribution.covariance left right := by
  calc
    distribution.covariance left (fun item => factor * right item) =
        distribution.covariance (fun item => factor * right item) left :=
      distribution.covariance_symm _ _
    _ = factor * distribution.covariance right left :=
      distribution.covariance_scale_left factor right left
    _ = factor * distribution.covariance left right := by
      rw [distribution.covariance_symm right left]

/-- Exact variance of a rational linear combination of two finite
observables. -/
theorem variance_linearCombination {α : Type}
    (distribution : Distribution α)
    (leftFactor rightFactor : Coordinate)
    (left right : α → Coordinate) :
    distribution.variance (fun item =>
        leftFactor * left item + rightFactor * right item) =
      leftFactor ^ 2 * distribution.variance left +
        rightFactor ^ 2 * distribution.variance right +
        2 * leftFactor * rightFactor *
          distribution.covariance left right := by
  rw [distribution.variance_add,
    distribution.variance_scale, distribution.variance_scale,
    distribution.covariance_scale_left,
    distribution.covariance_scale_right]
  ring1

/-- Finite rational Cauchy--Schwarz inequality for covariance.  The proof
uses nonnegativity of displayed linear-combination variances and handles
zero variances by explicit rational case splits. -/
theorem covariance_sq_le_variance_mul {α : Type}
    (distribution : Distribution α)
    (left right : α → Coordinate) :
    distribution.covariance left right ^ 2 ≤
      distribution.variance left * distribution.variance right := by
  let leftVariance := distribution.variance left
  let rightVariance := distribution.variance right
  let mixed := distribution.covariance left right
  have leftNonnegative : 0 ≤ leftVariance :=
    distribution.variance_nonneg left
  have rightNonnegative : 0 ≤ rightVariance :=
    distribution.variance_nonneg right
  by_cases rightZero : rightVariance = 0
  · by_cases leftZero : leftVariance = 0
    · have plusNonnegative := distribution.variance_nonneg
          (fun item => left item + right item)
      have minusNonnegative := distribution.variance_nonneg
          (fun item => left item - right item)
      have plusFormula :
          distribution.variance (fun item => left item + right item) =
            leftVariance + rightVariance + 2 * mixed := by
        simpa only [leftVariance, rightVariance, mixed] using
          distribution.variance_add left right
      have minusFormula :
          distribution.variance (fun item => left item - right item) =
            leftVariance + rightVariance - 2 * mixed := by
        have formula := distribution.variance_linearCombination
          1 (-1) left right
        change distribution.variance
            (fun item => 1 * left item + -1 * right item) = _ at formula
        calc
          distribution.variance (fun item => left item - right item) =
              distribution.variance (fun item =>
                1 * left item + -1 * right item) :=
            distribution.variance_congr _ _ (fun item => by ring1)
          _ =
              1 ^ 2 * distribution.variance left +
                (-1) ^ 2 * distribution.variance right +
                2 * 1 * (-1) * distribution.covariance left right := formula
          _ = leftVariance + rightVariance - 2 * mixed := by
            dsimp only [leftVariance, rightVariance, mixed]
            ring1
      rw [plusFormula, leftZero, rightZero] at plusNonnegative
      rw [minusFormula, leftZero, rightZero] at minusNonnegative
      have mixedNonnegative : 0 ≤ mixed := by
        have doubledNonnegative : 0 ≤ 2 * mixed := by
          simpa only [zero_add] using plusNonnegative
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := (2 : Coordinate))
        · simpa only [zero_mul, mul_comm] using doubledNonnegative
        · decide
      have mixedNonpositive : mixed ≤ 0 := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := (2 : Coordinate))
        · have doubledNonpositive : 2 * mixed ≤ 0 := by
            exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
              minusNonnegative
          simpa only [zero_mul, mul_comm] using doubledNonpositive
        · decide
      have mixedZero : mixed = 0 :=
        RFAP.ConstructiveFraction.le_antisymm _ _
          mixedNonpositive mixedNonnegative
      change mixed ^ 2 ≤ leftVariance * rightVariance
      rw [mixedZero, leftZero, rightZero]
      exact le_rfl
    · have leftPositive : 0 < leftVariance :=
        lt_of_le_of_ne leftNonnegative (Ne.symm leftZero)
      have combinationNonnegative := distribution.variance_nonneg
        (fun item =>
          leftVariance * right item - mixed * left item)
      have formula := distribution.variance_linearCombination
        leftVariance (-mixed) right left
      have differenceFormula : distribution.variance (fun item =>
            leftVariance * right item - mixed * left item) =
          leftVariance ^ 2 * distribution.variance right +
            (-mixed) ^ 2 * distribution.variance left +
            2 * leftVariance * (-mixed) *
              distribution.covariance right left := by
        calc
          distribution.variance (fun item =>
              leftVariance * right item - mixed * left item) =
              distribution.variance (fun item =>
                leftVariance * right item + -mixed * left item) :=
            distribution.variance_congr _ _ (fun item => by ring1)
          _ = _ := formula
      rw [differenceFormula] at combinationNonnegative
      rw [distribution.covariance_symm right left] at combinationNonnegative
      change 0 ≤
        leftVariance ^ 2 * rightVariance +
          (-mixed) ^ 2 * leftVariance +
          2 * leftVariance * (-mixed) * mixed at combinationNonnegative
      have factored :
          leftVariance ^ 2 * rightVariance +
                (-mixed) ^ 2 * leftVariance +
                2 * leftVariance * (-mixed) * mixed =
            (leftVariance * rightVariance - mixed ^ 2) *
              leftVariance := by
        ring1
      rw [factored] at combinationNonnegative
      have differenceNonnegative :
          0 ≤ leftVariance * rightVariance - mixed ^ 2 := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := leftVariance)
        · simpa only [zero_mul] using combinationNonnegative
        · exact leftPositive
      change mixed ^ 2 ≤ leftVariance * rightVariance
      exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        differenceNonnegative
  · have rightPositive : 0 < rightVariance :=
      lt_of_le_of_ne rightNonnegative (Ne.symm rightZero)
    have combinationNonnegative := distribution.variance_nonneg
      (fun item =>
        rightVariance * left item - mixed * right item)
    have formula := distribution.variance_linearCombination
      rightVariance (-mixed) left right
    have differenceFormula : distribution.variance (fun item =>
          rightVariance * left item - mixed * right item) =
        rightVariance ^ 2 * distribution.variance left +
          (-mixed) ^ 2 * distribution.variance right +
          2 * rightVariance * (-mixed) *
            distribution.covariance left right := by
      calc
        distribution.variance (fun item =>
            rightVariance * left item - mixed * right item) =
            distribution.variance (fun item =>
              rightVariance * left item + -mixed * right item) :=
          distribution.variance_congr _ _ (fun item => by ring1)
        _ = _ := formula
    rw [differenceFormula] at combinationNonnegative
    change 0 ≤
      rightVariance ^ 2 * leftVariance +
        (-mixed) ^ 2 * rightVariance +
        2 * rightVariance * (-mixed) * mixed at combinationNonnegative
    have factored :
        rightVariance ^ 2 * leftVariance +
              (-mixed) ^ 2 * rightVariance +
              2 * rightVariance * (-mixed) * mixed =
          (leftVariance * rightVariance - mixed ^ 2) *
            rightVariance := by
      ring1
    rw [factored] at combinationNonnegative
    have differenceNonnegative :
        0 ≤ leftVariance * rightVariance - mixed ^ 2 := by
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        (c := rightVariance)
      · simpa only [zero_mul] using combinationNonnegative
      · exact rightPositive
    change mixed ^ 2 ≤ leftVariance * rightVariance
    exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      differenceNonnegative

end Distribution

end FiniteMeasure
