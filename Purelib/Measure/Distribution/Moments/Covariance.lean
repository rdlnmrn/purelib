module
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Stability
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Algebra of finite rational covariance

Covariance on a displayed finite distribution is a rational bilinear form.
The usual translation, subtraction, polarization, and parallelogram laws are
therefore exact finite identities; no limiting argument or completed norm is
involved.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib.Data.Rat
/-- Take the expectation of the product of the two observables' deviations from their original means. -/
def covariance {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) : Fraction.Rational :=
  distribution.expectation fun item =>
    (left item - distribution.expectation left) *
      (right item - distribution.expectation right)

/-- The covariance of an observable with itself is its variance. -/
theorem covariance_self {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) :
    distribution.covariance value value = distribution.variance value := by
  unfold covariance variance varianceAround
  exact distribution.expectation_congr _ _ (fun item => by rw [pow_two])

/-- Exchanging the two observables preserves their covariance. -/
theorem covariance_symm {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
    distribution.covariance left right =
      distribution.covariance right left := by
  unfold covariance
  exact distribution.expectation_congr _ _ (fun item => by ring1)

/-- Covariance equals the product moment minus the product of the original means. -/
theorem covariance_eq_productMoment_sub_means {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
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

/-- The variance of a sum is the sum of variances plus twice the original covariance. -/
theorem variance_add {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
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

/-- Scaling the left observable scales covariance by the same rational factor. -/
theorem covariance_scale_left {α : Type}
    (distribution : Distribution α) (factor : Fraction.Rational)
    (left right : α → Fraction.Rational) :
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

/-- Scaling the right observable scales covariance by the same rational factor. -/
theorem covariance_scale_right {α : Type}
    (distribution : Distribution α) (factor : Fraction.Rational)
    (left right : α → Fraction.Rational) :
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

/-- Variance of a linear combination expands into the two scaled variances and the covariance cross term. -/
theorem variance_linearCombination {α : Type}
    (distribution : Distribution α)
    (leftFactor rightFactor : Fraction.Rational)
    (left right : α → Fraction.Rational) :
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

/-- Squared covariance is bounded by the product of the two variances.

The finite rational proof treats vanishing variances separately and otherwise uses nonnegativity of the exact scalar
linear-combination variance; no square roots are introduced. -/
theorem covariance_sq_le_variance_mul {α : Type}
    (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
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
        apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
          (c := (2 : Fraction.Rational))
        · simpa only [zero_mul, mul_comm] using doubledNonnegative
        · decide
      have mixedNonpositive : mixed ≤ 0 := by
        apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
          (c := (2 : Fraction.Rational))
        · have doubledNonpositive : 2 * mixed ≤ 0 := by
            exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
              minusNonnegative
          simpa only [zero_mul, mul_comm] using doubledNonpositive
        · decide
      have mixedZero : mixed = 0 :=
        Fraction.Order.Basic.Compatibility.le_antisymm _ _
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
        apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
          (c := leftVariance)
        · simpa only [zero_mul] using combinationNonnegative
        · exact leftPositive
      change mixed ^ 2 ≤ leftVariance * rightVariance
      exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
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
      apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        (c := rightVariance)
      · simpa only [zero_mul] using combinationNonnegative
      · exact rightPositive
    change mixed ^ 2 ≤ leftVariance * rightVariance
    exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      differenceNonnegative

/-- Covariance is additive in the left observable. -/
theorem covariance_add_left {α : Type}
    (distribution : Distribution α)
    (left middle right : α → Fraction.Rational) :
    distribution.covariance (fun item => left item + middle item) right =
      distribution.covariance left right +
        distribution.covariance middle right := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    distribution.covariance_eq_productMoment_sub_means,
    distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_add]
  have productExpectation :
      distribution.expectation
          (fun item => (left item + middle item) * right item) =
        distribution.expectation
          (fun item => left item * right item + middle item * right item) :=
    distribution.expectation_congr _ _ (fun item => by ring1)
  rw [productExpectation, distribution.expectation_add]
  ring1

/-- Covariance is additive in the right observable. -/
theorem covariance_add_right {α : Type}
    (distribution : Distribution α)
    (left right final : α → Fraction.Rational) :
    distribution.covariance left (fun item => right item + final item) =
      distribution.covariance left right +
        distribution.covariance left final := by
  calc
    distribution.covariance left (fun item => right item + final item) =
        distribution.covariance (fun item => right item + final item) left :=
      distribution.covariance_symm _ _
    _ = distribution.covariance right left +
          distribution.covariance final left :=
      distribution.covariance_add_left right final left
    _ = distribution.covariance left right +
          distribution.covariance left final := by
      rw [distribution.covariance_symm right left,
        distribution.covariance_symm final left]

/-- Covariance preserves subtraction in the left observable. -/
theorem covariance_sub_left {α : Type}
    (distribution : Distribution α)
    (left middle right : α → Fraction.Rational) :
    distribution.covariance (fun item => left item - middle item) right =
      distribution.covariance left right -
        distribution.covariance middle right := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    distribution.covariance_eq_productMoment_sub_means,
    distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_sub]
  have productExpectation :
      distribution.expectation
          (fun item => (left item - middle item) * right item) =
        distribution.expectation
          (fun item => left item * right item - middle item * right item) :=
    distribution.expectation_congr _ _ (fun item => by ring1)
  rw [productExpectation, distribution.expectation_sub]
  ring1

/-- Covariance preserves subtraction in the right observable. -/
theorem covariance_sub_right {α : Type}
    (distribution : Distribution α)
    (left right final : α → Fraction.Rational) :
    distribution.covariance left (fun item => right item - final item) =
      distribution.covariance left right -
        distribution.covariance left final := by
  calc
    distribution.covariance left (fun item => right item - final item) =
        distribution.covariance (fun item => right item - final item) left :=
      distribution.covariance_symm _ _
    _ = distribution.covariance right left -
          distribution.covariance final left :=
      distribution.covariance_sub_left right final left
    _ = distribution.covariance left right -
          distribution.covariance left final := by
      rw [distribution.covariance_symm right left,
        distribution.covariance_symm final left]

/-- The covariance of a constant left observable with any right observable vanishes. -/
theorem covariance_constant_left {α : Type}
    (distribution : Distribution α) (constant : Fraction.Rational)
    (value : α → Fraction.Rational) :
    distribution.covariance (fun _ => constant) value = 0 := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_constant]
  have productPointwise :
      (fun item => constant * value item) =
        (fun item => constant * value item) := rfl
  rw [productPointwise, distribution.expectation_scale]
  ring1

/-- The covariance of any left observable with a constant right observable vanishes. -/
theorem covariance_constant_right {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational)
    (constant : Fraction.Rational) :
    distribution.covariance value (fun _ => constant) = 0 := by
  rw [distribution.covariance_symm]
  exact distribution.covariance_constant_left constant value

/-- Adding a constant to the left observable preserves covariance. -/
theorem covariance_add_constant_left {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational)
    (constant : Fraction.Rational) :
    distribution.covariance (fun item => left item + constant) right =
      distribution.covariance left right := by
  rw [distribution.covariance_add_left left (fun _ => constant) right,
    distribution.covariance_constant_left, add_zero]

/-- Adding a constant to the right observable preserves covariance. -/
theorem covariance_add_constant_right {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational)
    (constant : Fraction.Rational) :
    distribution.covariance left (fun item => right item + constant) =
      distribution.covariance left right := by
  rw [distribution.covariance_add_right left right (fun _ => constant),
    distribution.covariance_constant_right, add_zero]

/-- The variance of a difference is the sum of variances minus twice the original covariance. -/
theorem variance_sub {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
    distribution.variance (fun item => left item - right item) =
      distribution.variance left + distribution.variance right -
        2 * distribution.covariance left right := by
  have formula := distribution.variance_linearCombination
    1 (-1) left right
  calc
    distribution.variance (fun item => left item - right item) =
        distribution.variance
          (fun item => 1 * left item + -1 * right item) :=
      distribution.variance_congr _ _ (fun item => by ring1)
    _ =
        1 ^ 2 * distribution.variance left +
          (-1) ^ 2 * distribution.variance right +
          2 * 1 * (-1) * distribution.covariance left right := formula
    _ = distribution.variance left + distribution.variance right -
          2 * distribution.covariance left right := by ring1

/-- Twice covariance equals the variance of the sum minus the two original variances. -/
theorem two_mul_covariance_eq_variance_add_sub {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    2 * distribution.covariance left right =
      distribution.variance (fun item => left item + right item) -
        distribution.variance left - distribution.variance right := by
  rw [distribution.variance_add]
  ring1

/-- The variances of the sum and difference total twice the sum of the original variances. -/
theorem variance_parallelogram {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.variance (fun item => left item + right item) +
        distribution.variance (fun item => left item - right item) =
      2 * distribution.variance left + 2 * distribution.variance right := by
  rw [distribution.variance_add, distribution.variance_sub]
  ring1

/-- Twice covariance is at most the sum of the original variances. -/
theorem two_mul_covariance_le_variance_add {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    2 * distribution.covariance left right ≤
      distribution.variance left + distribution.variance right := by
  have nonnegative := distribution.variance_nonneg
    (fun item => left item - right item)
  rw [distribution.variance_sub] at nonnegative
  exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct nonnegative

/-- The negative sum of the original variances is at most twice covariance. -/
theorem neg_variance_add_le_two_mul_covariance {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    -(distribution.variance left + distribution.variance right) ≤
      2 * distribution.covariance left right := by
  have nonnegative := distribution.variance_nonneg
    (fun item => left item + right item)
  rw [distribution.variance_add] at nonnegative
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    2 * distribution.covariance left right -
          -(distribution.variance left + distribution.variance right) =
        distribution.variance left + distribution.variance right +
          2 * distribution.covariance left right := by ring1
    _ ≥ 0 := nonnegative

end

end Distribution

end Purelib.Measure
