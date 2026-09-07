import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Moments

/-!
# Algebra of finite rational covariance

Covariance on a displayed finite distribution is a rational bilinear form.
The usual translation, subtraction, polarization, and parallelogram laws are
therefore exact finite identities; no limiting argument or completed norm is
involved.
-/

namespace FiniteMeasure

namespace Distribution

/-- Covariance is additive in its left observable. -/
theorem covariance_add_left {α : Type}
    (distribution : Distribution α)
    (left middle right : α → Coordinate) :
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

/-- Covariance is additive in its right observable. -/
theorem covariance_add_right {α : Type}
    (distribution : Distribution α)
    (left right final : α → Coordinate) :
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

/-- Covariance distributes over subtraction in its left observable. -/
theorem covariance_sub_left {α : Type}
    (distribution : Distribution α)
    (left middle right : α → Coordinate) :
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

/-- Covariance distributes over subtraction in its right observable. -/
theorem covariance_sub_right {α : Type}
    (distribution : Distribution α)
    (left right final : α → Coordinate) :
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

/-- A constant left observable has zero covariance. -/
theorem covariance_constant_left {α : Type}
    (distribution : Distribution α) (constant : Coordinate)
    (value : α → Coordinate) :
    distribution.covariance (fun _ => constant) value = 0 := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_constant]
  have productPointwise :
      (fun item => constant * value item) =
        (fun item => constant * value item) := rfl
  rw [productPointwise, distribution.expectation_scale]
  ring1

/-- A constant right observable has zero covariance. -/
theorem covariance_constant_right {α : Type}
    (distribution : Distribution α) (value : α → Coordinate)
    (constant : Coordinate) :
    distribution.covariance value (fun _ => constant) = 0 := by
  rw [distribution.covariance_symm]
  exact distribution.covariance_constant_left constant value

/-- Translating the left observable preserves covariance. -/
theorem covariance_add_constant_left {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
    (constant : Coordinate) :
    distribution.covariance (fun item => left item + constant) right =
      distribution.covariance left right := by
  rw [distribution.covariance_add_left left (fun _ => constant) right,
    distribution.covariance_constant_left, add_zero]

/-- Translating the right observable preserves covariance. -/
theorem covariance_add_constant_right {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
    (constant : Coordinate) :
    distribution.covariance left (fun item => right item + constant) =
      distribution.covariance left right := by
  rw [distribution.covariance_add_right left right (fun _ => constant),
    distribution.covariance_constant_right, add_zero]

/-- Exact variance formula for a pointwise difference. -/
theorem variance_sub {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
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

/-- Covariance recovered by the exact variance polarization identity. -/
theorem two_mul_covariance_eq_variance_add_sub {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    2 * distribution.covariance left right =
      distribution.variance (fun item => left item + right item) -
        distribution.variance left - distribution.variance right := by
  rw [distribution.variance_add]
  ring1

/-- Exact parallelogram identity for centered finite rational observables. -/
theorem variance_parallelogram {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.variance (fun item => left item + right item) +
        distribution.variance (fun item => left item - right item) =
      2 * distribution.variance left + 2 * distribution.variance right := by
  rw [distribution.variance_add, distribution.variance_sub]
  ring1

/-- Twice the covariance is bounded above by the sum of the two variances. -/
theorem two_mul_covariance_le_variance_add {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    2 * distribution.covariance left right ≤
      distribution.variance left + distribution.variance right := by
  have nonnegative := distribution.variance_nonneg
    (fun item => left item - right item)
  rw [distribution.variance_sub] at nonnegative
  exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct nonnegative

/-- The negative sum of the variances is a lower bound for twice the
covariance. -/
theorem neg_variance_add_le_two_mul_covariance {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    -(distribution.variance left + distribution.variance right) ≤
      2 * distribution.covariance left right := by
  have nonnegative := distribution.variance_nonneg
    (fun item => left item + right item)
  rw [distribution.variance_add] at nonnegative
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    2 * distribution.covariance left right -
          -(distribution.variance left + distribution.variance right) =
        distribution.variance left + distribution.variance right +
          2 * distribution.covariance left right := by ring1
    _ ≥ 0 := nonnegative

end Distribution

end FiniteMeasure
