module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Circles.Projective.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, §16.3: the projective circle

The projective circle is stored by its denominator-free equation
`x² + y² - y = 0`.  Its rational parametrization is executable for every
requested field element; the theorem carries the exact finite certificate
`λ² ≠ -1` needed to cancel its denominator.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Rational coordinate formula for the circle `x² + y² - y = 0`.

The parameter gives coordinates `[t/(1+t²), 1/(1+t²)]`; incidence is certified separately when the denominator is
nonzero. -/
def projectiveCirclePoint (parameter : K) : Plane.Point K :=
  ⟨parameter / (1 + parameter ^ 2), 1 / (1 + parameter ^ 2)⟩

/-- Forward half of Theorem 107: every admissible parameter produces a point on the projective circle. -/
theorem projectiveCirclePoint_contains [Nontrivial K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    Conic.projectiveCircle.Contains (projectiveCirclePoint parameter) := by
  let denominator := 1 + parameter ^ 2
  have denominatorNonzero : denominator ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter).2
      squareNotNegativeOne
  have parameterCancel : (parameter / denominator) * denominator = parameter :=
    ExplicitField.div_mul_cancel parameter denominatorNonzero
  have oneCancel : (1 / denominator) * denominator = 1 :=
    ExplicitField.div_mul_cancel 1 denominatorNonzero
  have denominatorSquareNonzero : denominator * denominator ≠ 0 :=
    ExplicitField.mul_ne_zero denominatorNonzero denominatorNonzero
  apply (Conic.projectiveCircle_contains_iff
    (projectiveCirclePoint parameter)).2
  change (parameter / denominator) ^ 2 + (1 / denominator) ^ 2 -
      1 / denominator = 0
  let equation := (parameter / denominator) ^ 2 +
    (1 / denominator) ^ 2 - 1 / denominator
  have scaledEquation : equation * (denominator * denominator) = 0 := by
    calc
      equation * (denominator * denominator) =
          ((parameter / denominator) * denominator) ^ 2 +
            ((1 / denominator) * denominator) ^ 2 -
            ((1 / denominator) * denominator) * denominator := by
        unfold equation
        ring1
      _ = parameter ^ 2 + 1 - denominator := by
        rw [parameterCancel, oneCancel]
        ring1
      _ = 0 := by unfold denominator; ring1
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorSquareNonzero
  calc
    equation * (denominator * denominator) = 0 := scaledEquation
    _ = 0 * (denominator * denominator) := by ring1

/-- Every non-origin projective-circle point has an admissible parameter.

The witness is the explicit quotient `x/y`, whose denominator is shown nonzero from incidence and exclusion of the
origin. -/
theorem projectiveCirclePoint_exists [Nontrivial K] [DecidableEq K]
    (point : Plane.Point K) (pointOnCircle : Conic.projectiveCircle.Contains point)
    (pointNotOrigin : point ≠ (⟨0, 0⟩ : Plane.Point K)) :
    ∃ parameter : K,
      parameter ^ 2 ≠ -1 ∧ point = projectiveCirclePoint parameter := by
  have circleEquation : point.x ^ 2 + point.y ^ 2 - point.y = 0 :=
    (Conic.projectiveCircle_contains_iff point).1 pointOnCircle
  have yNonzero : point.y ≠ 0 := by
    intro yZero
    have xSquareZero : point.x ^ 2 = 0 := by
      calc
        point.x ^ 2 = point.x ^ 2 + point.y ^ 2 - point.y := by
          rw [yZero]
          ring1
        _ = 0 := circleEquation
    have xZero : point.x = 0 := by
      by_cases xZero : point.x = 0
      · exact xZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero xZero xZero)
            (by simpa [pow_two] using xSquareZero))
    apply pointNotOrigin
    apply Plane.Point.ext
    · exact xZero
    · exact yZero
  let parameter := point.x / point.y
  have parameterTimesY : parameter * point.y = point.x := by
    unfold parameter
    exact ExplicitField.div_mul_cancel point.x yNonzero
  have factoredEquation :
      point.y * (point.y + point.y * parameter ^ 2 - 1) = 0 := by
    calc
      point.y * (point.y + point.y * parameter ^ 2 - 1) =
          (parameter * point.y) ^ 2 + point.y ^ 2 - point.y := by ring1
      _ = point.x ^ 2 + point.y ^ 2 - point.y := by
        rw [parameterTimesY]
      _ = 0 := circleEquation
  have secondFactorZero : point.y + point.y * parameter ^ 2 - 1 = 0 := by
    by_cases factorZero : point.y + point.y * parameter ^ 2 - 1 = 0
    · exact factorZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero yNonzero factorZero) factoredEquation)
  have denominatorProduct : point.y * (1 + parameter ^ 2) = 1 := by
    calc
      point.y * (1 + parameter ^ 2) =
          (point.y + point.y * parameter ^ 2 - 1) + 1 := by ring1
      _ = 1 := by rw [secondFactorZero]; ring1
  have denominatorNonzero : 1 + parameter ^ 2 ≠ 0 := by
    intro denominatorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = point.y * (1 + parameter ^ 2) := denominatorProduct.symm
      _ = 0 := by rw [denominatorZero]; ring1
  have yFormula : point.y = 1 / (1 + parameter ^ 2) := by
    apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
    calc
      point.y * (1 + parameter ^ 2) = 1 := denominatorProduct
      _ = (1 / (1 + parameter ^ 2)) * (1 + parameter ^ 2) :=
        (ExplicitField.div_mul_cancel 1 denominatorNonzero).symm
  have xFormula : point.x = parameter / (1 + parameter ^ 2) := by
    calc
      point.x = parameter * point.y := parameterTimesY.symm
      _ = parameter * (1 / (1 + parameter ^ 2)) := by rw [yFormula]
      _ = parameter / (1 + parameter ^ 2) := by
        rw [ExplicitField.div_eq_mul_inv,
          ExplicitField.div_eq_mul_inv]
        ring1
  refine ⟨parameter,
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter).1
      denominatorNonzero, ?_⟩
  apply Plane.Point.ext
  · exact xFormula
  · exact yFormula

/-- Parametrize every non-origin point of the projective circle.

Parameters whose square is not minus one produce circle points, and every non-origin circle point has such a parameter
(Theorem 107). -/
theorem projective_circle [Nontrivial K] [DecidableEq K] :
    (∀ parameter : K, parameter ^ 2 ≠ -1 →
      Conic.projectiveCircle.Contains (projectiveCirclePoint parameter)) ∧
    (∀ point : Plane.Point K,
      Conic.projectiveCircle.Contains point → point ≠ (⟨0, 0⟩ : Plane.Point K) →
        ∃ parameter : K,
          parameter ^ 2 ≠ -1 ∧
            point = projectiveCirclePoint parameter) := by
  exact ⟨projectiveCirclePoint_contains,
    projectiveCirclePoint_exists⟩
end

end Purelib.Curves.Plane.Conic

end
