module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

public section

/-!
# Stationary quad-triple equations

Finite polynomial stationarity and the quad-triple identity determine the
squared-rate relation over an explicitly supplied field.
-/

namespace Purelib.Algebra.Proportions.QuadTriple.Stationary

variable {K : Type*} [ExplicitField K]

/-- A stationary quad-triple equation forces a squared-rate relation.

Two is nonzero and the two times differ; these hypotheses permit the factors introduced by squaring the stationarity
equation to be cancelled. -/
theorem stationary_quadTriple_derivative [DecidableEq K]
    (firstTime secondTime totalTime firstRate secondRate : K)
    (twoNonzero : (2 : K) ≠ 0)
    (timesDifferent : firstTime ≠ secondTime)
    (quadTriple :
      (firstTime + secondTime - totalTime) ^ 2 =
        4 * firstTime * secondTime)
    (stationaryDerivative :
      2 * (firstTime + secondTime - totalTime) *
          (firstRate + secondRate) =
        4 * (firstRate * secondTime + firstTime * secondRate)) :
    secondTime * firstRate ^ 2 = firstTime * secondRate ^ 2 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by ring1]
    exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have sixteenNonzero : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 4 * 4 by ring1]
    exact ExplicitField.mul_ne_zero fourNonzero fourNonzero
  have squaredDerivative := congrArg (fun value : K => value ^ 2)
    stationaryDerivative
  have scaledFactorization :
      16 * ((firstTime - secondTime) *
        (secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2)) = 0 := by
    calc
      16 * ((firstTime - secondTime) *
          (secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2)) =
        4 * (firstTime + secondTime - totalTime) ^ 2 *
            (firstRate + secondRate) ^ 2 -
          16 * (firstRate * secondTime +
            firstTime * secondRate) ^ 2 := by
              rw [quadTriple]
              ring1
      _ =
        (2 * (firstTime + secondTime - totalTime) *
            (firstRate + secondRate)) ^ 2 -
          (4 * (firstRate * secondTime +
            firstTime * secondRate)) ^ 2 := by
              ring1
      _ = 0 := by rw [squaredDerivative]; ring1
  have factorization :
      (firstTime - secondTime) *
        (secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2) = 0 :=
    ExplicitField.eq_zero_of_mul_eq_zero_left sixteenNonzero (by
      calc
        16 * ((firstTime - secondTime) *
            (secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2)) = 0 :=
          scaledFactorization)
  have differenceNonzero : firstTime - secondTime ≠ 0 := by
    intro differenceZero
    apply timesDifferent
    calc
      firstTime = (firstTime - secondTime) + secondTime := by ring1
      _ = secondTime := by rw [differenceZero]; ring1
  have resultDifference :
      secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2 = 0 :=
    ExplicitField.eq_zero_of_mul_eq_zero_left differenceNonzero factorization
  calc
    secondTime * firstRate ^ 2 =
        (secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2) +
          firstTime * secondRate ^ 2 := by ring1
    _ = firstTime * secondRate ^ 2 := by rw [resultDifference]; ring1
end Purelib.Algebra.Proportions.QuadTriple.Stationary
