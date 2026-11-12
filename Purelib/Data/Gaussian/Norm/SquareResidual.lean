module

public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Separation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Finite magnitude control from a displayed Gaussian square residual -/

public section

namespace Purelib.Data.Gaussian.Norm.SquareResidual

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Fraction (Rational)
open Fraction.Order
open Purelib.Data.Gaussian.Basic.Canonical (normSq normSq_nonneg normSq_neg)

/-- A Gaussian square residual bounded by the radicand gives an explicit root-magnitude ceiling.

The supplied radicand bound and residual bound concern the actual displayed
rational values. No selected algebraic root or completed value is required.
-/
theorem normSq_le {value radicand : Canonical} {bound : Fraction.Rational}
    (radicandBound : Norm.Basic.normSq radicand ≤ bound)
    (residual : Norm.Basic.normSq (value * value - radicand) ≤ Norm.Basic.normSq radicand) :
    Norm.Basic.normSq value ≤ 1 + 4 * bound := by
  have boundNonnegative := (Norm.Basic.normSq_nonneg radicand).trans radicandBound
  have identity : value * value = (value * value - radicand) + radicand := by ring1
  have squareBound : Norm.Basic.normSq value * Norm.Basic.normSq value ≤ 4 * bound := by
    rewrite [← Norm.Basic.normSq_mul, identity]
    calc
      _ ≤ 2 * (Norm.Basic.normSq (value * value - radicand) + Norm.Basic.normSq radicand) :=
        Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * (bound + bound) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct (residual.trans radicandBound) radicandBound)
          (by decide +kernel)
      _ = _ := by ring1
  by_cases small : Norm.Basic.normSq value ≤ 1
  · exact small.trans (le_add_of_nonneg_right
      (Arithmetic.mul_nonneg_direct (by decide +kernel) boundNonnegative))
  · have oneLe : (1 : Fraction.Rational) ≤ Norm.Basic.normSq value := le_of_not_ge small
    have normLeSquare : Norm.Basic.normSq value ≤ Norm.Basic.normSq value * Norm.Basic.normSq value := by
      calc
        _ = 1 * Norm.Basic.normSq value := (Fraction.Field.one_mul _).symm
        _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_right_direct oneLe (Norm.Basic.normSq_nonneg _)
    exact (normLeSquare.trans squareBound).trans (le_add_of_nonneg_left (by decide +kernel))

/-- Two actual square residuals and radicand movement control root displacement times a displayed sum floor.

The actual two roots and radicands remain separate inputs. Factoring their
square difference and paying both residuals gives the explicit estimate;
the lower bound on their sum selects compatible signed readings.
-/
theorem distance_mul_le {first last firstParameter lastParameter : Canonical}
    {firstResidual lastResidual parameterMovement sumFloor : Fraction.Rational}
    (sumLower : sumFloor ≤ Norm.Basic.normSq (first + last))
    (firstBound : Norm.Basic.normSq (first * first - firstParameter) ≤ firstResidual)
    (lastBound : Norm.Basic.normSq (last * last - lastParameter) ≤ lastResidual)
    (parameterBound : Norm.Basic.normSq (firstParameter - lastParameter) ≤ parameterMovement) :
    Norm.Basic.normSq (first - last) * sumFloor ≤
      4 * (firstResidual + lastResidual) + 2 * parameterMovement := by
  let firstError := first * first - firstParameter
  let lastError := last * last - lastParameter
  have factorization : (first - last) * (first + last) =
      (firstError - lastError) + (firstParameter - lastParameter) := by
    unfold firstError lastError
    ring1
  have residualDifference : Norm.Basic.normSq (firstError - lastError) ≤ 2 * (firstResidual + lastResidual) := by
    have difference : firstError - lastError = firstError + -lastError := by ring1
    rewrite [difference]
    exact (Norm.Bounds.normSq_add_le_two _ _).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct firstBound (by
          rewrite [Norm.Basic.normSq_neg]
          exact lastBound)) (by decide +kernel))
  calc
    _ ≤ Norm.Basic.normSq (first - last) * Norm.Basic.normSq (first + last) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct sumLower (Norm.Basic.normSq_nonneg _)
    _ = Norm.Basic.normSq ((first - last) * (first + last)) := (Norm.Basic.normSq_mul _ _).symm
    _ ≤ 2 * (2 * (firstResidual + lastResidual) + parameterMovement) := by
      rewrite [factorization]
      exact (Norm.Bounds.normSq_add_le_two _ _).trans
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct residualDifference parameterBound) (by decide +kernel))
    _ = _ := by ring1

/-- A unit sum floor gives the original direct root-distance bound from both actual square residuals.

This is the unit-floor specialization of the same difference-of-squares
certificate, retaining both roots and their distinct original radicands.
-/
theorem distance_le {first last firstParameter lastParameter : Canonical}
    {firstResidual lastResidual parameterMovement : Fraction.Rational}
    (sumLower : (1 : Fraction.Rational) ≤ Norm.Basic.normSq (first + last))
    (firstBound : Norm.Basic.normSq (first * first - firstParameter) ≤ firstResidual)
    (lastBound : Norm.Basic.normSq (last * last - lastParameter) ≤ lastResidual)
    (parameterBound : Norm.Basic.normSq (firstParameter - lastParameter) ≤ parameterMovement) :
    Norm.Basic.normSq (first - last) ≤ 4 * (firstResidual + lastResidual) + 2 * parameterMovement := by
  have bound := distance_mul_le sumLower firstBound lastBound parameterBound
  rewrite [Fraction.Field.mul_one_direct] at bound
  exact bound

/-- A short root step with paid square residuals remains near the same original reference reading.

The reference squared norm fixes every unit in the estimate. Separate
quadratic residuals and radicand movement bound the difference of squares;
the short actual root step supplies the signed sum floor. No square root
of a rational bound or independently selected root is used.
-/
theorem near_of_short_step {reference current next referenceParameter nextParameter : Canonical}
    (positive : 0 < normSq reference)
    (near : normSq (current - reference) ≤ normSq reference / 4)
    (step : normSq (next - current) ≤ normSq current / 1024)
    (referenceResidual : normSq (reference * reference - referenceParameter) ≤ normSq reference ^ 2 / 1024)
    (nextResidual : normSq (next * next - nextParameter) ≤ normSq next ^ 2 / 1024)
    (movement : normSq (referenceParameter - nextParameter) ≤ normSq reference ^ 2 / 1024) :
    normSq (next - reference) ≤ normSq reference / 16 := by
  have currentNorm : normSq current ≤ (5 / 2 : Rational) * normSq reference := by
    have identity : current = (current - reference) + reference := by ring1
    calc
      _ = normSq ((current - reference) + reference) := congrArg normSq identity
      _ ≤ 2 * (normSq (current - reference) + normSq reference) := by
        have bound := Norm.Bounds.normSq_add_le_two (current - reference) reference
        simp only [Norm.Basic.normSq_eq_canonical] at bound
        exact bound
      _ ≤ 2 * (normSq reference / 4 + normSq reference) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_right_direct near _) (by decide +kernel)
      _ = (2 * ((4 : Rational)⁻¹ + 1)) * normSq reference := by
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        ring1
      _ = _ := congrArg (fun coefficient : Rational => coefficient * normSq reference) (by decide +kernel)
  have provisional : normSq (next - reference) ≤ (3 / 4 : Rational) * normSq reference := by
    have identity : next - reference = (next - current) + (current - reference) := by ring1
    calc
      _ = normSq ((next - current) + (current - reference)) := congrArg normSq identity
      _ ≤ 2 * (normSq (next - current) + normSq (current - reference)) := by
        have bound := Norm.Bounds.normSq_add_le_two (next - current) (current - reference)
        simp only [Norm.Basic.normSq_eq_canonical] at bound
        exact bound
      _ ≤ 2 * (((5 / 2 : Rational) * normSq reference) / 1024 + normSq reference / 4) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct
            (step.trans (Field.divide_mono currentNorm (by decide +kernel))) near) (by decide +kernel)
      _ = (2 * ((5 / 2 : Rational) * (1024 : Rational)⁻¹ + (4 : Rational)⁻¹)) * normSq reference := by
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        ring1
      _ = (517 / 1024 : Rational) * normSq reference :=
        congrArg (fun coefficient : Rational => coefficient * normSq reference) (by decide +kernel)
      _ ≤ (3 / 4 : Rational) * normSq reference :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) positive.le
  have nextNorm : normSq next ≤ (7 / 2 : Rational) * normSq reference := by
    have identity : next = (next - reference) + reference := by ring1
    calc
      _ = normSq ((next - reference) + reference) := congrArg normSq identity
      _ ≤ 2 * (normSq (next - reference) + normSq reference) := by
        have bound := Norm.Bounds.normSq_add_le_two (next - reference) reference
        simp only [Norm.Basic.normSq_eq_canonical] at bound
        exact bound
      _ ≤ 2 * ((3 / 4 : Rational) * normSq reference + normSq reference) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_right_direct provisional _) (by decide +kernel)
      _ = (2 * ((3 / 4 : Rational) + 1)) * normSq reference := by ring1
      _ = _ := congrArg (fun coefficient : Rational => coefficient * normSq reference) (by decide +kernel)
  have nextPaid : normSq (next * next - nextParameter) ≤
      (49 / 4096 : Rational) * normSq reference ^ 2 := by
    calc
      _ ≤ normSq next ^ 2 / 1024 := nextResidual
      _ ≤ ((7 / 2 : Rational) * normSq reference) ^ 2 / 1024 :=
        Field.divide_mono (Arithmetic.pow_le_pow_direct (normSq_nonneg next) nextNorm 2) (by decide +kernel)
      _ = (((7 / 2 : Rational) ^ 2) * (1024 : Rational)⁻¹) * normSq reference ^ 2 := by
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        ring1
      _ = _ := congrArg (fun coefficient : Rational => coefficient * normSq reference ^ 2) (by decide +kernel)
  have nearReference : normSq (reference - next) ≤ normSq reference := by
    have symmetry : reference - next = -(next - reference) := by ring1
    rewrite [symmetry, normSq_neg]
    exact provisional.trans (by
      have bound := Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by decide +kernel : (3 / 4 : Rational) ≤ 1) positive.le
      rewrite [Fraction.Field.one_mul] at bound
      exact bound)
  have quarterDouble : Norm.Basic.normSq (reference + reference) / 4 = normSq reference := by
    rewrite [Norm.Basic.normSq_double, Norm.Basic.normSq_eq_canonical]
    calc
      _ = ((4 : Rational) * (4 : Rational)⁻¹) * normSq reference := by
        rewrite [Fraction.Field.div_eq_mul_inv_direct]
        ring1
      _ = 1 * normSq reference :=
        congrArg (fun coefficient : Rational => coefficient * normSq reference) (by decide +kernel)
      _ = _ := Fraction.Field.one_mul _
  have sumLower : normSq reference ≤ normSq (reference + next) := by
    have close : Norm.Basic.normSq ((reference + reference) - (reference + next)) ≤
        Norm.Basic.normSq (reference + reference) / 4 := by
      rewrite [show (reference + reference) - (reference + next) = reference - next by ring1,
        quarterDouble, Norm.Basic.normSq_eq_canonical]
      exact nearReference
    have lower := Norm.Bounds.quarter_normSq_le_of_close (reference + reference) (reference + next) close
    rewrite [quarterDouble, Norm.Basic.normSq_eq_canonical] at lower
    exact lower
  have estimate := distance_mul_le
    (first := reference) (last := next)
    (firstParameter := referenceParameter) (lastParameter := nextParameter)
    (firstResidual := normSq reference ^ 2 / 1024)
    (lastResidual := (49 / 4096 : Rational) * normSq reference ^ 2)
    (parameterMovement := normSq reference ^ 2 / 1024) (sumFloor := normSq reference)
    (by rewrite [Norm.Basic.normSq_eq_canonical]; exact sumLower)
    (by rewrite [Norm.Basic.normSq_eq_canonical]; exact referenceResidual)
    (by rewrite [Norm.Basic.normSq_eq_canonical]; exact nextPaid)
    (by rewrite [Norm.Basic.normSq_eq_canonical]; exact movement)
  rewrite [Norm.Basic.normSq_eq_canonical,
    show reference - next = -(next - reference) by ring1, normSq_neg] at estimate
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := normSq reference) _ positive
  calc
    _ ≤ 4 * (normSq reference ^ 2 / 1024 + (49 / 4096 : Rational) * normSq reference ^ 2) +
        2 * (normSq reference ^ 2 / 1024) := estimate
    _ = (4 * ((1024 : Rational)⁻¹ + (49 / 4096 : Rational)) + 2 * (1024 : Rational)⁻¹) *
        normSq reference ^ 2 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = (55 / 1024 : Rational) * normSq reference ^ 2 :=
      congrArg (fun coefficient : Rational => coefficient * normSq reference ^ 2) (by decide +kernel)
    _ ≤ (1 / 16 : Rational) * normSq reference ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
        (Arithmetic.pow_nonneg_direct positive.le 2)
    _ = (normSq reference / 16) * normSq reference := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1

/-- A positive sum floor pays both actual square residuals and movement of the two original radicands.

The two readings and their radicands remain separate. The difference of
squares uses the exact original sum quadrance; division is paid by the
retained positive floor, without asserting a common selected square root.
-/
theorem distance_le_of_sum_lower {first last firstParameter lastParameter : Canonical}
    {floor firstResidual lastResidual parameterMovement : Fraction.Rational}
    (positive : 0 < floor) (sumLower : floor ≤ Norm.Basic.normSq (first + last))
    (firstBound : Norm.Basic.normSq (first * first - firstParameter) ≤ firstResidual)
    (lastBound : Norm.Basic.normSq (last * last - lastParameter) ≤ lastResidual)
    (parameterBound : Norm.Basic.normSq (firstParameter - lastParameter) ≤ parameterMovement) :
    Norm.Basic.normSq (first - last) ≤
      (4 * (firstResidual + lastResidual) + 2 * parameterMovement) / floor :=
  (Fraction.Order.Field.le_div_iff_pos positive).mpr
    (distance_mul_le sumLower firstBound lastBound parameterBound)

/-- Two paid square residuals bound the root difference when the actual sum has a positive floor.

The common exact radicand cancels in the difference of the two squared
readings. The original quadrance product identity and the supplied sum floor
pay division by that positive floor; no individual root apartness is assumed.
-/
theorem distance_lt_of_sum_lower {left right parameter : Canonical} {lower target : Fraction.Rational}
    (lowerPositive : 0 < lower) (sumLower : lower ≤ Canonical.normSq (left + right))
    (leftResidual : Canonical.normSq (left * left - parameter) < target * lower / 4)
    (rightResidual : Canonical.normSq (right * right - parameter) < target * lower / 4) :
    Canonical.normSq (left - right) < target := by
  have residualBound : Canonical.normSq (left * left - right * right) < target * lower := by
    have identity : left * left - right * right =
        (left * left - parameter) - (right * right - parameter) := by ring1
    rewrite [identity]
    calc
      _ ≤ 2 * (Canonical.normSq (left * left - parameter) + Canonical.normSq (right * right - parameter)) := by
        have scalar := Norm.Bounds.normSq_sub_le_two (left * left - parameter) (right * right - parameter)
        rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical,
          Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar
      _ < 2 * (target * lower / 4 + target * lower / 4) :=
        Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
          (Arithmetic.add_lt_add_direct leftResidual rightResidual)
      _ = (target * lower / 4) * 4 := by ring1
      _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  apply Arithmetic.lt_of_mul_lt_mul_right_direct (c := lower) _ lowerPositive
  calc
    Canonical.normSq (left - right) * lower ≤ Canonical.normSq (left - right) * Canonical.normSq (left + right) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct sumLower (Canonical.normSq_nonneg _)
    _ = Canonical.normSq (left * left - right * right) := by
      rewrite [← Canonical.normSq_mul,
        show (left - right) * (left + right) = left * left - right * right by ring1]
      rfl
    _ < _ := residualBound

end Purelib.Data.Gaussian.Norm.SquareResidual
