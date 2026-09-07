import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Transcendental.FiniteLog

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

namespace CCL.FiniteLog

open RFAP.ConstructiveGaussian.Gaussian

theorem denominator_product_lower {x y : Coordinate}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    2 ≤ (x + 1) * (y + 1) := by
  have xLower : (3 / 2 : Coordinate) ≤ x + 1 := by
    calc
      (3 / 2 : Coordinate) = 1 / 2 + 1 := by decide
      _ ≤ x + 1 := add_le_add xHalf le_rfl
  have yLower : (3 / 2 : Coordinate) ≤ y + 1 := by
    calc
      (3 / 2 : Coordinate) = 1 / 2 + 1 := by decide
      _ ≤ y + 1 := add_le_add yHalf le_rfl
  have productLower := RFAP.ConstructiveFraction.mul_le_mul_direct
    xLower yLower (by decide : (0 : Coordinate) ≤ 3 / 2)
    ((by decide : (0 : Coordinate) ≤ 3 / 2).trans xLower)
  calc
    (2 : Coordinate) ≤ (3 / 2 : Coordinate) * (3 / 2) := by decide
    _ ≤ (x + 1) * (y + 1) := productLower

theorem reducedArgument_sub {x y : Coordinate}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    reducedArgument x - reducedArgument y =
      2 * (x - y) / ((x + 1) * (y + 1)) := by
  rw [reducedArgument, reducedArgument]
  calc
    (x - 1) / (x + 1) - (y - 1) / (y + 1) =
        ((x - 1) * (y + 1) - (y - 1) * (x + 1)) /
          ((x + 1) * (y + 1)) :=
      RFAP.ConstructiveFraction.div_sub_div_direct _ _ _ _
        (denominator_pos xHalf).ne' (denominator_pos yHalf).ne'
    _ = 2 * (x - y) / ((x + 1) * (y + 1)) := by
      congr 1
      ring1

def reducedArgumentSlope (x y : Coordinate) : Coordinate :=
  2 / ((x + 1) * (y + 1))

theorem reducedArgumentSlope_nonneg {x y : Coordinate}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    0 ≤ reducedArgumentSlope x y := by
  have productPositive := RFAP.ConstructiveFraction.mul_pos_direct
    (denominator_pos xHalf) (denominator_pos yHalf)
  exact RFAP.ConstructiveFraction.div_nonneg_direct (by decide)
    productPositive.le

theorem reducedArgumentSlope_le_one {x y : Coordinate}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    reducedArgumentSlope x y ≤ 1 := by
  have productPositive := RFAP.ConstructiveFraction.mul_pos_direct
    (denominator_pos xHalf) (denominator_pos yHalf)
  apply (RFAP.ConstructiveFraction.div_le_iff_pos productPositive).mpr
  rw [RFAP.ConstructiveFraction.one_mul]
  exact denominator_product_lower xHalf yHalf

theorem reducedArgument_sub_sq_le {x y : Coordinate}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    (reducedArgument x - reducedArgument y) ^ 2 ≤ (x - y) ^ 2 := by
  have slopeSq : reducedArgumentSlope x y ^ 2 ≤ 1 := by
    have bound := RFAP.ConstructiveFraction.pow_le_pow_direct
      (reducedArgumentSlope_nonneg xHalf yHalf)
      (reducedArgumentSlope_le_one xHalf yHalf) 2
    simpa only [one_pow] using bound
  have factorization :
      2 * (x - y) / ((x + 1) * (y + 1)) =
        reducedArgumentSlope x y * (x - y) := by
    rw [reducedArgumentSlope]
    change (2 * (x - y)) * ((x + 1) * (y + 1))⁻¹ =
      (2 * ((x + 1) * (y + 1))⁻¹) * (x - y)
    calc
      (2 * (x - y)) * ((x + 1) * (y + 1))⁻¹ =
          2 * ((x - y) * ((x + 1) * (y + 1))⁻¹) :=
        RFAP.ConstructiveFraction.mul_assoc _ _ _
      _ = 2 * (((x + 1) * (y + 1))⁻¹ * (x - y)) := by
        rw [RFAP.ConstructiveFraction.mul_comm (x - y)]
      _ = (2 * ((x + 1) * (y + 1))⁻¹) * (x - y) :=
        (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
  rw [reducedArgument_sub xHalf yHalf, factorization, mul_pow]
  have multiplied := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    slopeSq (RFAP.ConstructiveFraction.sq_nonneg_direct (x - y))
  simpa only [RFAP.ConstructiveFraction.one_mul] using multiplied

theorem sq_add_le_two (a b : Coordinate) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have nonnegative := RFAP.ConstructiveFraction.sq_nonneg_direct (a - b)
  apply sub_nonneg.mp
  calc
    0 ≤ (a - b) ^ 2 := nonnegative
    _ = 2 * (a ^ 2 + b ^ 2) - (a + b) ^ 2 := by ring1

theorem squaredArgument_sub_sq_le {x y : Coordinate}
    (xHalf : 1 / 2 ≤ x) (xTwo : x ≤ 2)
    (yHalf : 1 / 2 ≤ y) (yTwo : y ≤ 2) :
    (squaredArgument x - squaredArgument y) ^ 2 ≤ (x - y) ^ 2 := by
  let zx := reducedArgument x
  let zy := reducedArgument y
  have sumSq : (zx + zy) ^ 2 ≤ 1 := by
    calc
      (zx + zy) ^ 2 ≤ 2 * (zx ^ 2 + zy ^ 2) := sq_add_le_two zx zy
      _ ≤ 2 * ((1 / 9 : Coordinate) + 1 / 9) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add (squaredArgument_le_ninth xHalf xTwo)
            (squaredArgument_le_ninth yHalf yTwo)) (by decide)
      _ ≤ 1 := by decide
  have differenceSq := reducedArgument_sub_sq_le xHalf yHalf
  have identity : squaredArgument x - squaredArgument y =
      (zx - zy) * (zx + zy) := by
    dsimp only [squaredArgument, zx, zy]
    ring1
  rw [identity, mul_pow]
  have multiplied := RFAP.ConstructiveFraction.mul_le_mul_direct
    differenceSq sumSq (RFAP.ConstructiveFraction.sq_nonneg_direct (zx + zy))
    (RFAP.ConstructiveFraction.sq_nonneg_direct (x - y))
  simpa only [RFAP.ConstructiveFraction.mul_one_direct] using multiplied

theorem coefficient_sq_le_one {index : Nat} (positive : 1 ≤ index) :
    coefficient index ^ 2 ≤ 1 := by
  have squared := RFAP.ConstructiveFraction.pow_le_pow_direct
    (coefficient_nonneg positive) (coefficient_le_one index) 2
  simpa only [one_pow] using squared

theorem step_inputs_sub (w v : Coordinate) (index : Nat)
    (wTail vTail : Coordinate) :
    step w index wTail - step v index vTail =
      coefficient index * ((w - v) * wTail + v * (wTail - vTail)) := by
  rw [step_eq, step_eq]
  ring1

def hornerInputScale : Coordinate := 16

theorem horner_input_close {w v : Coordinate}
    (wNonnegative : 0 ≤ w) (wLe : w ≤ 1 / 9)
    (vNonnegative : 0 ≤ v) (vLe : v ≤ 1 / 9) :
    ∀ (depth index : Nat), 1 ≤ index →
      (horner w index depth - horner v index depth) ^ 2 ≤
        hornerInputScale * (w - v) ^ 2
  | 0, _, _ => by
      rw [horner_zero, horner_zero]
      change (0 : Coordinate) ^ 2 ≤ hornerInputScale * (w - v) ^ 2
      exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.sq_nonneg_direct (w - v))
  | depth + 1, index, positive => by
      rw [horner_succ, horner_succ, step_inputs_sub, mul_pow]
      let wTail := horner w (index + 1) depth
      let vTail := horner v (index + 1) depth
      let differenceSq := (w - v) ^ 2
      have wTailBounds := horner_bounds wNonnegative wLe depth (index + 1)
        (by omega)
      have wTailSq : wTail ^ 2 ≤ 4 := by
        have squared := RFAP.ConstructiveFraction.pow_le_pow_direct
          ((by decide : (0 : Coordinate) ≤ 1).trans wTailBounds.1)
          wTailBounds.2 2
        simpa only [wTail] using (squared.trans_eq (by decide))
      have tailDifference : (wTail - vTail) ^ 2 ≤
          hornerInputScale * differenceSq :=
        horner_input_close wNonnegative wLe vNonnegative vLe depth
          (index + 1) (by omega)
      have vSq : v ^ 2 ≤ 1 / 4 := by
        calc
          v ^ 2 ≤ (1 / 9 : Coordinate) ^ 2 :=
            RFAP.ConstructiveFraction.pow_le_pow_direct vNonnegative vLe 2
          _ ≤ 1 / 4 := by decide
      have firstBound : ((w - v) * wTail) ^ 2 ≤ 4 * differenceSq := by
        rw [mul_pow]
        have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          wTailSq (RFAP.ConstructiveFraction.sq_nonneg_direct (w - v))
        simpa only [differenceSq] using (show
          (w - v) ^ 2 * wTail ^ 2 ≤ (w - v) ^ 2 * 4 from scaled).trans_eq
            (by ring1)
      have secondBound : (v * (wTail - vTail)) ^ 2 ≤
          4 * differenceSq := by
        rw [mul_pow]
        calc
          v ^ 2 * (wTail - vTail) ^ 2 ≤
              (1 / 4 : Coordinate) *
                (hornerInputScale * differenceSq) :=
            RFAP.ConstructiveFraction.mul_le_mul_direct vSq tailDifference
              (RFAP.ConstructiveFraction.sq_nonneg_direct (wTail - vTail))
              (by decide)
          _ = 4 * differenceSq := by
            rw [hornerInputScale]
            calc
              (1 / 4 : Coordinate) * (16 * differenceSq) =
                  ((1 / 4 : Coordinate) * 16) * differenceSq := by ring1
              _ = 4 * differenceSq := by
                rw [show (1 / 4 : Coordinate) * 16 = 4 by decide]
      have sumBound :
          ((w - v) * wTail + v * (wTail - vTail)) ^ 2 ≤
            hornerInputScale * differenceSq := by
        calc
          ((w - v) * wTail + v * (wTail - vTail)) ^ 2 ≤
              2 * (((w - v) * wTail) ^ 2 +
                (v * (wTail - vTail)) ^ 2) := sq_add_le_two _ _
          _ ≤ 2 * (4 * differenceSq + 4 * differenceSq) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add firstBound secondBound) (by decide)
          _ = hornerInputScale * differenceSq := by
            rw [hornerInputScale]
            ring1
      have multiplied := RFAP.ConstructiveFraction.mul_le_mul_direct
        (coefficient_sq_le_one positive) sumBound
        (RFAP.ConstructiveFraction.sq_nonneg_direct
          ((w - v) * wTail + v * (wTail - vTail)))
        (by decide : (0 : Coordinate) ≤ 1)
      simpa only [RFAP.ConstructiveFraction.one_mul] using multiplied

theorem outputFactor_sub_sq_le {x y : Coordinate}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    (outputFactor x - outputFactor y) ^ 2 ≤ 4 * (x - y) ^ 2 := by
  have argumentDifference := reducedArgument_sub_sq_le xHalf yHalf
  rw [outputFactor, outputFactor]
  have identity : 2 * reducedArgument x - 2 * reducedArgument y =
      2 * (reducedArgument x - reducedArgument y) := by ring1
  rw [identity, mul_pow]
  have twoSq : (2 : Coordinate) ^ 2 = 4 := by decide
  rw [twoSq]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    argumentDifference (by decide)

def sampleInputScale : Coordinate := 2 * (16 + 16)

theorem sample_input_close {x y : Coordinate}
    (xHalf : 1 / 2 ≤ x) (xTwo : x ≤ 2)
    (yHalf : 1 / 2 ≤ y) (yTwo : y ≤ 2) (depth : Nat) :
    normSq (sample x depth - sample y depth) ≤
      sampleInputScale * (x - y) ^ 2 := by
  rw [sample, sample, normSq_real_sub, sampleCoordinate_eq, sampleCoordinate_eq]
  let xTail := horner (squaredArgument x) 1 depth
  let yTail := horner (squaredArgument y) 1 depth
  let differenceSq := (x - y) ^ 2
  have xTailBounds := horner_bounds (squaredArgument_nonneg x)
    (squaredArgument_le_ninth xHalf xTwo) depth 1 (by decide)
  have xTailSq : xTail ^ 2 ≤ 4 := by
    have squared := RFAP.ConstructiveFraction.pow_le_pow_direct
      ((by decide : (0 : Coordinate) ≤ 1).trans xTailBounds.1)
      xTailBounds.2 2
    simpa only [xTail] using squared.trans_eq (by decide)
  have factorDifference :
      (outputFactor x - outputFactor y) ^ 2 ≤ 4 * differenceSq :=
    outputFactor_sub_sq_le xHalf yHalf
  have tailDifference : (xTail - yTail) ^ 2 ≤
      hornerInputScale * differenceSq := by
    exact (horner_input_close (squaredArgument_nonneg x)
      (squaredArgument_le_ninth xHalf xTwo) (squaredArgument_nonneg y)
      (squaredArgument_le_ninth yHalf yTwo) depth 1 (by decide)).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (squaredArgument_sub_sq_le xHalf xTwo yHalf yTwo) (by decide))
  have firstBound : ((outputFactor x - outputFactor y) * xTail) ^ 2 ≤
      16 * differenceSq := by
    rw [mul_pow]
    calc
      (outputFactor x - outputFactor y) ^ 2 * xTail ^ 2 ≤
          (4 * differenceSq) * 4 :=
        RFAP.ConstructiveFraction.mul_le_mul_direct factorDifference xTailSq
          (RFAP.ConstructiveFraction.sq_nonneg_direct xTail)
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (RFAP.ConstructiveFraction.sq_nonneg_direct (x - y)))
      _ = 16 * differenceSq := by ring1
  have secondBound : (outputFactor y * (xTail - yTail)) ^ 2 ≤
      16 * differenceSq := by
    rw [mul_pow]
    have multiplied := RFAP.ConstructiveFraction.mul_le_mul_direct
      (outputFactor_sq_le_one yHalf yTwo) tailDifference
      (RFAP.ConstructiveFraction.sq_nonneg_direct (xTail - yTail))
      (by decide : (0 : Coordinate) ≤ 1)
    simpa only [RFAP.ConstructiveFraction.one_mul, hornerInputScale] using multiplied
  have identity : outputFactor x * xTail - outputFactor y * yTail =
      (outputFactor x - outputFactor y) * xTail +
        outputFactor y * (xTail - yTail) := by ring1
  rw [identity]
  calc
    ((outputFactor x - outputFactor y) * xTail +
        outputFactor y * (xTail - yTail)) ^ 2 ≤
      2 * (((outputFactor x - outputFactor y) * xTail) ^ 2 +
        (outputFactor y * (xTail - yTail)) ^ 2) := sq_add_le_two _ _
    _ ≤ 2 * (16 * differenceSq + 16 * differenceSq) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstBound secondBound) (by decide)
    _ = sampleInputScale * (x - y) ^ 2 := by
      dsimp only [sampleInputScale, differenceSq]
      ring1

end CCL.FiniteLog
