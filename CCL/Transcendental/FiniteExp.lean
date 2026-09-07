import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Geometry.FiniteGeometric
import CCL.Progressive.Approximation

/-!
# Finite exponential Horner approximation

This is a finite operational exponential on Gaussian rationals in the closed
unit disk.  `sample x n` evaluates exactly one finite Horner program.  The
pairwise theorem compares any two displayed truncations and supplies an
explicit rational squared-error sidecar.  Nothing in this module defines a
completed exponential value or invokes an infinite series or a limit.
-/

namespace CCL.FiniteExp

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev Named := CCL.ProgressiveTransducer.Named

open RFAP.ConstructiveGaussian.Gaussian

/-- Multiplication of a Gaussian rational by a rational coordinate. -/
def scale (a : Coordinate) (z : Gaussian) : Gaussian :=
  ⟨a * z.re, a * z.im⟩

@[simp] theorem scale_re (a : Coordinate) (z : Gaussian) :
    (scale a z).re = a * z.re := rfl

@[simp] theorem scale_im (a : Coordinate) (z : Gaussian) :
    (scale a z).im = a * z.im := rfl

theorem normSq_scale (a : Coordinate) (z : Gaussian) :
    normSq (scale a z) = a ^ 2 * normSq z := by
  simp only [normSq, scale_re, scale_im]
  ring1

/-- One affine stage `y ↦ 1 + xy/n` of the paper's exponential recurrence. -/
def step (x : Gaussian) (denominator : Nat) (tail : Gaussian) : Gaussian :=
  canonical (1 + scale (1 / (denominator : Coordinate)) (x * tail))

theorem step_eq (x : Gaussian) (denominator : Nat) (tail : Gaussian) :
    step x denominator tail =
      1 + scale (1 / (denominator : Coordinate)) (x * tail) :=
  canonical_eq _

/-- A displayed finite Horner program.  At depth zero its tail is exactly the
rational value one. -/
def horner (x : Gaussian) : Nat → Nat → Gaussian
  | _, 0 => 1
  | denominator, depth + 1 =>
      step x denominator (horner x (denominator + 1) depth)

@[simp] theorem horner_zero (x : Gaussian) (denominator : Nat) :
    horner x denominator 0 = 1 := rfl

@[simp] theorem horner_succ (x : Gaussian) (denominator depth : Nat) :
    horner x denominator (depth + 1) =
      step x denominator (horner x (denominator + 1) depth) := rfl

/-- Every finite truncation at the displayed rational input zero is exactly
one.  This is the first analytic normalization law, proved before introducing
any completed exponential value. -/
theorem horner_zero_input :
    ∀ (depth denominator : Nat),
      horner (0 : Gaussian) denominator depth = 1
  | 0, _ => rfl
  | depth + 1, denominator => by
      rw [horner_succ, step_eq,
        horner_zero_input depth (denominator + 1)]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, one_re, one_im, scale_re, scale_im,
          mul_re, mul_im, zero_re, zero_im] <;> ring1

theorem step_sub_step (x : Gaussian) (denominator : Nat)
    (left right : Gaussian) :
    step x denominator left - step x denominator right =
      scale (1 / (denominator : Coordinate)) (x * (left - right)) := by
  rw [step_eq, step_eq]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [scale_re, scale_im, add_re, add_im, sub_re,
      sub_im, one_re, one_im, mul_re, mul_im] <;> ring1

theorem reciprocal_nat_sq_le_quarter {denominator : Nat}
    (atLeastTwo : 2 ≤ denominator) :
    (1 / (denominator : Coordinate)) ^ 2 ≤ (1 / 4 : Coordinate) := by
  have denominatorOrder : (2 : Coordinate) ≤ (denominator : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct atLeastTwo
  have inverseOrder : (denominator : Coordinate)⁻¹ ≤ (2 : Coordinate)⁻¹ :=
    RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct (by decide)
      denominatorOrder
  have inverseNonnegative : 0 ≤ (denominator : Coordinate)⁻¹ :=
    (RFAP.ConstructiveFraction.inv_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct (by omega))).le
  have squareOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
    inverseNonnegative inverseOrder 2
  calc
    (1 / (denominator : Coordinate)) ^ 2 =
        ((denominator : Coordinate)⁻¹) ^ 2 := by
      rw [RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ConstructiveFraction.one_mul]
    _ ≤ ((2 : Coordinate)⁻¹) ^ 2 := squareOrder
    _ = 1 / 4 := by decide

/-- Every inner Horner truncation stays in squared norm four on the rational
unit disk. -/
theorem step_bounded (x : Gaussian) (unitInput : normSq x ≤ 1)
    {denominator : Nat} (atLeastTwo : 2 ≤ denominator) {tail : Gaussian}
    (tailBound : normSq tail ≤ 4) :
    normSq (step x denominator tail) ≤ 4 := by
  rw [step_eq]
  have productBound : normSq (x * tail) ≤ 4 := by
    rw [normSq_mul]
    have multiplied := RFAP.ConstructiveFraction.mul_le_mul_direct unitInput
      tailBound (normSq_nonneg tail) (by decide : (0 : Coordinate) ≤ 1)
    simpa only [RFAP.ConstructiveFraction.one_mul] using multiplied
  have reciprocalBound := reciprocal_nat_sq_le_quarter atLeastTwo
  have reciprocalNonnegative :
      0 ≤ (1 / (denominator : Coordinate)) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have scaledBound :
      normSq (scale (1 / (denominator : Coordinate)) (x * tail)) ≤ 1 := by
    rw [normSq_scale]
    calc
      (1 / (denominator : Coordinate)) ^ 2 * normSq (x * tail) ≤
          (1 / (denominator : Coordinate)) ^ 2 * 4 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct productBound
          reciprocalNonnegative
      _ ≤ (1 / 4 : Coordinate) * 4 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          reciprocalBound (by decide)
      _ = 1 := by decide
  calc
    normSq (1 + scale (1 / (denominator : Coordinate)) (x * tail)) ≤
        2 * (normSq (1 : Gaussian) +
          normSq (scale (1 / (denominator : Coordinate)) (x * tail))) :=
      normSq_add_le_two _ _
    _ ≤ 2 * (1 + 1) := by
      rw [normSq_one]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl scaledBound) (by decide)
    _ = 4 := by decide

theorem horner_bounded (x : Gaussian) (unitInput : normSq x ≤ 1) :
    ∀ (depth denominator : Nat), 2 ≤ denominator →
      normSq (horner x denominator depth) ≤ 4
  | 0, _, _ => by
      rw [horner_zero, normSq_one]
      decide
  | depth + 1, denominator, atLeastTwo => by
      rw [horner_succ]
      exact step_bounded x unitInput atLeastTwo
        (horner_bounded x unitInput depth (denominator + 1) (by omega))

theorem horner_sub_one_bounded (x : Gaussian) (unitInput : normSq x ≤ 1)
    (depth denominator : Nat) (atLeastTwo : 2 ≤ denominator) :
    normSq (horner x denominator depth - 1) ≤ 10 := by
  calc
    normSq (horner x denominator depth - 1) ≤
        2 * (normSq (horner x denominator depth) + normSq (1 : Gaussian)) :=
      normSq_sub_le_two _ _
    _ ≤ 2 * (4 + 1) := by
      rw [normSq_one]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (horner_bounded x unitInput depth denominator atLeastTwo)
          le_rfl) (by decide)
    _ = 10 := by decide

/-- Each shared inner Horner stage contracts squared disagreement by one
quarter. -/
theorem step_difference_contract (x : Gaussian) (unitInput : normSq x ≤ 1)
    {denominator : Nat} (atLeastTwo : 2 ≤ denominator)
    (left right : Gaussian) :
    normSq (step x denominator left - step x denominator right) ≤
      (1 / 4 : Coordinate) * normSq (left - right) := by
  rw [step_sub_step, normSq_scale, normSq_mul]
  have inputScaled : normSq x * normSq (left - right) ≤
      1 * normSq (left - right) :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct unitInput
      (normSq_nonneg (left - right))
  have reciprocalNonnegative :
      0 ≤ (1 / (denominator : Coordinate)) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  calc
    (1 / (denominator : Coordinate)) ^ 2 *
          (normSq x * normSq (left - right)) ≤
        (1 / (denominator : Coordinate)) ^ 2 *
          (1 * normSq (left - right)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct inputScaled
        reciprocalNonnegative
    _ = (1 / (denominator : Coordinate)) ^ 2 *
        normSq (left - right) := by ring1
    _ ≤ (1 / 4 : Coordinate) * normSq (left - right) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (reciprocal_nat_sq_le_quarter atLeastTwo)
        (normSq_nonneg (left - right))

theorem step_inputs_sub (x y : Gaussian) (denominator : Nat)
    (xTail yTail : Gaussian) :
    step x denominator xTail - step y denominator yTail =
      scale (1 / (denominator : Coordinate))
        ((x - y) * xTail + y * (xTail - yTail)) := by
  rw [step_eq, step_eq]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [scale_re, scale_im, add_re, add_im, sub_re, sub_im,
      one_re, one_im, mul_re, mul_im] <;> ring1

/-- Uniform finite sensitivity of equal-depth inner Horner programs on the
rational unit disk. -/
theorem horner_input_close (x y : Gaussian) (xUnit : normSq x ≤ 1)
    (yUnit : normSq y ≤ 1) :
    ∀ (depth denominator : Nat), 2 ≤ denominator →
      normSq (horner x denominator depth - horner y denominator depth) ≤
        4 * normSq (x - y)
  | 0, _, _ => by
      rw [horner_zero, horner_zero, sub_self, normSq_zero]
      exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (normSq_nonneg (x - y))
  | depth + 1, denominator, atLeastTwo => by
      rw [horner_succ, horner_succ, step_inputs_sub, normSq_scale]
      let xTail := horner x (denominator + 1) depth
      let yTail := horner y (denominator + 1) depth
      let difference := normSq (x - y)
      have xTailBound : normSq xTail ≤ 4 :=
        horner_bounded x xUnit depth (denominator + 1) (by omega)
      have tailDifference : normSq (xTail - yTail) ≤ 4 * difference :=
        horner_input_close x y xUnit yUnit depth (denominator + 1) (by omega)
      have firstBound : normSq ((x - y) * xTail) ≤ 4 * difference := by
        rw [normSq_mul]
        have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          xTailBound (normSq_nonneg (x - y))
        calc
          normSq (x - y) * normSq xTail ≤ normSq (x - y) * 4 := scaled
          _ = 4 * difference := by
            dsimp only [difference]
            ring1
      have secondBound : normSq (y * (xTail - yTail)) ≤ 4 * difference := by
        rw [normSq_mul]
        have scaled := RFAP.ConstructiveFraction.mul_le_mul_direct yUnit
          tailDifference (normSq_nonneg (xTail - yTail))
          (by decide : (0 : Coordinate) ≤ 1)
        simpa only [RFAP.ConstructiveFraction.one_mul] using scaled
      have sumBound :
          normSq ((x - y) * xTail + y * (xTail - yTail)) ≤
            16 * difference := by
        calc
          normSq ((x - y) * xTail + y * (xTail - yTail)) ≤
              2 * (normSq ((x - y) * xTail) +
                normSq (y * (xTail - yTail))) := normSq_add_le_two _ _
          _ ≤ 2 * (4 * difference + 4 * difference) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add firstBound secondBound) (by decide)
          _ = 16 * difference := by ring1
      have reciprocalNonnegative :
          0 ≤ (1 / (denominator : Coordinate)) ^ 2 :=
        RFAP.ConstructiveFraction.sq_nonneg_direct _
      calc
        (1 / (denominator : Coordinate)) ^ 2 *
            normSq ((x - y) * xTail + y * (xTail - yTail)) ≤
          (1 / (denominator : Coordinate)) ^ 2 * (16 * difference) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              sumBound reciprocalNonnegative
        _ ≤ (1 / 4 : Coordinate) * (16 * difference) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (reciprocal_nat_sq_le_quarter atLeastTwo)
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              (normSq_nonneg (x - y)))
        _ = 4 * normSq (x - y) := by
          dsimp only [difference]
          calc
            (1 / 4 : Coordinate) * (16 * normSq (x - y)) =
                ((1 / 4 : Coordinate) * 16) * normSq (x - y) := by ring1
            _ = 4 * normSq (x - y) := by
              rw [show (1 / 4 : Coordinate) * 16 = 4 by decide]

/-- Any two displayed truncations compare directly, with no mention of a
limit or a completed exponential. -/
theorem horner_add_depth_close (x : Gaussian) (unitInput : normSq x ≤ 1) :
    ∀ (earlier extra denominator : Nat), 2 ≤ denominator →
      normSq (horner x denominator (earlier + extra) -
        horner x denominator earlier) ≤
          10 * (1 / 4 : Coordinate) ^ earlier
  | 0, extra, denominator, atLeastTwo => by
      simp only [Nat.zero_add, horner_zero, pow_zero]
      simpa only [RFAP.ConstructiveFraction.mul_one_direct] using
        horner_sub_one_bounded x unitInput extra denominator atLeastTwo
  | earlier + 1, extra, denominator, atLeastTwo => by
      rw [show earlier + 1 + extra = (earlier + extra) + 1 by ring1,
        horner_succ, horner_succ]
      calc
        normSq
            (step x denominator (horner x (denominator + 1) (earlier + extra)) -
              step x denominator (horner x (denominator + 1) earlier)) ≤
            (1 / 4 : Coordinate) *
              normSq (horner x (denominator + 1) (earlier + extra) -
                horner x (denominator + 1) earlier) :=
          step_difference_contract x unitInput atLeastTwo _ _
        _ ≤ (1 / 4 : Coordinate) *
            (10 * (1 / 4 : Coordinate) ^ earlier) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (horner_add_depth_close x unitInput earlier extra
              (denominator + 1)
              (atLeastTwo.trans (Nat.le_add_right denominator 1))) (by decide)
        _ = 10 * (1 / 4 : Coordinate) ^ (earlier + 1) := by
          rw [pow_succ]
          ring1

/-- The displayed finite exponential sample.  This is exactly the paper's
Horner recurrence cut off after `index` inner stages. -/
def sample (x : Gaussian) (index : Nat) : Gaussian :=
  step x 1 (horner x 2 index)

/-- The displayed finite exponential program satisfies `exp(0) = 1` exactly
at every depth. -/
theorem sample_zero (index : Nat) : sample 0 index = 1 := by
  rw [sample, step_eq, horner_zero_input]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [add_re, add_im, one_re, one_im, scale_re, scale_im,
      mul_re, mul_im, zero_re, zero_im] <;> ring1

/-- Uniform finite sensitivity of displayed outer exponential samples. -/
theorem sample_input_close (x y : Gaussian) (xUnit : normSq x ≤ 1)
    (yUnit : normSq y ≤ 1) (depth : Nat) :
    normSq (sample x depth - sample y depth) ≤ 16 * normSq (x - y) := by
  rw [sample, sample, step_inputs_sub, normSq_scale]
  let xTail := horner x 2 depth
  let yTail := horner y 2 depth
  let difference := normSq (x - y)
  have xTailBound : normSq xTail ≤ 4 :=
    horner_bounded x xUnit depth 2 (by decide)
  have tailDifference : normSq (xTail - yTail) ≤ 4 * difference :=
    horner_input_close x y xUnit yUnit depth 2 (by decide)
  have firstBound : normSq ((x - y) * xTail) ≤ 4 * difference := by
    rw [normSq_mul]
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      xTailBound (normSq_nonneg (x - y))
    calc
      normSq (x - y) * normSq xTail ≤ normSq (x - y) * 4 := scaled
      _ = 4 * difference := by
        dsimp only [difference]
        ring1
  have secondBound : normSq (y * (xTail - yTail)) ≤ 4 * difference := by
    rw [normSq_mul]
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_direct yUnit
      tailDifference (normSq_nonneg (xTail - yTail))
      (by decide : (0 : Coordinate) ≤ 1)
    simpa only [RFAP.ConstructiveFraction.one_mul] using scaled
  have sumBound := normSq_add_le_two ((x - y) * xTail)
    (y * (xTail - yTail))
  have scalar : (1 / ((1 : Nat) : Coordinate)) ^ 2 = 1 := by decide
  rw [scalar, RFAP.ConstructiveFraction.one_mul]
  calc
    normSq ((x - y) * xTail + y * (xTail - yTail)) ≤
        2 * (normSq ((x - y) * xTail) +
          normSq (y * (xTail - yTail))) := sumBound
    _ ≤ 2 * (4 * difference + 4 * difference) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstBound secondBound) (by decide)
    _ = 16 * normSq (x - y) := by
      dsimp only [difference]
      ring1

theorem sample_difference_le_inner (x : Gaussian) (unitInput : normSq x ≤ 1)
    (left right : Nat) :
    normSq (sample x left - sample x right) ≤
      normSq (horner x 2 left - horner x 2 right) := by
  rw [sample, sample, step_sub_step, normSq_scale, normSq_mul]
  have scalar : (1 / ((1 : Nat) : Coordinate)) ^ 2 = 1 := by decide
  rw [scalar, RFAP.ConstructiveFraction.one_mul]
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    unitInput (normSq_nonneg (horner x 2 left - horner x 2 right))
  simpa only [RFAP.ConstructiveFraction.one_mul] using scaled

theorem sample_later_close (x : Gaussian) (unitInput : normSq x ≤ 1)
    {earlier later : Nat} (order : earlier ≤ later) :
    normSq (sample x later - sample x earlier) ≤
      CCL.FiniteGeometric.quarterRadius 10 earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  calc
    normSq (sample x (earlier + extra) - sample x earlier) ≤
        normSq (horner x 2 (earlier + extra) - horner x 2 earlier) :=
      sample_difference_le_inner x unitInput _ _
    _ ≤ 10 * (1 / 4 : Coordinate) ^ earlier :=
      horner_add_depth_close x unitInput earlier extra 2 (by decide)
    _ = CCL.FiniteGeometric.quarterRadius 10 earlier :=
      (CCL.FiniteGeometric.quarterRadius_eq_mul_pow 10 earlier).symm

/-- Every displayed outer sample has a uniform finite center bound. -/
theorem sample_bounded (x : Gaussian) (unitInput : normSq x ≤ 1)
    (index : Nat) :
    normSq (sample x index) ≤ 10 := by
  have tailBound := horner_bounded x unitInput index 2 (by decide)
  have productBound : normSq (x * horner x 2 index) ≤ 4 := by
    rw [normSq_mul]
    have multiplied := RFAP.ConstructiveFraction.mul_le_mul_direct unitInput
      tailBound (normSq_nonneg (horner x 2 index))
      (by decide : (0 : Coordinate) ≤ 1)
    simpa only [RFAP.ConstructiveFraction.one_mul] using multiplied
  have scaledIdentity :
      scale (1 / ((1 : Nat) : Coordinate)) (x * horner x 2 index) =
        x * horner x 2 index := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [scale_re, scale_im] <;>
      change (1 / ((1 : Nat) : Coordinate)) * _ = _ <;>
      rw [show (1 / ((1 : Nat) : Coordinate)) = 1 by decide,
        RFAP.ConstructiveFraction.one_mul]
  rw [sample, step_eq, scaledIdentity]
  calc
    normSq (1 + x * horner x 2 index) ≤
        2 * (normSq (1 : Gaussian) + normSq (x * horner x 2 index)) :=
      normSq_add_le_two _ _
    _ ≤ 2 * (1 + 4) := by
      rw [normSq_one]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl productBound) (by decide)
    _ = 10 := by decide

/-- The finite Horner samples on the closed rational unit disk, packaged with
their rational squared-error sidecar. -/
def approximation (x : Gaussian) (unitInput : normSq x ≤ 1) : Approximation where
  sample := sample x
  radiusSq := CCL.FiniteGeometric.quarterRadius 10
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg (by decide)
  later_close := sample_later_close x unitInput
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow 10 current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge 10 current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate 10 (by decide)
  centerBound := 10
  centerBound_nonneg := by decide
  sample_bounded := sample_bounded x unitInput

def named (x : Gaussian) (unitInput : normSq x ≤ 1) : Named :=
  (approximation x unitInput).toNamed

/-- Every natural request returns exactly that many CCL bits.  Its sidecar
semantics ranges only over explicitly witnessed later finite Horner samples. -/
theorem productive (x : Gaussian) (unitInput : normSq x ≤ 1) (count : Nat) :
    (named x unitInput).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (named x unitInput).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (named x unitInput).machine count).emitted.length = count :=
  (approximation x unitInput).output_productive count

end CCL.FiniteExp
