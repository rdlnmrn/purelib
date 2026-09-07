import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Transcendental.FiniteLogSensitivity

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

namespace CCL.FiniteComplexLog

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian

def scalar (value : Coordinate) : Gaussian := ⟨value, 0⟩

@[simp] theorem normSq_scalar (value : Coordinate) :
    normSq (scalar value) = value ^ 2 := by
  change value ^ 2 + 0 ^ 2 = value ^ 2
  ring1

def coefficient (index : Nat) : Coordinate :=
  CCL.FiniteLog.coefficient index

theorem coefficient_nonneg {index : Nat} (positive : 1 ≤ index) :
    0 ≤ coefficient index :=
  CCL.FiniteLog.coefficient_nonneg positive

theorem coefficient_le_one (index : Nat) : coefficient index ≤ 1 :=
  CCL.FiniteLog.coefficient_le_one index

theorem coefficient_sq_le_one {index : Nat} (positive : 1 ≤ index) :
    coefficient index ^ 2 ≤ 1 := by
  have squared := RFAP.ConstructiveFraction.pow_le_pow_direct
    (coefficient_nonneg positive) (coefficient_le_one index) 2
  simpa only [one_pow] using squared

def step (w : Gaussian) (index : Nat) (tail : Gaussian) : Gaussian :=
  canonical (1 + scalar (coefficient index) * w * tail)

theorem step_eq (w : Gaussian) (index : Nat) (tail : Gaussian) :
    step w index tail = 1 + scalar (coefficient index) * w * tail :=
  canonical_eq _

def horner (w : Gaussian) : Nat → Nat → Gaussian
  | _, 0 => 1
  | index, depth + 1 => step w index (horner w (index + 1) depth)

@[simp] theorem horner_zero (w : Gaussian) (index : Nat) :
    horner w index 0 = 1 := rfl

@[simp] theorem horner_succ (w : Gaussian) (index depth : Nat) :
    horner w index (depth + 1) =
      step w index (horner w (index + 1) depth) := rfl

theorem scaled_term_bound {w tail : Gaussian} {index : Nat}
    (positive : 1 ≤ index) (wBound : normSq w ≤ 1 / 9)
    (tailBound : normSq tail ≤ 4) :
    normSq (scalar (coefficient index) * w * tail) ≤ 4 / 9 := by
  rw [normSq_mul, normSq_mul, normSq_scalar]
  calc
    coefficient index ^ 2 * normSq w * normSq tail ≤
        1 * (1 / 9 : Coordinate) * 4 :=
      RFAP.ConstructiveFraction.mul_le_mul_direct
        (RFAP.ConstructiveFraction.mul_le_mul_direct
          (coefficient_sq_le_one positive) wBound
          (normSq_nonneg w) (by decide))
        tailBound (normSq_nonneg tail)
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))
    _ = 4 / 9 := by decide

theorem step_bound {w tail : Gaussian} {index : Nat}
    (positive : 1 ≤ index) (wBound : normSq w ≤ 1 / 9)
    (tailBound : normSq tail ≤ 4) :
    normSq (step w index tail) ≤ 4 := by
  rw [step_eq]
  calc
    normSq (1 + scalar (coefficient index) * w * tail) ≤
        2 * (normSq 1 + normSq (scalar (coefficient index) * w * tail)) :=
      normSq_add_le_two _ _
    _ ≤ 2 * ((1 : Coordinate) + 4 / 9) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl (scaled_term_bound positive wBound tailBound))
        (by decide)
    _ ≤ 4 := by decide

/-- A square-root-free weighted triangle estimate specialized to the ratio
needed by the sharper local-log bound. -/
theorem normSq_add_le_three_one_and_half (u v : Gaussian) :
    normSq (u + v) ≤ 3 * normSq u + (3 / 2) * normSq v := by
  let difference :=
    3 * normSq u + (3 / 2) * normSq v - normSq (u + v)
  let scalarTwo : Gaussian := ⟨2, 0⟩
  have coefficient : (2 : Coordinate) * (3 / 2) = 3 := by
    calc
      (2 : Coordinate) * (3 / 2) = (3 / 2) * 2 :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ = 3 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne 3 2 (by decide)
  have scaledIdentity :
      2 * difference = normSq (scalarTwo * u - v) := by
    calc
      2 * difference =
          6 * normSq u + (2 * (3 / 2)) * normSq v -
            2 * normSq (u + v) := by
        dsimp only [difference]
        ring1
      _ = 6 * normSq u + 3 * normSq v - 2 * normSq (u + v) := by
        rw [coefficient]
      _ = normSq (scalarTwo * u - v) := by
        dsimp only [scalarTwo, normSq]
        simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im]
        ring1
  have scaledNonnegative : 0 ≤ 2 * difference := by
    rw [scaledIdentity]
    exact normSq_nonneg _
  have differenceNonnegative : 0 ≤ difference := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (2 : Coordinate)) _ (by decide)
    calc
      0 * 2 = 0 := by ring1
      _ ≤ 2 * difference := scaledNonnegative
      _ = difference * 2 := RFAP.ConstructiveFraction.mul_comm _ _
  apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
    (c := -normSq (u + v))
  calc
    normSq (u + v) + -normSq (u + v) = 0 := by ring1
    _ ≤ difference := differenceNonnegative
    _ = (3 * normSq u + (3 / 2) * normSq v) +
        -normSq (u + v) := by
      dsimp only [difference]
      ring1

theorem scaled_term_bound_quarter {w tail : Gaussian} {index : Nat}
    (positive : 1 ≤ index) (wBound : normSq w ≤ 1 / 9)
    (tailBound : normSq tail ≤ 9 / 4) :
    normSq (scalar (coefficient index) * w * tail) ≤ 1 / 4 := by
  rw [normSq_mul, normSq_mul, normSq_scalar]
  calc
    coefficient index ^ 2 * normSq w * normSq tail ≤
        1 * (1 / 9 : Coordinate) * (9 / 4) :=
      RFAP.ConstructiveFraction.mul_le_mul_direct
        (RFAP.ConstructiveFraction.mul_le_mul_direct
          (coefficient_sq_le_one positive) wBound
          (normSq_nonneg w) (by decide))
        tailBound (normSq_nonneg tail)
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))
    _ = 1 / 4 := by decide

theorem step_bound_nine_four {w tail : Gaussian} {index : Nat}
    (positive : 1 ≤ index) (wBound : normSq w ≤ 1 / 9)
    (tailBound : normSq tail ≤ 9 / 4) :
    normSq (step w index tail) ≤ 9 / 4 := by
  rw [step_eq, RFAP.ConstructiveGaussian.Gaussian.add_comm]
  calc
    normSq (scalar (coefficient index) * w * tail + 1) ≤
        3 * normSq (scalar (coefficient index) * w * tail) +
          (3 / 2) * normSq 1 :=
      normSq_add_le_three_one_and_half _ _
    _ ≤ 3 * (1 / 4 : Coordinate) + (3 / 2) * 1 :=
      add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (scaled_term_bound_quarter positive wBound tailBound) (by decide))
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (by rw [normSq_one]) (by decide))
    _ = 9 / 4 := by decide

theorem horner_bound_nine_four {w : Gaussian}
    (wBound : normSq w ≤ 1 / 9) :
    ∀ (depth index : Nat), 1 ≤ index →
      normSq (horner w index depth) ≤ 9 / 4
  | 0, _, _ => by rw [horner_zero, normSq_one]; decide
  | depth + 1, index, positive => by
      rw [horner_succ]
      exact step_bound_nine_four positive wBound
        (horner_bound_nine_four wBound depth (index + 1) (by omega))

theorem horner_bound {w : Gaussian} (wBound : normSq w ≤ 1 / 9) :
    ∀ (depth index : Nat), 1 ≤ index → normSq (horner w index depth) ≤ 4
  | 0, _, _ => by rw [horner_zero, normSq_one]; decide
  | depth + 1, index, positive => by
      rw [horner_succ]
      exact step_bound positive wBound
        (horner_bound wBound depth (index + 1) (by omega))

theorem step_sub_step (w : Gaussian) (index : Nat) (left right : Gaussian) :
    step w index left - step w index right =
      scalar (coefficient index) * w * (left - right) := by
  rw [step_eq, step_eq]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im,
      scalar, one_re, one_im] <;> ring1

theorem step_difference_contract {w : Gaussian} (wBound : normSq w ≤ 1 / 9)
    {index : Nat} (positive : 1 ≤ index) (left right : Gaussian) :
    normSq (step w index left - step w index right) ≤
      (1 / 4 : Coordinate) * normSq (left - right) := by
  rw [step_sub_step, normSq_mul, normSq_mul, normSq_scalar]
  have factorBound : coefficient index ^ 2 * normSq w ≤ 1 / 4 := by
    calc
      coefficient index ^ 2 * normSq w ≤ 1 * (1 / 9 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_le_mul_direct
          (coefficient_sq_le_one positive) wBound
          (normSq_nonneg w) (by decide)
      _ ≤ 1 / 4 := by decide
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    factorBound (normSq_nonneg (left - right))

theorem horner_sub_one_bound {w : Gaussian} (wBound : normSq w ≤ 1 / 9)
    (depth index : Nat) (positive : 1 ≤ index) :
    normSq (horner w index depth - 1) ≤ 10 := by
  exact (normSq_sub_le_two _ _).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add (horner_bound wBound depth index positive) le_rfl)
      (by decide))

theorem horner_add_depth_close {w : Gaussian} (wBound : normSq w ≤ 1 / 9) :
    ∀ (earlier extra index : Nat), 1 ≤ index →
      normSq (horner w index (earlier + extra) - horner w index earlier) ≤
        10 * (1 / 4 : Coordinate) ^ earlier
  | 0, extra, index, positive => by
      simp only [Nat.zero_add, horner_zero, pow_zero,
        RFAP.ConstructiveFraction.mul_one_direct]
      exact horner_sub_one_bound wBound extra index positive
  | earlier + 1, extra, index, positive => by
      rw [show earlier + 1 + extra = (earlier + extra) + 1 by ring1,
        horner_succ, horner_succ]
      exact (step_difference_contract wBound positive _ _).trans (by
        have previous := horner_add_depth_close wBound earlier extra
          (index + 1) (positive.trans (Nat.le_add_right index 1))
        calc
          (1 / 4 : Coordinate) *
              normSq
                (horner w (index + 1) (earlier + extra) -
                  horner w (index + 1) earlier) ≤
              (1 / 4 : Coordinate) *
                (10 * (1 / 4 : Coordinate) ^ earlier) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct previous
              (by decide)
          _ = 10 * (1 / 4 : Coordinate) ^ (earlier + 1) := by
            rw [pow_succ]
            ring1)

def squaredArgument (z : Gaussian) : Gaussian := canonical (z * z)

theorem squaredArgument_eq (z : Gaussian) : squaredArgument z = z * z :=
  canonical_eq _

theorem squaredArgument_bound {z : Gaussian} (zBound : normSq z ≤ 1 / 9) :
    normSq (squaredArgument z) ≤ 1 / 9 := by
  rw [squaredArgument_eq, normSq_mul]
  calc
    normSq z * normSq z ≤ (1 / 9 : Coordinate) * (1 / 9) :=
      RFAP.ConstructiveFraction.mul_le_mul_direct zBound zBound
        (normSq_nonneg z) (by decide)
    _ ≤ 1 / 9 := by decide

def outputFactor (z : Gaussian) : Gaussian :=
  canonical (scalar 2 * z)

theorem outputFactor_eq (z : Gaussian) : outputFactor z = scalar 2 * z :=
  canonical_eq _

theorem outputFactor_bound {z : Gaussian} (zBound : normSq z ≤ 1 / 9) :
    normSq (outputFactor z) ≤ 1 := by
  rw [outputFactor_eq, normSq_mul, normSq_scalar]
  calc
    (2 : Coordinate) ^ 2 * normSq z ≤ 4 * (1 / 9 : Coordinate) := by
      rw [show (2 : Coordinate) ^ 2 = 4 by decide]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct zBound
        (by decide)
    _ ≤ 1 := by decide

theorem outputFactor_bound_four_ninth {z : Gaussian}
    (zBound : normSq z ≤ 1 / 9) :
    normSq (outputFactor z) ≤ 4 / 9 := by
  rw [outputFactor_eq, normSq_mul, normSq_scalar]
  calc
    (2 : Coordinate) ^ 2 * normSq z ≤ 4 * (1 / 9 : Coordinate) := by
      rw [show (2 : Coordinate) ^ 2 = 4 by decide]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct zBound
        (by decide)
    _ = 4 / 9 := by decide

def sample (z : Gaussian) (depth : Nat) : Gaussian :=
  canonical (outputFactor z * horner (squaredArgument z) 1 depth)

theorem sample_eq (z : Gaussian) (depth : Nat) :
    sample z depth = outputFactor z * horner (squaredArgument z) 1 depth :=
  canonical_eq _

theorem sample_bounded {z : Gaussian} (zBound : normSq z ≤ 1 / 9)
    (depth : Nat) : normSq (sample z depth) ≤ 4 := by
  rw [sample_eq, normSq_mul]
  calc
    normSq (outputFactor z) *
        normSq (horner (squaredArgument z) 1 depth) ≤ 1 * 4 :=
      RFAP.ConstructiveFraction.mul_le_mul_direct
        (outputFactor_bound zBound)
        (horner_bound (squaredArgument_bound zBound) depth 1 (by decide))
        (normSq_nonneg _)
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 1) (by decide)).le
    _ = 4 := RFAP.ConstructiveFraction.one_mul _

/-- Sharper bound: every displayed local complex-log truncation lies in the
closed unit disk. -/
theorem sample_bounded_one {z : Gaussian} (zBound : normSq z ≤ 1 / 9)
    (depth : Nat) : normSq (sample z depth) ≤ 1 := by
  rw [sample_eq, normSq_mul]
  calc
    normSq (outputFactor z) *
        normSq (horner (squaredArgument z) 1 depth) ≤
      (4 / 9 : Coordinate) * (9 / 4) :=
        RFAP.ConstructiveFraction.mul_le_mul_direct
          (outputFactor_bound_four_ninth zBound)
          (horner_bound_nine_four (squaredArgument_bound zBound)
            depth 1 (by decide))
          (normSq_nonneg _) (by decide)
    _ = 1 := by decide

theorem sample_later_close {z : Gaussian} (zBound : normSq z ≤ 1 / 9)
    {earlier later : Nat} (order : earlier ≤ later) :
    normSq (sample z later - sample z earlier) ≤
      5 * (1 / 4 : Coordinate) ^ earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [sample_eq, sample_eq]
  have identity :
      outputFactor z * horner (squaredArgument z) 1 (earlier + extra) -
          outputFactor z * horner (squaredArgument z) 1 earlier =
        outputFactor z *
          (horner (squaredArgument z) 1 (earlier + extra) -
            horner (squaredArgument z) 1 earlier) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
  rw [identity, normSq_mul]
  calc
    normSq (outputFactor z) *
        normSq
          (horner (squaredArgument z) 1 (earlier + extra) -
            horner (squaredArgument z) 1 earlier) ≤
        (4 / 9 : Coordinate) *
          (10 * (1 / 4 : Coordinate) ^ earlier) := by
      apply RFAP.ConstructiveFraction.mul_le_mul_direct
      · rw [outputFactor_eq, normSq_mul, normSq_scalar]
        calc
          (2 : Coordinate) ^ 2 * normSq z ≤ 4 * (1 / 9 : Coordinate) := by
            rw [show (2 : Coordinate) ^ 2 = 4 by decide]
            exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              zBound (by decide)
          _ = 4 / 9 := by decide
      · exact horner_add_depth_close (squaredArgument_bound zBound)
          earlier extra 1 (by decide)
      · exact normSq_nonneg _
      · decide
    _ ≤ 5 * (1 / 4 : Coordinate) ^ earlier := by
      have powerNonnegative :
          0 ≤ (1 / 4 : Coordinate) ^ earlier :=
        RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) earlier
      calc
        (4 / 9 : Coordinate) *
            (10 * (1 / 4 : Coordinate) ^ earlier) =
            (40 / 9 : Coordinate) * (1 / 4 : Coordinate) ^ earlier := by
          calc
            (4 / 9 : Coordinate) *
                (10 * (1 / 4 : Coordinate) ^ earlier) =
                ((4 / 9 : Coordinate) * 10) *
                  (1 / 4 : Coordinate) ^ earlier := by
              rw [RFAP.ConstructiveFraction.mul_assoc]
            _ = (40 / 9 : Coordinate) *
                  (1 / 4 : Coordinate) ^ earlier := by
              rw [show (4 / 9 : Coordinate) * 10 = 40 / 9 by
                rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
                  RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
                ring1]
        _ ≤ 5 * (1 / 4 : Coordinate) ^ earlier :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (by
              apply (RFAP.ConstructiveFraction.div_le_iff_pos
                (RFAP.ConstructiveFraction.natCast_pos_direct
                  (n := 9) (by decide))).2
              calc
                (40 : Coordinate) ≤ 45 :=
                  RFAP.ConstructiveFraction.natCast_le_direct (by decide)
                _ = 5 * 9 := by ring1)
            powerNonnegative

theorem step_inputs_sub (w v : Gaussian) (index : Nat)
    (wTail vTail : Gaussian) :
    step w index wTail - step v index vTail =
      scalar (coefficient index) *
        ((w - v) * wTail + v * (wTail - vTail)) := by
  rw [step_eq, step_eq]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im,
      scalar, one_re, one_im] <;> ring1

def hornerInputScale : Coordinate := 16

theorem horner_input_close {w v : Gaussian}
    (wBound : normSq w ≤ 1 / 9) (vBound : normSq v ≤ 1 / 9) :
    ∀ (depth index : Nat), 1 ≤ index →
      normSq (horner w index depth - horner v index depth) ≤
        hornerInputScale * normSq (w - v)
  | 0, _, _ => by
      rw [horner_zero, horner_zero, sub_self, normSq_zero]
      exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (normSq_nonneg (w - v))
  | depth + 1, index, positive => by
      rw [horner_succ, horner_succ, step_inputs_sub, normSq_mul,
        normSq_scalar]
      let wTail := horner w (index + 1) depth
      let vTail := horner v (index + 1) depth
      let difference := normSq (w - v)
      have firstBound : normSq ((w - v) * wTail) ≤ 4 * difference := by
        rw [normSq_mul]
        calc
          normSq (w - v) * normSq wTail ≤ difference * 4 :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (horner_bound wBound depth (index + 1) (by omega))
              (normSq_nonneg (w - v))
          _ = 4 * difference :=
            RFAP.ConstructiveFraction.mul_comm _ _
      have tailDifference : normSq (wTail - vTail) ≤
          hornerInputScale * difference :=
        horner_input_close wBound vBound depth (index + 1) (by omega)
      have secondBound : normSq (v * (wTail - vTail)) ≤
          2 * difference := by
        rw [normSq_mul]
        calc
          normSq v * normSq (wTail - vTail) ≤
              (1 / 9 : Coordinate) * (hornerInputScale * difference) :=
            RFAP.ConstructiveFraction.mul_le_mul_direct vBound tailDifference
              (normSq_nonneg _) (by decide)
          _ ≤ 2 * difference := by
            rw [hornerInputScale]
            have nonnegative : 0 ≤ difference := normSq_nonneg _
            calc
              (1 / 9 : Coordinate) * (16 * difference) =
                  ((1 / 9 : Coordinate) * 16) * difference := by
                rw [RFAP.ConstructiveFraction.mul_assoc]
              _ = (16 / 9 : Coordinate) * difference := by
                rw [show (1 / 9 : Coordinate) * 16 = 16 / 9 by decide]
              _ ≤ 2 * difference :=
                RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
                  (by decide) nonnegative
      have sumBound :
          normSq ((w - v) * wTail + v * (wTail - vTail)) ≤
            hornerInputScale * difference := by
        calc
          normSq ((w - v) * wTail + v * (wTail - vTail)) ≤
              2 * (normSq ((w - v) * wTail) +
                normSq (v * (wTail - vTail))) := normSq_add_le_two _ _
          _ ≤ 2 * (4 * difference + 2 * difference) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add firstBound secondBound) (by decide)
          _ ≤ hornerInputScale * difference := by
            rw [hornerInputScale]
            have nonnegative : 0 ≤ difference := normSq_nonneg _
            calc
              2 * (4 * difference + 2 * difference) = 12 * difference := by
                ring1
              _ ≤ 16 * difference :=
                RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
                  (by decide) nonnegative
      have multiplied := RFAP.ConstructiveFraction.mul_le_mul_direct
        (coefficient_sq_le_one positive) sumBound
        (normSq_nonneg _) (by decide : (0 : Coordinate) ≤ 1)
      simpa only [RFAP.ConstructiveFraction.one_mul] using multiplied

theorem squaredArgument_sub {z y : Gaussian} :
    squaredArgument z - squaredArgument y = (z - y) * (z + y) := by
  rw [squaredArgument_eq, squaredArgument_eq]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1

theorem squaredArgument_input_close {z y : Gaussian}
    (zBound : normSq z ≤ 1 / 9) (yBound : normSq y ≤ 1 / 9) :
    normSq (squaredArgument z - squaredArgument y) ≤ normSq (z - y) := by
  rw [squaredArgument_sub, normSq_mul]
  have sumBound : normSq (z + y) ≤ 1 := by
    calc
      normSq (z + y) ≤ 2 * (normSq z + normSq y) :=
        normSq_add_le_two _ _
      _ ≤ 2 * ((1 / 9 : Coordinate) + 1 / 9) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add zBound yBound) (by decide)
      _ ≤ 1 := by decide
  simpa only [RFAP.ConstructiveFraction.mul_one_direct] using
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct sumBound
      (normSq_nonneg (z - y))

def sampleInputScale : Coordinate := 2 * (16 + 16)

theorem sampleInputScale_nonneg : 0 ≤ sampleInputScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (by decide))

theorem sample_input_close {z y : Gaussian}
    (zBound : normSq z ≤ 1 / 9) (yBound : normSq y ≤ 1 / 9)
    (depth : Nat) :
    normSq (sample z depth - sample y depth) ≤
      sampleInputScale * normSq (z - y) := by
  rw [sample_eq, sample_eq]
  let zTail := horner (squaredArgument z) 1 depth
  let yTail := horner (squaredArgument y) 1 depth
  let difference := normSq (z - y)
  have factorDifference :
      normSq (outputFactor z - outputFactor y) ≤ 4 * difference := by
    rw [outputFactor_eq, outputFactor_eq]
    have identity : scalar 2 * z - scalar 2 * y = scalar 2 * (z - y) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im, scalar] <;> ring1
    rw [identity, normSq_mul, normSq_scalar]
    change (2 : Coordinate) ^ 2 * normSq (z - y) ≤ 4 * difference
    rw [show (2 : Coordinate) ^ 2 = 4 by decide]
  have zTailBound : normSq zTail ≤ 4 :=
    horner_bound (squaredArgument_bound zBound) depth 1 (by decide)
  have tailDifference : normSq (zTail - yTail) ≤
      hornerInputScale * difference :=
    (horner_input_close (squaredArgument_bound zBound)
      (squaredArgument_bound yBound) depth 1 (by decide)).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (squaredArgument_input_close zBound yBound) (by decide))
  have firstBound :
      normSq ((outputFactor z - outputFactor y) * zTail) ≤
        16 * difference := by
    rw [normSq_mul]
    calc
      normSq (outputFactor z - outputFactor y) * normSq zTail ≤
          (4 * difference) * 4 :=
        RFAP.ConstructiveFraction.mul_le_mul_direct factorDifference zTailBound
          (normSq_nonneg _) (by
            exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              (normSq_nonneg _))
      _ = 16 * difference := by ring1
  have secondBound :
      normSq (outputFactor y * (zTail - yTail)) ≤ 16 * difference := by
    rw [normSq_mul]
    have multiplied := RFAP.ConstructiveFraction.mul_le_mul_direct
      (outputFactor_bound yBound) tailDifference (normSq_nonneg _)
      (by decide : (0 : Coordinate) ≤ 1)
    simpa only [hornerInputScale, RFAP.ConstructiveFraction.one_mul]
      using multiplied
  have identity : outputFactor z * zTail - outputFactor y * yTail =
      (outputFactor z - outputFactor y) * zTail +
        outputFactor y * (zTail - yTail) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
  rw [identity]
  calc
    normSq ((outputFactor z - outputFactor y) * zTail +
        outputFactor y * (zTail - yTail)) ≤
      2 * (normSq ((outputFactor z - outputFactor y) * zTail) +
        normSq (outputFactor y * (zTail - yTail))) := normSq_add_le_two _ _
    _ ≤ 2 * (16 * difference + 16 * difference) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstBound secondBound) (by decide)
    _ = sampleInputScale * normSq (z - y) := by
      rw [sampleInputScale]
      ring1

end CCL.FiniteComplexLog
