import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Geometry.FiniteGeometric
import CCL.Progressive.Approximation

/-!
# Finite logarithm Horner approximation

For a displayed positive rational input in `[1/2,2]`, this module computes only
finite truncations of `2z(1 + z²/3 + z⁴/5 + ⋯)`, where
`z = (x - 1)/(x + 1)`.  The ellipsis is descriptive only: every definition
below is structural recursion with a natural depth, and every semantic
predicate has an explicit later finite index witness.  No completed logarithm,
infinite series, or limit is introduced.
-/

namespace CCL.FiniteLog

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation := CCL.ProgressiveApproximation.Approximation
abbrev Named := CCL.ProgressiveTransducer.Named

open RFAP.ConstructiveGaussian.Gaussian

def real (x : Coordinate) : Gaussian := ⟨x, 0⟩

theorem normSq_real_sub (x y : Coordinate) :
    normSq (real x - real y) = (x - y) ^ 2 := by
  change (x - y) ^ 2 + (0 - 0) ^ 2 = (x - y) ^ 2
  ring1

def reducedArgument (x : Coordinate) : Coordinate :=
  (x - 1) / (x + 1)

def squaredArgument (x : Coordinate) : Coordinate :=
  reducedArgument x ^ 2

theorem denominator_pos {x : Coordinate} (halfLe : 1 / 2 ≤ x) :
    0 < x + 1 := by
  exact add_pos_of_nonneg_of_pos
    ((by decide : (0 : Coordinate) ≤ 1 / 2).trans halfLe)
    (by decide)

theorem reducedArgument_le_third {x : Coordinate} (halfLe : 1 / 2 ≤ x)
    (leTwo : x ≤ 2) :
    reducedArgument x ≤ 1 / 3 := by
  apply (RFAP.ConstructiveFraction.div_le_iff_pos (denominator_pos halfLe)).mpr
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := (3 : Coordinate)) _ (by decide)
  have twice : 2 * x ≤ 2 * 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct leTwo (by decide)
  have rightCancel : (1 / 3 * (x + 1)) * (3 : Coordinate) = x + 1 := by
    calc
      (1 / 3 * (x + 1)) * (3 : Coordinate) =
          (x + 1) * ((1 / 3 : Coordinate) * 3) := by ring1
      _ = (x + 1) * 1 := by rw [show (1 / 3 : Coordinate) * 3 = 1 by decide]
      _ = x + 1 := RFAP.ConstructiveFraction.mul_one_direct _
  apply sub_nonneg.mp
  calc
    0 ≤ 2 * 2 - 2 * x := sub_nonneg.mpr twice
    _ = (x + 1) - (x - 1) * 3 := by ring1
    _ = (1 / 3 * (x + 1)) * 3 - (x - 1) * 3 := by rw [rightCancel]

theorem neg_third_le_reducedArgument {x : Coordinate} (halfLe : 1 / 2 ≤ x) :
    -(1 / 3 : Coordinate) ≤ reducedArgument x := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    (denominator_pos halfLe)).mpr
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := (3 : Coordinate)) _ (by decide)
  have scaledHalf := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    halfLe (by decide : (0 : Coordinate) ≤ 4)
  have twoLeFourX : (2 : Coordinate) ≤ 4 * x := by
    calc
      (2 : Coordinate) = 4 * (1 / 2) := by decide
      _ ≤ 4 * x := scaledHalf
  have leftCancel :
      (-(1 / 3 : Coordinate) * (x + 1)) * 3 = -(x + 1) := by
    calc
      (-(1 / 3 : Coordinate) * (x + 1)) * 3 =
          (x + 1) * (-(1 / 3 : Coordinate) * 3) := by ring1
      _ = (x + 1) * -1 := by
        rw [show -(1 / 3 : Coordinate) * 3 = -1 by decide]
      _ = -(x + 1) := by ring1
  apply sub_nonneg.mp
  calc
    0 ≤ 4 * x - 2 := sub_nonneg.mpr twoLeFourX
    _ = (x - 1) * 3 - -(x + 1) := by ring1
    _ = (x - 1) * 3 - (-(1 / 3 : Coordinate) * (x + 1)) * 3 := by
      rw [leftCancel]

theorem squaredArgument_nonneg (x : Coordinate) :
    0 ≤ squaredArgument x :=
  RFAP.ConstructiveFraction.sq_nonneg_direct (reducedArgument x)

theorem squaredArgument_le_ninth {x : Coordinate} (halfLe : 1 / 2 ≤ x)
    (leTwo : x ≤ 2) :
    squaredArgument x ≤ 1 / 9 := by
  have leftNonnegative : 0 ≤ reducedArgument x + 1 / 3 := by
    have shifted := add_le_add_right (neg_third_le_reducedArgument halfLe)
      (1 / 3 : Coordinate)
    calc
      0 = 1 / 3 + -(1 / 3 : Coordinate) := by ring1
      _ ≤ 1 / 3 + reducedArgument x := shifted
      _ = reducedArgument x + 1 / 3 := by ring1
  have rightNonnegative : 0 ≤ 1 / 3 - reducedArgument x :=
    sub_nonneg.mpr (reducedArgument_le_third halfLe leTwo)
  have productNonnegative := RFAP.ConstructiveFraction.mul_nonneg_direct
    leftNonnegative rightNonnegative
  apply sub_nonneg.mp
  calc
    0 ≤ (reducedArgument x + 1 / 3) *
        (1 / 3 - reducedArgument x) := productNonnegative
    _ = (1 / 3 : Coordinate) ^ 2 - reducedArgument x ^ 2 := by ring1
    _ = 1 / 9 - squaredArgument x := by
      rw [show (1 / 3 : Coordinate) ^ 2 = 1 / 9 by decide]
      rfl

def coefficient (index : Nat) : Coordinate :=
  (2 * (index : Coordinate) - 1) / (2 * (index : Coordinate) + 1)

theorem coefficient_nonneg {index : Nat} (positive : 1 ≤ index) :
    0 ≤ coefficient index := by
  have indexNonnegative : (0 : Coordinate) ≤ (index : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le index)
  have oneLeIndex : (1 : Coordinate) ≤ (index : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct positive
  have indexLeTwice : (index : Coordinate) ≤ 2 * (index : Coordinate) := by
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (by decide : (1 : Coordinate) ≤ 2) indexNonnegative
    simpa only [RFAP.ConstructiveFraction.one_mul] using scaled
  have numeratorNonnegative :
      0 ≤ 2 * (index : Coordinate) - 1 :=
    sub_nonneg.mpr (oneLeIndex.trans indexLeTwice)
  have denominatorNonnegative :
      0 ≤ 2 * (index : Coordinate) + 1 :=
    add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) indexNonnegative)
      (by decide)
  exact RFAP.ConstructiveFraction.div_nonneg_direct numeratorNonnegative
    denominatorNonnegative

theorem coefficient_le_one (index : Nat) :
    coefficient index ≤ 1 := by
  have indexNonnegative : (0 : Coordinate) ≤ (index : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le index)
  have denominatorPositive :
      0 < 2 * (index : Coordinate) + 1 :=
    add_pos_of_nonneg_of_pos
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) indexNonnegative)
      (by decide)
  apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).mpr
  rw [RFAP.ConstructiveFraction.one_mul]
  have constants : (-1 : Coordinate) ≤ 1 := by decide
  have shifted := add_le_add_left constants (2 * (index : Coordinate))
  calc
    2 * (index : Coordinate) - 1 = -1 + 2 * (index : Coordinate) := by ring1
    _ ≤ 1 + 2 * (index : Coordinate) := shifted
    _ = 2 * (index : Coordinate) + 1 := by ring1

def step (w : Coordinate) (index : Nat) (tail : Coordinate) : Coordinate :=
  RFAP.ConstructiveFraction.canonical (1 + coefficient index * w * tail)

theorem step_eq (w : Coordinate) (index : Nat) (tail : Coordinate) :
    step w index tail = 1 + coefficient index * w * tail :=
  RFAP.ConstructiveFraction.canonical_eq _

def horner (w : Coordinate) : Nat → Nat → Coordinate
  | _, 0 => 1
  | index, depth + 1 => step w index (horner w (index + 1) depth)

@[simp] theorem horner_zero (w : Coordinate) (index : Nat) :
    horner w index 0 = 1 := rfl

@[simp] theorem horner_succ (w : Coordinate) (index depth : Nat) :
    horner w index (depth + 1) =
      step w index (horner w (index + 1) depth) := rfl

theorem coefficient_mul_le_ninth {w : Coordinate} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) (index : Nat) :
    coefficient index * w ≤ 1 / 9 := by
  have multiplied := RFAP.ConstructiveFraction.mul_le_mul_direct
    (coefficient_le_one index) wLe wNonnegative
    (by decide : (0 : Coordinate) ≤ 1)
  simpa only [RFAP.ConstructiveFraction.one_mul] using multiplied

theorem coefficient_mul_nonneg {w : Coordinate} (wNonnegative : 0 ≤ w)
    {index : Nat} (positive : 1 ≤ index) :
    0 ≤ coefficient index * w :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (coefficient_nonneg positive) wNonnegative

theorem step_bounds {w : Coordinate} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) {index : Nat} (positive : 1 ≤ index)
    {tail : Coordinate} (tailLower : 1 ≤ tail) (tailUpper : tail ≤ 2) :
    1 ≤ step w index tail ∧ step w index tail ≤ 2 := by
  rw [step_eq]
  have coefficientWNonnegative := coefficient_mul_nonneg wNonnegative positive
  have termNonnegative : 0 ≤ coefficient index * w * tail :=
    RFAP.ConstructiveFraction.mul_nonneg_direct coefficientWNonnegative
      ((by decide : (0 : Coordinate) ≤ 1).trans tailLower)
  have termUpper : coefficient index * w * tail ≤ (1 / 9 : Coordinate) * 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_direct
      (coefficient_mul_le_ninth wNonnegative wLe index) tailUpper
      ((by decide : (0 : Coordinate) ≤ 1).trans tailLower)
      (by decide)
  constructor
  · calc
      1 = 0 + 1 := by ring1
      _ ≤ coefficient index * w * tail + 1 :=
        add_le_add_left termNonnegative 1
      _ = 1 + coefficient index * w * tail := by ring1
  · calc
      1 + coefficient index * w * tail = coefficient index * w * tail + 1 := by ring1
      _ ≤ (1 / 9 : Coordinate) * 2 + 1 := add_le_add_left termUpper 1
      _ = 1 + (1 / 9 : Coordinate) * 2 := by ring1
      _ ≤ 2 := by decide

theorem horner_bounds {w : Coordinate} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) :
    ∀ (depth index : Nat), 1 ≤ index →
      1 ≤ horner w index depth ∧ horner w index depth ≤ 2
  | 0, _, _ => by
      rw [horner_zero]
      exact ⟨le_rfl, by decide⟩
  | depth + 1, index, positive => by
      rw [horner_succ]
      have tail := horner_bounds wNonnegative wLe depth (index + 1) (by omega)
      exact step_bounds wNonnegative wLe positive tail.1 tail.2

theorem step_sub_step (w : Coordinate) (index : Nat) (left right : Coordinate) :
    step w index left - step w index right =
      (coefficient index * w) * (left - right) := by
  rw [step_eq, step_eq]
  ring1

theorem coefficient_mul_sq_le_quarter {w : Coordinate}
    (wNonnegative : 0 ≤ w) (wLe : w ≤ 1 / 9)
    {index : Nat} (positive : 1 ≤ index) :
    (coefficient index * w) ^ 2 ≤ 1 / 4 := by
  calc
    (coefficient index * w) ^ 2 ≤ (1 / 9 : Coordinate) ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct
        (coefficient_mul_nonneg wNonnegative positive)
        (coefficient_mul_le_ninth wNonnegative wLe index) 2
    _ ≤ 1 / 4 := by decide

theorem step_difference_contract {w : Coordinate} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) {index : Nat} (positive : 1 ≤ index)
    (left right : Coordinate) :
    (step w index left - step w index right) ^ 2 ≤
      (1 / 4 : Coordinate) * (left - right) ^ 2 := by
  rw [step_sub_step, mul_pow]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    (coefficient_mul_sq_le_quarter wNonnegative wLe positive)
    (RFAP.ConstructiveFraction.sq_nonneg_direct (left - right))

theorem horner_sub_one_sq_le_one {w : Coordinate} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) (depth index : Nat) (positive : 1 ≤ index) :
    (horner w index depth - 1) ^ 2 ≤ 1 := by
  have bounds := horner_bounds wNonnegative wLe depth index positive
  have differenceNonnegative : 0 ≤ horner w index depth - 1 :=
    sub_nonneg.mpr bounds.1
  have differenceLe : horner w index depth - 1 ≤ 1 := by
    have shifted := add_le_add_right bounds.2 (-1)
    calc
      horner w index depth - 1 = -1 + horner w index depth := by ring1
      _ ≤ -1 + 2 := shifted
      _ = 1 := by ring1
  have squared := RFAP.ConstructiveFraction.pow_le_pow_direct
    differenceNonnegative differenceLe 2
  simpa only [one_pow] using squared

theorem horner_add_depth_close {w : Coordinate} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) :
    ∀ (earlier extra index : Nat), 1 ≤ index →
      (horner w index (earlier + extra) - horner w index earlier) ^ 2 ≤
        (1 / 4 : Coordinate) ^ earlier
  | 0, extra, index, positive => by
      simp only [Nat.zero_add, horner_zero, pow_zero]
      exact horner_sub_one_sq_le_one wNonnegative wLe extra index positive
  | earlier + 1, extra, index, positive => by
      rw [show earlier + 1 + extra = (earlier + extra) + 1 by ring1,
        horner_succ, horner_succ]
      calc
        (step w index (horner w (index + 1) (earlier + extra)) -
            step w index (horner w (index + 1) earlier)) ^ 2 ≤
          (1 / 4 : Coordinate) *
            (horner w (index + 1) (earlier + extra) -
              horner w (index + 1) earlier) ^ 2 :=
          step_difference_contract wNonnegative wLe positive _ _
        _ ≤ (1 / 4 : Coordinate) * (1 / 4 : Coordinate) ^ earlier :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (horner_add_depth_close wNonnegative wLe earlier extra
              (index + 1) (Nat.succ_le_succ (Nat.zero_le index))) (by decide)
        _ = (1 / 4 : Coordinate) ^ (earlier + 1) := by
          rw [pow_succ]
          ring1

def outputFactor (x : Coordinate) : Coordinate := 2 * reducedArgument x

theorem outputFactor_sq_le_one {x : Coordinate} (halfLe : 1 / 2 ≤ x)
    (leTwo : x ≤ 2) :
    outputFactor x ^ 2 ≤ 1 := by
  calc
    outputFactor x ^ 2 = 4 * squaredArgument x := by
      rw [outputFactor, squaredArgument]
      ring1
    _ ≤ 4 * (1 / 9 : Coordinate) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (squaredArgument_le_ninth halfLe leTwo) (by decide)
    _ ≤ 1 := by decide

def sampleCoordinate (x : Coordinate) (index : Nat) : Coordinate :=
  RFAP.ConstructiveFraction.canonical
    (outputFactor x * horner (squaredArgument x) 1 index)

theorem sampleCoordinate_eq (x : Coordinate) (index : Nat) :
    sampleCoordinate x index =
      outputFactor x * horner (squaredArgument x) 1 index :=
  RFAP.ConstructiveFraction.canonical_eq _

def sample (x : Coordinate) (index : Nat) : Gaussian :=
  real (sampleCoordinate x index)

theorem sample_difference_le_inner {x : Coordinate} (halfLe : 1 / 2 ≤ x)
    (leTwo : x ≤ 2) (left right : Nat) :
    normSq (sample x left - sample x right) ≤
      (horner (squaredArgument x) 1 left -
        horner (squaredArgument x) 1 right) ^ 2 := by
  rw [sample, sample, normSq_real_sub, sampleCoordinate_eq, sampleCoordinate_eq]
  have factorSq : outputFactor x ^ 2 ≤ 1 :=
    outputFactor_sq_le_one halfLe leTwo
  rw [show outputFactor x * horner (squaredArgument x) 1 left -
      outputFactor x * horner (squaredArgument x) 1 right =
      outputFactor x * (horner (squaredArgument x) 1 left -
        horner (squaredArgument x) 1 right) by ring1,
    mul_pow]
  have multiplied := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    factorSq
    (RFAP.ConstructiveFraction.sq_nonneg_direct
      (horner (squaredArgument x) 1 left -
        horner (squaredArgument x) 1 right))
  simpa only [RFAP.ConstructiveFraction.one_mul] using multiplied

theorem sample_later_close {x : Coordinate} (halfLe : 1 / 2 ≤ x)
    (leTwo : x ≤ 2)
    {earlier later : Nat} (order : earlier ≤ later) :
    normSq (sample x later - sample x earlier) ≤
      CCL.FiniteGeometric.quarterRadius 1 earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  calc
    normSq (sample x (earlier + extra) - sample x earlier) ≤
        (horner (squaredArgument x) 1 (earlier + extra) -
          horner (squaredArgument x) 1 earlier) ^ 2 :=
      sample_difference_le_inner halfLe leTwo _ _
    _ ≤ (1 / 4 : Coordinate) ^ earlier :=
      horner_add_depth_close (squaredArgument_nonneg x)
        (squaredArgument_le_ninth halfLe leTwo) earlier extra 1 (by decide)
    _ = CCL.FiniteGeometric.quarterRadius 1 earlier := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        RFAP.ConstructiveFraction.one_mul]

theorem sample_bounded {x : Coordinate} (halfLe : 1 / 2 ≤ x) (leTwo : x ≤ 2)
    (index : Nat) : normSq (sample x index) ≤ 4 := by
  have inner := horner_bounds (squaredArgument_nonneg x)
    (squaredArgument_le_ninth halfLe leTwo) index 1 (by decide)
  have innerSq : horner (squaredArgument x) 1 index ^ 2 ≤ 4 := by
    calc
      horner (squaredArgument x) 1 index ^ 2 ≤ (2 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct
          ((by decide : (0 : Coordinate) ≤ 1).trans inner.1) inner.2 2
      _ = 4 := by decide
  have innerSqNonnegative :
      0 ≤ horner (squaredArgument x) 1 index ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  rw [sample, normSq]
  change sampleCoordinate x index ^ 2 + 0 ^ 2 ≤ 4
  rw [sampleCoordinate_eq]
  calc
    (outputFactor x * horner (squaredArgument x) 1 index) ^ 2 + 0 ^ 2 =
        (outputFactor x * horner (squaredArgument x) 1 index) ^ 2 := by ring1
    _ = outputFactor x ^ 2 * horner (squaredArgument x) 1 index ^ 2 := by
      rw [mul_pow]
    _ ≤ 1 * 4 :=
      RFAP.ConstructiveFraction.mul_le_mul_direct
        (outputFactor_sq_le_one halfLe leTwo) innerSq
        innerSqNonnegative
        (by decide)
    _ = 4 := by decide

def approximation (x : Coordinate) (halfLe : 1 / 2 ≤ x) (leTwo : x ≤ 2) :
    Approximation where
  sample := sample x
  radiusSq := CCL.FiniteGeometric.quarterRadius 1
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg (by decide)
  later_close := sample_later_close halfLe leTwo
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow 1 current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge 1 current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate 1 (by decide)
  centerBound := 4
  centerBound_nonneg := by decide
  sample_bounded := sample_bounded halfLe leTwo

def named (x : Coordinate) (halfLe : 1 / 2 ≤ x) (leTwo : x ≤ 2) : Named :=
  (approximation x halfLe leTwo).toNamed

theorem productive (x : Coordinate) (halfLe : 1 / 2 ≤ x) (leTwo : x ≤ 2)
    (count : Nat) :
    (named x halfLe leTwo).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (named x halfLe leTwo).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (named x halfLe leTwo).machine count).emitted.length = count :=
  (approximation x halfLe leTwo).output_productive count

end CCL.FiniteLog
