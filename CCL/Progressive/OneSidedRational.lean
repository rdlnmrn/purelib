import FiniteMeasure.OneSidedProcess
import CCL.Progressive.Enclosures

/-!
# One-sided rational pairs as ordinary CCL processes

This CCL-side bridge converts a lower/upper rational pair only when it carries
the explicit finite gap modulus in `FiniteMeasure.LocatedPair`.  The bare
one-sided processes remain rate-free.

The requested CCL squared-error target is translated to the strictly smaller
rational gap `target / (target + 1)`.  Its square is below `target`, so the
construction needs no square root, completion, limit, or unbounded search.
-/

namespace CCL.ProgressiveOneSidedRational

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Ball := CCL.ArithmeticEnclosures.Ball

open RFAP.ConstructiveGaussian.Gaussian

/-- Embed a displayed rational on the real axis of the Gaussian rationals. -/
def realPoint (value : Coordinate) : Gaussian :=
  ⟨value, 0⟩

@[simp] theorem realPoint_re (value : Coordinate) :
    (realPoint value).re = value :=
  rfl

@[simp] theorem realPoint_im (value : Coordinate) :
    (realPoint value).im = 0 :=
  rfl

@[simp] theorem realPoint_sub (left right : Coordinate) :
    realPoint left - realPoint right = realPoint (left - right) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [realPoint_re, sub_re]
  · simp only [realPoint_im, sub_im]
    ring1

@[simp] theorem normSq_realPoint (value : Coordinate) :
    normSq (realPoint value) = value ^ 2 := by
  simp only [normSq, realPoint_re, realPoint_im]
  ring1

/-- A rational interval as a real-axis Gaussian ball.  The lower endpoint is
the canonical centre and the interval width supplies a square error bound. -/
def ballOfBound (bound : FiniteMeasure.Bound) : Ball where
  center := realPoint bound.sample
  radiusSq := bound.width ^ 2
  radiusSq_nonneg := RFAP.ConstructiveFraction.sq_nonneg_direct bound.width

@[simp] theorem ballOfBound_center_re (bound : FiniteMeasure.Bound) :
    (ballOfBound bound).center.re = bound.sample :=
  rfl

@[simp] theorem ballOfBound_center_im (bound : FiniteMeasure.Bound) :
    (ballOfBound bound).center.im = 0 :=
  rfl

@[simp] theorem ballOfBound_radiusSq (bound : FiniteMeasure.Bound) :
    (ballOfBound bound).radiusSq = bound.width ^ 2 :=
  rfl

/-- Every displayed rational admitted by the interval is admitted by its
real-axis Gaussian ball. -/
theorem ballOfBound_contains {bound : FiniteMeasure.Bound}
    {value : Coordinate} (inside : bound.Contains value) :
    (ballOfBound bound).Contains (realPoint value) := by
  unfold CCL.ArithmeticEnclosures.Ball.Contains
  rw [show (ballOfBound bound).center = realPoint bound.sample by rfl,
    realPoint_sub, normSq_realPoint]
  have directed := FiniteMeasure.Bound.sample_difference_le inside
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ (bound.width - (value - bound.sample)) *
          (bound.width + (value - bound.sample)) := by
      apply RFAP.ConstructiveFraction.mul_nonneg_direct
      · exact RFAP.ConstructiveFraction.sub_nonneg_direct directed.1
      · have nonnegative :
          0 ≤ bound.width - (bound.sample - value) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct directed.2
        calc
          0 ≤ bound.width - (bound.sample - value) := nonnegative
          _ = bound.width + (value - bound.sample) := by ring1
    _ = bound.width ^ 2 - (value - bound.sample) ^ 2 := by ring1

/-- A coarse explicit bound for every later real-axis ball centre, obtained
from containment in one displayed outer interval. -/
theorem ballOfBound_center_bounded {inner outer : FiniteMeasure.Bound}
    (refines : FiniteMeasure.Bound.Refines inner outer) :
    normSq (ballOfBound inner).center ≤
      2 * (normSq (realPoint outer.sample) + outer.width ^ 2) := by
  have sampleInside : outer.Contains inner.sample :=
    refines.contains inner.sample_contains
  have differenceInside :
      normSq (realPoint inner.sample - realPoint outer.sample) ≤
        outer.width ^ 2 := by
    simpa only [ballOfBound, CCL.ArithmeticEnclosures.Ball.Contains] using
      ballOfBound_contains sampleInside
  have decomposition :
      realPoint inner.sample = realPoint outer.sample +
        (realPoint inner.sample - realPoint outer.sample) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [realPoint_re, realPoint_im, add_re, add_im, sub_re, sub_im] <;>
      ring1
  rw [show (ballOfBound inner).center = realPoint inner.sample by rfl,
    decomposition]
  exact (normSq_add_le_two _ _).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl differenceInside) (by decide))

/-- A positive, subunit rational gap budget computed from a CCL squared-error
target without taking a square root. -/
def gapTarget (target : Coordinate) : Coordinate :=
  target / (target + 1)

theorem gapTarget_pos {target : Coordinate} (positive : 0 < target) :
    0 < gapTarget target :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    (add_pos positive (by decide))

theorem gapTarget_lt_one {target : Coordinate} (positive : 0 < target) :
    gapTarget target < 1 := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (add_pos positive (by decide))).2
  calc
    target < target + 1 :=
      lt_add_of_pos_right target (by decide : (0 : Coordinate) < 1)
    _ = 1 * (target + 1) := by ring1

theorem gapTarget_lt_target {target : Coordinate} (positive : 0 < target) :
    gapTarget target < target := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (add_pos positive (by decide))).2
  have squarePositive : 0 < target ^ 2 := by
    exact RFAP.ConstructiveFraction.pow_pos_direct positive 2
  calc
    target < target + target ^ 2 := lt_add_of_pos_right target squarePositive
    _ = target * (target + 1) := by ring1

theorem gapTarget_sq_lt_target {target : Coordinate} (positive : 0 < target) :
    gapTarget target ^ 2 < target := by
  have gapPositive := gapTarget_pos positive
  have squareLtGap : gapTarget target ^ 2 < gapTarget target := by
    rw [pow_two]
    calc
      gapTarget target * gapTarget target < 1 * gapTarget target :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          (gapTarget_lt_one positive) gapPositive
      _ = gapTarget target := by ring1
  exact squareLtGap.trans (gapTarget_lt_target positive)

theorem square_lt_target_of_gap_lt {value target : Coordinate}
    (valueNonnegative : 0 ≤ value) (targetPositive : 0 < target)
    (small : value < gapTarget target) : value ^ 2 < target := by
  have gapPositive := gapTarget_pos targetPositive
  have firstStep : value * value ≤ value * gapTarget target :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      small.le valueNonnegative
  have secondStep : value * gapTarget target <
      gapTarget target * gapTarget target :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      small gapPositive
  rw [pow_two]
  exact firstStep.trans_lt
    (secondStep.trans (by
      simpa only [pow_two] using gapTarget_sq_lt_target targetPositive))

end CCL.ProgressiveOneSidedRational

namespace FiniteMeasure.LocatedPair

/-- Convert a one-sided pair with an explicit finite gap modulus into the
ordinary stateful CCL process.  Possible values are exactly the displayed
real-axis rational candidates in the current paired interval. -/
def toProcess {lower : LowerProcess} {upper : UpperProcess}
    (pair : LocatedPair lower upper) : CCL.ProgressiveEnclosures.Process where
  State := pair.State
  ball state :=
    CCL.ProgressiveOneSidedRational.ballOfBound
      (pair.observation state).bound
  Possible state value := ∃ candidate : Coordinate,
    (pair.observation state).bound.Contains candidate ∧
      value = CCL.ProgressiveOneSidedRational.realPoint candidate
  witness state :=
    ⟨CCL.ProgressiveOneSidedRational.realPoint
        (pair.observation state).bound.sample,
      ⟨(pair.observation state).bound.sample,
        (pair.observation state).bound.sample_contains, rfl⟩⟩
  possible_inside := by
    rintro state value ⟨candidate, inside, rfl⟩
    exact CCL.ProgressiveOneSidedRational.ballOfBound_contains inside
  refine state target positive :=
    pair.request state
      (CCL.ProgressiveOneSidedRational.gapTarget target)
      (CCL.ProgressiveOneSidedRational.gapTarget_pos positive)
  refine_persists := by
    rintro state target positive value ⟨candidate, inside, rfl⟩
    let gapPositive :=
      CCL.ProgressiveOneSidedRational.gapTarget_pos positive
    exact ⟨candidate,
      (pair.request_refines state _ gapPositive).bound.contains inside, rfl⟩
  accurate := by
    intro state target positive
    let gapPositive :=
      CCL.ProgressiveOneSidedRational.gapTarget_pos positive
    have small := pair.accurate state
      (CCL.ProgressiveOneSidedRational.gapTarget target) gapPositive
    change (pair.observation
      (pair.request state
        (CCL.ProgressiveOneSidedRational.gapTarget target)
        gapPositive)).gap ^ 2 < target
    exact CCL.ProgressiveOneSidedRational.square_lt_target_of_gap_lt
      (pair.observation
        (pair.request state
          (CCL.ProgressiveOneSidedRational.gapTarget target)
          gapPositive)).gap_nonnegative positive small
  centerBound :=
    2 * (RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.ProgressiveOneSidedRational.realPoint
        (pair.observation pair.initial).bound.sample) +
      (pair.observation pair.initial).bound.width ^ 2)
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
        (RFAP.ConstructiveFraction.sq_nonneg_direct _))
  center_bounded state :=
    CCL.ProgressiveOneSidedRational.ballOfBound_center_bounded
      (pair.refinesInitial state).bound

@[simp] theorem toProcess_ball {lower : LowerProcess} {upper : UpperProcess}
    (pair : LocatedPair lower upper) (state : pair.State) :
    pair.toProcess.ball state =
      CCL.ProgressiveOneSidedRational.ballOfBound
        (pair.observation state).bound :=
  rfl

@[simp] theorem toProcess_refine {lower : LowerProcess} {upper : UpperProcess}
    (pair : LocatedPair lower upper) (state : pair.State)
    (target : Coordinate) (positive : 0 < target) :
    pair.toProcess.refine state target positive =
      pair.request state
        (CCL.ProgressiveOneSidedRational.gapTarget target)
        (CCL.ProgressiveOneSidedRational.gapTarget_pos positive) :=
  rfl

end FiniteMeasure.LocatedPair
