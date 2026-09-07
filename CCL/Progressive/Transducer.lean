import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.Charts

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace CCL.ProgressiveTransducer

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev LoopDomain := CCL.ProgressiveCharts.LoopDomain
abbrev Word := List Bool

open RFAP.ConstructiveGaussian.Gaussian
open CCL.ProgressiveCharts

/-- Which ordinary raw-grammar unary run a normalized regular state is in. -/
inductive RegularKind where
  | initialHigh
  | loop
deriving DecidableEq, Repr

/-- Normalized process ready for one redundant loop decision.  The finite
syntax fields do not affect enclosure decisions; they retain exactly the raw
parser phase needed to certify the emitted pure bitstream. -/
structure LoopState where
  kind : RegularKind
  count : Nat
  process : Process
  state : process.State
  domain : LoopDomain process

/-- Residual process after a sector.  `count` is the number of unary padding
bits already emitted.  The retained strict upper bound is exactly what makes
an eventual nonzero inverse chart normalized after those bits. -/
structure ResidualState where
  process : Process
  state : process.State
  count : Nat
  upper : Coordinate
  upperBound : ∀ {value : Gaussian}, process.Possible state value →
    normSq value ≤ upper
  upperStrict : upper <
    CCL.ResidualDecision.paddingTarget count

/-- Initial mode before either radial chart has been selected. -/
structure InitialState where
  process : Process
  state : process.State

/-- Initial-low mode after its leading zero has been emitted.  The fixed
strict upper bound is preserved by every low-unary step and prevents the
low chart from overshooting the enlarged sector band. -/
structure LowState where
  count : Nat
  process : Process
  state : process.State
  upperBound : ∀ {value : Gaussian}, process.Possible state value →
    normSq value < 43 / 20

inductive Mode where
  | initial (state : InitialState)
  | low (state : LowState)
  | loop (state : LoopState)
  | residual (state : ResidualState)

/-- One nonempty output chunk and the mode after the whole chunk is consumed.
Sector chunks contain the delimiter followed by their three-bit code. -/
structure Emission where
  bits : Word
  nonempty : bits ≠ []
  next : Mode

/-- The explicit upper norm stored by a small residual ball. -/
def smallUpper (ball : CCL.ArithmeticEnclosures.Ball) : Coordinate :=
  2 * (ball.radiusSq + normSq ball.center)

theorem smallUpper_bound
    {process : Process} {state : process.State}
    {target : Coordinate}
    (_small : CCL.ResidualDecision.SmallBall
      (process.ball state) target)
    {value : Gaussian} (possible : process.Possible state value) :
    normSq value ≤ smallUpper (process.ball state) := by
  have decomposition :
      value = (value - (process.ball state).center) +
        (process.ball state).center := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  rw [decomposition]
  exact (normSq_add_le_two _ _).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add (process.possible_inside possible) le_rfl) (by decide))

/-! ## Total initial-chart selection -/

/-- One fixed rational accuracy is enough both to distinguish the overlapping
initial charts and to keep a low-unary rescaling below the enlarged sector
band. -/
def initialRadiusSq : Coordinate :=
  ((CCL.RedundantOutput.uniformRadiusSq / 10) / 10) / 10

theorem initialRadiusSq_pos : 0 < initialRadiusSq := by
  unfold initialRadiusSq
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.div_pos_direct
        CCL.RedundantOutput.uniformRadiusSq_pos (by decide))
      (by decide)) (by decide)

theorem initialRadiusSq_lt_uniform :
    initialRadiusSq < CCL.RedundantOutput.uniformRadiusSq := by
  unfold initialRadiusSq CCL.RedundantOutput.uniformRadiusSq
    CCL.RedundantOutput.allowance
  decide

private theorem ten_pos : (0 : Coordinate) < 10 := by decide

private theorem div_ten_lt_self {value : Coordinate} (positive : 0 < value) :
    value / 10 < value := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos ten_pos).2
  calc
    value = value * 1 :=
      (RFAP.ConstructiveFraction.mul_one_direct value).symm
    _ < value * 10 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive (by decide)

private theorem initialRadiusSq_lt_uniform_tenth :
    initialRadiusSq <
      CCL.RedundantOutput.uniformRadiusSq / 10 := by
  let first := CCL.RedundantOutput.uniformRadiusSq / 10
  let second := first / 10
  have firstPositive : 0 < first :=
    RFAP.ConstructiveFraction.div_pos_direct
      CCL.RedundantOutput.uniformRadiusSq_pos ten_pos
  have secondPositive : 0 < second :=
    RFAP.ConstructiveFraction.div_pos_direct firstPositive ten_pos
  exact (div_ten_lt_self secondPositive).trans
    (div_ten_lt_self firstPositive)

private theorem sixteen_mul_uniform_tenth :
    16 * (CCL.RedundantOutput.uniformRadiusSq / 10) =
      CCL.RedundantOutput.allowance / 10 := by
  have sixteenDivOne : (16 / 1 : Coordinate) = 16 :=
    calc
      (16 / 1 : Coordinate) = (16 / 1) * 1 :=
        (RFAP.ConstructiveFraction.mul_one_direct _).symm
      _ = 16 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne 16 1 (by decide)
  have uniformTimesSixteen :
      CCL.RedundantOutput.uniformRadiusSq * 16 =
        CCL.RedundantOutput.allowance := by
    unfold CCL.RedundantOutput.uniformRadiusSq
    exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
      CCL.RedundantOutput.allowance 16 (by decide)
  calc
    16 * (CCL.RedundantOutput.uniformRadiusSq / 10) =
        (CCL.RedundantOutput.uniformRadiusSq / 10) * 16 :=
      RFAP.ConstructiveFraction.mul_comm _ _
    _ = (CCL.RedundantOutput.uniformRadiusSq / 10) *
        (16 / 1) := by rw [sixteenDivOne]
    _ = (CCL.RedundantOutput.uniformRadiusSq * 16) /
        (10 * 1) :=
      RFAP.ConstructiveFraction.div_mul_div_direct _ _ _ _
    _ = CCL.RedundantOutput.allowance / 10 := by
      rw [uniformTimesSixteen,
        RFAP.ConstructiveFraction.mul_one_direct]

private theorem sixteen_mul_initial_lt_allowance_tenth :
    16 * initialRadiusSq <
      CCL.RedundantOutput.allowance / 10 := by
  exact (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    (by decide) initialRadiusSq_lt_uniform_tenth).trans_eq
      sixteen_mul_uniform_tenth

private theorem allowance_lt_one_twenty_fifth :
    CCL.RedundantOutput.allowance < (1 / 25 : Coordinate) := by
  unfold CCL.RedundantOutput.allowance
  decide

/-- A small displayed rational used twice in the low-centre estimate. -/
private def lowCenterSlack : Coordinate := (1 / 25) / 8

private theorem lowCenterSlack_pos : 0 < lowCenterSlack := by
  unfold lowCenterSlack
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.div_pos_direct (by decide) (by decide))
    (by decide)

private theorem two_uniform_lt_lowCenterSlack :
    2 * CCL.RedundantOutput.uniformRadiusSq < lowCenterSlack := by
  have divided :
      CCL.RedundantOutput.allowance / 8 <
        (1 / 25 : Coordinate) / 8 := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos
      (by decide : (0 : Coordinate) < 8)).2
    calc
      CCL.RedundantOutput.allowance < (1 / 25 : Coordinate) :=
        allowance_lt_one_twenty_fifth
      _ = ((1 / 25 : Coordinate) / 8) * 8 :=
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 8 (by decide)).symm
  have identity :
      2 * CCL.RedundantOutput.uniformRadiusSq =
        CCL.RedundantOutput.allowance / 8 := by
    unfold CCL.RedundantOutput.uniformRadiusSq
    have twoDivOne : (2 / 1 : Coordinate) = 2 := by
      calc
        (2 / 1 : Coordinate) = (2 / 1) * 1 :=
          (RFAP.ConstructiveFraction.mul_one_direct _).symm
        _ = 2 :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne 2 1 (by decide)
    calc
      2 * (CCL.RedundantOutput.allowance / 16) =
          (CCL.RedundantOutput.allowance / 16) * (2 / 1) := by
        rw [twoDivOne, RFAP.ConstructiveFraction.mul_comm]
      _ = (CCL.RedundantOutput.allowance * 2) / (16 * 1) :=
        RFAP.ConstructiveFraction.div_mul_div_direct _ _ _ _
      _ = (2 * CCL.RedundantOutput.allowance) / (2 * 8) := by
        apply congrArg₂ (fun numerator denominator : Coordinate =>
          numerator / denominator)
        · exact RFAP.ConstructiveFraction.mul_comm _ _
        · decide
      _ = CCL.RedundantOutput.allowance / 8 :=
        RFAP.ConstructiveFraction.mul_div_mul_left_direct 2 _ _ (by decide)
  exact identity.trans_lt divided

private def lowCenterWeight : Coordinate := (10 * 10) * 10

private theorem lowCenterWeight_pos : 0 < lowCenterWeight := by
  unfold lowCenterWeight
  exact RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct ten_pos ten_pos) ten_pos

private theorem lowCenterWeight_mul_initial :
    lowCenterWeight * initialRadiusSq =
      CCL.RedundantOutput.uniformRadiusSq := by
  let uniform := CCL.RedundantOutput.uniformRadiusSq
  have tenNonzero : (10 : Coordinate) ≠ 0 := ten_pos.ne'
  calc
    lowCenterWeight * initialRadiusSq =
        (((uniform / 10) / 10) / 10) * ((10 * 10) * 10) := by
      unfold lowCenterWeight initialRadiusSq
      ring1
    _ = ((((uniform / 10) / 10) / 10) * 10) * 10 * 10 := by
      ring1
    _ = ((uniform / 10) / 10) * 10 * 10 := by
      have cancellation : (((uniform / 10) / 10) / 10) * 10 =
          (uniform / 10) / 10 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 10 tenNonzero
      rw [cancellation]
    _ = (uniform / 10) * 10 := by
      have cancellation : ((uniform / 10) / 10) * 10 = uniform / 10 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 10 tenNonzero
      rw [cancellation]
    _ = uniform :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 10 tenNonzero

private theorem lowCenterSlack_mul_weight :
    lowCenterSlack * lowCenterWeight = 5 := by
  unfold lowCenterSlack lowCenterWeight
  decide

private theorem lowCenter_budget :
    (43 / 20 : Coordinate) + lowCenterSlack + lowCenterSlack < 13 / 6 := by
  have eightNonzero : (8 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 8) (by decide)).ne'
  have twentyFiveNonzero : (25 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 25) (by decide)).ne'
  have twoHundredNonzero : (200 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 200) (by decide)).ne'
  have slackValue : lowCenterSlack = (1 / 200 : Coordinate) := by
    unfold lowCenterSlack
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      eightNonzero twoHundredNonzero
    calc
      (1 / 25 : Coordinate) * 200 = ((1 / 25) * 25) * 8 := by ring1
      _ = 1 * 8 := by
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          1 25 twentyFiveNonzero]
      _ = (1 : Coordinate) * 8 := rfl
  rw [slackValue]
  have twentyNonzero : (20 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 20) (by decide)).ne'
  have sixNonzero : (6 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 6) (by decide)).ne'
  have firstScaled : (43 / 20 : Coordinate) * 600 = 1290 := by
    calc
      (43 / 20 : Coordinate) * 600 = ((43 / 20) * 20) * 30 := by ring1
      _ = 43 * 30 := by
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          43 20 twentyNonzero]
      _ = 1290 := by ring1
  have slackScaled : (1 / 200 : Coordinate) * 600 = 3 := by
    calc
      (1 / 200 : Coordinate) * 600 = ((1 / 200) * 200) * 3 := by ring1
      _ = 1 * 3 := by
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          1 200 twoHundredNonzero]
      _ = 3 := RFAP.ConstructiveFraction.one_mul _
  have upperScaled : (13 / 6 : Coordinate) * 600 = 1300 := by
    calc
      (13 / 6 : Coordinate) * 600 = ((13 / 6) * 6) * 100 := by ring1
      _ = 13 * 100 := by
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne 13 6 sixNonzero]
      _ = 1300 := by ring1
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := 600)
  · calc
      ((43 / 20 : Coordinate) + 1 / 200 + 1 / 200) * 600 =
          (43 / 20) * 600 + (1 / 200) * 600 + (1 / 200) * 600 := by ring1
      _ = 1290 + 3 + 3 := by rw [firstScaled, slackScaled]
      _ = 1296 := by ring1
      _ < 1300 := RFAP.ConstructiveFraction.natCast_lt_direct (by decide)
      _ = (13 / 6 : Coordinate) * 600 := upperScaled.symm
  · exact RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 600) (by decide)

private theorem lowCenterSlack_mul_ten : lowCenterSlack * 10 = 1 / 20 := by
  unfold lowCenterSlack
  decide

private theorem allowance_tenth_lt_lowCenterSlack :
    CCL.RedundantOutput.allowance / 10 < lowCenterSlack := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos ten_pos).2
  rw [lowCenterSlack_mul_ten]
  exact allowance_lt_one_twenty_fifth.trans (by decide)

private def lowUnaryGap : Coordinate := (1 / 15) / 8

private theorem oneTwentyFifth_lt_oneFifteenth :
    (1 / 25 : Coordinate) < 1 / 15 := by
  have fifteenthPositive : (0 : Coordinate) < 1 / 15 :=
    RFAP.ConstructiveFraction.div_pos_direct (by decide) (by decide)
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 25)).2
  calc
    1 = (1 / 15 : Coordinate) * 15 :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 15 (by decide)).symm
    _ < (1 / 15 : Coordinate) * 25 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        fifteenthPositive (by decide)

private theorem lowCenterSlack_lt_lowUnaryGap :
    lowCenterSlack < lowUnaryGap := by
  unfold lowCenterSlack lowUnaryGap
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 8)).2
  calc
    (1 / 25 : Coordinate) < 1 / 15 :=
      oneTwentyFifth_lt_oneFifteenth
    _ = ((1 / 15 : Coordinate) / 8) * 8 :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 8 (by decide)).symm

private theorem lowUnaryGap_identity :
    lowUnaryGap + (16 / 15 : Coordinate) * 1 = 43 / 40 := by
  let common : Coordinate := 15 * 8
  have commonPositive : 0 < common :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) (by decide)
  have gapCancellation : lowUnaryGap * common = 1 := by
    unfold lowUnaryGap common
    calc
      (1 / 15 / 8 : Coordinate) * (15 * 8) =
          ((1 / 15 / 8 : Coordinate) * 8) * 15 := by ring1
      _ = (1 / 15 : Coordinate) * 15 := by
        exact congrArg (fun value : Coordinate => value * 15)
          (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
            (1 / 15) 8 (by decide))
      _ = 1 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 15 (by decide)
  have sectorCancellation : (16 / 15 : Coordinate) * common = 16 * 8 := by
    unfold common
    calc
      (16 / 15 : Coordinate) * (15 * 8) =
          ((16 / 15 : Coordinate) * 15) * 8 := by ring1
      _ = 16 * 8 := by
        exact congrArg (fun value : Coordinate => value * 8)
          (RFAP.ConstructiveFraction.div_mul_cancel_of_ne 16 15 (by decide))
  have resultCancellation : (43 / 40 : Coordinate) * common = 43 * 3 := by
    unfold common
    have denominatorIdentity : (15 : Coordinate) * 8 = 40 * 3 := by decide
    rw [denominatorIdentity]
    calc
      (43 / 40 : Coordinate) * (40 * 3) =
          ((43 / 40 : Coordinate) * 40) * 3 := by ring1
      _ = 43 * 3 := by
        exact congrArg (fun value : Coordinate => value * 3)
          (RFAP.ConstructiveFraction.div_mul_cancel_of_ne 43 40
            (RFAP.ConstructiveFraction.natCast_pos_direct
              (n := 40) (by decide)).ne')
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne commonPositive.ne'
  calc
    (lowUnaryGap + (16 / 15 : Coordinate) * 1) * common =
        lowUnaryGap * common + (16 / 15) * common := by ring1
    _ = 1 + 16 * 8 := by rw [gapCancellation, sectorCancellation]
    _ = 43 * 3 := by decide
    _ = (43 / 40 : Coordinate) * common := resultCancellation.symm

private theorem lowUnary_budget :
    lowCenterSlack + (16 / 15 : Coordinate) * 1 < 43 / 40 := by
  calc
    lowCenterSlack + (16 / 15 : Coordinate) * 1 <
        lowUnaryGap + (16 / 15) * 1 :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct
        lowCenterSlack_lt_lowUnaryGap _
    _ = 43 / 40 := lowUnaryGap_identity

def initialRefinedState (process : Process) (state : process.State) :
    process.State :=
  process.refine state initialRadiusSq initialRadiusSq_pos

theorem initialRefined_accurate (process : Process) (state : process.State) :
    (process.ball (initialRefinedState process state)).radiusSq <
      initialRadiusSq :=
  process.accurate state initialRadiusSq initialRadiusSq_pos

theorem initialRefined_uniform (process : Process) (state : process.State) :
    (process.ball (initialRefinedState process state)).radiusSq <
      CCL.RedundantOutput.uniformRadiusSq :=
  (initialRefined_accurate process state).trans initialRadiusSq_lt_uniform

/-- If a sufficiently fine rational centre is below one, every candidate is
small enough that one low-unary rescaling remains inside the fixed enlarged
upper band. -/
theorem candidate_norm_lt_low_unary_bound
    {process : Process} {state : process.State}
    (accurate : (process.ball state).radiusSq < initialRadiusSq)
    (centerSmall : normSq (process.ball state).center < 1)
    {value : Gaussian} (possible : process.Possible state value) :
    normSq value < 43 / 40 := by
  have decomposition :
      value = (value - (process.ball state).center) +
        (process.ball state).center := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  have weighted := CCL.RedundantOutput.normSq_add_le_weighted
    (value - (process.ball state).center) (process.ball state).center
  have radiusScaled : 16 * (process.ball state).radiusSq <
      CCL.RedundantOutput.allowance / 10 :=
    (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (by decide) accurate).trans sixteen_mul_initial_lt_allowance_tenth
  have centerScaled : (16 / 15 : Coordinate) *
      normSq (process.ball state).center < (16 / 15) * 1 :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (by decide) centerSmall
  rw [decomposition]
  exact weighted.trans_lt (calc
    16 * normSq (value - (process.ball state).center) +
          (16 / 15) * normSq (process.ball state).center ≤
        16 * (process.ball state).radiusSq +
          (16 / 15) * normSq (process.ball state).center :=
      add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (process.possible_inside possible) (by decide)) le_rfl
    _ < CCL.RedundantOutput.allowance / 10 +
        (16 / 15) * 1 :=
      RFAP.ConstructiveFraction.add_lt_add_direct radiusScaled centerScaled
    _ < lowCenterSlack + (16 / 15) * 1 :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct
        allowance_tenth_lt_lowCenterSlack _
    _ < 43 / 40 := lowUnary_budget)

/-- Multiplying a candidate admitted by the low branch by `gamma` preserves
the fixed strict upper invariant used by `LowState`. -/
theorem scaled_candidate_norm_lt_low_upper
    {process : Process} {state : process.State}
    (accurate : (process.ball state).radiusSq < initialRadiusSq)
    (centerSmall : normSq (process.ball state).center < 1)
    {value : Gaussian} (possible : process.Possible state value) :
    normSq (gamma * value) < 43 / 20 := by
  rw [normSq_mul, normSq_gamma]
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    (by decide : (0 : Coordinate) < 2)
    (candidate_norm_lt_low_unary_bound accurate centerSmall possible)
  have scaledIdentity : 2 * (43 / 40 : Coordinate) = 43 / 20 := by
    calc
      2 * (43 / 40 : Coordinate) = (2 * 43) / 40 := by
        rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        ring1
      _ = 43 / 20 := by
        apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        · exact (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 40) (by decide)).ne'
        · exact (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 20) (by decide)).ne'
        · ring1
  exact scaled.trans_eq scaledIdentity

/-- The fixed low-state candidate upper bound and one very fine displayed
radius keep the rational centre strictly inside the enlarged sector band. -/
theorem low_center_lt_extended_upper
    (current : LowState) :
    normSq
        (current.process.ball
          (initialRefinedState current.process current.state)).center <
      13 / 6 := by
  let refined := initialRefinedState current.process current.state
  rcases current.process.witness refined with ⟨witness, possible⟩
  have possibleAtOld : current.process.Possible current.state witness :=
    current.process.refine_persists current.state _ _ possible
  have witnessUpper : normSq witness < 43 / 20 :=
    current.upperBound possibleAtOld
  have errorNorm :
      normSq ((current.process.ball refined).center - witness) ≤
        (current.process.ball refined).radiusSq := by
    have reversed :
        (current.process.ball refined).center - witness =
          -(witness - (current.process.ball refined).center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
    rw [reversed, normSq_neg]
    exact current.process.possible_inside possible
  have radiusUpper := initialRefined_accurate current.process current.state
  have weightPlusPositive : 0 < lowCenterWeight + 1 :=
    add_pos_of_pos_of_nonneg lowCenterWeight_pos (by decide)
  have errorScaled : (lowCenterWeight + 1) *
      normSq ((current.process.ball refined).center - witness) <
      lowCenterSlack := by
    have first : (lowCenterWeight + 1) *
        normSq ((current.process.ball refined).center - witness) <
        (lowCenterWeight + 1) * initialRadiusSq :=
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        errorNorm weightPlusPositive.le).trans_lt
        (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          weightPlusPositive radiusUpper)
    have second : (lowCenterWeight + 1) * initialRadiusSq <
        2 * CCL.RedundantOutput.uniformRadiusSq := by
      calc
        (lowCenterWeight + 1) * initialRadiusSq =
            lowCenterWeight * initialRadiusSq + initialRadiusSq := by ring1
        _ = CCL.RedundantOutput.uniformRadiusSq +
            initialRadiusSq := by rw [lowCenterWeight_mul_initial]
        _ = initialRadiusSq +
            CCL.RedundantOutput.uniformRadiusSq := by ring1
        _ < CCL.RedundantOutput.uniformRadiusSq +
            CCL.RedundantOutput.uniformRadiusSq :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct
            initialRadiusSq_lt_uniform CCL.RedundantOutput.uniformRadiusSq
        _ = 2 * CCL.RedundantOutput.uniformRadiusSq := by ring1
    exact first.trans (second.trans two_uniform_lt_lowCenterSlack)
  have witnessDivWeight : normSq witness / lowCenterWeight <
      lowCenterSlack := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos
      lowCenterWeight_pos).2
    rw [lowCenterSlack_mul_weight]
    have fortyThreeTwentiethsLtFive : (43 / 20 : Coordinate) < 5 := by
      apply (RFAP.ConstructiveFraction.div_lt_iff_pos
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 20) (by decide))).2
      calc
        (43 : Coordinate) < 100 :=
          RFAP.ConstructiveFraction.natCast_lt_direct (by decide)
        _ = 5 * 20 := by ring1
    exact witnessUpper.trans fortyThreeTwentiethsLtFive
  have ratioIdentity :
      ((lowCenterWeight + 1) / lowCenterWeight) * normSq witness =
        normSq witness + normSq witness / lowCenterWeight := by
    have weightNonzero := lowCenterWeight_pos.ne'
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      lowCenterWeight_pos.ne'
    calc
      (((lowCenterWeight + 1) / lowCenterWeight) * normSq witness) *
          lowCenterWeight =
          normSq witness *
            (((lowCenterWeight + 1) / lowCenterWeight) *
              lowCenterWeight) := by ring1
      _ = normSq witness * (lowCenterWeight + 1) := by
        have cancellation :
            (lowCenterWeight + 1) / lowCenterWeight * lowCenterWeight =
              lowCenterWeight + 1 :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ weightNonzero
        rw [cancellation]
      _ = (normSq witness + normSq witness / lowCenterWeight) *
          lowCenterWeight := by
        have cancellation : normSq witness / lowCenterWeight *
            lowCenterWeight = normSq witness :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ weightNonzero
        rw [show (normSq witness + normSq witness / lowCenterWeight) *
            lowCenterWeight = normSq witness * lowCenterWeight +
              (normSq witness / lowCenterWeight) * lowCenterWeight by ring1,
          cancellation]
        ring1
  have witnessScaled :
      ((lowCenterWeight + 1) / lowCenterWeight) * normSq witness <
        (43 / 20 : Coordinate) + lowCenterSlack := by
    rw [ratioIdentity]
    exact RFAP.ConstructiveFraction.add_lt_add_direct witnessUpper
      witnessDivWeight
  have decomposition :
      (current.process.ball refined).center =
        ((current.process.ball refined).center - witness) + witness := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  rw [decomposition]
  exact (normSq_add_le_parameter lowCenterWeight lowCenterWeight_pos
      ((current.process.ball refined).center - witness) witness).trans_lt (calc
    (lowCenterWeight + 1) *
          normSq ((current.process.ball refined).center - witness) +
        ((lowCenterWeight + 1) / lowCenterWeight) * normSq witness <
      lowCenterSlack + ((43 / 20 : Coordinate) + lowCenterSlack) :=
        RFAP.ConstructiveFraction.add_lt_add_direct errorScaled witnessScaled
    _ = (43 / 20 : Coordinate) + lowCenterSlack + lowCenterSlack := by ring1
    _ < 13 / 6 := lowCenter_budget)

/-- The state after one initial-low unary bit, with its quantitative upper
invariant reconstructed solely from the finite ball that justified the bit. -/
def nextLowState (process : Process) (base : process.State)
    (accurate : (process.ball base).radiusSq < initialRadiusSq)
    (centerSmall : normSq (process.ball base).center < 1)
    (count : Nat) : LowState := by
  let nextProcess := upscaledProcess process base 1
  let nextState := upscaledInitial process base 1
  exact
    { count := count
      process := nextProcess
      state := nextState
      upperBound := by
        intro value possible
        rcases upscaled_candidate_semantics process base 1 possible with
          ⟨sourceValue, sourcePossible, valueEqual⟩
        rw [valueEqual, natPow_succ, natPow_zero,
          RFAP.ConstructiveGaussian.Gaussian.one_mul]
        exact scaled_candidate_norm_lt_low_upper accurate centerSmall
          sourcePossible }

@[simp] theorem nextLowState_count (process : Process) (base : process.State)
    (accurate : (process.ball base).radiusSq < initialRadiusSq)
    (centerSmall : normSq (process.ball base).center < 1) (count : Nat) :
    (nextLowState process base accurate centerSmall count).count = count := by
  rfl

/-- Quantitative residual state produced by one normalized safe-sector
choice.  Factoring it out lets the optional contraction sidecar refer to the
live controller state without changing the raw emission. -/
def loopSectorResidualState (current : LoopState)
    (sector : CCL.Sectors.Sector)
    (certificate : CCL.RedundantOutput.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state))) : ResidualState :=
  let base := current.domain.refinedState current.state
  let nextProcess := residualProcess current.process base sector
  let nextState := residualInitial current.process base sector
  let upper := safeResidualUpper sector (current.process.ball base)
  { process := nextProcess
    state := nextState
    count := 0
    upper := upper
    upperBound := by
      intro value possible
      exact translated_based_norm_le_safeResidualUpper
        current.process base sector certificate possible
    upperStrict := safeResidualUpper_lt_half certificate }

@[simp] theorem loopSectorResidualState_count (current : LoopState)
    (sector : CCL.Sectors.Sector)
    (certificate : CCL.RedundantOutput.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state))) :
    (loopSectorResidualState current sector certificate).count = 0 := rfl

/-- One productive chunk from a normalized loop state. -/
def loopStep (current : LoopState) : Emission := by
  let base := current.domain.refinedState current.state
  match decision : current.domain.decide current.state with
  | .unary certificate =>
      let nextProcess := unaryScaledProcess current.process base
      let nextState := unaryScaledInitial current.process base
      let nextDomain := unaryScaledLoopDomain current.process base certificate
      exact
        { bits := [true]
          nonempty := by decide
          next := .loop
            { kind := current.kind
              count := current.count + 1
              process := nextProcess
              state := nextState
              domain := nextDomain } }
  | .sector sector certificate =>
      exact
        { bits := false :: sector.code
          nonempty := by simp
          next := .residual
            (loopSectorResidualState current sector certificate) }

/-- Normalized loop state entered after a residual apartness decision.  The
chart change is silent; the enclosing `step` immediately emits the next
ordinary loop chunk. -/
def residualApartLoopState (current : ResidualState)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (current.process.ball
        (CCL.ArithmeticController.residualState
          current.process current.state (current.count + 1)))) : LoopState :=
  let refined := CCL.ArithmeticController.residualState
    current.process current.state (current.count + 1)
  have upperBoundAtRefined : ∀ {value : Gaussian},
      current.process.Possible refined value →
        normSq value ≤ current.upper := by
    intro value possible
    exact current.upperBound
      (current.process.refine_persists current.state _ _ possible)
  { kind := .loop
    count := current.count
    process := normalizedInverseProcess current.process refined
      certificate current.count
    state := normalizedInverseInitial current.process refined
      certificate current.count
    domain := normalizedInverseLoopDomain current.process refined
      certificate current.count current.upper upperBoundAtRefined
        current.upperStrict }

/-- One productive chunk from the total initial-chart decision. -/
def initialStep (current : InitialState) : Emission := by
  let base := initialRefinedState current.process current.state
  have accurate := initialRefined_accurate current.process current.state
  have uniform := initialRefined_uniform current.process current.state
  by_cases normalized : 1 ≤ normSq (current.process.ball base).center
  · match decision : CCL.RedundantOutput.decide
        (current.process.ball base) normalized uniform with
    | .unary certificate =>
        let nextProcess := unaryScaledProcess current.process base
        let nextState := unaryScaledInitial current.process base
        let nextDomain := unaryScaledLoopDomain current.process base
          certificate
        exact
          { bits := [true]
            nonempty := by decide
            next := .loop
              { kind := .initialHigh
                count := 1
                process := nextProcess
                state := nextState
                domain := nextDomain } }
    | .sector sector certificate =>
        let nextProcess := residualProcess current.process base sector
        let nextState := residualInitial current.process base sector
        let upper := safeResidualUpper sector (current.process.ball base)
        exact
          { bits := false :: false :: sector.code
            nonempty := by simp
            next := .residual
              { process := nextProcess
                state := nextState
                count := 0
                upper := upper
                upperBound := by
                  intro value possible
                  exact translated_based_norm_le_safeResidualUpper
                    current.process base sector certificate possible
                upperStrict := safeResidualUpper_lt_half certificate } }
  · have centerSmall : normSq (current.process.ball base).center < 1 :=
      lt_of_not_ge normalized
    exact
      { bits := [false, true]
        nonempty := by decide
        next := .low (nextLowState current.process base accurate
          centerSmall 1) }

/-- One productive chunk while the initial-low unary chart is active. -/
def lowStep (current : LowState) : Emission := by
  let base := initialRefinedState current.process current.state
  have accurate := initialRefined_accurate current.process current.state
  have uniform := initialRefined_uniform current.process current.state
  have centerUpper := low_center_lt_extended_upper current
  by_cases normalized : 1 ≤ normSq (current.process.ball base).center
  · let sector := CCL.Sectors.Sector.select
      (current.process.ball base).center
    have certificate : CCL.RedundantOutput.SafeBall sector
        (current.process.ball base) :=
      CCL.RedundantOutput.safeBall_of_extendedBand
        ⟨normalized, centerUpper.le⟩ uniform
    let nextProcess := residualProcess current.process base sector
    let nextState := residualInitial current.process base sector
    let upper := safeResidualUpper sector (current.process.ball base)
    exact
      { bits := false :: sector.code
        nonempty := by simp
        next := .residual
          { process := nextProcess
            state := nextState
            count := 0
            upper := upper
            upperBound := by
              intro value possible
              exact translated_based_norm_le_safeResidualUpper
                current.process base sector certificate possible
            upperStrict := safeResidualUpper_lt_half certificate } }
  · have centerSmall : normSq (current.process.ball base).center < 1 :=
      lt_of_not_ge normalized
    exact
      { bits := [true]
        nonempty := by decide
        next := .low (nextLowState current.process base accurate
          centerSmall (current.count + 1)) }

/-- One productive residual-padding chunk.  An apart residual changes chart
and immediately performs the now-available loop step. -/
def residualStep (current : ResidualState) : Emission := by
  let requestedCount := current.count + 1
  let refined := CCL.ArithmeticController.residualState
    current.process current.state requestedCount
  match decision : CCL.ArithmeticController.decideResidual
      current.process current.state requestedCount with
  | .small certificate =>
      exact
        { bits := [true]
          nonempty := by decide
          next := .residual
            { process := current.process
              state := refined
              count := requestedCount
              upper := smallUpper (current.process.ball refined)
              upperBound := fun possible =>
                smallUpper_bound certificate possible
              upperStrict := certificate } }
  | .apart certificate =>
      exact loopStep (residualApartLoopState current certificate)

/-- One productive chunk from any mode.  Each branch is a named executable
finite decision, so its proof can be audited independently. -/
def step : Mode → Emission
  | .initial current => initialStep current
  | .low current => lowStep current
  | .loop current => loopStep current
  | .residual current => residualStep current

/-- Cursor which exposes a single raw bit at a time.  A completed sector chunk
is buffered, so clients see the same pure `List Bool` interface as elsewhere
in the CCL development. -/
structure Machine where
  mode : Mode
  emitted : Word
  pending : Word

/-- Start before the total overlapping initial-chart decision.  No chart bit
is committed until that finite decision has been made. -/
def Machine.initial (process : Process) (state : process.State) : Machine :=
  { mode := .initial
      { process := process
        state := state }
    emitted := []
    pending := [] }

/-- Expose the first bit of one certified nonempty chunk. -/
def consumeEmission (emitted : Word) (emission : Emission) : Bool × Machine :=
  match bitsEqual : emission.bits with
  | bit :: rest =>
      (bit,
        { mode := emission.next
          emitted := emitted ++ [bit]
          pending := rest })
  | [] => False.elim (emission.nonempty bitsEqual)

theorem consumeEmission_emitted (emitted : Word) (emission : Emission) :
    (consumeEmission emitted emission).2.emitted =
      emitted ++ [(consumeEmission emitted emission).1] := by
  cases emission with
  | mk bits nonempty next =>
      cases bits with
      | cons bit rest => rfl
      | nil => exact (nonempty rfl).elim

/-- Consume exactly one raw output bit. -/
def nextBit (machine : Machine) : Bool × Machine :=
  match machine.pending with
  | bit :: rest =>
      (bit,
        { mode := machine.mode
          emitted := machine.emitted ++ [bit]
          pending := rest })
  | [] =>
      consumeEmission machine.emitted (step machine.mode)

theorem nextBit_emitted (machine : Machine) :
    (nextBit machine).2.emitted =
      machine.emitted ++ [(nextBit machine).1] := by
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | cons bit rest => rfl
      | nil =>
          exact consumeEmission_emitted emitted (step mode)

theorem nextBit_length (machine : Machine) :
    (nextBit machine).2.emitted.length = machine.emitted.length + 1 := by
  rw [nextBit_emitted, List.length_append]
  rfl

/-- Structural recursion on the finite requested bit count. -/
def advance : Machine → Nat → Machine
  | machine, 0 => machine
  | machine, count + 1 => advance (nextBit machine).2 count

theorem advance_length (machine : Machine) : ∀ count : Nat,
    (advance machine count).emitted.length = machine.emitted.length + count
  | 0 => by simp only [advance, Nat.add_zero]
  | count + 1 => by
      rw [advance, advance_length (nextBit machine).2 count,
        nextBit_length]
      ring1

theorem advance_extends (machine : Machine) : ∀ count : Nat,
    machine.emitted.IsPrefix (advance machine count).emitted
  | 0 => by simp only [advance]; exact List.prefix_refl _
  | count + 1 => by
      have first : machine.emitted.IsPrefix (nextBit machine).2.emitted := by
        rw [nextBit_emitted]
        exact List.prefix_append _ _
      exact first.trans (advance_extends (nextBit machine).2 count)

/-- Top-level finite productivity statement for the progressive arithmetic
controller: every natural request returns exactly that many further raw bits
and never retracts the existing prefix. -/
theorem productive (machine : Machine) (count : Nat) :
    machine.emitted.IsPrefix (advance machine count).emitted ∧
      (advance machine count).emitted.length =
        machine.emitted.length + count :=
  ⟨advance_extends machine count, advance_length machine count⟩

/-! ## Elementary arithmetic entry points -/

/-- A progressive process at one explicit finite state. -/
structure Named where
  process : Process
  state : process.State

namespace Named

def exact (value : Gaussian) : Named :=
  { process := CCL.ProgressiveEnclosures.Process.exact value
    state := () }

def add (left right : Named) : Named :=
  { process := CCL.ProgressiveEnclosures.Process.add
      left.process right.process
    state := (left.state, right.state) }

def neg (name : Named) : Named :=
  { process := CCL.ProgressiveEnclosures.Process.neg name.process
    state := name.state }

def sub (left right : Named) : Named :=
  { process := CCL.ProgressiveEnclosures.Process.sub
      left.process right.process
    state := (left.state, right.state) }

def mul (left right : Named) : Named :=
  { process := CCL.ProgressiveEnclosures.Process.mul
      left.process right.process
    state := (left.state, right.state) }

/-- Denominator apartness is an explicit input to constructive division. -/
structure Apart (name : Named) where
  certificate : CCL.ProgressiveEnclosures.Process.Apart name.process

def div (left right : Named) (apart : Apart right) : Named :=
  { process := CCL.ProgressiveEnclosures.Process.div
      left.process right.process apart.certificate
    state := (left.state, right.state) }

/-- Begin the pure raw output bitstream cursor for an arithmetic name. -/
def machine (name : Named) : Machine := Machine.initial name.process name.state

/-- Unconditional finite-request productivity for any progressive arithmetic
name, including exact zero and opaque exact rational results. -/
theorem productive (name : Named) (count : Nat) :
    (name.machine).emitted.IsPrefix
        (advance name.machine count).emitted ∧
      (advance name.machine count).emitted.length = count := by
  have result := CCL.ProgressiveTransducer.productive
    name.machine count
  simpa only [machine, Machine.initial, List.length_nil, Nat.zero_add]
    using result

theorem add_productive (left right : Named) (count : Nat) :
    ((left.add right).machine).emitted.IsPrefix
        (advance (left.add right).machine count).emitted ∧
      (advance (left.add right).machine count).emitted.length = count :=
  (left.add right).productive count

theorem sub_productive (left right : Named) (count : Nat) :
    ((left.sub right).machine).emitted.IsPrefix
        (advance (left.sub right).machine count).emitted ∧
      (advance (left.sub right).machine count).emitted.length = count :=
  (left.sub right).productive count

theorem mul_productive (left right : Named) (count : Nat) :
    ((left.mul right).machine).emitted.IsPrefix
        (advance (left.mul right).machine count).emitted ∧
      (advance (left.mul right).machine count).emitted.length = count :=
  (left.mul right).productive count

theorem div_productive (left right : Named) (apart : Apart right)
    (count : Nat) :
    ((left.div right apart).machine).emitted.IsPrefix
        (advance (left.div right apart).machine count).emitted ∧
      (advance (left.div right apart).machine count).emitted.length = count :=
  (left.div right apart).productive count

end Named

end CCL.ProgressiveTransducer
