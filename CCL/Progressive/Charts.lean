import mathlib.Tactic.QuotientFreeRing
import CCL.Arithmetic.Controller
import CCL.Encoding.Normalization

/-!
# Constructive chart preparation for progressive CCL arithmetic

The local arithmetic controller needs two chart-side facts which are stronger
than mere convergence of a squared-error radius:

* a possible-value lower norm must be turned into apartness of the whole
  displayed rational ball before affine inversion; and
* a strict possible-value lower norm above one must be turned into a centre
  norm at least one before the redundant loop decision.

This module begins that bridge.  All witnesses are rational candidates in one
explicit finite state.  No completed value is selected.
-/

namespace CCL.ProgressiveCharts

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Ball := CCL.ArithmeticEnclosures.Ball
abbrev Process := CCL.ProgressiveEnclosures.Process

open RFAP.ConstructiveGaussian.Gaussian

/-- A positive lower norm for every candidate admitted by every finite state.
Unlike `Process.Apart`, this initially says nothing about spurious points in
the enclosing ball. -/
structure PossibleApart (process : Process) where
  lowerSq : Coordinate
  positive : 0 < lowerSq
  lower : ∀ (state : process.State) {value : Gaussian},
    process.Possible state value → lowerSq ≤ normSq value

/-- A small common target below each of two positive rational targets. -/
def commonTarget (left right : Coordinate) : Coordinate :=
  (left * right) / (left + right)

theorem commonTarget_pos {left right : Coordinate}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    0 < commonTarget left right :=
  RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct leftPositive rightPositive)
    (add_pos leftPositive rightPositive)

theorem commonTarget_lt_left {left right : Coordinate}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    commonTarget left right < left := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (add_pos leftPositive rightPositive)).2
  have rightLt : right < left + right := by
    calc
      right = 0 + right := (zero_add right).symm
      _ < left + right :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct leftPositive right
  exact RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    leftPositive rightLt

theorem commonTarget_lt_right {left right : Coordinate}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    commonTarget left right < right := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (add_pos leftPositive rightPositive)).2
  have leftLt : left < left + right := by
    calc
      left = 0 + left := (zero_add left).symm
      _ < right + left :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          rightPositive left
      _ = left + right := add_comm _ _
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    rightPositive leftLt
  calc
    left * right = right * left :=
      RFAP.ConstructiveFraction.mul_comm _ _
    _ < right * (left + right) := scaled

private theorem half_mul_two (value : Coordinate) :
    (value / 2) * 2 = value :=
  RFAP.ConstructiveFraction.div_mul_cancel_of_ne value 2 (by decide)

private theorem eighth_mul_eight (value : Coordinate) :
    (value / 8) * 8 = value :=
  RFAP.ConstructiveFraction.div_mul_cancel_of_ne value 8 (by decide)

/-- A possible point with norm at least `lowerSq`, together with radius below
`lowerSq/12`, forces the entire displayed ball to stay at least
`lowerSq/8` away from zero. -/
def apartBallOfPossibleLower (ball : Ball) (lowerSq : Coordinate)
    (lowerPositive : 0 < lowerSq) (witness : Gaussian)
    (inside : ball.Contains witness) (witnessLower : lowerSq ≤ normSq witness)
    (fine : ball.radiusSq < lowerSq / 12) :
    CCL.ArithmeticEnclosures.Ball.Apart ball := by
  let centerNorm := normSq ball.center
  have witnessDecomposition :
      witness = (witness - ball.center) + ball.center := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  have witnessUpper : normSq witness ≤
      2 * (ball.radiusSq + centerNorm) := by
    rw [witnessDecomposition]
    exact (normSq_add_le_two (witness - ball.center) ball.center).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add inside le_rfl) (by decide))
  have centerLower : lowerSq / 2 - ball.radiusSq ≤ centerNorm := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (2 : Coordinate)) _ (by decide)
    apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
      (c := 2 * ball.radiusSq)
    calc
      (lowerSq / 2 - ball.radiusSq) * 2 +
          2 * ball.radiusSq = lowerSq := by
        rw [show (lowerSq / 2 - ball.radiusSq) * 2 =
            (lowerSq / 2) * 2 - ball.radiusSq * 2 by ring1,
          half_mul_two]
        ring1
      _ ≤ normSq witness := witnessLower
      _ ≤ 2 * (ball.radiusSq + centerNorm) := witnessUpper
      _ = centerNorm * 2 + 2 * ball.radiusSq := by ring1
  have twelveRadiusLt : ball.radiusSq * 12 < lowerSq :=
    (RFAP.ConstructiveFraction.lt_div_iff_pos
      (by decide : (0 : Coordinate) < 12)).1 fine
  have sixRadiusLt : ball.radiusSq * 6 < lowerSq := by
    have radiusNonnegative := ball.radiusSq_nonneg
    have sixLeTwelve : ball.radiusSq * 6 ≤ ball.radiusSq * 12 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (by decide) radiusNonnegative
    exact sixLeTwelve.trans_lt twelveRadiusLt
  have separated : 2 * ball.radiusSq < centerNorm := by
    have beforeCenter :
        2 * ball.radiusSq < lowerSq / 2 - ball.radiusSq := by
      apply RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
        (c := ball.radiusSq)
      calc
        2 * ball.radiusSq + ball.radiusSq = 3 * ball.radiusSq := by ring1
        _ < lowerSq / 2 := by
          apply (RFAP.ConstructiveFraction.lt_div_iff_pos
            (by decide : (0 : Coordinate) < 2)).2
          calc
            (3 * ball.radiusSq) * 2 = ball.radiusSq * 6 := by ring1
            _ < lowerSq := sixRadiusLt
        _ = (lowerSq / 2 - ball.radiusSq) + ball.radiusSq := by ring1
    exact beforeCenter.trans_le centerLower
  let raw := CCL.ResidualDecision.apartOfCenter ball separated
  have fixedLower : lowerSq / 8 ≤ raw.lowerSq := by
    dsimp only [raw, CCL.ResidualDecision.apartOfCenter]
    have twelveRadiusLe : ball.radiusSq * 12 ≤ lowerSq :=
      twelveRadiusLt.le
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (8 : Coordinate)) _ (by decide)
    calc
      (lowerSq / 8) * 8 = lowerSq := eighth_mul_eight lowerSq
      _ ≤ 2 * lowerSq - ball.radiusSq * 12 := by
        apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
          (c := ball.radiusSq * 12)
        calc
          lowerSq + ball.radiusSq * 12 =
              ball.radiusSq * 12 + lowerSq := add_comm _ _
          _ ≤ lowerSq + lowerSq :=
            RFAP.ConstructiveFraction.add_le_add_right_direct
              twelveRadiusLe lowerSq
          _ = (2 * lowerSq - ball.radiusSq * 12) +
              ball.radiusSq * 12 := by ring1
      _ = (lowerSq / 2 - ball.radiusSq) * 4 -
          ball.radiusSq * 8 := by
        rw [show (lowerSq / 2 - ball.radiusSq) * 4 =
            ((lowerSq / 2) * 2) * 2 - ball.radiusSq * 4 by ring1,
          half_mul_two]
        ring1
      _ ≤ centerNorm * 4 - ball.radiusSq * 8 := by
        have scaledCenter :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            centerLower (by decide : (0 : Coordinate) ≤ 4)
        calc
          (lowerSq / 2 - ball.radiusSq) * 4 - ball.radiusSq * 8 =
              (lowerSq / 2 - ball.radiusSq) * 4 +
                -(ball.radiusSq * 8) := sub_eq_add_neg _ _
          _ ≤ centerNorm * 4 + -(ball.radiusSq * 8) :=
            RFAP.ConstructiveFraction.add_le_add_right_direct
              scaledCenter (-(ball.radiusSq * 8))
          _ = centerNorm * 4 - ball.radiusSq * 8 :=
            (_root_.sub_eq_add_neg _ _).symm
      _ = (centerNorm / 2 - ball.radiusSq) * 8 := by
        rw [show (centerNorm / 2 - ball.radiusSq) * 8 =
            ((centerNorm / 2) * 2) * 4 - ball.radiusSq * 8 by ring1,
          half_mul_two]
  exact
    { lowerSq := lowerSq / 8
      positive := RFAP.ConstructiveFraction.div_pos_direct lowerPositive
        (by decide)
      lower := fun insideValue => fixedLower.trans (raw.lower insideValue) }

namespace PossibleApart

theorem twelfth_pos {process : Process} (apart : PossibleApart process) :
    0 < apart.lowerSq / 12 :=
  RFAP.ConstructiveFraction.div_pos_direct apart.positive (by decide)

theorem eighth_pos {process : Process} (apart : PossibleApart process) :
    0 < apart.lowerSq / 8 :=
  RFAP.ConstructiveFraction.div_pos_direct apart.positive (by decide)

end PossibleApart

/-- State of a process whose whole displayed ball, rather than merely its
finite candidates, has been made uniformly apart from zero. -/
structure ApartState (process : Process) (apart : PossibleApart process) where
  source : process.State
  wholeBallLower : ∀ {value : Gaussian},
    (process.ball source).Contains value → apart.lowerSq / 8 ≤ normSq value

/-- One finite refinement prepares an arbitrary state for safe affine
inversion. -/
def prepareApartState {process : Process} (apart : PossibleApart process)
    (state : process.State) : ApartState process apart := by
  let refined := process.refine state (apart.lowerSq / 12) apart.twelfth_pos
  rcases process.witness refined with ⟨witness, possible⟩
  let certificate := apartBallOfPossibleLower (process.ball refined)
    apart.lowerSq apart.positive witness (process.possible_inside possible)
    (apart.lower refined possible) (process.accurate state _ _)
  exact
    { source := refined
      wholeBallLower := certificate.lower }

/-- The apartified process.  Its state type retains only explicit finite
source states together with their finite whole-ball separation proofs. -/
def apartify {source : Process} (possibleApart : PossibleApart source) : Process where
  State := ApartState source possibleApart
  ball state := source.ball state.source
  Possible state value := source.Possible state.source value
  witness state := source.witness state.source
  possible_inside possible := source.possible_inside possible
  refine state target positive := by
    let apartTarget := possibleApart.lowerSq / 12
    let inputTarget := commonTarget target apartTarget
    have inputPositive : 0 < inputTarget :=
      commonTarget_pos positive possibleApart.twelfth_pos
    let refined := source.refine state.source inputTarget inputPositive
    rcases source.witness refined with ⟨witness, possible⟩
    have fine : (source.ball refined).radiusSq < possibleApart.lowerSq / 12 :=
      (source.accurate state.source inputTarget inputPositive).trans
        (commonTarget_lt_right positive possibleApart.twelfth_pos)
    let certificate := apartBallOfPossibleLower (source.ball refined)
      possibleApart.lowerSq possibleApart.positive witness
      (source.possible_inside possible) (possibleApart.lower refined possible)
      fine
    exact
      { source := refined
        wholeBallLower := certificate.lower }
  refine_persists := by
    intro state target positive value possible
    exact source.refine_persists state.source _ _ possible
  accurate := by
    intro state target positive
    exact (source.accurate state.source _ _).trans
      (commonTarget_lt_left positive possibleApart.twelfth_pos)
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  center_bounded state := source.center_bounded state.source

/-- Uniform ball apartness of the apartified process. -/
def apartifyApart {source : Process} (possibleApart : PossibleApart source) :
    CCL.ProgressiveEnclosures.Process.Apart
      (apartify possibleApart) where
  lowerSq := possibleApart.lowerSq / 8
  positive := possibleApart.eighth_pos
  lower state := state.wholeBallLower

/-- The prepared state belongs to the apartified process and preserves every
later candidate as a candidate of the original supplied state. -/
theorem prepareApartState_persists {process : Process}
    (apart : PossibleApart process) (state : process.State) {value : Gaussian}
    (possible : (apartify apart).Possible (prepareApartState apart state) value) :
    process.Possible state value :=
  process.refine_persists state _ _ possible

/-! ## Preparing a normalized loop centre -/

/-- Parameterized square-root-free triangle estimate.  The identity behind
the proof is
`weight * (RHS - LHS) = N(weight * u - v)`. -/
theorem normSq_add_le_parameter (weight : Coordinate)
    (weightPositive : 0 < weight) (u v : Gaussian) :
    normSq (u + v) ≤
      (weight + 1) * normSq u +
        ((weight + 1) / weight) * normSq v := by
  let difference :=
    (weight + 1) * normSq u +
      ((weight + 1) / weight) * normSq v - normSq (u + v)
  let scalar : Gaussian := ⟨weight, 0⟩
  have coefficient :
      weight * ((weight + 1) / weight) = weight + 1 := by
    calc
      weight * ((weight + 1) / weight) =
          ((weight + 1) / weight) * weight :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ = weight + 1 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          weightPositive.ne'
  have scaledIdentity :
      weight * difference = normSq (scalar * u - v) := by
    calc
      weight * difference =
          (weight * (weight + 1)) * normSq u +
            (weight * ((weight + 1) / weight)) * normSq v -
            weight * normSq (u + v) := by
        dsimp only [difference]
        ring1
      _ = (weight * (weight + 1)) * normSq u +
            (weight + 1) * normSq v - weight * normSq (u + v) := by
        rw [coefficient]
      _ = normSq (scalar * u - v) := by
        dsimp only [scalar, normSq]
        simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im]
        ring1
  have scaledNonnegative : 0 ≤ weight * difference := by
    rw [scaledIdentity]
    exact normSq_nonneg _
  have differenceNonnegative : 0 ≤ difference := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := weight) _ weightPositive
    calc
      0 * weight = 0 := by ring1
      _ ≤ weight * difference := scaledNonnegative
      _ = difference * weight :=
        RFAP.ConstructiveFraction.mul_comm _ _
  apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
    (c := -normSq (u + v))
  calc
    normSq (u + v) + -normSq (u + v) = 0 := by ring1
    _ ≤ difference := differenceNonnegative
    _ = ((weight + 1) * normSq u +
        ((weight + 1) / weight) * normSq v) +
        -normSq (u + v) := by
      dsimp only [difference]
      ring1

/-- Finite lower-norm data for a loop chart, including a displayed weight
whose triangle coefficient lies strictly below the candidate lower bound. -/
structure LoopDomain (process : Process) where
  lowerSq : Coordinate
  lower : ∀ (state : process.State) {value : Gaussian},
    process.Possible state value → lowerSq ≤ normSq value
  weight : Coordinate
  weightPositive : 0 < weight
  coefficient_lt : (weight + 1) / weight < lowerSq

namespace LoopDomain

/-- Every explicit lower bound strictly above one supplies a usable finite
weight.  The choice `2 / (lowerSq - 1)` is a rational calculation, not an
Archimedean or infinitary selection. -/
def ofLower {process : Process} (apart : PossibleApart process)
    (aboveOne : 1 < apart.lowerSq) : LoopDomain process := by
  let gap := apart.lowerSq - 1
  have gapPositive : 0 < gap :=
    RFAP.ConstructiveFraction.sub_pos_direct aboveOne
  let weight := 2 / gap
  have weightPositive : 0 < weight :=
    RFAP.ConstructiveFraction.div_pos_direct (by decide) gapPositive
  have weightGap : weight * gap = 2 := by
    dsimp only [weight]
    exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne 2 gap
      gapPositive.ne'
  have coefficientLt : (weight + 1) / weight < apart.lowerSq := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos weightPositive).2
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := gap) _ gapPositive
    have gapLtTwice : gap < 2 * gap := by
      calc
        gap = 0 + gap := (zero_add gap).symm
        _ < gap + gap :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct gapPositive gap
        _ = 2 * gap := by ring1
    calc
      (weight + 1) * gap = 2 + gap := by
        calc
          (weight + 1) * gap = weight * gap + gap := by ring1
          _ = 2 + gap := by rw [weightGap]
      _ < 2 + 2 * gap :=
        calc
          2 + gap = gap + 2 := add_comm _ _
          _ < 2 * gap + 2 :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct gapLtTwice 2
          _ = 2 + 2 * gap := add_comm _ _
      _ = (apart.lowerSq * weight) * gap := by
        calc
          2 + 2 * gap = (1 + gap) * 2 := by ring1
          _ = apart.lowerSq * 2 := by
            dsimp only [gap]
            ring1
          _ = apart.lowerSq * (weight * gap) := by rw [weightGap]
          _ = (apart.lowerSq * weight) * gap :=
            (_root_.mul_assoc _ _ _).symm
  exact
    { lowerSq := apart.lowerSq
      lower := apart.lower
      weight := weight
      weightPositive := weightPositive
      coefficient_lt := coefficientLt }

def slack {process : Process} (domain : LoopDomain process) : Coordinate :=
  domain.lowerSq - (domain.weight + 1) / domain.weight

theorem slack_pos {process : Process} (domain : LoopDomain process) :
    0 < domain.slack :=
  RFAP.ConstructiveFraction.sub_pos_direct domain.coefficient_lt

def normalizationTarget {process : Process}
    (domain : LoopDomain process) : Coordinate :=
  domain.slack / (domain.weight + 1)

theorem weight_add_one_pos {process : Process}
    (domain : LoopDomain process) : 0 < domain.weight + 1 :=
  add_pos domain.weightPositive (by decide)

theorem normalizationTarget_pos {process : Process}
    (domain : LoopDomain process) : 0 < domain.normalizationTarget :=
  RFAP.ConstructiveFraction.div_pos_direct domain.slack_pos
    domain.weight_add_one_pos

/-- A fine enough ball around one admitted rational candidate has normalized
centre norm at least one. -/
theorem center_normalized_of_fine {process : Process}
    (domain : LoopDomain process) (state : process.State)
    (fine : (process.ball state).radiusSq < domain.normalizationTarget) :
    1 ≤ normSq (process.ball state).center := by
  rcases process.witness state with ⟨witness, possible⟩
  have inside := process.possible_inside possible
  have witnessLower := domain.lower state possible
  let error := witness - (process.ball state).center
  have decomposition : witness = error + (process.ball state).center := by
    dsimp only [error]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  by_cases normalized : 1 ≤ normSq (process.ball state).center
  · exact normalized
  · have centerLt : normSq (process.ball state).center < 1 :=
      lt_of_not_ge normalized
    have coefficientPositive :
        0 < (domain.weight + 1) / domain.weight :=
      RFAP.ConstructiveFraction.div_pos_direct domain.weight_add_one_pos
        domain.weightPositive
    have errorNorm : normSq error ≤ (process.ball state).radiusSq := by
      exact inside
    have errorTerm :
        (domain.weight + 1) * normSq error < domain.slack := by
      have errorSmall : normSq error < domain.normalizationTarget :=
        errorNorm.trans_lt fine
      have scaled := (RFAP.ConstructiveFraction.lt_div_iff_pos
        domain.weight_add_one_pos).1 errorSmall
      calc
        (domain.weight + 1) * normSq error =
            normSq error * (domain.weight + 1) :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ < domain.slack := scaled
    have centerTerm :
        ((domain.weight + 1) / domain.weight) *
            normSq (process.ball state).center <
          (domain.weight + 1) / domain.weight := by
      have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        coefficientPositive centerLt
      simpa only [RFAP.ConstructiveFraction.mul_one_direct] using scaled
    have strictUpper : normSq witness < domain.lowerSq := by
      rw [decomposition]
      calc
        normSq (error + (process.ball state).center) ≤
            (domain.weight + 1) * normSq error +
              ((domain.weight + 1) / domain.weight) *
                normSq (process.ball state).center :=
          normSq_add_le_parameter domain.weight domain.weightPositive _ _
        _ < domain.slack +
            (domain.weight + 1) / domain.weight :=
          RFAP.ConstructiveFraction.add_lt_add_direct errorTerm centerTerm
        _ = domain.lowerSq := by
          unfold slack
          ring1
    exact ((not_lt_of_ge witnessLower) strictUpper).elim

/-- One request target which is simultaneously below the normalization and
uniform redundant-output thresholds. -/
def decisionTarget {process : Process} (domain : LoopDomain process) :
    Coordinate :=
  commonTarget domain.normalizationTarget
    CCL.RedundantOutput.uniformRadiusSq

theorem decisionTarget_pos {process : Process}
    (domain : LoopDomain process) : 0 < domain.decisionTarget :=
  commonTarget_pos domain.normalizationTarget_pos
    CCL.RedundantOutput.uniformRadiusSq_pos

def refinedState {process : Process} (domain : LoopDomain process)
    (state : process.State) : process.State :=
  process.refine state domain.decisionTarget domain.decisionTarget_pos

theorem refined_accurate {process : Process} (domain : LoopDomain process)
    (state : process.State) :
    (process.ball (domain.refinedState state)).radiusSq <
      CCL.RedundantOutput.uniformRadiusSq :=
  (process.accurate state _ _).trans
    (commonTarget_lt_right domain.normalizationTarget_pos
      CCL.RedundantOutput.uniformRadiusSq_pos)

theorem refined_center_normalized {process : Process}
    (domain : LoopDomain process) (state : process.State) :
    1 ≤ normSq (process.ball (domain.refinedState state)).center := by
  apply domain.center_normalized_of_fine
  exact (process.accurate state _ _).trans
    (commonTarget_lt_left domain.normalizationTarget_pos
      CCL.RedundantOutput.uniformRadiusSq_pos)

/-- Total loop decision from the semantically natural strict lower norm,
without assuming normalized rational centres at every prior state. -/
def decide {process : Process} (domain : LoopDomain process)
    (state : process.State) :
    CCL.RedundantOutput.Decision
      (process.ball (domain.refinedState state)) :=
  CCL.RedundantOutput.decide _
    (domain.refined_center_normalized state) (domain.refined_accurate state)

end LoopDomain

/-! ## Rebasing and exact translations -/

/-- A later source state together with a finite proof that all its candidates
were already candidates of one fixed base state. -/
structure BasedState (process : Process) (base : process.State) where
  source : process.State
  persists : ∀ {value : Gaussian},
    process.Possible source value → process.Possible base value

namespace BasedState

def initial (process : Process) (base : process.State) :
    BasedState process base :=
  { source := base
    persists := fun possible => possible }

end BasedState

/-- Restrict a progressive process to the refinement future of one explicit
finite base state. -/
def based (process : Process) (base : process.State) : Process where
  State := BasedState process base
  ball state := process.ball state.source
  Possible state value := process.Possible state.source value
  witness state := process.witness state.source
  possible_inside possible := process.possible_inside possible
  refine state target positive :=
    { source := process.refine state.source target positive
      persists := fun possible =>
        state.persists
          (process.refine_persists state.source target positive possible) }
  refine_persists := by
    intro state target positive value possible
    exact process.refine_persists state.source target positive possible
  accurate state target positive := process.accurate state.source target positive
  centerBound := process.centerBound
  centerBound_nonneg := process.centerBound_nonneg
  center_bounded state := process.center_bounded state.source

theorem based_initial_persists (process : Process) (base : process.State)
    {state : (based process base).State} {value : Gaussian}
    (possible : (based process base).Possible state value) :
    process.Possible base value :=
  state.persists possible

/-- The exact zero-radius ball at a displayed rational point. -/
def pointBall (point : Gaussian) : Ball :=
  { center := point
    radiusSq := 0
    radiusSq_nonneg := le_rfl }

theorem pointBall_contains (point : Gaussian) :
    (pointBall point).Contains point := by
  unfold pointBall CCL.ArithmeticEnclosures.Ball.Contains
  rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]

/-- Exact rational translation of a progressive process. -/
def translate (process : Process) (shift : Gaussian) : Process where
  State := process.State
  ball state := (process.ball state).sub (pointBall shift)
  Possible state value := ∃ sourceValue : Gaussian,
    process.Possible state sourceValue ∧ value = sourceValue - shift
  witness state := by
    rcases process.witness state with ⟨sourceValue, possible⟩
    exact ⟨sourceValue - shift, sourceValue, possible, rfl⟩
  possible_inside := by
    rintro state value ⟨sourceValue, possible, rfl⟩
    exact CCL.ArithmeticEnclosures.Ball.contains_sub
      (process.possible_inside possible) (pointBall_contains shift)
  refine state target positive :=
    process.refine state (CCL.ProgressiveEnclosures.Name.additiveInputTarget
      target) (CCL.ProgressiveEnclosures.Name.quarter_pos positive)
  refine_persists := by
    rintro state target positive value ⟨sourceValue, possible, equal⟩
    exact ⟨sourceValue, process.refine_persists state _ _ possible, equal⟩
  accurate := by
    intro state target positive
    apply CCL.ProgressiveEnclosures.Name.add_radius_lt
    · exact process.accurate state _ _
    · exact CCL.ProgressiveEnclosures.Name.quarter_pos positive
  centerBound := 2 * (process.centerBound + normSq shift)
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg process.centerBound_nonneg (normSq_nonneg shift))
  center_bounded := by
    intro state
    change normSq ((process.ball state).center - shift) ≤
      2 * (process.centerBound + normSq shift)
    exact (normSq_sub_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (process.center_bounded state) le_rfl) (by decide))

/-! ## A safe emitted sector gives a persistent residual chart -/

/-- Rational uniform residual upper bound already contained in a safe-ball
certificate. -/
def safeResidualUpper (sector : CCL.Sectors.Sector)
    (ball : Ball) : Coordinate :=
  16 * ball.radiusSq +
    (16 / 15) * normSq (ball.center - sector.rep)

theorem safeResidualUpper_lt_half
    {sector : CCL.Sectors.Sector} {ball : Ball}
    (safe : CCL.RedundantOutput.SafeBall sector ball) :
    safeResidualUpper sector ball < 1 / 2 :=
  safe

/-- Every admitted candidate of the rebased residual process satisfies the
same explicit upper bound as the ball on which the sector was emitted. -/
theorem translated_based_norm_le_safeResidualUpper
    (process : Process) (base : process.State)
    (sector : CCL.Sectors.Sector)
    (_safe : CCL.RedundantOutput.SafeBall sector (process.ball base))
    {state : (translate (based process base) sector.rep).State}
    {residual : Gaussian}
    (possible : (translate (based process base) sector.rep).Possible
      state residual) :
    normSq residual ≤ safeResidualUpper sector (process.ball base) := by
  rcases possible with ⟨sourceValue, sourcePossible, residualEqual⟩
  have basePossible : process.Possible base sourceValue :=
    state.persists sourcePossible
  have inside := process.possible_inside basePossible
  have difference :
      sourceValue - sector.rep =
        (sourceValue - (process.ball base).center) +
          ((process.ball base).center - sector.rep) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  rw [residualEqual, difference]
  exact (CCL.RedundantOutput.normSq_add_le_weighted _ _).trans
    (add_le_add
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        inside (by decide)) le_rfl)

/-- Turn a whole-ball apartness certificate at a base state into uniform
candidate apartness throughout its rebased future. -/
def possibleApartOfBall
    (process : Process) (base : process.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (process.ball base)) : PossibleApart (based process base) where
  lowerSq := certificate.lowerSq
  positive := certificate.positive
  lower := by
    intro state value valuePossible
    exact certificate.lower
      (process.possible_inside (state.persists valuePossible))

/-- Residual process after emitting a safe sector at one finite source state. -/
def residualProcess (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector) : Process :=
  translate (based source base) sector.rep

def residualInitial (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector) :
    (residualProcess source base sector).State :=
  BasedState.initial source base

/-- Candidate apartness inherited from a residual ball on which the
small-or-apart controller selected its apart branch. -/
def residualFuturePossibleApart
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector)
    (residualBase : (residualProcess source base sector).State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      ((residualProcess source base sector).ball residualBase)) :
    PossibleApart (based (residualProcess source base sector) residualBase) :=
  possibleApartOfBall _ _ certificate

/-- Apartified residual future used as the denominator of the exact inverse
chart. -/
def apartResidualFuture
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector)
    (residualBase : (residualProcess source base sector).State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      ((residualProcess source base sector).ball residualBase)) : Process :=
  apartify
    (residualFuturePossibleApart source base sector residualBase certificate)

/-- Exact affine inverse tail `gamma⁻¹ / residual`. -/
def inverseTailProcess
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector)
    (residualBase : (residualProcess source base sector).State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      ((residualProcess source base sector).ball residualBase)) : Process :=
  let denominator :=
    apartResidualFuture source base sector residualBase certificate
  CCL.ProgressiveEnclosures.Process.div
    (CCL.ProgressiveEnclosures.Process.exact gamma⁻¹)
    denominator
    (apartifyApart
      (residualFuturePossibleApart source base sector residualBase certificate))

/-- Explicit initial state of the inverse-tail process. -/
def inverseTailInitial
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector)
    (residualBase : (residualProcess source base sector).State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      ((residualProcess source base sector).ball residualBase)) :
    (inverseTailProcess source base sector residualBase certificate).State :=
  let possibleApart :=
    residualFuturePossibleApart source base sector residualBase certificate
  ((), prepareApartState possibleApart
    (BasedState.initial (residualProcess source base sector) residualBase))

/-- The original safe-sector upper bound persists through rebasing and
apartification of the residual process. -/
theorem apartResidualFuture_norm_le_upper
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector)
    (safe : CCL.RedundantOutput.SafeBall sector (source.ball base))
    (residualBase : (residualProcess source base sector).State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      ((residualProcess source base sector).ball residualBase))
    {state : (apartResidualFuture source base sector residualBase
      certificate).State} {residual : Gaussian}
    (possible : (apartResidualFuture source base sector residualBase
      certificate).Possible state residual) :
    normSq residual ≤ safeResidualUpper sector (source.ball base) := by
  apply translated_based_norm_le_safeResidualUpper source base sector safe
  exact state.source.persists possible

theorem safeResidualUpper_pos_of_apart
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector)
    (safe : CCL.RedundantOutput.SafeBall sector (source.ball base))
    (residualBase : (residualProcess source base sector).State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      ((residualProcess source base sector).ball residualBase)) :
    0 < safeResidualUpper sector (source.ball base) := by
  rcases (residualProcess source base sector).witness residualBase with
    ⟨residual, possible⟩
  have residualLower := certificate.lower
    ((residualProcess source base sector).possible_inside possible)
  have residualUpper :=
    translated_based_norm_le_safeResidualUpper source base sector safe possible
  exact certificate.positive.trans_le (residualLower.trans residualUpper)

/-- Uniform lower norm of every affine inverse-tail candidate. -/
def inverseTailLower
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector) : Coordinate :=
  1 / (2 * safeResidualUpper sector (source.ball base))

theorem inverseTailLower_pos
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector)
    (safe : CCL.RedundantOutput.SafeBall sector (source.ball base))
    (residualBase : (residualProcess source base sector).State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      ((residualProcess source base sector).ball residualBase)) :
    0 < inverseTailLower source base sector := by
  apply RFAP.ConstructiveFraction.div_pos_direct (by decide)
  exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (safeResidualUpper_pos_of_apart source base sector safe residualBase
      certificate)

theorem inverseTailLower_gt_one
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector)
    (safe : CCL.RedundantOutput.SafeBall sector (source.ball base))
    (residualBase : (residualProcess source base sector).State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      ((residualProcess source base sector).ball residualBase)) :
    1 < inverseTailLower source base sector := by
  let upper := safeResidualUpper sector (source.ball base)
  have upperPositive : 0 < upper :=
    safeResidualUpper_pos_of_apart source base sector safe residualBase
      certificate
  have denominatorPositive : 0 < 2 * upper :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) upperPositive
  apply (RFAP.ConstructiveFraction.lt_div_iff_pos denominatorPositive).2
  change 1 * (2 * upper) < 1
  calc
    1 * (2 * upper) = 2 * upper := by ring1
    _ < 1 := by
      have half := safeResidualUpper_lt_half safe
      have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide : (0 : Coordinate) < 2) half
      calc
        2 * upper < 2 * (1 / 2) := scaled
        _ = 1 := by
          calc
            2 * (1 / 2 : Coordinate) = (1 / 2) * 2 :=
              RFAP.ConstructiveFraction.mul_comm _ _
            _ = 1 :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 2 (by decide)

private theorem normSq_gamma_inv : normSq gamma⁻¹ = (1 / 2 : Coordinate) := by
  rw [inv_eq, normSq_inv gamma (by decide), normSq_gamma]
  change (2 : Coordinate)⁻¹ = 1 / 2
  change (2 : Coordinate)⁻¹ = 1 * (2 : Coordinate)⁻¹
  exact (_root_.one_mul _).symm

private theorem half_mul_inverse (value : Coordinate) :
    (1 / 2 : Coordinate) * value⁻¹ = 1 / (2 * value) := by
  have oneDiv : (1 / value : Coordinate) = value⁻¹ := by
    change 1 * value⁻¹ = value⁻¹
    exact one_mul _
  calc
    (1 / 2 : Coordinate) * value⁻¹ =
        (1 / 2) * (1 / value) := by rw [oneDiv]
    _ = (1 * 1) / (2 * value) :=
      RFAP.ConstructiveFraction.div_mul_div_direct 1 2 1 value
    _ = 1 / (2 * value) := by
      apply congrArg (fun numerator : Coordinate => numerator / (2 * value))
      exact RFAP.ConstructiveFraction.mul_one_direct 1

/-- Every candidate of the inverse-tail process has one uniform rational
lower norm strictly above one. -/
def inverseTailPossibleApart
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector)
    (safe : CCL.RedundantOutput.SafeBall sector (source.ball base))
    (residualBase : (residualProcess source base sector).State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      ((residualProcess source base sector).ball residualBase)) :
    PossibleApart
      (inverseTailProcess source base sector residualBase certificate) := by
  let residualFuture :=
    apartResidualFuture source base sector residualBase certificate
  let residualApart :=
    residualFuturePossibleApart source base sector residualBase certificate
  exact
    { lowerSq := inverseTailLower source base sector
      positive := inverseTailLower_pos source base sector safe residualBase
        certificate
      lower := by
        intro state value possible
        rcases possible with
          ⟨numerator, residual, numeratorPossible, residualPossible, valueEqual⟩
        have numeratorEqual : numerator = gamma⁻¹ := numeratorPossible
        have residualUpper : normSq residual ≤
            safeResidualUpper sector (source.ball base) :=
          apartResidualFuture_norm_le_upper source base sector safe
            residualBase certificate residualPossible
        have residualLower := residualApart.lower state.2.source residualPossible
        have residualNormPositive : 0 < normSq residual :=
          residualApart.positive.trans_le residualLower
        have residualNonzero : residual ≠ 0 := by
          intro residualZero
          rw [residualZero, normSq_zero] at residualNormPositive
          exact (lt_irrefl _ residualNormPositive).elim
        rw [valueEqual, numeratorEqual,
          normSq_div _ _ residualNonzero, normSq_gamma_inv,
          half_mul_inverse]
        apply RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
          (by decide : (0 : Coordinate) ≤ 1)
          (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
            residualNormPositive)
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          residualUpper (by decide) }

/-- The inverse tail therefore supplies the semantically natural loop domain
needed by the total redundant decision. -/
def inverseTailLoopDomain
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector)
    (safe : CCL.RedundantOutput.SafeBall sector (source.ball base))
    (residualBase : (residualProcess source base sector).State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      ((residualProcess source base sector).ball residualBase)) :
    LoopDomain (inverseTailProcess source base sector residualBase certificate) :=
  LoopDomain.ofLower
    (inverseTailPossibleApart source base sector safe residualBase certificate)
    (inverseTailLower_gt_one source base sector safe residualBase certificate)

private theorem gaussian_mul_pair_swap (a b c d : Gaussian) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  calc
    (a * b) * (c * d) = a * (b * (c * d)) :=
      RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
    _ = a * ((b * c) * d) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc b c d]
    _ = a * ((c * b) * d) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm b c]
    _ = a * (c * (b * d)) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc c b d]
    _ = (a * c) * (b * d) :=
      (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm

/-- The affine expression used by `inverseTailProcess` is exactly the CCL
post-sector inverse chart. -/
theorem gamma_inv_div_eq_inverse (residual : Gaussian)
    (residualNonzero : residual ≠ 0) :
    gamma⁻¹ / residual = (gamma * residual)⁻¹ := by
  have gammaNonzero : gamma ≠ 0 := by decide
  have productNonzero : gamma * residual ≠ 0 :=
    mul_ne_zero_direct gammaNonzero residualNonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne productNonzero
  calc
    (gamma⁻¹ / residual) * (gamma * residual) =
        (gamma⁻¹ * residual⁻¹) * (gamma * residual) := by
      rw [RFAP.ExplicitField.div_eq_mul_inv]
    _ = (gamma⁻¹ * gamma) * (residual⁻¹ * residual) :=
      gaussian_mul_pair_swap _ _ _ _
    _ = (1 : Gaussian) * 1 := by
      apply congrArg₂ (fun left right : Gaussian => left * right)
      · exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
          gamma gammaNonzero
      · exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
          residual residualNonzero
    _ = 1 := RFAP.ConstructiveGaussian.Gaussian.mul_one _
    _ = (gamma * residual)⁻¹ * (gamma * residual) :=
      (RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
        (gamma * residual) productNonzero).symm

/-- Every later inverse-tail candidate is the exact inverse chart of a
nonzero residual candidate already admitted at the selected residual base. -/
theorem inverseTail_candidate_semantics
    (source : Process) (base : source.State)
    (sector : CCL.Sectors.Sector)
    (residualBase : (residualProcess source base sector).State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      ((residualProcess source base sector).ball residualBase))
    {state : (inverseTailProcess source base sector residualBase
      certificate).State} {tail : Gaussian}
    (possible : (inverseTailProcess source base sector residualBase
      certificate).Possible state tail) :
    ∃ residual : Gaussian,
      (residualProcess source base sector).Possible residualBase residual ∧
      residual ≠ 0 ∧ tail = (gamma * residual)⁻¹ := by
  let residualApart :=
    residualFuturePossibleApart source base sector residualBase certificate
  rcases possible with
    ⟨numerator, residual, numeratorPossible, residualPossible, tailEqual⟩
  have residualAtBase :
      (residualProcess source base sector).Possible residualBase residual :=
    state.2.source.persists residualPossible
  have residualLower := residualApart.lower state.2.source residualPossible
  have residualNormPositive : 0 < normSq residual :=
    residualApart.positive.trans_le residualLower
  have residualNonzero : residual ≠ 0 := by
    intro residualZero
    rw [residualZero, normSq_zero] at residualNormPositive
    exact (lt_irrefl _ residualNormPositive).elim
  refine ⟨residual, residualAtBase, residualNonzero, ?_⟩
  calc
    tail = numerator / residual := tailEqual
    _ = gamma⁻¹ / residual := by rw [numeratorPossible]
    _ = (gamma * residual)⁻¹ :=
      gamma_inv_div_eq_inverse residual residualNonzero

/-! ## Unary loop scaling -/

/-- Explicit candidate lower norm extracted from a unary-ball certificate. -/
def unaryCandidateLower (ball : Ball) : Coordinate :=
  (normSq ball.center - 16 * ball.radiusSq) / (16 / 15)

private theorem sixteen_fifteenths_pos :
    (0 : Coordinate) < 16 / 15 :=
  RFAP.ConstructiveFraction.div_pos_direct (by decide) (by decide)

theorem unaryCandidateLower_gt_two {ball : Ball}
    (unary : CCL.RedundantOutput.UnaryBall ball) :
    2 < unaryCandidateLower ball := by
  apply (RFAP.ConstructiveFraction.lt_div_iff_pos
    sixteen_fifteenths_pos).2
  apply RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
    (c := 16 * ball.radiusSq)
  calc
    2 * (16 / 15) + 16 * ball.radiusSq =
        (16 / 15) * 2 + 16 * ball.radiusSq := by ring1
    _ < normSq ball.center := unary
    _ = (normSq ball.center - 16 * ball.radiusSq) +
        16 * ball.radiusSq := by ring1

theorem unaryCandidateLower_le {ball : Ball} {value : Gaussian}
    (inside : ball.Contains value) :
    unaryCandidateLower ball ≤ normSq value := by
  have centerDecomposition :
      ball.center = (ball.center - value) + value := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  have errorNorm : normSq (ball.center - value) ≤ ball.radiusSq := by
    have difference : ball.center - value = -(value - ball.center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
    rw [difference, normSq_neg]
    exact inside
  have centerUpper : normSq ball.center ≤
      16 * ball.radiusSq + (16 / 15) * normSq value := by
    rw [centerDecomposition]
    exact (CCL.RedundantOutput.normSq_add_le_weighted
      (ball.center - value) value).trans
      (add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          errorNorm (by decide)) le_rfl)
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    sixteen_fifteenths_pos).2
  apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
    (c := 16 * ball.radiusSq)
  calc
    normSq ball.center - 16 * ball.radiusSq + 16 * ball.radiusSq =
        normSq ball.center := by ring1
    _ ≤ 16 * ball.radiusSq + (16 / 15) * normSq value := centerUpper
    _ = normSq value * (16 / 15) + 16 * ball.radiusSq := by ring1

/-- Process after one emitted unary-one digit, normalized by multiplication
with `gamma⁻¹`. -/
def unaryScaledProcess (source : Process) (base : source.State) : Process :=
  CCL.ProgressiveEnclosures.Process.mul
    (CCL.ProgressiveEnclosures.Process.exact gamma⁻¹)
    (based source base)

def unaryScaledInitial (source : Process) (base : source.State) :
    (unaryScaledProcess source base).State :=
  ((), BasedState.initial source base)

/-- Every later candidate after a unary output is exactly the preceding
candidate multiplied by the inverse unary scale. -/
theorem unaryScaled_candidate_semantics
    (source : Process) (base : source.State)
    {state : (unaryScaledProcess source base).State} {value : Gaussian}
    (possible : (unaryScaledProcess source base).Possible state value) :
    ∃ sourceValue : Gaussian,
      source.Possible base sourceValue ∧
      value = gamma⁻¹ * sourceValue := by
  rcases possible with
    ⟨factor, sourceValue, factorPossible, sourcePossible, valueEqual⟩
  exact ⟨sourceValue, state.2.persists sourcePossible,
    valueEqual.trans (congrArg (fun item => item * sourceValue)
      factorPossible)⟩

def unaryScaledLower (source : Process) (base : source.State) : Coordinate :=
  unaryCandidateLower (source.ball base) / 2

theorem unaryScaledLower_gt_one
    (source : Process) (base : source.State)
    (unary : CCL.RedundantOutput.UnaryBall (source.ball base)) :
    1 < unaryScaledLower source base := by
  apply (RFAP.ConstructiveFraction.lt_div_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    1 * 2 = 2 := by ring1
    _ < unaryCandidateLower (source.ball base) :=
      unaryCandidateLower_gt_two unary

/-- Uniform candidate lower norm after unary normalization. -/
def unaryScaledPossibleApart
    (source : Process) (base : source.State)
    (_unary : CCL.RedundantOutput.UnaryBall (source.ball base)) :
    PossibleApart (unaryScaledProcess source base) := by
  exact
    { lowerSq := unaryScaledLower source base
      positive := lt_trans (by decide : (0 : Coordinate) < 1)
        (unaryScaledLower_gt_one source base _unary)
      lower := by
        intro state value possible
        rcases possible with
          ⟨factor, sourceValue, factorPossible, sourcePossible, valueEqual⟩
        have factorEqual : factor = gamma⁻¹ := factorPossible
        have sourceAtBase : source.Possible base sourceValue :=
          state.2.persists sourcePossible
        have sourceLower := unaryCandidateLower_le
          (source.possible_inside sourceAtBase)
        rw [valueEqual, factorEqual, normSq_mul, normSq_gamma_inv]
        change unaryCandidateLower (source.ball base) / 2 ≤
          (1 / 2 : Coordinate) * normSq sourceValue
        have halfIdentity : (1 / 2 : Coordinate) * normSq sourceValue =
            normSq sourceValue / 2 := by
          change (1 * (2 : Coordinate)⁻¹) * normSq sourceValue =
            normSq sourceValue * (2 : Coordinate)⁻¹
          calc
            (1 * (2 : Coordinate)⁻¹) * normSq sourceValue =
                (2 : Coordinate)⁻¹ * normSq sourceValue := by
              rw [_root_.one_mul]
            _ = normSq sourceValue * (2 : Coordinate)⁻¹ :=
              RFAP.ConstructiveFraction.mul_comm _ _
        rw [halfIdentity]
        apply (RFAP.ConstructiveFraction.div_le_iff_pos
          (by decide : (0 : Coordinate) < 2)).2
        calc
          unaryCandidateLower (source.ball base) ≤ normSq sourceValue :=
            sourceLower
          _ = (normSq sourceValue / 2) * 2 :=
            (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
              (normSq sourceValue) 2 (by decide)).symm }

def unaryScaledLoopDomain
    (source : Process) (base : source.State)
    (unary : CCL.RedundantOutput.UnaryBall (source.ball base)) :
    LoopDomain (unaryScaledProcess source base) :=
  LoopDomain.ofLower (unaryScaledPossibleApart source base unary)
    (unaryScaledLower_gt_one source base unary)

/-! ## Inverse normalization after retained unary padding -/

/-- Generic exact inverse chart based at an apart residual state. -/
def inverseOfApartProcess
    (residual : Process) (base : residual.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (residual.ball base)) : Process :=
  let candidateApart := possibleApartOfBall residual base certificate
  let denominator := apartify candidateApart
  CCL.ProgressiveEnclosures.Process.div
    (CCL.ProgressiveEnclosures.Process.exact gamma⁻¹)
    denominator (apartifyApart candidateApart)

def inverseOfApartInitial
    (residual : Process) (base : residual.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (residual.ball base)) :
    (inverseOfApartProcess residual base certificate).State :=
  let candidateApart := possibleApartOfBall residual base certificate
  ((), prepareApartState candidateApart (BasedState.initial residual base))

/-- Divide the inverse tail by the unary scale already emitted. -/
def normalizedInverseProcess
    (residual : Process) (base : residual.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (residual.ball base)) (count : Nat) : Process :=
  CCL.ProgressiveEnclosures.Process.mul
    (CCL.ProgressiveEnclosures.Process.exact
      (natPow gamma count)⁻¹)
    (inverseOfApartProcess residual base certificate)

def normalizedInverseInitial
    (residual : Process) (base : residual.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (residual.ball base)) (count : Nat) :
    (normalizedInverseProcess residual base certificate count).State :=
  ((), inverseOfApartInitial residual base certificate)

/-- Every candidate of the normalized inverse chart is an exact scaled
post-sector inverse of one nonzero residual admitted at the retained base.
The scale records precisely the unary padding already emitted. -/
theorem normalizedInverse_candidate_semantics
    (residual : Process) (base : residual.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (residual.ball base)) (count : Nat)
    {state : (normalizedInverseProcess residual base certificate count).State}
    {value : Gaussian}
    (possible : (normalizedInverseProcess residual base certificate count).Possible
      state value) :
    ∃ residualValue : Gaussian,
      residual.Possible base residualValue ∧
      residualValue ≠ 0 ∧
      value = (natPow gamma count)⁻¹ * (gamma * residualValue)⁻¹ := by
  rcases possible with
    ⟨scale, inverseTail, scalePossible, inversePossible, valueEqual⟩
  rcases inversePossible with
    ⟨numerator, residualValue, numeratorPossible, residualPossible,
      inverseEqual⟩
  have residualAtBase : residual.Possible base residualValue :=
    state.2.2.source.persists residualPossible
  have residualNormPositive : 0 < normSq residualValue :=
    certificate.positive.trans_le
      (certificate.lower (residual.possible_inside residualAtBase))
  have residualNonzero : residualValue ≠ 0 := by
    intro residualZero
    rw [residualZero, normSq_zero] at residualNormPositive
    exact (lt_irrefl _ residualNormPositive).elim
  refine ⟨residualValue, residualAtBase, residualNonzero, ?_⟩
  calc
    value = scale * inverseTail := valueEqual
    _ = (natPow gamma count)⁻¹ * (numerator / residualValue) := by
      rw [scalePossible, inverseEqual]
    _ = (natPow gamma count)⁻¹ * (gamma⁻¹ / residualValue) := by
      rw [numeratorPossible]
    _ = (natPow gamma count)⁻¹ * (gamma * residualValue)⁻¹ := by
      rw [gamma_inv_div_eq_inverse residualValue residualNonzero]

private theorem normSq_natPow_gamma_inv (count : Nat) :
    normSq ((natPow gamma count)⁻¹) = ((2 : Coordinate) ^ count)⁻¹ := by
  have powerNonzero : natPow gamma count ≠ 0 :=
    natPow_ne_zero_direct gamma (by decide) count
  rw [inv_eq, normSq_inv _ powerNonzero, normSq_natPow, normSq_gamma]

/-- Candidate apartness of a normalized inverse process from a retained
strict residual upper bound. -/
def normalizedInversePossibleApart
    (residual : Process) (base : residual.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (residual.ball base)) (count : Nat) (upper : Coordinate)
    (upperBound : ∀ {value : Gaussian}, residual.Possible base value →
      normSq value ≤ upper)
    (upperStrict : upper <
      CCL.ResidualDecision.paddingTarget count) :
    PossibleApart (normalizedInverseProcess residual base certificate count) := by
  let power : Coordinate := (2 : Coordinate) ^ (count + 1)
  let lowerSq : Coordinate := (power * upper)⁻¹
  rcases residual.witness base with ⟨displayed, displayedPossible⟩
  have displayedLower := certificate.lower
    (residual.possible_inside displayedPossible)
  have upperPositive : 0 < upper :=
    certificate.positive.trans_le
      (displayedLower.trans (upperBound displayedPossible))
  have powerPositive : 0 < power :=
    RFAP.ConstructiveFraction.pow_pos_direct (by decide) (count + 1)
  have denominatorPositive : 0 < power * upper :=
    RFAP.ConstructiveFraction.mul_pos_direct powerPositive upperPositive
  have denominatorLtOne : power * upper < 1 := by
    have scaled := (RFAP.ConstructiveFraction.lt_div_iff_pos powerPositive).1
      upperStrict
    calc
      power * upper = upper * power :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ < 1 := scaled
  have lowerPositive : 0 < lowerSq := by
    exact RFAP.ConstructiveFraction.inv_pos_direct denominatorPositive
  have lowerGtOne : 1 < lowerSq := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := power * upper) _ denominatorPositive
    calc
      1 * (power * upper) = power * upper := by ring1
      _ < 1 := denominatorLtOne
      _ = (power * upper)⁻¹ * (power * upper) :=
        (RFAP.ConstructiveFraction.inv_mul_cancel _
          denominatorPositive.ne').symm
  let candidateApart := possibleApartOfBall residual base certificate
  exact
    { lowerSq := lowerSq
      positive := lowerPositive
      lower := by
        intro state value possible
        rcases possible with
          ⟨scale, tail, scalePossible, tailPossible, valueEqual⟩
        rcases tailPossible with
          ⟨numerator, denominator, numeratorPossible,
            denominatorPossible, tailEqual⟩
        have denominatorAtBase : residual.Possible base denominator :=
          state.2.2.source.persists denominatorPossible
        have denominatorUpper := upperBound denominatorAtBase
        have denominatorLower :=
          candidateApart.lower state.2.2.source denominatorPossible
        have denominatorNormPositive : 0 < normSq denominator :=
          candidateApart.positive.trans_le denominatorLower
        have denominatorNonzero : denominator ≠ 0 := by
          intro denominatorZero
          rw [denominatorZero, normSq_zero] at denominatorNormPositive
          exact (lt_irrefl _ denominatorNormPositive).elim
        have smallDenominatorPositive :
            0 < power * normSq denominator :=
          RFAP.ConstructiveFraction.mul_pos_direct powerPositive
            denominatorNormPositive
        have smallDenominatorLe :
            power * normSq denominator ≤ power * upper :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            denominatorUpper powerPositive.le
        have inverseOrder : (power * upper)⁻¹ ≤
            (power * normSq denominator)⁻¹ :=
          RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct
            smallDenominatorPositive smallDenominatorLe
        rw [valueEqual, scalePossible, tailEqual, numeratorPossible,
          normSq_mul, normSq_natPow_gamma_inv,
          normSq_div _ _ denominatorNonzero, normSq_gamma_inv,
          half_mul_inverse]
        have normIdentity :
            ((2 : Coordinate) ^ count)⁻¹ *
                (1 / (2 * normSq denominator)) =
              (power * normSq denominator)⁻¹ := by
          have firstInverse :
              (1 / (2 * normSq denominator) : Coordinate) =
                (2 * normSq denominator)⁻¹ := by
            change 1 * (2 * normSq denominator)⁻¹ =
              (2 * normSq denominator)⁻¹
            exact _root_.one_mul _
          rw [firstInverse, ← RFAP.ConstructiveFraction.inv_mul_direct]
          apply congrArg (fun coordinate : Coordinate => coordinate⁻¹)
          dsimp only [power]
          rw [pow_succ]
          ring1
        rw [normIdentity]
        exact inverseOrder }

def normalizedInverseLoopDomain
    (residual : Process) (base : residual.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (residual.ball base)) (count : Nat) (upper : Coordinate)
    (upperBound : ∀ {value : Gaussian}, residual.Possible base value →
      normSq value ≤ upper)
    (upperStrict : upper <
      CCL.ResidualDecision.paddingTarget count) :
    LoopDomain (normalizedInverseProcess residual base certificate count) :=
  let apart := normalizedInversePossibleApart residual base certificate count
    upper upperBound upperStrict
  LoopDomain.ofLower apart (by
    dsimp only [apart]
    let power : Coordinate := (2 : Coordinate) ^ (count + 1)
    rcases residual.witness base with ⟨displayed, displayedPossible⟩
    have displayedLower := certificate.lower
      (residual.possible_inside displayedPossible)
    have upperPositive : 0 < upper := certificate.positive.trans_le
      (displayedLower.trans (upperBound displayedPossible))
    have powerPositive : 0 < power :=
      RFAP.ConstructiveFraction.pow_pos_direct (by decide) (count + 1)
    have denominatorPositive : 0 < power * upper :=
      RFAP.ConstructiveFraction.mul_pos_direct powerPositive upperPositive
    have denominatorLtOne : power * upper < 1 := by
      have scaled := (RFAP.ConstructiveFraction.lt_div_iff_pos powerPositive).1
        upperStrict
      calc
        power * upper = upper * power :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ < 1 := scaled
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := power * upper) _ denominatorPositive
    calc
      1 * (power * upper) = power * upper := by ring1
      _ < 1 := denominatorLtOne
      _ = (power * upper)⁻¹ * (power * upper) :=
        (RFAP.ConstructiveFraction.inv_mul_cancel _
          denominatorPositive.ne').symm)

/-! ## Initial low-chart scaling -/

/-- Explicit finite exponent which scales any positive rational lower norm
strictly above one. -/
def upscaleExponent (lowerSq : Coordinate) : Nat :=
  RFAP.ConstructiveFraction.ceilNat (1 / lowerSq) + 1

theorem upscaleExponent_lower {lowerSq : Coordinate}
    (positive : 0 < lowerSq) :
    1 < (2 : Coordinate) ^ upscaleExponent lowerSq * lowerSq := by
  let inverse : Coordinate := 1 / lowerSq
  let ceiling := RFAP.ConstructiveFraction.ceilNat inverse
  have inverseNonnegative : 0 ≤ inverse :=
    (RFAP.ConstructiveFraction.div_pos_direct (by decide) positive).le
  have inverseLe : inverse ≤ (ceiling : Nat) := by
    exact RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg
      inverseNonnegative
  have oneLe : 1 ≤ (ceiling : Coordinate) * lowerSq := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        inverseLe positive.le
    calc
      1 = inverse * lowerSq := by
        dsimp only [inverse]
        exact (RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 lowerSq
          positive.ne').symm
      _ ≤ (ceiling : Coordinate) * lowerSq := scaled
  have ceilingStrict : (ceiling : Coordinate) * lowerSq <
      ((ceiling + 1 : Nat) : Coordinate) * lowerSq := by
    apply RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      _ positive
    exact RFAP.ConstructiveFraction.natCast_lt_direct (Nat.lt_succ_self _)
  have successorLower : 1 <
      ((ceiling + 1 : Nat) : Coordinate) * lowerSq :=
    oneLe.trans_lt ceilingStrict
  have powerBoundNat : ceiling + 1 ≤ 2 ^ (ceiling + 1) := by
    exact (CCL.Normalization.succ_le_two_pow (ceiling + 1)).trans'
      (Nat.le_succ (ceiling + 1))
  have powerBound : ((ceiling + 1 : Nat) : Coordinate) ≤
      (2 : Coordinate) ^ (ceiling + 1) := by
    have castBound := RFAP.ConstructiveFraction.natCast_le_direct powerBoundNat
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using castBound
  have scaledPower :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct powerBound
      positive.le
  dsimp only [upscaleExponent, ceiling]
  exact successorLower.trans_le scaledPower

/-- Scale a based process upward by an exact natural power of `gamma`. -/
def upscaledProcess (source : Process) (base : source.State)
    (exponent : Nat) : Process :=
  CCL.ProgressiveEnclosures.Process.mul
    (CCL.ProgressiveEnclosures.Process.exact
      (natPow gamma exponent))
    (based source base)

def upscaledInitial (source : Process) (base : source.State)
    (exponent : Nat) : (upscaledProcess source base exponent).State :=
  ((), BasedState.initial source base)

/-- Every later initial-low candidate is the exact upward rescaling of one
candidate admitted at the retained original state. -/
theorem upscaled_candidate_semantics
    (source : Process) (base : source.State) (exponent : Nat)
    {state : (upscaledProcess source base exponent).State} {value : Gaussian}
    (possible : (upscaledProcess source base exponent).Possible state value) :
    ∃ sourceValue : Gaussian,
      source.Possible base sourceValue ∧
      value = natPow gamma exponent * sourceValue := by
  rcases possible with
    ⟨factor, sourceValue, factorPossible, sourcePossible, valueEqual⟩
  exact ⟨sourceValue, state.2.persists sourcePossible,
    valueEqual.trans (congrArg (fun item => item * sourceValue)
      factorPossible)⟩

def upscaledPossibleApart
    (source : Process) (base : source.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (source.ball base)) (exponent : Nat) :
    PossibleApart (upscaledProcess source base exponent) := by
  exact
    { lowerSq := (2 : Coordinate) ^ exponent * certificate.lowerSq
      positive := RFAP.ConstructiveFraction.mul_pos_direct
        (RFAP.ConstructiveFraction.pow_pos_direct (by decide) exponent)
        certificate.positive
      lower := by
        intro state value possible
        rcases possible with
          ⟨factor, sourceValue, factorPossible, sourcePossible, valueEqual⟩
        have sourceAtBase : source.Possible base sourceValue :=
          state.2.persists sourcePossible
        have sourceLower := certificate.lower
          (source.possible_inside sourceAtBase)
        rw [valueEqual, factorPossible, normSq_mul, normSq_natPow, normSq_gamma]
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          sourceLower
          (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) exponent) }

def upscaledLoopDomain
    (source : Process) (base : source.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (source.ball base)) :
    LoopDomain
      (upscaledProcess source base (upscaleExponent certificate.lowerSq)) :=
  let apart := upscaledPossibleApart source base certificate
    (upscaleExponent certificate.lowerSq)
  LoopDomain.ofLower apart (upscaleExponent_lower certificate.positive)

theorem upscaledPrefix_lower
    (priorCount : Nat) {lowerSq : Coordinate} (positive : 0 < lowerSq) :
    1 < (2 : Coordinate) ^ (priorCount + upscaleExponent lowerSq) * lowerSq := by
  have baseLower := upscaleExponent_lower positive
  have powerOne : (1 : Coordinate) ≤ (2 : Coordinate) ^ priorCount := by
    have monotone := RFAP.ConstructiveFraction.pow_le_pow_direct
      (by decide : (0 : Coordinate) ≤ 1)
      (by decide : (1 : Coordinate) ≤ 2) priorCount
    simpa only [one_pow] using monotone
  calc
    1 < (2 : Coordinate) ^ upscaleExponent lowerSq * lowerSq := baseLower
    _ ≤ (2 : Coordinate) ^ priorCount *
        ((2 : Coordinate) ^ upscaleExponent lowerSq * lowerSq) := by
      calc
        (2 : Coordinate) ^ upscaleExponent lowerSq * lowerSq =
            1 * ((2 : Coordinate) ^ upscaleExponent lowerSq * lowerSq) :=
          (_root_.one_mul _).symm
        _ ≤ (2 : Coordinate) ^ priorCount *
            ((2 : Coordinate) ^ upscaleExponent lowerSq * lowerSq) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            powerOne
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
              positive.le)
    _ = (2 : Coordinate) ^ (priorCount + upscaleExponent lowerSq) * lowerSq := by
      rw [pow_add]
      ring1

def upscaledLoopDomainWithPrefix
    (source : Process) (base : source.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (source.ball base)) (priorCount : Nat) :
    LoopDomain (upscaledProcess source base
      (priorCount + upscaleExponent certificate.lowerSq)) :=
  let apart := upscaledPossibleApart source base certificate
    (priorCount + upscaleExponent certificate.lowerSq)
  LoopDomain.ofLower apart
    (upscaledPrefix_lower priorCount certificate.positive)

end CCL.ProgressiveCharts
