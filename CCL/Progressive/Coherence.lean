import mathlib.Tactic.QuotientFreeRing
import CCL.Arithmetic.OperationalEquivalence

/-!
# Finite coherence certificates for progressive CCL processes

`Process` deliberately permits branching refinement strategies: it promises
that every requested branch becomes accurate, but does not by itself say that
two independently refined branches describe one operational value.  This
module adds exactly that missing, finite certificate.

A coherent process assigns a nonnegative rational squared allowance to every
finite state.  The current enclosure radius is no larger than that allowance,
every pair of explicitly possible Gaussian-rational readings is close at the
sum of their allowances, and one ordinary refinement makes the allowance
smaller than any requested positive rational target.  There is no completed
value, infinite carrier, limit, or choice of a value common to all states.
-/

namespace CCL.ProgressiveCoherence

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev Ball := CCL.ArithmeticEnclosures.Ball
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev NamedEquivalent :=
  CCL.OperationalEquivalence.NamedEquivalent

open RFAP.ConstructiveGaussian.Gaussian

/-- A wholly finite certificate that all refinement branches of a process
describe one progressively sharpened operational value.  The factor four is
the squared two-leg triangle bound needed when two readings are compared
through one displayed finite centre. -/
structure Coherent (process : Process) where
  allowance : process.State → Coordinate
  allowance_nonneg : ∀ state, 0 ≤ allowance state
  ball_radius_le : ∀ state,
    (process.ball state).radiusSq ≤ allowance state
  possible_close : ∀ {leftState rightState : process.State}
      {leftValue rightValue : Gaussian},
    process.Possible leftState leftValue →
      process.Possible rightState rightValue →
        normSq (leftValue - rightValue) ≤
          4 * (allowance leftState + allowance rightState)
  accuracyRequest : Coordinate → Coordinate
  accuracyRequest_pos : ∀ {target : Coordinate}, 0 < target →
    0 < accuracyRequest target
  refine_accurate : ∀ (state : process.State) (target : Coordinate)
      (_positive : 0 < target) (request : Coordinate)
      (requestPositive : 0 < request),
    request < accuracyRequest target →
      allowance (process.refine state request requestPositive) < target

namespace Coherent

/-- The exact displayed-rational process is coherent with zero semantic
allowance. -/
def exact (value : Gaussian) :
    Coherent (CCL.ProgressiveEnclosures.Process.exact value) where
  allowance _ := 0
  allowance_nonneg _ := le_rfl
  ball_radius_le _ := le_rfl
  possible_close := by
    intro leftState rightState leftValue rightValue leftEqual rightEqual
    subst leftValue
    subst rightValue
    rw [sub_self, normSq_zero]
    change (0 : Coordinate) ≤ 0
    exact le_rfl
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    exact positive

private theorem center_sub_eq_neg_sub (center value : Gaussian) :
    center - value = -(value - center) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1

private theorem approximation_pair_close_from
    (approximation : Approximation) {base left right : Nat}
    (leftOrder : base ≤ left) (rightOrder : base ≤ right) :
    normSq (approximation.sample left - approximation.sample right) ≤
      4 * approximation.radiusSq base := by
  have leftClose := approximation.later_close leftOrder
  have rightCloseForward := approximation.later_close rightOrder
  have rightClose :
      normSq
          (approximation.sample base - approximation.sample right) ≤
        approximation.radiusSq base := by
    rw [center_sub_eq_neg_sub, normSq_neg]
    exact rightCloseForward
  calc
    normSq (approximation.sample left - approximation.sample right) ≤
        2 * (normSq
            (approximation.sample left - approximation.sample base) +
          normSq
            (approximation.sample base - approximation.sample right)) :=
      normSq_sub_le_via _ _ _
    _ ≤ 2 *
        (approximation.radiusSq base + approximation.radiusSq base) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftClose rightClose) (by decide)
    _ = 4 * approximation.radiusSq base := by ring1

/-- Every limit-free progressive approximation already carries enough finite
data to certify coherence of the process generated from it. -/
def ofApproximation (approximation : Approximation) :
    Coherent approximation.toProcess where
  allowance index := approximation.radiusSq index
  allowance_nonneg := approximation.radiusSq_nonneg
  ball_radius_le _ := le_rfl
  possible_close := by
    intro leftState rightState leftValue rightValue leftPossible rightPossible
    change approximation.Possible leftState leftValue at leftPossible
    change approximation.Possible rightState rightValue at rightPossible
    rcases leftPossible with ⟨leftLater, leftOrder, rfl⟩
    rcases rightPossible with ⟨rightLater, rightOrder, rfl⟩
    rcases Nat.le_total leftState rightState with stateOrder | stateOrder
    · calc
        normSq
            (approximation.sample leftLater -
              approximation.sample rightLater) ≤
            4 * approximation.radiusSq leftState :=
          approximation_pair_close_from approximation leftOrder
            (stateOrder.trans rightOrder)
        _ ≤ 4 *
            (approximation.radiusSq leftState +
              approximation.radiusSq rightState) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (le_add_of_nonneg_right
              (approximation.radiusSq_nonneg rightState)) (by decide)
    · calc
        normSq
            (approximation.sample leftLater -
              approximation.sample rightLater) ≤
            4 * approximation.radiusSq rightState :=
          approximation_pair_close_from approximation
            (stateOrder.trans leftOrder) rightOrder
        _ ≤ 4 *
            (approximation.radiusSq leftState +
              approximation.radiusSq rightState) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (le_add_of_nonneg_left
              (approximation.radiusSq_nonneg leftState)) (by decide)
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    exact (approximation.refineIndex_accurate state request
      requestPositive).trans requestSmall

/-! ## Arithmetic closure -/

/-- A positive rational request strictly below each of two positive requests.
This is finite arithmetic data, not an infimum operation. -/
def commonRequest (left right : Coordinate) : Coordinate :=
  (left * right) / (left + right)

theorem commonRequest_pos {left right : Coordinate}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    0 < commonRequest left right :=
  RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct leftPositive rightPositive)
    (add_pos leftPositive rightPositive)

theorem commonRequest_lt_left {left right : Coordinate}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    commonRequest left right < left := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (add_pos leftPositive rightPositive)).2
  have rightLt : right < left + right := by
    calc
      right = 0 + right := (zero_add right).symm
      _ < left + right :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct leftPositive right
  exact RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    leftPositive rightLt

theorem commonRequest_lt_right {left right : Coordinate}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    commonRequest left right < right := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (add_pos leftPositive rightPositive)).2
  have leftLt : left < left + right := by
    calc
      left = 0 + left := (zero_add left).symm
      _ < right + left :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct rightPositive left
      _ = left + right := add_comm _ _
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    rightPositive leftLt
  calc
    left * right = right * left := RFAP.ConstructiveFraction.mul_comm _ _
    _ < right * (left + right) := scaled

/-- Finite process coherence is preserved by addition. -/
def add {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right) : Coherent (left.add right) where
  allowance state :=
    2 * (leftCoherent.allowance state.1 + rightCoherent.allowance state.2)
  allowance_nonneg state :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg (leftCoherent.allowance_nonneg state.1)
        (rightCoherent.allowance_nonneg state.2))
  ball_radius_le state := by
    change 2 *
        ((left.ball state.1).radiusSq + (right.ball state.2).radiusSq) ≤
      2 *
        (leftCoherent.allowance state.1 +
          rightCoherent.allowance state.2)
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add (leftCoherent.ball_radius_le state.1)
        (rightCoherent.ball_radius_le state.2)) (by decide)
  possible_close := by
    rintro leftState rightState leftValue rightValue
      ⟨leftX, leftY, leftXPossible, leftYPossible, rfl⟩
      ⟨rightX, rightY, rightXPossible, rightYPossible, rfl⟩
    have leftClose := leftCoherent.possible_close
      leftXPossible rightXPossible
    have rightClose := rightCoherent.possible_close
      leftYPossible rightYPossible
    have difference :
        leftX + leftY - (rightX + rightY) =
          (leftX - rightX) + (leftY - rightY) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im] <;> ring1
    rw [difference]
    calc
      normSq ((leftX - rightX) + (leftY - rightY)) ≤
          2 * (normSq (leftX - rightX) + normSq (leftY - rightY)) :=
        normSq_add_le_two _ _
      _ ≤ 2 *
          (4 * (leftCoherent.allowance leftState.1 +
              leftCoherent.allowance rightState.1) +
            4 * (rightCoherent.allowance leftState.2 +
              rightCoherent.allowance rightState.2)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftClose rightClose) (by decide)
      _ = 4 *
          (2 * (leftCoherent.allowance leftState.1 +
              rightCoherent.allowance leftState.2) +
            2 * (leftCoherent.allowance rightState.1 +
              rightCoherent.allowance rightState.2)) := by ring1
  accuracyRequest target :=
    let semanticInputTarget :=
      CCL.ProgressiveEnclosures.Name.additiveInputTarget target
    4 * commonRequest
      (leftCoherent.accuracyRequest semanticInputTarget)
      (rightCoherent.accuracyRequest semanticInputTarget)
  accuracyRequest_pos := by
    intro target positive
    let semanticInputTarget :=
      CCL.ProgressiveEnclosures.Name.additiveInputTarget target
    have semanticPositive : 0 < semanticInputTarget :=
      CCL.ProgressiveEnclosures.Name.quarter_pos positive
    exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (commonRequest_pos
        (leftCoherent.accuracyRequest_pos semanticPositive)
        (rightCoherent.accuracyRequest_pos semanticPositive))
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    let semanticInputTarget :=
      CCL.ProgressiveEnclosures.Name.additiveInputTarget target
    have semanticPositive : 0 < semanticInputTarget :=
      CCL.ProgressiveEnclosures.Name.quarter_pos positive
    let leftRequest := leftCoherent.accuracyRequest semanticInputTarget
    let rightRequest := rightCoherent.accuracyRequest semanticInputTarget
    have leftRequestPositive : 0 < leftRequest :=
      leftCoherent.accuracyRequest_pos semanticPositive
    have rightRequestPositive : 0 < rightRequest :=
      rightCoherent.accuracyRequest_pos semanticPositive
    let sharedRequest := commonRequest leftRequest rightRequest
    have sharedPositive : 0 < sharedRequest :=
      commonRequest_pos leftRequestPositive rightRequestPositive
    let processInputTarget :=
      CCL.ProgressiveEnclosures.Name.additiveInputTarget request
    have processInputPositive : 0 < processInputTarget :=
      CCL.ProgressiveEnclosures.Name.quarter_pos requestPositive
    have processInputSmall : processInputTarget < sharedRequest := by
      apply (RFAP.ConstructiveFraction.div_lt_iff_pos
        (show (0 : Coordinate) < 4 by decide)).2
      calc
        request < 4 * sharedRequest := requestSmall
        _ = sharedRequest * 4 :=
          RFAP.ConstructiveFraction.mul_comm _ _
    have leftInputSmall : processInputTarget < leftRequest :=
      processInputSmall.trans
        (commonRequest_lt_left leftRequestPositive rightRequestPositive)
    have rightInputSmall : processInputTarget < rightRequest :=
      processInputSmall.trans
        (commonRequest_lt_right leftRequestPositive rightRequestPositive)
    let leftAllowance : Ball :=
      { center := 0
        radiusSq := leftCoherent.allowance
          (left.refine state.1
            processInputTarget processInputPositive)
        radiusSq_nonneg := leftCoherent.allowance_nonneg _ }
    let rightAllowance : Ball :=
      { center := 0
        radiusSq := rightCoherent.allowance
          (right.refine state.2
            processInputTarget processInputPositive)
        radiusSq_nonneg := rightCoherent.allowance_nonneg _ }
    change (leftAllowance.add rightAllowance).radiusSq < target
    apply CCL.ProgressiveEnclosures.Name.add_radius_lt
    · exact leftCoherent.refine_accurate state.1 semanticInputTarget
        semanticPositive processInputTarget processInputPositive leftInputSmall
    · exact rightCoherent.refine_accurate state.2 semanticInputTarget
        semanticPositive processInputTarget processInputPositive rightInputSmall

/-- Finite process coherence is preserved by negation. -/
def neg {process : Process} (coherent : Coherent process) :
    Coherent process.neg where
  allowance := coherent.allowance
  allowance_nonneg := coherent.allowance_nonneg
  ball_radius_le := coherent.ball_radius_le
  possible_close := by
    rintro leftState rightState leftValue rightValue
      ⟨leftSource, leftPossible, rfl⟩
      ⟨rightSource, rightPossible, rfl⟩
    have close := coherent.possible_close leftPossible rightPossible
    have difference :
        -leftSource - -rightSource = -(leftSource - rightSource) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
    rw [difference, normSq_neg]
    exact close
  accuracyRequest := coherent.accuracyRequest
  accuracyRequest_pos := coherent.accuracyRequest_pos
  refine_accurate := coherent.refine_accurate

/-- Finite process coherence is preserved by subtraction. -/
def sub {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right) : Coherent (left.sub right) :=
  add leftCoherent (neg rightCoherent)

/-- A possible finite reading is bounded by its semantic allowance and the
process's rational centre bound. -/
theorem possible_normSq_le {process : Process} (coherent : Coherent process)
    {state : process.State} {value : Gaussian}
    (possible : process.Possible state value) :
    normSq value ≤ 2 * (coherent.allowance state + process.centerBound) := by
  let center := (process.ball state).center
  have inside := process.possible_inside possible
  have deviationLe : normSq (value - center) ≤ coherent.allowance state :=
    inside.trans (coherent.ball_radius_le state)
  have identity : value = (value - center) + center := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  rw [identity]
  exact (normSq_add_le_two _ _).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add deviationLe (process.center_bounded state)) (by decide))

/-- The state-local polynomial used as a conservative product allowance. -/
def productBase (leftBound rightBound leftAllowance rightAllowance :
    Coordinate) : Coordinate :=
  leftAllowance * rightAllowance +
    leftAllowance * leftAllowance +
    rightAllowance * rightAllowance +
    leftAllowance * rightBound +
    leftBound * rightAllowance

def productAllowance (leftBound rightBound leftAllowance rightAllowance :
    Coordinate) : Coordinate :=
  4 * productBase leftBound rightBound leftAllowance rightAllowance

private theorem productBase_nonneg {leftBound rightBound leftAllowance
    rightAllowance : Coordinate}
    (leftBoundNonnegative : 0 ≤ leftBound)
    (rightBoundNonnegative : 0 ≤ rightBound)
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    0 ≤ productBase leftBound rightBound leftAllowance rightAllowance := by
  unfold productBase
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            leftNonnegative rightNonnegative)
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            leftNonnegative leftNonnegative))
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          rightNonnegative rightNonnegative))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        leftNonnegative rightBoundNonnegative))
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      leftBoundNonnegative rightNonnegative)

private theorem twice_mul_le_sq_add_sq (left right : Coordinate) :
    2 * left * right ≤ left * left + right * right := by
  apply sub_nonneg.mp
  have squareNonnegative :=
    RFAP.ConstructiveFraction.sq_nonneg_direct (left - right)
  convert squareNonnegative using 1
  ring1

private theorem product_cross_bound
    (leftBound rightBound leftOne leftTwo rightOne rightTwo : Coordinate)
    (leftOneNonnegative : 0 ≤ leftOne)
    (rightTwoNonnegative : 0 ≤ rightTwo) :
    (leftOne + leftTwo) * (rightOne + rightBound) +
        (leftTwo + leftBound) * (rightOne + rightTwo) ≤
      productBase leftBound rightBound leftOne rightOne +
        productBase leftBound rightBound leftTwo rightTwo := by
  let common :=
    leftOne * rightOne + leftTwo * rightTwo +
      rightBound * (leftOne + leftTwo) +
      leftBound * (rightOne + rightTwo)
  have cross := twice_mul_le_sq_add_sq leftTwo rightOne
  have extraNonnegative :
      0 ≤ leftOne * leftOne + rightTwo * rightTwo :=
    add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        leftOneNonnegative leftOneNonnegative)
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        rightTwoNonnegative rightTwoNonnegative)
  calc
    (leftOne + leftTwo) * (rightOne + rightBound) +
        (leftTwo + leftBound) * (rightOne + rightTwo) =
      common + 2 * leftTwo * rightOne := by
        dsimp only [common]
        ring1
    _ ≤ common + (leftTwo * leftTwo + rightOne * rightOne) :=
      add_le_add_right cross common
    _ ≤ common + (leftTwo * leftTwo + rightOne * rightOne) +
        (leftOne * leftOne + rightTwo * rightTwo) :=
      le_add_of_nonneg_right extraNonnegative
    _ = productBase leftBound rightBound leftOne rightOne +
        productBase leftBound rightBound leftTwo rightTwo := by
      dsimp only [common]
      unfold productBase
      ring1

private theorem product_ball_radius_le
    {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right) (state : left.State × right.State) :
    ((left.ball state.1).mul (right.ball state.2)).radiusSq ≤
      productAllowance left.centerBound right.centerBound
        (leftCoherent.allowance state.1)
        (rightCoherent.allowance state.2) := by
  let leftRadius := (left.ball state.1).radiusSq
  let rightRadius := (right.ball state.2).radiusSq
  let leftAllowance := leftCoherent.allowance state.1
  let rightAllowance := rightCoherent.allowance state.2
  have leftRadiusLe : leftRadius ≤ leftAllowance :=
    leftCoherent.ball_radius_le state.1
  have rightRadiusLe : rightRadius ≤ rightAllowance :=
    rightCoherent.ball_radius_le state.2
  have firstTerm :
      leftRadius * normSq (right.ball state.2).center ≤
        leftAllowance * right.centerBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct leftRadiusLe
      (right.center_bounded state.2) (normSq_nonneg _)
      (leftCoherent.allowance_nonneg state.1)
  have secondTerm :
      normSq (left.ball state.1).center * rightRadius ≤
        left.centerBound * rightAllowance :=
    RFAP.ConstructiveFraction.mul_le_mul_direct
      (left.center_bounded state.1) rightRadiusLe
      (right.ball state.2).radiusSq_nonneg left.centerBound_nonneg
  have productTerm : leftRadius * rightRadius ≤
      leftAllowance * rightAllowance :=
    RFAP.ConstructiveFraction.mul_le_mul_direct leftRadiusLe rightRadiusLe
      (right.ball state.2).radiusSq_nonneg
      (leftCoherent.allowance_nonneg state.1)
  have productNonnegative : 0 ≤ leftAllowance * rightAllowance :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (leftCoherent.allowance_nonneg state.1)
      (rightCoherent.allowance_nonneg state.2)
  have leftSquareNonnegative : 0 ≤ leftAllowance * leftAllowance :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (leftCoherent.allowance_nonneg state.1)
      (leftCoherent.allowance_nonneg state.1)
  have rightSquareNonnegative : 0 ≤ rightAllowance * rightAllowance :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (rightCoherent.allowance_nonneg state.2)
      (rightCoherent.allowance_nonneg state.2)
  change 4 *
      (leftRadius * normSq (right.ball state.2).center +
        normSq (left.ball state.1).center * rightRadius) +
      2 * (leftRadius * rightRadius) ≤
    productAllowance left.centerBound right.centerBound
      leftAllowance rightAllowance
  calc
    4 *
        (leftRadius * normSq (right.ball state.2).center +
          normSq (left.ball state.1).center * rightRadius) +
        2 * (leftRadius * rightRadius) ≤
      4 * (leftAllowance * right.centerBound +
          left.centerBound * rightAllowance) +
        2 * (leftAllowance * rightAllowance) :=
      add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide))
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          productTerm (by decide))
    _ ≤ 4 * (leftAllowance * right.centerBound +
          left.centerBound * rightAllowance) +
        2 * (leftAllowance * rightAllowance) +
        (2 * (leftAllowance * rightAllowance) +
          4 * (leftAllowance * leftAllowance) +
          4 * (rightAllowance * rightAllowance)) :=
      le_add_of_nonneg_right
        (add_nonneg
          (add_nonneg
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              productNonnegative)
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              leftSquareNonnegative))
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            rightSquareNonnegative))
    _ = productAllowance left.centerBound right.centerBound
        leftAllowance rightAllowance := by
      unfold productAllowance productBase
      ring1

private theorem product_possible_close
    {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right)
    {leftState rightState : left.State × right.State}
    {leftX leftY rightX rightY : Gaussian}
    (leftXPossible : left.Possible leftState.1 leftX)
    (leftYPossible : right.Possible leftState.2 leftY)
    (rightXPossible : left.Possible rightState.1 rightX)
    (rightYPossible : right.Possible rightState.2 rightY) :
    normSq (leftX * leftY - rightX * rightY) ≤
      4 *
        (productAllowance left.centerBound right.centerBound
            (leftCoherent.allowance leftState.1)
            (rightCoherent.allowance leftState.2) +
          productAllowance left.centerBound right.centerBound
            (leftCoherent.allowance rightState.1)
            (rightCoherent.allowance rightState.2)) := by
  let leftOne := leftCoherent.allowance leftState.1
  let leftTwo := leftCoherent.allowance rightState.1
  let rightOne := rightCoherent.allowance leftState.2
  let rightTwo := rightCoherent.allowance rightState.2
  have leftClose : normSq (leftX - rightX) ≤
      4 * (leftOne + leftTwo) :=
    leftCoherent.possible_close leftXPossible rightXPossible
  have rightClose : normSq (leftY - rightY) ≤
      4 * (rightOne + rightTwo) :=
    rightCoherent.possible_close leftYPossible rightYPossible
  have rightOneNorm : normSq leftY ≤
      2 * (rightOne + right.centerBound) :=
    possible_normSq_le rightCoherent leftYPossible
  have leftTwoNorm : normSq rightX ≤
      2 * (leftTwo + left.centerBound) :=
    possible_normSq_le leftCoherent rightXPossible
  have leftSumNonnegative : 0 ≤ 4 * (leftOne + leftTwo) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg (leftCoherent.allowance_nonneg leftState.1)
        (leftCoherent.allowance_nonneg rightState.1))
  have leftNormBoundNonnegative :
      0 ≤ 2 * (leftTwo + left.centerBound) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg (leftCoherent.allowance_nonneg rightState.1)
        left.centerBound_nonneg)
  have firstTerm :
      normSq ((leftX - rightX) * leftY) ≤
        (4 * (leftOne + leftTwo)) *
          (2 * (rightOne + right.centerBound)) := by
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      leftClose rightOneNorm (normSq_nonneg leftY) leftSumNonnegative
  have secondTerm :
      normSq (rightX * (leftY - rightY)) ≤
        (2 * (leftTwo + left.centerBound)) *
          (4 * (rightOne + rightTwo)) := by
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      leftTwoNorm rightClose (normSq_nonneg (leftY - rightY))
      leftNormBoundNonnegative
  have difference :
      leftX * leftY - rightX * rightY =
        (leftX - rightX) * leftY + rightX * (leftY - rightY) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
  have crossBound := product_cross_bound
    left.centerBound right.centerBound leftOne leftTwo rightOne rightTwo
    (leftCoherent.allowance_nonneg leftState.1)
    (rightCoherent.allowance_nonneg rightState.2)
  rw [difference]
  calc
    normSq
        ((leftX - rightX) * leftY + rightX * (leftY - rightY)) ≤
      2 * (normSq ((leftX - rightX) * leftY) +
        normSq (rightX * (leftY - rightY))) :=
      normSq_add_le_two _ _
    _ ≤ 2 *
        ((4 * (leftOne + leftTwo)) *
            (2 * (rightOne + right.centerBound)) +
          (2 * (leftTwo + left.centerBound)) *
            (4 * (rightOne + rightTwo))) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstTerm secondTerm) (by decide)
    _ = 16 *
        ((leftOne + leftTwo) * (rightOne + right.centerBound) +
          (leftTwo + left.centerBound) * (rightOne + rightTwo)) := by ring1
    _ ≤ 16 *
        (productBase left.centerBound right.centerBound leftOne rightOne +
          productBase left.centerBound right.centerBound leftTwo rightTwo) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        crossBound (by decide)
    _ = 4 *
        (productAllowance left.centerBound right.centerBound
            (leftCoherent.allowance leftState.1)
            (rightCoherent.allowance leftState.2) +
          productAllowance left.centerBound right.centerBound
            (leftCoherent.allowance rightState.1)
            (rightCoherent.allowance rightState.2)) := by
      dsimp only [leftOne, leftTwo, rightOne, rightTwo]
      unfold productAllowance
      ring1

/-- A strictly positive coefficient for the conservative semantic product
allowance. -/
def productCoefficient (left right : Process) : Coordinate :=
  4 * (3 + left.centerBound + right.centerBound)

theorem productCoefficient_pos (left right : Process) :
    0 < productCoefficient left right := by
  unfold productCoefficient
  exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (by decide) left.centerBound_nonneg)
      right.centerBound_nonneg)

/-- A finite operand-allowance target which is below one and whose product
with `productCoefficient` is below the requested result allowance. -/
def productInputTarget (left right : Process) (target : Coordinate) :
    Coordinate :=
  target / (target + productCoefficient left right)

theorem productInputTarget_pos (left right : Process) {target : Coordinate}
    (positive : 0 < target) : 0 < productInputTarget left right target :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    (add_pos positive (productCoefficient_pos left right))

theorem productInputTarget_lt_one (left right : Process)
    {target : Coordinate} (positive : 0 < target) :
    productInputTarget left right target < 1 := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (add_pos positive (productCoefficient_pos left right))).2
  calc
    target < target + productCoefficient left right :=
      lt_add_of_pos_right target (productCoefficient_pos left right)
    _ = 1 * (target + productCoefficient left right) := by ring1

private theorem quotient_mul_reorder
    (numerator denominator factor : Coordinate) :
    numerator / denominator * factor =
      (numerator * factor) / denominator := by
  change (numerator * denominator⁻¹) * factor =
    (numerator * factor) * denominator⁻¹
  calc
    (numerator * denominator⁻¹) * factor =
        numerator * (denominator⁻¹ * factor) :=
      _root_.mul_assoc _ _ _
    _ = numerator * (factor * denominator⁻¹) := by
      rw [RFAP.ConstructiveFraction.mul_comm denominator⁻¹ factor]
    _ = (numerator * factor) * denominator⁻¹ :=
      (_root_.mul_assoc _ _ _).symm

theorem productInputTarget_budget_lt (left right : Process)
    {target : Coordinate} (positive : 0 < target) :
    productInputTarget left right target * productCoefficient left right <
      target := by
  have denominatorPositive :
      0 < target + productCoefficient left right :=
    add_pos positive (productCoefficient_pos left right)
  change target / (target + productCoefficient left right) *
      productCoefficient left right < target
  calc
    target / (target + productCoefficient left right) *
        productCoefficient left right =
      (target * productCoefficient left right) /
        (target + productCoefficient left right) :=
      quotient_mul_reorder _ _ _
    _ < target := by
      apply (RFAP.ConstructiveFraction.div_lt_iff_pos
        denominatorPositive).2
      have coefficientLt : productCoefficient left right <
          target + productCoefficient left right := by
        calc
          productCoefficient left right =
              0 + productCoefficient left right :=
            (show (0 : Coordinate) + productCoefficient left right =
                productCoefficient left right from zero_add _).symm
          _ < target + productCoefficient left right :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct positive _
      exact RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive coefficientLt

private theorem mul_allowances_lt_target
    {left right : Process} {leftAllowance rightAllowance target : Coordinate}
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance)
    (targetPositive : 0 < target)
    (leftSmall : leftAllowance < productInputTarget left right target)
    (rightSmall : rightAllowance < productInputTarget left right target) :
    productAllowance left.centerBound right.centerBound
        leftAllowance rightAllowance < target := by
  generalize epsilonIdentity :
    productInputTarget left right target = epsilon at leftSmall rightSmall
  have epsilonPositive : 0 < epsilon :=
    epsilonIdentity ▸ productInputTarget_pos left right targetPositive
  have epsilonLtOne : epsilon < 1 :=
    epsilonIdentity ▸ productInputTarget_lt_one left right targetPositive
  have leftLtOne : leftAllowance < 1 := leftSmall.trans epsilonLtOne
  have rightLtOne : rightAllowance < 1 := rightSmall.trans epsilonLtOne
  have productSmall : leftAllowance * rightAllowance < epsilon := by
    calc
      leftAllowance * rightAllowance ≤ epsilon * rightAllowance :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          leftSmall.le rightNonnegative
      _ < epsilon * 1 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          epsilonPositive rightLtOne
      _ = epsilon := RFAP.ConstructiveFraction.mul_one_direct _
  have leftSquareSmall : leftAllowance * leftAllowance < epsilon := by
    calc
      leftAllowance * leftAllowance ≤ epsilon * leftAllowance :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          leftSmall.le leftNonnegative
      _ < epsilon * 1 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          epsilonPositive leftLtOne
      _ = epsilon := RFAP.ConstructiveFraction.mul_one_direct _
  have rightSquareSmall : rightAllowance * rightAllowance < epsilon := by
    calc
      rightAllowance * rightAllowance ≤ epsilon * rightAllowance :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          rightSmall.le rightNonnegative
      _ < epsilon * 1 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          epsilonPositive rightLtOne
      _ = epsilon := RFAP.ConstructiveFraction.mul_one_direct _
  have leftLinear : leftAllowance * right.centerBound ≤
      epsilon * right.centerBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      leftSmall.le right.centerBound_nonneg
  have rightLinear : left.centerBound * rightAllowance ≤
      left.centerBound * epsilon :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      rightSmall.le left.centerBound_nonneg
  have firstTwo := RFAP.ConstructiveFraction.add_lt_add_direct
    productSmall leftSquareSmall
  have firstThree := RFAP.ConstructiveFraction.add_lt_add_direct
    firstTwo rightSquareSmall
  have withLeftLinear :
      leftAllowance * rightAllowance +
          leftAllowance * leftAllowance +
          rightAllowance * rightAllowance +
          leftAllowance * right.centerBound <
        epsilon + epsilon + epsilon + epsilon * right.centerBound :=
    (RFAP.ConstructiveFraction.add_lt_add_right_direct firstThree
      (leftAllowance * right.centerBound)).trans_le
        (add_le_add_right leftLinear (epsilon + epsilon + epsilon))
  have baseSmall :
      leftAllowance * rightAllowance +
          leftAllowance * leftAllowance +
          rightAllowance * rightAllowance +
          leftAllowance * right.centerBound +
          left.centerBound * rightAllowance <
        epsilon + epsilon + epsilon + epsilon * right.centerBound +
          left.centerBound * epsilon :=
    (RFAP.ConstructiveFraction.add_lt_add_right_direct withLeftLinear
      (left.centerBound * rightAllowance)).trans_le
        (add_le_add_right rightLinear
          (epsilon + epsilon + epsilon + epsilon * right.centerBound))
  have scaledBaseSmall :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (by decide : (0 : Coordinate) < 4) baseSmall
  calc
    productAllowance left.centerBound right.centerBound
        leftAllowance rightAllowance <
      4 *
        ((epsilon + epsilon + epsilon) +
          epsilon * right.centerBound + left.centerBound * epsilon) := by
      exact scaledBaseSmall
    _ = epsilon * productCoefficient left right := by
      unfold productCoefficient
      ring1
    _ < target := by
      rw [← epsilonIdentity]
      exact productInputTarget_budget_lt left right targetPositive

/-- The process multiplication request is strictly smaller than its positive
outer request. -/
theorem processMultiplicativeInputTarget_lt_target
    (leftName rightName : CCL.ProgressiveEnclosures.Name)
    {target : Coordinate} (positive : 0 < target) :
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget
        leftName rightName target < target := by
  let epsilon :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget
      leftName rightName target
  have epsilonPositive : 0 < epsilon :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget_pos
      leftName rightName positive
  have boundPartNonnegative :
      0 ≤ 4 * (leftName.centerBound + rightName.centerBound) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg leftName.centerBound_nonneg rightName.centerBound_nonneg)
  have coefficientOne :
      1 ≤ CCL.ProgressiveEnclosures.Name.multiplicativeCoefficient
        leftName rightName := by
    unfold CCL.ProgressiveEnclosures.Name.multiplicativeCoefficient
    exact (show (1 : Coordinate) ≤ 2 by decide).trans
      (le_add_of_nonneg_left boundPartNonnegative)
  calc
    epsilon = epsilon * 1 :=
      (RFAP.ConstructiveFraction.mul_one_direct _).symm
    _ ≤ epsilon *
        CCL.ProgressiveEnclosures.Name.multiplicativeCoefficient
          leftName rightName :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        coefficientOne epsilonPositive.le
    _ < target :=
      CCL.ProgressiveEnclosures.Name.multiplicative_budget_lt
        leftName rightName positive

/-- Finite process coherence is preserved by multiplication.  The semantic
allowance includes the two squared operand allowances needed to absorb
cross-state uncertainty; the computed process request is correspondingly
smaller than the final requested product allowance. -/
def mul {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right) : Coherent (left.mul right) where
  allowance state :=
    productAllowance left.centerBound right.centerBound
      (leftCoherent.allowance state.1) (rightCoherent.allowance state.2)
  allowance_nonneg state :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (productBase_nonneg left.centerBound_nonneg right.centerBound_nonneg
        (leftCoherent.allowance_nonneg state.1)
        (rightCoherent.allowance_nonneg state.2))
  ball_radius_le := product_ball_radius_le leftCoherent rightCoherent
  possible_close := by
    rintro leftState rightState leftValue rightValue
      ⟨leftX, leftY, leftXPossible, leftYPossible, rfl⟩
      ⟨rightX, rightY, rightXPossible, rightYPossible, rfl⟩
    exact product_possible_close leftCoherent rightCoherent
      leftXPossible leftYPossible rightXPossible rightYPossible
  accuracyRequest target :=
    let semanticInputTarget := productInputTarget left right target
    commonRequest
      (leftCoherent.accuracyRequest semanticInputTarget)
      (rightCoherent.accuracyRequest semanticInputTarget)
  accuracyRequest_pos := by
    intro target positive
    let semanticInputTarget := productInputTarget left right target
    have semanticPositive : 0 < semanticInputTarget :=
      productInputTarget_pos left right positive
    exact commonRequest_pos
      (leftCoherent.accuracyRequest_pos semanticPositive)
      (rightCoherent.accuracyRequest_pos semanticPositive)
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    let semanticInputTarget := productInputTarget left right target
    have semanticPositive : 0 < semanticInputTarget :=
      productInputTarget_pos left right positive
    let leftRequest := leftCoherent.accuracyRequest semanticInputTarget
    let rightRequest := rightCoherent.accuracyRequest semanticInputTarget
    have leftRequestPositive : 0 < leftRequest :=
      leftCoherent.accuracyRequest_pos semanticPositive
    have rightRequestPositive : 0 < rightRequest :=
      rightCoherent.accuracyRequest_pos semanticPositive
    let sharedRequest := commonRequest leftRequest rightRequest
    have sharedPositive : 0 < sharedRequest :=
      commonRequest_pos leftRequestPositive rightRequestPositive
    change request < sharedRequest at requestSmall
    let leftName :=
      CCL.ProgressiveEnclosures.Name.centerOnly
        (left.ball state.1).center left.centerBound left.centerBound_nonneg
        (left.center_bounded state.1)
    let rightName :=
      CCL.ProgressiveEnclosures.Name.centerOnly
        (right.ball state.2).center right.centerBound right.centerBound_nonneg
        (right.center_bounded state.2)
    let processInputTarget :=
      CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget
        leftName rightName request
    have processInputPositive : 0 < processInputTarget :=
      CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget_pos
        leftName rightName requestPositive
    have processInputLtRequest : processInputTarget < request :=
      processMultiplicativeInputTarget_lt_target
        leftName rightName requestPositive
    have processInputLtShared : processInputTarget < sharedRequest :=
      processInputLtRequest.trans requestSmall
    have processInputLtLeft : processInputTarget < leftRequest :=
      processInputLtShared.trans
        (commonRequest_lt_left leftRequestPositive rightRequestPositive)
    have processInputLtRight : processInputTarget < rightRequest :=
      processInputLtShared.trans
        (commonRequest_lt_right leftRequestPositive rightRequestPositive)
    have leftSmall :
        leftCoherent.allowance
            (left.refine state.1 processInputTarget processInputPositive) <
          semanticInputTarget :=
      leftCoherent.refine_accurate state.1 semanticInputTarget semanticPositive
        processInputTarget processInputPositive processInputLtLeft
    have rightSmall :
        rightCoherent.allowance
            (right.refine state.2 processInputTarget processInputPositive) <
          semanticInputTarget :=
      rightCoherent.refine_accurate state.2 semanticInputTarget semanticPositive
        processInputTarget processInputPositive processInputLtRight
    change productAllowance left.centerBound right.centerBound
        (leftCoherent.allowance
          (left.refine state.1 processInputTarget processInputPositive))
        (rightCoherent.allowance
          (right.refine state.2 processInputTarget processInputPositive)) <
      target
    exact mul_allowances_lt_target
      (leftCoherent.allowance_nonneg _)
      (rightCoherent.allowance_nonneg _) positive leftSmall rightSmall

/-! ## Apartness-certified division coherence -/

/-- A separable state-local numerator allowance for comparing two quotients.
It includes enough squares to absorb the cross-state products without ever
selecting a completed value. -/
def divisionMarginal (leftBound rightBound leftAllowance rightAllowance :
    Coordinate) : Coordinate :=
  8 * leftAllowance * leftAllowance +
    4 * rightBound * leftAllowance +
    8 * rightAllowance * rightAllowance +
    4 * leftBound * rightAllowance

private theorem divisionMarginal_nonneg
    {leftBound rightBound leftAllowance rightAllowance : Coordinate}
    (leftBoundNonnegative : 0 ≤ leftBound)
    (rightBoundNonnegative : 0 ≤ rightBound)
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    0 ≤ divisionMarginal leftBound rightBound
      leftAllowance rightAllowance := by
  unfold divisionMarginal
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            leftNonnegative) leftNonnegative)
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            rightBoundNonnegative) leftNonnegative))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          rightNonnegative) rightNonnegative))
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        leftBoundNonnegative) rightNonnegative)

private theorem productAllowance_le_divisionMarginal
    {leftBound rightBound leftAllowance rightAllowance : Coordinate}
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    productAllowance leftBound rightBound leftAllowance rightAllowance ≤
      divisionMarginal leftBound rightBound leftAllowance rightAllowance := by
  have squarePlusProduct :
      0 ≤ (leftAllowance - rightAllowance) *
          (leftAllowance - rightAllowance) +
        leftAllowance * rightAllowance :=
    add_nonneg (by
      simpa only [pow_two] using
        RFAP.ConstructiveFraction.sq_nonneg_direct
          (leftAllowance - rightAllowance))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        leftNonnegative rightNonnegative)
  apply sub_nonneg.mp
  have scaled := RFAP.ConstructiveFraction.mul_nonneg_direct
    (by decide : (0 : Coordinate) ≤ 4) squarePlusProduct
  have identity :
      divisionMarginal leftBound rightBound leftAllowance rightAllowance -
          productAllowance leftBound rightBound leftAllowance rightAllowance =
        4 * ((leftAllowance - rightAllowance) *
          (leftAllowance - rightAllowance) +
            leftAllowance * rightAllowance) := by
    unfold divisionMarginal productAllowance productBase
    ring1
  rw [identity]
  exact scaled

private theorem divisionMarginal_le_two_productAllowance
    {leftBound rightBound leftAllowance rightAllowance : Coordinate}
    (leftBoundNonnegative : 0 ≤ leftBound)
    (rightBoundNonnegative : 0 ≤ rightBound)
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    divisionMarginal leftBound rightBound leftAllowance rightAllowance ≤
      2 * productAllowance leftBound rightBound
        leftAllowance rightAllowance := by
  apply sub_nonneg.mp
  have crossNonnegative : 0 ≤ 8 * leftAllowance * rightAllowance :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        leftNonnegative) rightNonnegative
  have leftLinearNonnegative :
      0 ≤ 4 * rightBound * leftAllowance :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        rightBoundNonnegative) leftNonnegative
  have rightLinearNonnegative :
      0 ≤ 4 * leftBound * rightAllowance :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        leftBoundNonnegative) rightNonnegative
  have total := add_nonneg
    (add_nonneg crossNonnegative leftLinearNonnegative)
    rightLinearNonnegative
  have identity :
      2 * productAllowance leftBound rightBound
            leftAllowance rightAllowance -
          divisionMarginal leftBound rightBound
            leftAllowance rightAllowance =
        8 * leftAllowance * rightAllowance +
          4 * rightBound * leftAllowance +
          4 * leftBound * rightAllowance := by
    unfold divisionMarginal productAllowance productBase
    ring1
  rw [identity]
  exact total

def divisionSemanticAllowance (leftBound rightBound lowerSq leftAllowance
    rightAllowance : Coordinate) : Coordinate :=
  (4 * divisionMarginal leftBound rightBound
      leftAllowance rightAllowance) / (lowerSq * lowerSq)

theorem divisionSemanticAllowance_nonneg
    {leftBound rightBound lowerSq leftAllowance rightAllowance : Coordinate}
    (leftBoundNonnegative : 0 ≤ leftBound)
    (rightBoundNonnegative : 0 ≤ rightBound)
    (lowerNonnegative : 0 ≤ lowerSq)
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    0 ≤ divisionSemanticAllowance leftBound rightBound lowerSq
      leftAllowance rightAllowance := by
  apply RFAP.ConstructiveFraction.div_nonneg_direct
  · exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (divisionMarginal_nonneg leftBoundNonnegative rightBoundNonnegative
        leftNonnegative rightNonnegative)
  · exact RFAP.ConstructiveFraction.mul_nonneg_direct
      lowerNonnegative lowerNonnegative

def divisionAllowance {left right : Process}
    (leftCoherent : Coherent left) (rightCoherent : Coherent right)
    (apart : CCL.ProgressiveEnclosures.Process.Apart right)
    (state : (left.div right apart).State) : Coordinate :=
  ((left.div right apart).ball state).radiusSq +
    divisionSemanticAllowance left.centerBound right.centerBound apart.lowerSq
      (leftCoherent.allowance state.1) (rightCoherent.allowance state.2)

private theorem gaussian_div_mul_cancel (numerator denominator : Gaussian)
    (denominatorNonzero : denominator ≠ 0) :
    numerator / denominator * denominator = numerator := by
  rw [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    numerator * denominator⁻¹ * denominator =
        numerator * (denominator⁻¹ * denominator) :=
      RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
    _ = numerator * 1 := by
      rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul
          denominator denominatorNonzero]
    _ = numerator := RFAP.ConstructiveGaussian.Gaussian.mul_one numerator

private theorem gaussian_div_sub_div_direct
    (a b c d : Gaussian) (cNonzero : c ≠ 0) (dNonzero : d ≠ 0) :
    a / c - b / d = (a * d - b * c) / (c * d) := by
  have productNonzero :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct cNonzero dNonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    productNonzero
  calc
    (a / c - b / d) * (c * d) =
        (a / c * c) * d - (b / d * d) * c := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    _ = a * d - b * c := by
      rw [gaussian_div_mul_cancel _ _ cNonzero,
        gaussian_div_mul_cancel _ _ dNonzero]
    _ = ((a * d - b * c) / (c * d)) * (c * d) :=
      (gaussian_div_mul_cancel _ _ productNonzero).symm

private theorem division_possible_close
    {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right)
    (apart : CCL.ProgressiveEnclosures.Process.Apart right)
    {leftState rightState : (left.div right apart).State}
    {leftX leftY rightX rightY : Gaussian}
    (leftXPossible : left.Possible leftState.1 leftX)
    (leftYPossible : right.Possible leftState.2 leftY)
    (rightXPossible : left.Possible rightState.1 rightX)
    (rightYPossible : right.Possible rightState.2 rightY) :
    normSq (leftX / leftY - rightX / rightY) ≤
      4 *
        (divisionAllowance leftCoherent rightCoherent apart leftState +
          divisionAllowance leftCoherent rightCoherent apart rightState) := by
  let leftOne := leftCoherent.allowance leftState.1
  let leftTwo := leftCoherent.allowance rightState.1
  let rightOne := rightCoherent.allowance leftState.2
  let rightTwo := rightCoherent.allowance rightState.2
  let marginalOne := divisionMarginal left.centerBound right.centerBound
    leftOne rightOne
  let marginalTwo := divisionMarginal left.centerBound right.centerBound
    leftTwo rightTwo
  have leftDenominatorLower : apart.lowerSq ≤ normSq leftY :=
    apart.lower leftState.2 (right.possible_inside leftYPossible)
  have rightDenominatorLower : apart.lowerSq ≤ normSq rightY :=
    apart.lower rightState.2 (right.possible_inside rightYPossible)
  have leftDenominatorPositive : 0 < normSq leftY :=
    apart.positive.trans_le leftDenominatorLower
  have rightDenominatorPositive : 0 < normSq rightY :=
    apart.positive.trans_le rightDenominatorLower
  have leftDenominatorNonzero : leftY ≠ 0 := by
    intro equal
    rw [equal, normSq_zero] at leftDenominatorPositive
    exact (lt_irrefl _ leftDenominatorPositive).elim
  have rightDenominatorNonzero : rightY ≠ 0 := by
    intro equal
    rw [equal, normSq_zero] at rightDenominatorPositive
    exact (lt_irrefl _ rightDenominatorPositive).elim
  have leftClose : normSq (leftX - rightX) ≤
      4 * (leftOne + leftTwo) :=
    leftCoherent.possible_close leftXPossible rightXPossible
  have rightClose : normSq (rightY - leftY) ≤
      4 * (rightTwo + rightOne) :=
    rightCoherent.possible_close rightYPossible leftYPossible
  have rightTwoNorm : normSq rightY ≤
      2 * (rightTwo + right.centerBound) :=
    possible_normSq_le rightCoherent rightYPossible
  have leftTwoNorm : normSq rightX ≤
      2 * (leftTwo + left.centerBound) :=
    possible_normSq_le leftCoherent rightXPossible
  have firstTerm :
      normSq ((leftX - rightX) * rightY) ≤
        (4 * (leftOne + leftTwo)) *
          (2 * (rightTwo + right.centerBound)) := by
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      leftClose rightTwoNorm (normSq_nonneg rightY)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg (leftCoherent.allowance_nonneg leftState.1)
          (leftCoherent.allowance_nonneg rightState.1)))
  have secondTerm :
      normSq (rightX * (rightY - leftY)) ≤
        (2 * (leftTwo + left.centerBound)) *
          (4 * (rightTwo + rightOne)) := by
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      leftTwoNorm rightClose (normSq_nonneg (rightY - leftY))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg (leftCoherent.allowance_nonneg rightState.1)
          left.centerBound_nonneg))
  have numeratorIdentity :
      leftX * rightY - rightX * leftY =
        (leftX - rightX) * rightY + rightX * (rightY - leftY) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
  have crossBound := product_cross_bound
    left.centerBound right.centerBound leftOne leftTwo rightTwo rightOne
    (leftCoherent.allowance_nonneg leftState.1)
    (rightCoherent.allowance_nonneg leftState.2)
  have crossProductBound :
      normSq (leftX * rightY - rightX * leftY) ≤
        4 *
          (productAllowance left.centerBound right.centerBound
              leftOne rightTwo +
            productAllowance left.centerBound right.centerBound
              leftTwo rightOne) := by
    rw [numeratorIdentity]
    calc
      normSq
          ((leftX - rightX) * rightY + rightX * (rightY - leftY)) ≤
        2 * (normSq ((leftX - rightX) * rightY) +
          normSq (rightX * (rightY - leftY))) :=
        normSq_add_le_two _ _
      _ ≤ 2 *
          ((4 * (leftOne + leftTwo)) *
              (2 * (rightTwo + right.centerBound)) +
            (2 * (leftTwo + left.centerBound)) *
              (4 * (rightTwo + rightOne))) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = 16 *
          ((leftOne + leftTwo) * (rightTwo + right.centerBound) +
            (leftTwo + left.centerBound) * (rightTwo + rightOne)) := by
        ring1
      _ ≤ 16 *
          (productBase left.centerBound right.centerBound leftOne rightTwo +
            productBase left.centerBound right.centerBound leftTwo rightOne) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          crossBound (by decide)
      _ = 4 *
          (productAllowance left.centerBound right.centerBound leftOne rightTwo +
            productAllowance left.centerBound right.centerBound leftTwo rightOne) := by
        unfold productAllowance
        ring1
  have crossMarginalBound :
      productAllowance left.centerBound right.centerBound leftOne rightTwo +
          productAllowance left.centerBound right.centerBound leftTwo rightOne ≤
        marginalOne + marginalTwo := by
    calc
      productAllowance left.centerBound right.centerBound leftOne rightTwo +
          productAllowance left.centerBound right.centerBound leftTwo rightOne ≤
        divisionMarginal left.centerBound right.centerBound leftOne rightTwo +
          divisionMarginal left.centerBound right.centerBound leftTwo rightOne :=
        add_le_add
          (productAllowance_le_divisionMarginal
            (leftCoherent.allowance_nonneg leftState.1)
            (rightCoherent.allowance_nonneg rightState.2))
          (productAllowance_le_divisionMarginal
            (leftCoherent.allowance_nonneg rightState.1)
            (rightCoherent.allowance_nonneg leftState.2))
      _ = marginalOne + marginalTwo := by
        dsimp only [marginalOne, marginalTwo, leftOne, leftTwo,
          rightOne, rightTwo]
        unfold divisionMarginal
        ring1
  have numeratorBound :
      normSq (leftX * rightY - rightX * leftY) ≤
        4 * (marginalOne + marginalTwo) :=
    crossProductBound.trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        crossMarginalBound (by decide))
  have denominatorLower : apart.lowerSq * apart.lowerSq ≤
      normSq leftY * normSq rightY :=
    RFAP.ConstructiveFraction.mul_le_mul_direct
      leftDenominatorLower rightDenominatorLower apart.positive.le
      (normSq_nonneg leftY)
  have lowerProductPositive : 0 < apart.lowerSq * apart.lowerSq :=
    RFAP.ConstructiveFraction.mul_pos_direct apart.positive apart.positive
  have numeratorNonnegative :
      0 ≤ normSq (leftX * rightY - rightX * leftY) :=
    normSq_nonneg _
  have marginalOneNonnegative : 0 ≤ marginalOne :=
    divisionMarginal_nonneg left.centerBound_nonneg right.centerBound_nonneg
      (leftCoherent.allowance_nonneg leftState.1)
      (rightCoherent.allowance_nonneg leftState.2)
  have marginalTwoNonnegative : 0 ≤ marginalTwo :=
    divisionMarginal_nonneg left.centerBound_nonneg right.centerBound_nonneg
      (leftCoherent.allowance_nonneg rightState.1)
      (rightCoherent.allowance_nonneg rightState.2)
  rw [gaussian_div_sub_div_direct _ _ _ _
      leftDenominatorNonzero rightDenominatorNonzero,
    RFAP.ConstructiveGaussian.Gaussian.normSq_div _ _
      (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        leftDenominatorNonzero rightDenominatorNonzero), normSq_mul]
  calc
    normSq (leftX * rightY - rightX * leftY) /
          (normSq leftY * normSq rightY) ≤
        normSq (leftX * rightY - rightX * leftY) /
          (apart.lowerSq * apart.lowerSq) :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        numeratorNonnegative lowerProductPositive denominatorLower
    _ ≤ (4 * (marginalOne + marginalTwo)) /
          (apart.lowerSq * apart.lowerSq) := by
      change normSq (leftX * rightY - rightX * leftY) *
          (apart.lowerSq * apart.lowerSq)⁻¹ ≤
        (4 * (marginalOne + marginalTwo)) *
          (apart.lowerSq * apart.lowerSq)⁻¹
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        numeratorBound
        (RFAP.ConstructiveFraction.inv_pos_direct lowerProductPositive).le
    _ = divisionSemanticAllowance left.centerBound right.centerBound
          apart.lowerSq leftOne rightOne +
        divisionSemanticAllowance left.centerBound right.centerBound
          apart.lowerSq leftTwo rightTwo := by
      unfold divisionSemanticAllowance
      change (4 * (marginalOne + marginalTwo)) *
          (apart.lowerSq * apart.lowerSq)⁻¹ =
        (4 * marginalOne) * (apart.lowerSq * apart.lowerSq)⁻¹ +
          (4 * marginalTwo) * (apart.lowerSq * apart.lowerSq)⁻¹
      rw [mul_add, add_mul]
    _ ≤ divisionAllowance leftCoherent rightCoherent apart leftState +
          divisionAllowance leftCoherent rightCoherent apart rightState := by
      unfold divisionAllowance
      exact add_le_add
        (le_add_of_nonneg_left
          ((left.div right apart).ball leftState).radiusSq_nonneg)
        (le_add_of_nonneg_left
          ((left.div right apart).ball rightState).radiusSq_nonneg)
    _ ≤ 4 *
        (divisionAllowance leftCoherent rightCoherent apart leftState +
          divisionAllowance leftCoherent rightCoherent apart rightState) := by
      let total := divisionAllowance leftCoherent rightCoherent apart leftState +
        divisionAllowance leftCoherent rightCoherent apart rightState
      have totalNonnegative : 0 ≤ total := by
        unfold total divisionAllowance
        exact add_nonneg
          (add_nonneg
            ((left.div right apart).ball leftState).radiusSq_nonneg
            (divisionSemanticAllowance_nonneg left.centerBound_nonneg
              right.centerBound_nonneg apart.positive.le
              (leftCoherent.allowance_nonneg leftState.1)
              (rightCoherent.allowance_nonneg leftState.2)))
          (add_nonneg
            ((left.div right apart).ball rightState).radiusSq_nonneg
            (divisionSemanticAllowance_nonneg left.centerBound_nonneg
              right.centerBound_nonneg apart.positive.le
              (leftCoherent.allowance_nonneg rightState.1)
              (rightCoherent.allowance_nonneg rightState.2)))
      change total ≤ 4 * total
      calc
        total = 1 * total := (one_mul total).symm
        _ ≤ 4 * total :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (by decide) totalNonnegative

def divisionSemanticTarget (lowerSq target : Coordinate) : Coordinate :=
  (target / 32) * (lowerSq * lowerSq)

theorem divisionSemanticTarget_pos {lowerSq target : Coordinate}
    (lowerPositive : 0 < lowerSq) (targetPositive : 0 < target) :
    0 < divisionSemanticTarget lowerSq target :=
  RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.div_pos_direct targetPositive
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 32) (by decide)))
    (RFAP.ConstructiveFraction.mul_pos_direct lowerPositive lowerPositive)

private theorem eight_div_thirtyTwo (target : Coordinate) :
    8 * (target / 32) = target / 4 := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 32) (by decide)).ne'
  calc
    (8 * (target / 32)) * 32 = 8 * ((target / 32) * 32) :=
      RFAP.ConstructiveFraction.mul_assoc 8 (target / 32) 32
    _ = 8 * target := by
      rw [show (target / 32) * 32 = target from
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 32
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 32) (by decide)).ne']
    _ = target * 8 := RFAP.ConstructiveFraction.mul_comm 8 target
    _ = ((target / 4) * 4) * 8 := by
      rw [show (target / 4) * 4 = target from
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 4
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 4) (by decide)).ne']
    _ = (target / 4) * (4 * 8) :=
      RFAP.ConstructiveFraction.mul_assoc (target / 4) 4 8
    _ = (target / 4) * 32 := by
      rw [show (4 : Coordinate) * 8 = 32 by ring1]

private theorem divisionSemanticAllowance_lt_quarter
    {left right : Process}
    (apart : CCL.ProgressiveEnclosures.Process.Apart right)
    {leftAllowance rightAllowance target : Coordinate}
    (targetPositive : 0 < target)
    (leftSmall : leftAllowance <
      productInputTarget left right
        (divisionSemanticTarget apart.lowerSq target))
    (rightSmall : rightAllowance <
      productInputTarget left right
        (divisionSemanticTarget apart.lowerSq target))
    (leftNonnegative : 0 ≤ leftAllowance)
    (rightNonnegative : 0 ≤ rightAllowance) :
    divisionSemanticAllowance left.centerBound right.centerBound
        apart.lowerSq leftAllowance rightAllowance < target / 4 := by
  have semanticTargetPositive :
      0 < divisionSemanticTarget apart.lowerSq target :=
    divisionSemanticTarget_pos apart.positive targetPositive
  have productSmall := mul_allowances_lt_target
    leftNonnegative rightNonnegative semanticTargetPositive leftSmall rightSmall
  have marginalLe := divisionMarginal_le_two_productAllowance
    left.centerBound_nonneg right.centerBound_nonneg
    leftNonnegative rightNonnegative
  have fourMarginalLe :
      4 * divisionMarginal left.centerBound right.centerBound
          leftAllowance rightAllowance ≤
        8 * productAllowance left.centerBound right.centerBound
          leftAllowance rightAllowance := by
    calc
      4 * divisionMarginal left.centerBound right.centerBound
          leftAllowance rightAllowance ≤
        4 * (2 * productAllowance left.centerBound right.centerBound
          leftAllowance rightAllowance) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          marginalLe (by decide)
      _ = 8 * productAllowance left.centerBound right.centerBound
          leftAllowance rightAllowance := by ring1
  have numeratorSmall :
      4 * divisionMarginal left.centerBound right.centerBound
          leftAllowance rightAllowance <
        8 * divisionSemanticTarget apart.lowerSq target :=
    fourMarginalLe.trans_lt
      (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide) productSmall)
  unfold divisionSemanticAllowance
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (RFAP.ConstructiveFraction.mul_pos_direct
      apart.positive apart.positive)).2
  calc
    4 * divisionMarginal left.centerBound right.centerBound
        leftAllowance rightAllowance <
      8 * divisionSemanticTarget apart.lowerSq target := numeratorSmall
    _ = (target / 4) * (apart.lowerSq * apart.lowerSq) := by
      unfold divisionSemanticTarget
      rw [← RFAP.ConstructiveFraction.mul_assoc,
        eight_div_thirtyTwo]

def divisionOuterTarget (left right : Process) (lowerSq operandRequest :
    Coordinate) : Coordinate :=
  (operandRequest *
      (4 * (left.centerBound + right.centerBound + 1))) /
    (lowerSq * lowerSq)

theorem divisionOuterTarget_pos (left right : Process)
    {lowerSq operandRequest : Coordinate}
    (lowerPositive : 0 < lowerSq) (requestPositive : 0 < operandRequest) :
    0 < divisionOuterTarget left right lowerSq operandRequest := by
  apply RFAP.ConstructiveFraction.div_pos_direct
  · exact RFAP.ConstructiveFraction.mul_pos_direct requestPositive
      (CCL.ProgressiveEnclosures.Name.divisionDenominator_pos
        (CCL.ProgressiveEnclosures.Name.centerOnly 0
          left.centerBound left.centerBound_nonneg (by
            rw [normSq_zero]
            exact left.centerBound_nonneg))
        (CCL.ProgressiveEnclosures.Name.centerOnly 0
          right.centerBound right.centerBound_nonneg (by
            rw [normSq_zero]
            exact right.centerBound_nonneg)))
  · exact RFAP.ConstructiveFraction.mul_pos_direct
      lowerPositive lowerPositive

theorem processDivisionInputTarget_lt
    {left right : Process}
    (leftName rightName : CCL.ProgressiveEnclosures.Name)
    (leftBound : leftName.centerBound = left.centerBound)
    (rightBound : rightName.centerBound = right.centerBound)
    {lowerSq operandRequest request : Coordinate}
    (lowerPositive : 0 < lowerSq)
    (requestSmall :
      request < divisionOuterTarget left right lowerSq operandRequest) :
    CCL.ProgressiveEnclosures.Name.divisionInputTarget
        leftName rightName lowerSq request < operandRequest := by
  let denominator := 4 * (left.centerBound + right.centerBound + 1)
  have denominatorPositive : 0 < denominator := by
    dsimp only [denominator]
    rw [← leftBound, ← rightBound]
    exact CCL.ProgressiveEnclosures.Name.divisionDenominator_pos
      leftName rightName
  have lowerProductPositive : 0 < lowerSq * lowerSq :=
    RFAP.ConstructiveFraction.mul_pos_direct lowerPositive lowerPositive
  unfold CCL.ProgressiveEnclosures.Name.divisionInputTarget
  rw [leftBound, rightBound]
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).2
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    requestSmall lowerProductPositive
  unfold divisionOuterTarget at scaled
  have outerCancelled :
      (operandRequest * (4 * (left.centerBound + right.centerBound + 1)) /
          (lowerSq * lowerSq)) * (lowerSq * lowerSq) =
        operandRequest * (4 * (left.centerBound + right.centerBound + 1)) :=
    RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
      lowerProductPositive.ne'
  rw [outerCancelled] at scaled
  simpa only [denominator] using scaled

/-- The finite operand request used by stateful addition is strictly smaller
than its positive outer request. -/
theorem additiveInputTarget_lt_target {target : Coordinate}
    (positive : 0 < target) :
    CCL.ProgressiveEnclosures.Name.additiveInputTarget target <
      target := by
  unfold CCL.ProgressiveEnclosures.Name.additiveInputTarget
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (show (0 : Coordinate) < 4 by decide)).2
  have threeTargetPositive : 0 < 3 * target :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) positive
  calc
    target = target + 0 := by ring1
    _ < target + 3 * target :=
      RFAP.ConstructiveFraction.add_lt_add_left_direct
        threeTargetPositive target
    _ = target * 4 := by ring1

private theorem half_add_quarter_lt {target : Coordinate}
    (positive : 0 < target) : target / 2 + target / 4 < target := by
  have quarterPositive : 0 < target / 4 :=
    RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
  have quarters : target / 4 + target / 4 = target / 2 := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      (show (4 : Coordinate) ≠ 0 by decide)
    calc
      (target / 4 + target / 4) * 4 =
          (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
      _ = target + target := by
        rw [show (target / 4) * 4 = target from
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 4 (by decide)]
      _ = target * 2 := by ring1
      _ = ((target / 2) * 2) * 2 := by
        rw [show (target / 2) * 2 = target from
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 2 (by decide)]
      _ = (target / 2) * 4 := by ring1
  have halves : target / 2 + target / 2 = target := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      (show (2 : Coordinate) ≠ 0 by decide)
    calc
      (target / 2 + target / 2) * 2 =
          (target / 2) * 2 + (target / 2) * 2 := by rw [add_mul]
      _ = target + target := by
        rw [show (target / 2) * 2 = target from
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 2 (by decide)]
      _ = target * 2 := by ring1
  have addQuarter := RFAP.ConstructiveFraction.add_lt_add_left_direct
    quarterPositive (target / 2 + target / 4)
  calc
    target / 2 + target / 4 = target / 2 + target / 4 + 0 := by ring1
    _ < target / 2 + target / 4 + target / 4 := addQuarter
    _ = target / 2 + (target / 4 + target / 4) := by ring1
    _ = target / 2 + target / 2 := by rw [quarters]
    _ = target := halves

/-- Finite process coherence is preserved by division once the denominator
process carries a uniform finite apartness certificate.  The request schedule
first makes both operand allowances small enough for the semantic quotient
estimate, then makes the ordinary enclosure radius small enough for the
remaining half of the requested budget. -/
def div {left right : Process} (leftCoherent : Coherent left)
    (rightCoherent : Coherent right)
    (apart : CCL.ProgressiveEnclosures.Process.Apart right) :
    Coherent (left.div right apart) where
  allowance := divisionAllowance leftCoherent rightCoherent apart
  allowance_nonneg state :=
    add_nonneg ((left.div right apart).ball state).radiusSq_nonneg
      (divisionSemanticAllowance_nonneg left.centerBound_nonneg
        right.centerBound_nonneg apart.positive.le
        (leftCoherent.allowance_nonneg state.1)
        (rightCoherent.allowance_nonneg state.2))
  ball_radius_le state :=
    le_add_of_nonneg_right
      (divisionSemanticAllowance_nonneg left.centerBound_nonneg
        right.centerBound_nonneg apart.positive.le
        (leftCoherent.allowance_nonneg state.1)
        (rightCoherent.allowance_nonneg state.2))
  possible_close := by
    rintro leftState rightState leftValue rightValue
      ⟨leftX, leftY, leftXPossible, leftYPossible, rfl⟩
      ⟨rightX, rightY, rightXPossible, rightYPossible, rfl⟩
    exact division_possible_close leftCoherent rightCoherent apart
      leftXPossible leftYPossible rightXPossible rightYPossible
  accuracyRequest target :=
    let semanticTarget := divisionSemanticTarget apart.lowerSq target
    let operandTarget := productInputTarget left right semanticTarget
    let leftRequest := leftCoherent.accuracyRequest operandTarget
    let rightRequest := rightCoherent.accuracyRequest operandTarget
    let sharedRequest := commonRequest leftRequest rightRequest
    CCL.ProgressiveCharts.commonTarget (target / 2)
      (divisionOuterTarget left right apart.lowerSq sharedRequest)
  accuracyRequest_pos := by
    intro target positive
    let semanticTarget := divisionSemanticTarget apart.lowerSq target
    have semanticPositive : 0 < semanticTarget :=
      divisionSemanticTarget_pos apart.positive positive
    let operandTarget := productInputTarget left right semanticTarget
    have operandPositive : 0 < operandTarget :=
      productInputTarget_pos left right semanticPositive
    let leftRequest := leftCoherent.accuracyRequest operandTarget
    let rightRequest := rightCoherent.accuracyRequest operandTarget
    have leftRequestPositive : 0 < leftRequest :=
      leftCoherent.accuracyRequest_pos operandPositive
    have rightRequestPositive : 0 < rightRequest :=
      rightCoherent.accuracyRequest_pos operandPositive
    let sharedRequest := commonRequest leftRequest rightRequest
    have sharedPositive : 0 < sharedRequest :=
      commonRequest_pos leftRequestPositive rightRequestPositive
    exact CCL.ProgressiveCharts.commonTarget_pos
      (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))
      (divisionOuterTarget_pos left right apart.positive sharedPositive)
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    let semanticTarget := divisionSemanticTarget apart.lowerSq target
    have semanticPositive : 0 < semanticTarget :=
      divisionSemanticTarget_pos apart.positive positive
    let operandTarget := productInputTarget left right semanticTarget
    have operandPositive : 0 < operandTarget :=
      productInputTarget_pos left right semanticPositive
    let leftRequest := leftCoherent.accuracyRequest operandTarget
    let rightRequest := rightCoherent.accuracyRequest operandTarget
    have leftRequestPositive : 0 < leftRequest :=
      leftCoherent.accuracyRequest_pos operandPositive
    have rightRequestPositive : 0 < rightRequest :=
      rightCoherent.accuracyRequest_pos operandPositive
    let sharedRequest := commonRequest leftRequest rightRequest
    have sharedPositive : 0 < sharedRequest :=
      commonRequest_pos leftRequestPositive rightRequestPositive
    let outerTarget :=
      divisionOuterTarget left right apart.lowerSq sharedRequest
    have outerPositive : 0 < outerTarget :=
      divisionOuterTarget_pos left right apart.positive sharedPositive
    let radiusTarget := target / 2
    have radiusPositive : 0 < radiusTarget :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    change request <
      CCL.ProgressiveCharts.commonTarget radiusTarget outerTarget
        at requestSmall
    have requestLtRadius : request < radiusTarget :=
      requestSmall.trans
        (CCL.ProgressiveCharts.commonTarget_lt_left
          radiusPositive outerPositive)
    have requestLtOuter : request < outerTarget :=
      requestSmall.trans
        (CCL.ProgressiveCharts.commonTarget_lt_right
          radiusPositive outerPositive)
    let leftName :=
      CCL.ProgressiveEnclosures.Name.centerOnly
        (left.ball state.1).center left.centerBound left.centerBound_nonneg
        (left.center_bounded state.1)
    let rightName :=
      CCL.ProgressiveEnclosures.Name.centerOnly
        (right.ball state.2).center right.centerBound right.centerBound_nonneg
        (right.center_bounded state.2)
    let processInputTarget :=
      CCL.ProgressiveEnclosures.Name.divisionInputTarget
        leftName rightName apart.lowerSq request
    have processInputPositive : 0 < processInputTarget :=
      CCL.ProgressiveEnclosures.Name.divisionInputTarget_pos
        leftName rightName apart.lowerSq apart.positive requestPositive
    have processInputLtShared : processInputTarget < sharedRequest :=
      processDivisionInputTarget_lt leftName rightName rfl rfl apart.positive
        requestLtOuter
    have processInputLtLeft : processInputTarget < leftRequest :=
      processInputLtShared.trans
        (commonRequest_lt_left leftRequestPositive rightRequestPositive)
    have processInputLtRight : processInputTarget < rightRequest :=
      processInputLtShared.trans
        (commonRequest_lt_right leftRequestPositive rightRequestPositive)
    have leftSmall :
        leftCoherent.allowance
            (left.refine state.1 processInputTarget processInputPositive) <
          operandTarget :=
      leftCoherent.refine_accurate state.1 operandTarget operandPositive
        processInputTarget processInputPositive processInputLtLeft
    have rightSmall :
        rightCoherent.allowance
            (right.refine state.2 processInputTarget processInputPositive) <
          operandTarget :=
      rightCoherent.refine_accurate state.2 operandTarget operandPositive
        processInputTarget processInputPositive processInputLtRight
    have semanticSmall :
        divisionSemanticAllowance left.centerBound right.centerBound
            apart.lowerSq
            (leftCoherent.allowance
              (left.refine state.1 processInputTarget processInputPositive))
            (rightCoherent.allowance
              (right.refine state.2 processInputTarget processInputPositive)) <
          target / 4 :=
      divisionSemanticAllowance_lt_quarter apart positive leftSmall rightSmall
        (leftCoherent.allowance_nonneg _)
        (rightCoherent.allowance_nonneg _)
    have radiusSmall :
        ((left.div right apart).ball
            ((left.div right apart).refine state request requestPositive)).radiusSq <
          target / 2 :=
      ((left.div right apart).accurate state request requestPositive).trans
        requestLtRadius
    change
      ((left.div right apart).ball
          ((left.div right apart).refine state request requestPositive)).radiusSq +
        divisionSemanticAllowance left.centerBound right.centerBound
          apart.lowerSq
          (leftCoherent.allowance
            (left.refine state.1 processInputTarget processInputPositive))
          (rightCoherent.allowance
            (right.refine state.2 processInputTarget processInputPositive)) <
        target
    exact (RFAP.ConstructiveFraction.add_lt_add_direct
      radiusSmall semanticSmall).trans (half_add_quarter_lt positive)

/-- Restricting a coherent process to the refinement future of one explicit
base state preserves coherence.  The based state remembers that every later
candidate was already possible at the base; the numerical allowance remains
the allowance of its displayed source state. -/
def based {process : Process} (coherent : Coherent process)
    (base : process.State) :
    Coherent (CCL.ProgressiveCharts.based process base) where
  allowance state := coherent.allowance state.source
  allowance_nonneg state := coherent.allowance_nonneg state.source
  ball_radius_le state := coherent.ball_radius_le state.source
  possible_close := by
    intro leftState rightState leftValue rightValue leftPossible rightPossible
    exact coherent.possible_close leftPossible rightPossible
  accuracyRequest := coherent.accuracyRequest
  accuracyRequest_pos := coherent.accuracyRequest_pos
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    exact coherent.refine_accurate state.source target positive request
      requestPositive requestSmall

/-- Preparing an explicitly candidate-apart process for whole-ball inversion
preserves finite coherence.  Each refinement uses one finite common request;
no limiting value or completed family of states is selected. -/
def apartify {process : Process} (coherent : Coherent process)
    (apart : CCL.ProgressiveCharts.PossibleApart process) :
    Coherent (CCL.ProgressiveCharts.apartify apart) where
  allowance state := coherent.allowance state.source
  allowance_nonneg state := coherent.allowance_nonneg state.source
  ball_radius_le state := coherent.ball_radius_le state.source
  possible_close := by
    intro leftState rightState leftValue rightValue leftPossible rightPossible
    exact coherent.possible_close leftPossible rightPossible
  accuracyRequest := coherent.accuracyRequest
  accuracyRequest_pos := coherent.accuracyRequest_pos
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    let apartTarget := apart.lowerSq / 12
    have apartTargetPositive : 0 < apartTarget := apart.twelfth_pos
    let inputTarget :=
      CCL.ProgressiveCharts.commonTarget request apartTarget
    have inputPositive : 0 < inputTarget :=
      CCL.ProgressiveCharts.commonTarget_pos requestPositive
        apartTargetPositive
    have inputSmallRequest : inputTarget < request :=
      CCL.ProgressiveCharts.commonTarget_lt_left requestPositive
        apartTargetPositive
    change coherent.allowance
        (process.refine state.source inputTarget inputPositive) < target
    exact coherent.refine_accurate state.source target positive inputTarget
      inputPositive (inputSmallRequest.trans requestSmall)

/-- Once the canonical rational process request is below a coherence
certificate's computed request, that finite sample state has the desired
semantic allowance. -/
theorem stateAt_allowance_lt {process : Process} (coherent : Coherent process)
    (start : process.State) (index : Nat) (target : Coordinate)
    (positive : 0 < target)
    (requestSmall :
      CCL.ProgressiveSampling.refinementTarget index <
        coherent.accuracyRequest target) :
    coherent.allowance
        (CCL.ProgressiveSampling.stateAt process start index) <
      target := by
  cases index with
  | zero =>
      exact coherent.refine_accurate start target positive _ _ requestSmall
  | succ index =>
      exact coherent.refine_accurate
        (CCL.ProgressiveSampling.stateAt process start index)
        target positive _ _ requestSmall

private theorem quarterRadius_index_antitone {scale : Coordinate}
    (scaleNonnegative : 0 ≤ scale) {earlier later : Nat}
    (order : earlier ≤ later) :
    CCL.FiniteGeometric.quarterRadius scale later ≤
      CCL.FiniteGeometric.quarterRadius scale earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_add]
  have extraPowerLe : (1 / 4 : Coordinate) ^ extra ≤ 1 := by
    have powerOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      (show (0 : Coordinate) ≤ 1 / 4 by decide)
      (show (1 / 4 : Coordinate) ≤ 1 by decide) extra
    simpa only [one_pow] using powerOrder
  have earlierPowerNonnegative : 0 ≤ (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _
  have scaledNonnegative :
      0 ≤ scale * (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.mul_nonneg_direct scaleNonnegative
      earlierPowerNonnegative
  calc
    scale * ((1 / 4 : Coordinate) ^ earlier *
        (1 / 4 : Coordinate) ^ extra) =
      (scale * (1 / 4 : Coordinate) ^ earlier) *
        (1 / 4 : Coordinate) ^ extra := by ring1
    _ ≤ (scale * (1 / 4 : Coordinate) ^ earlier) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        extraPowerLe scaledNonnegative
    _ = scale * (1 / 4 : Coordinate) ^ earlier :=
      RFAP.ConstructiveFraction.mul_one_direct _

private theorem eight_eighths (target : Coordinate) :
    4 * (target / 8 + target / 8) = target := by
  have half : target / 8 + target / 8 = target / 4 := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      (show (8 : Coordinate) ≠ 0 by decide)
    calc
      (target / 8 + target / 8) * 8 =
          (target / 8) * 8 + (target / 8) * 8 := by rw [add_mul]
      _ = target + target := by
        rw [show target / 8 * 8 = target from
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 8 (by decide)]
      _ = target * 2 := by ring1
      _ = ((target / 4) * 4) * 2 := by
        rw [show target / 4 * 4 = target from
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 4 (by decide)]
      _ = (target / 4) * 8 := by ring1
  rw [half, RFAP.ConstructiveFraction.mul_comm]
  exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 4 (by decide)

theorem eighth_pos {target : Coordinate} (positive : 0 < target) :
    0 < target / 8 :=
  RFAP.ConstructiveFraction.div_pos_direct positive (by decide)

/-- Coherence closes the original branching-process gap: any two starting
states of one coherent process yield operationally equivalent CCL names.
The comparison computes one finite sampling index and thereafter compares
only explicit rational witnesses at finite states. -/
def namedEquivalent {process : Process} (coherent : Coherent process)
    (leftStart rightStart : process.State) :
    NamedEquivalent
      ({ process := process, state := leftStart } : Named)
      ({ process := process, state := rightStart } : Named) where
  compare := by
    intro leftIndex rightIndex target positive
    let startIndex := max leftIndex rightIndex
    let semanticTarget := target / 8
    have semanticPositive : 0 < semanticTarget := eighth_pos positive
    let processTarget := coherent.accuracyRequest semanticTarget
    have processTargetPositive : 0 < processTarget :=
      coherent.accuracyRequest_pos semanticPositive
    let comparisonIndex :=
      CCL.FiniteGeometric.firstQuarterBelow
        1 startIndex processTarget
    have comparisonRequestSmall :
        CCL.ProgressiveSampling.refinementTarget comparisonIndex <
          processTarget := by
      exact CCL.FiniteGeometric.firstQuarterBelow_accurate
        1 (by decide) startIndex processTarget processTargetPositive
    exact
      { leftIndex := comparisonIndex
        rightIndex := comparisonIndex
        left_ge := (Nat.le_max_left _ _).trans
          (CCL.FiniteGeometric.firstQuarterBelow_ge
            1 startIndex processTarget)
        right_ge := (Nat.le_max_right _ _).trans
          (CCL.FiniteGeometric.firstQuarterBelow_ge
            1 startIndex processTarget)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftAllowanceLt :
              coherent.allowance
                  (CCL.ProgressiveSampling.stateAt process
                    leftStart leftLater) < target / 8 :=
            stateAt_allowance_lt coherent leftStart leftLater semanticTarget
              semanticPositive
              ((quarterRadius_index_antitone (by decide) leftOrder).trans_lt
                comparisonRequestSmall)
          have rightAllowanceLt :
              coherent.allowance
                  (CCL.ProgressiveSampling.stateAt process
                    rightStart rightLater) < target / 8 :=
            stateAt_allowance_lt coherent rightStart rightLater semanticTarget
              semanticPositive
              ((quarterRadius_index_antitone (by decide) rightOrder).trans_lt
                comparisonRequestSmall)
          have close := coherent.possible_close
            (CCL.ProgressiveSampling.witnessAt_possible
              process leftStart leftLater)
            (CCL.ProgressiveSampling.witnessAt_possible
              process rightStart rightLater)
          calc
            normSq
                (CCL.ProgressiveSampling.witnessAt process
                    leftStart leftLater -
                  CCL.ProgressiveSampling.witnessAt process
                    rightStart rightLater) ≤
              4 *
                (coherent.allowance
                    (CCL.ProgressiveSampling.stateAt process
                      leftStart leftLater) +
                  coherent.allowance
                    (CCL.ProgressiveSampling.stateAt process
                      rightStart rightLater)) := close
            _ < 4 * (target / 8 + target / 8) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  leftAllowanceLt rightAllowanceLt)
            _ = target := eight_eighths target }

end Coherent

/-! ## Coherent names as an arithmetic interface -/

/-- A productive CCL name together with the finite sidecar certificate that
its independently refined process branches remain semantically coherent. -/
structure CoherentNamed where
  name : Named
  coherent : Coherent name.process

namespace CoherentNamed

/-- A displayed exact Gaussian rational as a coherent productive name. -/
def exact (value : Gaussian) : CoherentNamed :=
  { name := CCL.ProgressiveTransducer.Named.exact value
    coherent := Coherent.exact value }

/-- Turn a limit-free finite approximation directly into a coherent name. -/
def ofApproximation (approximation : Approximation) : CoherentNamed :=
  { name := approximation.toNamed
    coherent := Coherent.ofApproximation approximation }

def add (left right : CoherentNamed) : CoherentNamed :=
  { name := left.name.add right.name
    coherent := Coherent.add left.coherent right.coherent }

def neg (value : CoherentNamed) : CoherentNamed :=
  { name := value.name.neg
    coherent := Coherent.neg value.coherent }

def sub (left right : CoherentNamed) : CoherentNamed :=
  { name := left.name.sub right.name
    coherent := Coherent.sub left.coherent right.coherent }

def mul (left right : CoherentNamed) : CoherentNamed :=
  { name := left.name.mul right.name
    coherent := Coherent.mul left.coherent right.coherent }

/-- Restrict a coherent name to the finite refinement future of `state`.
Unlike merely changing the starting state, this changes the process state type
so that every retained state carries its provenance from the chosen base. -/
def based (value : CoherentNamed)
    (state : value.name.process.State) : CoherentNamed :=
  { name :=
      { process := CCL.ProgressiveCharts.based value.name.process state
        state := CCL.ProgressiveCharts.BasedState.initial
          value.name.process state }
    coherent := Coherent.based value.coherent state }

/-- Restricting a coherent name to a finite refinement future preserves its
operational value.  The proof compares only displayed rational witnesses and
uses the source coherence allowance on both sides. -/
def basedEquivalent (value : CoherentNamed)
    (state : value.name.process.State) :
    NamedEquivalent value.name (based value state).name where
  compare := by
    intro leftIndex rightIndex target positive
    let startIndex := max leftIndex rightIndex
    let semanticTarget := target / 8
    have semanticPositive : 0 < semanticTarget := Coherent.eighth_pos positive
    let processRequest := value.coherent.accuracyRequest semanticTarget
    have processRequestPositive : 0 < processRequest :=
      value.coherent.accuracyRequest_pos semanticPositive
    let comparisonIndex := CCL.FiniteGeometric.firstQuarterBelow
      1 startIndex processRequest
    have comparisonRequestSmall :
        CCL.ProgressiveSampling.refinementTarget comparisonIndex <
          processRequest :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate
        1 (by decide) startIndex processRequest processRequestPositive
    exact
      { leftIndex := comparisonIndex
        rightIndex := comparisonIndex
        left_ge := (Nat.le_max_left _ _).trans
          (CCL.FiniteGeometric.firstQuarterBelow_ge
            1 startIndex processRequest)
        right_ge := (Nat.le_max_right _ _).trans
          (CCL.FiniteGeometric.firstQuarterBelow_ge
            1 startIndex processRequest)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftAllowanceLt :
              value.coherent.allowance
                  (CCL.ProgressiveSampling.stateAt value.name.process
                    value.name.state leftLater) < target / 8 :=
            Coherent.stateAt_allowance_lt value.coherent value.name.state
              leftLater semanticTarget semanticPositive
              ((Coherent.quarterRadius_index_antitone (by decide)
                leftOrder).trans_lt comparisonRequestSmall)
          have rightAllowanceLt :
              value.coherent.allowance
                  (CCL.ProgressiveSampling.stateAt
                    (CCL.ProgressiveCharts.based value.name.process state)
                    (CCL.ProgressiveCharts.BasedState.initial
                      value.name.process state) rightLater).source <
                target / 8 :=
            Coherent.stateAt_allowance_lt
              (Coherent.based value.coherent state)
              (CCL.ProgressiveCharts.BasedState.initial
                value.name.process state)
              rightLater semanticTarget semanticPositive
              ((Coherent.quarterRadius_index_antitone (by decide)
                rightOrder).trans_lt comparisonRequestSmall)
          have close := value.coherent.possible_close
            (CCL.ProgressiveSampling.witnessAt_possible value.name.process
              value.name.state leftLater)
            (show value.name.process.Possible
                (CCL.ProgressiveSampling.stateAt
                  (CCL.ProgressiveCharts.based value.name.process state)
                  (CCL.ProgressiveCharts.BasedState.initial
                    value.name.process state) rightLater).source
                (CCL.ProgressiveSampling.witnessAt
                  (CCL.ProgressiveCharts.based value.name.process state)
                  (CCL.ProgressiveCharts.BasedState.initial
                    value.name.process state) rightLater) from
              CCL.ProgressiveSampling.witnessAt_possible
                (CCL.ProgressiveCharts.based value.name.process state)
                (CCL.ProgressiveCharts.BasedState.initial
                  value.name.process state) rightLater)
          calc
            RFAP.ConstructiveGaussian.Gaussian.normSq
                ((CCL.ProgressiveSampling.approximation value.name).sample
                    leftLater -
                  (CCL.ProgressiveSampling.approximation
                    (based value state).name).sample rightLater) <=
              4 *
                (value.coherent.allowance
                    (CCL.ProgressiveSampling.stateAt value.name.process
                      value.name.state leftLater) +
                  value.coherent.allowance
                    (CCL.ProgressiveSampling.stateAt
                      (CCL.ProgressiveCharts.based value.name.process state)
                      (CCL.ProgressiveCharts.BasedState.initial
                        value.name.process state) rightLater).source) := close
            _ < 4 * (target / 8 + target / 8) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  leftAllowanceLt rightAllowanceLt)
            _ = target := Coherent.eight_eighths target }

/-- Prepare a candidate-apart coherent name for whole-ball division using one
explicit finite starting-state refinement. -/
def apartify (value : CoherentNamed)
    (apart : CCL.ProgressiveCharts.PossibleApart
      value.name.process) : CoherentNamed :=
  { name :=
      { process := CCL.ProgressiveCharts.apartify apart
        state := CCL.ProgressiveCharts.prepareApartState apart
          value.name.state }
    coherent := Coherent.apartify value.coherent apart }

/-- Preparing a candidate-apart coherent name for division preserves its
finite operational value.  The prepared process has a different state type,
so this is stronger than merely rebasing the original process: every sampled
candidate on the prepared side is compared through the original coherence
certificate. -/
def apartifyEquivalent (value : CoherentNamed)
    (apart : CCL.ProgressiveCharts.PossibleApart value.name.process) :
    NamedEquivalent value.name (apartify value apart).name where
  compare := by
    intro leftIndex rightIndex target positive
    let startIndex := max leftIndex rightIndex
    let semanticTarget := target / 8
    have semanticPositive : 0 < semanticTarget := Coherent.eighth_pos positive
    let leftRequest := value.coherent.accuracyRequest semanticTarget
    let preparedCoherent := Coherent.apartify value.coherent apart
    let rightRequest := preparedCoherent.accuracyRequest semanticTarget
    let processRequest := CCL.ProgressiveCharts.commonTarget
      leftRequest rightRequest
    have leftRequestPositive : 0 < leftRequest :=
      value.coherent.accuracyRequest_pos semanticPositive
    have rightRequestPositive : 0 < rightRequest :=
      preparedCoherent.accuracyRequest_pos semanticPositive
    have processRequestPositive : 0 < processRequest :=
      CCL.ProgressiveCharts.commonTarget_pos leftRequestPositive
        rightRequestPositive
    let comparisonIndex := CCL.FiniteGeometric.firstQuarterBelow
      1 startIndex processRequest
    have comparisonRequestSmall :
        CCL.ProgressiveSampling.refinementTarget comparisonIndex <
          processRequest :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate
        1 (by decide) startIndex processRequest processRequestPositive
    have comparisonLeftSmall :
        CCL.ProgressiveSampling.refinementTarget comparisonIndex <
          leftRequest :=
      comparisonRequestSmall.trans
        (CCL.ProgressiveCharts.commonTarget_lt_left
          leftRequestPositive rightRequestPositive)
    have comparisonRightSmall :
        CCL.ProgressiveSampling.refinementTarget comparisonIndex <
          rightRequest :=
      comparisonRequestSmall.trans
        (CCL.ProgressiveCharts.commonTarget_lt_right
          leftRequestPositive rightRequestPositive)
    exact
      { leftIndex := comparisonIndex
        rightIndex := comparisonIndex
        left_ge := (Nat.le_max_left _ _).trans
          (CCL.FiniteGeometric.firstQuarterBelow_ge
            1 startIndex processRequest)
        right_ge := (Nat.le_max_right _ _).trans
          (CCL.FiniteGeometric.firstQuarterBelow_ge
            1 startIndex processRequest)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftAllowanceLt :
              value.coherent.allowance
                  (CCL.ProgressiveSampling.stateAt value.name.process
                    value.name.state leftLater) < target / 8 :=
            Coherent.stateAt_allowance_lt value.coherent value.name.state
              leftLater semanticTarget semanticPositive
              ((Coherent.quarterRadius_index_antitone (by decide)
                leftOrder).trans_lt comparisonLeftSmall)
          have rightAllowanceLt :
              preparedCoherent.allowance
                  (CCL.ProgressiveSampling.stateAt
                    (CCL.ProgressiveCharts.apartify apart)
                    (CCL.ProgressiveCharts.prepareApartState apart
                      value.name.state) rightLater) < target / 8 :=
            Coherent.stateAt_allowance_lt preparedCoherent
              (CCL.ProgressiveCharts.prepareApartState apart value.name.state)
              rightLater semanticTarget semanticPositive
              ((Coherent.quarterRadius_index_antitone (by decide)
                rightOrder).trans_lt comparisonRightSmall)
          have close := value.coherent.possible_close
            (CCL.ProgressiveSampling.witnessAt_possible value.name.process
              value.name.state leftLater)
            (show value.name.process.Possible
                (CCL.ProgressiveSampling.stateAt
                  (CCL.ProgressiveCharts.apartify apart)
                  (CCL.ProgressiveCharts.prepareApartState apart
                    value.name.state) rightLater).source
                (CCL.ProgressiveSampling.witnessAt
                  (CCL.ProgressiveCharts.apartify apart)
                  (CCL.ProgressiveCharts.prepareApartState apart
                    value.name.state) rightLater) from
              CCL.ProgressiveSampling.witnessAt_possible
                (CCL.ProgressiveCharts.apartify apart)
                (CCL.ProgressiveCharts.prepareApartState apart
                  value.name.state) rightLater)
          calc
            RFAP.ConstructiveGaussian.Gaussian.normSq
                ((CCL.ProgressiveSampling.approximation value.name).sample
                    leftLater -
                  (CCL.ProgressiveSampling.approximation
                    (apartify value apart).name).sample rightLater) <=
              4 *
                (value.coherent.allowance
                    (CCL.ProgressiveSampling.stateAt value.name.process
                      value.name.state leftLater) +
                  value.coherent.allowance
                    (CCL.ProgressiveSampling.stateAt
                      (CCL.ProgressiveCharts.apartify apart)
                      (CCL.ProgressiveCharts.prepareApartState apart
                        value.name.state) rightLater).source) := close
            _ < 4 * (target / 8 + target / 8) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  leftAllowanceLt rightAllowanceLt)
            _ = target := Coherent.eight_eighths target }

/-- Apartness-certified division of two coherent productive names. -/
def div (left right : CoherentNamed)
    (apart : CCL.ProgressiveTransducer.Named.Apart right.name) :
    CoherentNamed :=
  { name := left.name.div right.name apart
    coherent := Coherent.div left.coherent right.coherent apart.certificate }

/-- Replacing only the explicit starting state of a coherent process does not
change the operational value of its productive CCL name. -/
def rebaseEquivalent (value : CoherentNamed)
    (state : value.name.process.State) :
    NamedEquivalent value.name
      ({ process := value.name.process, state := state } : Named) :=
  value.coherent.namedEquivalent value.name.state state

end CoherentNamed

end CCL.ProgressiveCoherence
