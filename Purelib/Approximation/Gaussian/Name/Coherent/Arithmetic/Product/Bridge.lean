module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
public import Purelib.Approximation.Gaussian.Name.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Approximation.Gaussian.Request.Multiplication
public import Purelib.Approximation.Gaussian.Sampling.Dyadic
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Multiplication
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

/-!
# Coherent Gaussian products and their retained arithmetic process

The comparison relates the original coherent operands' arithmetic product to
its canonical equal-index sampled product. The requested tolerance and retained
center bounds determine the same finite component observations and payment.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Request.Basic
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat

/-- A positive product refinement request below both operand accuracy requests makes both retained operand allowances
smaller than the target.

Both supplied coherent operands use the product process's computed input request. The retained request-smallness
certificates bound the same refined component allowances by the positive target. -/
private theorem coherentProduct_refine_component_allowance_lt
    {leftProcess rightProcess : Process}
    (leftCoherent : Gaussian.Process.Coherence.Basic.Coherent leftProcess)
    (rightCoherent : Gaussian.Process.Coherence.Basic.Coherent rightProcess)
    (state : leftProcess.State × rightProcess.State)
    (request : Fraction.Rational) (requestPositive : 0 < request)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (leftRequestSmall : request < leftCoherent.accuracyRequest target)
    (rightRequestSmall : request < rightCoherent.accuracyRequest target) :
    let refined := (leftProcess.mul rightProcess).refine
      state request requestPositive
    leftCoherent.allowance refined.1 < target ∧
      rightCoherent.allowance refined.2 < target := by
  let leftName := Name.centerOnly
    (leftProcess.ball state.1).center leftProcess.centerBound
      leftProcess.centerBound_nonneg (leftProcess.center_bounded state.1)
  let rightName := Name.centerOnly
    (rightProcess.ball state.2).center rightProcess.centerBound
      rightProcess.centerBound_nonneg (rightProcess.center_bounded state.2)
  let inputRequest :=
    Name.multiplicativeInputTarget
      leftName rightName request
  have inputPositive : 0 < inputRequest :=
    Name.multiplicativeInputTarget_pos
      leftName rightName requestPositive
  have inputLtRequest : inputRequest < request :=
    Gaussian.Process.Coherence.Basic.Coherent.processMultiplicativeInputTarget_lt_target
      leftName rightName requestPositive
  change leftCoherent.allowance
        (leftProcess.refine state.1 inputRequest inputPositive) < target ∧
      rightCoherent.allowance
        (rightProcess.refine state.2 inputRequest inputPositive) < target
  exact ⟨leftCoherent.refine_accurate state.1 target targetPositive
      inputRequest inputPositive (inputLtRequest.trans leftRequestSmall),
    rightCoherent.refine_accurate state.2 target targetPositive
      inputRequest inputPositive (inputLtRequest.trans rightRequestSmall)⟩

/-- A canonical product sample request below both operand accuracy requests gives operand allowances below the target.

The canonical product sample retains its two original component states. The two supplied request bounds certify their
corresponding coherent allowances at that finite index. -/
public theorem coherentProduct_stateAt_component_allowance_lt
    {leftProcess rightProcess : Process}
    (leftCoherent : Gaussian.Process.Coherence.Basic.Coherent leftProcess)
    (rightCoherent : Gaussian.Process.Coherence.Basic.Coherent rightProcess)
    (start : leftProcess.State × rightProcess.State) (index : Nat)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (leftRequestSmall :
      Gaussian.Process.Sampling.refinementTarget index <
        leftCoherent.accuracyRequest target)
    (rightRequestSmall :
      Gaussian.Process.Sampling.refinementTarget index <
        rightCoherent.accuracyRequest target) :
    let state := Gaussian.Process.Sampling.stateAt
      (leftProcess.mul rightProcess) start index
    leftCoherent.allowance state.1 < target ∧
      rightCoherent.allowance state.2 < target := by
  cases index with
  | zero =>
      exact coherentProduct_refine_component_allowance_lt
        leftCoherent rightCoherent start _ _ target targetPositive
          leftRequestSmall rightRequestSmall
  | succ index =>
      exact coherentProduct_refine_component_allowance_lt
        leftCoherent rightCoherent
          (Gaussian.Process.Sampling.stateAt
            (leftProcess.mul rightProcess) start index) _ _ target
              targetPositive leftRequestSmall rightRequestSmall

/-- The rational comparison coefficient combining product movement and the original operand center bounds.

The retained process center bounds determine this same positive rational coefficient. Both original process owners
remain its inputs. -/
@[expose] public def coherentProductBridgeCoefficient (left right : Process) : Fraction.Rational
  :=
  8 + 4 *
    (8 *
      (2 * (1 + left.centerBound) + 2 * (1 + right.centerBound)))

/-- The retained product comparison coefficient is strictly positive.

The constant eight is positive and both retained process center bounds are nonnegative. The displayed positive scalar
factors preserve nonnegativity of their combined contribution. -/
public theorem coherentProductBridgeCoefficient_pos (left right : Process) :
    0 < coherentProductBridgeCoefficient left right := by
  unfold coherentProductBridgeCoefficient
  exact Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg (by decide) left.centerBound_nonneg))
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg (by decide) right.centerBound_nonneg)))))

/-- The semantic operand target obtained by dividing the output target by its sum with the retained product comparison
coefficient.

The positive output tolerance and retained coefficient form the denominator. The same process owners and rational
division operation determine the input tolerance. -/
@[expose] public def coherentProductBridgeTarget (left right : Process)
    (target : Fraction.Rational) : Fraction.Rational :=
  target / (target + coherentProductBridgeCoefficient left right)

/-- The semantic product comparison target is positive for a positive output target.

The requested target and retained coefficient are both strictly positive. Their sum is the denominator of the same
rational input tolerance. -/
public theorem coherentProductBridgeTarget_pos (left right : Process)
    {target : Fraction.Rational} (positive : 0 < target) :
    0 < coherentProductBridgeTarget left right target :=
  Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (coherentProductBridgeCoefficient_pos left right).le)

/-- The semantic product comparison target is strictly below one for a positive output target.

The retained coefficient is strictly positive, so the requested target is strictly smaller than their sum. Division by
this positive sum gives the displayed strict unit bound. -/
public theorem coherentProductBridgeTarget_lt_one (left right : Process)
    {target : Fraction.Rational} (positive : 0 < target) :
    coherentProductBridgeTarget left right target < 1 := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (coherentProductBridgeCoefficient_pos left right).le)).2
  calc
    target = 0 + target :=
      (Fraction.Field.zero_add target).symm
    _ < coherentProductBridgeCoefficient left right + target :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct
        (coherentProductBridgeCoefficient_pos left right) target
    _ = target + coherentProductBridgeCoefficient left right :=
      _root_.add_comm _ _
    _ = 1 * (target + coherentProductBridgeCoefficient left right) :=
      (Fraction.Field.one_mul _).symm

/-- Multiplying the semantic product target by the retained comparison coefficient remains strictly below the original
positive target.

The positive requested target makes the coefficient strictly smaller than their sum. Scaling this strict comparison by
the same target bounds the retained comparison payment. -/
public theorem coherentProductBridgeTarget_budget_lt (left right : Process)
    {target : Fraction.Rational} (positive : 0 < target) :
    coherentProductBridgeTarget left right target *
        coherentProductBridgeCoefficient left right < target := by
  have denominatorPositive :
      0 < target + coherentProductBridgeCoefficient left right :=
    Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (coherentProductBridgeCoefficient_pos left right).le
  change target / (target + coherentProductBridgeCoefficient left right) *
      coherentProductBridgeCoefficient left right < target
  calc
    target / (target + coherentProductBridgeCoefficient left right) *
        coherentProductBridgeCoefficient left right =
      (target * coherentProductBridgeCoefficient left right) /
        (target + coherentProductBridgeCoefficient left right) := by
      change (target *
          (target + coherentProductBridgeCoefficient left right)⁻¹) *
            coherentProductBridgeCoefficient left right =
        (target * coherentProductBridgeCoefficient left right) *
          (target + coherentProductBridgeCoefficient left right)⁻¹
      calc
        (target *
            (target + coherentProductBridgeCoefficient left right)⁻¹) *
              coherentProductBridgeCoefficient left right =
          target *
            ((target + coherentProductBridgeCoefficient left right)⁻¹ *
              coherentProductBridgeCoefficient left right) :=
            _root_.mul_assoc _ _ _
        _ = target *
            (coherentProductBridgeCoefficient left right *
              (target + coherentProductBridgeCoefficient left right)⁻¹) := by
          rw [Fraction.Field.mul_comm
            (target + coherentProductBridgeCoefficient left right)⁻¹]
        _ = (target * coherentProductBridgeCoefficient left right) *
            (target + coherentProductBridgeCoefficient left right)⁻¹ :=
          (_root_.mul_assoc _ _ _).symm
    _ < target := by
      apply (Fraction.Order.Field.div_lt_iff_pos
        denominatorPositive).2
      have coefficientLt : coherentProductBridgeCoefficient left right <
          target + coherentProductBridgeCoefficient left right := by
        calc
          coherentProductBridgeCoefficient left right =
              0 + coherentProductBridgeCoefficient left right :=
            (Fraction.Field.zero_add _).symm
          _ < target + coherentProductBridgeCoefficient left right :=
            Fraction.Order.Arithmetic.add_lt_add_right_direct positive _
      exact Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        positive coefficientLt

/-- Actual stateful multiplication of two coherent names is operationally equivalent to their canonical equal-index
sampled product.

The comparison retains the original coherent operand processes and their canonical sample observations. Every positive
request is paid by the same computed finite indices and center-bound coefficient. -/
@[expose] public def coherentMul_toNamed (left right : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul left.name right.name)
      (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation left.name right.name).toNamed := by
  let leftProcess := left.name.process
  let rightProcess := right.name.process
  let process := leftProcess.mul rightProcess
  let start : process.State := (left.name.state, right.name.state)
  let product := Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation left.name right.name
  let bridge : Gaussian.Equivalence.Equivalent
      (Sampling.approximation
        (Named.mul
          left.name right.name)) product :=
    { compare := by
        intro leftStart rightStart target positive
        let semanticTarget := coherentProductBridgeTarget
          leftProcess rightProcess target
        have semanticPositive : 0 < semanticTarget :=
          coherentProductBridgeTarget_pos leftProcess rightProcess positive
        have semanticLtOne : semanticTarget < 1 :=
          coherentProductBridgeTarget_lt_one leftProcess rightProcess positive
        let leftThreshold := left.coherent.accuracyRequest semanticTarget
        let rightThreshold := right.coherent.accuracyRequest semanticTarget
        have leftThresholdPositive : 0 < leftThreshold :=
          left.coherent.accuracyRequest_pos semanticPositive
        have rightThresholdPositive : 0 < rightThreshold :=
          right.coherent.accuracyRequest_pos semanticPositive
        let inputThreshold :=
          Gaussian.Process.Coherence.Basic.Coherent.commonRequest
            leftThreshold rightThreshold
        have inputThresholdPositive : 0 < inputThreshold :=
          Gaussian.Process.Coherence.Basic.Coherent.commonRequest_pos
            leftThresholdPositive rightThresholdPositive
        let outputThreshold :=
          Gaussian.Process.Coherence.Basic.Coherent.commonRequest
            inputThreshold semanticTarget
        have outputThresholdPositive : 0 < outputThreshold :=
          Gaussian.Process.Coherence.Basic.Coherent.commonRequest_pos
            inputThresholdPositive semanticPositive
        let leftIndex := Search.firstQuarterBelow
          1 leftStart outputThreshold
        have leftIndexGe : leftStart ≤ leftIndex :=
          Search.firstQuarterBelow_ge
            1 leftStart outputThreshold
        have outputRequestSmall :
            Gaussian.Process.Sampling.refinementTarget leftIndex <
              outputThreshold :=
          Search.firstQuarterBelow_accurate
            1 (by decide) leftStart outputThreshold outputThresholdPositive
        have outputRequestLtInput :
            Gaussian.Process.Sampling.refinementTarget leftIndex <
              inputThreshold :=
          outputRequestSmall.trans
            (Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_left
              inputThresholdPositive semanticPositive)
        have outputRequestLtSemantic :
            Gaussian.Process.Sampling.refinementTarget leftIndex <
              semanticTarget :=
          outputRequestSmall.trans
            (Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_right
              inputThresholdPositive semanticPositive)
        have outputRequestLtLeft :
            Gaussian.Process.Sampling.refinementTarget leftIndex <
              leftThreshold :=
          outputRequestLtInput.trans
            (Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_left
              leftThresholdPositive rightThresholdPositive)
        have outputRequestLtRight :
            Gaussian.Process.Sampling.refinementTarget leftIndex <
              rightThreshold :=
          outputRequestLtInput.trans
            (Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_right
              leftThresholdPositive rightThresholdPositive)
        let rightIndex := Search.firstQuarterBelow
          1 rightStart inputThreshold
        have rightIndexGe : rightStart ≤ rightIndex :=
          Search.firstQuarterBelow_ge
            1 rightStart inputThreshold
        have rightRequestSmall :
            Gaussian.Process.Sampling.refinementTarget rightIndex <
              inputThreshold :=
          Search.firstQuarterBelow_accurate
            1 (by decide) rightStart inputThreshold inputThresholdPositive
        let baseState := Gaussian.Process.Sampling.stateAt
          process start leftIndex
        have componentSmall :
            left.coherent.allowance baseState.1 < semanticTarget ∧
              right.coherent.allowance baseState.2 < semanticTarget :=
          coherentProduct_stateAt_component_allowance_lt
            left.coherent right.coherent start leftIndex semanticTarget
              semanticPositive outputRequestLtLeft outputRequestLtRight
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := leftIndexGe
            right_ge := rightIndexGe
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have canonicalRequestSmall :
                  Gaussian.Process.Sampling.refinementTarget
                      rightLater < inputThreshold :=
                (quarterRadius_antitone (by decide)
                  rightOrder).trans_lt
                  rightRequestSmall
              have canonicalRequestLtLeft :
                  Gaussian.Process.Sampling.refinementTarget
                      rightLater < leftThreshold :=
                canonicalRequestSmall.trans
                  (Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_left
                    leftThresholdPositive rightThresholdPositive)
              have canonicalRequestLtRight :
                  Gaussian.Process.Sampling.refinementTarget
                      rightLater < rightThreshold :=
                canonicalRequestSmall.trans
                  (Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_right
                    leftThresholdPositive rightThresholdPositive)
              have canonicalLeftSmall :
                  left.coherent.allowance
                      (Gaussian.Process.Sampling.stateAt leftProcess
                        left.name.state rightLater) < semanticTarget :=
                Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt
                  left.coherent left.name.state
                    rightLater semanticTarget semanticPositive
                      canonicalRequestLtLeft
              have canonicalRightSmall :
                  right.coherent.allowance
                      (Gaussian.Process.Sampling.stateAt rightProcess
                        right.name.state rightLater) < semanticTarget :=
                Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt
                  right.coherent right.name.state
                    rightLater semanticTarget semanticPositive
                      canonicalRequestLtRight
              let leftReading := (leftProcess.witness baseState.1).val
              let rightReading := (rightProcess.witness baseState.2).val
              let canonicalLeft :=
                Gaussian.Process.Sampling.witnessAt leftProcess
                  left.name.state rightLater
              let canonicalRight :=
                Gaussian.Process.Sampling.witnessAt rightProcess
                  right.name.state rightLater
              have leftPossible :
                  leftProcess.Possible baseState.1 leftReading :=
                (leftProcess.witness baseState.1).property
              have rightPossible :
                  rightProcess.Possible baseState.2 rightReading :=
                (rightProcess.witness baseState.2).property
              have canonicalLeftPossible :
                  leftProcess.Possible
                      (Gaussian.Process.Sampling.stateAt leftProcess
                        left.name.state rightLater) canonicalLeft :=
                Gaussian.Process.Sampling.witnessAt_possible
                  leftProcess left.name.state rightLater
              have canonicalRightPossible :
                  rightProcess.Possible
                      (Gaussian.Process.Sampling.stateAt rightProcess
                        right.name.state rightLater) canonicalRight :=
                Gaussian.Process.Sampling.witnessAt_possible
                  rightProcess right.name.state rightLater
              have leftCloseRaw := left.coherent.possible_close
                leftPossible canonicalLeftPossible
              have rightCloseRaw := right.coherent.possible_close
                rightPossible canonicalRightPossible
              have leftClose : Data.Gaussian.Norm.Basic.normSq (leftReading - canonicalLeft) ≤
                  8 * semanticTarget := by
                calc
                  Data.Gaussian.Norm.Basic.normSq (leftReading - canonicalLeft) ≤
                    4 *
                      (left.coherent.allowance baseState.1 +
                        left.coherent.allowance
                          (Gaussian.Process.Sampling.stateAt
                            leftProcess left.name.state rightLater)) :=
                    leftCloseRaw
                  _ ≤ 4 * (semanticTarget + semanticTarget) :=
                    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                      (add_le_add componentSmall.1.le canonicalLeftSmall.le)
                      (by decide)
                  _ = 8 * semanticTarget := by ring1
              have rightClose : Data.Gaussian.Norm.Basic.normSq (rightReading - canonicalRight) ≤
                  8 * semanticTarget := by
                calc
                  Data.Gaussian.Norm.Basic.normSq (rightReading - canonicalRight) ≤
                    4 *
                      (right.coherent.allowance baseState.2 +
                        right.coherent.allowance
                          (Gaussian.Process.Sampling.stateAt
                            rightProcess right.name.state rightLater)) :=
                    rightCloseRaw
                  _ ≤ 4 * (semanticTarget + semanticTarget) :=
                    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                      (add_le_add componentSmall.2.le canonicalRightSmall.le)
                      (by decide)
                  _ = 8 * semanticTarget := by ring1
              let leftBound := 2 * (1 + leftProcess.centerBound)
              let rightBound := 2 * (1 + rightProcess.centerBound)
              have rightAllowanceBound :
                  right.coherent.allowance baseState.2 +
                      rightProcess.centerBound ≤
                    1 + rightProcess.centerBound := by
                calc
                  right.coherent.allowance baseState.2 +
                      rightProcess.centerBound =
                    rightProcess.centerBound +
                      right.coherent.allowance baseState.2 :=
                    _root_.add_comm _ _
                  _ ≤ rightProcess.centerBound + semanticTarget :=
                    add_le_add_right componentSmall.2.le _
                  _ ≤ rightProcess.centerBound + 1 :=
                    add_le_add_right semanticLtOne.le _
                  _ = 1 + rightProcess.centerBound :=
                    _root_.add_comm _ _
              have canonicalLeftAllowanceBound :
                  left.coherent.allowance
                      (Gaussian.Process.Sampling.stateAt leftProcess
                        left.name.state rightLater) + leftProcess.centerBound ≤
                    1 + leftProcess.centerBound := by
                calc
                  left.coherent.allowance
                        (Gaussian.Process.Sampling.stateAt leftProcess
                          left.name.state rightLater) + leftProcess.centerBound =
                    leftProcess.centerBound +
                      left.coherent.allowance
                        (Gaussian.Process.Sampling.stateAt leftProcess
                          left.name.state rightLater) :=
                    _root_.add_comm _ _
                  _ ≤ leftProcess.centerBound + semanticTarget :=
                    add_le_add_right canonicalLeftSmall.le _
                  _ ≤ leftProcess.centerBound + 1 :=
                    add_le_add_right semanticLtOne.le _
                  _ = 1 + leftProcess.centerBound :=
                    _root_.add_comm _ _
              have rightReadingNorm : Data.Gaussian.Norm.Basic.normSq rightReading ≤ rightBound :=
                (Gaussian.Process.Coherence.Basic.Coherent.possible_normSq_le
                  right.coherent rightPossible).trans
                    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                      rightAllowanceBound (by decide))
              have canonicalLeftNorm : Data.Gaussian.Norm.Basic.normSq canonicalLeft ≤ leftBound :=
                (Gaussian.Process.Coherence.Basic.Coherent.possible_normSq_le
                  left.coherent
                    canonicalLeftPossible).trans
                      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                          canonicalLeftAllowanceBound (by decide))
              have firstTerm :
                  Data.Gaussian.Norm.Basic.normSq ((leftReading - canonicalLeft) * rightReading) ≤
                    (8 * semanticTarget) * rightBound := by
                rw [Data.Gaussian.Norm.Basic.normSq_mul]
                exact Fraction.Order.Arithmetic.mul_le_mul_direct
                  leftClose rightReadingNorm (Data.Gaussian.Norm.Basic.normSq_nonneg _)
                  (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
                    semanticPositive.le)
              have secondTerm :
                  Data.Gaussian.Norm.Basic.normSq
                      (canonicalLeft * (rightReading - canonicalRight)) ≤
                    leftBound * (8 * semanticTarget) := by
                rw [Data.Gaussian.Norm.Basic.normSq_mul]
                exact Fraction.Order.Arithmetic.mul_le_mul_direct
                  canonicalLeftNorm rightClose (Data.Gaussian.Norm.Basic.normSq_nonneg _)
                  (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
                    (add_nonneg (by decide) leftProcess.centerBound_nonneg))
              have productIdentity :
                  leftReading * rightReading -
                      canonicalLeft * canonicalRight =
                    (leftReading - canonicalLeft) * rightReading +
                      canonicalLeft * (rightReading - canonicalRight) := by
                apply Data.Gaussian.Basic.ext <;>
                  simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                    Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
                    Purelib.Data.Gaussian.Basic.mul_re, Purelib.Data.Gaussian.Basic.mul_im] <;>
                    ring1
              have productBound :
                  Data.Gaussian.Norm.Basic.normSq
                      (leftReading * rightReading -
                        canonicalLeft * canonicalRight) ≤
                    16 * semanticTarget * (leftBound + rightBound) := by
                rw [productIdentity]
                calc
                  Data.Gaussian.Norm.Basic.normSq
                      ((leftReading - canonicalLeft) * rightReading +
                        canonicalLeft * (rightReading - canonicalRight)) ≤
                    2 *
                      (Data.Gaussian.Norm.Basic.normSq
                          ((leftReading - canonicalLeft) * rightReading) +
                        Data.Gaussian.Norm.Basic.normSq
                          (canonicalLeft *
                            (rightReading - canonicalRight))) :=
                    Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
                  _ ≤ 2 *
                      ((8 * semanticTarget) * rightBound +
                        leftBound * (8 * semanticTarget)) :=
                    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                      (add_le_add firstTerm secondTerm) (by decide)
                  _ = 16 * semanticTarget * (leftBound + rightBound) := by
                    ring1
              have actualTail :
                  Data.Gaussian.Norm.Basic.normSq
                      (Gaussian.Process.Sampling.witnessAt process
                          start leftLater -
                        Gaussian.Process.Sampling.witnessAt process
                          start leftIndex) ≤
                    4 * Gaussian.Process.Sampling.refinementTarget
                      leftIndex := by
                rw [← Gaussian.Sampling.Dyadic.quarterRadius_four_eq_four_refinementTarget]
                exact Gaussian.Process.Sampling.witnessAt_later_close
                  process start leftOrder
              have baseWitness :
                  Gaussian.Process.Sampling.witnessAt process
                      start leftIndex = leftReading * rightReading :=
                rfl
              have canonicalLeftSample :
                  (Sampling.approximation left.name).sample
                      rightLater = canonicalLeft :=
                rfl
              have canonicalRightSample :
                  (Sampling.approximation right.name).sample
                      rightLater = canonicalRight :=
                rfl
              change Data.Gaussian.Norm.Basic.normSq
                  (Gaussian.Process.Sampling.witnessAt process
                      start leftLater - product.sample rightLater) < target
              rw [Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation_sample,
                canonicalLeftSample, canonicalRightSample]
              calc
                Data.Gaussian.Norm.Basic.normSq
                    (Gaussian.Process.Sampling.witnessAt process
                        start leftLater - canonicalLeft * canonicalRight) ≤
                  2 *
                    (Data.Gaussian.Norm.Basic.normSq
                        (Gaussian.Process.Sampling.witnessAt process
                            start leftLater -
                          Gaussian.Process.Sampling.witnessAt process
                            start leftIndex) +
                      Data.Gaussian.Norm.Basic.normSq
                        (Gaussian.Process.Sampling.witnessAt process
                            start leftIndex -
                          canonicalLeft * canonicalRight)) :=
                    Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
                _ ≤ 2 *
                    (4 *
                        Gaussian.Process.Sampling.refinementTarget
                          leftIndex +
                      16 * semanticTarget * (leftBound + rightBound)) := by
                  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                  · apply add_le_add actualTail
                    rw [baseWitness]
                    exact productBound
                  · decide
                _ ≤ 2 *
                    (4 * semanticTarget +
                      16 * semanticTarget * (leftBound + rightBound)) :=
                  Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                    (add_le_add
                      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                          outputRequestLtSemantic.le (by decide)) le_rfl)
                    (by decide)
                _ = semanticTarget *
                    coherentProductBridgeCoefficient
                      leftProcess rightProcess := by
                  dsimp only [leftBound, rightBound]
                  unfold coherentProductBridgeCoefficient
                  ring1
                _ < target :=
                  coherentProductBridgeTarget_budget_lt
                    leftProcess rightProcess positive } }
  exact Equivalent.trans bridge
    (Equivalent.symm
      (Equivalent.toNamed_sampling
        product))

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
