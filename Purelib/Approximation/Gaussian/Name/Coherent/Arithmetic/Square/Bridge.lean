module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Approximation.Gaussian.Request.Multiplication
import Purelib.Approximation.Gaussian.Sampling.Dyadic
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square
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
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Gaussian.Norm
open Purelib.Approximation.Gaussian.Process.Coherence.Basic

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Square.Bridge

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Request.Basic
open Purelib.Approximation.Gaussian.Sequence.Arithmetic
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat

section
public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

/-- A sufficiently small positive self-product refinement request makes both retained component allowances smaller than
the positive target. -/
private theorem coherentMul_refine_component_allowance_lt
    {process : Process} (coherent : Coherent process)
    (state : process.State × process.State)
    (request : Fraction.Rational) (requestPositive : 0 < request)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (requestSmall : request < coherent.accuracyRequest target) :
    let refined := (process.mul process).refine
      state request requestPositive
    coherent.allowance refined.1 < target ∧
      coherent.allowance refined.2 < target := by
  let leftName := Name.centerOnly
    (process.ball state.1).center process.centerBound
      process.centerBound_nonneg (process.center_bounded state.1)
  let rightName := Name.centerOnly
    (process.ball state.2).center process.centerBound
      process.centerBound_nonneg (process.center_bounded state.2)
  let inputRequest :=
    Name.multiplicativeInputTarget
      leftName rightName request
  have inputPositive : 0 < inputRequest :=
    Name.multiplicativeInputTarget_pos
      leftName rightName requestPositive
  have inputLtRequest : inputRequest < request :=
    Coherent.processMultiplicativeInputTarget_lt_target
      leftName rightName requestPositive
  have inputSmall : inputRequest < coherent.accuracyRequest target :=
    inputLtRequest.trans requestSmall
  change coherent.allowance
        (process.refine state.1 inputRequest inputPositive) < target ∧
      coherent.allowance
        (process.refine state.2 inputRequest inputPositive) < target
  exact ⟨coherent.refine_accurate state.1 target targetPositive
      inputRequest inputPositive inputSmall,
    coherent.refine_accurate state.2 target targetPositive
      inputRequest inputPositive inputSmall⟩

/-- A canonical self-product sample satisfying the original coherence request bound has both component allowances below
the positive target. -/
public theorem coherentMul_stateAt_component_allowance_lt
    {process : Process} (coherent : Coherent process)
    (start : process.State × process.State) (index : Nat)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (requestSmall :
      Process.Sampling.refinementTarget index <
        coherent.accuracyRequest target) :
    let state := Process.Sampling.stateAt
      (process.mul process) start index
    coherent.allowance state.1 < target ∧
      coherent.allowance state.2 < target := by
  cases index with
  | zero =>
      exact coherentMul_refine_component_allowance_lt
        coherent start _ _
        target targetPositive requestSmall
  | succ index =>
      exact coherentMul_refine_component_allowance_lt
        coherent
        (Process.Sampling.stateAt
          (process.mul process) start index) _ _ target targetPositive
            requestSmall

/-- The positive rational square-comparison coefficient determined by the original process center bound. -/
@[expose] def coherentSquareBridgeCoefficient (process : Process) : Fraction.Rational :=
  8 + 4 * (4 * (8 * (1 + process.centerBound)))

/-- The retained square-comparison coefficient is strictly positive. -/
theorem coherentSquareBridgeCoefficient_pos (process : Process) :
    0 < coherentSquareBridgeCoefficient process :=
      by
  unfold coherentSquareBridgeCoefficient
  exact Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
    (Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.mul_nonneg_direct (by decide)
        (Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg (by decide) process.centerBound_nonneg))))

/-- Divide the requested square tolerance by its sum with the retained square-comparison coefficient. -/
@[expose] def coherentSquareBridgeTarget (process : Process) (target : Fraction.Rational) :
    Fraction.Rational :=
  target / (target + coherentSquareBridgeCoefficient
    process)

/-- The operand square-comparison tolerance is positive for a positive output target. -/
theorem coherentSquareBridgeTarget_pos (process : Process)
    {target : Fraction.Rational} (positive : 0 < target) :
    0 < coherentSquareBridgeTarget process target :=
  Field.div_pos_direct positive
    (Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (coherentSquareBridgeCoefficient_pos process).le)

/-- The operand square-comparison tolerance is below one for a positive output target. -/
theorem coherentSquareBridgeTarget_lt_one (process : Process)
    {target : Fraction.Rational} (positive : 0 < target) :
    coherentSquareBridgeTarget process target < 1 := by
  apply (Field.div_lt_iff_pos
    (Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (coherentSquareBridgeCoefficient_pos process).le)).2
  calc
    target = 0 + target :=
      (Fraction.Field.zero_add target).symm
    _ < coherentSquareBridgeCoefficient process + target
      :=
      Arithmetic.add_lt_add_right_direct
        (coherentSquareBridgeCoefficient_pos process)
          target
    _ = target + coherentSquareBridgeCoefficient process
      :=
      _root_.add_comm _ _
    _ = 1 * (target + coherentSquareBridgeCoefficient
      process) :=
      (Fraction.Field.one_mul _).symm

/-- Scaling the operand tolerance by the square-comparison coefficient stays strictly below the positive output target.
-/
theorem coherentSquareBridgeTarget_budget_lt (process : Process)
    {target : Fraction.Rational} (positive : 0 < target) :
    coherentSquareBridgeTarget process target *
        coherentSquareBridgeCoefficient process < target
          := by
  have denominatorPositive :
      0 < target + coherentSquareBridgeCoefficient process
        :=
    Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (coherentSquareBridgeCoefficient_pos process).le
  change target /
      (target + coherentSquareBridgeCoefficient process) *
        coherentSquareBridgeCoefficient process < target
  calc
    target / (target + coherentSquareBridgeCoefficient
      process) *
        coherentSquareBridgeCoefficient process =
      (target * coherentSquareBridgeCoefficient process) /
        (target + coherentSquareBridgeCoefficient process)
          := by
      change (target *
          (target + coherentSquareBridgeCoefficient
            process)⁻¹) *
            coherentSquareBridgeCoefficient process =
        (target * coherentSquareBridgeCoefficient process)
          *
          (target + coherentSquareBridgeCoefficient
            process)⁻¹
      calc
        (target *
            (target + coherentSquareBridgeCoefficient
              process)⁻¹) *
              coherentSquareBridgeCoefficient process =
          target *
            ((target + coherentSquareBridgeCoefficient
              process)⁻¹ *
              coherentSquareBridgeCoefficient process) :=
            _root_.mul_assoc _ _ _
        _ = target *
            (coherentSquareBridgeCoefficient process *
              (target + coherentSquareBridgeCoefficient
                process)⁻¹) := by
          rw [Fraction.Field.mul_comm
            (target + coherentSquareBridgeCoefficient
              process)⁻¹]
        _ = (target * coherentSquareBridgeCoefficient
          process) *
            (target + coherentSquareBridgeCoefficient
              process)⁻¹ :=
          (_root_.mul_assoc _ _ _).symm
    _ < target := by
      apply (Field.div_lt_iff_pos
        denominatorPositive).2
      have coefficientLt : coherentSquareBridgeCoefficient
        process <
          target + coherentSquareBridgeCoefficient process
            := by
        calc
          coherentSquareBridgeCoefficient process =
              0 + coherentSquareBridgeCoefficient process
                :=
            (Fraction.Field.zero_add _).symm
          _ < target + coherentSquareBridgeCoefficient
            process :=
            Arithmetic.add_lt_add_right_direct positive _
      exact Arithmetic.mul_lt_mul_of_pos_left_direct
        positive coefficientLt

/-- Actual stateful self-multiplication of a coherent CCL name is operationally equivalent to the canonical pointwise
square of its finite sampling approximation. -/
@[expose] def coherentSquare_toNamed (value : CoherentNamed) :
    NamedEquivalent
      (Named.mul value.name value.name)
      (Square.squareApproximation
        (Sampling.approximation value.name)).toNamed := by
  let process := value.name.process
  let start : process.State × process.State :=
    (value.name.state, value.name.state)
  let source := Sampling.approximation value.name
  let squared := Square.squareApproximation source
  let bridge : Equivalent
      (Sampling.approximation
        (Named.mul
          value.name value.name)) squared :=
    { compare := by
        intro leftStart rightStart target positive
        let semanticTarget := coherentSquareBridgeTarget
          process target
        have semanticPositive : 0 < semanticTarget :=
          coherentSquareBridgeTarget_pos process positive
        have semanticLtOne : semanticTarget < 1 :=
          coherentSquareBridgeTarget_lt_one process
            positive
        let processThreshold := value.coherent.accuracyRequest semanticTarget
        have processThresholdPositive : 0 < processThreshold :=
          value.coherent.accuracyRequest_pos semanticPositive
        let outputThreshold :=
          Coherent.commonRequest
            processThreshold semanticTarget
        have outputThresholdPositive : 0 < outputThreshold :=
          Coherent.commonRequest_pos
            processThresholdPositive semanticPositive
        let leftIndex := Search.firstQuarterBelow
          1 leftStart outputThreshold
        have leftIndexGe : leftStart ≤ leftIndex :=
          Search.firstQuarterBelow_ge
            1 leftStart outputThreshold
        have outputRequestSmall :
            Process.Sampling.refinementTarget leftIndex <
              outputThreshold :=
          Search.firstQuarterBelow_accurate
            1 (by decide) leftStart outputThreshold outputThresholdPositive
        have outputRequestLtProcess :
            Process.Sampling.refinementTarget leftIndex <
              processThreshold :=
          outputRequestSmall.trans
            (Coherent.commonRequest_lt_left
              processThresholdPositive semanticPositive)
        have outputRequestLtSemantic :
            Process.Sampling.refinementTarget leftIndex <
              semanticTarget :=
          outputRequestSmall.trans
            (Coherent.commonRequest_lt_right
              processThresholdPositive semanticPositive)
        let rightIndex := Search.firstQuarterBelow
          1 rightStart processThreshold
        have rightIndexGe : rightStart ≤ rightIndex :=
          Search.firstQuarterBelow_ge
            1 rightStart processThreshold
        have rightRequestSmall :
            Process.Sampling.refinementTarget rightIndex <
              processThreshold :=
          Search.firstQuarterBelow_accurate
            1 (by decide) rightStart processThreshold processThresholdPositive
        let baseState := Process.Sampling.stateAt
          (process.mul process) start leftIndex
        have componentSmall :
            value.coherent.allowance baseState.1 < semanticTarget ∧
              value.coherent.allowance baseState.2 < semanticTarget :=

            coherentMul_stateAt_component_allowance_lt
            value.coherent start
            leftIndex semanticTarget semanticPositive outputRequestLtProcess
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := leftIndexGe
            right_ge := rightIndexGe
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have canonicalRequestSmall :
                  Process.Sampling.refinementTarget
                      rightLater < processThreshold :=
                (quarterRadius_antitone (by decide)
                  rightOrder).trans_lt
                  rightRequestSmall
              have canonicalAllowanceSmall :
                  value.coherent.allowance
                      (Process.Sampling.stateAt process
                        value.name.state rightLater) < semanticTarget :=
                Coherent.stateAt_allowance_lt
                  value.coherent value.name.state rightLater semanticTarget
                    semanticPositive canonicalRequestSmall
              let leftReading := (process.witness baseState.1).val
              let rightReading := (process.witness baseState.2).val
              let canonicalReading :=
                Process.Sampling.witnessAt process
                  value.name.state rightLater
              have leftPossible : process.Possible baseState.1 leftReading :=
                (process.witness baseState.1).property
              have rightPossible : process.Possible baseState.2 rightReading :=
                (process.witness baseState.2).property
              have canonicalPossible :
                  process.Possible
                      (Process.Sampling.stateAt process
                        value.name.state rightLater) canonicalReading :=
                Process.Sampling.witnessAt_possible
                  process value.name.state rightLater
              have leftCloseRaw := value.coherent.possible_close
                leftPossible canonicalPossible
              have rightCloseRaw := value.coherent.possible_close
                rightPossible canonicalPossible
              have allowanceSumLeft :
                  value.coherent.allowance baseState.1 +
                      value.coherent.allowance
                        (Process.Sampling.stateAt process
                          value.name.state rightLater) <
                    semanticTarget + semanticTarget :=
                Arithmetic.add_lt_add_direct
                  componentSmall.1 canonicalAllowanceSmall
              have allowanceSumRight :
                  value.coherent.allowance baseState.2 +
                      value.coherent.allowance
                        (Process.Sampling.stateAt process
                          value.name.state rightLater) <
                    semanticTarget + semanticTarget :=
                Arithmetic.add_lt_add_direct
                  componentSmall.2 canonicalAllowanceSmall
              have leftClose : Basic.normSq (leftReading - canonicalReading) ≤
                  8 * semanticTarget := by
                calc
                  Basic.normSq (leftReading - canonicalReading) ≤
                    4 *
                      (value.coherent.allowance baseState.1 +
                        value.coherent.allowance
                          (Process.Sampling.stateAt process
                            value.name.state rightLater)) := leftCloseRaw
                  _ ≤ 4 * (semanticTarget + semanticTarget) :=
                    Arithmetic.mul_le_mul_of_nonneg_left_direct
                      allowanceSumLeft.le (by decide)
                  _ = 8 * semanticTarget := by ring1
              have rightClose : Basic.normSq (rightReading - canonicalReading) ≤
                  8 * semanticTarget := by
                calc
                  Basic.normSq (rightReading - canonicalReading) ≤
                    4 *
                      (value.coherent.allowance baseState.2 +
                        value.coherent.allowance
                          (Process.Sampling.stateAt process
                            value.name.state rightLater)) := rightCloseRaw
                  _ ≤ 4 * (semanticTarget + semanticTarget) :=
                    Arithmetic.mul_le_mul_of_nonneg_left_direct
                      allowanceSumRight.le (by decide)
                  _ = 8 * semanticTarget := by ring1
              let readingBound := 2 * (1 + process.centerBound)
              have rightAllowanceBound :
                  value.coherent.allowance baseState.2 + process.centerBound ≤
                    1 + process.centerBound := by
                calc
                  value.coherent.allowance baseState.2 + process.centerBound =
                      process.centerBound +
                        value.coherent.allowance baseState.2 :=
                    _root_.add_comm _ _
                  _ ≤ process.centerBound + semanticTarget :=
                    add_le_add_right componentSmall.2.le process.centerBound
                  _ ≤ process.centerBound + 1 :=
                    add_le_add_right semanticLtOne.le process.centerBound
                  _ = 1 + process.centerBound :=
                    _root_.add_comm _ _
              have canonicalAllowanceBound :
                  value.coherent.allowance
                      (Process.Sampling.stateAt process
                        value.name.state rightLater) + process.centerBound ≤
                    1 + process.centerBound := by
                calc
                  value.coherent.allowance
                        (Process.Sampling.stateAt process
                          value.name.state rightLater) + process.centerBound =
                      process.centerBound +
                        value.coherent.allowance
                          (Process.Sampling.stateAt process
                            value.name.state rightLater) :=
                    _root_.add_comm _ _
                  _ ≤ process.centerBound + semanticTarget :=
                    add_le_add_right canonicalAllowanceSmall.le
                      process.centerBound
                  _ ≤ process.centerBound + 1 :=
                    add_le_add_right semanticLtOne.le process.centerBound
                  _ = 1 + process.centerBound :=
                    _root_.add_comm _ _
              have rightReadingNorm : Basic.normSq rightReading ≤ readingBound :=
                (Coherent.possible_normSq_le
                  value.coherent rightPossible).trans
                    (Arithmetic.mul_le_mul_of_nonneg_left_direct
                      rightAllowanceBound (by decide))
              have canonicalReadingNorm :
                  Basic.normSq canonicalReading ≤ readingBound :=
                (Coherent.possible_normSq_le
                  value.coherent canonicalPossible).trans
                    (Arithmetic.mul_le_mul_of_nonneg_left_direct
                      canonicalAllowanceBound (by decide))
              have firstTerm :
                  Basic.normSq
                      ((leftReading - canonicalReading) * rightReading) ≤
                    (8 * semanticTarget) * readingBound := by
                rw [Basic.normSq_mul]
                exact Arithmetic.mul_le_mul_direct
                  leftClose rightReadingNorm (Basic.normSq_nonneg _)
                  (Arithmetic.mul_nonneg_direct (by decide)
                    semanticPositive.le)
              have secondTerm :
                  Basic.normSq
                      (canonicalReading *
                        (rightReading - canonicalReading)) ≤
                    readingBound * (8 * semanticTarget) := by
                rw [Basic.normSq_mul]
                exact Arithmetic.mul_le_mul_direct
                  canonicalReadingNorm rightClose (Basic.normSq_nonneg _)
                  (Arithmetic.mul_nonneg_direct (by decide)
                    (add_nonneg (by decide) process.centerBound_nonneg))
              have productIdentity :
                  leftReading * rightReading -
                      canonicalReading * canonicalReading =
                    (leftReading - canonicalReading) * rightReading +
                      canonicalReading *
                        (rightReading - canonicalReading) := by
                apply Data.Gaussian.Basic.ext <;>
                  simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
                    Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
                    Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;>
                    ring1
              have productBound :
                  Basic.normSq
                      (leftReading * rightReading -
                        canonicalReading * canonicalReading) ≤
                    32 * semanticTarget * readingBound := by
                rw [productIdentity]
                calc
                  Basic.normSq
                      ((leftReading - canonicalReading) * rightReading +
                        canonicalReading *
                          (rightReading - canonicalReading)) ≤
                    2 *
                      (Basic.normSq
                          ((leftReading - canonicalReading) * rightReading) +
                        Basic.normSq
                          (canonicalReading *
                            (rightReading - canonicalReading))) :=
                    Bounds.normSq_add_le_two _ _
                  _ ≤ 2 *
                      ((8 * semanticTarget) * readingBound +
                        readingBound * (8 * semanticTarget)) :=
                    Arithmetic.mul_le_mul_of_nonneg_left_direct
                      (add_le_add firstTerm secondTerm) (by decide)
                  _ = 32 * semanticTarget * readingBound := by ring1
              have actualTail :
                  Basic.normSq
                      (Process.Sampling.witnessAt
                          (process.mul process) start leftLater -
                        Process.Sampling.witnessAt
                          (process.mul process) start leftIndex) ≤
                    4 * Process.Sampling.refinementTarget
                      leftIndex := by
                rw [← Sampling.Dyadic.quarterRadius_four_eq_four_refinementTarget]
                exact Process.Sampling.witnessAt_later_close
                  (process.mul process) start leftOrder
              have baseWitness :
                  Process.Sampling.witnessAt
                      (process.mul process) start leftIndex =
                    leftReading * rightReading :=
                rfl
              have canonicalSample : source.sample rightLater =
                  canonicalReading :=
                rfl
              change Basic.normSq
                  (Process.Sampling.witnessAt
                      (process.mul process) start leftLater -
                    source.sample rightLater * source.sample rightLater) < target
              rw [canonicalSample]
              calc
                Basic.normSq
                    (Process.Sampling.witnessAt
                        (process.mul process) start leftLater -
                      canonicalReading * canonicalReading) ≤
                  2 *
                    (Basic.normSq
                        (Process.Sampling.witnessAt
                            (process.mul process) start leftLater -
                          Process.Sampling.witnessAt
                            (process.mul process) start leftIndex) +
                      Basic.normSq
                        (Process.Sampling.witnessAt
                            (process.mul process) start leftIndex -
                          canonicalReading * canonicalReading)) :=
                    Bounds.normSq_sub_le_via _ _ _
                _ ≤ 2 *
                    (4 *
                        Process.Sampling.refinementTarget
                          leftIndex +
                      32 * semanticTarget * readingBound) := by
                  apply Arithmetic.mul_le_mul_of_nonneg_left_direct
                  · apply add_le_add actualTail
                    rw [baseWitness]
                    exact productBound
                  · decide
                _ ≤ 2 *
                    (4 * semanticTarget +
                      32 * semanticTarget * readingBound) :=
                  Arithmetic.mul_le_mul_of_nonneg_left_direct
                    (add_le_add
                      (Arithmetic.mul_le_mul_of_nonneg_left_direct
                        outputRequestLtSemantic.le (by decide)) le_rfl)
                    (by decide)
                _ = semanticTarget *
                  coherentSquareBridgeCoefficient
                  process := by
                  dsimp only [readingBound]
                  unfold
                    coherentSquareBridgeCoefficient
                  ring1
                _ < target :=
                  coherentSquareBridgeTarget_budget_lt
                    process positive } }
  exact Equivalent.trans bridge
    (Equivalent.symm
      (Equivalent.toNamed_sampling
        squared))

end

end

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Square.Bridge
