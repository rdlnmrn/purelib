module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
public import Purelib.Approximation.Gaussian.Name.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
public import Purelib.Approximation.Gaussian.Process.Coherence.Addition
public import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
public import Purelib.Approximation.Gaussian.Sampling.Dyadic
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Bounds.Fraction
public import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Addition
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Process.Coherence.Basic
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

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

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat

/-- Actual stateful addition of two coherent names is operationally equivalent to their canonical equal-index sampled
sum. -/
@[expose] public def coherentAdd_toSampled (left right : CoherentNamed) :
    Equivalent
      (Sampling.approximation (Named.add left.name right.name))
      (Sequence.Arithmetic.Sum.sampledSumApproximation left.name right.name) := by
  let leftProcess := left.name.process
  let rightProcess := right.name.process
  let process := leftProcess.add rightProcess
  let start : process.State := (left.name.state, right.name.state)
  let coherent := Coherent.add
    left.coherent right.coherent
  let sum := Sequence.Arithmetic.Sum.sampledSumApproximation left.name right.name
  let bridge : Equivalent
      (Sampling.approximation
        (Named.add
          left.name right.name)) sum :=
    { compare := by
        intro leftStart rightStart target positive
        let semanticTarget := target / 32
        have semanticPositive : 0 < semanticTarget :=
          Field.div_pos_direct positive
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 32) (by decide))
        let componentTarget := semanticTarget / 4
        have componentPositive : 0 < componentTarget :=
          Field.div_pos_direct semanticPositive
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 4) (by decide))
        let actualThreshold := coherent.accuracyRequest semanticTarget
        let leftThreshold := left.coherent.accuracyRequest componentTarget
        let rightThreshold := right.coherent.accuracyRequest componentTarget
        have actualThresholdPositive : 0 < actualThreshold :=
          coherent.accuracyRequest_pos semanticPositive
        have leftThresholdPositive : 0 < leftThreshold :=
          left.coherent.accuracyRequest_pos componentPositive
        have rightThresholdPositive : 0 < rightThreshold :=
          right.coherent.accuracyRequest_pos componentPositive
        let componentThreshold :=
          Coherent.commonRequest
            leftThreshold rightThreshold
        have componentThresholdPositive : 0 < componentThreshold :=
          Coherent.commonRequest_pos
            leftThresholdPositive rightThresholdPositive
        let inputThreshold :=
          Coherent.commonRequest
            actualThreshold componentThreshold
        have inputThresholdPositive : 0 < inputThreshold :=
          Coherent.commonRequest_pos
            actualThresholdPositive componentThresholdPositive
        let outputThreshold :=
          Coherent.commonRequest
            inputThreshold semanticTarget
        have outputThresholdPositive : 0 < outputThreshold :=
          Coherent.commonRequest_pos
            inputThresholdPositive semanticPositive
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
        have outputRequestLtInput :
            Process.Sampling.refinementTarget leftIndex <
              inputThreshold :=
          outputRequestSmall.trans
            (Coherent.commonRequest_lt_left
              inputThresholdPositive semanticPositive)
        have outputRequestLtActual :
            Process.Sampling.refinementTarget leftIndex <
              actualThreshold :=
          outputRequestLtInput.trans
            (Coherent.commonRequest_lt_left
              actualThresholdPositive componentThresholdPositive)
        have outputRequestLtSemantic :
            Process.Sampling.refinementTarget leftIndex <
              semanticTarget :=
          outputRequestSmall.trans
            (Coherent.commonRequest_lt_right
              inputThresholdPositive semanticPositive)
        let rightIndex := Search.firstQuarterBelow
          1 rightStart componentThreshold
        have rightIndexGe : rightStart ≤ rightIndex :=
          Search.firstQuarterBelow_ge
            1 rightStart componentThreshold
        have rightRequestSmall :
            Process.Sampling.refinementTarget rightIndex <
              componentThreshold :=
          Search.firstQuarterBelow_accurate
            1 (by decide) rightStart componentThreshold
              componentThresholdPositive
        let baseState := Process.Sampling.stateAt
          process start leftIndex
        have baseAllowanceSmall :
            coherent.allowance baseState < semanticTarget :=
          Coherent.stateAt_allowance_lt
            coherent start leftIndex semanticTarget semanticPositive
              outputRequestLtActual
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := leftIndexGe
            right_ge := rightIndexGe
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have canonicalRequestSmall :
                  Process.Sampling.refinementTarget
                      rightLater < componentThreshold :=
                (quarterRadius_antitone (by decide)
                  rightOrder).trans_lt
                  rightRequestSmall
              have canonicalRequestLtLeft :
                  Process.Sampling.refinementTarget
                      rightLater < leftThreshold :=
                canonicalRequestSmall.trans
                  (Coherent.commonRequest_lt_left
                    leftThresholdPositive rightThresholdPositive)
              have canonicalRequestLtRight :
                  Process.Sampling.refinementTarget
                      rightLater < rightThreshold :=
                canonicalRequestSmall.trans
                  (Coherent.commonRequest_lt_right
                    leftThresholdPositive rightThresholdPositive)
              let canonicalLeftState :=
                Process.Sampling.stateAt leftProcess
                  left.name.state rightLater
              let canonicalRightState :=
                Process.Sampling.stateAt rightProcess
                  right.name.state rightLater
              have canonicalLeftSmall :
                  left.coherent.allowance canonicalLeftState < componentTarget :=
                Coherent.stateAt_allowance_lt
                  left.coherent left.name.state rightLater componentTarget
                    componentPositive canonicalRequestLtLeft
              have canonicalRightSmall :
                  right.coherent.allowance canonicalRightState < componentTarget :=
                Coherent.stateAt_allowance_lt
                  right.coherent right.name.state rightLater componentTarget
                    componentPositive canonicalRequestLtRight
              have canonicalAllowanceSmall :
                  coherent.allowance
                      (canonicalLeftState, canonicalRightState) <
                    semanticTarget := by
                change 2 *
                    (left.coherent.allowance canonicalLeftState +
                      right.coherent.allowance canonicalRightState) <
                  semanticTarget
                calc
                  2 *
                      (left.coherent.allowance canonicalLeftState +
                        right.coherent.allowance canonicalRightState) <
                    2 * (componentTarget + componentTarget) :=
                    Arithmetic.mul_lt_mul_of_pos_left_direct
                      (by decide)
                      (Arithmetic.add_lt_add_direct
                        canonicalLeftSmall canonicalRightSmall)
                  _ = semanticTarget := by
                    dsimp only [componentTarget]
                    calc
                      2 * (semanticTarget / 4 + semanticTarget / 4) = 4 * (semanticTarget / 4) := by ring1
                      _ = semanticTarget := Fraction.Compatibility.four_mul_quarter_scale semanticTarget
              let baseReading := (process.witness baseState).val
              let canonicalLeft :=
                Process.Sampling.witnessAt leftProcess
                  left.name.state rightLater
              let canonicalRight :=
                Process.Sampling.witnessAt rightProcess
                  right.name.state rightLater
              have basePossible : process.Possible baseState baseReading :=
                (process.witness baseState).property
              have canonicalLeftPossible :
                  leftProcess.Possible canonicalLeftState canonicalLeft :=
                Process.Sampling.witnessAt_possible
                  leftProcess left.name.state rightLater
              have canonicalRightPossible :
                  rightProcess.Possible canonicalRightState canonicalRight :=
                Process.Sampling.witnessAt_possible
                  rightProcess right.name.state rightLater
              have canonicalPossible :
                  process.Possible (canonicalLeftState, canonicalRightState)
                    (canonicalLeft + canonicalRight) :=
                ⟨canonicalLeft, canonicalRight, canonicalLeftPossible,
                  canonicalRightPossible, rfl⟩
              have baseCanonicalRaw := coherent.possible_close
                basePossible canonicalPossible
              have baseCanonical :
                  Basic.normSq (baseReading - (canonicalLeft + canonicalRight)) <
                    8 * semanticTarget := by
                calc
                  Basic.normSq (baseReading - (canonicalLeft + canonicalRight)) ≤
                    4 *
                      (coherent.allowance baseState +
                        coherent.allowance
                          (canonicalLeftState, canonicalRightState)) :=
                    baseCanonicalRaw
                  _ < 4 * (semanticTarget + semanticTarget) :=
                    Arithmetic.mul_lt_mul_of_pos_left_direct
                      (by decide)
                      (Arithmetic.add_lt_add_direct
                        baseAllowanceSmall canonicalAllowanceSmall)
                  _ = 8 * semanticTarget := by ring1
              have actualTail :
                  Basic.normSq
                      (Process.Sampling.witnessAt process
                          start leftLater -
                        Process.Sampling.witnessAt process
                          start leftIndex) <
                    4 * semanticTarget := by
                calc
                  Basic.normSq
                      (Process.Sampling.witnessAt process
                          start leftLater -
                        Process.Sampling.witnessAt process
                          start leftIndex) ≤
                    4 * Process.Sampling.refinementTarget
                      leftIndex := by
                    rw [← Sampling.Dyadic.quarterRadius_four_eq_four_refinementTarget]
                    exact
                      Process.Sampling.witnessAt_later_close
                        process start leftOrder
                  _ < 4 * semanticTarget :=
                    Arithmetic.mul_lt_mul_of_pos_left_direct
                      (by decide) outputRequestLtSemantic
              have baseWitness :
                  Process.Sampling.witnessAt process
                      start leftIndex = baseReading :=
                rfl
              change Basic.normSq
                  (Process.Sampling.witnessAt process
                      start leftLater - sum.sample rightLater) < target
              rw [Sequence.Arithmetic.Sum.sampledSumApproximation_sample]
              calc
                Basic.normSq
                    (Process.Sampling.witnessAt process
                        start leftLater - (canonicalLeft + canonicalRight)) ≤
                  2 *
                    (Basic.normSq
                        (Process.Sampling.witnessAt process
                            start leftLater -
                          Process.Sampling.witnessAt process
                            start leftIndex) +
                      Basic.normSq
                        (Process.Sampling.witnessAt process
                            start leftIndex -
                          (canonicalLeft + canonicalRight))) :=
                    Bounds.normSq_sub_le_via _ _ _
                _ < 2 *
                    (4 * semanticTarget + 8 * semanticTarget) :=
                  Arithmetic.mul_lt_mul_of_pos_left_direct
                    (by decide)
                    (Arithmetic.add_lt_add_direct actualTail
                      (by rw [baseWitness]; exact baseCanonical))
                _ = 24 * semanticTarget := by ring1
                _ < target := by
                  dsimp only [semanticTarget]
                  exact Bounds.Fraction.twenty_four_thirty_seconds_lt positive } }
  exact bridge

/-- Compare the original coherent sum to the productive name of its same retained canonical sampler. -/
@[expose] public def coherentAdd_toNamed (left right : CoherentNamed) :
    NamedEquivalent
      (Named.add left.name right.name)
      (Sequence.Arithmetic.Sum.sampledSumApproximation left.name right.name).toNamed :=
  Equivalent.trans (coherentAdd_toSampled left right)
    (Equivalent.symm (Equivalent.toNamed_sampling
      (Sequence.Arithmetic.Sum.sampledSumApproximation left.name right.name)))
end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge

end
