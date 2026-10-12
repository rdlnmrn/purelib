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
@[expose] public def coherentAdd_toNamed (left right : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add left.name right.name)
      (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation left.name right.name).toNamed := by
  let leftProcess := left.name.process
  let rightProcess := right.name.process
  let process := leftProcess.add rightProcess
  let start : process.State := (left.name.state, right.name.state)
  let coherent := Gaussian.Process.Coherence.Basic.Coherent.add
    left.coherent right.coherent
  let sum := Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation left.name right.name
  let bridge : Gaussian.Equivalence.Equivalent
      (Sampling.approximation
        (Named.add
          left.name right.name)) sum :=
    { compare := by
        intro leftStart rightStart target positive
        let semanticTarget := target / 32
        have semanticPositive : 0 < semanticTarget :=
          Fraction.Order.Field.div_pos_direct positive
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 32) (by decide))
        let componentTarget := semanticTarget / 4
        have componentPositive : 0 < componentTarget :=
          Fraction.Order.Field.div_pos_direct semanticPositive
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
          Gaussian.Process.Coherence.Basic.Coherent.commonRequest
            leftThreshold rightThreshold
        have componentThresholdPositive : 0 < componentThreshold :=
          Gaussian.Process.Coherence.Basic.Coherent.commonRequest_pos
            leftThresholdPositive rightThresholdPositive
        let inputThreshold :=
          Gaussian.Process.Coherence.Basic.Coherent.commonRequest
            actualThreshold componentThreshold
        have inputThresholdPositive : 0 < inputThreshold :=
          Gaussian.Process.Coherence.Basic.Coherent.commonRequest_pos
            actualThresholdPositive componentThresholdPositive
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
        have outputRequestLtActual :
            Gaussian.Process.Sampling.refinementTarget leftIndex <
              actualThreshold :=
          outputRequestLtInput.trans
            (Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_left
              actualThresholdPositive componentThresholdPositive)
        have outputRequestLtSemantic :
            Gaussian.Process.Sampling.refinementTarget leftIndex <
              semanticTarget :=
          outputRequestSmall.trans
            (Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_right
              inputThresholdPositive semanticPositive)
        let rightIndex := Search.firstQuarterBelow
          1 rightStart componentThreshold
        have rightIndexGe : rightStart ≤ rightIndex :=
          Search.firstQuarterBelow_ge
            1 rightStart componentThreshold
        have rightRequestSmall :
            Gaussian.Process.Sampling.refinementTarget rightIndex <
              componentThreshold :=
          Search.firstQuarterBelow_accurate
            1 (by decide) rightStart componentThreshold
              componentThresholdPositive
        let baseState := Gaussian.Process.Sampling.stateAt
          process start leftIndex
        have baseAllowanceSmall :
            coherent.allowance baseState < semanticTarget :=
          Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt
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
                  Gaussian.Process.Sampling.refinementTarget
                      rightLater < componentThreshold :=
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
              let canonicalLeftState :=
                Gaussian.Process.Sampling.stateAt leftProcess
                  left.name.state rightLater
              let canonicalRightState :=
                Gaussian.Process.Sampling.stateAt rightProcess
                  right.name.state rightLater
              have canonicalLeftSmall :
                  left.coherent.allowance canonicalLeftState < componentTarget :=
                Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt
                  left.coherent left.name.state rightLater componentTarget
                    componentPositive canonicalRequestLtLeft
              have canonicalRightSmall :
                  right.coherent.allowance canonicalRightState < componentTarget :=
                Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt
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
                    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                      (by decide)
                      (Fraction.Order.Arithmetic.add_lt_add_direct
                        canonicalLeftSmall canonicalRightSmall)
                  _ = semanticTarget := by
                    dsimp only [componentTarget]
                    calc
                      2 * (semanticTarget / 4 + semanticTarget / 4) = 4 * (semanticTarget / 4) := by ring1
                      _ = semanticTarget := Fraction.Compatibility.four_mul_quarter_scale semanticTarget
              let baseReading := (process.witness baseState).val
              let canonicalLeft :=
                Gaussian.Process.Sampling.witnessAt leftProcess
                  left.name.state rightLater
              let canonicalRight :=
                Gaussian.Process.Sampling.witnessAt rightProcess
                  right.name.state rightLater
              have basePossible : process.Possible baseState baseReading :=
                (process.witness baseState).property
              have canonicalLeftPossible :
                  leftProcess.Possible canonicalLeftState canonicalLeft :=
                Gaussian.Process.Sampling.witnessAt_possible
                  leftProcess left.name.state rightLater
              have canonicalRightPossible :
                  rightProcess.Possible canonicalRightState canonicalRight :=
                Gaussian.Process.Sampling.witnessAt_possible
                  rightProcess right.name.state rightLater
              have canonicalPossible :
                  process.Possible (canonicalLeftState, canonicalRightState)
                    (canonicalLeft + canonicalRight) :=
                ⟨canonicalLeft, canonicalRight, canonicalLeftPossible,
                  canonicalRightPossible, rfl⟩
              have baseCanonicalRaw := coherent.possible_close
                basePossible canonicalPossible
              have baseCanonical :
                  Data.Gaussian.Norm.Basic.normSq (baseReading - (canonicalLeft + canonicalRight)) <
                    8 * semanticTarget := by
                calc
                  Data.Gaussian.Norm.Basic.normSq (baseReading - (canonicalLeft + canonicalRight)) ≤
                    4 *
                      (coherent.allowance baseState +
                        coherent.allowance
                          (canonicalLeftState, canonicalRightState)) :=
                    baseCanonicalRaw
                  _ < 4 * (semanticTarget + semanticTarget) :=
                    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                      (by decide)
                      (Fraction.Order.Arithmetic.add_lt_add_direct
                        baseAllowanceSmall canonicalAllowanceSmall)
                  _ = 8 * semanticTarget := by ring1
              have actualTail :
                  Data.Gaussian.Norm.Basic.normSq
                      (Gaussian.Process.Sampling.witnessAt process
                          start leftLater -
                        Gaussian.Process.Sampling.witnessAt process
                          start leftIndex) <
                    4 * semanticTarget := by
                calc
                  Data.Gaussian.Norm.Basic.normSq
                      (Gaussian.Process.Sampling.witnessAt process
                          start leftLater -
                        Gaussian.Process.Sampling.witnessAt process
                          start leftIndex) ≤
                    4 * Gaussian.Process.Sampling.refinementTarget
                      leftIndex := by
                    rw [← Gaussian.Sampling.Dyadic.quarterRadius_four_eq_four_refinementTarget]
                    exact
                      Gaussian.Process.Sampling.witnessAt_later_close
                        process start leftOrder
                  _ < 4 * semanticTarget :=
                    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                      (by decide) outputRequestLtSemantic
              have baseWitness :
                  Gaussian.Process.Sampling.witnessAt process
                      start leftIndex = baseReading :=
                rfl
              change Data.Gaussian.Norm.Basic.normSq
                  (Gaussian.Process.Sampling.witnessAt process
                      start leftLater - sum.sample rightLater) < target
              rw [Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation_sample]
              calc
                Data.Gaussian.Norm.Basic.normSq
                    (Gaussian.Process.Sampling.witnessAt process
                        start leftLater - (canonicalLeft + canonicalRight)) ≤
                  2 *
                    (Data.Gaussian.Norm.Basic.normSq
                        (Gaussian.Process.Sampling.witnessAt process
                            start leftLater -
                          Gaussian.Process.Sampling.witnessAt process
                            start leftIndex) +
                      Data.Gaussian.Norm.Basic.normSq
                        (Gaussian.Process.Sampling.witnessAt process
                            start leftIndex -
                          (canonicalLeft + canonicalRight))) :=
                    Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
                _ < 2 *
                    (4 * semanticTarget + 8 * semanticTarget) :=
                  Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                    (by decide)
                    (Fraction.Order.Arithmetic.add_lt_add_direct actualTail
                      (by rw [baseWitness]; exact baseCanonical))
                _ = 24 * semanticTarget := by ring1
                _ < target := by
                  dsimp only [semanticTarget]
                  exact Purelib.Data.Rat.Bounds.Fraction.twenty_four_thirty_seconds_lt positive } }
  exact Equivalent.trans bridge
    (Equivalent.symm
      (Equivalent.toNamed_sampling
        sum))
end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge

end
