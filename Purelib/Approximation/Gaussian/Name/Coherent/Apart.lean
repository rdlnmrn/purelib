module
import Purelib.Data.Nat.Order
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
public import Purelib.Approximation.Gaussian.Process.Coherence.Apart
public import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Data.Nat.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

/-!
# Apartness preparation of coherent Gaussian names

A retained candidate-apart certificate prepares the original coherent name
for whole-ball division. The preparation retains its starting process state
and coherence data; the operational comparison records both original names,
requests and sampled candidates at their computed finite indices.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Process.Apart
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Request
open Purelib.Data.Rat

open Purelib.Data.Nat

/-- Prepare a candidate-apart coherent name for whole-ball division using one explicit finite starting-state refinement.

The original persistent name supplies the process and starting state. Its
candidate-apart certificate determines the same retained preparation and
coherence data. -/
@[expose] public def apartify (value : Coherent.CoherentNamed)
    (apart : Possible.PossibleApart
      value.name.process) : Coherent.CoherentNamed :=
  { name :=
      { process := Preparation.apartify apart
        state := Preparation.prepareApartState apart
          value.name.state }
    coherent := Gaussian.Process.Coherence.Basic.Coherent.apartify value.coherent apart }

/-- Preparing a candidate-apart coherent name preserves its finite operational value.

The original and prepared names retain their own states and refinement
requests. The original coherence certificate compares their sampled candidates
at the same computed comparison index and displayed target. -/
@[expose] public def apartifyEquivalent (value : Coherent.CoherentNamed)
    (apart : Possible.PossibleApart value.name.process) :
    Gaussian.Equivalence.NamedEquivalent value.name (Approximation.Gaussian.Name.Coherent.CoherentNamed.apartify value
      apart).name where
  compare := by
    intro leftIndex rightIndex target positive
    let startIndex := max leftIndex rightIndex
    let semanticTarget := target / 8
    have semanticPositive : 0 < semanticTarget := Purelib.Data.Rat.Bounds.Quarter.eighth_pos positive
    let leftRequest := value.coherent.accuracyRequest semanticTarget
    let preparedCoherent := Gaussian.Process.Coherence.Basic.Coherent.apartify value.coherent apart
    let rightRequest := preparedCoherent.accuracyRequest semanticTarget
    let processRequest := Common.commonTarget
      leftRequest rightRequest
    have leftRequestPositive : 0 < leftRequest :=
      value.coherent.accuracyRequest_pos semanticPositive
    have rightRequestPositive : 0 < rightRequest :=
      preparedCoherent.accuracyRequest_pos semanticPositive
    have processRequestPositive : 0 < processRequest :=
      Common.commonTarget_pos leftRequestPositive
        rightRequestPositive
    let comparisonIndex := Search.firstQuarterBelow
      1 startIndex processRequest
    have comparisonRequestSmall :
        Gaussian.Process.Sampling.refinementTarget comparisonIndex <
          processRequest :=
      Search.firstQuarterBelow_accurate
        1 (by decide) startIndex processRequest processRequestPositive
    have comparisonLeftSmall :
        Gaussian.Process.Sampling.refinementTarget comparisonIndex <
          leftRequest :=
      comparisonRequestSmall.trans
        (Common.commonTarget_lt_left
          leftRequestPositive rightRequestPositive)
    have comparisonRightSmall :
        Gaussian.Process.Sampling.refinementTarget comparisonIndex <
          rightRequest :=
      comparisonRequestSmall.trans
        (Common.commonTarget_lt_right
          leftRequestPositive rightRequestPositive)
    exact
      { leftIndex := comparisonIndex
        rightIndex := comparisonIndex
        left_ge := by
          apply Nat.le_trans _ (Search.firstQuarterBelow_ge 1 startIndex processRequest)
          change leftIndex ≤ max leftIndex rightIndex
          rewrite [Order.max_eq_natMax]
          exact Order.le_max_left leftIndex rightIndex
        right_ge := by
          apply Nat.le_trans _ (Search.firstQuarterBelow_ge 1 startIndex processRequest)
          change rightIndex ≤ max leftIndex rightIndex
          rewrite [Order.max_eq_natMax]
          exact Order.le_max_right leftIndex rightIndex
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftAllowanceLt :
              value.coherent.allowance
                  (Gaussian.Process.Sampling.stateAt value.name.process
                    value.name.state leftLater) < target / 8 :=
            Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt value.coherent value.name.state
              leftLater semanticTarget semanticPositive
              ((quarterRadius_antitone (by decide)
                leftOrder).trans_lt comparisonLeftSmall)
          have rightAllowanceLt :
              preparedCoherent.allowance
                  (Gaussian.Process.Sampling.stateAt
                    (Preparation.apartify apart)
                    (Preparation.prepareApartState apart
                      value.name.state) rightLater) < target / 8 :=
            Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt preparedCoherent
              (Preparation.prepareApartState apart value.name.state)
              rightLater semanticTarget semanticPositive
              ((quarterRadius_antitone (by decide)
                rightOrder).trans_lt comparisonRightSmall)
          have close := value.coherent.possible_close
            (Gaussian.Process.Sampling.witnessAt_possible value.name.process
              value.name.state leftLater)
            (show value.name.process.Possible
                (Gaussian.Process.Sampling.stateAt
                  (Preparation.apartify apart)
                  (Preparation.prepareApartState apart
                    value.name.state) rightLater).source
                (Gaussian.Process.Sampling.witnessAt
                  (Preparation.apartify apart)
                  (Preparation.prepareApartState apart
                    value.name.state) rightLater) from
              Gaussian.Process.Sampling.witnessAt_possible
                (Preparation.apartify apart)
                (Preparation.prepareApartState apart
                  value.name.state) rightLater)
          calc
            Data.Gaussian.Norm.Basic.normSq
                ((Sampling.approximation value.name).sample
                    leftLater -
                  (Sampling.approximation
                    (Approximation.Gaussian.Name.Coherent.CoherentNamed.apartify value apart).name).sample rightLater)
                      <=
              4 *
                (value.coherent.allowance
                    (Gaussian.Process.Sampling.stateAt value.name.process
                      value.name.state leftLater) +
                  value.coherent.allowance
                    (Gaussian.Process.Sampling.stateAt
                      (Preparation.apartify apart)
                      (Preparation.prepareApartState apart
                        value.name.state) rightLater).source) := close
            _ < 4 * (target / 8 + target / 8) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  leftAllowanceLt rightAllowanceLt)
            _ = target := Purelib.Data.Rat.Bounds.Quarter.eight_eighths target }
end Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
