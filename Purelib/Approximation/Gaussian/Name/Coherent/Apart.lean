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

/-- Select the supplied original apart state, or perform the unchanged original starting refinement.

The optional state has the same original process and candidate-apartness
certificate. The supplied branch consumes that complete state literally.
-/
@[expose] public def apartState (value : CoherentNamed)
    (apart : Possible.PossibleApart value.name.process)
    (cached : Option (Preparation.ApartState value.name.process apart) := none) :
    Preparation.ApartState value.name.process apart :=
  match cached with
  | some state => state
  | none => Preparation.prepareApartState apart value.name.state

/-- An actual supplied apart state bypasses the default refinement completely. -/
public theorem apartState_some (value : CoherentNamed)
    (apart : Possible.PossibleApart value.name.process)
    (cached : Preparation.ApartState value.name.process apart) :
    value.apartState apart (some cached) = cached := rfl

/-- No supplied apart state retains the complete original finite refinement. -/
public theorem apartState_none (value : CoherentNamed)
    (apart : Possible.PossibleApart value.name.process) :
    value.apartState apart none = Preparation.prepareApartState apart value.name.state := rfl

/-- Prepare a candidate-apart coherent name using a supplied apart state or the original finite starting refinement.

The original name supplies the process and coherence data. A supplied state
belongs to that same apartified process; without one the original starting
state is refined by the same positive candidate bound.
-/
@[expose] public def apartify (value : CoherentNamed)
    (apart : Possible.PossibleApart
      value.name.process)
    (cached : Option (Preparation.ApartState value.name.process apart) := none) : CoherentNamed :=
  { name :=
      { process := Preparation.apartify apart
        state := value.apartState apart cached }
    coherent := Process.Coherence.Basic.Coherent.apartify value.coherent apart }

/-- Preparing a candidate-apart coherent name preserves its finite operational value.

The original and prepared names retain their own states and refinement
requests. The original coherence certificate compares their sampled candidates
at the same computed comparison index and displayed target. -/
@[expose] public def apartifyEquivalent (value : CoherentNamed)
    (apart : Possible.PossibleApart value.name.process)
    (cached : Option (Preparation.ApartState value.name.process apart) := none) :
    NamedEquivalent value.name (apartify value apart cached).name where
  compare := by
    intro leftIndex rightIndex target positive
    let retained := value.apartState apart cached
    let startIndex := max leftIndex rightIndex
    let semanticTarget := target / 8
    have semanticPositive : 0 < semanticTarget := Bounds.Quarter.eighth_pos positive
    let leftRequest := value.coherent.accuracyRequest semanticTarget
    let preparedCoherent := Process.Coherence.Basic.Coherent.apartify value.coherent apart
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
        Process.Sampling.refinementTarget comparisonIndex <
          processRequest :=
      Search.firstQuarterBelow_accurate
        1 (by decide) startIndex processRequest processRequestPositive
    have comparisonLeftSmall :
        Process.Sampling.refinementTarget comparisonIndex <
          leftRequest :=
      comparisonRequestSmall.trans
        (Common.commonTarget_lt_left
          leftRequestPositive rightRequestPositive)
    have comparisonRightSmall :
        Process.Sampling.refinementTarget comparisonIndex <
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
                  (Process.Sampling.stateAt value.name.process
                    value.name.state leftLater) < target / 8 :=
            Process.Coherence.Basic.Coherent.stateAt_allowance_lt value.coherent value.name.state
              leftLater semanticTarget semanticPositive
              ((quarterRadius_antitone (by decide)
                leftOrder).trans_lt comparisonLeftSmall)
          have rightAllowanceLt :
              preparedCoherent.allowance
                  (Process.Sampling.stateAt
                    (Preparation.apartify apart)
                    retained rightLater) < target / 8 :=
            Process.Coherence.Basic.Coherent.stateAt_allowance_lt preparedCoherent
              retained
              rightLater semanticTarget semanticPositive
              ((quarterRadius_antitone (by decide)
                rightOrder).trans_lt comparisonRightSmall)
          have close := value.coherent.possible_close
            (Process.Sampling.witnessAt_possible value.name.process
              value.name.state leftLater)
            (show value.name.process.Possible
                (Process.Sampling.stateAt
                  (Preparation.apartify apart)
                  retained rightLater).source
                (Process.Sampling.witnessAt
                  (Preparation.apartify apart)
                  retained rightLater) from
              Process.Sampling.witnessAt_possible
                (Preparation.apartify apart)
                retained rightLater)
          calc
            Data.Gaussian.Norm.Basic.normSq
                ((Sampling.approximation value.name).sample
                    leftLater -
                  (Sampling.approximation
                    (apartify value apart cached).name).sample rightLater)
                      <=
              4 *
                (value.coherent.allowance
                    (Process.Sampling.stateAt value.name.process
                      value.name.state leftLater) +
                  value.coherent.allowance
                    (Process.Sampling.stateAt
                      (Preparation.apartify apart)
                      retained rightLater).source) := close
            _ < 4 * (target / 8 + target / 8) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  leftAllowanceLt rightAllowanceLt)
            _ = target := Bounds.Quarter.eight_eighths target }

/-- No supplied apart state preserves the complete original prepared name and starting refinement. -/
public theorem apartify_none (value : CoherentNamed)
    (apart : Possible.PossibleApart value.name.process) :
    value.apartify apart none =
      { name :=
          { process := Preparation.apartify apart
            state := Preparation.prepareApartState apart value.name.state }
        coherent := Process.Coherence.Basic.Coherent.apartify value.coherent apart } := rfl

/-- Supplying the original computed state preserves the entire default apartified name. -/
public theorem apartify_canonical (value : CoherentNamed)
    (apart : Possible.PossibleApart value.name.process) :
    value.apartify apart (some (Preparation.prepareApartState apart value.name.state)) =
      value.apartify apart none := rfl

/-- Supplying the original computed state preserves the entire default operational comparison. -/
public theorem apartifyEquivalent_canonical (value : CoherentNamed)
    (apart : Possible.PossibleApart value.name.process) :
    value.apartifyEquivalent apart (some (Preparation.prepareApartState apart value.name.state)) =
      value.apartifyEquivalent apart none := rfl

end Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
