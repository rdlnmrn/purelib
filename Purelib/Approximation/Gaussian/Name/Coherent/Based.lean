module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Coherence
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Based
public import Purelib.Approximation.Gaussian.Process.Coherence.Based
import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Nat.Order
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

/-!
# Based coherent Gaussian names

A finite refinement future retains the chosen starting state and its source
provenance. Explicit comparison certificates preserve the operational value
when restricting the future or replacing the starting state.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation

open Purelib Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Process.Based
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat

public section

/-- Restrict a coherent name to the finite refinement future of a chosen state.

Each retained process state carries its provenance from the supplied base;
the source coherence certificate bounds the same displayed readings. -/
@[expose] def based (value : Coherent.CoherentNamed)
    (state : value.name.process.State) : Coherent.CoherentNamed :=
  { name :=
      { process := Gaussian.Process.Based.based value.name.process state
        state := BasedState.initial
          value.name.process state }
    coherent := Gaussian.Process.Coherence.Basic.Coherent.based value.coherent state }

/-- Restricting a coherent name to a finite refinement future preserves its value.

The comparison uses explicit displayed rational witnesses and the source
coherence allowance on both sides for every positive requested tolerance. -/
@[expose] def basedEquivalent (value : Coherent.CoherentNamed)
    (state : value.name.process.State) :
    Gaussian.Equivalence.NamedEquivalent value.name (based value state).name where
  compare := by
    intro leftIndex rightIndex target positive
    let startIndex := max leftIndex rightIndex
    have leftBound : leftIndex ≤ startIndex := by
      change leftIndex ≤ max leftIndex rightIndex
      rw [Data.Nat.Order.max_eq_natMax]
      exact Data.Nat.Order.le_max_left _ _
    have rightBound : rightIndex ≤ startIndex := by
      change rightIndex ≤ max leftIndex rightIndex
      rw [Data.Nat.Order.max_eq_natMax]
      exact Data.Nat.Order.le_max_right _ _
    let semanticTarget := target / 8
    have semanticPositive : 0 < semanticTarget := Purelib.Data.Rat.Bounds.Quarter.eighth_pos positive
    let processRequest := value.coherent.accuracyRequest semanticTarget
    have processRequestPositive : 0 < processRequest :=
      value.coherent.accuracyRequest_pos semanticPositive
    let comparisonIndex := Search.firstQuarterBelow
      1 startIndex processRequest
    have comparisonRequestSmall :
        Gaussian.Process.Sampling.refinementTarget comparisonIndex <
          processRequest :=
      Search.firstQuarterBelow_accurate
        1 (by decide) startIndex processRequest processRequestPositive
    exact
      { leftIndex := comparisonIndex
        rightIndex := comparisonIndex
        left_ge := leftBound.trans
          (Search.firstQuarterBelow_ge
            1 startIndex processRequest)
        right_ge := rightBound.trans
          (Search.firstQuarterBelow_ge
            1 startIndex processRequest)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftAllowanceLt :
              value.coherent.allowance
                  (Gaussian.Process.Sampling.stateAt value.name.process
                    value.name.state leftLater) < target / 8 :=
            Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt value.coherent value.name.state
              leftLater semanticTarget semanticPositive
              ((quarterRadius_antitone (by decide)
                leftOrder).trans_lt comparisonRequestSmall)
          have rightAllowanceLt :
              value.coherent.allowance
                  (Gaussian.Process.Sampling.stateAt
                    (Gaussian.Process.Based.based value.name.process state)
                    (BasedState.initial
                      value.name.process state) rightLater).source <
                target / 8 :=
            Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt
              (Gaussian.Process.Coherence.Basic.Coherent.based value.coherent state)
              (BasedState.initial
                value.name.process state)
              rightLater semanticTarget semanticPositive
              ((quarterRadius_antitone (by decide)
                rightOrder).trans_lt comparisonRequestSmall)
          have close := value.coherent.possible_close
            (Gaussian.Process.Sampling.witnessAt_possible value.name.process
              value.name.state leftLater)
            (show value.name.process.Possible
                (Gaussian.Process.Sampling.stateAt
                  (Gaussian.Process.Based.based value.name.process state)
                  (BasedState.initial
                    value.name.process state) rightLater).source
                (Gaussian.Process.Sampling.witnessAt
                  (Gaussian.Process.Based.based value.name.process state)
                  (BasedState.initial
                    value.name.process state) rightLater) from
              Gaussian.Process.Sampling.witnessAt_possible
                (Gaussian.Process.Based.based value.name.process state)
                (BasedState.initial
                  value.name.process state) rightLater)
          calc
            Data.Gaussian.Norm.Basic.normSq
                ((Sampling.approximation value.name).sample
                    leftLater -
                  (Sampling.approximation
                    (based value state).name).sample rightLater) <=
              4 *
                (value.coherent.allowance
                    (Gaussian.Process.Sampling.stateAt value.name.process
                      value.name.state leftLater) +
                  value.coherent.allowance
                    (Gaussian.Process.Sampling.stateAt
                      (Gaussian.Process.Based.based value.name.process state)
                      (BasedState.initial
                        value.name.process state) rightLater).source) := close
            _ < 4 * (target / 8 + target / 8) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  leftAllowanceLt rightAllowanceLt)
            _ = target := Purelib.Data.Rat.Bounds.Quarter.eight_eighths target }

/-- Replacing a coherent process starting state preserves its operational value.

The finite comparison retains the original process and uses its coherence
certificate to compare the readings from the two supplied starting states. -/
@[expose] def rebaseEquivalent (value : Coherent.CoherentNamed)
    (state : value.name.process.State) :
    Gaussian.Equivalence.NamedEquivalent value.name
      ({ process := value.name.process, state := state } : Purelib.Approximation.Gaussian.Name.Basic.Named) :=
  value.coherent.namedEquivalent value.name.state state

end

end Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
