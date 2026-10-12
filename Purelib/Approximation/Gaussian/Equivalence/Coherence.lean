module
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Data.Nat.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Nat.Order

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

/-!
# Comparisons of retained coherent process states

The same process coherence certificate bounds two independently retained starting
states. A finite geometric search selects common later sampling requests whose
original witness readings satisfy the displayed squared-distance tolerance.
-/

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Nat
open Purelib.Approximation.Gaussian.Equivalence

/-- Coherence closes the original branching-process gap: any two starting states of one coherent process yield
operationally equivalent CCL names. The comparison computes one finite sampling index and thereafter compares only
explicit rational witnesses at finite states.

The same coherence certificate bounds both independently retained starting
states. One original geometric search index makes their requested allowances
small, and all later original witness readings satisfy the displayed tolerance. -/
@[expose] public def Coherent.namedEquivalent {process : Process} (coherent :
  Gaussian.Process.Coherence.Basic.Coherent process)
    (leftStart rightStart : process.State) :
    Gaussian.Equivalence.NamedEquivalent
      ({ process := process, state := leftStart } : Gaussian.Name.Basic.Named)
      ({ process := process, state := rightStart } : Gaussian.Name.Basic.Named) where
  compare := by
    intro leftIndex rightIndex target positive
    let startIndex := max leftIndex rightIndex
    have leftMaximum : leftIndex ≤ startIndex := by
      change leftIndex ≤ max leftIndex rightIndex
      rw [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have rightMaximum : rightIndex ≤ startIndex := by
      change rightIndex ≤ max leftIndex rightIndex
      rw [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    let semanticTarget := target / 8
    have semanticPositive : 0 < semanticTarget := Purelib.Data.Rat.Bounds.Quarter.eighth_pos positive
    let processTarget := coherent.accuracyRequest semanticTarget
    have processTargetPositive : 0 < processTarget :=
      coherent.accuracyRequest_pos semanticPositive
    let comparisonIndex :=
      Search.firstQuarterBelow
        1 startIndex processTarget
    have comparisonRequestSmall :
        Gaussian.Process.Sampling.refinementTarget comparisonIndex <
          processTarget := by
      exact Search.firstQuarterBelow_accurate
        1 (by decide) startIndex processTarget processTargetPositive
    exact
      { leftIndex := comparisonIndex
        rightIndex := comparisonIndex
        left_ge := leftMaximum.trans
          (Search.firstQuarterBelow_ge
            1 startIndex processTarget)
        right_ge := rightMaximum.trans
          (Search.firstQuarterBelow_ge
            1 startIndex processTarget)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftAllowanceLt :
              coherent.allowance
                  (Gaussian.Process.Sampling.stateAt process
                    leftStart leftLater) < target / 8 :=
            Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt coherent leftStart leftLater semanticTarget
              semanticPositive
              ((quarterRadius_antitone (by decide)
                leftOrder).trans_lt
                comparisonRequestSmall)
          have rightAllowanceLt :
              coherent.allowance
                  (Gaussian.Process.Sampling.stateAt process
                    rightStart rightLater) < target / 8 :=
            Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt coherent rightStart rightLater semanticTarget
              semanticPositive
              ((quarterRadius_antitone (by decide)
                rightOrder).trans_lt
                comparisonRequestSmall)
          have close := coherent.possible_close
            (Gaussian.Process.Sampling.witnessAt_possible
              process leftStart leftLater)
            (Gaussian.Process.Sampling.witnessAt_possible
              process rightStart rightLater)
          calc
            Data.Gaussian.Norm.Basic.normSq
                (Gaussian.Process.Sampling.witnessAt process
                    leftStart leftLater -
                  Gaussian.Process.Sampling.witnessAt process
                    rightStart rightLater) ≤
              4 *
                (coherent.allowance
                    (Gaussian.Process.Sampling.stateAt process
                      leftStart leftLater) +
                  coherent.allowance
                    (Gaussian.Process.Sampling.stateAt process
                      rightStart rightLater)) := close
            _ < 4 * (target / 8 + target / 8) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  leftAllowanceLt rightAllowanceLt)
            _ = target := Purelib.Data.Rat.Bounds.Quarter.eight_eighths target }

end Purelib.Approximation.Gaussian.Process.Coherence.Basic
