module

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Constructive small-residual samples with explicit denominator height

A selected Newton band contains a point on a computable square Gaussian grid.
Coordinatewise nearest-integer rounding halves the required mesh width: the
grid denominator is one more than the integer floor of `1 / (2r)`.  This gives
an exact finite denominator certificate for the box-to-residual estimate.
-/

namespace Purelib.Data.Nat.SquareThreshold.Basic

/-! ## Square-root-scaled residual requests -/

/-- Scan boundedly for the first candidate whose square exceeds the input.

Return the current candidate on success or when fuel is exhausted. Each unsuccessful
step increments the candidate and consumes one unit of fuel; the public threshold
supplies sufficient fuel. -/
def squareThresholdAux (input candidate : Nat) : Nat → Nat
  | 0 => candidate
  | fuel + 1 =>
      if input < candidate * candidate then candidate
      else squareThresholdAux input (candidate + 1) fuel

open Purelib.Data.Nat.SquareThreshold
/-- A fueled square-threshold scan returns no more than its start plus its fuel. -/
theorem squareThresholdAux_le_add (input candidate fuel : Nat) :
    squareThresholdAux input candidate fuel ≤ candidate + fuel := by
  induction fuel generalizing candidate with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      unfold squareThresholdAux
      split
      · exact Nat.le_add_right candidate (fuel + 1)
      · have recursive := inductionHypothesis (candidate + 1)
        calc
          squareThresholdAux input (candidate + 1) fuel ≤
              (candidate + 1) + fuel := recursive
          _ = candidate + (fuel + 1) := by ring1

/-- A reachable successful terminal candidate guarantees a successful square scan.

If the square of candidate + fuel is strictly above input, the returned candidate
also has square strictly above input. -/
theorem squareThresholdAux_spec {input candidate fuel : Nat}
    (eventual : input < (candidate + fuel) * (candidate + fuel)) :
    input < squareThresholdAux input candidate fuel *
      squareThresholdAux input candidate fuel := by
  induction fuel generalizing candidate with
  | zero =>
      simpa only [squareThresholdAux, Nat.add_zero] using eventual
  | succ fuel inductionHypothesis =>
      unfold squareThresholdAux
      split
      · assumption
      · apply inductionHypothesis
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          eventual

/-- The square scan returns no later than any reachable successful comparison.

The comparison must lie between the starting candidate and candidate + fuel, and its
square must exceed input. The scan therefore stops at or before it. -/
theorem squareThresholdAux_minimal {input candidate fuel comparison : Nat}
    (candidateLe : candidate ≤ comparison)
    (comparisonReachable : comparison ≤ candidate + fuel)
    (comparisonWorks : input < comparison * comparison) :
    squareThresholdAux input candidate fuel ≤ comparison := by
  induction fuel generalizing candidate with
  | zero =>
      unfold squareThresholdAux
      exact candidateLe
  | succ fuel inductionHypothesis =>
      unfold squareThresholdAux
      split
      · exact candidateLe
      · rename_i candidateFails
        have candidateNe : candidate ≠ comparison := by
          intro equal
          subst comparison
          exact candidateFails comparisonWorks
        have nextCandidateLe : candidate + 1 ≤ comparison :=
          Nat.succ_le_of_lt (Nat.lt_of_le_of_ne candidateLe candidateNe)
        have comparisonStillReachable : comparison ≤ candidate + 1 + fuel := by
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            Nat.add_succ] using comparisonReachable
        exact inductionHypothesis (candidate := candidate + 1)
          nextCandidateLe comparisonStillReachable

/-- Compute the least positive natural whose square exceeds the input.

Start the bounded scan at one with input + 1 units of fuel. The square comparison
uses exact natural arithmetic. -/
def squareThreshold (input : Nat) : Nat :=
  squareThresholdAux input 1 (input + 1)

/-- The computed square threshold has square strictly greater than its input. -/
theorem squareThreshold_spec (input : Nat) :
    input < squareThreshold input * squareThreshold input := by
  apply squareThresholdAux_spec
  rw [show 1 + (input + 1) = input + 2 by ring1]
  have oneLe : 1 ≤ input + 2 :=
    Nat.succ_le_succ (Nat.zero_le (input + 1))
  have productBound := Nat.mul_le_mul_left (input + 2) oneLe
  calc
    input < input + 2 := Nat.lt_add_of_pos_right (by decide)
    _ = (input + 2) * 1 := (Nat.mul_one _).symm
    _ ≤ (input + 2) * (input + 2) := productBound

/-- The computed square threshold is strictly positive. -/
theorem squareThreshold_pos (input : Nat) : 0 < squareThreshold
  input := by
  have strict := squareThreshold_spec input
  apply Nat.pos_of_ne_zero
  intro zero
  rw [zero] at strict
  simp only [Nat.zero_mul] at strict
  exact (Nat.not_lt_zero input) strict

/-- The computed square threshold is no larger than any positive successful candidate.

Every positive comparison whose square exceeds input bounds the result, whether or
not it lies within the explicit search fuel. -/
theorem squareThreshold_minimal {input comparison : Nat}
    (comparisonPositive : 0 < comparison)
    (comparisonWorks : input < comparison * comparison) :
    squareThreshold input ≤ comparison := by
  by_cases reachable : comparison ≤ 1 + (input + 1)
  · exact squareThresholdAux_minimal comparisonPositive reachable
      comparisonWorks
  · have outputBound := squareThresholdAux_le_add input 1 (input + 1)
    unfold squareThreshold
    exact outputBound.trans
      (Nat.le_of_lt (Nat.lt_of_not_ge reachable))
end Purelib.Data.Nat.SquareThreshold.Basic

end
