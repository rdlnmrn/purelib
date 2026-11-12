module

public import Purelib.Approximation.Gaussian.Name.Coherent.State
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Finite comparison of references certified at retained coefficient states

Both original channels, states and universal candidate bounds remain inputs.
A comparison of their actual based futures supplies possible candidates at
those same states; neither observed reference is replaced by a new witness.
-/

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.State.CoefficientState

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order

/-- Universal bounds at two retained equivalent coefficient states control their original reference values.

The finite comparison is taken after both original states. Its two possible
candidates remain possible at those states, so their independently retained
bounds and the requested comparison pay the reference discrepancy.
-/
theorem reference_difference_le (first last : CoefficientState) (firstReference lastReference : Canonical)
    (firstAllowance lastAllowance : Rational)
    (firstBound : ∀ candidate, first.channel.name.process.Possible first.state candidate →
      Norm.Basic.normSq (candidate - firstReference) ≤ firstAllowance)
    (lastBound : ∀ candidate, last.channel.name.process.Possible last.state candidate →
      Norm.Basic.normSq (candidate - lastReference) ≤ lastAllowance)
    (equivalent : NamedEquivalent first.channel.name last.channel.name)
    (positive : 0 < firstAllowance + lastAllowance) :
    Norm.Basic.normSq (firstReference - lastReference) ≤ 8 * (firstAllowance + lastAllowance) := by
  let firstBased := first.channel.based first.state
  let lastBased := last.channel.based last.state
  let basedEquivalent := (first.channel.basedEquivalent first.state).symm.trans
    (equivalent.trans (last.channel.basedEquivalent last.state))
  let target := firstAllowance + lastAllowance
  let comparison := basedEquivalent.compare 0 0 target positive
  let firstSample := (Name.Sampling.approximation firstBased.name).sample comparison.leftIndex
  let lastSample := (Name.Sampling.approximation lastBased.name).sample comparison.rightIndex
  have firstPossible : first.channel.name.process.Possible first.state firstSample :=
    Process.Based.based_initial_persists first.channel.name.process first.state
      (Process.Sampling.witnessAt_possible firstBased.name.process firstBased.name.state comparison.leftIndex)
  have lastPossible : last.channel.name.process.Possible last.state lastSample :=
    Process.Based.based_initial_persists last.channel.name.process last.state
      (Process.Sampling.witnessAt_possible lastBased.name.process lastBased.name.state comparison.rightIndex)
  have firstError := firstBound firstSample firstPossible
  have lastError := lastBound lastSample lastPossible
  have firstNonnegative : 0 ≤ firstAllowance := (Norm.Basic.normSq_nonneg _).trans firstError
  have close : Norm.Basic.normSq (firstSample - lastSample) ≤ target :=
    (comparison.close (Nat.le_refl _) (Nat.le_refl _)).le
  have inner := (Norm.Bounds.normSq_sub_le_via firstSample lastSample lastReference).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct close lastError) (by decide +kernel))
  have firstReverse : Norm.Basic.normSq (firstReference - firstSample) ≤ firstAllowance := by
    rewrite [Norm.Bounds.normSq_sub_symm]
    exact firstError
  calc
    _ ≤ 2 * (Norm.Basic.normSq (firstReference - firstSample) +
        Norm.Basic.normSq (firstSample - lastReference)) := Norm.Bounds.normSq_sub_le_via _ _ _
    _ ≤ 2 * (firstAllowance + 2 * (target + lastAllowance)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct firstReverse inner) (by decide +kernel)
    _ = 6 * firstAllowance + 8 * lastAllowance := by dsimp only [target]; ring1
    _ ≤ 8 * firstAllowance + 8 * lastAllowance := Arithmetic.add_le_add_direct
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by decide +kernel : (6 : Rational) ≤ 8) firstNonnegative) (Purelib.Data.Rat.Fraction.Order.Basic.le_refl _)
    _ = _ := by ring1

end Purelib.Approximation.Gaussian.Name.Coherent.State.CoefficientState

end
