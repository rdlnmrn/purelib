module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Coupling.Basic
public import Purelib.Measure.Coupling.Law.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Weighted.Integral
public import Purelib.Examples.Measure.Distribution.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Coupling.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)

/-- The finite graph coupling from the fair coin to deterministic tails. -/
def coinToFalseCoupling : Coupling Bool Bool
  where
  joint := (Coupling.graph fairCoin fun _ => false).joint

/-- The Boolean equality relation on two coin outcomes. -/
def sameBool (left right : Bool) : Bool :=
  left == right

/-- The zero-one cost of a mismatch between coin outcomes. -/
def boolMismatchCost (left right : Bool) :
  Fraction.Rational :=
  if sameBool left right then 0 else 1

/-- The relation requiring the right outcome to be the Boolean complement of the left. -/
def flipRelation (left right : Bool) : Bool :=
  right == !left

/-- The graph law coupling between the fair coin and its flipped pushforward. -/
def fairFlipLawCoupling :
    LawCoupling fairCoin (fairCoin.map fun outcome =>
      !outcome) :=
  LawCoupling.graph fairCoin fun outcome => !outcome

/-- Reversing the retained flip coupling exchanges its original marginal laws. -/
example : LawCoupling (fairCoin.map fun outcome => !outcome)
  fairCoin :=
  fairFlipLawCoupling.symm

/-- The flip coupling has zero mismatch probability for the complement relation. -/
example : fairFlipLawCoupling.mismatchProbability
  flipRelation = 0 := by
  decide

/-- The heads and flipped-tails probabilities differ by at most the retained flip mismatch probability. -/
example :
    (fairCoin.map fun outcome => !outcome).probability
          (fun outcome => !outcome) -
        fairCoin.probability (fun outcome => outcome) ≤
          fairFlipLawCoupling.mismatchProbability
            flipRelation ∧
      fairCoin.probability (fun outcome => outcome) -
          (fairCoin.map fun outcome => !outcome).probability
            (fun outcome => !outcome) ≤
          fairFlipLawCoupling.mismatchProbability
            flipRelation := by
  apply fairFlipLawCoupling.probability_close_of_eventsAgree
    flipRelation (fun outcome => outcome) (fun outcome => !outcome)
  intro atom member related
  rcases atom with ⟨⟨left, right⟩, weight, nonnegative⟩
  change (right == !left) = true at related
  have rightEqual : right = !left := eq_of_beq related
  subst right
  cases left <;> rfl

/-- The coupling to deterministic tails has equality-mismatch probability one half. -/
example : coinToFalseCoupling.mismatchProbability
  sameBool = 1 / 2 := by
  decide

/-- The coupling to deterministic tails has zero-one transport cost one half. -/
example : coinToFalseCoupling.transportCost
  boolMismatchCost = 1 / 2 := by
  decide

/-- The left marginal of the coupling to tails assigns heads probability one half. -/
example : coinToFalseCoupling.leftMarginal.probability
    (fun outcome => outcome) = 1 / 2 := by
  decide

/-- The right marginal of the coupling to tails assigns heads probability zero. -/
example : coinToFalseCoupling.rightMarginal.probability
    (fun outcome => outcome) = 0 := by
  decide

/-- The graph coupling's left marginal retains the original fair-coin heads probability. -/
example : coinToFalseCoupling.leftMarginal.probability
    (fun outcome => outcome) = fairCoin.probability (fun outcome => outcome) := by
  exact Coupling.graph_leftMarginal_probability fairCoin
    (fun _ => false) (fun outcome => outcome)

/-- The graph coupling satisfies the deterministic-tails relation with zero mismatch probability. -/
example : coinToFalseCoupling.mismatchProbability
    (fun _ right => !right) = 0 := by
  apply Coupling.graph_mismatchProbability_eq_zero
  intro atom member
  rfl

/-- The marginal heads-probability gap equals the retained equality-mismatch probability. -/
example :
    coinToFalseCoupling.leftMarginal.probability (fun outcome =>
      outcome) -
        coinToFalseCoupling.rightMarginal.probability (fun outcome =>
          outcome) =
      coinToFalseCoupling.mismatchProbability
        sameBool := by
  decide

/-- Both directions of the marginal heads-probability difference are bounded by the retained mismatch probability. -/
example :
    coinToFalseCoupling.rightMarginal.probability (fun outcome =>
      outcome) -
          coinToFalseCoupling.leftMarginal.probability (fun outcome =>
            outcome) ≤
        coinToFalseCoupling.mismatchProbability
          sameBool ∧
      coinToFalseCoupling.leftMarginal.probability (fun outcome =>
        outcome) -
          coinToFalseCoupling.rightMarginal.probability (fun outcome
            => outcome) ≤
        coinToFalseCoupling.mismatchProbability
          sameBool := by
  apply coinToFalseCoupling.probability_close_of_eventsAgree
    sameBool
  intro atom member related
  exact eq_of_beq related

/-- Both directions of the indicator-expectation difference are bounded by the retained zero-one transport cost. -/
example :
    coinToFalseCoupling.rightMarginal.expectation
          (Purelib.Measure.Distribution.indicator fun outcome => outcome) -
        coinToFalseCoupling.leftMarginal.expectation
          (Purelib.Measure.Distribution.indicator fun outcome => outcome) ≤
      coinToFalseCoupling.transportCost
        boolMismatchCost ∧
    coinToFalseCoupling.leftMarginal.expectation
          (Purelib.Measure.Distribution.indicator fun outcome => outcome) -
        coinToFalseCoupling.rightMarginal.expectation
          (Purelib.Measure.Distribution.indicator fun outcome => outcome) ≤
      coinToFalseCoupling.transportCost
        boolMismatchCost := by
  apply coinToFalseCoupling.expectation_close_of_transportCost
  intro atom member
  rcases atom.item with ⟨left, right⟩
  cases left <;> cases right <;> decide

/-- The original fair coin assigns heads probability one half. -/
example : fairCoin.probability (fun outcome => outcome) = 1 / 2 := by
  decide

end Purelib.Examples.Measure.Distribution.Coupling.Coin.WorkedExamples

end
