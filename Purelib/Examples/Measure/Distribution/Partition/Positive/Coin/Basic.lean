module
import Purelib.Data.List.Membership
import Purelib.Examples.Measure.Distribution.Coin.Basic
import Purelib.Examples.Measure.Distribution.Conditioned.Coin.Basic
public import Purelib.Examples.Measure.Distribution.Partition.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
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
import Purelib.Measure.Distribution.Conditioning.Probability
import Purelib.Measure.Distribution.Conditioning.Independence
import Purelib.Measure.Weighted.Event
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Event.Family
public import Purelib.Measure.Distribution.Partition.Independence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic

open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)
open Purelib.Examples.Measure.Distribution.Conditioned.Coin.Basic (fairCoin_true_positive)
open Purelib.Examples.Measure.Distribution.Partition.Coin.Basic (coinPartition)

/-- The two singleton coin events as a positive partition of the fair coin. -/
def positiveCoinPartition :
  PositiveEventPartition fairCoin where
  events := coinPartition.events
  disjoint := coinPartition.disjoint
  covers := coinPartition.covers
  positive := by
    intro event member
    simp only [-eq_self, -iff_self, coinPartition] at member
    have member := (Purelib.Data.List.Membership.mem_cons.mp member).elim
      (fun equal => Or.inl equal)
      (fun tail => Or.inr (Purelib.Data.List.Membership.mem_singleton.mp tail))
    rcases member with rfl | rfl <;> decide

/-- The single full event as a positive partition of the fair coin. -/
def wholeCoinPartition :
  PositiveEventPartition fairCoin where
  events := [fun _ => true]
  disjoint := by
    constructor
    · intro atom member both
      have impossible : false = true := by
        simpa only [unionEvents] using both.2
      exact Bool.noConfusion impossible
    · trivial
  covers := by
    intro atom member
    rfl
  positive := by
    intro event member
    have member := Purelib.Data.List.Membership.mem_singleton.mp member
    subst event
    decide

/-- The heads event is conditionally independent of itself on the singleton coin partition. -/
theorem coinSingletonConditionalIndependence
  :
    positiveCoinPartition.ConditionallyIndependentEvents
      (fun outcome => outcome) (fun outcome => outcome) := by
  intro condition member
  simp only [-eq_self, -iff_self, positiveCoinPartition,
    coinPartition] at member
  have member := (Purelib.Data.List.Membership.mem_cons.mp member).elim
    (fun equal => Or.inl equal)
    (fun tail => Or.inr (Purelib.Data.List.Membership.mem_singleton.mp tail))
  rcases member with rfl | rfl
  · apply (fairCoin.conditionallyIndependentEvents_iff _ _ _ _).mpr
    unfold Distribution.conditionalProbability
    decide
  · apply (fairCoin.conditionallyIndependentEvents_iff _ _ _ _).mpr
    unfold Distribution.conditionalProbability
    decide

/-- The two heads indicators satisfy the conditional product identity when conditioned on heads. -/
example : fairCoin.conditionalProbability
      (intersectionEvent (fun outcome => outcome) (fun outcome => outcome))
      (fun outcome => outcome) fairCoin_true_positive =
    fairCoin.conditionalProbability (fun outcome => outcome)
        (fun outcome => outcome) fairCoin_true_positive *
      fairCoin.conditionalProbability (fun outcome => outcome)
        (fun outcome => outcome) fairCoin_true_positive :=
          by
  unfold Distribution.conditionalProbability
  decide

end Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic

end
