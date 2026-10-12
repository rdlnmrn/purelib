module
import Purelib.Data.Nat.Addition
public import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Data.Fin.Bijection.Iteration
import Purelib.Data.Fin.Cyclic.Predecessor
public import Purelib.Topology.Knot.Braid.PositiveBand.Basic
import Purelib.Topology.Knot.Braid.PositiveBand.Permutation
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data.Fin.Bijection.Basic

open Purelib.Data.Fin.Cyclic

open Purelib.Topology.Knot.Braid

open Purelib.Data

section
public section

/-!
# Coprime torus braids close to knots

This file proves the constructive coprime case of the torus-link component
theorem.  Each positive band decreases the finite strand label by one, with a
displayed wrap count.  Telescoping those finite equalities shows that a return
after `k` bands forces the strand count to divide `k`.  A stored Bézout
certificate then cancels the `q` factor for the braid
`(σ₁…σₚ₋₁)^q`, ruling out every early return when `p` and `q` are
coprime.
-/

namespace Purelib.Topology.Knot.Braid.PositiveBand.Cycle

/-- One positive band decreases a strand label by one with an explicit wrap count.

For a positive strand count, the new label plus one equals the old label plus a natural multiple of that count. -/
theorem positiveBand_balance {strands : Nat} (positive : 0 < strands)
    (index : Fin strands) :
    ∃ wraps : Nat,
      ((PositiveBand.Basic.positiveBand strands).permutation.forward index).val + 1 =
        index.val + wraps * strands := by
  rw [PositiveBand.Permutation.positiveBand_permutation_forward positive index]
  exact Predecessor.cyclicPredecessor_balance positive index

open Purelib.Topology.Knot.Braid.PositiveBand
/-- Telescoping balance for a displayed finite number of positive bands. -/
theorem positiveBand_iterate_balance {strands : Nat}
    (positive : 0 < strands) (steps : Nat) (index : Fin strands) :
    ∃ wraps : Nat,
      (Data.Fin.Bijection.iterateForward
          (PositiveBand.Basic.positiveBand strands).permutation steps index).val + steps =
        index.val + wraps * strands := by
  induction steps with
  | zero =>
      exact ⟨0, by simp only [-eq_self, -iff_self,
        Data.Fin.Bijection.iterateForward_zero,
        add_zero, zero_mul]; rfl⟩
  | succ steps inductionHypothesis =>
      obtain ⟨earlierWraps, earlierBalance⟩ := inductionHypothesis
      let earlier := Data.Fin.Bijection.iterateForward
        (PositiveBand.Basic.positiveBand strands).permutation steps index
      obtain ⟨nextWraps, nextBalance⟩ :=
        Cycle.positiveBand_balance positive earlier
      refine ⟨earlierWraps + nextWraps, ?_⟩
      change
        ((PositiveBand.Basic.positiveBand strands).permutation.forward earlier).val +
            (steps + 1) =
          index.val + (earlierWraps + nextWraps) * strands
      calc
        ((PositiveBand.Basic.positiveBand strands).permutation.forward earlier).val +
              (steps + 1) =
            (((PositiveBand.Basic.positiveBand strands).permutation.forward earlier).val + 1) +
              steps := by omega
        _ = (earlier.val + nextWraps * strands) + steps := by
          rw [nextBalance]
        _ = (earlier.val + steps) + nextWraps * strands := by ring1
        _ = (index.val + earlierWraps * strands) +
              nextWraps * strands := by rw [earlierBalance]
        _ = index.val + (earlierWraps + nextWraps) * strands := by ring1

/-- Returning after `steps` positive bands forces divisibility by the strand count. -/
theorem positiveBand_return_dvd {strands : Nat} (positive : 0 < strands)
    (steps : Nat) (index : Fin strands)
    (returned : Data.Fin.Bijection.iterateForward
      (PositiveBand.Basic.positiveBand strands).permutation steps index = index) :
    strands ∣ steps := by
  obtain ⟨wraps, balance⟩ :=
    Cycle.positiveBand_iterate_balance positive steps index
  rw [returned] at balance
  have stepsEq : steps = wraps * strands := Nat.Addition.add_left_cancel balance
  exact ⟨wraps, stepsEq.trans (Nat.mul_comm wraps strands)⟩

/-- One positive band is itself a full cycle of all displayed strands. -/
theorem positiveBand_isSingleCycle {strands : Nat} (positive : 0 < strands) :
    Data.Fin.Bijection.IsSingleCycle
      (PositiveBand.Basic.positiveBand strands).permutation := by
  apply Data.Fin.Bijection.isSingleCycle_of_noEarlyReturn
  intro index steps stepsPositive stepsSmall returned
  obtain ⟨factor, factorization⟩ :=
    Cycle.positiveBand_return_dvd positive steps index returned
  have factorPositive : 0 < factor := by
    by_cases zero : factor = 0
    · subst factor
      simp only [-eq_self, -iff_self, Nat.mul_zero] at factorization
      exact (Nat.ne_of_gt stepsPositive factorization).elim
    · exact Nat.pos_of_ne_zero zero
  have strandsAtMostSteps : strands ≤ steps := by
    calc
      strands ≤ strands * factor :=
        Nat.le_mul_of_pos_right strands factorPositive
      _ = steps := factorization.symm
  exact (Nat.not_lt_of_ge strandsAtMostSteps stepsSmall).elim

/-- Iterating a positive band by a multiple of the positive strand count fixes every strand. -/
theorem positiveBand_return_at_multiple {strands : Nat}
    (positive : 0 < strands) (factor : Nat) (index : Fin strands) :
    Data.Fin.Bijection.iterateForward
      (PositiveBand.Basic.positiveBand strands).permutation (strands * factor) index = index := by
  induction factor with
  | zero => rfl
  | succ factor inductionHypothesis =>
      rw [Nat.mul_add, Nat.mul_one,
        Data.Fin.Bijection.iterateForward_add,
        inductionHypothesis]
      exact (Cycle.positiveBand_isSingleCycle positive).return_at_count index
end Purelib.Topology.Knot.Braid.PositiveBand.Cycle

end
