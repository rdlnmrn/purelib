module
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Data.List.OfFn.Basic

public import Purelib.Data.Fin.Cyclic.Predecessor
public import Purelib.Data.Nat.Permutation.Adjacent
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Generator.NaturalAction
public import Purelib.Topology.Knot.Braid.PositiveBand.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Fin.Bijection.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic

open Purelib.Data.Fin.Cyclic

open Purelib.Data.List

open Purelib.Data.Nat.Permutation

section
public section

/-!
# The finite permutation of a positive torus band

The ascending Artin band moves strand zero to the last position and every
other strand down by one.  This file proves that fact by evaluating each
displayed adjacent transposition.  The auxiliary arithmetic acts only on a
bounded natural prefix and is fully executable.
-/

namespace Purelib.Topology.Knot.Braid.PositiveBand.Permutation

open Purelib.Topology.Knot.Braid

/-! ## Finite-word prefixes -/

/-- The first `steps` generators of the positive band on `strands`, together with the displayed bound that makes every
generator index valid. -/
@[expose] def positivePrefix (strands steps : Nat) (bound : steps ≤ strands - 1) :
    Word strands :=
  List.ofFn fun index : Fin steps =>
    Generator.positiveGenerator ⟨index.val, index.isLt.trans_le bound⟩

/-- Extend a bounded positive band prefix by its next adjacent generator.

The supplied upper bound ensures both the shorter prefix and the appended generator retain valid indices. -/
theorem positivePrefix_succ (strands steps : Nat)
    (bound : steps + 1 ≤ strands - 1) :
    PositiveBand.Permutation.positivePrefix strands (steps + 1) bound =
      PositiveBand.Permutation.positivePrefix strands steps (by omega) ++
        [Generator.positiveGenerator ⟨steps, by omega⟩] := by
  unfold PositiveBand.Permutation.positivePrefix
  rw [OfFn.Basic.ofFn_succ_last]
  apply congrArg₂ List.append
  · apply OfFn.Basic.ofFn_congr
    intro index
    apply congrArg Generator.positiveGenerator
    apply Fin.ext
    rfl
  · apply congrArg fun generator => [generator]
    apply congrArg Generator.positiveGenerator
    apply Fin.ext
    rfl

/-- A bounded positive prefix acts by the corresponding ascending natural swaps.

The equation compares the value of each finite strand index with the executable natural-number action. -/
theorem positivePrefix_permutation_val (strands : Nat) :
    ∀ (steps : Nat) (bound : steps ≤ strands - 1)
      (index : Fin strands),
      ((PositiveBand.Permutation.positivePrefix strands steps bound).permutation.forward index).val =
        Adjacent.ascendingAction steps index.val
  | 0, _bound, _index => rfl
  | steps + 1, bound, index => by
      let earlierBound : steps ≤ strands - 1 := by omega
      let last : Generator strands :=
        Generator.positiveGenerator ⟨steps, by omega⟩
      have split : PositiveBand.Permutation.positivePrefix strands (steps + 1) bound =
          PositiveBand.Permutation.positivePrefix strands steps earlierBound ++ [last] := by
        exact PositiveBand.Permutation.positivePrefix_succ strands steps bound
      calc
        ((PositiveBand.Permutation.positivePrefix strands (steps + 1) bound).permutation.forward
            index).val =
          ((Word.permutation ([last] : Word strands)).forward
            ((PositiveBand.Permutation.positivePrefix strands steps earlierBound).permutation.forward
              index)).val := by
          rw [split]
          exact congrArg Fin.val
            (Word.permutation_append
              (PositiveBand.Permutation.positivePrefix strands steps earlierBound) [last] index)
        _ = Adjacent.adjacentNatSwap steps
            ((PositiveBand.Permutation.positivePrefix strands steps earlierBound).permutation.forward
              index).val := by
          exact Generator.NaturalAction.generator_permutation_val last
            ((PositiveBand.Permutation.positivePrefix strands steps earlierBound).permutation.forward
              index)
        _ = Adjacent.adjacentNatSwap steps (Adjacent.ascendingAction steps index.val) := by
          rw [Purelib.Topology.Knot.Braid.PositiveBand.Permutation.positivePrefix_permutation_val strands steps
            earlierBound index]
        _ = Adjacent.ascendingAction (steps + 1) index.val := rfl

/-- The full positive band is the prefix of length strands minus one. -/
theorem positiveBand_eq_prefix (strands : Nat) :
    PositiveBand.Basic.positiveBand strands = PositiveBand.Permutation.positivePrefix strands (strands - 1) (by omega)
      := by
  rfl

/-- Exact endpoint action of the displayed positive Artin band. -/
theorem positiveBand_permutation_forward {strands : Nat}
    (positive : 0 < strands) (index : Fin strands) :
    (PositiveBand.Basic.positiveBand strands).permutation.forward index =
      Predecessor.cyclicPredecessor positive index := by
  apply Fin.ext
  rw [PositiveBand.Permutation.positiveBand_eq_prefix,
    PositiveBand.Permutation.positivePrefix_permutation_val strands (strands - 1) (by omega) index,
    Adjacent.ascendingAction_formula]
  by_cases zero : index.val = 0
  · rw [if_pos zero]
    unfold Predecessor.cyclicPredecessor
    rw [dif_pos zero]
  · have within : index.val ≤ strands - 1 := by omega
    rw [if_neg zero, if_pos within, Predecessor.cyclicPredecessor_of_ne_zero positive index zero]

end Purelib.Topology.Knot.Braid.PositiveBand.Permutation

end
