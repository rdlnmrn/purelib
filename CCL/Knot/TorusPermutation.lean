import mathlib.Data.ConstructiveList
import CCL.Knot.TorusBraid

/-!
# The finite permutation of a positive torus band

The ascending Artin band moves strand zero to the last position and every
other strand down by one.  This file proves that fact by evaluating each
displayed adjacent transposition.  The auxiliary arithmetic acts only on a
bounded natural prefix and is fully executable.
-/

namespace CCL.Knot.TorusPermutation

open CCL.Knot.FiniteBraid
open CCL.Knot.TorusBraid

/-! ## Natural-index evaluation -/

/-- Adjacent transposition on natural labels. -/
def adjacentNatSwap (pivot value : Nat) : Nat :=
  if value = pivot then pivot + 1
  else if value = pivot + 1 then pivot
  else value

/-- Execute the ascending swaps `0,1,…,steps-1`. -/
def ascendingAction : Nat → Nat → Nat
  | 0, value => value
  | steps + 1, value => adjacentNatSwap steps (ascendingAction steps value)

theorem ascendingAction_formula : ∀ (steps value : Nat),
    ascendingAction steps value =
      if value = 0 then steps
      else if value ≤ steps then value - 1 else value
  | 0, value => by
      by_cases zero : value = 0
      · subst value
        rfl
      · have notLe : ¬value ≤ 0 := by omega
        simp only [ascendingAction, zero, notLe, ↓reduceIte]
  | steps + 1, value => by
      rw [ascendingAction, ascendingAction_formula]
      by_cases zero : value = 0
      · subst value
        simp [adjacentNatSwap]
      · by_cases within : value ≤ steps
        · have withinSucc : value ≤ steps + 1 := by omega
          have predecessorNePivot : value - 1 ≠ steps := by omega
          have predecessorNeNext : value - 1 ≠ steps + 1 := by omega
          simp only [zero, within, withinSucc, ↓reduceIte,
            adjacentNatSwap, predecessorNePivot, predecessorNeNext]
        · by_cases atNext : value = steps + 1
          · subst value
            have nonzero : steps + 1 ≠ 0 := by omega
            have notWithin : ¬steps + 1 ≤ steps := by omega
            have withinSucc : steps + 1 ≤ steps + 1 := Nat.le_refl _
            have nextNePivot : steps + 1 ≠ steps := by omega
            have predecessor : steps + 1 - 1 = steps := by omega
            simp only [nonzero, notWithin, withinSucc, nextNePivot,
              predecessor, adjacentNatSwap, ↓reduceIte]
          · have aboveNext : steps + 1 < value := by omega
            have notWithinSucc : ¬value ≤ steps + 1 := by omega
            have valueNePivot : value ≠ steps := by omega
            simp only [zero, within, notWithinSucc, adjacentNatSwap,
              valueNePivot, atNext, ↓reduceIte]

/-! ## Finite-word prefixes -/

/-- The first `steps` generators of the positive band on `strands`, together
with the displayed bound that makes every generator index valid. -/
def positivePrefix (strands steps : Nat) (bound : steps ≤ strands - 1) :
    Word strands :=
  List.ofFn fun index : Fin steps =>
    positiveGenerator ⟨index.val, index.isLt.trans_le bound⟩

theorem positivePrefix_succ (strands steps : Nat)
    (bound : steps + 1 ≤ strands - 1) :
    positivePrefix strands (steps + 1) bound =
      positivePrefix strands steps (by omega) ++
        [positiveGenerator ⟨steps, by omega⟩] := by
  unfold positivePrefix
  rw [QuotientFreeList.ofFn_succ_last]
  apply congrArg₂ List.append
  · apply QuotientFreeList.ofFn_congr
    intro index
    apply congrArg positiveGenerator
    apply Fin.ext
    rfl
  · apply congrArg fun generator => [generator]
    apply congrArg positiveGenerator
    apply Fin.ext
    rfl

theorem generator_permutation_val {strands : Nat}
    (generator : Generator strands) (index : Fin strands) :
    (generator.permutation.forward index).val =
      adjacentNatSwap generator.index.val index.val := by
  change (swapIndices generator.left generator.right index).val =
    adjacentNatSwap generator.index.val index.val
  by_cases atLeft : index.val = generator.index.val
  · have equal : index = generator.left := Fin.ext atLeft
    subst index
    rw [swapIndices_left]
    change generator.index.val + 1 =
      adjacentNatSwap generator.index.val generator.index.val
    unfold adjacentNatSwap
    rw [if_pos rfl]
  · by_cases atRight : index.val = generator.index.val + 1
    · have equal : index = generator.right := Fin.ext atRight
      subst index
      rw [swapIndices_right]
      change generator.index.val =
        adjacentNatSwap generator.index.val (generator.index.val + 1)
      unfold adjacentNatSwap
      rw [if_neg (by omega), if_pos rfl]
    · have notLeft : index ≠ generator.left := by
        intro equal
        exact atLeft (congrArg Fin.val equal)
      have notRight : index ≠ generator.right := by
        intro equal
        exact atRight (congrArg Fin.val equal)
      rw [swapIndices_of_ne notLeft notRight]
      change index.val = adjacentNatSwap generator.index.val index.val
      unfold adjacentNatSwap
      rw [if_neg atLeft, if_neg atRight]

theorem positivePrefix_permutation_val (strands : Nat) :
    ∀ (steps : Nat) (bound : steps ≤ strands - 1)
      (index : Fin strands),
      ((positivePrefix strands steps bound).permutation.forward index).val =
        ascendingAction steps index.val
  | 0, _bound, _index => rfl
  | steps + 1, bound, index => by
      let earlierBound : steps ≤ strands - 1 := by omega
      let last : Generator strands :=
        positiveGenerator ⟨steps, by omega⟩
      have split : positivePrefix strands (steps + 1) bound =
          positivePrefix strands steps earlierBound ++ [last] := by
        exact positivePrefix_succ strands steps bound
      calc
        ((positivePrefix strands (steps + 1) bound).permutation.forward
            index).val =
          ((CCL.Knot.FiniteBraid.Word.permutation ([last] : Word strands)).forward
            ((positivePrefix strands steps earlierBound).permutation.forward
              index)).val := by
          rw [split]
          exact congrArg Fin.val
            (CCL.Knot.FiniteBraid.Word.permutation_append
              (positivePrefix strands steps earlierBound) [last] index)
        _ = adjacentNatSwap steps
            ((positivePrefix strands steps earlierBound).permutation.forward
              index).val := by
          exact generator_permutation_val last
            ((positivePrefix strands steps earlierBound).permutation.forward
              index)
        _ = adjacentNatSwap steps (ascendingAction steps index.val) := by
          rw [positivePrefix_permutation_val strands steps earlierBound index]
        _ = ascendingAction (steps + 1) index.val := rfl

theorem positiveBand_eq_prefix (strands : Nat) :
    positiveBand strands = positivePrefix strands (strands - 1) (by omega) := by
  rfl

/-! ## The standard cyclic predecessor -/

def cyclicPredecessor {count : Nat} (positive : 0 < count)
    (index : Fin count) : Fin count :=
  if zero : index.val = 0 then
    ⟨count - 1, by omega⟩
  else
    ⟨index.val - 1, by omega⟩

@[simp] theorem cyclicPredecessor_zero {count : Nat} (positive : 0 < count) :
    cyclicPredecessor positive ⟨0, positive⟩ = ⟨count - 1, by omega⟩ := by
  simp only [cyclicPredecessor, ↓reduceDIte]

theorem cyclicPredecessor_of_ne_zero {count : Nat} (positive : 0 < count)
    (index : Fin count) (nonzero : index.val ≠ 0) :
    cyclicPredecessor positive index = ⟨index.val - 1, by omega⟩ := by
  simp only [cyclicPredecessor, nonzero, ↓reduceDIte]

/-- Exact endpoint action of the displayed positive Artin band. -/
theorem positiveBand_permutation_forward {strands : Nat}
    (positive : 0 < strands) (index : Fin strands) :
    (positiveBand strands).permutation.forward index =
      cyclicPredecessor positive index := by
  apply Fin.ext
  rw [positiveBand_eq_prefix,
    positivePrefix_permutation_val strands (strands - 1) (by omega) index,
    ascendingAction_formula]
  by_cases zero : index.val = 0
  · simp only [zero, cyclicPredecessor, ↓reduceIte, ↓reduceDIte]
  · have within : index.val ≤ strands - 1 := by omega
    simp only [zero, within, cyclicPredecessor, ↓reduceIte, ↓reduceDIte]

end CCL.Knot.TorusPermutation
