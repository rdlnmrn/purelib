module

public import Purelib.Polynomial.Dense.Roots.Bank
public import Purelib.Data.List.Occurrences
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Replicate
import Purelib.Data.Fin

/-!
# The original coordinate word of ordered root blocks

Each original block index occurs exactly its retained multiplicity. The same
expanded word determines occurrence orders strictly below those multiplicities;
no second root enumeration or copied root scalar is introduced.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Word

open Purelib.Data.List

variable {K : Type*}

/-- Expand the original ordered blocks into their bounded repeated block indices. -/
@[expose] def expand : (blocks : List (Block K)) → List (Fin blocks.length)
  | [] => []
  | block :: tail => List.replicate block.multiplicity 0 ++ (expand tail).map Fin.succ

/-- The actual expanded word has the total retained block multiplicity. -/
theorem length_expand (blocks : List (Block K)) : (expand blocks).length = totalMultiplicity blocks := by
  induction blocks with
  | nil => rfl
  | cons block tail previous =>
      rw [expand, Append.length_append, Replicate.length_replicate, Map.length_map, previous]
      rfl

/-- Each original block occurs exactly its retained multiplicity in the expanded coordinate word. -/
theorem count (blocks : List (Block K)) (index : Fin blocks.length) :
    countBefore index (expand blocks) (expand blocks).length = (blocks[index.val]'index.isLt).multiplicity := by
  induction blocks with
  | nil => exact Fin.elim0 index
  | cons block tail previous =>
      refine Purelib.Data.Fin.cases_induction ?_ (fun index => ?_) index
      · change countBefore (0 : Fin (tail.length + 1))
          (List.replicate block.multiplicity 0 ++ (expand tail).map Fin.succ)
          (List.replicate block.multiplicity 0 ++ (expand tail).map Fin.succ).length = block.multiplicity
        rw [countBefore_append, countBefore_replicate, if_pos rfl]
        have avoids : ∀ value : Fin tail.length, value.succ ≠ (0 : Fin (tail.length + 1)) := by
          intro value equal
          have values := congrArg Fin.val equal
          change value.val + 1 = 0 at values
          exact Nat.noConfusion values
        rw [countBefore_map_avoiding Fin.succ 0 avoids, Nat.add_zero]
      · change countBefore index.succ
          (List.replicate block.multiplicity 0 ++ (expand tail).map Fin.succ)
          (List.replicate block.multiplicity 0 ++ (expand tail).map Fin.succ).length =
          (tail[index.val]'index.isLt).multiplicity
        have different : (0 : Fin (tail.length + 1)) ≠ index.succ := by
          intro equal
          have values := congrArg Fin.val equal
          change 0 = index.val + 1 at values
          exact Nat.noConfusion values
        have injective : ∀ first second : Fin tail.length, first.succ = second.succ → first = second := by
          intro first second equal
          exact Fin.ext (Nat.succ.inj (congrArg Fin.val equal))
        rw [countBefore_append, countBefore_replicate, if_neg different,
          Map.length_map, countBefore_map Fin.succ injective, Nat.zero_add]
        exact previous index

/-- Every retained occurrence order lies below its same original block multiplicity. -/
theorem order_lt (blocks : List (Block K)) (occurrences : Occurrences (expand blocks))
    (index : Fin (expand blocks).length) :
    let original := (expand blocks)[index.val]'index.isLt
    occurrences.orders index < (blocks[original.val]'original.isLt).multiplicity := by
  dsimp only
  rw [occurrences.order_spec]
  have strict := countBefore_lt_total (expand blocks) index
  rw [count] at strict
  exact strict

end Purelib.Polynomial.Dense.Roots.Word
