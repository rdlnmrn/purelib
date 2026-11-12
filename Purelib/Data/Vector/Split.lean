module

public import Purelib.Data.Vector.Basic
import Purelib.Tactic.QuotientFreeOmega

/-!
# Splitting structural vectors at an original finite coordinate

Both pieces retain their original bounded indices. Joining their entries
recovers the complete original structural vector, including empty pieces.
-/

public section

namespace Purelib.Data.Vector.Split

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic

variable {K : Type*} {size cut : Nat}

/-- Retain the entries before the supplied cut in their original order. -/
@[expose] def take (bound : cut ≤ size) (values : Vec K size) : Vec K cut :=
  vectorOfFn fun index => values ⟨index.val, Nat.lt_of_lt_of_le index.isLt bound⟩

/-- Retain the entries at and after the supplied cut in their original order. -/
@[expose] def drop (bound : cut ≤ size) (values : Vec K size) : Vec K (size - cut) :=
  vectorOfFn fun index => values ⟨cut + index.val, by have := index.isLt; omega0⟩

/-- Join the two original ordered coordinate blocks at the supplied cut. -/
@[expose] def join (bound : cut ≤ size) (first : Vec K cut) (second : Vec K (size - cut)) :
    Vec K size :=
  vectorOfFn fun index =>
    if before : index.val < cut then first ⟨index.val, before⟩
    else second ⟨index.val - cut, by have := index.isLt; omega0⟩

/-- Prefix lookup reads the same original bounded coordinate. -/
theorem take_apply (bound : cut ≤ size) (values : Vec K size) (index : Fin cut) :
    take bound values index = values ⟨index.val, Nat.lt_of_lt_of_le index.isLt bound⟩ :=
  vectorOfFn_apply _ _

/-- Suffix lookup reads the original coordinate shifted by the retained cut. -/
theorem drop_apply (bound : cut ≤ size) (values : Vec K size) (index : Fin (size - cut)) :
    drop bound values index = values ⟨cut + index.val, by have := index.isLt; omega0⟩ :=
  vectorOfFn_apply _ _

/-- Joined lookup before the cut consumes the original first block. -/
theorem join_apply_take (bound : cut ≤ size) (first : Vec K cut) (second : Vec K (size - cut))
    (index : Fin cut) :
    join bound first second ⟨index.val, Nat.lt_of_lt_of_le index.isLt bound⟩ = first index := by
  unfold join
  rw [vectorOfFn_apply, dif_pos index.isLt]

/-- Joined lookup after the cut consumes the original second block. -/
theorem join_apply_drop (bound : cut ≤ size) (first : Vec K cut) (second : Vec K (size - cut))
    (index : Fin (size - cut)) :
    join bound first second ⟨cut + index.val, by have := index.isLt; omega0⟩ = second index := by
  unfold join
  rw [vectorOfFn_apply, dif_neg (by change ¬cut + index.val < cut; omega0)]
  congr 1
  apply Fin.ext
  change cut + index.val - cut = index.val
  omega0

/-- Splitting a joined vector recovers its exact retained first block. -/
theorem take_join (bound : cut ≤ size) (first : Vec K cut) (second : Vec K (size - cut)) :
    take bound (join bound first second) = first := by
  apply vector_ext
  intro index
  rw [take_apply, join_apply_take]

/-- Splitting a joined vector recovers its exact retained second block. -/
theorem drop_join (bound : cut ≤ size) (first : Vec K cut) (second : Vec K (size - cut)) :
    drop bound (join bound first second) = second := by
  apply vector_ext
  intro index
  rw [drop_apply, join_apply_drop]

/-- Joining both computed pieces recovers the complete original structural vector. -/
theorem join_split (bound : cut ≤ size) (values : Vec K size) :
    join bound (take bound values) (drop bound values) = values := by
  apply vector_ext
  intro index
  unfold join
  rw [vectorOfFn_apply]
  split
  · rw [take_apply]
  · rw [drop_apply]
    congr 1
    apply Fin.ext
    change cut + (index.val - cut) = index.val
    omega0

end Purelib.Data.Vector.Split
