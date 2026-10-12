module
import Purelib.Tactic.QuotientFreeOmega

section
public section

/-!
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

namespace Purelib.Data.Fin.AdjacentTriple

/-! ### The three-strand cell -/

/-- The first index of three consecutive positions.

A starting index in Fin (strands - 2) supplies the retained bound for the position index.val in Fin strands. -/
@[expose] def tripleLeft {strands : Nat} (index : Fin (strands - 2)) : Fin
  strands :=
  ⟨index.val, Nat.lt_of_lt_of_le index.isLt (Nat.sub_le _ _)⟩

/-- The middle index of three consecutive positions.

A starting index in Fin (strands - 2) supplies the retained bound for the position index.val + 1 in Fin strands. -/
@[expose] def tripleMiddle {strands : Nat} (index : Fin (strands - 2)) : Fin
  strands :=
  ⟨index.val + 1, Nat.lt_trans (Nat.lt_succ_self _)
    (show index.val + 2 < strands from (by have retained : index.val < strands - 2 := index.isLt; omega0))⟩

/-- The last index of three consecutive positions.

A starting index in Fin (strands - 2) supplies the retained bound for the position index.val + 2 in Fin strands. -/
@[expose] def tripleRight {strands : Nat} (index : Fin (strands - 2)) : Fin
  strands :=
  ⟨index.val + 2, (by have retained : index.val < strands - 2 := index.isLt; omega0)⟩

open Purelib.Data.Fin
/-- The first adjacent position has natural value index.val. -/
@[simp] theorem tripleLeft_val {strands : Nat}
    (index : Fin (strands - 2)) : (tripleLeft index).val = index.val := rfl

/-- The middle adjacent position has natural value index.val + 1. -/
@[simp] theorem tripleMiddle_val {strands : Nat}
    (index : Fin (strands - 2)) :
    (tripleMiddle index).val = index.val + 1 := rfl

/-- The last adjacent position has natural value index.val + 2. -/
@[simp] theorem tripleRight_val {strands : Nat}
    (index : Fin (strands - 2)) :
    (tripleRight index).val = index.val + 2 := rfl

/-- The first and middle positions of an adjacent triple are distinct. -/
theorem tripleLeft_ne_middle {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleLeft index ≠ tripleMiddle index := by
  intro equal
  have values := congrArg Fin.val equal
  change index.val = index.val + 1 at values
  exact (Nat.ne_of_lt (Nat.lt_succ_self _)) values

/-- The first and last positions of an adjacent triple are distinct. -/
theorem tripleLeft_ne_right {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleLeft index ≠ tripleRight index := by
  intro equal
  have values := congrArg Fin.val equal
  change index.val = index.val + 2 at values
  exact (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _))) values

/-- The middle and last positions of an adjacent triple are distinct. -/
theorem tripleMiddle_ne_right {strands : Nat}
    (index : Fin (strands - 2)) :
    tripleMiddle index ≠ tripleRight index := by
  intro equal
  have values := congrArg Fin.val equal
  change index.val + 1 = index.val + 2 at values
  exact (Nat.ne_of_lt (Nat.lt_succ_self _)) values

end Purelib.Data.Fin.AdjacentTriple

end
