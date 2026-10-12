module
import Purelib.Data.Fin
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
public import Purelib.LinearAlgebra.Matrix.Basic

section
section
public section

/-! Coordinate-unit readings of the retained disjoint finite handle form. -/
namespace Purelib.LinearAlgebra.Alternating.Handle.Basic

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

/-- An ordered pair of coordinates in the same finite dimension. -/
abbrev PivotIndices (n : Nat) := Fin n × Fin n

variable {n : Nat} {raw : List (Purelib.LinearAlgebra.Alternating.Handle.Basic.PivotIndices n)}

open Purelib.LinearAlgebra.Alternating in
/-- Equal entries in a duplicate-free handle list have equal bounded indices.

The list bounds are retained in both indexed reads. -/
theorem handleIndex_injective (raw : List (Handle.Basic.PivotIndices n)) (unique : raw.Nodup)
    (first last : Fin raw.length)
    (equal : raw[first.val]'first.isLt = raw[last.val]'last.isLt) : first = last := by
  have finite (items : List (Handle.Basic.PivotIndices n)) : items.Nodup → ∀ first last : Fin items.length,
      items[first.val]'first.isLt = items[last.val]'last.isLt → first = last := by
    induction items with
    | nil => intro _ first; exact Fin.elim0 first
    | cons head rest ih =>
        intro distinct first last
        obtain ⟨absent, tailUnique⟩ := List.pairwise_cons.mp distinct
        refine Purelib.Data.Fin.cases_induction ?_ (fun first => ?_) first
        · refine Purelib.Data.Fin.cases_induction ?_ (fun last => ?_) last
          · intro _; rfl
          · intro same
            change head = rest[last.val]'last.isLt at same
            exact (absent _ (List.getElem_mem last.isLt) same).elim
        · refine Purelib.Data.Fin.cases_induction ?_ (fun last => ?_) last
          · intro same
            change rest[first.val]'first.isLt = head at same
            exact (absent _ (List.getElem_mem first.isLt) same.symm).elim
          · intro same
            exact congrArg Fin.succ (ih tailUnique first last same)
  exact finite raw unique first last equal
end Purelib.LinearAlgebra.Alternating.Handle.Basic

end

end

section
public section

/-!
# Exact replay of integral pairing reductions

An untrusted producer supplies only oriented unit pivots. Each successful
stage retains its shear and reduced matrix; invalidity identifies a bad pivot
or an entry which fails the claimed final normal form. Rejection is only of
this submitted reduction, not of the existence of another integral basis.
-/

namespace Purelib.LinearAlgebra.Alternating.Handle.Basic

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

variable {n : Nat}

open Purelib.LinearAlgebra.Alternating
/-- Compute the signed matrix entry of a finite list of oriented handles.

Each ordered pair contributes positive one in its forward position, negative one in the reverse position, and zero
elsewhere. -/
@[expose] def handleEntry : List (Handle.Basic.PivotIndices n) → Fin n → Fin n → Int
  | [], _, _ => 0
  | indices :: remaining, row, column =>
      (if row = indices.1 ∧ column = indices.2 then 1 else 0) -
      (if row = indices.2 ∧ column = indices.1 then 1 else 0) +
        Purelib.LinearAlgebra.Alternating.Handle.Basic.handleEntry remaining row column

/-- List both coordinates of every handle in order.

The flattened list retains each first coordinate immediately before its matching last coordinate. -/
@[expose] def handleIndices (raw : List (Handle.Basic.PivotIndices n)) : List (Fin n) := raw.flatMap fun indices =>
  [indices.1, indices.2]

/-- An unused row coordinate has zero entries in the handle matrix. -/
theorem handleEntry_unused (raw : List (Handle.Basic.PivotIndices n)) (row column : Fin n)
    (unused : row ∉ Handle.Basic.handleIndices raw) : Handle.Basic.handleEntry raw row column = 0 := by
  induction raw with
  | nil => rfl
  | cons indices remaining ih =>
      have first : row ≠ indices.1 := fun equal => unused (by
        change row ∈ indices.1 :: indices.2 :: Handle.Basic.handleIndices remaining
        rw [equal]; exact List.mem_cons_self)
      have last : row ≠ indices.2 := fun equal => unused (by
        change row ∈ indices.1 :: indices.2 :: Handle.Basic.handleIndices remaining
        rw [equal]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have tail : row ∉ Handle.Basic.handleIndices remaining := fun member =>
        unused (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
      rw [Handle.Basic.handleEntry, if_neg (fun both => first both.1), if_neg (fun both => last both.1), ih tail]
      rfl
end Purelib.LinearAlgebra.Alternating.Handle.Basic

end

section
public section

/-!
# Intersection of the computed integral cycle rows

The actual cycle change of basis has the same signed unit-handle form as
the reduced matrix. These finite integer identities do not assume a
geometric genus or a preassigned ordering of branch labels.
-/

namespace Purelib.LinearAlgebra.Alternating.Handle.Basic

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

variable {n : Nat} {matrix : SquareMatrix.IntegralMatrix n} {raw : List
  (Purelib.LinearAlgebra.Alternating.Handle.Basic.PivotIndices n)}

open Purelib.LinearAlgebra.Alternating in
/-- Either coordinate of a retained handle occurs in the flattened coordinate list.

The membership witness retains the original handle occurrence and its selected coordinate in the ordered flattened list.
-/
theorem handle_coordinate_mem (pair : Handle.Basic.PivotIndices n) (member : pair ∈ raw)
    (coordinate : Fin n) (selected : coordinate ∈ [pair.1, pair.2]) : coordinate ∈ Handle.Basic.handleIndices raw :=
  open Purelib in Data.List.Flatten.mem_flatMap.mpr ⟨pair, member, selected⟩

/-- The two coordinates of a retained handle are distinct when all handle coordinates are distinct. -/
private theorem handle_distinct (disjoint : (Handle.Basic.handleIndices raw).Nodup)
    (pair : Handle.Basic.PivotIndices n) (member : pair ∈ raw) : pair.1 ≠ pair.2 := by
  induction raw with
  | nil => exact (List.not_mem_nil member).elim
  | cons head rest ih =>
      obtain ⟨firstClear, remaining⟩ := List.pairwise_cons.mp disjoint
      obtain ⟨_, tailUnique⟩ := List.pairwise_cons.mp remaining
      rcases Purelib.Data.List.Membership.mem_cons.mp member with same | tailMember
      · subst pair
        intro equal
        exact firstClear _ List.mem_cons_self equal
      · exact ih tailUnique tailMember

open Purelib.LinearAlgebra.Alternating
/-- Two handles in a disjoint list coincide or have disjoint coordinate pairs. -/
private theorem handle_separate (disjoint : (Handle.Basic.handleIndices raw).Nodup)
    (first last : Handle.Basic.PivotIndices n) (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    first = last ∨ ∀ x ∈ [first.1, first.2], ∀ y ∈ [last.1, last.2], x ≠ y := by
  induction raw with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head rest ih =>
      obtain ⟨firstClear, remaining⟩ := List.pairwise_cons.mp disjoint
      obtain ⟨lastClear, tailUnique⟩ := List.pairwise_cons.mp remaining
      have headApart (pair : Handle.Basic.PivotIndices n) (member : pair ∈ rest) :
          ∀ x ∈ [head.1, head.2], ∀ y ∈ [pair.1, pair.2], x ≠ y := by
        intro x hx y hy equal
        have tailMember := Handle.Basic.handle_coordinate_mem pair member y hy
        have xMember : x ∈ Handle.Basic.handleIndices rest := equal.symm ▸ tailMember
        rcases Purelib.Data.List.Membership.mem_cons.mp hx with same | tail
        · rw [same] at xMember
          exact firstClear _ (List.mem_cons_of_mem _ xMember) rfl
        · have same := Purelib.Data.List.Membership.mem_singleton.mp tail
          rw [same] at xMember
          exact lastClear _ xMember rfl
      rcases Purelib.Data.List.Membership.mem_cons.mp firstMember with same | firstTail
      · subst first
        rcases Purelib.Data.List.Membership.mem_cons.mp lastMember with same | lastTail
        · exact Or.inl same.symm
        · exact Or.inr (headApart last lastTail)
      · rcases Purelib.Data.List.Membership.mem_cons.mp lastMember with same | lastTail
        · subst last
          exact Or.inr (fun x hx y hy => Ne.symm (headApart first firstTail y hy x hx))
        · exact ih tailUnique firstTail lastTail

/-- No first coordinate equals a last coordinate in a disjoint handle list. -/
theorem handle_first_ne_last (disjoint : (Handle.Basic.handleIndices raw).Nodup)
    (first last : Handle.Basic.PivotIndices n) (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    first.1 ≠ last.2 := by
  rcases Handle.Basic.handle_separate disjoint first last firstMember lastMember with same | apart
  · subst last
    exact Handle.Basic.handle_distinct disjoint first firstMember
  · exact apart _ List.mem_cons_self _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- First coordinates identify retained handles in a disjoint list. -/
theorem handle_first_eq_first (disjoint : (Handle.Basic.handleIndices raw).Nodup)
    (first last : Handle.Basic.PivotIndices n) (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    first.1 = last.1 ↔ first = last := by
  constructor
  · intro equal
    rcases Handle.Basic.handle_separate disjoint first last firstMember lastMember with same | apart
    · exact same
    · exact (apart _ List.mem_cons_self _ List.mem_cons_self equal).elim
  · intro equal; exact congrArg Prod.fst equal

/-- Last coordinates identify retained handles in a disjoint list. -/
theorem handle_last_eq_last (disjoint : (Handle.Basic.handleIndices raw).Nodup)
    (first last : Handle.Basic.PivotIndices n) (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    first.2 = last.2 ↔ first = last := by
  constructor
  · intro equal
    rcases Handle.Basic.handle_separate disjoint first last firstMember lastMember with same | apart
    · exact same
    · exact (apart _ (List.mem_cons_of_mem _ List.mem_cons_self)
        _ (List.mem_cons_of_mem _ List.mem_cons_self) equal).elim
  · intro equal; exact congrArg Prod.snd equal
end Purelib.LinearAlgebra.Alternating.Handle.Basic

end
