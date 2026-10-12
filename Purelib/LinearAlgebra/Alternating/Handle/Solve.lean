module
import Purelib.Data.List.Membership
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.Flatten
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.Handle.Pairing
import Purelib.LinearAlgebra.Vector.Update
import Purelib.LinearAlgebra.Vector.Weighted
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.Ring

section

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra.Vector

section
public section

/-!
# Constructive integral row spanning from a retained unit normal form

Only the finitely many unused-coordinate kernel tests are required.
Transform the requested row, solve each disjoint unit handle, and apply
the retained transpose changes backwards. All coefficients are integers;
there is no field division, search, quotient, or choice of a preimage.
-/

namespace Purelib.LinearAlgebra.Alternating.Handle.Solve

variable {n : Nat}

/-- Construct integral coefficients solving each displayed unit handle.

The finite recursion adds the opposite coordinate to the first slot and the negative first coordinate to the last slot;
all unused slots start at zero. -/
@[expose] def handleSolve (raw : List (Handle.Basic.PivotIndices n)) (values : Data.Vector Int n) :
  Data.Vector Int n :=
  match raw with
  | [] => Data.Vector.Basic.vectorOfFn fun _ => 0
  | pair :: rest => Update.bump (Update.bump (Purelib.LinearAlgebra.Alternating.Handle.Solve.handleSolve rest values)
    pair.1 (values pair.2)) pair.2 (-values pair.1)

section
open Purelib.LinearAlgebra.Alternating
/-- The computed handle solution vanishes outside the retained handle coordinates. -/
private theorem handleSolve_unused (raw : List (Handle.Basic.PivotIndices n)) (values : Data.Vector Int n)
  (index : Fin n)
    (unused : index ∉ Handle.Basic.handleIndices raw) : Handle.Solve.handleSolve raw values index = 0 := by
  induction raw with
  | nil => exact Data.Vector.Basic.vectorOfFn_apply _ _
  | cons pair rest ih =>
      have first : index ≠ pair.1 := fun same => unused (same.symm ▸ List.mem_cons_self)
      have last : index ≠ pair.2 := fun same => unused (same.symm ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      have tail : index ∉ Handle.Basic.handleIndices rest := fun member => unused (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ member))
      rw [Handle.Solve.handleSolve, Update.bump_apply, Update.bump_apply, if_neg first, if_neg last, ih tail, add_zero,
        add_zero]

/-- On each disjoint handle, the computed solution exchanges coordinates with the required sign.

The first output is the last input and the last output is the negative first input. -/
private theorem handleSolve_handle (raw : List (Handle.Basic.PivotIndices n)) (disjoint : (Handle.Basic.handleIndices
  raw).Nodup)
    (values : Data.Vector Int n) (pair : Handle.Basic.PivotIndices n) (member : pair ∈ raw) :
    Handle.Solve.handleSolve raw values pair.1 = values pair.2 ∧ Handle.Solve.handleSolve raw values pair.2 = -values
      pair.1 := open Purelib in by
  induction raw with
  | nil => exact (List.not_mem_nil member).elim
  | cons head rest ih =>
      obtain ⟨firstFresh, restUnique⟩ := List.pairwise_cons.mp disjoint
      obtain ⟨lastFresh, tailUnique⟩ := List.pairwise_cons.mp restUnique
      have firstClear : head.1 ∉ head.2 :: Handle.Basic.handleIndices rest :=
        fun member => firstFresh _ member rfl
      have lastClear : head.2 ∉ Handle.Basic.handleIndices rest :=
        fun member => lastFresh _ member rfl
      have distinct : head.1 ≠ head.2 := fun same => firstClear (same ▸ List.mem_cons_self)
      have firstTail : head.1 ∉ Handle.Basic.handleIndices rest := fun found => firstClear (List.mem_cons_of_mem _
        found)
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst pair
        constructor
        · rw [Handle.Solve.handleSolve, Update.bump_apply, Update.bump_apply, if_pos rfl, if_neg distinct,
            Handle.Solve.handleSolve_unused rest values head.1 firstTail]
          ring1
        · rw [Handle.Solve.handleSolve, Update.bump_apply, Update.bump_apply, if_pos rfl, if_neg (Ne.symm distinct),
            Handle.Solve.handleSolve_unused rest values head.2 lastClear]
          ring1
      · have inTail (index : Fin n) (either : index = pair.1 ∨ index = pair.2) : index ∈ Handle.Basic.handleIndices rest
          :=
          Data.List.Flatten.mem_flatMap.mpr ⟨pair, member, either.elim (fun same => same.symm ▸ List.mem_cons_self)
            (fun same => same.symm ▸ List.mem_cons_of_mem _ List.mem_cons_self)⟩
        have retained (index : Fin n) (either : index = pair.1 ∨ index = pair.2) :
            Handle.Solve.handleSolve (head :: rest) values index = Handle.Solve.handleSolve rest values index := by
          have first : index ≠ head.1 := fun same => firstTail (same ▸ inTail index either)
          have last : index ≠ head.2 := fun same => lastClear (same ▸ inTail index either)
          rw [Handle.Solve.handleSolve, Update.bump_apply, Update.bump_apply, if_neg first, if_neg last, add_zero,
            add_zero]
        rw [retained _ (Or.inl rfl), retained _ (Or.inr rfl)]
        exact ih tailUnique member

end

/-- Sum coordinate products over the displayed handle list.

Both coordinates of each handle contribute in list order, retaining repetitions if the list has any. -/
private def handleWeighted (raw : List (Handle.Basic.PivotIndices n)) (weights values : Data.Vector Int n)
  : Int :=
  match raw with
  | [] => 0
  | pair :: rest => weights pair.1 * values pair.1 + weights pair.2 * values pair.2 +
    Purelib.LinearAlgebra.Alternating.Handle.Solve.handleWeighted rest weights values

/-- For disjoint handles, the handle-weighted sum equals the finite coordinate sum restricted to their support. -/
private theorem handleWeighted_eq (raw : List (Handle.Basic.PivotIndices n)) (disjoint : (Handle.Basic.handleIndices
  raw).Nodup)
    (weights values : Data.Vector Int n) :
    Purelib.LinearAlgebra.Alternating.Handle.Solve.handleWeighted raw weights values =
      Purelib.Algebra.FiniteSum.Fin.sumFin (fun index => if index ∈ Handle.Basic.handleIndices raw then weights index *
      values index else 0) := open Purelib.Algebra in by
  induction raw with
  | nil => exact FiniteSum.Fin.sumFin_zero.symm
  | cons pair rest ih =>
      obtain ⟨firstFresh, restUnique⟩ := List.pairwise_cons.mp disjoint
      obtain ⟨lastFresh, tailUnique⟩ := List.pairwise_cons.mp restUnique
      have firstClear : pair.1 ∉ pair.2 :: Handle.Basic.handleIndices rest :=
        fun member => firstFresh _ member rfl
      have lastClear : pair.2 ∉ Handle.Basic.handleIndices rest :=
        fun member => lastFresh _ member rfl
      have firstTail : pair.1 ∉ Handle.Basic.handleIndices rest := fun member => firstClear (List.mem_cons_of_mem _
        member)
      change pair.2 ∉ Handle.Basic.handleIndices rest at lastClear
      have distinct : pair.1 ≠ pair.2 := fun same => firstClear (same ▸ List.mem_cons_self)
      have split (index : Fin n) :
          (if index ∈ Handle.Basic.handleIndices (pair :: rest) then weights index * values index else 0) =
            (if index = pair.1 then weights index * values index else 0) +
            (if index = pair.2 then weights index * values index else 0) +
            (if index ∈ Handle.Basic.handleIndices rest then weights index * values index else 0) := by
        by_cases first : index = pair.1
        · subst index
          have present : pair.1 ∈ Handle.Basic.handleIndices (pair :: rest) := List.mem_cons_self
          rw [if_pos present, if_pos rfl, if_neg distinct, if_neg firstTail, add_zero, add_zero]
        · by_cases last : index = pair.2
          · subst index
            have present : pair.2 ∈ Handle.Basic.handleIndices (pair :: rest) := List.mem_cons_of_mem _
              List.mem_cons_self
            rw [if_pos present, if_neg first, if_pos rfl, if_neg lastClear, zero_add, add_zero]
          · have member : index ∈ Handle.Basic.handleIndices (pair :: rest) ↔ index ∈ Handle.Basic.handleIndices rest :=
              by
              change index ∈ pair.1 :: pair.2 :: Handle.Basic.handleIndices rest ↔ _
              constructor
              · intro found
                cases found with
                | head => exact (first rfl).elim
                | tail _ found =>
                    cases found with
                    | head => exact (last rfl).elim
                    | tail _ found => exact found
              · intro found
                exact List.Mem.tail _ (List.Mem.tail _ found)
            by_cases present : index ∈ Handle.Basic.handleIndices rest
            · rw [if_pos (member.mpr present), if_neg first, if_neg last, if_pos present, zero_add, zero_add]
            · rw [if_neg (fun found => present (member.mp found)), if_neg first, if_neg last,
                if_neg present, zero_add, zero_add]
      rw [FiniteSum.Fin.sumFin_congr split, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_add,
        FiniteSum.Fin.sumFin_ite_eq, FiniteSum.Fin.sumFin_ite_eq, ← ih tailUnique]
      rfl

open Purelib.LinearAlgebra.Alternating in
/-- The computed handle solution represents every supported integral weighted pairing.

Disjointness and vanishing weights outside the retained coordinates are the only support assumptions. -/
theorem handleSolve_pairing (raw : List (Handle.Basic.PivotIndices n)) (disjoint : (Handle.Basic.handleIndices
  raw).Nodup)
    (weights values : Data.Vector Int n) (supported : ∀ index, index ∉ Handle.Basic.handleIndices raw →
      weights index = 0) :
    Handle.Pairing.handlePairing raw (Handle.Solve.handleSolve raw weights) values = Weighted.weighted weights values :=
      open Purelib.Algebra in by
  have evaluate (part : List (Handle.Basic.PivotIndices n)) (included : ∀ pair ∈ part, pair ∈ raw) :
      Handle.Pairing.handlePairing part (Handle.Solve.handleSolve raw weights) values = Handle.Solve.handleWeighted part
        weights values := by
    induction part with
    | nil => rfl
    | cons pair rest ih =>
        have atHandle := Handle.Solve.handleSolve_handle raw disjoint weights pair (included pair List.mem_cons_self)
        rw [Handle.Pairing.handlePairing, atHandle.1, atHandle.2, ih (fun pair member => included pair
          (List.mem_cons_of_mem _ member)), Handle.Solve.handleWeighted]
        ring1
  rw [evaluate raw (fun _ member => member), Handle.Solve.handleWeighted_eq raw disjoint]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  by_cases member : index ∈ Handle.Basic.handleIndices raw
  · rw [if_pos member]
  · rw [if_neg member, supported index member, zero_mul]
end Purelib.LinearAlgebra.Alternating.Handle.Solve

end

end
