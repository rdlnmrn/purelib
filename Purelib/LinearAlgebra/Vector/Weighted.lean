module

public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Vector.Update
import Mathlib.Tactic.TypeStar
import Purelib.Tactic.Ring

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_add sumFin_congr sumFin_ite_eq sumFin_mul_left)

open _root_.Purelib.Data renaming Vector -> Vec

open Purelib.LinearAlgebra.Vector.Update (bump bump_apply)

section
@[expose] public section

/-!
# Pairing-preserving dual changes of coordinates

Congruence changes a matrix as `S C Sᵀ`; its arguments must change by
`S⁻ᵀ`, not by `S`. The formulas here use two cached finite weighted sums
per shear and work over any supplied commutative ring.
-/

namespace Purelib.LinearAlgebra.Vector.Weighted

variable {K : Type*} [CommRing K] {n : Nat}

/-- Sum the coordinate products of weights and a structural vector.

The bounded index type fixes the number of entries, and the supplied commutative ring determines addition and
multiplication. -/
def weighted (weights : Fin n → K) (values : Vec K n) : K :=
  sumFin fun index => weights index * values index

open _root_.Purelib.LinearAlgebra.Vector.Weighted (weighted) in
/-- Scaling every weight scales the weighted vector sum.

A common left factor can be taken outside the finite sum over the same vector entries in any commutative ring. -/
theorem weighted_scale (scale : K) (weights : Fin n → K) (values : Vec K n)
  :
    weighted (fun index => scale * weights index) values = scale * weighted weights values := by
  exact (sumFin_congr (fun index => by dsimp only; ring1)).trans (sumFin_mul_left _ _)

/-- An indicator weight selects one term of a finite sum.

The weight equals the supplied amount at the specified bounded index and zero elsewhere, so the result is that amount
times the selected value. -/
public theorem indicator_mul (index : Fin n) (amount : K) (values : Fin n
  → K) :
    sumFin (fun position => (if position = index then amount else 0) * values position) = amount * values index := by
  calc
    _ = sumFin (fun position => if position = index then amount * values position else 0) := by
      apply sumFin_congr; intro position
      by_cases same : position = index
      · rw [if_pos same, if_pos same]
      · rw [if_neg same, if_neg same, zero_mul]
    _ = _ := sumFin_ite_eq index _

open _root_.Purelib.LinearAlgebra.Vector.Weighted (indicator_mul weighted)
/-- A unit weight at one index reads the corresponding vector entry.

All other weights are zero, and the retained bounded index selects an entry of the original structural vector. -/
theorem weighted_unit (index : Fin n) (values : Vec K n) :
    weighted (fun position => if position = index then 1 else 0) values = values index := by
  rw [weighted, indicator_mul, one_mul]

/-- Changing one vector entry changes its weighted sum by the corresponding weighted increment.

Adding an amount at the selected bounded index adds that amount times its weight to the original sum, while preserving
all other entries. -/
theorem weighted_bump (weights : Fin n → K) (values : Vec K n) (index : Fin
  n) (amount : K) :
    weighted weights (bump values index amount) = weighted weights values + amount * weights index := by
  calc
    _ = sumFin (fun position => weights position * values position +
        (if position = index then amount else 0) * weights position) := by
      apply sumFin_congr; intro position
      rw [bump_apply]
      ring1
    _ = _ := by rw [sumFin_add, indicator_mul]; rfl

/-- Remove the weighted component at an original bounded unit-weight pivot.

The weighted value is computed once and added with its opposite sign at the
selected coordinate. Every other coefficient retains its original value. -/
def removePivot (weights : Fin n → K) (values : Vec K n) (pivot : Fin n) : Vec K n :=
  let retained := weighted weights values
  bump values pivot (-retained)

/-- A unit-weight pivot correction has zero weighted value. -/
theorem weighted_removePivot (weights : Fin n → K) (values : Vec K n) (pivot : Fin n)
    (unit : weights pivot = 1) :
    weighted weights (removePivot weights values pivot) = 0 := by
  rewrite [removePivot, weighted_bump, unit, mul_one]
  ring1

/-- The pivot correction preserves each actual nonpivot entry. -/
theorem removePivot_other (weights : Fin n → K) (values : Vec K n) (pivot position : Fin n)
    (different : position ≠ pivot) :
    removePivot weights values pivot position = values position := by
  rewrite [removePivot, bump_apply, if_neg different]
  exact add_zero _

/-- The selected pivot loses exactly the original cached weighted value. -/
theorem removePivot_same (weights : Fin n → K) (values : Vec K n) (pivot : Fin n) :
    removePivot weights values pivot pivot = values pivot - weighted weights values := by
  rewrite [removePivot, bump_apply, if_pos rfl]
  ring1

/-- A vector already in the weighted kernel is retained as the complete same vector. -/
theorem removePivot_of_zero (weights : Fin n → K) (values : Vec K n) (pivot : Fin n)
    (zero : weighted weights values = 0) : removePivot weights values pivot = values := by
  apply Purelib.Data.Vector.Basic.vector_ext
  intro position
  rewrite [removePivot, zero, neg_zero, bump_apply]
  by_cases same : position = pivot
  · rewrite [if_pos same]
    exact add_zero _
  · rewrite [if_neg same]
    exact add_zero _

/-- Matching weighted values and all nonpivot entries identify the complete original vectors.

The selected coordinate has weight one. Its difference is isolated by the
original single-coordinate update; no function extensionality is needed. -/
theorem eq_of_weighted_eq_of_other (weights : Fin n → K) (left right : Vec K n) (pivot : Fin n)
    (unit : weights pivot = 1) (same : weighted weights left = weighted weights right)
    (other : ∀ position, position ≠ pivot → left position = right position) : left = right := by
  have rightUpdate : right = bump left pivot (right pivot - left pivot) := by
    apply Purelib.Data.Vector.Basic.vector_ext
    intro position
    rewrite [bump_apply]
    by_cases selected : position = pivot
    · subst position
      rewrite [if_pos rfl]
      ring1
    · rewrite [if_neg selected]
      exact (other position selected).symm.trans (add_zero _).symm
  have weightedUpdate := congrArg (weighted weights) rightUpdate
  rewrite [weighted_bump, unit, mul_one] at weightedUpdate
  have difference : right pivot - left pivot = 0 := by
    calc
      _ = (weighted weights left + (right pivot - left pivot)) - weighted weights left := by ring1
      _ = weighted weights right - weighted weights left :=
        congrArg (fun value => value - weighted weights left) weightedUpdate.symm
      _ = 0 := by rewrite [same]; ring1
  apply Purelib.Data.Vector.Basic.vector_ext
  intro position
  by_cases selected : position = pivot
  · subst position
    calc
      _ = right pivot - (right pivot - left pivot) := by ring1
      _ = _ := by rewrite [difference]; ring1
  · exact other position selected

end Purelib.LinearAlgebra.Vector.Weighted

end
