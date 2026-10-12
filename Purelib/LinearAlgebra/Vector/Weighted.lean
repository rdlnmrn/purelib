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

end Purelib.LinearAlgebra.Vector.Weighted

end
