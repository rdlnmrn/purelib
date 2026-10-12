module

import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Vector.Update
public import Purelib.LinearAlgebra.Vector.Weighted
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra.Vector

section
@[expose] public section

/-!
# Pairing-preserving dual changes of coordinates

Congruence changes a matrix as `S C Sᵀ`; its arguments must change by
`S⁻ᵀ`, not by `S`. The formulas here use two cached finite weighted sums
per shear and work over any supplied commutative ring.
-/

namespace Purelib.LinearAlgebra.Bilinear.Matrix.Basic

variable {K : Type*} [CommRing K] {n : Nat}

/-- Evaluate a finite matrix-entry function on two structural vectors.

The double finite sum multiplies each entry by its left row coordinate and right column coordinate. -/
def bilinear (matrix : Fin n → Fin n → K) (left right :
  Data.Vector K n) : K :=
  FiniteSum.Fin.sumFin fun row => FiniteSum.Fin.sumFin fun column => matrix row column * left row * right column

open Purelib.LinearAlgebra
/-- Pointwise equal matrix entries give equal bilinear values. -/
theorem bilinear_congr {first last : Fin n → Fin n → K}
    (equal : ∀ row column, first row column = last row column) (left right : Data.Vector K n) :
    bilinear first left right = bilinear last left right := by
  apply FiniteSum.Fin.sumFin_congr; intro row
  apply FiniteSum.Fin.sumFin_congr; intro column
  rw [equal]

/-- Adding matrix entries adds their bilinear values. -/
theorem bilinear_add (first last : Fin n → Fin n → K) (left right :
  Data.Vector K n) :
    bilinear (fun row column => first row column + last row column) left right =
      bilinear first left right + bilinear last left right := by
  unfold bilinear
  calc
    _ = FiniteSum.Fin.sumFin (fun row =>
        FiniteSum.Fin.sumFin (fun column => first row column * left row * right column) +
          FiniteSum.Fin.sumFin (fun column => last row column * left row * right column)) := by
      apply FiniteSum.Fin.sumFin_congr; intro row
      exact (FiniteSum.Fin.sumFin_congr (fun column => by dsimp only; ring1)).trans (FiniteSum.Fin.sumFin_add _ _)
    _ = _ := FiniteSum.Fin.sumFin_add _ _

/-- An outer-product matrix pairs as the product of its two weighted coordinate sums. -/
theorem bilinear_outer (first last : Fin n → K) (left right :
  Data.Vector K n) :
    bilinear (fun row column => first row * last column) left right = Weighted.weighted first left
      * Weighted.weighted last right := by
  calc
    _ = FiniteSum.Fin.sumFin (fun row => (first row * left row) * FiniteSum.Fin.sumFin (fun column => last column *
      right column)) := by
      apply FiniteSum.Fin.sumFin_congr; intro row
      exact (FiniteSum.Fin.sumFin_congr (fun column => by dsimp only; ring1)).trans (FiniteSum.Fin.sumFin_mul_left _ _)
    _ = _ := FiniteSum.Fin.sumFin_mul_right _ _

/-- Subtracting matrix entries subtracts their bilinear values. -/
theorem bilinear_sub (first last : Fin n → Fin n → K) (left right :
  Data.Vector K n) :
    bilinear (fun row column => first row column - last row column) left right =
      bilinear first left right - bilinear last left right := by
  unfold bilinear
  calc
    _ = FiniteSum.Fin.sumFin (fun row =>
        FiniteSum.Fin.sumFin (fun column => first row column * left row * right column) -
          FiniteSum.Fin.sumFin (fun column => last row column * left row * right column)) := by
      apply FiniteSum.Fin.sumFin_congr; intro row
      exact (FiniteSum.Fin.sumFin_congr (fun column => by dsimp only; ring1)).trans (FiniteSum.Fin.sumFin_sub _ _)
    _ = _ := FiniteSum.Fin.sumFin_sub _ _

/-- The zero matrix-entry function has zero bilinear value. -/
theorem bilinear_zero (left right : Data.Vector K n) :
    bilinear (fun _ _ => 0) left right = 0 := by
  exact (FiniteSum.Fin.sumFin_congr (fun row =>
    (FiniteSum.Fin.sumFin_congr (fun column => by dsimp only; rw [zero_mul, zero_mul])).trans
      FiniteSum.Fin.sumFin_zero)).trans FiniteSum.Fin.sumFin_zero

/-- A single-coordinate update on the left adds the corresponding scaled row pairing. -/
theorem bilinear_bump_left (matrix : Fin n → Fin n → K) (left right :
  Data.Vector K n)
    (index : Fin n) (amount : K) :
    bilinear matrix (Update.bump left index amount) right = bilinear matrix
      left right + amount * Weighted.weighted (matrix index) right := by
  calc
    _ = FiniteSum.Fin.sumFin (fun row => FiniteSum.Fin.sumFin (fun column => matrix row column * left row * right
      column) +
        (if row = index then amount else 0) * FiniteSum.Fin.sumFin (fun column => matrix row column * right column)) :=
          by
      apply FiniteSum.Fin.sumFin_congr; intro row
      calc
        _ = FiniteSum.Fin.sumFin (fun column => matrix row column * left row * right column +
            (if row = index then amount else 0) * (matrix row column * right column)) := by
          apply FiniteSum.Fin.sumFin_congr; intro column
          rw [Update.bump_apply]
          ring1
        _ = _ := by rw [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_mul_left]
    _ = _ := by rw [FiniteSum.Fin.sumFin_add, Weighted.indicator_mul]; rfl

/-- A single-coordinate update on the right adds the corresponding scaled column pairing. -/
theorem bilinear_bump_right (matrix : Fin n → Fin n → K) (left right
  : Data.Vector K n)
    (index : Fin n) (amount : K) :
    bilinear matrix left (Update.bump right index amount) = bilinear matrix
      left right +
      amount * Weighted.weighted (fun row => matrix row index) left := by
  calc
    _ = FiniteSum.Fin.sumFin (fun row => FiniteSum.Fin.sumFin (fun column => matrix row column * left row * right
      column) +
        amount * (matrix row index * left row)) := by
      apply FiniteSum.Fin.sumFin_congr; intro row
      calc
        _ = FiniteSum.Fin.sumFin (fun column => matrix row column * left row * right column +
            (if column = index then amount else 0) * (matrix row column * left row)) := by
          apply FiniteSum.Fin.sumFin_congr; intro column
          rw [Update.bump_apply]
          ring1
        _ = _ := by rw [FiniteSum.Fin.sumFin_add, Weighted.indicator_mul]
    _ = _ := by rw [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_mul_left]; rfl

end Purelib.LinearAlgebra.Bilinear.Matrix.Basic

end
