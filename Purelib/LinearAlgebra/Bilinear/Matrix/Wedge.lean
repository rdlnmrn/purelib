module

import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Bilinear.Matrix.Basic
import Purelib.LinearAlgebra.Vector.Weighted
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra.Vector

@[expose] public section

/-! Finite bilinear evaluation of a displayed sum of row wedges. -/
namespace Purelib.LinearAlgebra.Bilinear.Matrix.Wedge

open Purelib.LinearAlgebra
variable {K : Type*} [CommRing K] {n : Nat}

/-- Bilinear evaluation commutes with a finite indexed sum of matrix entries. -/
theorem bilinear_sum {count : Nat} (matrices : Fin count → Fin n → Fin n → K)
    (left right : Data.Vector K n) :
    Bilinear.Matrix.Basic.bilinear (fun row column => FiniteSum.Fin.sumFin (fun index => matrices index row column))
      left right =
      FiniteSum.Fin.sumFin (fun index => Bilinear.Matrix.Basic.bilinear (matrices index) left right) := by
  induction count with
  | zero => exact Bilinear.Matrix.Basic.bilinear_zero left right
  | succ count ih =>
      apply (Bilinear.Matrix.Basic.bilinear_congr (fun row column => FiniteSum.Fin.sumFin_succ (fun index => matrices
        index row column)) left right).trans
      rw [Bilinear.Matrix.Basic.bilinear_add, ih, FiniteSum.Fin.sumFin_succ]

/-- Evaluate a row wedge as the difference of the two products of weighted sums. -/
theorem bilinear_wedge (first last : Fin n → K) (left right : Data.Vector K n) :
    Bilinear.Matrix.Basic.bilinear (fun row column => first row * last column - last row * first column) left right =
      Weighted.weighted first left * Weighted.weighted last right - Weighted.weighted last left * Weighted.weighted
        first right := by
  rw [Bilinear.Matrix.Basic.bilinear_sub, Bilinear.Matrix.Basic.bilinear_outer, Bilinear.Matrix.Basic.bilinear_outer]

end Purelib.LinearAlgebra.Bilinear.Matrix.Wedge
