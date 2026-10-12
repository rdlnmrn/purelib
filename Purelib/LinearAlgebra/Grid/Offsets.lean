module

import Purelib.Data.Fin
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Vector.Scan
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

@[expose] public section

/-!
# Finite primitive offsets with quantified non-tree defects

Anchor primitives along the first column and all horizontal tree edges.
Unlike sheet signs, approximate primitive offsets need not have exactly
zero square defect.  Every remaining vertical mismatch is a finite sum of
square defects; its squared norm grows at most quadratically in the column
count, not exponentially under repeated two-term error estimates.
-/

namespace Purelib.LinearAlgebra.Grid

open scoped Purelib.Data.Nat

open Purelib.Data.Gaussian.Basic.Canonical

namespace Offsets

/-- A structural vector with its retained finite length. -/
abbrev Vector := Data.Vector
/-- The exact Gaussian rational coefficient type. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- The exact rational coordinate type. -/
abbrev Coordinate := Fraction.Rational

end Offsets
namespace Offsets

set_option genInjectivity false in

/-- Gaussian increments on the horizontal and vertical edges of a finite rectangular grid.

The two structural arrays retain the different vertex bounds for each edge direction. -/
structure Edges (columns rows : Nat) where
  /-- The horizontal increment at each bounded column and vertex row. -/ horizontal : LinearAlgebra.Grid.Offsets.Vector
    (LinearAlgebra.Grid.Offsets.Vector LinearAlgebra.Grid.Offsets.Gaussian (rows + 1)) columns
  /-- The vertical increment at each vertex column and bounded row. -/ vertical : LinearAlgebra.Grid.Offsets.Vector
    (LinearAlgebra.Grid.Offsets.Vector LinearAlgebra.Grid.Offsets.Gaussian rows) (columns + 1)

constructive_injectivity Edges

end Offsets
namespace Offsets.Edges

/-- Compute the oriented boundary defect of one bounded grid square.

The forward horizontal and vertical increments are subtracted from their opposite boundary readings with the displayed
orientation. -/
def square {columns rows : Nat} (edges : LinearAlgebra.Grid.Offsets.Edges columns rows) (column : Fin columns)
  (row : Fin rows) : Gaussian :=
  edges.horizontal column row.castSucc + edges.vertical column.succ row -
    edges.vertical column.castSucc row - edges.horizontal column row.succ

end Offsets.Edges
set_option genInjectivity false in
/-- Cached vertex offsets checked against the original spanning-tree equations.

Horizontal edges and the first column retain their exact increment equations. The remaining square defects are bounded
separately and need not vanish. -/
structure Offsets {columns rows : Nat} (edges : LinearAlgebra.Grid.Offsets.Edges columns rows) where
  /-- The cached Gaussian offset at every bounded grid vertex. -/ values : LinearAlgebra.Grid.Offsets.Vector
    (LinearAlgebra.Grid.Offsets.Vector LinearAlgebra.Grid.Offsets.Gaussian (rows + 1)) (columns + 1)
  /-- Each forward horizontal vertex difference equals its retained edge increment. -/ horizontal : ∀ column row,
    values column.succ row = values column.castSucc row + edges.horizontal column row
  /-- Each forward vertical difference in the first column equals its retained edge increment. -/ firstVertical : ∀ row,
    values 0 row.succ = values 0 row.castSucc + edges.vertical 0 row

constructive_injectivity Offsets

namespace Offsets

end Offsets
namespace Offsets

variable {columns rows : Nat} {edges : Purelib.LinearAlgebra.Grid.Offsets.Edges columns rows}

/-- Integrate the retained edge increments along the first column and each horizontal row.

The supplied initial value anchors the cached vertex array; the result certifies exactly the spanning-tree equations. -/
def build (edges : LinearAlgebra.Grid.Offsets.Edges columns rows) (initial : Gaussian := 0) :
  Offsets edges :=
  let first := Data.Vector.Scan.scan (· + ·) initial (edges.vertical 0)
  { values := Data.Vector.Scan.propagate (· + ·) first edges.horizontal
    horizontal := Data.Vector.Scan.propagate_step (· + ·) first edges.horizontal
    firstVertical := by
      intro row
      rw [Data.Vector.Scan.propagate_zero]
      exact Data.Vector.Scan.scan_step (· + ·) (edges.vertical 0) initial row }

/-- The constructed offset at the grid origin equals the supplied initial value. -/
theorem build_origin (edges : LinearAlgebra.Grid.Offsets.Edges columns rows) (initial :
  LinearAlgebra.Grid.Offsets.Gaussian) :
    (build edges initial).values 0 0 = initial := by
  change Data.Vector.Scan.propagate (· + ·) (Data.Vector.Scan.scan (· + ·) initial (edges.vertical 0)) edges.horizontal
    0 0 = initial
  rw [Data.Vector.Scan.propagate_zero, Data.Vector.Scan.scan_zero]

/-- Compute the discrepancy between a vertical vertex difference and its retained edge increment. -/
def verticalGap (offsets : Offsets edges) (column : Fin (columns + 1)) (row : Fin rows) :
  Gaussian :=
  offsets.values column row.succ - offsets.values column row.castSucc - edges.vertical column row

/-- The vertical gap vanishes along the anchored first column. -/
theorem verticalGap_zero (offsets : Offsets edges) (row : Fin rows) : offsets.verticalGap 0
  row = 0 := by
  rw [verticalGap, offsets.firstVertical]
  ring1

/-- Moving one column forward subtracts the corresponding oriented square defect. -/
theorem verticalGap_step (offsets : Offsets edges) (column : Fin columns) (row : Fin rows) :
    offsets.verticalGap column.succ row = offsets.verticalGap column.castSucc row - edges.square column row := by
  simp only [verticalGap, offsets.horizontal,
    LinearAlgebra.Grid.Offsets.Edges.square]
  ring1

/-- Represent a vertical gap by a list of bounded square defects along its column prefix.

The retained list has exactly the column index as its length, and each term obeys the supplied squared-norm bound. -/
private theorem verticalGap_terms (offsets : Offsets edges) (bound :
  LinearAlgebra.Grid.Offsets.Coordinate)
    (squareBound : ∀ column row, Data.Gaussian.Norm.Basic.normSq (edges.square column row) ≤ bound)
    (column : Fin (columns + 1)) (row : Fin rows) :
    ∃ terms : List LinearAlgebra.Grid.Offsets.Gaussian, terms.length = column.val ∧
      (∀ term ∈ terms, Data.Gaussian.Norm.Basic.normSq term ≤ bound) ∧ offsets.verticalGap column row =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum terms := by
  induction column using Data.Fin.induction with
  | zero =>
      exact ⟨[], rfl, (fun _ member => (List.not_mem_nil member).elim), offsets.verticalGap_zero row⟩
  | succ column ih =>
      rcases ih with ⟨terms, length, bounded, equal⟩
      refine ⟨-edges.square column row :: terms, ?_, ?_, ?_⟩
      · exact congrArg (· + 1) length
      · intro term member
        rcases Data.List.Membership.mem_cons.mp member with same | member
        · rw [same, Data.Gaussian.Norm.Basic.normSq_neg]
          exact squareBound column row
        · exact bounded term member
      · rw [offsets.verticalGap_step, equal]
        change Data.Gaussian.Norm.Sum.Basic.gaussianSum terms - edges.square column row = -edges.square column row
          + Data.Gaussian.Norm.Sum.Basic.gaussianSum terms
        ring1

/-- Cauchy pays the actual number of square defects on this column prefix. -/
theorem verticalGap_bound (offsets : Offsets edges) (bound :
  LinearAlgebra.Grid.Offsets.Coordinate)
    (squareBound : ∀ column row, Data.Gaussian.Norm.Basic.normSq (edges.square column row) ≤ bound)
    (column : Fin (columns + 1)) (row : Fin rows) :
    Data.Gaussian.Norm.Basic.normSq (offsets.verticalGap column row) ≤ (column.val :
      LinearAlgebra.Grid.Offsets.Coordinate) ^ 2 * bound := by
  rcases offsets.verticalGap_terms bound squareBound column row with ⟨terms, length, bounded, equal⟩
  rw [equal]
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le terms bound bounded
  rw [length] at estimate
  exact estimate.trans_eq (by ring1)

/-- Bound every vertical gap by the squared grid width times the square-defect bound.

The supplied bound is nonnegative and applies to every bounded grid square. -/
theorem verticalGap_width_bound (offsets : Offsets edges) (bound :
  LinearAlgebra.Grid.Offsets.Coordinate) (nonnegative : 0 ≤ bound)
    (squareBound : ∀ column row, Data.Gaussian.Norm.Basic.normSq (edges.square column row) ≤ bound)
    (column : Fin (columns + 1)) (row : Fin rows) :
    Data.Gaussian.Norm.Basic.normSq (offsets.verticalGap column row) ≤ (columns :
      LinearAlgebra.Grid.Offsets.Coordinate) ^ 2 * bound := by
  have width := Fraction.Cast.Order.natCast_le_direct (Nat.le_of_lt_succ column.isLt)
  have nonnegativeIndex := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le column.val)
  exact (offsets.verticalGap_bound bound squareBound column row).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.pow_le_pow_direct nonnegativeIndex width 2) nonnegative)

end Offsets

end Purelib.LinearAlgebra.Grid
