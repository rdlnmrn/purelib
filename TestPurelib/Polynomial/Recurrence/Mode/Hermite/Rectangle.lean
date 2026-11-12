module

import Purelib.Polynomial.Recurrence.Mode.Hermite.Rectangle
import Purelib.LinearAlgebra.Matrix.NormalForm.Coordinates
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field

/-!
# Rectangular original modes over a zero-divisor coefficient ring

The actual retained constructor handles fewer rows, extra target rows, an
empty source word and zero-root source columns. Auxiliary repeated orders
complete finite target coordinates without being asserted as source modes.
-/

namespace TestPurelib.Polynomial.Recurrence.Mode.Hermite.Rectangle

open Purelib.Data renaming Vector → Vec
open Purelib.Algebra.Quadratic
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Recurrence
open Purelib.Polynomial.Recurrence.Mode
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix

/-- The same original two-coordinate coefficient algebra has a square-zero generator. -/
private abbrev Dual := Pair Purelib.Data.Gaussian.Basic.Canonical 0

/-- The original nonzero nilpotent coefficient is the retained generator. -/
private def epsilon : Dual := Pair.generator

/-- Original root blocks retain a repeated zero root and a perturbed unit root. -/
private def blocks : List (Block Dual) := [⟨0, 2, by decide⟩, ⟨1 + epsilon, 1, by decide⟩]

/-- The original two-root difference inverse table is finite structural data. -/
private def differences : SquareMatrix Dual blocks.length := matrixOfFn fun row column =>
  if row.val = column.val then 0 else if row.val = 0 then -(1 - epsilon) else 1 - epsilon

/-- Every actual distinct-block difference multiplies the same retained inverse to one. -/
private theorem units : ∀ first second : Fin blocks.length, first ≠ second →
    (Hermite.point blocks first - Hermite.point blocks second) * differences first second = 1 := by decide +kernel

/-- The original source word interleaves its two zero-root occurrence coordinates. -/
private def word : List (Fin blocks.length) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩]

/-- The first actual source coordinate retains its original word bound. -/
private def first : Fin word.length := ⟨0, by decide +kernel⟩

/-- The third actual source coordinate retains its original word bound. -/
private def third : Fin word.length := ⟨2, by decide +kernel⟩

/-- One target row uses the actual full original Hermite inverse on the right. -/
private def wide := Hermite.Rectangle.prepare blocks differences units word 1 5 (by decide)

/-- The actual wider source has exactly one computed image coordinate. -/
private theorem wide_rank : wide.normal.rank = 1 := wide.rank_eq

/-- Its two retained free original coordinates are the complete source kernel coordinates. -/
private theorem wide_kernel_count : wide.normal.kernelDimension = 2 := by
  change 3 - wide.normal.rank = 2
  rw [wide_rank]

/-- The actual first initial row retains one at the first zero-root source coordinate. -/
private theorem wide_first : wide.initial 0 first = 1 := by decide +kernel

/-- The generalized zero-root source coordinate starts one row later. -/
private theorem wide_generalized_zero : wide.initial 0 third = 0 := by decide +kernel

/-- The third actual source column retains the original transient at its first successor. -/
private theorem wide_transient : wide.values third 1 = 1 := by decide +kernel

/-- The one selected unit-root source requires two auxiliary columns for three target rows. -/
private def selected : List (Fin blocks.length) := [⟨1, by decide⟩]

/-- The only actual selected source coordinate retains its original word bound. -/
private def selectedFirst : Fin selected.length := ⟨0, by decide +kernel⟩

/-- Three target rows use one actual padded Hermite inverse on the left. -/
private def tall := Hermite.Rectangle.prepare blocks differences units selected 3 5 (by decide)

/-- The auxiliary second-order coordinate retains its actual completed-word bound. -/
private def auxiliary : Fin tall.completed.length := ⟨2, by decide +kernel⟩

/-- The actual completed coordinate word has three entries. -/
private theorem tall_completed : tall.completed.length = 3 := by decide +kernel

/-- The original source order remains zero in its same cached occurrence prefix. -/
private theorem tall_original_order : tall.occurrences.orders selectedFirst = 0 := by decide +kernel

/-- An auxiliary coordinate has order two even though the original root block has multiplicity one. -/
private theorem tall_auxiliary_order : tall.basis.occurrences.orders auxiliary = 2 := by decide +kernel

/-- The actual taller rectangle has one computed image coordinate. -/
private theorem tall_rank : tall.normal.rank = 1 := tall.rank_eq

/-- The original complementary target has two retained coordinates. -/
private theorem tall_complement_count : tall.normal.cokernelDimension = 2 := by
  change 3 - tall.normal.rank = 2
  rw [tall_rank]

/-- Its source column retains the original fourth power of one plus the nilpotent coefficient. -/
private theorem tall_later : tall.values selectedFirst 4 = 1 + 4 * epsilon := by decide +kernel

/-- The same original source root has the explicit actual inverse one minus epsilon. -/
private def shift := Hermite.Shift.prepare blocks selected tall.occurrences (.cons (1 - epsilon) .nil)
  (by decide +kernel)

/-- The exact cached source horizon follows its original shift, with no extra Hermite preparation. -/
private theorem tall_follows : Boundary.Transition tall.values shift.matrix := tall.follows shift

/-- A zero target row count retains the zero-root source without a root-unit premise. -/
private def zeroRows := Hermite.Rectangle.prepare blocks differences units [⟨0, by decide⟩] 0 3 (by decide)

/-- The zero-root source remains one free coordinate when there are no startup equations. -/
private theorem zero_rows_kernel : zeroRows.normal.kernelDimension = 1 := by decide +kernel

/-- An empty original source word supplies no padding despite extra target rows. -/
private def empty := Hermite.Rectangle.prepare blocks differences units [] 4 4 (by decide)

/-- Every original target coordinate remains complementary for the empty source. -/
private theorem empty_complement : empty.normal.cokernelDimension = 4 := by decide +kernel

end TestPurelib.Polynomial.Recurrence.Mode.Hermite.Rectangle
