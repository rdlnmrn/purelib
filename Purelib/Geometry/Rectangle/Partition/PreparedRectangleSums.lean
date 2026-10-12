module
import Purelib.Algebra.FiniteSum.Fin

import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleIndices
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Exact finite row-major reindexing for the retained Cartesian partition. -/
namespace Purelib.Geometry.Rectangle.Partition.PreparedRectangleSums

open Purelib.Algebra
open Purelib.Geometry.Rectangle.Partition

open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts (rectangles)
open Purelib.Geometry.Rectangle.Partition.PreparedRectangleIndices (rectangles_count rectangleIndex)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ sumFin_congr)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (Gaussian)

/-- Sum a finite consecutive block of Gaussian values starting at an offset.

The bounded coordinates add to the retained offset, visiting exactly the
requested count of consecutive positions in their original order. -/
private def rangeSum (count offset : Nat) (value : Nat → PreparedBoxPartitions.Gaussian) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index : Fin count => value (offset + index.val))

/-- Split the first value from a nonempty offset range sum.

The first position is the retained offset. Every following coordinate moves
to its exact successor offset in the remaining finite block. -/
private theorem rangeSum_succ (count offset : Nat) (value : Nat → PreparedBoxPartitions.Gaussian) :
    rangeSum (count + 1) offset value = value offset + rangeSum count (offset + 1) value := by
  rw [rangeSum, FiniteSum.Fin.sumFin_succ]
  change value (offset + 0) + FiniteSum.Fin.sumFin (fun index : Fin count => value (offset + (index.val + 1))) = _
  simp only [Nat.add_zero]
  congr 1
  apply FiniteSum.Fin.sumFin_congr
  intro index
  congr 1
  omega

/-- Split an offset range sum at a specified finite block length.

The original first block precedes the last block at the shifted offset.
Finite-sum recursion preserves both block lengths and every displayed value. -/
private theorem rangeSum_add (first last offset : Nat) (value : Nat → PreparedBoxPartitions.Gaussian) :
    rangeSum (first + last) offset value = rangeSum first offset value + rangeSum last (offset + first) value := by
  induction first generalizing offset with
  | zero =>
      rw [Nat.zero_add, Nat.add_zero]
      change rangeSum last offset value = 0 + rangeSum last offset value
      rw [zero_add]
  | succ first ih =>
      rw [Nat.succ_add, rangeSum_succ, ih, rangeSum_succ]
      have equal : offset + 1 + first = offset + (first + 1) := by omega
      rw [equal]
      ring1

/-- Reindex a consecutive finite range as equal-length row blocks.

Every row retains its original offset and fixed column count. The successor
row contributes that same first block before the unchanged remaining rows. -/
private theorem rangeSum_rows (rows columns offset : Nat) (value : Nat → PreparedBoxPartitions.Gaussian) :
    rangeSum (rows * columns) offset value =
      FiniteSum.Fin.sumFin (fun row : Fin rows => rangeSum columns (offset + row.val * columns) value) := by
  induction rows generalizing offset with
  | zero => rw [Nat.zero_mul]; rfl
  | succ rows ih =>
      rw [Nat.succ_mul, Nat.add_comm (rows * columns) columns, rangeSum_add, ih, FiniteSum.Fin.sumFin_succ]
      simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, Fin.val_succ]
      have shifted : FiniteSum.Fin.sumFin (fun row : Fin rows => rangeSum columns (offset + columns + row.val * columns)
        value) =
          FiniteSum.Fin.sumFin (fun row : Fin rows => rangeSum columns (offset + (row.val + 1) * columns) value) := by
        apply FiniteSum.Fin.sumFin_congr
        intro row
        congr 1
        rw [Nat.succ_mul]
        omega
      rw [← shifted]

/-- Every retained box appears once, at its original row-major position.

The retained Cartesian enumeration supplies the exact bounded position for
each interval pair. Pointwise reindexing keeps the original displayed value. -/
theorem sumFin_rectangles (horizontal vertical : List Interval)
    (value : Fin (PreparedRectangleCuts.rectangles horizontal vertical).length → PreparedBoxPartitions.Gaussian) :
    FiniteSum.Fin.sumFin value = FiniteSum.Fin.sumFin (fun column : Fin horizontal.length => FiniteSum.Fin.sumFin (fun
      row : Fin vertical.length =>
      value (PreparedRectangleIndices.rectangleIndex horizontal vertical column row))) := by
  let extended := fun index : Nat => if inside : index < (PreparedRectangleCuts.rectangles horizontal vertical).length
    then value ⟨index, inside⟩ else 0
  have original : FiniteSum.Fin.sumFin value = rangeSum (PreparedRectangleCuts.rectangles horizontal vertical).length 0
    extended := by
    apply FiniteSum.Fin.sumFin_congr
    intro index
    dsimp only [extended]
    rw [Nat.zero_add, dif_pos index.isLt]
  rw [original, PreparedRectangleIndices.rectangles_count, rangeSum_rows]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  apply FiniteSum.Fin.sumFin_congr
  intro row
  dsimp only [rangeSum, extended]
  have bounded : column.val * vertical.length + row.val < (PreparedRectangleCuts.rectangles horizontal vertical).length
    :=
    (PreparedRectangleIndices.rectangleIndex horizontal vertical column row).isLt
  rw [Nat.zero_add, dif_pos bounded]
  rfl

end Purelib.Geometry.Rectangle.Partition.PreparedRectangleSums

end
