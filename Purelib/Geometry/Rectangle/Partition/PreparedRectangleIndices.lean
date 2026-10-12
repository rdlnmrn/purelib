module
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.Fin
import Purelib.Data.Nat.Multiplication

public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Init.Data.Nat.Basic
import Init.Prelude
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Executable row-major indices of the actual Cartesian box partition. -/
namespace Purelib.Geometry.Rectangle.Partition.PreparedRectangleIndices

open Purelib

open Purelib.Geometry.Rectangle.Partition

open Purelib.Data.List
open Purelib.Data.Nat

open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts (rectangles intervalBox)

/-- The Cartesian rectangle list has the product of the two axis lengths.

The retained Cartesian list is the ordered flat-map of the horizontal intervals and mapped vertical intervals. Its
structural product-length certificate counts the same original occurrences. -/
theorem rectangles_count (horizontal vertical : List Interval) :
    (PreparedRectangleCuts.rectangles horizontal vertical).length = horizontal.length * vertical.length := by
  exact Flatten.length_flatMap_map horizontal vertical PreparedRectangleCuts.intervalBox

/-- Compute the retained rectangle index from its column and row.

The offset is column times vertical length plus row, with a bound in the actual Cartesian box list. -/
@[expose] def rectangleIndex (horizontal vertical : List Interval) (column : Fin horizontal.length) (row : Fin
  vertical.length) :
    Fin (PreparedRectangleCuts.rectangles horizontal vertical).length :=
  ⟨column.val * vertical.length + row.val, by
    rw [Geometry.Rectangle.Partition.PreparedRectangleIndices.rectangles_count]
    have bounded := Nat.mul_le_mul_right vertical.length (Nat.succ_le_of_lt column.isLt)
    rw [Nat.succ_mul] at bounded
    omega⟩

/-- The computed rectangle index reads exactly the box of the supplied axis intervals.

Structural column splitting reads the exact original row in the retained head column or unchanged tail. Explicit bounded
append and map readbacks preserve the row-major offset and original interval owners. -/
theorem rectangle_at (horizontal vertical : List Interval) (column : Fin horizontal.length) (row : Fin vertical.length)
  :
    (PreparedRectangleCuts.rectangles horizontal
      vertical)[Geometry.Rectangle.Partition.PreparedRectangleIndices.rectangleIndex horizontal vertical column row] =
      PreparedRectangleCuts.intervalBox horizontal[column] vertical[row] := by
  induction horizontal with
  | nil => exact Fin.elim0 column
  | cons first rest ih =>
      refine Data.Fin.cases_induction ?_ (fun column => ?_) column
      · let head := vertical.map (PreparedRectangleCuts.intervalBox first)
        have headBound : row.val < head.length := by
          rw [Map.length_map]
          exact row.isLt
        have combinedBound : row.val < (head ++ PreparedRectangleCuts.rectangles rest vertical).length := by
          rw [Append.length_append]
          exact Nat.lt_of_lt_of_le headBound (Nat.le_add_right _ _)
        have read := (Append.getElem_append_left head _ row.val headBound combinedBound).trans
          (Map.getElem_map (PreparedRectangleCuts.intervalBox first) vertical row.val row.isLt headBound)
        simpa only [head, Fin.getElem_fin, rectangleIndex, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero,
          PreparedRectangleCuts.rectangles, Flatten.flatMap_cons] using read
      · let head := vertical.map (PreparedRectangleCuts.intervalBox first)
        let retained := rectangleIndex rest vertical column row
        have combinedBound : head.length + retained.val <
            (head ++ PreparedRectangleCuts.rectangles rest vertical).length := by
          rw [Append.length_append]
          exact Nat.add_lt_add_left retained.isLt head.length
        have offset : (column.val + 1) * vertical.length + row.val = head.length + retained.val := by
          dsimp only [head, retained, rectangleIndex]
          rw [Map.length_map, Multiplication.right_distrib, Nat.one_mul]
          omega0
        have originalBound : (column.val + 1) * vertical.length + row.val <
            (head ++ PreparedRectangleCuts.rectangles rest vertical).length := by
          rw [offset]
          exact combinedBound
        have read := (getElem_congr rfl offset originalBound).trans
          (Append.getElem_append_right head _ retained.val retained.isLt combinedBound)
        have result := read.trans (ih column)
        simpa only [head, Fin.getElem_fin, rectangleIndex, Fin.val_succ, List.getElem_cons_succ,
          PreparedRectangleCuts.rectangles, Flatten.flatMap_cons] using result

end Purelib.Geometry.Rectangle.Partition.PreparedRectangleIndices
