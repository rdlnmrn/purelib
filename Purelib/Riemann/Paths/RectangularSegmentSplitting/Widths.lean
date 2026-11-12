module

public import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Widths of the same retained rectangular segment split

The original interval-list equation and increasing partition pay the exact
finite width sum. Repeated physical points, stationary segments and every
original split occurrence remain at their retained indices.
-/

public section

namespace Purelib.Riemann.Paths.RectangularSegmentSplitting.SegmentSplit

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)
open Purelib.Algebra.FiniteSum.Rational.Order
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Geometry.Rectangle

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry}
    {first last : Canonical}

/-- The width of the SAME literal retained piece interval at its original finite position. -/
def width (split : SegmentSplit cuts first last) (position : Fin split.pieces.length) : Rational :=
  (split.pieces[position.val]'position.isLt).interval.upper -
    (split.pieces[position.val]'position.isLt).interval.lower

/-- Each actual width reads that original piece's retained interval endpoints. -/
theorem width_eq (split : SegmentSplit cuts first last) (position : Fin split.pieces.length) :
    split.width position = (split.pieces[position.val]'position.isLt).interval.upper -
      (split.pieces[position.val]'position.isLt).interval.lower := by
  unfold width
  rfl

/-- The original ordered interval gives a nonnegative width at every literal retained occurrence. -/
theorem width_nonnegative (split : SegmentSplit cuts first last) (position : Fin split.pieces.length) :
    0 ≤ split.width position :=
  Order.Arithmetic.sub_nonneg_direct (split.pieces[position.val]'position.isLt).interval.ordered.le

/-- Indexed widths read the original structural width fold of those SAME stored piece intervals. -/
private theorem sum_widths_list (pieces : List (SegmentPiece geometry first last)) :
    sumFin (fun position : Fin pieces.length =>
      (pieces[position.val]'position.isLt).interval.upper - (pieces[position.val]'position.isLt).interval.lower) =
      AxisPartition.widthSum (pieces.map SegmentPiece.interval) := by
  induction pieces with
  | nil => rfl
  | cons head tail previous =>
      rewrite [sumFin_succ]
      change (head.interval.upper - head.interval.lower) +
          sumFin (fun position : Fin tail.length =>
            (tail[position.val]'position.isLt).interval.upper -
              (tail[position.val]'position.isLt).interval.lower) =
        (head.interval.upper - head.interval.lower) + AxisPartition.widthSum (tail.map SegmentPiece.interval)
      exact congrArg (fun value : Rational => (head.interval.upper - head.interval.lower) + value) previous

/-- The original complete split widths sum to one, with no replacement partition or occurrence removal. -/
theorem sum_widths (split : SegmentSplit cuts first last) : sumFin split.width = 1 :=
  (sum_widths_list split.pieces).trans
    ((congrArg AxisPartition.widthSum split.intervals_eq).trans
      (split.partition.widthSum_eq.trans (by ring1)))

/-- Every actual split width is at most one by the same complete retained width sum. -/
theorem width_le_one (split : SegmentSplit cuts first last) (position : Fin split.pieces.length) :
    split.width position ≤ 1 :=
  (weight_le_sum split.width split.width_nonnegative position).trans_eq split.sum_widths

/-- The sum of squared actual split widths is at most one, including stationary physical segments. -/
theorem sum_squared_widths_le_one (split : SegmentSplit cuts first last) :
    sumFin (fun position : Fin split.pieces.length => (split.width position) ^ 2) ≤ 1 :=
  (IndexedBudget.sumFin_le (fun position =>
    (show (split.width position) ^ 2 = split.width position * split.width position by ring1).trans_le
      ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (split.width_le_one position)
        (split.width_nonnegative position)).trans_eq (Field.one_mul _)))).trans_eq split.sum_widths

end Purelib.Riemann.Paths.RectangularSegmentSplitting.SegmentSplit

end
