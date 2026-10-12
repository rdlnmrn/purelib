module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleIndices
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleSums
import Purelib.Geometry.Rectangle.Partition.PreparedAxisAdjacency
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

public section

/-! Row-major readback of the complete regular-face pieces. The indices refer
to the retained boxes, including the complementary pieces. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices

open Purelib.Data.Nat

open Purelib

open Purelib.Algebra

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Topology

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve} {higher : 1 <
    curve.polynomial.natDegree}
  {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} {preparation :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original}
  {target radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : Purelib.Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {position
    : Fin grid.faces.regulars.length}

/-- A strictly increasing endpoint pair forces the retained finite axis walk to have at least one edge. -/
private theorem walk_positive {intervals : List PreparedAxisPartitions.Interval} {first last : Fraction.Rational}
    (walk : AxisWalks.IncreasingWalk intervals first last) (proper : first < last) : 0 < walk.edges.length := by
  cases walk with
  | nil => exact (lt_irrefl _ proper).elim
  | cons interval member tail => exact Nat.succ_pos _

/-- A proper retained axis partition has at least one interval. -/
private theorem axis_positive {first last : Fraction.Rational} {points : List Fraction.Rational}
    (partition : Geometry.Rectangle.AxisPartition first last points) : 0 < partition.intervals.length := by
  rw [← partition.walk_edges]
  exact Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.walk_positive partition.walk partition.proper

/-- The number of horizontal adjacency positions in the retained rectangle partition. -/
@[expose] def columns (partition : NewtonObservationSurfacePartition.SurfacePartition observations grid position) : Nat
  := partition.cuts.x.intervals.length - 1
/-- The number of vertical adjacency positions in the retained rectangle partition. -/
@[expose] def rows (partition : NewtonObservationSurfacePartition.SurfacePartition observations grid position) : Nat :=
  partition.cuts.y.intervals.length - 1

/-- One plus the horizontal adjacency count is the retained x-interval count.

The proper axis partition contains at least one interval. Its positive length permits bounded natural subtraction of
one, and adding back that subtrahend recovers the complete horizontal interval bank. -/
theorem columns_eq (partition : NewtonObservationSurfacePartition.SurfacePartition observations grid position) :
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns partition) + 1 = partition.cuts.x.intervals.length
      :=
  (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le (Nat.succ_le_of_lt
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.axis_positive partition.cuts.x)))

/-- One plus the vertical adjacency count is the retained y-interval count.

The proper axis partition contains at least one interval. Its positive length permits bounded natural subtraction of
one, and adding back that subtrahend recovers the complete vertical interval bank. -/
theorem rows_eq (partition : NewtonObservationSurfacePartition.SurfacePartition observations grid position) :
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows partition) + 1 = partition.cuts.y.intervals.length :=
  (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le (Nat.succ_le_of_lt
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.axis_positive partition.cuts.y)))

/-- Map the retained column and row indices to the original stored rectangle-piece index. -/
@[expose] def pieceIndex (partition : NewtonObservationSurfacePartition.SurfacePartition observations grid position)
    (column : Fin ((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns partition) + 1)) (row : Fin
      ((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows partition) + 1)) : Fin partition.cuts.boxes.length
      :=
  Fin.cast (congrArg List.length partition.cuts.boxes_eq).symm
    (PreparedRectangleIndices.rectangleIndex _ _ (Fin.cast
      (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns_eq partition) column) (Fin.cast
      (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows_eq partition) row))

/-- Transporting a finite index along a list equality preserves its original box readback. -/
private theorem box_cast {first last : List Rational.Box} (equal : first = last) (index : Fin
  last.length) :
    first[(Fin.cast (congrArg List.length equal).symm index).val]'(Fin.cast (congrArg List.length equal).symm
      index).isLt =
      last[index.val]'index.isLt := by
  cases equal
  rfl

/-- The retained indexed piece is exactly the box formed by its original x and y intervals. -/
theorem piece_box (partition : NewtonObservationSurfacePartition.SurfacePartition observations grid position)
    (column : Fin ((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns partition) + 1)) (row : Fin
      ((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows partition) + 1)) :
    partition.cuts.boxes[((Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column
      row).val]'((Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column row).isLt
      =
      PreparedRectangleCuts.intervalBox
        (partition.cuts.x.intervals[(Fin.cast (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns_eq
          partition) column).val]'(Fin.cast (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns_eq
          partition) column).isLt)
        (partition.cuts.y.intervals[(Fin.cast (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows_eq
          partition) row).val]'(Fin.cast (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows_eq partition)
          row).isLt) := by
  unfold Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex
  rw [Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.box_cast partition.cuts.boxes_eq]
  exact PreparedRectangleIndices.rectangle_at _ _ _ _

/-- Consecutive retained columns have equal touching x-boundary coordinates. -/
theorem horizontal_neighbor (partition : NewtonObservationSurfacePartition.SurfacePartition observations grid position)
    (column : Fin (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns partition)) (row : Fin
      ((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows partition) + 1)) :
    (partition.cuts.boxes[((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition)
      column.castSucc row).val]'((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition)
      column.castSucc row).isLt).xUpper =
      (partition.cuts.boxes[((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column.succ
        row).val]'((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column.succ
        row).isLt).xLower := by
  rw [(Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.piece_box partition),
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.piece_box partition)]
  exact partition.cuts.x.consecutive column.val (by
      rw [← (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns_eq partition)];
      exact Nat.succ_lt_succ column.isLt)

/-- Consecutive retained rows have equal touching y-boundary coordinates. -/
theorem vertical_neighbor (partition : NewtonObservationSurfacePartition.SurfacePartition observations grid position)
    (column : Fin ((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns partition) + 1)) (row : Fin
      (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows partition)) :
    (partition.cuts.boxes[((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column
      row.castSucc).val]'((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column
      row.castSucc).isLt).yUpper =
      (partition.cuts.boxes[((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column
        row.succ).val]'((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column
        row.succ).isLt).yLower := by
  rw [(Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.piece_box partition),
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.piece_box partition)]
  exact partition.cuts.y.consecutive row.val (by
      rw [← (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows_eq partition)];
      exact Nat.succ_lt_succ row.isLt)

/-- A finite Gaussian sum is unchanged by transporting its original index type along a size equality. -/
private theorem sum_cast {first last : Nat} (equal : first = last) (value : Fin last → Data.Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin value = FiniteSum.Fin.sumFin (fun index : Fin first => value (Fin.cast equal index)) := by
  cases equal
  rfl

/-- The finite sum over all retained rectangle pieces equals the nested original column and row sums. -/
theorem sum_pieces (partition : NewtonObservationSurfacePartition.SurfacePartition observations grid position)
    (value : Fin partition.cuts.boxes.length → Data.Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin value = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => value
      ((Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column row))) := by
  rw [Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.sum_cast (congrArg List.length
    partition.cuts.boxes_eq).symm,
    PreparedRectangleSums.sumFin_rectangles, Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.sum_cast
      (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns_eq partition)]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  exact Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.sum_cast
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows_eq partition) _

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
