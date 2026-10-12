module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Data.Rat

open Purelib.Geometry.Rectangle.Partition

open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.NewtonObservationSurfacePartition

@[expose] public section

/-! Canonical observation cuts match across regular faces with the same
transverse extent. Retained piece indices read back the same side interval. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionCompatibility

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition.SurfacePartition (build)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve} {higher : 1 <
    curve.polynomial.natDegree}
  {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} {preparation :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original}
  {target radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : Purelib.Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original}

/-- Equal retained axis endpoints and the same cut list give equal canonical partition interval lists. -/
private theorem axis_intervals_eq {firstLower firstUpper lastLower lastUpper : Fraction.Rational}
    (firstProper : firstLower < firstUpper) (lastProper : lastLower < lastUpper)
    (lowerEq : firstLower = lastLower) (upperEq : firstUpper = lastUpper) (cuts : List Fraction.Rational) :
    (Geometry.Rectangle.AxisPartition.build firstLower firstUpper firstProper cuts).intervals =
      (Geometry.Rectangle.AxisPartition.build lastLower lastUpper lastProper cuts).intervals := by
  cases lowerEq
  cases upperEq
  rfl

/-- Equal original lists read equal entries at equal bounded index values. -/
private theorem read_eq {α : Type} {first last : List α} (equal : first = last)
    {i j : Nat} (same : i = j) (firstBound : i < first.length) (lastBound : j < last.length) :
    first[i]'firstBound = last[j]'lastBound := by
  cases equal
  cases same
  rfl

/-- Canonical observation cuts have equal x-interval lists on original faces with matching horizontal extent. -/
theorem build_x_compatible (observations : NewtonProtectedObservations.ProtectedObservations original)
    (grid : BranchCellBank.NewtonGrid preparation target radius) (first last : Fin grid.faces.regulars.length)
    (lowerEq : (grid.faces.regulars[first.val]'first.isLt).cell.box.xLower =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xLower)
    (upperEq : (grid.faces.regulars[first.val]'first.isLt).cell.box.xUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xUpper) :
    (SurfacePartition.build observations grid first).cuts.x.intervals = (SurfacePartition.build observations grid
      last).cuts.x.intervals :=
  Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionCompatibility.axis_intervals_eq _ _ lowerEq upperEq _

/-- Corresponding retained columns have the same exact x-boundaries when their original x-interval lists agree. -/
theorem piece_x_bounds {firstPosition lastPosition : Fin grid.faces.regulars.length}
    (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition) (last :
      NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.x.intervals = last.cuts.x.intervals)
    (firstColumn : Fin ((PieceIndices.columns first) + 1)) (lastColumn : Fin ((PieceIndices.columns last) + 1))
    (firstRow : Fin ((PieceIndices.rows first) + 1)) (lastRow : Fin ((PieceIndices.rows last) + 1))
    (same : firstColumn.val = lastColumn.val) :
    (first.cuts.boxes[((PieceIndices.pieceIndex first) firstColumn firstRow).val]'((PieceIndices.pieceIndex first)
      firstColumn firstRow).isLt).xLower =
      (last.cuts.boxes[((PieceIndices.pieceIndex last) lastColumn lastRow).val]'((PieceIndices.pieceIndex last)
        lastColumn lastRow).isLt).xLower ∧
    (first.cuts.boxes[((PieceIndices.pieceIndex first) firstColumn firstRow).val]'((PieceIndices.pieceIndex first)
      firstColumn firstRow).isLt).xUpper =
      (last.cuts.boxes[((PieceIndices.pieceIndex last) lastColumn lastRow).val]'((PieceIndices.pieceIndex last)
        lastColumn lastRow).isLt).xUpper := by
  rw [(PieceIndices.piece_box first), (PieceIndices.piece_box last)]
  have entry := Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionCompatibility.read_eq equal same (Fin.cast
    (PieceIndices.columns_eq first) firstColumn).isLt (Fin.cast (PieceIndices.columns_eq last) lastColumn).isLt
  exact ⟨congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower) entry,
    congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper) entry⟩

/-- Canonical observation cuts have equal y-interval lists on original faces with matching vertical extent. -/
theorem build_y_compatible (observations : NewtonProtectedObservations.ProtectedObservations original)
    (grid : BranchCellBank.NewtonGrid preparation target radius) (first last : Fin grid.faces.regulars.length)
    (lowerEq : (grid.faces.regulars[first.val]'first.isLt).cell.box.yLower =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yLower)
    (upperEq : (grid.faces.regulars[first.val]'first.isLt).cell.box.yUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yUpper) :
    (SurfacePartition.build observations grid first).cuts.y.intervals = (SurfacePartition.build observations grid
      last).cuts.y.intervals :=
  Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionCompatibility.axis_intervals_eq _ _ lowerEq upperEq _

/-- Corresponding retained rows have the same exact y-boundaries when their original y-interval lists agree. -/
theorem piece_y_bounds {firstPosition lastPosition : Fin grid.faces.regulars.length}
    (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition) (last :
      NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.y.intervals = last.cuts.y.intervals)
    (firstColumn : Fin ((PieceIndices.columns first) + 1)) (lastColumn : Fin ((PieceIndices.columns last) + 1))
    (firstRow : Fin ((PieceIndices.rows first) + 1)) (lastRow : Fin ((PieceIndices.rows last) + 1))
    (same : firstRow.val = lastRow.val) :
    (first.cuts.boxes[((PieceIndices.pieceIndex first) firstColumn firstRow).val]'((PieceIndices.pieceIndex first)
      firstColumn firstRow).isLt).yLower =
      (last.cuts.boxes[((PieceIndices.pieceIndex last) lastColumn lastRow).val]'((PieceIndices.pieceIndex last)
        lastColumn lastRow).isLt).yLower ∧
    (first.cuts.boxes[((PieceIndices.pieceIndex first) firstColumn firstRow).val]'((PieceIndices.pieceIndex first)
      firstColumn firstRow).isLt).yUpper =
      (last.cuts.boxes[((PieceIndices.pieceIndex last) lastColumn lastRow).val]'((PieceIndices.pieceIndex last)
        lastColumn lastRow).isLt).yUpper := by
  rw [(PieceIndices.piece_box first), (PieceIndices.piece_box last)]
  have entry := Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionCompatibility.read_eq equal same (Fin.cast
    (PieceIndices.rows_eq first) firstRow).isLt (Fin.cast (PieceIndices.rows_eq last) lastRow).isLt
  exact ⟨congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower) entry,
    congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper) entry⟩

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionCompatibility
