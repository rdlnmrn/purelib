module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionCompatibility
public import Purelib.Riemann.Readings.RectangularObservationEndpoints
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.NewtonObservationSurfacePartition

public section

/-! Executable matching of boundary pieces on adjacent complete regular
faces. The selected indices carry their transverse and shared-edge equalities. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionCompatibility
  (piece_x_bounds piece_y_bounds build_x_compatible build_y_compatible)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve} {higher : 1 <
    curve.polynomial.natDegree}
  {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} {preparation :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original}
  {target radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : Purelib.Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original}
  {firstPosition lastPosition : Fin grid.faces.regulars.length}

/-- Transporting a finite sum along equality of the original index bounds preserves its exact value. -/
private theorem sum_cast {first last : Nat} (equal : first = last) (value : Fin last → Data.Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index : Fin first => value (Fin.cast equal index)) = FiniteSum.Fin.sumFin value := by
  cases equal
  rfl

set_option genInjectivity false in
/-- Retained boundary-piece indices on two vertically adjacent original faces.

The selected pieces have equal horizontal extent and exactly matching upper and lower boundary coordinates. -/
structure HorizontalPieces (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition) where
  /-- The retained bounded piece index in the original first face partition. -/ firstPiece : Fin first.cuts.boxes.length
  /-- The retained bounded piece index in the original neighboring face partition. -/ lastPiece : Fin
    last.cuts.boxes.length
  /-- The retained pieces have equal lower horizontal coordinate bounds. -/ lower_eq :
    (first.cuts.boxes[firstPiece.val]'firstPiece.isLt).xLower =
    (last.cuts.boxes[lastPiece.val]'lastPiece.isLt).xLower
  /-- The retained pieces have equal upper horizontal coordinate bounds. -/ upper_eq :
    (first.cuts.boxes[firstPiece.val]'firstPiece.isLt).xUpper =
    (last.cuts.boxes[lastPiece.val]'lastPiece.isLt).xUpper
  /-- The original top row piece and neighboring bottom row piece share their exact boundary coordinate. -/ joined :
    (first.cuts.boxes[firstPiece.val]'firstPiece.isLt).yUpper =
    (last.cuts.boxes[lastPiece.val]'lastPiece.isLt).yLower

constructive_injectivity HorizontalPieces

namespace HorizontalPieces

/-- Match the original top row with the neighboring bottom row, retaining transported transverse indices and exact
boundary equalities. -/
@[expose] def build (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.x.intervals = last.cuts.x.intervals)
    (adjacent : (grid.faces.regulars[firstPosition.val]'firstPosition.isLt).cell.box.yUpper =
      (grid.faces.regulars[lastPosition.val]'lastPosition.isLt).cell.box.yLower)
    (column : Fin ((PieceIndices.columns first) + 1)) :
      Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.HorizontalPieces first last := by
  have counts : (PieceIndices.columns first) + 1 = (PieceIndices.columns last) + 1 :=
    (PieceIndices.columns_eq first).trans ((congrArg List.length equal).trans (PieceIndices.columns_eq last).symm)
  let next := Fin.cast counts column
  let firstPiece := (PieceIndices.pieceIndex first) column (Fin.last (PieceIndices.rows first))
  let lastPiece := (PieceIndices.pieceIndex last) next 0
  have bounds := PartitionCompatibility.piece_x_bounds first last equal column next (Fin.last (PieceIndices.rows first))
    0 rfl
  refine ⟨firstPiece, lastPiece, bounds.1, bounds.2, ?_⟩
  dsimp only [firstPiece, lastPiece]
  rw [PieceIndices.piece_box first, PieceIndices.piece_box last]
  exact (first.cuts.y.last_upper (Fin.cast (PieceIndices.rows_eq first) (Fin.last (PieceIndices.rows first)))
    (PieceIndices.rows_eq first)).trans
    (adjacent.trans (last.cuts.y.first_lower (Fin.cast (PieceIndices.rows_eq last) 0).isLt).symm)

/-- The constructed first index is exactly the original top row piece index. -/
theorem build_firstPiece (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.x.intervals = last.cuts.x.intervals)
    (adjacent : (grid.faces.regulars[firstPosition.val]'firstPosition.isLt).cell.box.yUpper =
      (grid.faces.regulars[lastPosition.val]'lastPosition.isLt).cell.box.yLower)
    (column : Fin ((PieceIndices.columns first) + 1)) :
    (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.HorizontalPieces.build first last equal adjacent
      column).firstPiece = (PieceIndices.pieceIndex first) column (Fin.last (PieceIndices.rows first)) := rfl

/-- The constructed neighbor index is exactly its bottom row piece index with the retained transverse index transport.
-/
theorem build_lastPiece (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.x.intervals = last.cuts.x.intervals)
    (adjacent : (grid.faces.regulars[firstPosition.val]'firstPosition.isLt).cell.box.yUpper =
      (grid.faces.regulars[lastPosition.val]'lastPosition.isLt).cell.box.yLower)
    (column : Fin ((PieceIndices.columns first) + 1)) :
    (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.HorizontalPieces.build first last equal adjacent
      column).lastPiece = (PieceIndices.pieceIndex last) (Fin.cast ((PieceIndices.columns_eq first).trans ((congrArg
      List.length equal).trans (PieceIndices.columns_eq last).symm)) column) 0 := rfl

/-- The retained first-piece sum equals the original complete top row sum. -/
theorem sum_firstPieces (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.x.intervals = last.cuts.x.intervals)
    (adjacent : (grid.faces.regulars[firstPosition.val]'firstPosition.isLt).cell.box.yUpper =
      (grid.faces.regulars[lastPosition.val]'lastPosition.isLt).cell.box.yLower)
    (value : Fin first.cuts.boxes.length → Data.Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index => value
      (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.HorizontalPieces.build first last equal adjacent
      index).firstPiece) =
      FiniteSum.Fin.sumFin (fun index => value ((PieceIndices.pieceIndex first) index (Fin.last (PieceIndices.rows
        first)))) :=
  FiniteSum.Fin.sumFin_congr fun index => congrArg value
    (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.HorizontalPieces.build_firstPiece first last equal
    adjacent index)

/-- The retained neighbor-piece sum equals the original complete bottom row sum. -/
theorem sum_lastPieces (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.x.intervals = last.cuts.x.intervals)
    (adjacent : (grid.faces.regulars[firstPosition.val]'firstPosition.isLt).cell.box.yUpper =
      (grid.faces.regulars[lastPosition.val]'lastPosition.isLt).cell.box.yLower)
    (value : Fin last.cuts.boxes.length → Data.Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index => value
      (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.HorizontalPieces.build first last equal adjacent
      index).lastPiece) =
      FiniteSum.Fin.sumFin (fun index => value ((PieceIndices.pieceIndex last) index 0)) := by
  have readback := FiniteSum.Fin.sumFin_congr fun index => congrArg value
    (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.HorizontalPieces.build_lastPiece first last equal
    adjacent index)
  exact readback.trans (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.sum_cast
    ((PieceIndices.columns_eq first).trans ((congrArg List.length equal).trans (PieceIndices.columns_eq last).symm))
    (fun index => value ((PieceIndices.pieceIndex last) index 0)))

/-- Construct the retained boundary-piece matching from the canonical observation partitions and original adjacent face
extents. -/
@[expose] def canonical (observations : NewtonProtectedObservations.ProtectedObservations original) (grid :
  BranchCellBank.NewtonGrid preparation target radius)
    (first last : Fin grid.faces.regulars.length)
    (lowerEq : (grid.faces.regulars[first.val]'first.isLt).cell.box.xLower =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xLower)
    (upperEq : (grid.faces.regulars[first.val]'first.isLt).cell.box.xUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xUpper)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.yUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yLower)
    (column : Fin (PieceIndices.columns
      (SurfacePartition.build observations grid first) + 1)) :
    Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.HorizontalPieces (SurfacePartition.build observations grid
      first) (SurfacePartition.build observations grid last) :=
  Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.HorizontalPieces.build _ _
    (PartitionCompatibility.build_x_compatible observations grid first last lowerEq upperEq) adjacent column

end HorizontalPieces

set_option genInjectivity false in
/-- Retained boundary-piece indices on two horizontally adjacent original faces.

The selected pieces have equal vertical extent and exactly matching right and left boundary coordinates. -/
structure VerticalPieces (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition) where
  /-- The retained bounded piece index in the original first face partition. -/ firstPiece : Fin first.cuts.boxes.length
  /-- The retained bounded piece index in the original neighboring face partition. -/ lastPiece : Fin
    last.cuts.boxes.length
  /-- The retained pieces have equal lower vertical coordinate bounds. -/ lower_eq :
    (first.cuts.boxes[firstPiece.val]'firstPiece.isLt).yLower =
    (last.cuts.boxes[lastPiece.val]'lastPiece.isLt).yLower
  /-- The retained pieces have equal upper vertical coordinate bounds. -/ upper_eq :
    (first.cuts.boxes[firstPiece.val]'firstPiece.isLt).yUpper =
    (last.cuts.boxes[lastPiece.val]'lastPiece.isLt).yUpper
  /-- The original rightmost column piece and neighboring leftmost column piece share their exact boundary coordinate.
  -/
  joined : (first.cuts.boxes[firstPiece.val]'firstPiece.isLt).xUpper =
    (last.cuts.boxes[lastPiece.val]'lastPiece.isLt).xLower

constructive_injectivity VerticalPieces

namespace VerticalPieces

/-- Match the original rightmost column with the neighboring leftmost column, retaining transported transverse indices
and exact boundary equalities. -/
@[expose] def build (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.y.intervals = last.cuts.y.intervals)
    (adjacent : (grid.faces.regulars[firstPosition.val]'firstPosition.isLt).cell.box.xUpper =
      (grid.faces.regulars[lastPosition.val]'lastPosition.isLt).cell.box.xLower)
    (row : Fin ((PieceIndices.rows first) + 1)) :
      Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces first last := by
  have counts : (PieceIndices.rows first) + 1 = (PieceIndices.rows last) + 1 :=
    (PieceIndices.rows_eq first).trans ((congrArg List.length equal).trans (PieceIndices.rows_eq last).symm)
  let next := Fin.cast counts row
  let firstPiece := (PieceIndices.pieceIndex first) (Fin.last (PieceIndices.columns first)) row
  let lastPiece := (PieceIndices.pieceIndex last) 0 next
  have bounds := PartitionCompatibility.piece_y_bounds first last equal (Fin.last (PieceIndices.columns first)) 0 row
    next rfl
  refine ⟨firstPiece, lastPiece, bounds.1, bounds.2, ?_⟩
  dsimp only [firstPiece, lastPiece]
  rw [PieceIndices.piece_box first, PieceIndices.piece_box last]
  exact (first.cuts.x.last_upper (Fin.cast (PieceIndices.columns_eq first) (Fin.last (PieceIndices.columns first)))
    (PieceIndices.columns_eq first)).trans
    (adjacent.trans (last.cuts.x.first_lower (Fin.cast (PieceIndices.columns_eq last) 0).isLt).symm)

/-- The constructed first index is exactly the original rightmost column piece index. -/
theorem build_firstPiece (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.y.intervals = last.cuts.y.intervals)
    (adjacent : (grid.faces.regulars[firstPosition.val]'firstPosition.isLt).cell.box.xUpper =
      (grid.faces.regulars[lastPosition.val]'lastPosition.isLt).cell.box.xLower)
    (row : Fin ((PieceIndices.rows first) + 1)) :
    (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces.build first last equal adjacent
      row).firstPiece = (PieceIndices.pieceIndex first) (Fin.last (PieceIndices.columns first)) row := rfl

/-- The constructed neighbor index is exactly its leftmost column piece index with the retained transverse index
transport. -/
theorem build_lastPiece (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.y.intervals = last.cuts.y.intervals)
    (adjacent : (grid.faces.regulars[firstPosition.val]'firstPosition.isLt).cell.box.xUpper =
      (grid.faces.regulars[lastPosition.val]'lastPosition.isLt).cell.box.xLower)
    (row : Fin ((PieceIndices.rows first) + 1)) :
    (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces.build first last equal adjacent
      row).lastPiece = (PieceIndices.pieceIndex last) 0 (Fin.cast ((PieceIndices.rows_eq first).trans ((congrArg
      List.length equal).trans (PieceIndices.rows_eq last).symm)) row) := rfl

/-- The retained first-piece sum equals the original complete rightmost column sum. -/
theorem sum_firstPieces (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.y.intervals = last.cuts.y.intervals)
    (adjacent : (grid.faces.regulars[firstPosition.val]'firstPosition.isLt).cell.box.xUpper =
      (grid.faces.regulars[lastPosition.val]'lastPosition.isLt).cell.box.xLower)
    (value : Fin first.cuts.boxes.length → Data.Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index => value
      (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces.build first last equal adjacent
      index).firstPiece) =
      FiniteSum.Fin.sumFin (fun index => value ((PieceIndices.pieceIndex first) (Fin.last (PieceIndices.columns first))
        index)) :=
  FiniteSum.Fin.sumFin_congr fun index => congrArg value
    (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces.build_firstPiece first last equal adjacent
    index)

/-- The retained neighbor-piece sum equals the original complete leftmost column sum. -/
theorem sum_lastPieces (first : NewtonObservationSurfacePartition.SurfacePartition observations grid firstPosition)
    (last : NewtonObservationSurfacePartition.SurfacePartition observations grid lastPosition)
    (equal : first.cuts.y.intervals = last.cuts.y.intervals)
    (adjacent : (grid.faces.regulars[firstPosition.val]'firstPosition.isLt).cell.box.xUpper =
      (grid.faces.regulars[lastPosition.val]'lastPosition.isLt).cell.box.xLower)
    (value : Fin last.cuts.boxes.length → Data.Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index => value
      (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces.build first last equal adjacent
      index).lastPiece) =
      FiniteSum.Fin.sumFin (fun index => value ((PieceIndices.pieceIndex last) 0 index)) := by
  have readback := FiniteSum.Fin.sumFin_congr fun index => congrArg value
    (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces.build_lastPiece first last equal adjacent
    index)
  exact readback.trans (Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.sum_cast
    ((PieceIndices.rows_eq first).trans ((congrArg List.length equal).trans (PieceIndices.rows_eq last).symm))
    (fun index => value ((PieceIndices.pieceIndex last) 0 index)))

/-- Construct the retained boundary-piece matching from the canonical observation partitions and original adjacent face
extents. -/
@[expose] def canonical (observations : NewtonProtectedObservations.ProtectedObservations original) (grid :
  BranchCellBank.NewtonGrid preparation target radius)
    (first last : Fin grid.faces.regulars.length)
    (lowerEq : (grid.faces.regulars[first.val]'first.isLt).cell.box.yLower =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yLower)
    (upperEq : (grid.faces.regulars[first.val]'first.isLt).cell.box.yUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yUpper)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.xUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xLower)
    (row : Fin (PieceIndices.rows
      (SurfacePartition.build observations grid first) + 1)) :
    Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces (SurfacePartition.build observations grid
      first) (SurfacePartition.build observations grid last) :=
  Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces.build _ _
    (PartitionCompatibility.build_y_compatible observations grid first last lowerEq upperEq) adjacent row

end VerticalPieces

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
