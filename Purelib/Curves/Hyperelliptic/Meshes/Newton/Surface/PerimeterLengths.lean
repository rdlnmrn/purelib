module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.JoinedTrace
public import Purelib.Integration.Path.TraceLengths
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry
import Purelib.Riemann.Integration.RectangularOwnedPerimeterOrder
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces

open Purelib.Integration.Path.JoinedTrace

open Purelib.Integration.Path.TraceLengths

open Purelib.Integration.Path.TraceLengths.VertexTrace

open Purelib.Riemann.Integration

@[expose] public section

/-! Cached nonnegative lengths on the actual concatenated face perimeter.
Their totals are the physical side lengths, including zero-length joins. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterLengths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces PiecePerimeterTraces)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2}
  {partitions : SurfacePartitions observations grid} {coarse :
    SurfaceMeshes partitions domains sheet}
  {fixed : Preflights domains sheet} {error :
    Rational}
  {energy : SurfaceRequest partitions coarse fixed error}
  {position : Fin grid.faces.regulars.length}

open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)

namespace FacePerimeterTraces

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Basic (sub_re sub_im)

/-- The complete actual bottom trace is ordered by its original horizontal coordinate, including the retained joins. -/
theorem bottom_ordered (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    VertexTrace.Ordered traces.bottom (fun owner => owner.point.re) := by
  rw [traces.bottom_eq]
  apply VertexTrace.ordered_concatenate
  · intro column
    exact RectangularOwnedPerimeterOrder.bottomOwned_ordered (traces.pieces.get ((PieceIndices.pieceIndex
      (partitions.get position)) column 0))
  · intro edge
    dsimp only [PiecePerimeterTraces.bottomPieces]
    rw [RectangularOwnedPerimeterOrder.bottomOwned_last_point, RectangularOwnedPerimeterOrder.bottomOwned_first_point]
    exact ((PieceIndices.horizontal_neighbor (partitions.get position)) edge 0).le

/-- The original bottom trace begins at the complete face's lower horizontal coordinate. -/
theorem bottom_first_re (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    traces.bottom.first.point.re = (grid.faces.regulars[position.val]'position.isLt).cell.box.xLower := by
  rw [traces.bottom_eq, VertexTrace.concatenate, VertexTrace.glue_first]
  dsimp only [PiecePerimeterTraces.bottomPieces]
  rw [RectangularOwnedPerimeterOrder.bottomOwned_first_point]
  have boxEq := (PieceIndices.piece_box (partitions.get position)) 0 0
  change _ = (grid.faces.regulars[position.val]'position.isLt).cell.box.xLower
  rw [boxEq]
  exact (partitions.get position).cuts.x.first_lower (Fin.cast (PieceIndices.columns_eq (partitions.get position))
    0).isLt

/-- The original bottom trace ends at the complete face's upper horizontal coordinate. -/
theorem bottom_last_re (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    traces.bottom.last.point.re = (grid.faces.regulars[position.val]'position.isLt).cell.box.xUpper := by
  rw [traces.bottom_eq, VertexTrace.concatenate_last]
  dsimp only [PiecePerimeterTraces.bottomPieces]
  rw [RectangularOwnedPerimeterOrder.bottomOwned_last_point]
  have boxEq := (PieceIndices.piece_box (partitions.get position)) (Fin.last (PieceIndices.columns (partitions.get
    position))) 0
  change _ = (grid.faces.regulars[position.val]'position.isLt).cell.box.xUpper
  rw [boxEq]
  exact (partitions.get position).cuts.x.last_upper _ (PieceIndices.columns_eq (partitions.get position))

/-- Cache nonnegative horizontal lengths on every actual original bottom trace edge. -/
def bottomLengths (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    VertexTrace.Lengths traces.bottom (fun owner => owner.point.re) :=
  Lengths.build traces.bottom _
    (bottom_ordered traces)

/-- The retained bottom trace length total equals the original physical face's horizontal width. -/
theorem bottom_total (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (lengths : VertexTrace.Lengths traces.bottom (fun owner => owner.point.re)) :
    lengths.total = (grid.faces.regulars[position.val]'position.isLt).cell.box.xUpper -
      (grid.faces.regulars[position.val]'position.isLt).cell.box.xLower := by
  rw [lengths.endpoints, bottom_last_re
    traces, bottom_first_re traces]

/-- Each actual original bottom trace step has squared Gaussian displacement equal to its retained squared scalar
length. -/
theorem bottom_movement (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (lengths : VertexTrace.Lengths traces.bottom (fun owner => owner.point.re)) (edge : Fin traces.bottom.rest.length) :
    Data.Gaussian.Norm.Basic.normSq ((traces.bottom.indexed edge.succ).point - (traces.bottom.indexed
      edge.castSucc).point) = (lengths.values edge)^2 := by
  rw [lengths.values_eq]
  simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
    FacePerimeterTraces.bottom_height traces]
  ring1

/-- The complete actual top trace is ordered by its original horizontal coordinate, including the retained joins. -/
theorem top_ordered (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    VertexTrace.Ordered traces.top (fun owner => owner.point.re) := by
  rw [traces.top_eq]
  apply VertexTrace.ordered_concatenate
  · intro column
    exact RectangularOwnedPerimeterOrder.topOwned_ordered (traces.pieces.get ((PieceIndices.pieceIndex (partitions.get
      position)) column (Fin.last (PieceIndices.rows (partitions.get position)))))
  · intro edge
    dsimp only [PiecePerimeterTraces.topPieces]
    rw [RectangularOwnedPerimeterOrder.topOwned_last_point, RectangularOwnedPerimeterOrder.topOwned_first_point]
    exact ((PieceIndices.horizontal_neighbor (partitions.get position)) edge (Fin.last (PieceIndices.rows
      (partitions.get position)))).le

/-- The original top trace begins at the complete face's lower horizontal coordinate. -/
theorem top_first_re (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    traces.top.first.point.re = (grid.faces.regulars[position.val]'position.isLt).cell.box.xLower := by
  rw [traces.top_eq, VertexTrace.concatenate, VertexTrace.glue_first]
  dsimp only [PiecePerimeterTraces.topPieces]
  rw [RectangularOwnedPerimeterOrder.topOwned_first_point]
  have boxEq := (PieceIndices.piece_box (partitions.get position)) 0 (Fin.last (PieceIndices.rows (partitions.get
    position)))
  change _ = (grid.faces.regulars[position.val]'position.isLt).cell.box.xLower
  rw [boxEq]
  exact (partitions.get position).cuts.x.first_lower (Fin.cast (PieceIndices.columns_eq (partitions.get position))
    0).isLt

/-- The original top trace ends at the complete face's upper horizontal coordinate. -/
theorem top_last_re (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    traces.top.last.point.re = (grid.faces.regulars[position.val]'position.isLt).cell.box.xUpper := by
  rw [traces.top_eq, VertexTrace.concatenate_last]
  dsimp only [PiecePerimeterTraces.topPieces]
  rw [RectangularOwnedPerimeterOrder.topOwned_last_point]
  have boxEq := (PieceIndices.piece_box (partitions.get position)) (Fin.last (PieceIndices.columns (partitions.get
    position))) (Fin.last (PieceIndices.rows (partitions.get position)))
  change _ = (grid.faces.regulars[position.val]'position.isLt).cell.box.xUpper
  rw [boxEq]
  exact (partitions.get position).cuts.x.last_upper _ (PieceIndices.columns_eq (partitions.get position))

/-- Cache nonnegative horizontal lengths on every actual original top trace edge. -/
def topLengths (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    VertexTrace.Lengths traces.top (fun owner => owner.point.re) :=
  Lengths.build traces.top _
    (top_ordered traces)

/-- The retained top trace length total equals the original physical face's horizontal width. -/
theorem top_total (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (lengths : VertexTrace.Lengths traces.top (fun owner => owner.point.re)) :
    lengths.total = (grid.faces.regulars[position.val]'position.isLt).cell.box.xUpper -
      (grid.faces.regulars[position.val]'position.isLt).cell.box.xLower := by
  rw [lengths.endpoints, top_last_re
    traces, top_first_re traces]

/-- Each actual original top trace step has squared Gaussian displacement equal to its retained squared scalar length.
-/
theorem top_movement (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (lengths : VertexTrace.Lengths traces.top (fun owner => owner.point.re)) (edge : Fin traces.top.rest.length) :
    Data.Gaussian.Norm.Basic.normSq ((traces.top.indexed edge.succ).point - (traces.top.indexed
      edge.castSucc).point) = (lengths.values edge)^2 := by
  rw [lengths.values_eq]
  simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
    FacePerimeterTraces.top_height traces]
  ring1

/-- The complete actual left trace is ordered by its original vertical coordinate, including the retained joins. -/
theorem left_ordered (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    VertexTrace.Ordered traces.left (fun owner => owner.point.im) := by
  rw [traces.left_eq]
  apply VertexTrace.ordered_concatenate
  · intro column
    exact RectangularOwnedPerimeterOrder.leftOwned_ordered (traces.pieces.get ((PieceIndices.pieceIndex (partitions.get
      position)) 0 column))
  · intro edge
    dsimp only [PiecePerimeterTraces.leftPieces]
    rw [RectangularOwnedPerimeterOrder.leftOwned_last_point, RectangularOwnedPerimeterOrder.leftOwned_first_point]
    exact ((PieceIndices.vertical_neighbor (partitions.get position)) 0 edge).le

/-- The original left trace begins at the complete face's lower vertical coordinate. -/
theorem left_first_im (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    traces.left.first.point.im = (grid.faces.regulars[position.val]'position.isLt).cell.box.yLower := by
  rw [traces.left_eq, VertexTrace.concatenate, VertexTrace.glue_first]
  dsimp only [PiecePerimeterTraces.leftPieces]
  rw [RectangularOwnedPerimeterOrder.leftOwned_first_point]
  have boxEq := (PieceIndices.piece_box (partitions.get position)) 0 0
  change _ = (grid.faces.regulars[position.val]'position.isLt).cell.box.yLower
  rw [boxEq]
  exact (partitions.get position).cuts.y.first_lower (Fin.cast (PieceIndices.rows_eq (partitions.get position)) 0).isLt

/-- The original left trace ends at the complete face's upper vertical coordinate. -/
theorem left_last_im (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    traces.left.last.point.im = (grid.faces.regulars[position.val]'position.isLt).cell.box.yUpper := by
  rw [traces.left_eq, VertexTrace.concatenate_last]
  dsimp only [PiecePerimeterTraces.leftPieces]
  rw [RectangularOwnedPerimeterOrder.leftOwned_last_point]
  have boxEq := (PieceIndices.piece_box (partitions.get position)) 0 (Fin.last (PieceIndices.rows (partitions.get
    position)))
  change _ = (grid.faces.regulars[position.val]'position.isLt).cell.box.yUpper
  rw [boxEq]
  exact (partitions.get position).cuts.y.last_upper _ (PieceIndices.rows_eq (partitions.get position))

/-- Cache nonnegative vertical lengths on every actual original left trace edge. -/
def leftLengths (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    VertexTrace.Lengths traces.left (fun owner => owner.point.im) :=
  Lengths.build traces.left _
    (left_ordered traces)

/-- The retained left trace length total equals the original physical face's vertical width. -/
theorem left_total (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (lengths : VertexTrace.Lengths traces.left (fun owner => owner.point.im)) :
    lengths.total = (grid.faces.regulars[position.val]'position.isLt).cell.box.yUpper -
      (grid.faces.regulars[position.val]'position.isLt).cell.box.yLower := by
  rw [lengths.endpoints, left_last_im
    traces, left_first_im traces]

/-- Each actual original left trace step has squared Gaussian displacement equal to its retained squared scalar length.
-/
theorem left_movement (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (lengths : VertexTrace.Lengths traces.left (fun owner => owner.point.im)) (edge : Fin traces.left.rest.length) :
    Data.Gaussian.Norm.Basic.normSq ((traces.left.indexed edge.succ).point - (traces.left.indexed
      edge.castSucc).point) = (lengths.values edge)^2 := by
  rw [lengths.values_eq]
  simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
    FacePerimeterTraces.left_horizontal traces]
  ring1

/-- The complete actual right trace is ordered by its original vertical coordinate, including the retained joins. -/
theorem right_ordered (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    VertexTrace.Ordered traces.right (fun owner => owner.point.im) := by
  rw [traces.right_eq]
  apply VertexTrace.ordered_concatenate
  · intro column
    exact RectangularOwnedPerimeterOrder.rightOwned_ordered (traces.pieces.get ((PieceIndices.pieceIndex (partitions.get
      position)) (Fin.last (PieceIndices.columns (partitions.get position))) column))
  · intro edge
    dsimp only [PiecePerimeterTraces.rightPieces]
    rw [RectangularOwnedPerimeterOrder.rightOwned_last_point, RectangularOwnedPerimeterOrder.rightOwned_first_point]
    exact ((PieceIndices.vertical_neighbor (partitions.get position)) (Fin.last (PieceIndices.columns (partitions.get
      position))) edge).le

/-- The original right trace begins at the complete face's lower vertical coordinate. -/
theorem right_first_im (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    traces.right.first.point.im = (grid.faces.regulars[position.val]'position.isLt).cell.box.yLower := by
  rw [traces.right_eq, VertexTrace.concatenate, VertexTrace.glue_first]
  dsimp only [PiecePerimeterTraces.rightPieces]
  rw [RectangularOwnedPerimeterOrder.rightOwned_first_point]
  have boxEq := (PieceIndices.piece_box (partitions.get position)) (Fin.last (PieceIndices.columns (partitions.get
    position))) 0
  change _ = (grid.faces.regulars[position.val]'position.isLt).cell.box.yLower
  rw [boxEq]
  exact (partitions.get position).cuts.y.first_lower (Fin.cast (PieceIndices.rows_eq (partitions.get position)) 0).isLt

/-- The original right trace ends at the complete face's upper vertical coordinate. -/
theorem right_last_im (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    traces.right.last.point.im = (grid.faces.regulars[position.val]'position.isLt).cell.box.yUpper := by
  rw [traces.right_eq, VertexTrace.concatenate_last]
  dsimp only [PiecePerimeterTraces.rightPieces]
  rw [RectangularOwnedPerimeterOrder.rightOwned_last_point]
  have boxEq := (PieceIndices.piece_box (partitions.get position)) (Fin.last (PieceIndices.columns (partitions.get
    position))) (Fin.last (PieceIndices.rows (partitions.get position)))
  change _ = (grid.faces.regulars[position.val]'position.isLt).cell.box.yUpper
  rw [boxEq]
  exact (partitions.get position).cuts.y.last_upper _ (PieceIndices.rows_eq (partitions.get position))

/-- Cache nonnegative vertical lengths on every actual original right trace edge. -/
def rightLengths (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    VertexTrace.Lengths traces.right (fun owner => owner.point.im) :=
  Lengths.build traces.right _
    (right_ordered traces)

/-- The retained right trace length total equals the original physical face's vertical width. -/
theorem right_total (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (lengths : VertexTrace.Lengths traces.right (fun owner => owner.point.im)) :
    lengths.total = (grid.faces.regulars[position.val]'position.isLt).cell.box.yUpper -
      (grid.faces.regulars[position.val]'position.isLt).cell.box.yLower := by
  rw [lengths.endpoints, right_last_im
    traces, right_first_im traces]

/-- Each actual original right trace step has squared Gaussian displacement equal to its retained squared scalar length.
-/
theorem right_movement (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (lengths : VertexTrace.Lengths traces.right (fun owner => owner.point.im)) (edge : Fin traces.right.rest.length) :
    Data.Gaussian.Norm.Basic.normSq ((traces.right.indexed edge.succ).point - (traces.right.indexed
      edge.castSucc).point) = (lengths.values edge)^2 := by
  rw [lengths.values_eq]
  simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
    FacePerimeterTraces.right_horizontal traces]
  ring1

end FacePerimeterTraces
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterLengths
