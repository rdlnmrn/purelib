module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Riemann.Integration.RectangularMatchedPerimeter
public import Purelib.Riemann.Readings.RectangularObservationEndpoints
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility

open Purelib.Data.Vector

open Purelib.Riemann.Readings.RectangularMatchedObservationSides

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide

@[expose] public section

/-! Matched boundary traces between complete regular-face pieces. The common
spatial depth and both original model owners are retained on every segment. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : Purelib.Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2}
  {partitions : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCuts : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains}
    {depth : Nat}
  {fixed : Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Purelib.Data.Rat.Fraction.Rational}

variable (request : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions
  (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
  sheet depth) fixed error)

/-- On a horizontal side the upper piece is the left trace, so its bottom minus the lower piece's top agrees with the
face-assembly seam orientation. -/
def horizontalSeamSide (position : Fin grid.faces.regulars.length)
    (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) (row : Fin (PieceIndices.rows (partitions.get
      position))) :
    let partition := partitions.get position
    let above := (request.meshes.get position).entries.get (PieceIndices.pieceIndex partition column row.succ)
    let below := (request.meshes.get position).entries.get (PieceIndices.pieceIndex partition column row.castSucc)
    ObservationMesh.MatchedHorizontalSide above below (Fin.cast above.boundaryRows_eq 0)
      (Fin.cast below.boundaryRows_eq (Fin.last below.boundaryRows))
      (partition.cuts.boxes[(PieceIndices.pieceIndex partition column row.castSucc).val]'(PieceIndices.pieceIndex
        partition column row.castSucc).isLt).yUpper := by
  let partition := partitions.get position
  let above := (request.meshes.get position).entries.get (PieceIndices.pieceIndex partition column row.succ)
  let below := (request.meshes.get position).entries.get (PieceIndices.pieceIndex partition column row.castSucc)
  apply MatchedHorizontalSide.build above below _ _ _ (SurfaceRequest.mesh_x_compatible request position column row.succ
    row.castSucc)
  · have equal := above.y_first.trans (PieceIndices.vertical_neighbor partition column row).symm
    exact ⟨equal.le, equal.symm.le.trans
      (above.partition.y.intervals[(Fin.cast above.boundaryRows_eq 0).val]'(Fin.cast above.boundaryRows_eq
        0).isLt).ordered.le⟩
  · have equal := below.y_last
    exact ⟨(below.partition.y.intervals[(Fin.cast below.boundaryRows_eq (Fin.last below.boundaryRows)).val]'
      (Fin.cast below.boundaryRows_eq (Fin.last below.boundaryRows)).isLt).ordered.le.trans equal.le, equal.ge⟩

/-- On a vertical side the left piece's right trace precedes the right piece's left trace, again with the face-assembly
orientation. -/
def verticalSeamSide (position : Fin grid.faces.regulars.length)
    (column : Fin (PieceIndices.columns (partitions.get position))) (row : Fin ((PieceIndices.rows (partitions.get
      position)) + 1)) :
    let partition := partitions.get position
    let left := (request.meshes.get position).entries.get (PieceIndices.pieceIndex partition column.castSucc row)
    let right := (request.meshes.get position).entries.get (PieceIndices.pieceIndex partition column.succ row)
    ObservationMesh.MatchedVerticalSide left right (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))
      (Fin.cast right.boundaryColumns_eq 0)
      (partition.cuts.boxes[(PieceIndices.pieceIndex partition column.castSucc row).val]'(PieceIndices.pieceIndex
        partition column.castSucc row).isLt).xUpper := by
  let partition := partitions.get position
  let left := (request.meshes.get position).entries.get (PieceIndices.pieceIndex partition column.castSucc row)
  let right := (request.meshes.get position).entries.get (PieceIndices.pieceIndex partition column.succ row)
  apply MatchedVerticalSide.build left right _ _ _ (SurfaceRequest.mesh_y_compatible request position column.castSucc
    column.succ row)
  · have equal := left.x_last
    exact ⟨(left.partition.x.intervals[(Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns)).val]'
      (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns)).isLt).ordered.le.trans equal.le, equal.ge⟩
  · have equal := right.x_first.trans (PieceIndices.horizontal_neighbor partition column row).symm
    exact ⟨equal.le, equal.symm.le.trans
      (right.partition.x.intervals[(Fin.cast right.boundaryColumns_eq 0).val]'(Fin.cast right.boundaryColumns_eq
        0).isLt).ordered.le⟩

set_option genInjectivity false in
/-- Cached matched horizontal and vertical traces between the actual adjacent pieces of one retained face.

Every trace uses the shared request depth and preserves both original model owners and the face-assembly seam
orientation. -/
structure SeamTraces (position : Fin grid.faces.regulars.length) where
  /-- The cached matched traces between vertically adjacent retained pieces. -/ horizontal : Data.Vector.DependentVector
    (fun column : Fin ((PieceIndices.columns (partitions.get position)) + 1) =>
    Data.Vector.DependentVector (fun row : Fin (PieceIndices.rows (partitions.get position)) =>
      (Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides.horizontalSeamSide request position column row).Trace
      request.depth))
  /-- The cached matched traces between horizontally adjacent retained pieces. -/ vertical : Data.Vector.DependentVector
    (fun column : Fin (PieceIndices.columns (partitions.get position)) =>
    Data.Vector.DependentVector (fun row : Fin ((PieceIndices.rows (partitions.get position)) + 1) =>
      (Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides.verticalSeamSide request position column row).Trace
      request.depth))

constructive_injectivity SeamTraces

/-- Construct and cache each actual piece-seam trace at the common retained spatial depth. -/
def SeamTraces.build (position : Fin grid.faces.regulars.length) :
  Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides.SeamTraces request position :=
  ⟨DependentVector.ofFn fun column => DependentVector.ofFn fun row =>
      Trace.build (Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides.horizontalSeamSide request position column
        row) request.depth,
    DependentVector.ofFn fun column => DependentVector.ofFn fun row =>
      Trace.build (Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides.verticalSeamSide request position column row)
        request.depth⟩

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides
