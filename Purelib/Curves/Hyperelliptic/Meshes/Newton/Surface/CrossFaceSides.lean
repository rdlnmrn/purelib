module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides
import Init.Data.Fin.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
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
public import Purelib.Riemann.Readings.RectangularObservationEndpoints

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Riemann.Readings.RectangularMatchedObservationSides

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh

@[expose] public section

/-! Matched sides between complete surface pieces on different regular faces
or sheet occurrences. Both meshes use the common cut bank and retain their
original primitive owners. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceSides

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
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
  (SurfaceCuts surfaceMeshes surfaceMeshes_x_compatible surfaceMeshes_y_compatible)

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
    grid.faces.regulars} {partitions : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions
    observations grid}
  {surfaceCuts : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains}
  {firstSheet lastSheet : Fin 2} {firstDepth lastDepth : Nat}
  {firstFixed : Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains firstSheet}
    {lastFixed : Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains lastSheet}
  {firstError lastError : Purelib.Data.Rat.Fraction.Rational}

variable (firstRequest : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions
  (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
  firstSheet firstDepth) firstFixed firstError)
  (lastRequest : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    lastSheet lastDepth) lastFixed lastError)
  (first last : Fin grid.faces.regulars.length)
  (firstPiece : Fin (partitions.get first).cuts.boxes.length)
  (lastPiece : Fin (partitions.get last).cuts.boxes.length)

/-- The first piece's upper side is matched to the last piece's lower side. -/
def horizontalFaceSide
    (lowerEq : ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).xLower =
      ((partitions.get last).cuts.boxes[lastPiece.val]'lastPiece.isLt).xLower)
    (upperEq : ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).xUpper =
      ((partitions.get last).cuts.boxes[lastPiece.val]'lastPiece.isLt).xUpper)
    (joined : ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).yUpper =
      ((partitions.get last).cuts.boxes[lastPiece.val]'lastPiece.isLt).yLower) :
    let left := (firstRequest.meshes.get first).entries.get firstPiece
    let right := (lastRequest.meshes.get last).entries.get lastPiece
    ObservationMesh.MatchedHorizontalSide left right (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))
      (Fin.cast right.boundaryRows_eq 0)
      ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).yUpper := by
  let left := (firstRequest.meshes.get first).entries.get firstPiece
  let right := (lastRequest.meshes.get last).entries.get lastPiece
  have compatible : left.partition.x.intervals = right.partition.x.intervals := by
    change ((firstRequest.meshes.get first).entries.get firstPiece).partition.x.intervals =
      ((lastRequest.meshes.get last).entries.get lastPiece).partition.x.intervals
    rw [MeshCompatibility.SurfaceRequest.mesh_x_intervals firstRequest,
      MeshCompatibility.SurfaceRequest.mesh_x_intervals lastRequest]
    exact MeshCompatibility.surfaceMeshes_x_compatible partitions domains surfaceCuts firstSheet lastSheet firstDepth
      lastDepth
      first last firstPiece lastPiece lowerEq upperEq
  apply MatchedHorizontalSide.build left right _ _ _ compatible
  · have equal := left.y_last
    exact ⟨(left.partition.y.intervals[(Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows)).val]'
      (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows)).isLt).ordered.le.trans equal.le, equal.ge⟩
  · have equal := right.y_first.trans joined.symm
    exact ⟨equal.le, equal.symm.le.trans
      (right.partition.y.intervals[(Fin.cast right.boundaryRows_eq 0).val]'
        (Fin.cast right.boundaryRows_eq 0).isLt).ordered.le⟩

/-- Match the first retained piece's right side to the last piece's left side.

Both original model owners and their common vertical interval list are retained across faces or sheets. -/
def verticalFaceSide
    (lowerEq : ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).yLower =
      ((partitions.get last).cuts.boxes[lastPiece.val]'lastPiece.isLt).yLower)
    (upperEq : ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).yUpper =
      ((partitions.get last).cuts.boxes[lastPiece.val]'lastPiece.isLt).yUpper)
    (joined : ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).xUpper =
      ((partitions.get last).cuts.boxes[lastPiece.val]'lastPiece.isLt).xLower) :
    let left := (firstRequest.meshes.get first).entries.get firstPiece
    let right := (lastRequest.meshes.get last).entries.get lastPiece
    ObservationMesh.MatchedVerticalSide left right (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))
      (Fin.cast right.boundaryColumns_eq 0)
      ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).xUpper := by
  let left := (firstRequest.meshes.get first).entries.get firstPiece
  let right := (lastRequest.meshes.get last).entries.get lastPiece
  have compatible : left.partition.y.intervals = right.partition.y.intervals := by
    change ((firstRequest.meshes.get first).entries.get firstPiece).partition.y.intervals =
      ((lastRequest.meshes.get last).entries.get lastPiece).partition.y.intervals
    rw [MeshCompatibility.SurfaceRequest.mesh_y_intervals firstRequest,
      MeshCompatibility.SurfaceRequest.mesh_y_intervals lastRequest]
    exact MeshCompatibility.surfaceMeshes_y_compatible partitions domains surfaceCuts firstSheet lastSheet firstDepth
      lastDepth
      first last firstPiece lastPiece lowerEq upperEq
  apply MatchedVerticalSide.build left right _ _ _ compatible
  · have equal := left.x_last
    exact ⟨(left.partition.x.intervals[(Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns)).val]'
      (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns)).isLt).ordered.le.trans equal.le, equal.ge⟩
  · have equal := right.x_first.trans joined.symm
    exact ⟨equal.le, equal.symm.le.trans
      (right.partition.x.intervals[(Fin.cast right.boundaryColumns_eq 0).val]'
        (Fin.cast right.boundaryColumns_eq 0).isLt).ordered.le⟩

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceSides
