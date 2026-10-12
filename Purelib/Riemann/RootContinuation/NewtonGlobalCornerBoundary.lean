module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.Periods.BilinearGridBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

public section

/-! The global endpoint correction is the sum of the actual outer corner
polygons on both sheets. No endpoint term is discarded as a contact error. -/
namespace Purelib.Riemann.RootContinuation.NewtonGlobalCornerBoundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples
  SheetAssemblies SheetPerimeters SheetFaces)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (endpointSideSum pairedEndpoints pairedCentered physicalEndpoints physicalCentered exterior_decomposition)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {partitions : SurfacePartitions observations grid}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet} {error : Purelib.Data.Rat.Fraction.Rational}
  {stage : Nat} {cache : Numerics domains stage} {coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests.PerimeterSamples

variable {requests : SynchronizedSurfaceRequests coarse fixed error} {traces : PerimeterTraces requests}
  (samples : PerimeterSamples requests traces cache coefficients)

open Purelib.Algebra in
/-- Oriented sum of all retained side endpoint corrections.

Adds bottom and right and subtracts top and left for each regular face. -/
@[expose] def endpointTotal : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => endpointSideSum samples .bottom position + endpointSideSum samples .right
    position -
    endpointSideSum samples .top position - endpointSideSum samples .left position)

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- Sum of the four-corner areas over regular faces and both sheets.

Reads the actual extreme partition corners in lower-left, lower-right, upper-right, upper-left order. -/
@[expose] def cornerBoundary {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet : Fin 2 =>
    let face := (faces.get sheet).get position
    BilinearGridBoundary.cornerArea (face.corners 0 0).lowerLeft
      (face.corners (Fin.last (Meshes.Newton.Surface.PieceIndices.columns (partitions.get position))) 0).lowerRight
      (face.corners (Fin.last (Meshes.Newton.Surface.PieceIndices.columns (partitions.get position))) (Fin.last
        (Meshes.Newton.Surface.PieceIndices.rows (partitions.get position)))).upperRight
      (face.corners 0 (Fin.last (Meshes.Newton.Surface.PieceIndices.rows (partitions.get position)))).upperLeft))

open Purelib.Algebra in
/-- The total endpoint correction is the retained corner boundary.

Uses each face endpoint identity and pointwise finite-sum transport across the regular-face and sheet indices. -/
theorem endpointTotal_readback {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters) :
    endpointTotal samples = cornerBoundary faces := by
  unfold endpointTotal cornerBoundary
  apply FiniteSum.Fin.sumFin_congr
  intro position
  unfold endpointSideSum
  rw [← FiniteSum.Fin.sumFin_add, ← FiniteSum.Fin.sumFin_sub, ← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  exact ((samples.get sheet).get position).endpoint_total ((faces.get sheet).get position)

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
/-- Split endpoint corrections into paired and physical contributions.

Uses the actual neighbor bank to partition each oriented side sum into regular-contact and physical-boundary terms. -/
theorem endpointTotal_split (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    endpointTotal samples = pairedEndpoints samples + physicalEndpoints samples neighbors := by
  have paired : pairedEndpoints samples =
      (FiniteSum.Fin.sumFin (fun p =>
        Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
        ((neighbors.entries.get p).right) (endpointSideSum samples .right p)) -
        FiniteSum.Fin.sumFin (fun p =>
          Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
          ((neighbors.entries.get p).left) (endpointSideSum samples .left p))) -
      (FiniteSum.Fin.sumFin (fun p =>
        Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
        ((neighbors.entries.get p).top) (endpointSideSum samples .top p)) -
        FiniteSum.Fin.sumFin (fun p =>
          Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
          ((neighbors.entries.get p).bottom) (endpointSideSum samples .bottom p))) := by
    unfold pairedEndpoints
    exact congrArg₂ (· - ·)
      (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.NeighborBank.pair_sum neighbors .right
        (endpointSideSum samples .right) (endpointSideSum samples .left))
      (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.NeighborBank.pair_sum neighbors .top
        (endpointSideSum samples .top) (endpointSideSum samples .bottom))
  have split (side : GridSide) : FiniteSum.Fin.sumFin (endpointSideSum samples side) =
      FiniteSum.Fin.sumFin (fun p =>
        Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
        (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
        (neighbors.entries.get p) side) (endpointSideSum samples side p)) +
        FiniteSum.Fin.sumFin (fun p =>
          Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue
          (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
          (neighbors.entries.get p) side) (endpointSideSum samples side p)) := by
    rw [FiniteSum.Fin.sumFin_congr (fun p =>
      Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.value_split
      (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at (neighbors.entries.get
      p) side) (endpointSideSum samples side p)), FiniteSum.Fin.sumFin_add]
  unfold endpointTotal
  rw [paired]
  simp only [-eq_self, -iff_self, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub]
  rw [split .bottom, split .right, split .top, split .left]
  dsimp only [physicalEndpoints,
    Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at]
  ring1

/-- Decompose exterior area into centered contacts, physical sides and corners.

Combines the retained exterior decomposition with the exact total endpoint readback, preserving both centered
contributions. -/
theorem exterior_eq_corner_boundary {assemblies : SheetAssemblies requests (cache := cache) (coefficients :=
  coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    samples.exterior = pairedCentered samples + physicalCentered samples neighbors + cornerBoundary faces := by
  rw [exterior_decomposition samples neighbors, ← endpointTotal_split samples neighbors, endpointTotal_readback samples
    faces]

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Riemann.RootContinuation.NewtonGlobalCornerBoundary
