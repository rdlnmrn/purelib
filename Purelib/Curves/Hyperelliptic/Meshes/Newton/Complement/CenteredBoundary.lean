module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.BilinearGridBoundary
public import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Riemann.RootContinuation.NewtonGlobalCornerBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SurfaceEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SurfaceEnergy.SynchronizedSurfaceRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.TwoSheetRequest

open Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests

open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary

public section

/-! Exact centered perimeter decomposition after annular excision.
The selected physical and newly exposed regular sides remain explicit. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary

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
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (SheetAssemblies SheetPerimeters
  SheetFaces PerimeterTraces PerimeterSamples)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples (sideSum)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (centeredSideSum endpointSideSum side_decomposition)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower (remainingFaceMask)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid grid.punctured}
  {observations : Purelib.Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {partitions : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions
    observations grid}
  {coarse : (sheet : Fin 2) → Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains
    sheet}
  {fixed : (sheet : Fin 2) → Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet}
    {error : Purelib.Data.Rat.Fraction.Rational}
  {stage : Nat} {cache : Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains
    stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests.PerimeterSamples

variable {requests : Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed
  error} {traces : Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces
  requests}
  (excision : Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
  (samples : Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples requests
    traces cache coefficients)

/-- The centered paired-side evaluation on the actual regular faces remaining after excision. -/
@[expose] def remainingPairedCentered : Gaussian :=
  SelectedEvaluationPartition.pairedEvaluation (ObservationLower.remainingFaceMask excision)
    (PerimeterSamples.centeredSideSum samples)

/-- The centered physical and selection-interface boundary evaluation of the retained complement. -/
@[expose] def remainingBoundaryCentered (neighbors : PuncturedFaces.NeighborBank grid.faces) : Gaussian :=
  SelectedSides.boundaryEvaluation neighbors (ObservationLower.remainingFaceMask excision)
    (PerimeterSamples.centeredSideSum samples)

/-- The selected perimeter evaluation of the original endpoint-area contributions. -/
@[expose] def remainingEndpointTotal : Gaussian :=
  SelectedEvaluationPartition.perimeterEvaluation (ObservationLower.remainingFaceMask excision)
    (PerimeterSamples.endpointSideSum samples)

/-- The signed corner areas of the original remaining faces on both retained sheets. -/
@[expose] def remainingCornerBoundary {assemblies : SynchronizedSurfaceRequests.SheetAssemblies requests (cache :=
  cache) (coefficients := coefficients)}
    {perimeters : SynchronizedSurfaceRequests.SheetPerimeters requests assemblies} (faces :
      SynchronizedSurfaceRequests.SheetFaces requests perimeters) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => SelectedSides.value (ObservationLower.remainingFaceMask excision position)
    (FiniteSum.Fin.sumFin (fun sheet : Fin 2 =>
    let face := (faces.get sheet).get position
    BilinearGridBoundary.cornerArea (face.corners 0 0).lowerLeft
      (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) 0).lowerRight
      (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) (Fin.last (PieceIndices.rows
        (partitions.get position)))).upperRight
      (face.corners 0 (Fin.last (PieceIndices.rows (partitions.get position)))).upperLeft)))

/-- The original selected endpoint-area total equals the retained remaining-face corner boundary. -/
private theorem remaining_endpointTotal_readback {assemblies : SynchronizedSurfaceRequests.SheetAssemblies requests
  (cache := cache) (coefficients := coefficients)}
    {perimeters : SynchronizedSurfaceRequests.SheetPerimeters requests assemblies} (faces :
      SynchronizedSurfaceRequests.SheetFaces requests perimeters) :

      remainingEndpointTotal
      excision samples =
      remainingCornerBoundary
      excision faces := by
  unfold CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingEndpointTotal
    SelectedEvaluationPartition.perimeterEvaluation
    remainingCornerBoundary
  apply FiniteSum.Fin.sumFin_congr
  intro position
  apply congrArg (SelectedSides.value (ObservationLower.remainingFaceMask excision position))
  unfold PerimeterSamples.endpointSideSum
  rw [← FiniteSum.Fin.sumFin_add, ← FiniteSum.Fin.sumFin_sub, ← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  exact ((samples.get sheet).get position).endpoint_total ((faces.get sheet).get position)

/-- The retained complement exterior splits into its centered perimeter and original endpoint-area total. -/
private theorem remaining_exterior_split :

      SurfaceEnergy.SynchronizedSurfaceRequests.PerimeterSamples.remainingExterior
      excision samples =
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.perimeterEvaluation
        (ObservationLower.remainingFaceMask excision) (PerimeterSamples.centeredSideSum samples) +

          remainingEndpointTotal
          excision samples := by
  unfold PerimeterSamples.remainingExterior
    CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingEndpointTotal
    SelectedEvaluationPartition.perimeterEvaluation
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  rw [PerimeterSamples.side_decomposition samples .bottom position, PerimeterSamples.side_decomposition samples .right
    position,
    PerimeterSamples.side_decomposition samples .top position, PerimeterSamples.side_decomposition samples .left
      position]
  cases ObservationLower.remainingFaceMask excision position with
  | false =>
      simp only [-eq_self, -iff_self, SelectedSides.value,
        if_neg (by decide : ¬ false = true)]
      rfl
  | true =>
      simp only [-eq_self, -iff_self, SelectedSides.value, if_pos rfl]
      ring1

/-- The actual complement exterior equals the centered paired contribution, centered boundary and retained corner
boundary. -/
theorem remaining_exterior_eq_corner_boundary
    {assemblies : SynchronizedSurfaceRequests.SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SynchronizedSurfaceRequests.SheetPerimeters requests assemblies} (faces :
      SynchronizedSurfaceRequests.SheetFaces requests perimeters)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    PerimeterSamples.remainingExterior excision samples =
      remainingPairedCentered
      excision samples +

        remainingBoundaryCentered
        excision samples neighbors +
        remainingCornerBoundary
        excision faces := by
  rw
    [remaining_exterior_split
    excision samples,
    SelectedEvaluationPartition.perimeter_partition neighbors (ObservationLower.remainingFaceMask excision)
      (PerimeterSamples.centeredSideSum samples),

      remaining_endpointTotal_readback
      excision samples faces]
  rfl

/-- The complement's centered boundary splits exactly into original physical sides and newly exposed regular interfaces.
-/
theorem remaining_boundary_components (neighbors : PuncturedFaces.NeighborBank grid.faces) :

      remainingBoundaryCentered
      excision samples neighbors =
      SelectedSides.physicalEvaluation neighbors (ObservationLower.remainingFaceMask excision)
        (PerimeterSamples.centeredSideSum samples) +
        SelectedSides.interfaceEvaluation (ObservationLower.remainingFaceMask excision)
          (PerimeterSamples.centeredSideSum samples) :=
  SelectedSides.boundaryEvaluation_partition neighbors (ObservationLower.remainingFaceMask excision)
    (PerimeterSamples.centeredSideSum samples)

end SynchronizedSurfaceRequests.PerimeterSamples
