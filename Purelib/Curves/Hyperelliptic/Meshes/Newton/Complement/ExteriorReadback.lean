module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
import Purelib.Riemann.RootContinuation.NewtonSelectedSideGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Tactic.Ring

public section

/-! Exact exterior ownership after annular excision, with all endpoint chords retained. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorReadback

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (SheetAssemblies SheetPerimeters
  SheetFaces PerimeterTraces PerimeterSamples)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower (remainingFaceMask)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (centeredSideSum)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples
  (componentSum componentCentered componentBoundary componentBoundary_split)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples
  (cachedEndpointSideSum componentEndpoints_cached)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides (value)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents (componentEvaluation)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius
    : Data.Rat.Fraction.Rational} {grid : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid
    preparation target radius}
  {observations : Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars}
    {partitions : Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {coarse : (sheet : Fin 2) → Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error
    : Data.Rat.Fraction.Rational}
  {stage : Nat} {cache : Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests.PerimeterSamples

variable {requests : Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error}
  {traces : Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces requests}
  (samples : Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples requests traces
    cache coefficients)
  {lifted : Riemann.Meshes.LiftedPuncturedGrid grid.punctured} (excision :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides in
/-- Excision preserves the original exterior contribution of every retained neighbor side. -/
private theorem exterior_value_retained (position : Fin grid.faces.regulars.length) (side :
  GridLiftedDualSteps.GridSide)
    (neighbor : PuncturedFaces.SideNeighbor grid.faces (grid.faces.regulars[position.val]'position.isLt) side)
    (value : Data.Gaussian.Basic.Canonical) :
    SideNeighbor.componentValue neighbor .exterior (SelectedSides.value (ObservationLower.remainingFaceMask excision
      position) value) =
      SideNeighbor.componentValue neighbor .exterior value := by
  cases neighbor with
  | exterior exterior =>
      have retained : ObservationLower.remainingFaceMask excision position = true := by
        change (!(AllHoleExcision.fineMask excision position)) = true
        cases selected : AllHoleExcision.fineMask excision position with
        | false => rfl
        | true => exact (AllHoleExcision.selected_not_exterior excision position side selected exterior).elim
      change SelectedSides.value (ObservationLower.remainingFaceMask excision position) value = value
      rw [retained]
      rfl
  | neighbor cell member matching location => cases location <;> rfl

/-- Annular excision preserves every original exterior side. -/
theorem remainingExterior_eq (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation neighbors
      (ObservationLower.remainingFaceMask excision) (PerimeterSamples.centeredSideSum samples) .exterior =

        PerimeterSamples.componentCentered
        samples neighbors .exterior := by
  unfold SelectedPhysicalComponents.componentEvaluation PerimeterSamples.componentCentered PerimeterSamples.componentSum
  rw [FiniteSum.Fin.sumFin_congr (fun p =>
    exterior_value_retained
    excision p .right (neighbors.entries.get p).right (PerimeterSamples.centeredSideSum samples .right p)),
    FiniteSum.Fin.sumFin_congr (fun p =>
      exterior_value_retained
      excision p .left (neighbors.entries.get p).left (PerimeterSamples.centeredSideSum samples .left p)),
    FiniteSum.Fin.sumFin_congr (fun p =>
      exterior_value_retained
      excision p .top (neighbors.entries.get p).top (PerimeterSamples.centeredSideSum samples .top p)),
    FiniteSum.Fin.sumFin_congr (fun p =>
      exterior_value_retained
      excision p .bottom (neighbors.entries.get p).bottom (PerimeterSamples.centeredSideSum samples .bottom p))]

/-- Read the surviving exterior as the actual owned perimeter minus its original cached endpoint chords. -/
theorem remainingExterior_cached
    {assemblies : SynchronizedSurfaceRequests.SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SynchronizedSurfaceRequests.SheetPerimeters requests assemblies} (faces :
      SynchronizedSurfaceRequests.SheetFaces requests perimeters)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    SelectedPhysicalComponents.componentEvaluation neighbors (ObservationLower.remainingFaceMask excision)
      (PerimeterSamples.centeredSideSum samples) .exterior =
      PerimeterSamples.componentBoundary samples neighbors .exterior -
        PerimeterSamples.componentSum neighbors .exterior (PerimeterSamples.cachedEndpointSideSum cache coefficients) :=
          by
  rw
    [remainingExterior_eq
    samples excision, PerimeterSamples.componentBoundary_split samples,
    ← PerimeterSamples.componentEndpoints_cached samples faces neighbors .exterior]
  ring1

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorReadback
