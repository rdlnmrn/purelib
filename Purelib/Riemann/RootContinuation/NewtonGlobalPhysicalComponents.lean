module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces

public section

/-! The surviving complete-surface physical term is split by its actual
exterior and hole owners. Every component retains its endpoint correction. -/
namespace Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents

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
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples (sideSum)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (centeredSideSum endpointSideSum side_decomposition physicalCentered)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues (PhysicalComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor (componentValue
  physical_components)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor
  (physicalValue)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {partitions : SurfacePartitions observations grid}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet} {error : Rational}
  {stage : Nat} {cache : Numerics domains stage} {coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests.PerimeterSamples

variable {requests : SynchronizedSurfaceRequests coarse fixed error} {traces : PerimeterTraces requests}
  (samples : PerimeterSamples requests traces cache coefficients)

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- Oriented sum of side values belonging to one physical component.

Selects the exterior or one hole using the retained neighbor bank, with right minus left minus top plus bottom
orientation. -/
@[expose] def componentSum (neighbors : PuncturedFaces.NeighborBank grid.faces) (component :
  PhysicalComponent grid.faces)
    (values : GridSide → Fin grid.faces.regulars.length → Basic.Canonical) : Gaussian :=
  sumFin (fun p => PhysicalComponentValues.SideNeighbor.componentValue
    ((neighbors.entries.get p).right) component (values .right p)) -
    sumFin (fun p => PhysicalComponentValues.SideNeighbor.componentValue
      ((neighbors.entries.get p).left) component (values .left p)) -
    (sumFin (fun p => PhysicalComponentValues.SideNeighbor.componentValue
      ((neighbors.entries.get p).top) component (values .top p)) -
      sumFin (fun p => PhysicalComponentValues.SideNeighbor.componentValue
        ((neighbors.entries.get p).bottom) component (values .bottom p)))

section
open Purelib.Curves.Hyperelliptic
/-- Centered side contribution of a selected physical component.

Applies the component sum to the retained centered perimeter samples. -/
@[expose] def componentCentered (neighbors : PuncturedFaces.NeighborBank grid.faces) (component :
  PhysicalComponent grid.faces) : Gaussian :=
  componentSum neighbors component (centeredSideSum samples)

/-- Endpoint correction of a selected physical component.

Applies the component sum to the retained endpoint side corrections. -/
@[expose] def componentEndpoints (neighbors : PuncturedFaces.NeighborBank grid.faces) (component :
  PhysicalComponent grid.faces) : Gaussian :=
  componentSum neighbors component (endpointSideSum samples)

/-- Full boundary contribution of a selected physical component.

Applies the component sum to the original side samples without altering the neighbor classification. -/
@[expose] def componentBoundary (neighbors : PuncturedFaces.NeighborBank grid.faces) (component :
  PhysicalComponent grid.faces) : Gaussian :=
  componentSum neighbors component (sideSum samples)

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- Selecting one physical component preserves addition.

Checks exterior, regular-neighbor and hole-neighbor cases using the actual retained component identity. -/
private theorem component_add {face : RegularFace grid.shrunk.prepared.toBranchCellBank} {side : GridSide}
    (neighbor : PuncturedFaces.SideNeighbor grid.faces face side) (component :
      PhysicalComponent grid.faces)
    (first last : Basic.Canonical) : PhysicalComponentValues.SideNeighbor.componentValue neighbor
      component (first + last) =
      PhysicalComponentValues.SideNeighbor.componentValue neighbor component first +
        PhysicalComponentValues.SideNeighbor.componentValue neighbor component last := by
  cases neighbor with
  | exterior equal =>
    cases component <;> (simp only [PhysicalComponentValues.SideNeighbor.componentValue, add_zero,
      -eq_self, -iff_self]; rfl)
  | neighbor cell member matching location =>
      cases location with
      | regular found equal =>
        cases component <;> (simp only [PhysicalComponentValues.SideNeighbor.componentValue,
          add_zero, -eq_self, -iff_self]; rfl)
      | hole found equal =>
        cases component with
        | exterior =>
          simp only [PhysicalComponentValues.SideNeighbor.componentValue, add_zero, -eq_self,
            -iff_self]; rfl
        | hole selected =>
          by_cases same : selected = found
          · simp only [PhysicalComponentValues.SideNeighbor.componentValue, if_pos same, -eq_self,
              -iff_self]; rfl
          · simp only [PhysicalComponentValues.SideNeighbor.componentValue, if_neg same, add_zero,
              -eq_self, -iff_self]; rfl

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
/-- Split a component boundary into centered and endpoint contributions.

Transports the side decomposition pointwise through component selection and the four oriented finite sums. -/
theorem componentBoundary_split (neighbors : PuncturedFaces.NeighborBank grid.faces) (component :
  PhysicalComponent grid.faces) :
    componentBoundary samples neighbors component =
      componentCentered samples neighbors component + componentEndpoints samples neighbors component := by
  have split (side : GridSide) :
      sumFin (fun p => PhysicalComponentValues.SideNeighbor.componentValue
        (FaceNeighbors.at
        (neighbors.entries.get p) side) component (sideSum samples side p)) =
      sumFin (fun p => PhysicalComponentValues.SideNeighbor.componentValue
        (FaceNeighbors.at
        (neighbors.entries.get p) side) component (centeredSideSum samples side p)) +
      sumFin (fun p => PhysicalComponentValues.SideNeighbor.componentValue
        (FaceNeighbors.at
        (neighbors.entries.get p) side) component (endpointSideSum samples side p)) := by
    rw [← sumFin_add]
    apply sumFin_congr
    intro p
    rw [side_decomposition samples side p, component_add]
  have bottom := split .bottom
  have right := split .right
  have top := split .top
  have left := split .left
  dsimp only [FaceNeighbors.at]
    at bottom right top left
  unfold componentBoundary componentCentered componentEndpoints componentSum
  rw [bottom, right, top, left]
  ring1

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- Split a physical side sum into exterior and individual-hole terms.

Uses the retained neighbor classification and swaps the finite face and hole sums without changing their witnesses. -/
private theorem side_components (neighbors : PuncturedFaces.NeighborBank grid.faces) (side : GridSide)
    (values : Fin grid.faces.regulars.length → Basic.Canonical) :
    sumFin (fun p =>
      physicalValue
      (FaceNeighbors.at (neighbors.entries.get
      p) side) (values p)) =
      sumFin (fun p => PhysicalComponentValues.SideNeighbor.componentValue
        (FaceNeighbors.at
        (neighbors.entries.get p) side) .exterior (values p)) +
      sumFin (fun hole => sumFin (fun p =>
        PhysicalComponentValues.SideNeighbor.componentValue
        (FaceNeighbors.at
        (neighbors.entries.get p) side) (.hole hole) (values p))) := by
  rw [sumFin_congr (fun p => PhysicalComponentValues.SideNeighbor.physical_components
    (FaceNeighbors.at (neighbors.entries.get p)
    side) (values p)),
    sumFin_add, FiniteSum.Fin.sumFin_swap]

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
/-- Split the physical centered value into exterior and hole components.

Applies the component decomposition separately to all four oriented sides. -/
theorem physicalCentered_components (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    physicalCentered samples neighbors = componentCentered samples neighbors .exterior +
      sumFin (fun hole => componentCentered samples neighbors (.hole hole)) := by
  have bottom := side_components neighbors .bottom (centeredSideSum samples .bottom)
  have right := side_components neighbors .right (centeredSideSum samples .right)
  have top := side_components neighbors .top (centeredSideSum samples .top)
  have left := side_components neighbors .left (centeredSideSum samples .left)
  dsimp only [FaceNeighbors.at]
    at bottom right top left
  unfold physicalCentered
  rw [bottom, right, top, left]
  simp only [componentCentered, componentSum, sumFin_sub]
  ring1

open Purelib.Algebra in
/-- Express physical centered area through full boundaries and endpoint corrections.

Keeps the exterior term and each hole term separate, subtracting the corresponding retained endpoint correction from
each boundary. -/
theorem physicalCentered_boundaries (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    physicalCentered samples neighbors =
      (componentBoundary samples neighbors .exterior - componentEndpoints samples neighbors .exterior) +
      sumFin (fun hole => componentBoundary samples neighbors (.hole hole) - componentEndpoints samples
        neighbors (.hole hole)) := by
  have readback (component) : componentCentered samples neighbors component =
      componentBoundary samples neighbors component - componentEndpoints samples neighbors component := by
    rw [componentBoundary_split samples neighbors component]
    ring1
  rw [physicalCentered_components samples neighbors, readback .exterior]
  exact congrArg (_ + ·) (sumFin_congr fun hole => readback (.hole hole))

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
