module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary

public section

/-! Physical endpoint corrections use the original corner cache shared by
the period triangles; no new numerical samples are introduced. -/
namespace Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
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
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (endpointSideSum physicalCentered)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples
  (componentSum componentEndpoints componentBoundary physicalCentered_boundaries)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues (PhysicalComponent)
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

open Purelib.Topology.Polygon.Stokes (edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic in
open Purelib.LinearAlgebra.Gaussian in
/-- Oriented endpoint area of one side from cached outer corners.

Reads the original four corner values in bottom, right, top or left order, retaining the forward coordinate orientation
of each side. -/
@[expose] def cachedSideEndpoint (cache : Numerics domains stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (side : GridSide) : Gaussian :=
  let value := Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position sheet
  match side with
  | .bottom => edgeArea (value 0) (value 1)
  | .right => edgeArea (value 1) (value 2)
  | .top => edgeArea (value 3) (value 2)
  | .left => edgeArea (value 0) (value 3)

open Purelib.Algebra in
open Purelib.LinearAlgebra.Gaussian in
/-- Sum of cached side endpoint areas over both sheets.

Uses the same numerical cache, coefficient vector, regular face and side for both retained readings. -/
@[expose] def cachedEndpointSideSum (cache : Numerics domains stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (side : GridSide) (position : Fin grid.faces.regulars.length) : Gaussian :=
  FiniteSum.Fin.sumFin fun sheet => cachedSideEndpoint cache coefficients position sheet side

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
/-- Read the retained side endpoint sum from cached outer corners.

Transports each sheet sample through its exact side endpoint identity and original outer-corner readback. -/
theorem endpointSideSum_cached
    {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters)
    (side : GridSide) (position : Fin grid.faces.regulars.length) :
    endpointSideSum samples side position = cachedEndpointSideSum cache coefficients side position := by
  unfold endpointSideSum cachedEndpointSideSum
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  let face := (faces.get sheet).get position
  let reading := (samples.get sheet).get position
  cases side with
  | bottom =>
      change reading.bottom.endpoint = _
      rw [Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered.bottom_endpoint reading face]
      change edgeArea (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face false false)
        (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face true false) = _
      rw [Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached,
        Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached]
      rfl
  | right =>
      change reading.right.endpoint = _
      rw [Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered.right_endpoint reading face]
      change edgeArea (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face true false)
        (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face true true) = _
      rw [Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached,
        Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached]
      rfl
  | top =>
      change reading.top.endpoint = _
      rw [Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered.top_endpoint reading face]
      change edgeArea (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face false true)
        (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face true true) = _
      rw [Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached,
        Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached]
      rfl
  | left =>
      change reading.left.endpoint = _
      rw [Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered.left_endpoint reading face]
      change edgeArea (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face false false)
        (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face false true) = _
      rw [Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached,
        Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached]
      rfl

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Curves.Hyperelliptic in
/-- Read one physical component's endpoints from the cached side sums.

Keeps the actual neighbor bank and selected exterior or hole component while replacing each endpoint by its exact cache
readback. -/
theorem componentEndpoints_cached
    {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) (component :
      Meshes.PuncturedGrid.PhysicalComponentValues.PhysicalComponent grid.faces) :
    componentEndpoints samples neighbors component =
      componentSum neighbors component (cachedEndpointSideSum cache coefficients) := by
  simp only [-eq_self, -iff_self, componentEndpoints, componentSum, endpointSideSum_cached samples faces]
  rfl

open Purelib.Algebra in
/-- Express physical centered area through boundaries and cached endpoints.

Preserves the separate exterior and hole boundary terms and subtracts their own selected cached endpoint sums. -/
theorem physicalCentered_cached_boundaries
    {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    physicalCentered samples neighbors =
      (componentBoundary samples neighbors .exterior -
        componentSum neighbors .exterior (cachedEndpointSideSum cache coefficients)) +
      FiniteSum.Fin.sumFin (fun hole => componentBoundary samples neighbors (.hole hole) -
        componentSum neighbors (.hole hole) (cachedEndpointSideSum cache coefficients)) := by
  rw [physicalCentered_boundaries samples neighbors]
  simp only [-eq_self, -iff_self, componentEndpoints_cached samples faces]
  rfl

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
