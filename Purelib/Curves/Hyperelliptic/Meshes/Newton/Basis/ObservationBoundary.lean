module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
public import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationComponents
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.EndpointReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CanonicalSurfaceEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Riemann

public section

/-! Assemble observed component bounds with the original cached endpoint subtraction. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationBoundary

open Purelib

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational} {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}

attribute [local congr] FiniteSum.Fin.sumFin_congr

variable {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {partitions :
  Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {coarse : (sheet : Fin 2) → Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Fraction.Rational}
  {requests : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error} {traces :
    Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces requests}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  (samples : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples requests traces cache
    coefficients)
  {differential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- All retained component endpoints are exactly the cached Newton exterior correction. -/
theorem AllSurfacePreparation.cachedEndpoints_sum_newton
    (prepared :
      PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains differential)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank grid.faces) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.components.map (fun component =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents.componentCachedEndpoints component cache
      coefficients)) =
      RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentSum
        neighbors .exterior
        (PerimeterSamples.cachedEndpointSideSum
        cache coefficients) := by
  apply (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents.componentCachedEndpoints_sum prepared
    neighbors cache coefficients).trans
  unfold Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation
    RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentSum
  simp only [Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value, -eq_self, -iff_self]
  have sides (side : Meshes.GridLiftedDualSteps.GridSide) (position : Fin grid.faces.regulars.length) :
      FiniteSum.Fin.sumFin (fun sheet =>
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter.cachedEndpoint cache
        coefficients position sheet side) =

          PerimeterSamples.cachedEndpointSideSum
          cache coefficients side position :=
    FiniteSum.Fin.sumFin_congr (fun sheet =>
      EndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples.commonBasis_endpoint_eq_cached
      position sheet side)
  simp only [sides, -eq_self, -iff_self]
  rfl

/-- The centered component sum keeps exactly the exterior endpoint correction. -/
theorem AllSurfacePreparation.observedBoundary_sum
    (prepared :
      PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains differential)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank grid.faces) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.components.map (fun component =>
      component.prepared.observedSides samples -
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents.componentCachedEndpoints component cache
        coefficients)) =
      RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentBoundary
        samples neighbors .exterior -
        RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentSum
          neighbors .exterior
          (PerimeterSamples.cachedEndpointSideSum
          cache coefficients) := by
  rw [Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_sub, prepared.observedSides_sum samples neighbors,
    Hyperelliptic.Meshes.Newton.Basis.ObservationBoundary.AllSurfacePreparation.cachedEndpoints_sum_newton prepared
      neighbors]

/-- Consume component bounds in the exact Newton exterior expression, including its endpoint subtraction. -/
theorem AllSurfacePreparation.canonical_observation_energy_upper
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank grid.faces)
    (readings : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
      (cache.get row) lifted.mesh)
    {allowance : Fraction.Rational}
    (bounded : ∀ component ∈
      (PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      (lifted := lifted) regular domains differential).components,
      (component.prepared.observedSides samples -
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents.componentCachedEndpoints component cache
        coefficients +
        Path.PairedIncrementArea.area (component.program.indexed.map
          (fun edge => Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values
              edge)))).im / 4 ≤
        allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :
    (RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentBoundary
      samples neighbors .exterior -
      RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentSum
        neighbors .exterior
        (PerimeterSamples.cachedEndpointSideSum
        cache coefficients) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (lifted.exteriorBoundaries.map (fun word =>
          Path.PairedIncrementArea.area (word.map
          (fun edge => Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values
              edge)))))).im / 4 ≤

        ((PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
        (lifted := lifted) regular domains differential).components.length : Fraction.Rational) *
        allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bound :=
    ExteriorProgram.AllSurfacePreparation.built_canonical_energy_upper
    cache coefficients readings
    (fun component => component.prepared.observedSides samples -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents.componentCachedEndpoints component cache
      coefficients) bounded
  rw [Hyperelliptic.Meshes.Newton.Basis.ObservationBoundary.AllSurfacePreparation.observedBoundary_sum samples _
    neighbors] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationBoundary
