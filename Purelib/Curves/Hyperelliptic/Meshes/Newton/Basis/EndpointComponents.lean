module
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
public import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.EndpointReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.EndpointReadback.SynchronizedSurfaceRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity

open Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests

open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests

@[expose] public section

/-! Reindex all common-basis endpoint chords onto the Newton exterior component. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.EndpointComponents

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Normalization
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {current
    : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {partitions : SurfacePartitions
    observations grid}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains
    sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet}
    {error : Rational}
  {stage : Nat} {cache : Numerics
    domains stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests.PerimeterSamples
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents (componentCachedEndpoints
  componentCachedEndpoints_sum)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples
  (componentSum)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples
  (cachedEndpointSideSum)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.EndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples
  (commonBasis_endpoint_eq_cached)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- The complete common-basis endpoint subtraction is Newton's exterior component correction on the original shared
cache. -/
theorem commonBasis_component_endpoints (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.components.map (fun component =>
      EndpointComponents.componentCachedEndpoints component cache coefficients)) =
      PerimeterSamples.componentSum neighbors .exterior (PerimeterSamples.cachedEndpointSideSum cache coefficients) :=
        by
  have combined := EndpointComponents.componentCachedEndpoints_sum prepared neighbors cache coefficients
  simp only [-eq_self, -iff_self, SelectedPhysicalComponents.componentEvaluation, SelectedSides.value,
    PerimeterSamples.componentSum,
    PerimeterSamples.commonBasis_endpoint_eq_cached, PerimeterSamples.cachedEndpointSideSum] at combined ⊢
  exact combined

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.EndpointComponents
