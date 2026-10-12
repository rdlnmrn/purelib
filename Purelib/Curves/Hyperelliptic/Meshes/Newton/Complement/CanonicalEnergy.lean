module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationBoundary
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
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
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Riemann

public section

/-! Transport common-basis component energy through the paid remaining-band comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CanonicalEnergy

open Purelib

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational} (allocated : Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest
    preparation target radius)
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {lifted :
    Meshes.LiftedPuncturedGrid allocated.family.single.grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    allocated.family.single.grid.faces.regulars} {partitions : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions
    observations allocated.family.single.grid}
  {coarse : (sheet : Fin 2) → Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Fraction.Rational}
  {stage : Nat} {cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage} {coefficients
    : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests

variable {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision allocated.family.single.grid lifted}
  {requests : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error} {traces :
    Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces requests}
  {position : Fin allocated.family.single.grid.faces.regulars.length} {side : Meshes.GridLiftedDualSteps.GridSide}

open Purelib.Data.Rat.Fraction.Compatibility

namespace RemainingBandRequest

variable {floor : Nat} {allowance : Fraction.Rational}

variable {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
  Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus}

/-- Pay the remaining-band error against the acquired canonical component bounds.
The estimate retains the canonical joining polygons and their original endpoint corrections. -/
theorem canonical_energy_upper
    (request : Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest
      (grid := allocated.family.single.grid) excision traces floor)
    (later : request.index ≤ stage) (samples :
      Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples requests traces cache
      coefficients)
    {assemblies : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetAssemblies requests (cache :=
      cache) (coefficients := coefficients)}
    {perimeters : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetPerimeters requests assemblies}
      (faces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetFaces requests perimeters)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank allocated.family.single.grid.faces)
    (positive : 0 < allowance)
    (targetLe : target ≤
      BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation) allowance)
    (readings : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
      (cache.get row) lifted.mesh)
    {componentAllowance : Fraction.Rational}
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
        componentAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :

      (CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
      excision samples neighbors + Data.Gaussian.Norm.Sum.Basic.gaussianSum (lifted.exteriorBoundaries.map (fun word =>
      Path.PairedIncrementArea.area (word.map (fun edge => Path.ConjugatePathReadback.conjugateDiagonal
        (FiniteSum.Fin.sumFin fun row => coefficients row *
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values
          edge)))))).im / 4 ≤

        (((PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
        (lifted := lifted) regular domains differential).components.length : Fraction.Rational) *
        componentAllowance + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  let joining := Data.Gaussian.Norm.Sum.Basic.gaussianSum (lifted.exteriorBoundaries.map (fun word =>
      Path.PairedIncrementArea.area (word.map (fun edge => Path.ConjugatePathReadback.conjugateDiagonal
        (FiniteSum.Fin.sumFin fun row => coefficients row *
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values
          edge)))))
  have comparison :=
    ExteriorComparison.SynchronizedSurfaceRequests.RemainingBandRequest.exterior_energy_lower
    allocated request later samples faces neighbors positive targetLe joining
  have upper :=
    Hyperelliptic.Meshes.Newton.Basis.ObservationBoundary.AllSurfacePreparation.canonical_observation_energy_upper
    samples neighbors readings bounded
  rw [Gaussian.Basic.add_comm joining
    (CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
    excision samples neighbors),
    Gaussian.Basic.add_comm joining
      (RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentBoundary
        samples neighbors .exterior -
        RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentSum
          neighbors .exterior
          (PerimeterSamples.cachedEndpointSideSum
          cache coefficients))] at comparison
  have paid := Fraction.Order.Arithmetic.add_le_add_right_direct (comparison.trans upper) (allowance *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
  exact (show
    (CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
    excision samples neighbors + joining).im / 4 =

      (CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
      excision samples neighbors + joining).im / 4 -
      allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients + allowance *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
    (paid.trans_eq (by ring1))

end RemainingBandRequest
end SynchronizedSurfaceRequests
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CanonicalEnergy
