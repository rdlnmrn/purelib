module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

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
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.RadialTriangles
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
public import Purelib.Riemann.RootContinuation.NewtonPhysicalPerimeterEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
public import Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.RootContinuation.NewtonScheduledExteriorCapEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAccuracy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshReindex
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests

public section

/-! Pay the remaining centered boundary on the shared regular cap schedule. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CapEnergy

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  (allocated : Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest preparation target radius)
  {lifted : Meshes.LiftedPuncturedGrid allocated.family.single.grid.punctured} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    allocated.family.single.grid.faces.regulars}
  {stage : Nat} {cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {fixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {surfaceTarget
    physicalTarget : Fraction.Rational}
  {minimum floor coarseDepth : Nat}
  {preparations : Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {partitions :
    Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations allocated.family.single.grid}
  (shared : Branches.NewtonSharedExteriorCuts.SharedExteriorCuts partitions preparations)
  {initialWhole : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
    coarseDepth) fixed surfaceTarget}
  {surfaceFixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet}
  {pieceDepth : Nat} {error : Fraction.Rational}
  {initialPieces : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests
    (fun sheet => Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
      sheet pieceDepth) surfaceFixed error}
  (schedule : Topology.NewtonPhysicalSurfaceSchedule.PhysicalSurfaceSchedule preparations initialWhole initialPieces
    physicalTarget minimum floor)
  {traces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces schedule.surface}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  (samples : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples schedule.surface traces
    cache coefficients)
  {assemblies : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetAssemblies schedule.surface (cache
    := cache) (coefficients := coefficients)}
  {perimeters : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetPerimeters schedule.surface
    assemblies} (faces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetFaces schedule.surface
    perimeters)
  (whole : (position : Fin allocated.family.single.grid.faces.regulars.length) → (sheet : Fin 2) →
    RootContinuation.NewtonPhysicalPerimeterEnergy.SynchronizedSurfaceRequests.PerimeterSamples.WholeFaceEnergyAssembly
      schedule.physical cache coefficients position sheet)
  (wholePerimeters : (position : Fin allocated.family.single.grid.faces.regulars.length) → (sheet : Fin 2) → (whole
    position sheet).Perimeter)
  {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {prepared :
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential}
  (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
  {box : Rational.Box} {polynomials :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box}
  {bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials} {capTarget :
    Fraction.Rational} {capMinimum : Nat}
  (capRequest : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds
    attached.caps.length capTarget capMinimum)
  {geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached}
  {parameters : Path.Dyadic.RadialTriangles.Parameters capRequest.depth}

include faces whole wholePerimeters

/-- The paid annular-complement comparison and scheduled physical cap bound
control the same remaining centered boundary, including its cached endpoints. -/
theorem remaining_cap_energy_upper
    {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision allocated.family.single.grid lifted}
      {remainingFloor : Nat}
    (remaining : Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest
      (grid := allocated.family.single.grid) excision traces remainingFloor)
    (remainingLater : remaining.index ≤ stage)
    (entries : schedule.physical.Readings cache) (physicalFaces : schedule.physical.FacePerimeterBank cache)
    (attachments : Data.Vector.DependentVector (fun first =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
      (schedule.basis.preparations.get first)))
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank allocated.family.single.grid.faces)
    (evaluated : schedule.basis.Evaluations polynomials capRequest.depth)
    (later : schedule.index ≤ stage) (spatial : schedule.basis.depth ≤ capRequest.depth)
    (caps : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisCap geometry parameters
      polynomials)
    (capSample : (capRequest.certify caps).Evaluation coefficients)
    (physicalAllowance : Fraction.Rational) (physicalNonnegative : 0 ≤ physicalAllowance)
    (physicalPaid : (genus : Fraction.Rational) ^ 2 * physicalTarget ≤ 16 * physicalAllowance ^ 2)
    {remainingAllowance : Fraction.Rational} (remainingPositive : 0 < remainingAllowance)
    (remainingPaid : target ≤
      BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation)
      remainingAllowance) :

      (CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
      excision samples neighbors +
      PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy
        attachments polynomials coefficients).im / 4 ≤
        (capTarget + physicalAllowance + remainingAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq
          coefficients := by
  let joining :=
    PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy
    attachments polynomials coefficients
  have boundary :=
    ExteriorComparison.SynchronizedSurfaceRequests.RemainingBandRequest.exterior_energy_lower
    allocated remaining remainingLater samples faces neighbors remainingPositive remainingPaid joining
  have capBound := RootContinuation.NewtonScheduledExteriorCapEnergy.exterior_cap_energy_upper shared schedule samples
    faces whole wholePerimeters attached capRequest
    entries physicalFaces attachments neighbors evaluated later spatial caps capSample physicalAllowance
      physicalNonnegative physicalPaid
  rw [Gaussian.Basic.add_comm joining
    (CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
    excision samples neighbors),
    Gaussian.Basic.add_comm joining
      (RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentBoundary
      samples neighbors .exterior -
      RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentSum
        neighbors .exterior
        (PerimeterSamples.cachedEndpointSideSum
        cache coefficients))] at boundary
  have combined := boundary.trans capBound
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct combined (remainingAllowance *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
  have cancel :
    (CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
    excision samples neighbors + joining).im / 4 =

        (CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
        excision samples neighbors + joining).im / 4 -
        remainingAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients + remainingAllowance
          * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by ring1
  exact cancel.trans_le (shifted.trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CapEnergy
