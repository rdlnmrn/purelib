module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
public import Purelib.Riemann.RootContinuation.NewtonPhysicalPerimeterEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.Dyadic.RadialTriangles
public import Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule
import Purelib.Riemann.RootContinuation.NewtonSharedPhysicalPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAccuracy
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshReindex
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! Apply the regular-cap energy comparison at the common depth and numerical
threshold retained by the physical/observation schedule. -/
namespace Purelib.Riemann.RootContinuation.NewtonScheduledExteriorCapEnergy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (surfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Branches.NewtonSharedExteriorCuts (SharedExteriorCuts)
open Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule (PhysicalSurfaceSchedule)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples
  SheetAssemblies SheetPerimeters SheetFaces)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples
  (componentSum componentBoundary)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples
  (cachedEndpointSideSum)
open Purelib.Riemann.RootContinuation.NewtonPhysicalPerimeterEnergy.SynchronizedSurfaceRequests.PerimeterSamples
  (WholeFaceEnergyAssembly)
open Purelib.Riemann.RootContinuation.NewtonSharedPhysicalPerimeters.SynchronizedSurfaceRequests.PerimeterSamples
  (newton_exterior_cap_energy_upper)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.Readings
  (capJoiningEnergy)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate (RegularBasisCap)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Data.Rat.Fraction.Rational} {grid : NewtonGrid preparation
    target radius}
  {lifted : LiftedPuncturedGrid grid.punctured} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {stage : Nat} {cache : Numerics domains stage}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {fixed : (sheet : Fin 2) → Preflights domains sheet} {surfaceTarget physicalTarget : Data.Rat.Fraction.Rational}
  {minimum floor coarseDepth : Nat}
  {preparations : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular
    domains}
  {observations : ProtectedObservations original} {partitions : SurfacePartitions observations grid}
  (shared : SharedExteriorCuts partitions preparations)
  {initialWhole : Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
    coarseDepth) fixed surfaceTarget}
  {surfaceFixed : (sheet : Fin 2) → Preflights domains sheet}
  {pieceDepth : Nat} {error : Data.Rat.Fraction.Rational}
  {initialPieces : SynchronizedSurfaceRequests
    (fun sheet => Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
      shared.surface sheet pieceDepth) surfaceFixed error}
  (schedule : PhysicalSurfaceSchedule preparations initialWhole initialPieces physicalTarget minimum floor)
  {traces : PerimeterTraces schedule.surface} {coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  (samples : PerimeterSamples
      schedule.surface traces cache coefficients)
  {assemblies : SheetAssemblies schedule.surface (cache := cache) (coefficients := coefficients)}
  {perimeters : SheetPerimeters schedule.surface assemblies} (faces : SheetFaces schedule.surface perimeters)
  (whole : (position : Fin grid.faces.regulars.length) → (sheet : Fin 2) →
    WholeFaceEnergyAssembly schedule.physical cache coefficients position sheet)
  (wholePerimeters : (position : Fin grid.faces.regulars.length) → (sheet : Fin 2) → (whole position sheet).Perimeter)
  {differential : Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential}
  (attached : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
  {box : Purelib.Geometry.Rational.Box} {polynomials :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box}
  {bounds : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials} {capTarget
    : Data.Rat.Fraction.Rational} {capMinimum : Nat}
  (capRequest : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds
    attached.caps.length capTarget capMinimum)
  {geometry :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached}
  {parameters : Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters capRequest.depth}

include faces whole wholePerimeters

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
/-- Read the exterior-cap bound from a synchronized physical schedule.

Uses the schedule's stored preparation equality and common depth to retain the actual whole perimeters, physical
readings and cap certificate at every sufficiently late stage. -/
theorem exterior_cap_energy_upper
    (entries : schedule.physical.Readings cache) (physicalFaces : schedule.physical.FacePerimeterBank cache)
    (attachments : Vector.DependentVector (fun first =>
      Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (schedule.basis.preparations.get first)))
    (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (evaluated : schedule.basis.Evaluations polynomials capRequest.depth)
    (later : schedule.index ≤ stage) (spatial : schedule.basis.depth ≤ capRequest.depth)
    (caps : Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisCap geometry parameters polynomials)
    (capSample : (capRequest.certify caps).Evaluation coefficients)
    (allowance : Fraction.Rational) (nonnegative : 0 ≤ allowance)
    (paid : (genus : Fraction.Rational) ^ 2 * physicalTarget ≤ 16 * allowance ^ 2) :
    (componentBoundary samples neighbors
        .exterior -
      componentSum neighbors .exterior (cachedEndpointSideSum cache coefficients) +
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy attachments
        polynomials coefficients).im / 4 ≤
        (capTarget + allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  cases schedule with
  | mk basis preparationsEq physical surface sameDepth initialPiecesLe index indexEq physicalLe surfaceLe =>
      cases preparationsEq
      exact newton_exterior_cap_energy_upper shared
          samples faces whole
          wholePerimeters attached capRequest
        sameDepth entries physicalFaces attachments neighbors evaluated (physicalLe.trans later) spatial
        caps capSample allowance nonnegative paid

end Purelib.Riemann.RootContinuation.NewtonScheduledExteriorCapEnergy
