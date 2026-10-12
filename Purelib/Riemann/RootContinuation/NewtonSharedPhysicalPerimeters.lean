module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPhysicalEndpointEnergy
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
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas
import Purelib.Riemann.Meshes.RectangularObservationMesh

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterTransport
import Purelib.Riemann.RootContinuation.NewtonSharedRequestedPerimeters
public import Purelib.Riemann.RootContinuation.NewtonPhysicalPerimeterEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshEnergy
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAccuracy
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Rat.Fraction.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshReindex
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

public section

/-! The Newton two-sheet boundary and the physical cap comparison read the
same cached perimeter at a common spatial depth and numerical stage. -/
namespace Purelib.Riemann.RootContinuation.NewtonSharedPhysicalPerimeters

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (surfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Branches.NewtonSharedExteriorCuts (SharedExteriorCuts)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues (PhysicalComponent)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples
  SheetAssemblies SheetPerimeters SheetFaces)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples (sideSum)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples
  (componentSum componentBoundary)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples
  (cachedEndpointSideSum)
open Purelib.Riemann.RootContinuation.NewtonPhysicalPerimeterEnergy.SynchronizedSurfaceRequests.PerimeterSamples
  (WholeFaceEnergyAssembly wholePerimeterSide physicalPerimeterEnergy_eq_combined)
open Purelib.Riemann.RootContinuation.NewtonPhysicalEndpointEnergy.SynchronizedSurfaceRequests.PerimeterSamples
  (exterior_cap_energy_upper)
open Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterTransport
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate (RegularBasisCap)
open Purelib.Riemann.Normalization
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas (Entry)

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
  {basis : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest regular domains
    physicalTarget minimum floor}
  {observations : ProtectedObservations original} {partitions : SurfacePartitions observations grid}
  (shared : SharedExteriorCuts partitions basis.preparations)
  {initial : Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
    coarseDepth) fixed surfaceTarget}
  {physical : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest basis initial}
  {surfaceFixed : (sheet : Fin 2) → Preflights domains sheet}
  {pieceDepth : Nat} {error : Data.Rat.Fraction.Rational}
  {requests : SynchronizedSurfaceRequests
    (fun sheet => Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
      shared.surface sheet pieceDepth) surfaceFixed error}

namespace SynchronizedSurfaceRequests.PerimeterSamples

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Riemann.Meshes in
/-- The physical mesh is the shared whole mesh at the retained request depth.

Uses the supplied common-depth equation and exact dependent-vector mesh readbacks without changing domain or partition
owners. -/
private theorem physical_mesh_eq_build (sameDepth : physical.surface.depth = requests.depth)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) :
    ((physical.surface.entries.get sheet).meshes.entries.get position) =
      ((Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
        (requests.entries.get sheet).depth).entries.get position) := by
  rw [Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request.mesh_eq,
    Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest.mesh_eq, physical.surface.depth_eq,
    sameDepth, ← requests.depth_eq sheet]
  simp only [Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build, Vector.DependentVector.ofFn_get, -eq_self,
    -iff_self]
  apply Eq.trans (congrArg
    (fun mesh : RectangularObservationMesh.ObservationMesh ((domains.get position).domain sheet).cuts
      (grid.faces.regulars[position.val]'position.isLt).cell.box => mesh.atDepth (requests.entries.get sheet).depth)
    (Vector.DependentVector.ofFn_get _ position))
  rfl

variable {traces : PerimeterTraces requests} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  genus}
  (samples : PerimeterSamples requests traces cache coefficients)
  {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
  {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters)
  (whole : (position : Fin grid.faces.regulars.length) → (sheet : Fin 2) →
    WholeFaceEnergyAssembly physical cache coefficients position sheet)
  (wholePerimeters : (position : Fin grid.faces.regulars.length) → (sheet : Fin 2) → (whole position sheet).Perimeter)

include faces whole wholePerimeters

open Purelib.Algebra in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.RootContinuation in
/-- Shared side samples equal the retained physical whole-perimeter sum.

At equal physical and surface depth, transports each sheet perimeter along its exact mesh identity and reads the
selected side area. -/
theorem sideSum_eq_physical (sameDepth : physical.surface.depth = requests.depth)
    (side : GridSide) (position : Fin grid.faces.regulars.length) :
    samples.sideSum side position = FiniteSum.Fin.sumFin (fun sheet => wholePerimeterSide (wholePerimeters position
      sheet) side) := by
  unfold sideSum
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  let equal := physical_mesh_eq_build shared sameDepth position sheet
  let retained := ClippedPerimeterTransport.cast equal (wholePerimeters position sheet)
  have readback := ClippedPerimeterTransport.cast_entries equal (wholePerimeters position sheet)
  cases side with
  | bottom =>
    exact (NewtonSharedRequestedPerimeters.bottom_sample_eq_whole (shared := shared) ((samples.get sheet).get position)
      ((faces.get sheet).get position) retained).trans (congrArg StitchedSideAreas.Entry.area readback.1)
  | right =>
    exact (NewtonSharedRequestedPerimeters.right_sample_eq_whole (shared := shared) ((samples.get sheet).get position)
      ((faces.get sheet).get position) retained).trans (congrArg StitchedSideAreas.Entry.area readback.2.1)
  | top =>
    exact (NewtonSharedRequestedPerimeters.top_sample_eq_whole (shared := shared) ((samples.get sheet).get position)
      ((faces.get sheet).get position) retained).trans (congrArg StitchedSideAreas.Entry.area readback.2.2.1)
  | left =>
    exact (NewtonSharedRequestedPerimeters.left_sample_eq_whole (shared := shared) ((samples.get sheet).get position)
      ((faces.get sheet).get position) retained).trans (congrArg StitchedSideAreas.Entry.area readback.2.2.2)

attribute [local congr] Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
/-- Read any physical component boundary from the retained whole perimeters.

Preserves the original neighbor bank and selected exterior or hole component under the exact shared-depth side
identities. -/
theorem componentBoundary_eq_physical (sameDepth : physical.surface.depth = requests.depth)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) (component :
      Meshes.PuncturedGrid.PhysicalComponentValues.PhysicalComponent grid.faces) :
    componentBoundary samples neighbors component =
      componentSum neighbors component (fun side position =>
        FiniteSum.Fin.sumFin (fun sheet => wholePerimeterSide (wholePerimeters position sheet) side)) := by
  simp only [componentBoundary, componentSum, sideSum_eq_physical shared samples faces whole wholePerimeters sameDepth,
    -eq_self, -iff_self]
  rfl

/-- Physical perimeter energy is the shared exterior component boundary.

Combines the coefficient perimeter identity with the exact whole-to-shared readback at equal retained depths. -/
theorem physicalEnergy_eq_componentBoundary (sameDepth : physical.surface.depth = requests.depth)
    (physicalFaces : physical.FacePerimeterBank cache) (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    physicalFaces.componentEnergy neighbors coefficients = componentBoundary samples neighbors .exterior :=
  (physicalPerimeterEnergy_eq_combined physicalFaces coefficients whole wholePerimeters neighbors).trans
    (componentBoundary_eq_physical shared samples faces whole wholePerimeters sameDepth neighbors .exterior).symm

variable {differential : Curves.Hyperelliptic.Differentials.Basic.Differential genus}
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

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
/-- Bound the shared Newton exterior boundary with endpoint and cap corrections.

Uses the actual physical readings and cap evaluation, retaining the common-depth certificate, spatial and numerical
bounds, and explicit allowance payment. -/
theorem newton_exterior_cap_energy_upper
    (sameDepth : physical.surface.depth = requests.depth)
    (entries : physical.Readings cache) (physicalFaces : physical.FacePerimeterBank cache)
    (attachments : Vector.DependentVector (fun first =>
      Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (basis.preparations.get first)))
    (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (evaluated : basis.Evaluations polynomials capRequest.depth)
    (later : physical.index ≤ stage) (spatial : basis.depth ≤ capRequest.depth)
    (caps : Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisCap geometry parameters polynomials)
    (capSample : (capRequest.certify caps).Evaluation coefficients)
    (allowance : Fraction.Rational) (nonnegative : 0 ≤ allowance)
    (paid : (genus : Fraction.Rational) ^ 2 * physicalTarget ≤ 16 * allowance ^ 2) :
    (componentBoundary samples neighbors .exterior -
      componentSum neighbors .exterior (cachedEndpointSideSum cache coefficients) +
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy attachments
        polynomials coefficients).im / 4 ≤
        (capTarget + allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bound := exterior_cap_energy_upper shared.source attached capRequest entries physicalFaces attachments neighbors
    evaluated later spatial caps coefficients capSample allowance nonnegative paid
  rw [physicalEnergy_eq_componentBoundary shared samples faces whole wholePerimeters sameDepth physicalFaces neighbors]
    at bound
  exact bound

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Riemann.RootContinuation.NewtonSharedPhysicalPerimeters
