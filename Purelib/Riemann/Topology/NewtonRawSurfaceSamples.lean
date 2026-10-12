module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Riemann.RootContinuation.NewtonRawBoundarySchedule
public import Purelib.Riemann.RootContinuation.NewtonPhysicalPerimeterEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshReindex
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonRawSurfaceSchedule
import Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.RootContinuation.NewtonRawJoiningSchedule
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Topology.NewtonRawSewingSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshSamples
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Riemann.Meshes.RectangularObservationMesh

public section

/-! Retain the complete surface readbacks on the shared numerical bank. The
coefficient-dependent faces and perimeters reuse the same request owners. -/
namespace Purelib.Riemann.Topology.NewtonRawSurfaceSamples

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.Topology.NewtonRawSurfaceSchedule (SurfaceSchedule)
open Purelib.Riemann.Topology.NewtonRawSewingSchedule (SewingSchedule)
open Purelib.Riemann.RootContinuation.NewtonRawJoiningSchedule (RawJoiningSchedule)
open Purelib.Riemann.RootContinuation.NewtonRawBoundarySchedule (RawBoundarySchedule)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (PhysicalMeshRequest)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterSamples SheetAssemblies
  SheetPerimeters SheetFaces)
open Purelib.Riemann.RootContinuation.NewtonPhysicalPerimeterEnergy.SynchronizedSurfaceRequests.PerimeterSamples
  (WholeFaceEnergyAssembly)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (assemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (perimeters faceAssemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {radius : Rational}
  {observations : ProtectedObservations base.bank.toBranchCellBank}
  {gridData : RawEnergyGrid observations preparation radius}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {physicalMinimum physicalFloor
    sewingFloor : Nat}
  (surfaceData : SurfaceSchedule gridData regular physicalMinimum physicalFloor)
  (sewingData : SewingSchedule gridData sewingFloor)

variable {joiningFloor : Nat}
  (joiningData : RawJoiningSchedule (paired := paired) surfaceData sewingData joiningFloor)

variable {boundaryFloor stage : Nat}
  (boundaryData : RawBoundarySchedule surfaceData sewingData joiningData boundaryFloor)
  (cache : Numerics gridData.domains stage)

open Purelib.Data in
set_option genInjectivity false in
/-- Numerical surface and physical readings on one retained cache.

Keeps both sheet requests' readings, the actual physical readings and their basis-pair face-perimeter bank. -/
structure RawSurfaceReadings where
  /-- Dependent readings of the two retained surface requests. -/ surface : Vector.DependentVector (fun sheet : Fin 2 =>
    (surfaceData.schedule.surface.entries.get sheet).Readings cache)
  /-- Actual physical request readings from the common cache. -/ physical : surfaceData.schedule.physical.Readings cache
  /-- Basis-pair face-perimeter bank for the physical request. -/ physicalFaces :
    surfaceData.schedule.physical.FacePerimeterBank cache

constructive_injectivity RawSurfaceReadings

namespace RawSurfaceReadings

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Acquire both sheet readings and physical perimeter data from one cache.

Builds each retained surface request reading and the actual physical request bank without replacing their owners. -/
@[expose] def build : RawSurfaceReadings surfaceData cache :=
  ⟨Vector.DependentVector.ofFn (fun sheet => (surfaceData.schedule.surface.entries.get sheet).readings cache),
    surfaceData.schedule.physical.readings cache,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.FacePerimeterBank.build
      surfaceData.schedule.physical cache⟩

end RawSurfaceReadings

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)

variable (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

section
open Purelib.Data
/-- Dependent whole-face energy assemblies indexed by sheet and regular face.

Every assembly uses the actual physical request, numerical cache and coefficient vector. -/
@[expose] def WholeEnergyAssemblies := Vector.DependentVector (fun sheet : Fin 2 => Vector.DependentVector
  (fun position : Fin gridData.allocated.family.single.grid.faces.regulars.length =>
    WholeFaceEnergyAssembly surfaceData.schedule.physical cache coefficients position sheet))

/-- Dependent perimeters of the retained whole energy assemblies.

Preserves the exact sheet and face indices and each original assembly owner. -/
@[expose] def WholeEnergyPerimeters (whole : WholeEnergyAssemblies surfaceData cache coefficients) :=
  Vector.DependentVector (fun sheet : Fin 2 => Vector.DependentVector
    (fun position : Fin gridData.allocated.family.single.grid.faces.regulars.length => ((whole.get sheet).get
      position).Perimeter))

end

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
  Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly in
set_option genInjectivity false in
/-- Retained piece and whole energy samples for a raw boundary schedule.

Keeps sheet assemblies, perimeters and faces, the actual remaining perimeter samples, and the whole-face
assembly/perimeter banks on the same cache. -/
structure RawSurfaceEnergy where
  /-- Sheet-indexed assemblies of the retained surface requests. -/ assemblies : SheetAssemblies
    surfaceData.schedule.surface (cache := cache) (coefficients := coefficients)
  /-- Actual perimeters of those retained assemblies. -/ perimeters : SheetPerimeters surfaceData.schedule.surface
    assemblies
  /-- Face assemblies retaining the exact perimeter bank. -/ faces : SheetFaces surfaceData.schedule.surface perimeters
  /-- Perimeter samples on the raw boundary schedule's retained traces. -/ remaining : PerimeterSamples
    surfaceData.schedule.surface boundaryData.traces cache coefficients
  /-- Dependent whole-face energy assemblies. -/ whole : WholeEnergyAssemblies surfaceData cache coefficients
  /-- Perimeters belonging to the exact retained whole assemblies. -/ wholePerimeters : WholeEnergyPerimeters
    surfaceData cache coefficients whole

constructive_injectivity RawSurfaceEnergy

namespace RawSurfaceEnergy

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Construct all raw surface energy assemblies and perimeter samples.

Reuses the retained surface and physical meshes and coefficient-combined seam values, preserving each dependent
assembly-to-perimeter-to-face construction. -/
@[expose] def build : RawSurfaceEnergy surfaceData sewingData joiningData boundaryData cache coefficients :=
  let assemblies : SheetAssemblies surfaceData.schedule.surface (cache := cache) (coefficients := coefficients) :=
    Vector.DependentVector.ofFn fun sheet => Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest.assemblies
      (surfaceData.schedule.surface.entries.get sheet) cache coefficients
  let perimeters : SheetPerimeters surfaceData.schedule.surface assemblies :=
    Vector.DependentVector.ofFn fun sheet => Meshes.Newton.Surface.FaceAssembly.perimeters (assemblies.get sheet)
  let faces : SheetFaces surfaceData.schedule.surface perimeters :=
    Vector.DependentVector.ofFn fun sheet => Meshes.Newton.Surface.FaceAssembly.faceAssemblies (perimeters.get sheet)
  let remaining := PerimeterSamples.build surfaceData.schedule.surface boundaryData.traces cache coefficients
  let whole : WholeEnergyAssemblies surfaceData cache coefficients := Vector.DependentVector.ofFn fun sheet =>
    Vector.DependentVector.ofFn fun position => ClippedAssembly.build
      ((surfaceData.schedule.physical.surface.entries.get sheet).meshes.entries.get position)
      (Meshes.Newton.Surface.SeamAreas.seamValues (sheet := sheet) cache coefficients position)
  let wholePerimeters : WholeEnergyPerimeters surfaceData cache coefficients whole := Vector.DependentVector.ofFn fun
    sheet =>
    Vector.DependentVector.ofFn fun position => ClippedAssembly.Perimeter.build ((whole.get sheet).get position)
  ⟨assemblies, perimeters, faces, remaining, whole, wholePerimeters⟩

end RawSurfaceEnergy
end Purelib.Riemann.Topology.NewtonRawSurfaceSamples
