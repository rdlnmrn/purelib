module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
public import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.NumericalAcquisition
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib.Data.Vector (DependentVector)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

public section

/-! Cache the actual physical and observation readings on one synchronized acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation

open Purelib.Curves
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns
  (Traces Perimeters PhysicalSamples prepareTraces preparePerimeters acquirePhysicalSamples)

open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests
  (PerimeterTraces PerimeterSamples SheetAssemblies SheetPerimeters SheetFaces)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    InverseRootPolynomial.Coordinate}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured} {differential : Differentials.Basic.Differential
    genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace RequestedSurfaceRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes

variable {whole :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {previous :
  CommonCuts domains}
  {selected : SourceCuts whole previous}
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet} {meshTarget :
    InverseRootPolynomial.Coordinate}
  {request : PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget}
  {retained : Basis.Preparation.CommonBasisPreparation prepared} {index :
    Nat} {inputs : retained.Inputs index}
  {requested : InverseRootPolynomial.Coordinate} {minimum : Nat}
  (schedules : Schedules
    selected request retained inputs requested minimum)

variable {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {partitions :
  Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCoarse : (sheet : Fin 2) → Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {surfaceFixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet}
    {surfaceTarget : InverseRootPolynomial.Coordinate}
  (initialSurface : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests surfaceCoarse surfaceFixed
    surfaceTarget)

namespace SurfaceAcquisition
variable {schedules initialSurface} (acquired :
  SurfaceAcquisition schedules initialSurface)
  (vertices : (outer : Fin prepared.occurrences.length) → Fin
    (Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities selected
    acquired.spatial.refined outer) → Nat)

variable (numerical :
  NumericalAcquisition
  acquired vertices)
  {stage : Nat} (cache : Numerics domains stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- Cache complete whole-face assemblies on the same physical mesh used by acquisition. -/
@[expose] def WholeAssemblies := DependentVector (fun sheet : Fin 2 => DependentVector
  (fun position : Fin grid.faces.regulars.length =>
    Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly
    ((acquired.spatial.refined.entries.get sheet).meshes.entries.get position)
    (Surface.SeamAreas.seamValues (sheet := sheet) cache coefficients position)))

/-- The dependent family of perimeter certificates for the exact cached whole-face assemblies. -/
@[expose] def WholePerimeters (whole :
  WholeAssemblies acquired
  cache coefficients) :=
  DependentVector (fun sheet : Fin 2 => DependentVector
    (fun position : Fin grid.faces.regulars.length => ((whole.get sheet).get position).Perimeter))

set_option genInjectivity false in
/-- These cached readings feed both the physical component proof and the observed sewn surface. -/
structure Evaluation where
  /-- The retained complete physical occurrence perimeter traces. -/ traces :
    Traces (prepared
    := prepared) selected acquired.spatial.refined
  /-- The physical perimeter banks on the exact retained traces and numerical cache. -/ perimeters :
    Perimeters
    selected acquired.spatial.refined traces cache
  /-- The acquired occurrence samples indexed by the retained schedules and physical owner banks. -/ physical :
    PhysicalSamples
    selected acquired.spatial.refined traces cache coefficients
    acquired.spatial.requests numerical.owners perimeters
  /-- The complete perimeter traces of the synchronized observation surface. -/ observationTraces :
    PerimeterTraces acquired.surface
  /-- The weighted observation samples on those exact traces and common numerical cache. -/ observed :
    PerimeterSamples acquired.surface observationTraces
    cache coefficients
  /-- The cached clipped assemblies of the original observation sheets. -/ assemblies :
    SheetAssemblies acquired.surface (cache := cache)
    (coefficients := coefficients)
  /-- The perimeter certificates for the retained observation assemblies. -/ observationPerimeters :
    SheetPerimeters acquired.surface assemblies
  /-- The original face-assembly witnesses for those exact observation perimeters. -/ faces :
    SheetFaces acquired.surface observationPerimeters
  /-- The cached whole-face assemblies on the actual acquired physical mesh. -/ whole :
    WholeAssemblies acquired
    cache coefficients
  /-- The perimeter certificates for those exact cached whole-face assemblies. -/ wholePerimeters :
    WholePerimeters acquired
    cache coefficients whole

constructive_injectivity Evaluation

namespace Evaluation

/-- Acquire once at the common certified index; every comparison consumes the retained banks. -/
@[expose] def build (member : ∀ outer, Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer ∈ whole.occurrences)
    (later : numerical.index ≤ stage) :
      Evaluation acquired
      vertices numerical cache coefficients := by
  let traces :=
    Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.prepareTraces
    (prepared := prepared) selected acquired.spatial.refined
  let perimeters :=
    Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.preparePerimeters
    selected acquired.spatial.refined traces cache
  let physical :=
    Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
    selected acquired.spatial.refined traces cache coefficients
    acquired.spatial.requests numerical.owners perimeters member numerical.face (numerical.face_le.trans later)
  let observationTraces := PerimeterTraces.build
    acquired.surface
  let observed := PerimeterSamples.build
    acquired.surface observationTraces cache coefficients
  let assemblies : SheetAssemblies acquired.surface
    (cache := cache) (coefficients := coefficients) :=
    DependentVector.ofFn fun sheet =>
      Surface.ExteriorRequest.assemblies (acquired.surface.entries.get
      sheet) cache coefficients
  let observationPerimeters : SheetPerimeters
    acquired.surface assemblies :=
    DependentVector.ofFn fun sheet => Surface.FaceAssembly.perimeters
      (assemblies.get sheet)
  let faces : SheetFaces acquired.surface
    observationPerimeters :=
    DependentVector.ofFn fun sheet => Surface.FaceAssembly.faceAssemblies
      (observationPerimeters.get sheet)
  let whole :
    WholeAssemblies acquired
    cache coefficients := DependentVector.ofFn fun sheet =>
    DependentVector.ofFn fun position =>
      Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly.build
      ((acquired.spatial.refined.entries.get sheet).meshes.entries.get position)
      (Surface.SeamAreas.seamValues (sheet := sheet) cache coefficients position)
  let wholePerimeters :
    WholePerimeters acquired
    cache coefficients whole := DependentVector.ofFn fun sheet =>
    DependentVector.ofFn fun position =>
      Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter.build ((whole.get sheet).get
      position)
  exact ⟨traces, perimeters, physical, observationTraces, observed, assemblies, observationPerimeters, faces, whole,
    wholePerimeters⟩

end Evaluation
end SurfaceAcquisition
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation
