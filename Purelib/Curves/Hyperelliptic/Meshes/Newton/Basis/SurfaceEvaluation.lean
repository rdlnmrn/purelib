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

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Normalization.InverseRootPolynomial.Coordinate}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured} {differential : Hyperelliptic.Differentials.Basic.Differential
    genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace RequestedSurfaceRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes

variable {whole :
  PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {previous :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  {selected : PuncturedGrid.Exterior.SourceCuts whole previous}
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget}
  {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared} {index :
    Nat} {inputs : retained.Inputs index}
  {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  (schedules : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    selected request retained inputs requested minimum)

variable {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {partitions :
  Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCoarse : (sheet : Fin 2) → Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {surfaceFixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet}
    {surfaceTarget : Normalization.InverseRootPolynomial.Coordinate}
  (initialSurface : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests surfaceCoarse surfaceFixed
    surfaceTarget)

namespace SurfaceAcquisition
variable {schedules initialSurface} (acquired :
  SurfaceAcquisition schedules initialSurface)
  (vertices : (outer : Fin prepared.occurrences.length) → Fin
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities selected
    acquired.spatial.refined outer) → Nat)

variable (numerical :
  NumericalAcquisition
  acquired vertices)
  {stage : Nat} (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- Cache complete whole-face assemblies on the same physical mesh used by acquisition. -/
@[expose] def WholeAssemblies := Data.Vector.DependentVector (fun sheet : Fin 2 => Data.Vector.DependentVector
  (fun position : Fin grid.faces.regulars.length =>
    Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly
    ((acquired.spatial.refined.entries.get sheet).meshes.entries.get position)
    (Hyperelliptic.Meshes.Newton.Surface.SeamAreas.seamValues (sheet := sheet) cache coefficients position)))

/-- The dependent family of perimeter certificates for the exact cached whole-face assemblies. -/
@[expose] def WholePerimeters (whole :
  Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation.RequestedSurfaceRuns.SurfaceAcquisition.WholeAssemblies acquired
  cache coefficients) :=
  Data.Vector.DependentVector (fun sheet : Fin 2 => Data.Vector.DependentVector
    (fun position : Fin grid.faces.regulars.length => ((whole.get sheet).get position).Perimeter))

set_option genInjectivity false in
/-- These cached readings feed both the physical component proof and the observed sewn surface. -/
structure Evaluation where
  /-- The retained complete physical occurrence perimeter traces. -/ traces :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Traces (prepared
    := prepared) selected acquired.spatial.refined
  /-- The physical perimeter banks on the exact retained traces and numerical cache. -/ perimeters :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Perimeters
    selected acquired.spatial.refined traces cache
  /-- The acquired occurrence samples indexed by the retained schedules and physical owner banks. -/ physical :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.PhysicalSamples
    selected acquired.spatial.refined traces cache coefficients
    acquired.spatial.requests numerical.owners perimeters
  /-- The complete perimeter traces of the synchronized observation surface. -/ observationTraces :
    Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces acquired.surface
  /-- The weighted observation samples on those exact traces and common numerical cache. -/ observed :
    Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples acquired.surface observationTraces
    cache coefficients
  /-- The cached clipped assemblies of the original observation sheets. -/ assemblies :
    Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetAssemblies acquired.surface (cache := cache)
    (coefficients := coefficients)
  /-- The perimeter certificates for the retained observation assemblies. -/ observationPerimeters :
    Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetPerimeters acquired.surface assemblies
  /-- The original face-assembly witnesses for those exact observation perimeters. -/ faces :
    Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetFaces acquired.surface observationPerimeters
  /-- The cached whole-face assemblies on the actual acquired physical mesh. -/ whole :
    Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation.RequestedSurfaceRuns.SurfaceAcquisition.WholeAssemblies acquired
    cache coefficients
  /-- The perimeter certificates for those exact cached whole-face assemblies. -/ wholePerimeters :
    Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation.RequestedSurfaceRuns.SurfaceAcquisition.WholePerimeters acquired
    cache coefficients whole

constructive_injectivity Evaluation

namespace Evaluation

/-- Acquire once at the common certified index; every comparison consumes the retained banks. -/
@[expose] def build (member : ∀ outer, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer ∈ whole.occurrences)
    (later : numerical.index ≤ stage) :
      Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation.RequestedSurfaceRuns.SurfaceAcquisition.Evaluation acquired
      vertices numerical cache coefficients := by
  let traces :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.prepareTraces
    (prepared := prepared) selected acquired.spatial.refined
  let perimeters :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.preparePerimeters
    selected acquired.spatial.refined traces cache
  let physical :=
    PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
    selected acquired.spatial.refined traces cache coefficients
    acquired.spatial.requests numerical.owners perimeters member numerical.face (numerical.face_le.trans later)
  let observationTraces := Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces.build
    acquired.surface
  let observed := Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples.build
    acquired.surface observationTraces cache coefficients
  let assemblies : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetAssemblies acquired.surface
    (cache := cache) (coefficients := coefficients) :=
    Data.Vector.DependentVector.ofFn fun sheet =>
      Surface.ExteriorRequest.assemblies (acquired.surface.entries.get
      sheet) cache coefficients
  let observationPerimeters : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetPerimeters
    acquired.surface assemblies :=
    Data.Vector.DependentVector.ofFn fun sheet => Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.perimeters
      (assemblies.get sheet)
  let faces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetFaces acquired.surface
    observationPerimeters :=
    Data.Vector.DependentVector.ofFn fun sheet => Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.faceAssemblies
      (observationPerimeters.get sheet)
  let whole :
    Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation.RequestedSurfaceRuns.SurfaceAcquisition.WholeAssemblies acquired
    cache coefficients := Data.Vector.DependentVector.ofFn fun sheet =>
    Data.Vector.DependentVector.ofFn fun position =>
      Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly.build
      ((acquired.spatial.refined.entries.get sheet).meshes.entries.get position)
      (Hyperelliptic.Meshes.Newton.Surface.SeamAreas.seamValues (sheet := sheet) cache coefficients position)
  let wholePerimeters :
    Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation.RequestedSurfaceRuns.SurfaceAcquisition.WholePerimeters acquired
    cache coefficients whole := Data.Vector.DependentVector.ofFn fun sheet =>
    Data.Vector.DependentVector.ofFn fun position =>
      Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter.build ((whole.get sheet).get
      position)
  exact ⟨traces, perimeters, physical, observationTraces, observed, assemblies, observationPerimeters, faces, whole,
    wholePerimeters⟩

end Evaluation
end SurfaceAcquisition
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation
