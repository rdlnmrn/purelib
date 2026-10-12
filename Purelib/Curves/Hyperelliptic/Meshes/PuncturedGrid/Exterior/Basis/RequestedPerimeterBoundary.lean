module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.RectangularObservationAssembly
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentBoundary
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOwnerSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib.Riemann

public section

/-! Match the physical component to its Newton perimeters without dropping joining polygons. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets.SharedHorizontalRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace RequestedSurfaceRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter (gridValues
  sideArea original_area)

variable {whole :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {previous :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  (selected : SourceCuts whole previous)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget)

variable {selected request} {retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared} {index : Nat} {inputs :
  retained.Inputs index}
  {traces : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Traces
    (prepared := prepared) selected request} {faceIndex : Nat} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {requested :
    Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  {schedules : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    selected request retained inputs requested minimum}
  {vertices : (outer : Fin prepared.occurrences.length) → Fin
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities selected
    request outer) → Nat}
  {owners :
    RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.SharedOwnerBanks
    schedules
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.pieceCounts
    selected request) vertices}
  {perimeters :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Perimeters
    selected request traces cache}

namespace PhysicalSamples

variable (samples :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.PhysicalSamples
  selected request traces cache coefficients schedules owners perimeters)

/-- Sum the exact cached centered side areas with the original component traversal signs. -/
@[expose] def centeredSides : Gaussian := Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn fun outer =>
  if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward then (samples.entries.get outer).sideArea
  else -(samples.entries.get outer).sideArea)

/-- Sum the exact cached endpoint-chord corrections with the original component traversal signs. -/
@[expose] def endpointSides : Gaussian := Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn fun outer =>
  let endpoint := ((samples.get outer).samples.get (traces.get outer) cache coefficients
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.side).endpoint
  if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward then endpoint else -endpoint)

/-- Sum the uncentered original side areas with their retained traversal signs. -/
@[expose] def originalSides : Gaussian := Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn fun outer =>
  let area := ((samples.get outer).samples.get (traces.get outer) cache coefficients
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.side).originalArea
  if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward then area else -area)

/-- Compute the joining polygon area of the complete acquired occurrence endpoint totals. -/
@[expose] def joiningArea : Gaussian := Path.PairedIncrementArea.area (List.ofFn fun outer =>
  Path.PairedIncrementArea.total (List.ofFn
    (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
    samples.entries outer)).flatten)

/-- Centering removes precisely the retained signed endpoint chords. -/
theorem centered_add_endpoints :
  centeredSides
  samples +
  endpointSides
  samples =
  originalSides
  samples := by
  unfold
    centeredSides
    endpointSides
    originalSides
  have addReadback := Gaussian.Norm.Sum.Basic.gaussianSum_map_add
    (List.ofFn (fun outer : Fin prepared.occurrences.length => outer))
    (fun outer => if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceForward
      then (samples.entries.get outer).sideArea else -(samples.entries.get outer).sideArea)
    (fun outer =>
      let endpoint := ((samples.get outer).samples.get (traces.get outer) cache coefficients
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).sideOccurrence.side).endpoint
      if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceForward
        then endpoint else -endpoint)
  simp only [Data.List.OfFn.Basic.map_ofFn] at addReadback
  dsimp only [Function.comp_def] at addReadback
  refine addReadback.trans ?_
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.OfFn.Basic.ofFn_congr
  intro outer
  rw [samples.entry_sideArea outer]
  have equal := ((samples.get outer).samples.get (traces.get outer) cache coefficients
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.side).decomposition
  cases (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward <;> simp only [if_pos (Eq.refl true), if_neg (by decide : ¬ false = true), -eq_self, -iff_self]
  · rw [equal]
    ring1
  · exact equal.symm

/-- The physical boundary is an uncentered Newton perimeter with the explicit
centering subtraction and its own polygon of occurrence totals. -/
theorem boundary_eq : Path.PairedIncrementArea.area
    (List.ofFn (fun outer => (List.ofFn
      (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
      samples.entries outer)).flatten)).flatten =

      originalSides
      samples -
      endpointSides
      samples +
      joiningArea
      samples := by
  have physical :=
    PhysicalComponentBoundary.CommonBasisRequest.Sampled.physical_boundary
    samples.entries
  change _ =
    centeredSides
    samples +
    joiningArea
    samples at physical
  rw [←
    centered_add_endpoints
    samples]
  exact physical.trans (by ring1)

/-- The family of original clipped observation assemblies on the exact occurrence meshes and weighted numerical cache.
-/
@[expose] def Assemblies := (outer : Fin prepared.occurrences.length) →
  Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.mesh outer selected
    request)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter.gridValues (occurrence :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) cache
      coefficients)

/-- The perimeter certificate for each retained clipped observation assembly. -/
@[expose] def AssemblyPerimeters (assemblies :
  Assemblies
  (selected := selected) (request := request) (cache := cache)
    (coefficients := coefficients)) := (outer : Fin prepared.occurrences.length) → (assemblies outer).Perimeter

/-- Each signed original area is the corresponding complete Newton side,
including its internal owner junctions. -/
theorem originalSides_eq (assemblies :
  Assemblies
  (selected := selected) (request := request) (cache := cache)
    (coefficients := coefficients)) (perimeters :
      AssemblyPerimeters
      assemblies) :

      originalSides
      samples = Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn fun outer =>
      let area := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter.sideArea cache
        coefficients (perimeters outer)
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).sideOccurrence.side
      if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceForward then area else -area) := by
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.OfFn.Basic.ofFn_congr
  intro outer
  exact congrArg (fun area => if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).sourceForward then area else -area)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter.original_area (traces.get
      outer) cache coefficients
      ((samples.get outer).samples.get (traces.get outer) cache coefficients
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).sideOccurrence.side) (assemblies outer) (perimeters outer))

end PhysicalSamples
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary
