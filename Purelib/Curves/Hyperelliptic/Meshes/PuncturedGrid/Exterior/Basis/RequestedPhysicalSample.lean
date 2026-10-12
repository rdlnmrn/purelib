module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOwnerSchedule
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
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Riemann.Readings.RectangularObservationAssembly
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterTriangles
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Budget.RequestedLengthBudget
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes

public section

/-! Retain the physical occurrence and its complete weighted perimeter together. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample

open Purelib.Data.Rat

open Purelib.Curves
open Purelib.Integration
open Purelib
open Purelib.Riemann

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets.SharedHorizontalRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns

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

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace RequestedOccurrenceRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns (mesh
  buildScheduled)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length)
  {whole :
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
  {stage : Nat} (traces : Paths.RectangularPerimeterTraces.PerimeterTraces (mesh outer selected request))
  (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
  (banks : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples.SharedPerimeter.Banks (occurrence :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) traces
    cache)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  (schedule :
    ParentRunSchedule
    retained inputs outer
    (SharedOccurrenceRuns.sideCapacity outer
      (mesh := mesh outer selected request)) requested minimum)
  {vertices : Fin
    (SharedOccurrenceRuns.sideCapacity outer
    (mesh := mesh outer selected request)) → Nat}
  (owners :
    SharedOwnerSchedule.CommonBasisPreparation.ParentRunSchedule.SharedOwners
    schedule (Paths.RectangularDyadicPairedTrace.dyadicCount (mesh outer selected request).depth) vertices)

/-- Certify that the stored weighted perimeter samples are exactly those computed from the retained banks. -/
@[expose] def SampleReadback (samples :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples.SharedPerimeter.Samples traces cache coefficients)
  : Prop :=
  samples = banks.sample traces cache coefficients

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns in
/-- The physical occurrence bank indexed by the exact retained weighted sample area and shared-owner budgets. -/
@[expose] def SampleBank (samples :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples.SharedPerimeter.Samples traces cache coefficients)
  :=
  PhysicalRunBank retained inputs outer coefficients
    stage (mesh outer selected request).depth
    (SharedOccurrenceRuns.sideCapacity outer
      (mesh := mesh outer selected request))
    ((samples.get traces cache coefficients
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.side).centeredArea)
    (max 1 1) (max owners.piece.budget.tolerance owners.junction.budget.tolerance)

set_option genInjectivity false in
/-- Both the local Newton triangle identity and the source-oriented run identity
consume these very weighted samples. All four endpoint chords remain cached. -/
structure PhysicalSample where
  /-- The cached weighted samples on all four original perimeter sides. -/ samples :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples.SharedPerimeter.Samples traces cache coefficients
  /-- The stored samples are exactly the weighted samples of the retained perimeter banks. -/ samples_eq :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample.RequestedOccurrenceRuns.SampleReadback
    outer selected request traces cache banks coefficients samples
  /-- The physical occurrence bank indexed by these exact samples, geometry and paid owner budgets. -/ bank :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample.RequestedOccurrenceRuns.SampleBank
    retained inputs outer selected request traces cache coefficients schedule owners samples

constructive_injectivity PhysicalSample

/-- Acquire the retained weighted perimeter samples and their scheduled physical occurrence bank.

The membership witness selects the original occurrence, and the paid face stage authorizes both piece and junction
owners on the same numerical cache. -/
@[expose] def acquireSample (member : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer ∈ whole.occurrences)
    (facePaid : owners.faceIndex ≤ stage) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample.RequestedOccurrenceRuns.PhysicalSample
      retained inputs outer selected request traces cache banks coefficients schedule owners :=
  let samples := banks.sample traces cache coefficients
  ⟨samples, rfl,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.buildScheduled
    retained inputs outer selected member request traces cache banks coefficients
    schedule owners facePaid⟩

namespace PhysicalSample
variable {retained inputs outer selected request traces cache banks coefficients schedule owners}
  (sample :
    RequestedOccurrenceRuns.PhysicalSample
    retained inputs outer selected request traces cache banks coefficients schedule owners)

/-- Package the retained physical bank with its exact geometry, area and scalar budget indices. -/
@[expose] def entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries.PhysicalRunEntry retained
  inputs outer coefficients stage :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries.PhysicalRunEntry.ofBank sample.bank

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns
/-- The packaged bank depth equals the actual requested occurrence mesh depth. -/
theorem entry_depth :
  (entry
  sample).depth = (mesh outer selected request).depth := rfl

/-- The packaged capacity equals the original requested side capacity. -/
theorem entry_capacity :
  (entry
  sample).capacity =
  SharedOccurrenceRuns.sideCapacity outer
    (mesh := mesh outer selected request) := rfl

end

/-- The packaged physical-bank allowance is bounded by one. -/
theorem entry_allowance :
  (entry
  sample).allowance ≤ 1 := by
  change max (1 : Normalization.InverseRootPolynomial.Coordinate) 1 ≤ 1
  exact Fraction.Order.Basic.max_le le_rfl le_rfl

/-- The packaged physical-bank tolerance is paid by each original parent request. -/
theorem entry_tolerance (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length) :

      (entry
      sample).tolerance ≤ (schedule.requests.get position).blocks.budget.tolerance :=
  Fraction.Order.Basic.max_le
    (SharedOwnerSchedule.CommonBasisPreparation.ParentRunSchedule.SharedOwners.piece_tolerance_le
    owners position)
    (SharedOwnerSchedule.CommonBasisPreparation.ParentRunSchedule.SharedOwners.junction_tolerance_le
    owners position)

/-- The source-oriented physical run area is the retained side area with its original traversal sign. -/
theorem area_readback : Path.PairedIncrementArea.area (List.ofFn sample.bank.physical).flatten =
    if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceForward then
      (entry
      sample).sideArea else
      -(entry
      sample).sideArea :=
  PhysicalRunBank.area_readback sample.bank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns in
/-- No endpoint, seam, or corner term is dropped when using the same samples. -/
theorem triangle_boundary
    (assembly : Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly (mesh outer selected request)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter.gridValues (occurrence :=
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) cache
        coefficients))
    (perimeter : assembly.Perimeter) :
    Readings.RectangularClippedLocalBoundary.localWedges
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterTriangles.SharedPerimeter.primitiveValues (occurrence
      := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) cache
      coefficients)
      (mesh outer selected request).triangles =
      ((sample.samples.bottom.centeredArea + sample.samples.bottom.endpoint) +
       (sample.samples.right.centeredArea + sample.samples.right.endpoint) -
       (sample.samples.top.centeredArea + sample.samples.top.endpoint) -
       (sample.samples.left.centeredArea + sample.samples.left.endpoint)) + assembly.seams + assembly.cornerTotal :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterTriangles.SharedPerimeter.Samples.triangle_boundary cache
    coefficients traces sample.samples assembly perimeter

end PhysicalSample
end RequestedOccurrenceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample
