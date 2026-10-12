module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOwnerSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath

public section

/-! Acquire the complete component occurrence bank from shared physical samples. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent

open Purelib.Curves
open Purelib
open Purelib.Riemann

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

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace RequestedSurfaceRuns

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

/-- The dependent vector of complete perimeter traces on the actual requested occurrence meshes. -/
@[expose] def Traces := Data.Vector.DependentVector (fun outer : Fin prepared.occurrences.length =>
  Paths.RectangularPerimeterTraces.PerimeterTraces
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.mesh outer selected
    request))

/-- Construct every retained occurrence perimeter trace on its original requested mesh. -/
@[expose] def prepareTraces :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Traces (prepared :=
  prepared) selected request :=
  Data.Vector.DependentVector.ofFn fun outer => Paths.RectangularPerimeterTraces.PerimeterTraces.build
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.mesh outer selected
    request)

variable (traces :
  Traces
  (prepared := prepared) selected request) {stage : Nat} (cache :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)

/-- The dependent vector of perimeter sample banks on the retained traces and one numerical cache. -/
@[expose] def Perimeters := Data.Vector.DependentVector (fun outer : Fin prepared.occurrences.length =>
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples.SharedPerimeter.Banks (occurrence :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) (traces.get
    outer) cache)

/-- Build every occurrence perimeter bank from the exact retained trace and common numerical cache. -/
@[expose] def preparePerimeters :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Perimeters selected
  request traces cache :=
  Data.Vector.DependentVector.ofFn fun outer =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples.SharedPerimeter.Banks.build (traces.get outer)
    cache

/-- Read the dyadic physical-piece count from each actual occurrence mesh depth. -/
@[expose] def pieceCounts (outer : Fin prepared.occurrences.length) : Nat :=
  Paths.RectangularDyadicPairedTrace.dyadicCount
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.mesh outer selected
    request).depth

variable {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {index : Nat} {inputs : retained.Inputs index}
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {requested :
    Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  (schedules : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    selected request retained inputs requested minimum)
  {vertices : (outer : Fin prepared.occurrences.length) → Fin
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities selected
    request outer) → Nat}
  (owners :
    RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.SharedOwnerBanks
    schedules
    (pieceCounts
    selected request) vertices)
  (perimeters :
    Perimeters
    selected request traces cache)

/-- The dependent vector of acquired physical samples retaining the original occurrence schedules and shared-owner
banks. -/
@[expose] def PhysicalSamples := Data.Vector.DependentVector (fun outer : Fin prepared.occurrences.length =>
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample.RequestedOccurrenceRuns.PhysicalSample
    retained inputs outer selected request (traces.get outer) cache
    (perimeters.get outer) coefficients (schedules.get outer) (owners.get outer))

/-- The selected face stage includes the refined surface index and all physical
piece, junction and parent owners. Every occurrence uses the same numerical bank. -/
@[expose] def acquirePhysicalSamples (member : ∀ outer,
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer ∈
  whole.occurrences)
    (face :
      RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.FaceStage
      owners request.index) (later : face.stage ≤ stage) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.PhysicalSamples
      selected request traces cache coefficients schedules owners perimeters :=
  Data.Vector.DependentVector.ofFn fun outer =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample.RequestedOccurrenceRuns.acquireSample
    retained inputs outer selected request
    (traces.get outer) cache (perimeters.get outer) coefficients (schedules.get outer) (owners.get outer)
    (member outer) ((face.owner_le outer).trans later)

namespace PhysicalSamples
variable {selected request traces cache coefficients schedules owners perimeters}
  (samples :
    RequestedSurfaceRuns.PhysicalSamples
    selected request traces cache coefficients schedules owners perimeters)

/-- Package each acquired occurrence bank with its original geometry, sample area and budget indices. -/
@[expose] def entries : PhysicalRunEntries retained
  inputs coefficients stage :=
  Data.Vector.DependentVector.ofFn fun outer => (samples.get outer).entry

/-- Each packaged physical bank preserves its actual requested occurrence mesh depth. -/
theorem entry_depth (outer : Fin prepared.occurrences.length) :
    (samples.entries.get outer).depth =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.mesh outer selected
      request).depth := by
  dsimp only
    [entries,
    -eq_self, -iff_self]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact (samples.get outer).entry_depth

/-- Each packaged physical bank preserves its actual requested side capacity. -/
theorem entry_capacity (outer : Fin prepared.occurrences.length) :
    (samples.entries.get outer).capacity =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities selected
      request outer := by
  dsimp only
    [entries,
    -eq_self, -iff_self]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact (samples.get outer).entry_capacity

/-- Every packaged occurrence allowance is bounded by one. -/
theorem entry_allowance (outer : Fin prepared.occurrences.length) : (samples.entries.get outer).allowance ≤ 1 := by
  dsimp only
    [entries,
    -eq_self, -iff_self]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact (samples.get outer).entry_allowance

/-- Every packaged occurrence tolerance fits each original retained parent request. -/
theorem entry_tolerance (outer : Fin prepared.occurrences.length)
    (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    (samples.entries.get outer).tolerance ≤ ((schedules.get outer).requests.get position).blocks.budget.tolerance := by
  dsimp only
    [entries,
    -eq_self, -iff_self]
  rw [Data.Vector.DependentVector.ofFn_get]
  exact (samples.get outer).entry_tolerance position

/-- Each packaged area is the centered area of its exact cached weighted side sample. -/
theorem entry_sideArea (outer : Fin prepared.occurrences.length) :
    (samples.entries.get outer).sideArea =
      (((samples.get outer).samples.get (traces.get outer) cache coefficients
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).sideOccurrence.side).centeredArea) := by
  dsimp only
    [entries,
    -eq_self, -iff_self]
  rw [Data.Vector.DependentVector.ofFn_get]
  rfl

end PhysicalSamples
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
