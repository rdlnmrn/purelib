module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandSideReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.Newton.Band.Basic

public section

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

/-! Build band-side requests before acquiring the shared numerical bank.
The later readings reuse the supplied trace geometry and normalized domains. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet}
  {target : Fraction.Rational} {i j : Fin genus} {stage : Nat} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    target}

/-- The actual rectangle perimeter traces for every retained regular position and sheet.

This geometry is fixed before acquiring the shared polynomial stage; later centered samples reuse these exact traces. -/
@[expose] def PerimeterTraceBank
    (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      target) :=
  Data.Vector.DependentVector (fun position : Fin base.faces.regulars.length => Data.Vector.DependentVector (fun sheet :
    Fin 2 =>
    Paths.RectangularPerimeterTraces.PerimeterTraces ((request.entries.get sheet).meshes.entries.get position)))

namespace PerimeterTraceBank

/-- Construct the original perimeter traces at every retained regular position and both sheets. -/
@[expose] def build (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
  target) :
    Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request :=
  Data.Vector.DependentVector.ofFn fun position => Data.Vector.DependentVector.ofFn fun sheet =>
    Paths.RectangularPerimeterTraces.PerimeterTraces.build ((request.entries.get sheet).meshes.entries.get position)

/-- Reuse all retained traces when sampling the late bank; the only newly
computed values are its centered primitive readings. -/
@[expose] def samples (traces : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
  (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage) (i j : Fin
  genus) :
    Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j :=
  ⟨traces, Data.Vector.DependentVector.ofFn fun position => Data.Vector.DependentVector.ofFn fun sheet =>
    Integration.RectangularCenteredPerimeter.Centered.build ((traces.get position).get sheet)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank in
/-- Sampling the centered perimeters preserves the exact supplied trace bank. -/
theorem samples_traces (traces : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
  (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage) (i j : Fin
  genus) :
    (samples traces cache i j).traces = traces := rfl

end PerimeterTraceBank

variable {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
  {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
  {family : RootContinuation.PreparedNewtonBandFamilies.DifferentialFamily profile genus} {bandTarget radius :
    Fraction.Rational}

/-- The original band-side request indexed by a retained oriented mesh-side occurrence.

Its domain, sheet and side come from that occurrence, while both differential indices share the same extracted Newton
band. -/
@[expose] def BandOccurrenceReference (traces :
  Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request) (band :
  RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family bandTarget radius)
    (i j : Fin genus) (occurrence : Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SideOccurrence
      lifted.mesh) :=
  Hyperelliptic.Meshes.PuncturedGrid.BandSideReferences.BandSideReference ((domains.get occurrence.position).domain
    occurrence.sheet)
    ((traces.get occurrence.position).get occurrence.sheet) band i j occurrence.side

namespace BandOccurrenceReference
variable {traces : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request}
  {band : RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family bandTarget radius}
  {occurrence : Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SideOccurrence lifted.mesh}

/-- Prepare the selected occurrence's two-differential side request on its retained trace and Newton band. -/
@[expose] def build (traces : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
  (band : RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family bandTarget radius)
    (i j : Fin genus) (occurrence : Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SideOccurrence
      lifted.mesh) : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceReference traces band i j
      occurrence :=
  Hyperelliptic.Meshes.PuncturedGrid.BandSideReferences.BandSideReference.build ((traces.get occurrence.position).get
    occurrence.sheet) band i j occurrence.side

/-- The retained late-stage threshold of the original occurrence-side request. -/
@[expose] def index (reference : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceReference
  traces band i j occurrence) : Nat :=
  Hyperelliptic.Meshes.PuncturedGrid.BandSideReferences.BandSideReference.index occurrence.side reference

/-- Bound the oriented occurrence area by the common Newton coefficient times the squared selected radius.

The original trace-length certificate and actual boundary membership supply the side geometry; both readings use the
same sufficiently late numerical cache. -/
theorem area_bound (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache
  i j) (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples)
    (reference : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceReference samples.traces band i
      j occurrence)
    (boundary : Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences.SideOccurrence.OnBoundary occurrence
      band.selection.sample.output.box)
    (later : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceReference.index reference ≤ stage)
      :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
      samples occurrence) ≤
      RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient family *
        band.selection.sample.output.radius^2 := by
  change Data.Gaussian.Norm.Basic.normSq
    (Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
    occurrence _) ≤ _
  rw [Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.normSq_oriented
    occurrence]
  exact Hyperelliptic.Meshes.PuncturedGrid.BandSideReferences.BandSideReference.area_bound reference ((lengths.get
    occurrence.position).get occurrence.sheet)
    (Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.BranchCellBank.LiftedMesh.SideOccurrence.boundary
      occurrence boundary) later (cache.normalize.atDomain occurrence.position occurrence.sheet i)
    (cache.normalize.atDomain occurrence.position occurrence.sheet j)
    ((samples.samples.get occurrence.position).get occurrence.sheet)

end BandOccurrenceReference

set_option genInjectivity false in
/-- Materialized requests retain the exact occurrence list, with one cached
maximum controlling both components of every later side reading. -/
structure BandOccurrenceBank (traces : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank
  request)
    (band : RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family bandTarget radius) (i j : Fin genus)
    (occurrences : List (Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SideOccurrence lifted.mesh))
      where
  /-- The materialized original side request for each retained list position, including repetitions. -/ references :
    Data.Vector.DependentVector (fun position : Fin occurrences.length =>
    Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceReference traces band i j
      (occurrences[position.val]'position.isLt))
  /-- The cached common stage threshold for every retained occurrence request. -/ index : Nat
  /-- Every materialized occurrence threshold is bounded by the common cached index. -/ index_ge : ∀ position,
    Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceReference.index (references.get position) ≤
    index

constructive_injectivity BandOccurrenceBank

namespace BandOccurrenceBank
variable {traces : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request}
  {band : RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family bandTarget radius}
  {occurrences : List (Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SideOccurrence lifted.mesh)}

/-- Materialize the original ordered occurrence requests and cache their maximum stage threshold. -/
@[expose] def build (traces : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
  (band : RootContinuation.PreparedNewtonBandFamilies.PreparedBandFamily family bandTarget radius)
    (i j : Fin genus) (occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SideOccurrence lifted.mesh)) :
    Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceBank traces band i j occurrences :=
  let references := Data.Vector.DependentVector.ofFn fun position : Fin occurrences.length =>
    Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceReference.build traces band i j
      (occurrences[position.val]'position.isLt)
  ⟨references, references.maximum (fun _ reference =>
    Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceReference.index reference),
    references.get_le_maximum (fun _ reference =>
      Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceReference.index reference)⟩

/-- Every listed occurrence satisfies the Newton area bound once the cached common threshold is reached. -/
theorem entry_bound (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request
  cache i j) (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples)
    (bank : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceBank samples.traces band i j
      occurrences)
    (boundary : ∀ occurrence ∈ occurrences,
      Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences.SideOccurrence.OnBoundary occurrence
      band.selection.sample.output.box)
    (later : bank.index ≤ stage) : ∀ occurrence ∈ occurrences,
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
      samples occurrence) ≤
      RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient family *
        band.selection.sample.output.radius^2 := by
  intro occurrence member
  obtain ⟨position, bound, equal⟩ := List.mem_iff_getElem.mp member
  have estimate := Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceReference.area_bound samples
    lengths (bank.references.get ⟨position, bound⟩)
    (boundary _ (List.getElem_mem bound)) ((bank.index_ge ⟨position, bound⟩).trans later)
  exact equal ▸ estimate

/-- The squared norm of the original ordered occurrence-area sum is bounded by the squared occurrence count times the
Newton area estimate.

Every original occurrence must lie on the selected band boundary, and all area readings use the common cache after the
retained request threshold. -/
theorem sum_bound (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache
  i j) (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples)
    (bank : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceBank samples.traces band i j
      occurrences)
    (boundary : ∀ occurrence ∈ occurrences,
      Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences.SideOccurrence.OnBoundary occurrence
      band.selection.sample.output.box)
    (later : bank.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (occurrences.map
      (Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
      samples))) ≤
      (occurrences.length : Fraction.Rational) * ((occurrences.length : Fraction.Rational) *
        (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient family *
          band.selection.sample.output.radius^2)) := by
  have bounded : ∀ value ∈ occurrences.map
    (Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
    samples), Data.Gaussian.Norm.Basic.normSq value ≤
      RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient family *
        band.selection.sample.output.radius^2 := by
    intro value member
    obtain ⟨occurrence, member, equal⟩ := Data.List.Map.mem_map.mp member
    exact equal ▸ Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceBank.entry_bound samples
      lengths bank boundary later occurrence member
  have estimate := Gaussian.Norm.Sum.Bounds.normSq_sum_le _ _ bounded
  rw [Purelib.Data.List.Map.length_map] at estimate
  exact estimate

end BandOccurrenceBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
