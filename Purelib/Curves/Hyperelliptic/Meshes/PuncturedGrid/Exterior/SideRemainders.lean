module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

/-! The original reciprocal-cap occurrences consume the shared fine-side
remainders. Their source triangles, sheets, orientations and multiplicities
are preserved; one endpoint allowance pays the complete occurrence list. -/
universe u

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet}
  {meshTarget : Fraction.Rational} {i j : Fin genus} {stage : Nat} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    meshTarget}

namespace SurfaceOccurrence

/-- The actual oriented mesh side retained by this original exterior surface occurrence. -/
@[expose] def sideOccurrence (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) : Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SideOccurrence
  lifted.mesh :=
  (Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace.sideOccurrence occurrence.placement).val

/-- The retained mesh side has the exact source edge of the original exterior placement. -/
theorem side_source (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) :
    occurrence.sideOccurrence.source = occurrence.placement.location.sourceEdge :=
  (Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace.sideOccurrence
    occurrence.placement).property

/-- The original oriented fine-side area minus its retained source-chord contribution. -/
@[expose] def fineRemainder (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (perimeters : Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
      : Gaussian :=
  Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrenceFineArea perimeters
    occurrence.sideOccurrence -
    Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right
    occurrence.placement.location.sourceEdge

/-- The exterior fine remainder equals the side remainder with its original retained orientation. -/
theorem fineRemainder_eq (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (perimeters : Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
      :
    occurrence.fineRemainder perimeters left right =
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
      occurrence.sideOccurrence
      (Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters
        occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side) := by
  unfold
    fineRemainder
  rw [← occurrence.side_source]
  exact Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrence_remainder perimeters
    occurrence.sideOccurrence left right

/-- The paid endpoint request bounds the original fine remainder against the centered area on the same side occurrence.
-/
theorem centered_error (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    {error : Fraction.Rational} (endpoints :
      PerimeterEndpointRequest fixed i j error) (later :
      endpoints.index ≤ stage)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j)
    (perimeters : Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
      :
    Data.Gaussian.Norm.Basic.normSq (occurrence.fineRemainder perimeters left right -
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
      samples occurrence.sideOccurrence) ≤ error := by
  have transport := congrArg (fun source => Data.Gaussian.Norm.Basic.normSq
    (Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrenceFineArea perimeters
    occurrence.sideOccurrence -
    Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right source -
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
      samples occurrence.sideOccurrence)) occurrence.side_source
  exact transport.symm.trans_le
    (SideOccurrenceReadings.LiftedPuncturedGrid.PerimeterEndpointRequest.occurrence_bound
    endpoints later samples perimeters left right occurrence.sideOccurrence)

end SurfaceOccurrence
namespace AllSurfacePreparation

/-- The side sources project to the literal original exterior word, preserving
both laps, component order and every retained occurrence. -/
theorem sideSources_project (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential) :
    prepared.occurrences.map (fun occurrence => occurrence.sideOccurrence.source.project
      lifted.mesh.triangulation.faces) =
      lifted.exteriorBoundaries.flatten := open Purelib in by
  have equal : prepared.occurrences.map (fun occurrence => occurrence.sideOccurrence.source.project
    lifted.mesh.triangulation.faces) =
      prepared.occurrences.map (fun occurrence => occurrence.placement.indexed) := by
    apply Data.List.Map.map_congr_left
    intro occurrence _
    exact (congrArg (fun source => source.project lifted.mesh.triangulation.faces) occurrence.side_source).trans
      occurrence.placement.location.sourceEdge_project
  exact equal.trans prepared.indexed_eq

/-- Sum the original fine-side remainders in the retained exterior occurrence order. -/
@[expose] def fineRemainder (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (perimeters : Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
      : Gaussian :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence => occurrence.fineRemainder
    perimeters left right))

/-- Sum the centered original side areas over the exact retained exterior occurrences. -/
@[expose] def centeredSideArea (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j) :
      Gaussian :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence =>
    Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
    samples occurrence.sideOccurrence))

set_option genInjectivity false in
/-- Count and allowance depend only on the original cap occurrence list. -/
structure SideRemainderRequest (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
      sheet) (i j : Fin genus) (target : Fraction.Rational) where
  /-- The requested complete exterior remainder target is positive. -/ positive : 0 < target
  /-- The cached original exterior occurrence count. -/ count : Nat
  /-- The count includes every retained occurrence and repetition. -/ count_eq : count = prepared.occurrences.length
  /-- The common per-occurrence endpoint allowance. -/ allowance : Fraction.Rational
  /-- The allowance is allocated from the target and exact retained count. -/ allowance_eq : allowance =
    Rational.Budget.Aggregate.perTerm target count
  /-- The original endpoint request paid at the common occurrence allowance. -/ endpoints :
    PerimeterEndpointRequest fixed i j allowance

constructive_injectivity SideRemainderRequest

namespace SideRemainderRequest
variable {prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target : Fraction.Rational}

/-- Allocate one endpoint allowance from the complete original exterior occurrence count. -/
@[expose] def build (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
      sheet) (i j : Fin genus) (target : Fraction.Rational) (positive : 0 < target) :

      AllSurfacePreparation.SideRemainderRequest
      prepared fixed i j target :=
  let count := prepared.occurrences.length
  let allowance := Rational.Budget.Aggregate.perTerm target count
  ⟨positive, count, rfl, allowance, rfl,
    PerimeterEndpointRequest.build fixed i j allowance
      (Rational.Budget.Aggregate.perTerm_positive positive count)⟩

/-- The Gaussian sum of pointwise differences is the difference of the original two list sums. -/
private theorem sum_difference {Item : Type u} (items : List Item) (first last : Item → Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map (fun item => first item - last item)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map first) - Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map
      last) := by
  induction items with
  | nil => exact (sub_self _).symm
  | cons head tail ih =>
    change (first head - last head) + _ = (first head + _) - (last head + _)
    rw [ih]
    ring1

/-- Full fine-side remainders and centered values use the same occurrence
owners, and the requested estimate pays every retained repetition. -/
theorem accurate (allocated :
  AllSurfacePreparation.SideRemainderRequest
  prepared fixed i j target)
    (later : allocated.endpoints.index ≤ stage) (samples :
      Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j)
    (perimeters : Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
      :
    Data.Gaussian.Norm.Basic.normSq (prepared.fineRemainder perimeters left right - prepared.centeredSideArea
      samples) < target := open Purelib in by
  let errors := prepared.occurrences.map (fun occurrence => occurrence.fineRemainder perimeters left right -
    Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
    samples occurrence.sideOccurrence)
  have bounded : ∀ value ∈ errors, Data.Gaussian.Norm.Basic.normSq value ≤ allocated.allowance := by
    intro value member
    obtain ⟨occurrence, _, equal⟩ := Data.List.Map.mem_map.mp member
    exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).symm.trans_le (occurrence.centered_error
      allocated.endpoints later samples perimeters left right)
  have estimate := Gaussian.Norm.Sum.Bounds.normSq_sum_le errors allocated.allowance bounded
  have count : errors.length = allocated.count := (Data.List.Map.length_map ..).trans allocated.count_eq.symm
  rw [count, allocated.allowance_eq] at estimate
  have paid := estimate.trans_lt (Rational.Budget.Aggregate.count_mul_perTerm_lt allocated.positive allocated.count)
  have equal : Data.Gaussian.Norm.Sum.Basic.gaussianSum errors = prepared.fineRemainder perimeters left right -
    prepared.centeredSideArea samples := by
    dsimp only
      [fineRemainder,
      centeredSideArea,
      errors, -eq_self, -iff_self]
    exact
      sum_difference
      prepared.occurrences
      (fun occurrence :
        SurfaceOccurrence
        regular domains differential => occurrence.fineRemainder (request := request) (cache := cache) perimeters left
        right)
      (fun occurrence :
        SurfaceOccurrence
        regular domains differential =>
        Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
        samples occurrence.sideOccurrence)
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).symm.trans_lt paid

end SideRemainderRequest
end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
