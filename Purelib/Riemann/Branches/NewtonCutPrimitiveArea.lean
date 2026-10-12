module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewnPathArea
public import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Vector.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Topology.Polygon.Stokes
import Purelib.RootIsolation.State.Raw
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-!
# Paid Newton polygons from the actual sewn primitive bank

The original band comparison, cut occurrences and sewing contacts are cached
once. A positive request selects a common late index at which the complete
cut-increment polygon agrees with the original Newton source polygon.
This pays inherited sewing errors without identifying distinct cut vertices.
-/

namespace Purelib.Riemann.Branches.NewtonCutPrimitiveArea.CutSourceWord

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces (CutSourceWord)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.BoundaryRibbon (area)

section
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Data.Gaussian
/-- Compute the ordered area corrections from original edge starts to the accumulated increment anchor.

Each original directed occurrence contributes its displacement term before the anchor advances by that same edge
increment. -/
@[expose] def offsetTerms {count : Nat} (values : Fin count → Basic.Canonical) (anchor : Basic.Canonical) :
    List (OrientedEdge count) → List Basic.Canonical
  | [] => []
  | edge :: tail =>
      let increment := values edge.finish - values edge.start
      area (values edge.start - anchor) increment :: offsetTerms values (anchor + increment) tail

/-- An edge's area splits into its anchor-based increment area and exact displacement correction. -/
private theorem displaced_edge (first last anchor : Basic.Canonical) :
    area first last = area anchor (anchor + (last - first)) + area (first - anchor) (last - first) := by
  apply Basic.ext <;>
    simp only [-eq_self, -iff_self, area, Data.Gaussian.Basic.conj,
      Basic.add_re, Basic.add_im,
      Basic.sub_re, Basic.sub_im,
      Basic.mul_re, Basic.mul_im] <;> ring1

end

open Purelib.Integration.Path.BoundaryRibbon (area) in
open Purelib.Data.Gaussian in
open Purelib.Integration.Energy in
open Purelib.Integration.Path in
/-- The original occurrence area equals the increment trace area plus the ordered displacement corrections. -/
theorem occurrence_area {count : Nat} (values : Fin count → Basic.Canonical) (anchor : Basic.Canonical) (edges : List
  (OrientedEdge count)) :
    edgeListArea (fun vertex => Polygon.energyPrimitivePoint (values vertex)) edges =
      IncrementArea.traceArea anchor (edges.map (fun edge => values edge.finish - values edge.start)) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (offsetTerms values anchor edges) := by
  induction edges generalizing anchor with
  | nil => exact (add_zero 0).symm
  | cons edge tail ih =>
      change area (values edge.start) (values edge.finish) + _ =
        (area anchor (anchor + (values edge.finish - values edge.start)) + _) +
          (area (values edge.start - anchor) (values edge.finish - values edge.start) + _)
      rw [displaced_edge (values edge.start) (values edge.finish) anchor, ih]
      ring1

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (OrientedEdge vertexCount)}
  {patch : CutPatch faces indices boundary} {original : List
    (SourceEdge faceCount)}

open Purelib.Data.Gaussian in
open Purelib.Integration.Energy in
set_option genInjectivity false in
/-- Cached raw occurrence area and exact displacement corrections for a retained cut-source word.

The stored terms and sums retain the same original edge order and sewn vertex values. -/
structure AreaReadback (word : CutSourceWord patch original) (values : Fin patch.count → Basic.Canonical) where
  /-- The retained ordered displacement-correction terms. -/ offsets : List Basic.Canonical
  /-- The cached terms equal the original word's exact offset computation from zero. -/ offsets_eq : offsets =
    offsetTerms values 0 word.edges
  /-- The cached sum of the retained displacement terms. -/ correction : Basic.Canonical
  /-- The correction cache equals the exact finite Gaussian sum of stored offsets. -/ correction_eq : correction =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum offsets
  /-- The cached original occurrence area. -/ raw : Basic.Canonical
  /-- The raw cache equals the edge-list area of the original word and vertex values. -/ raw_eq : raw = edgeListArea
    (fun vertex => Polygon.energyPrimitivePoint (values vertex)) word.edges

constructive_injectivity AreaReadback

namespace AreaReadback

open Purelib.Data.Gaussian in
open Purelib.Integration.Energy in
/-- Cache the original cut word's offset terms, correction sum and raw occurrence area. -/
@[expose] def build (word : CutSourceWord patch original) (values : Fin patch.count → Basic.Canonical) : AreaReadback
  word values :=
  let offsets := offsetTerms values 0 word.edges
  ⟨offsets, rfl, Data.Gaussian.Norm.Sum.Basic.gaussianSum offsets, rfl,
    edgeListArea (fun vertex => Polygon.energyPrimitivePoint (values vertex)) word.edges, rfl⟩

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- Subtracting the exact retained correction gives the original cut word's increment path area. -/
theorem corrected {word : CutSourceWord patch original} {values : Fin patch.count → Basic.Canonical}
    (readback : AreaReadback word values) :
    readback.raw - readback.correction =
      IncrementArea.pathArea (word.edges.map (fun edge => values edge.finish - values edge.start)) := by
  rw [readback.raw_eq, occurrence_area values 0, readback.correction_eq, readback.offsets_eq, add_sub_cancel_right]
  rfl

end AreaReadback
end Purelib.Riemann.Branches.NewtonCutPrimitiveArea.CutSourceWord

namespace Purelib.Riemann.Branches.NewtonCutPrimitiveArea.OuterPreparation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation (Comparison)
open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces (CutSourceWord)
open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.BranchCellBank.NewtonGrid.AnnularFaces.Lifted.OuterPreparation
  (cutSources)
open Purelib.Riemann.Branches.NewtonCutPrimitiveArea.CutSourceWord (AreaReadback)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (ContactBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting (Shape shape)
open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests (PathAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {index :
    Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : AnnularFaces grid index} {lifted :
    LiftedPuncturedGrid grid.punctured} {region :
    Lifted annulus lifted}
  {prepared : OuterPreparation region}
    {differential : Fin genus}
  {domains : FaceDomainBank lifted.frames
    grid.faces.regulars} {tolerance : Rational}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Topology.Surface in
set_option genInjectivity false in
/-- An original annular comparison with its retained cut word, source count, magnitude and prepared contacts.

The cut edges retain their original source owners, while the contact bank and shape cache refer to the same sewn
assembly. -/
structure CutComparison (prepared : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region)
  (differential : Fin genus)
    (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars) (tolerance :
      Fraction.Rational) where
  /-- The original annular outer-preparation comparison. -/ original :
    Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared differential domains tolerance
  /-- The retained cut-source word with exact original source owners. -/ word : CutSourceWord
    lifted.cutPolygon.patch.cut prepared.sources
  /-- The cached original outer-boundary occurrence count. -/ count : Nat
  /-- The count cache equals the original outer-boundary length. -/ count_eq : count = region.outer.length
  /-- The cached finite source-magnitude budget. -/ magnitude : Fraction.Rational
  /-- The magnitude cache equals the retained count times the original per-source bound. -/ magnitude_eq : magnitude =
    (count : Fraction.Rational) * (3 * tolerance + 4 * (target / 16))
  /-- The original sewn assembly's retained contact bank. -/ contacts : Sewing.SewnPrimitiveContacts.ContactBank
    lifted.cutPolygon.patch.assembly
  /-- Prepared contact coverage for the same original differential and domains. -/ covered :
    Meshes.PuncturedGrid.ContactBanks.ContactPreparations contacts.entries (standardDifferential differential) domains
  /-- The cached shape of the original sewn assembly. -/ profile : Sewing.SewnPrimitiveAccounting.Shape
  /-- The profile cache equals the original assembly's exact shape. -/ profile_eq : profile =
    Sewing.SewnPrimitiveAccounting.shape lifted.cutPolygon.patch.assembly

constructive_injectivity CutComparison

namespace CutComparison

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Topology.Surface in
/-- Retain an original annular comparison's cut-source word, magnitude budget, contact preparations and shape cache. -/
@[expose] def ofComparison (comparison : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison
  prepared differential domains tolerance) :
    CutComparison prepared differential domains tolerance :=
  let word := cutSources prepared
  let count := region.outer.length
  let magnitude := Budget.Aggregate.countCoordinate count * (3 * tolerance + 4 * (target / 16))
  let contacts := Sewing.SewnPrimitiveContacts.ContactBank.build lifted.cutPolygon.patch.assembly
  ⟨comparison, word, count, rfl, magnitude, by dsimp only [-eq_self, -iff_self, magnitude]; rw
    [Budget.Aggregate.countCoordinate_eq],
    contacts, Meshes.PuncturedGrid.ContactBanks.ContactPreparations.ofAssembly contacts _ domains,
      Sewing.SewnPrimitiveAccounting.shape lifted.cutPolygon.patch.assembly, rfl⟩

variable (comparison : CutComparison prepared differential domains tolerance)

open Purelib.Curves.Hyperelliptic in
/-- The original retained source list has the cached comparison count. -/
theorem source_count : prepared.sources.length = comparison.count := by
  have count := congrArg List.length (Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.sources_project
    prepared)
  rw [Purelib.Data.List.Map.length_map, ← comparison.count_eq] at count
  exact count

/-- The retained cut-edge word has the cached comparison count. -/
theorem word_count : comparison.word.edges.length = comparison.count :=
  comparison.word.length_eq.trans comparison.source_count

open Purelib.Curves.Hyperelliptic in
open Purelib.Topology.Surface in
/-- The retained cut-edge word projects to the exact original annular outer boundary. -/
theorem word_project : comparison.word.edges.map (Sewing.VertexSewing.OrientedEdge.map
  lifted.cutPolygon.patch.cut.vertexLabels) = region.outer :=
  comparison.word.project.trans (Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.sources_project
    prepared)

open Purelib.Data.Rat in
/-- The retained finite source-magnitude budget is nonnegative. -/
theorem magnitude_nonnegative : 0 ≤ comparison.magnitude := by
  rw [comparison.magnitude_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) comparison.original.reference.bound_nonnegative

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- Later original triangle readings satisfy the retained source-word magnitude budget. -/
theorem source_magnitude {stage : Nat} (later : comparison.original.reference.index ≤ stage)
    {shared : Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (standardDifferential differential) stage
      domains}
    (readings : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    Norm.Sum.Basic.gaussianNormSqSum (comparison.word.sources.sources.map (fun source => source.increment
      readings.values)) ≤ comparison.magnitude := by
  rw [comparison.word.sources_eq]
  have bounded : ∀ value ∈ prepared.sources.map (fun source => source.increment readings.values),
      Data.Gaussian.Norm.Basic.normSq value ≤ 3 * tolerance + 4 * (target / 16) := by
    rw [prepared.sources_eq]
    exact comparison.original.reference.source_bound comparison.original.shared later readings
  have bound := Purelib.Data.Gaussian.Norm.Sum.Bounds.normSum_le _ _ bounded
  rw [Purelib.Data.List.Map.length_map, comparison.source_count, ← comparison.magnitude_eq] at bound
  exact bound

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Topology.Surface in
set_option genInjectivity false in
/-- A cut-area request with an exact path-area budget and contact request beyond the original reference floor.

The same retained contact preparations pay the path tolerance, and the stage floor includes the original comparison
reference. -/
structure Request (comparison : CutComparison prepared differential domains tolerance) (error : Fraction.Rational)
  (floor : Nat) where
  /-- The retained path-area request with original count and magnitude budget. -/ budget :
    Sewing.SewnPathAreaRequests.PathAreaRequest lifted.cutPolygon.patch.assembly comparison.count comparison.magnitude
    error
  /-- The retained contact request at the exact path tolerance and combined original reference floor. -/ contact :
    Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request comparison.covered budget.path.tolerance
    (max floor comparison.original.reference.index)

constructive_injectivity Request

namespace Request

variable {comparison : CutComparison prepared differential domains tolerance} {error :
  Rational} {floor : Nat}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Topology.Surface in
/-- Construct a path-area budget and matching contact request from the original cut comparison.

The retained magnitude and exact assembly shape determine the path tolerance; its contact floor includes both the
requested floor and original reference stage. -/
@[expose] def build (comparison : CutComparison prepared differential domains tolerance) (error : Fraction.Rational)
    (positive : 0 < error) (floor : Nat) : Request comparison error floor :=
  let budget := Sewing.SewnPathAreaRequests.PathAreaRequest.ofProfile comparison.profile comparison.profile_eq
    comparison.count comparison.magnitude error
    comparison.magnitude_nonnegative positive
  ⟨budget, Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request.build comparison.covered budget.path.tolerance
    budget.path.tolerance_positive
    (max floor comparison.original.reference.index)⟩

/-- The retained contact stage meets the original requested floor. -/
theorem floor_le (request : Request comparison error floor) : floor ≤ request.contact.index :=
  (Purelib.Data.Nat.Order.le_max_left _ _).trans request.contact.floor_le

/-- A stage meeting the retained contact request also meets the original reference stage. -/
theorem reference_later (request : Request comparison error floor) {stage : Nat} (later : request.contact.index ≤ stage)
  :
    comparison.original.reference.index ≤ stage :=
  (Purelib.Data.Nat.Order.le_max_right _ _).trans (request.contact.floor_le.trans later)

open Purelib.Integration.Path.BoundaryRibbon (area) in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Topology.Surface in
/-- The retained cut-area request bounds the difference between sewn and original source increment areas. -/
theorem accurate (request : Request comparison error floor) {stage : Nat} (later : request.contact.index ≤ stage)
    {shared : Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (standardDifferential differential) stage
      domains}
    (readings : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (surface :
      Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values)
    (area : Sewing.SewnPathArea.PathSources.Sample.AreaSample
      (Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample surface comparison.word.sources)) :
      Data.Gaussian.Norm.Basic.normSq (area.sewn.area - area.source.area) < error := by
  have locallyAccurate := request.contact.localAccuracy_of_coverage
    (fun _ member => comparison.contacts.entries_eq.symm ▸ member) le_rfl later readings surface.sewn.readings
  have small := request.budget.path.cached_accurate surface locallyAccurate comparison.word.sources
    comparison.word_count.le
  exact request.budget.accurate area comparison.word_count (comparison.source_magnitude (request.reference_later later)
    readings) small

end Request

open Purelib.Integration.Path.BoundaryRibbon (area) in
open Purelib.Curves.Hyperelliptic in
open Purelib.Topology.Surface in
set_option genInjectivity false in
/-- Cached source-path and area readbacks for the same original sewn sample and cut comparison.

The exact original cached path drives the area sample, while occurrence readbacks retain the same sewn vertex values. -/
structure Sample (comparison : CutComparison prepared differential domains tolerance) {stage : Nat}
    {shared : Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (standardDifferential differential) stage
      domains}
    (readings : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (surface :
      Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values) where
  /-- The retained original cached source-path sample on the same sewn faces. -/ path :
    Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources.Sample comparison.word.sources surface.faces
  /-- The retained path equals the exact original cached-path construction. -/ path_eq : path =
    Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample surface comparison.word.sources
  /-- The area readback of the exact retained source-path sample. -/ area :
    Sewing.SewnPathArea.PathSources.Sample.AreaSample path
  /-- The retained occurrence-area readback for the same cut word and sewn vertex values. -/ occurrences : AreaReadback
    comparison.word surface.sewn.values

constructive_injectivity Sample

namespace Sample

variable {comparison : CutComparison prepared differential domains tolerance} {stage : Nat}
  {shared : FacePrimitiveBank (standardDifferential
    differential) stage domains}
  {readings : TriangleReadings shared
    lifted.mesh} {surface : CachedSample lifted.cutPolygon.patch
    readings.values}

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Branches in
open Purelib.Topology.Surface in
/-- Cache the original source-path sample, its area readback and the matching cut-word occurrence correction.

The area sample consumes the exact stored path, and the occurrence terms use the original sewn vertex values. -/
@[expose] def build (comparison : CutComparison prepared differential domains tolerance)
    (readings : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (surface :
      Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values) :
    Sample comparison readings surface :=
  let path := Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample surface comparison.word.sources
  ⟨path, rfl, Sewing.SewnPathArea.PathSources.Sample.AreaSample.build path,
    NewtonCutPrimitiveArea.CutSourceWord.AreaReadback.build comparison.word surface.sewn.values⟩

open Purelib.Integration.Path in
/-- The retained source area equals the original preparation's source-increment path area. -/
theorem source_area (sample : Sample comparison readings surface) :
    sample.area.source.area = IncrementArea.pathArea (prepared.sources.map (fun source => source.increment
      readings.values)) := by
  rw [sample.area.source_path, comparison.word.sources_eq]

open Purelib.Integration.Path in
open Purelib.Topology.Surface in
/-- The retained sewn area equals the cut word's sewn-increment path area. -/
theorem sewn_area (sample : Sample comparison readings surface) :
    sample.area.sewn.area = IncrementArea.pathArea (comparison.word.edges.map
      (fun edge => surface.sewn.values edge.finish - surface.sewn.values edge.start)) :=
  sample.area.sewn.area_eq.trans (congrArg IncrementArea.pathArea
    (Sewing.SewnPathArea.PathSources.Sample.areaPairs_left sample.path))

open Purelib.Integration.Path.BoundaryRibbon (area) in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained sample pays the original request's sewn-versus-source area bound at every sufficient contact stage. -/
theorem accurate (sample : Sample comparison readings surface) {error : Fraction.Rational} {floor : Nat}
    (request : Request comparison error floor) (later : request.contact.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (sample.area.sewn.area - sample.area.source.area) < error := by
  rcases sample with ⟨path, path_eq, area, occurrences⟩
  cases path_eq
  exact request.accurate later readings surface area

open Purelib.Integration.Energy in
/-- The retained raw occurrence area equals the original sewn sample's energy-value edge-list area. -/
theorem raw_area (sample : Sample comparison readings surface) :
    sample.occurrences.raw = edgeListArea surface.energyValues comparison.word.edges := by
  rw [sample.occurrences.raw_eq]
  have equal : ∀ edges : List (OrientedEdge lifted.cutPolygon.patch.cut.count),
      edgeListArea (fun vertex => Polygon.energyPrimitivePoint (surface.sewn.values vertex)) edges =
        edgeListArea surface.energyValues edges := by
    intro edges
    induction edges with
    | nil => rfl
    | cons edge tail ih => rw [edgeListArea, edgeListArea, surface.energyValues_eq, surface.energyValues_eq, ih]
  exact equal comparison.word.edges

/-- The retained raw area minus its exact correction equals the sewn increment area. -/
theorem corrected_area (sample : Sample comparison readings surface) :
    sample.occurrences.raw - sample.occurrences.correction = sample.area.sewn.area :=
  sample.occurrences.corrected.trans sample.sewn_area.symm

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The corrected occurrence area differs from the original source path area by less than the requested error. -/
theorem corrected_accurate (sample : Sample comparison readings surface) {error : Fraction.Rational} {floor : Nat}
    (request : Request comparison error floor) (later : request.contact.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq ((sample.occurrences.raw - sample.occurrences.correction) -
      IncrementArea.pathArea (prepared.sources.map (fun source => source.increment readings.values))) < error := by
  rw [sample.corrected_area, ← sample.source_area]
  exact sample.accurate request later

end Sample
end CutComparison
end Purelib.Riemann.Branches.NewtonCutPrimitiveArea.OuterPreparation
