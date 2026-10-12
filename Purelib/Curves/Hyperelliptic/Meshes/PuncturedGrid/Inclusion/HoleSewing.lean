module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.List.Permutation
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewnPathArea
import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests
public import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Tactic.Ring
public import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.CircuitSewing

public section

/-! The doubled original cell walk on the actual sewn cut surface. Every
cut occurrence and its offset correction is retained, rather than treating
distinct cut vertices with the same projected coordinate as equal. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Branches.NewtonCutPrimitiveArea
open Purelib.Riemann.Branches.NewtonCutPrimitiveArea.CutSourceWord
open Purelib.Topology.Mesh
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewnPathArea
open Purelib.Topology.Surface.Sewing.SewnPathArea.PathSources.Sample
open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces
open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests (SourceChartAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (paired_sources_nonloop)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces (CutSourceWord)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (ContactBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting (Shape shape)
open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests (PathAreaRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests (IncludedStemRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests (IncludedHoleRequest)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {current : LiftedPuncturedGrid next}
  (bank : BasedBranchBank lifted)
    (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)

/-- The original branch-cell boundary resplit on the enlarged grid and traversed twice. -/
@[expose] def doubleWalk (branch : BranchIsolation.Data.Index branches) :=
  let walk := included.resplit (bank.rows.get branch).boundary ((base.bank.cell branch).anchor_mem (base.bank.cell_mem
    branch))
  walk.append walk

variable {domains : FaceDomainBank current.frames
  next.faces.regulars} {differential : Differential genus}

set_option genInjectivity false in
/-- The doubled original-cell walk retained on the actual sewn cut surface.

Its source word preserves every cut occurrence, with the full contact bank and exact assembly profile. -/
structure IncludedHoleSewing (branch : BranchIsolation.Data.Index branches)
    (domains : DomainBanks.FaceDomainBank current.frames next.faces.regulars) (differential :
      Differentials.Basic.Differential genus) where
  /-- The actual paired source placement of the doubled resplit boundary. -/ paired : WalkOccurrences.PairedWalk
    current.mesh (doubleWalk bank included branch)
  /-- The cut source word retaining the exact ordered source occurrences. -/ word : CutSourceWord
    current.cutPolygon.patch.cut (paired.sources 0)
  /-- The complete retained contact bank on the actual cut assembly. -/ contacts : SewnPrimitiveContacts.ContactBank
    current.cutPolygon.patch.assembly
  /-- Differential preparations covering the same retained contact entries. -/ covered :
    ContactBanks.ContactPreparations contacts.entries differential domains
  /-- The cached finite shape of the cut assembly. -/ profile : SewnPrimitiveAccounting.Shape
  /-- The cached profile is the actual cut-assembly shape. -/ profile_eq : profile = SewnPrimitiveAccounting.shape
    current.cutPolygon.patch.assembly

constructive_injectivity IncludedHoleSewing

namespace IncludedHoleSewing

variable {bank included} {branch : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}

/-- Construct the doubled boundary placement, its cut source word and the covered contact bank on the retained assembly.
-/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (included : Extension.CoordinateInclusion
  base.bank.grid next.bank.grid)
    (branch : BranchIsolation.Data.Index branches) (domains : DomainBanks.FaceDomainBank current.frames
      next.faces.regulars)
    (differential : Differentials.Basic.Differential genus) : IncludedHoleSewing bank included branch domains
      differential :=
  let paired := PairedWalk.build current.mesh (doubleWalk bank included branch)
  let word := CutSourceWord.build current.cutPolygon.patch.cut (paired.sources 0) (by
    intro source member
    exact ⟨(Permutation.mem_iff current.cutPolygon.coverage source.source).mpr
      (Permutation.ofFn_mem (fun index => index) source.source), SignedSourceChartRequests.paired_sources_nonloop paired
        0 source member⟩)
  let contacts := ContactBank.build current.cutPolygon.patch.assembly
  ⟨paired, word, contacts, ContactPreparations.ofAssembly contacts differential domains,
    SewnPrimitiveAccounting.shape current.cutPolygon.patch.assembly, rfl⟩

/-- Projecting the retained cut-edge word recovers the actual indexed doubled original-cell walk. -/
theorem project (geometry : IncludedHoleSewing bank included branch domains differential) :
    geometry.word.edges.map (OrientedEdge.map current.cutPolygon.patch.cut.vertexLabels) =
      current.edges.indexedEdges current.vertices (doubleWalk bank included branch) 0 :=
  geometry.word.project.trans (geometry.paired.sources_project 0)

set_option genInjectivity false in
/-- A paid comparison of a retained sewn hole word with its canonical chart word.

The path, contact and source-to-chart requests share the actual word count and magnitude budget. -/
structure Request (geometry : IncludedHoleSewing bank included branch domains differential)
    (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (target : Fraction.Rational) (floor : Nat) where
  /-- The requested squared-area error is strictly positive. -/ positive : 0 < target
  /-- The cached number of retained cut-edge occurrences. -/ count : Nat
  /-- The occurrence count reads the actual retained cut word. -/ count_eq : count = geometry.word.edges.length
  /-- The cached bound on the sum of source-increment squared norms. -/ magnitude : Fraction.Rational
  /-- The magnitude is the retained occurrence count times the paid edge-magnitude bound. -/ magnitude_eq : magnitude =
    (count : Fraction.Rational) * (4 * fixed.bound)
  /-- The actual sewn path-area request at one quarter of the target. -/ budget : SewnPathAreaRequests.PathAreaRequest
    current.cutPolygon.patch.assembly count magnitude (target / 4)
  /-- The contact request paying the sewn path tolerance above both the supplied floor and magnitude stage. -/ contact :
    ContactPreparations.Request geometry.covered budget.path.tolerance (max floor fixed.index)
  /-- The actual source-to-chart area comparison at one quarter of the target. -/ chart : SourceChartAreaRequest fixed
    (geometry.paired.sources 0) (target / 4)
  /-- The cached maximum stage paying the contact and chart requests. -/ index : Nat
  /-- The cached stage equals the maximum of the retained contact and chart stages. -/ index_eq : index = max
    contact.index chart.index

constructive_injectivity Request

namespace Request

variable {geometry : IncludedHoleSewing bank included branch domains differential}
  {fixed : FaceMagnitudeBank domains differential}
    {target : Rational} {floor : Nat}

/-- Prepare the sewn path, covered contacts and source-to-chart requests, then cache their shared stage. -/
@[expose] def build (geometry : IncludedHoleSewing bank included branch domains differential)
    (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (target : Fraction.Rational) (positive : 0 < target)
      (floor : Nat) :
    Request geometry fixed target floor :=
  let count := geometry.word.edges.length
  let magnitude := (count : Fraction.Rational) * (4 * fixed.bound)
  have nonnegative : 0 ≤ magnitude := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      fixed.nonnegative)
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let budget := PathAreaRequest.ofProfile geometry.profile geometry.profile_eq count magnitude (target / 4) nonnegative
    quarterPositive
  let contact := ContactPreparations.Request.build geometry.covered budget.path.tolerance budget.path.tolerance_positive
    (max floor fixed.index)
  let chart := SourceChartAreaRequest.build fixed (geometry.paired.sources 0)
    (SignedSourceChartRequests.paired_sources_nonloop geometry.paired 0)
    (target / 4) quarterPositive
  ⟨positive, count, rfl, magnitude, rfl, budget, contact, chart, max contact.index chart.index, rfl⟩

/-- The actual retained source increments satisfy the cached total squared-norm budget at a paid magnitude stage. -/
private theorem source_magnitude (request : Request geometry fixed target floor)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (later : fixed.index ≤ stage) :
    Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (geometry.word.sources.sources.map (fun source => source.increment
      readings.values)) ≤ request.magnitude := by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh current.mesh) fixed later readings
  rw [geometry.word.sources_eq]
  have bound := Data.Gaussian.Norm.Sum.Bounds.normSum_le ((geometry.paired.sources 0).map (fun source =>
    source.increment readings.values)) (4 * fixed.bound) (by
    intro value member
    obtain ⟨source, _, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact retainedMagnitude.source_bounded source)
  change Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum ((geometry.paired.sources 0).map (fun source => source.increment
    readings.values)) ≤
    (((geometry.paired.sources 0).map (fun source => source.increment readings.values)).length : Fraction.Rational) *
      (4 * fixed.bound) at bound
  rw [Data.List.Map.length_map, ← geometry.word.length_eq, ← request.count_eq, ← request.magnitude_eq] at bound
  exact bound

/-- The actual cut-edge area minus all retained occurrence offsets agrees with the canonical doubled original-cell word
to the requested accuracy. -/
theorem accurate (request : Request geometry fixed target floor)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (surface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values)
    (readback : CutSourceWord.AreaReadback geometry.word surface.sewn.values)
    (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq ((readback.raw - readback.correction) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
        (current.edges.indexedEdges current.vertices (doubleWalk bank included branch) 0)) ≤ target := by
  have contactLater := (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  have chartLater := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have fixedLater := (Data.Nat.Order.le_max_right _ _).trans (request.contact.floor_le.trans contactLater)
  let path := CachedSample.pathSample surface geometry.word.sources
  let area := AreaSample.build path
  have locallyAccurate := request.contact.localAccuracy_of_coverage
    (fun _ member => geometry.contacts.entries_eq.symm ▸ member) le_rfl contactLater readings surface.sewn.readings
  have small := request.budget.path.cached_accurate surface locallyAccurate geometry.word.sources
    request.count_eq.symm.le
  have sewn := request.budget.accurate area request.count_eq.symm (request.source_magnitude readings fixedLater) small
  let sample := SingleReadings.ofReadings (owner := SourceChartComparison.ownerFromMesh current.mesh) readings
  let chartSources := SourceObservations.realize sample.values (geometry.paired.sources 0)
  let chartComparison := request.chart.realize sample chartSources chartLater
  have charts := chartComparison.pay
  rw [chartComparison.residual_readback] at charts
  rw [geometry.paired.sources_project] at charts
  have source : area.source.area = IncrementArea.pathArea
      ((geometry.paired.sources 0).map (fun source => source.increment readings.values)) := by
    rw [area.source_path, geometry.word.sources_eq]
  have actual : readback.raw - readback.correction = area.sewn.area :=
    readback.corrected.trans (area.sewn.area_eq.trans (congrArg IncrementArea.pathArea
      (PathSources.Sample.areaPairs_left path))).symm
  rw [actual]
  have chartBound : Data.Gaussian.Norm.Basic.normSq
      (area.source.area - RetracingWords.wordArea
        (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
        (current.edges.indexedEdges current.vertices (doubleWalk bank included branch) 0)) ≤ target / 4 := by
    have h := source ▸ charts
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    dsimp only [sample, SingleReadings.values,
      SingleReadings.ofReadings] at h
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    convert h using 1; rfl
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via area.sewn.area area.source.area
      (RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
        (current.edges.indexedEdges current.vertices (doubleWalk bank included branch) 0))).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct sewn.le chartBound) (by decide))
  exact estimate.trans_eq ((by ring1 : 2 * (target / 4 + target / 4) = target / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end Request
end IncludedHoleSewing

/-- Read the original based branch excursion from the actual sewn surface. Both the full doubled area and every
cut-occurrence correction remain in the conclusion; no projected-vertex equality is used to erase offsets. -/
theorem included_branch_sewn_accurate (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    (branch : BranchIsolation.Data.Index branches) (sheet : Fin 2)
    (target : Fraction.Rational) (positive : 0 < target) (floor : Nat) :
    let part := target / 4
    let partPositive : 0 < part := Fraction.Order.Field.div_pos_direct positive (by decide)
    let innerPositive : 0 < part / 10 := Fraction.Order.Field.div_pos_direct partPositive (by decide)
    let stems := IncludedStemRequest.build bank included fixed branch sheet (part / 10) innerPositive
    let holes := IncludedHoleRequest.build bank included fixed branch (part / 10) innerPositive
    let geometry := IncludedHoleSewing.build bank included branch domains differential
    let sewing := IncludedHoleSewing.Request.build geometry fixed part partPositive floor
    ∀ stage (shared : PrimitiveData.FacePrimitiveBank differential stage domains) (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (surface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values),
      max (max stems.index holes.index) sewing.index ≤ stage →
      let readback := AreaReadback.build geometry.word surface.sewn.values
      let loop := current.edges.indexedEdges current.vertices
        (included.resplit (bank.rows.get branch).reference.walk (FramedBranchCellBank.baseMember base.bank)) sheet
      Data.Gaussian.Norm.Basic.normSq ((readback.raw - readback.correction) -
        (RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values) loop +
          RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values) loop)) ≤ target := by
  intro part partPositive innerPositive stems holes geometry sewing stage shared readings surface later readback loop
  have branchBound := HoleRequests.included_branch_area_accurate bank included fixed branch sheet part partPositive
    stage shared readings
    ((Data.Nat.Order.le_max_left _ _).trans later)
  have sewn := sewing.accurate readings surface readback ((Data.Nat.Order.le_max_right _ _).trans later)
  let canonical := RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
    (current.edges.indexedEdges current.vertices (doubleWalk bank included branch) 0)
  let doubled := RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values) loop +
    RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values) loop
  have branchBoundOld : Data.Gaussian.Norm.Basic.normSq (doubled - canonical) ≤ part := by
    have h := branchBound
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    dsimp only [doubled, canonical, doubleWalk]
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have reversed : Data.Gaussian.Norm.Basic.normSq (canonical - doubled) ≤ part := by
    rw [show canonical - doubled = -(doubled - canonical) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact branchBoundOld
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via
      (readback.raw - readback.correction) canonical doubled).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct sewn reversed) (by decide))
  exact estimate.trans_eq ((by ring1 : 2 * (part + part) = target / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
