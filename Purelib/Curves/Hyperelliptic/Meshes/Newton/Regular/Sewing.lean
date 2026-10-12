module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Branches.NewtonCutPrimitiveArea

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewnPathArea
import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Branches.NewtonCutPrimitiveArea

open Purelib.Topology.Mesh

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPathArea

open Purelib.Topology.Surface.Sewing.SewnPathArea.PathSources.Sample

open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

@[expose] public section

/-! Requested comparisons from both original regular-cell cut boundaries
to their canonical polygons, sharing contact preparations and numerical data. -/

open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance (BoundaryWords)
open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces (CutSourceWord)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (ContactBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting (Shape shape)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests (SourceChartAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (paired_sources_nonloop)
open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests (PathAreaRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {face : RegularFace original}
  {lifted : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank lifted.frames
    grid.faces.regulars} {differential : Differential genus}

set_option genInjectivity false in
/-- Both sheet requests consume the same retained contact preparations. -/
structure SewingData (domains : DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars) (differential :
  Differentials.Basic.Differential genus) where
  /-- The retained contact bank for the actual cut-patch assembly. -/ contacts : SewnPrimitiveContacts.ContactBank
    lifted.cutPolygon.patch.assembly
  /-- The primitive contact preparations on the original face domains. -/ covered : ContactBanks.ContactPreparations
    contacts.entries differential domains
  /-- The cached finite shape of the cut-patch assembly. -/ profile : SewnPrimitiveAccounting.Shape
  /-- The cached profile is exactly the shape of the retained assembly. -/ profile_eq : profile =
    SewnPrimitiveAccounting.shape lifted.cutPolygon.patch.assembly

constructive_injectivity SewingData

/-- Cache the actual cut-patch contacts, their face-domain preparations and the original assembly profile. -/
def SewingData.build (domains : DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars) (differential :
  Differentials.Basic.Differential genus) :
    SewingData domains differential :=
  let contacts := ContactBank.build lifted.cutPolygon.patch.assembly
  ⟨contacts, ContactPreparations.ofAssembly contacts differential domains, SewnPrimitiveAccounting.shape
    lifted.cutPolygon.patch.assembly, rfl⟩

set_option genInjectivity false in
/-- The paid sewing and source-chart requests for one regular-cell boundary sheet.

The retained cut word determines the count and magnitude caches, and both requests share the original contact
preparations and face magnitude bank. -/
structure SheetRequest (words : CutBalance.BoundaryWords face lifted) (sheet : Fin 2)
    (word : CutSourceWord lifted.cutPolygon.patch.cut (words.paired.sources sheet))
    (sewing : SewingData domains differential) (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    (error : Fraction.Rational) (floor : Nat) where
  /-- The cached number of actual cut-word edges. -/ count : Nat
  /-- The count is exactly the retained cut-word edge length. -/ count_eq : count = word.edges.length
  /-- The cached source squared-norm allowance. -/ magnitude : Fraction.Rational
  /-- The magnitude is the retained count times four times the original face bound. -/ magnitude_eq : magnitude = (count
    : Fraction.Rational) * (4 * fixed.bound)
  /-- The finite path-area request paying one quarter of the total error. -/ budget :
    SewnPathAreaRequests.PathAreaRequest lifted.cutPolygon.patch.assembly count magnitude (error / 4)
  /-- The contact request at the shared sewing tolerance and original floor. -/ contact : ContactPreparations.Request
    sewing.covered budget.path.tolerance (max floor fixed.index)
  /-- The source-chart request for the actual sheet source occurrences. -/ chart : SourceChartAreaRequest fixed
    (words.paired.sources sheet) (error / 4)
  /-- The cached common contact and chart threshold. -/ index : Nat
  /-- The stage is exactly the maximum of both retained request thresholds. -/ index_eq : index = max contact.index
    chart.index

constructive_injectivity SheetRequest

namespace SheetRequest

variable {words : BoundaryWords face lifted} {sheet : Fin
  2}
  {word : CutSourceWord lifted.cutPolygon.patch.cut (words.paired.sources sheet)}
  {sewing : SewingData domains differential} {fixed :
    FaceMagnitudeBank domains differential}
  {error : Rational} {floor : Nat}

/-- Prepare the shared contact and source-chart comparisons for a positive regular-sheet error budget. -/
def build (words : CutBalance.BoundaryWords face lifted) (sheet : Fin 2)
    (word : CutSourceWord lifted.cutPolygon.patch.cut (words.paired.sources sheet))
    (sewing : SewingData domains differential) (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) : SheetRequest words sheet word sewing fixed error
      floor :=
  let count := word.edges.length
  let magnitude := (count : Fraction.Rational) * (4 * fixed.bound)
  have nonnegative : 0 ≤ magnitude := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      fixed.nonnegative)
  have quarterPositive : 0 < error / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let budget := PathAreaRequest.ofProfile sewing.profile sewing.profile_eq count magnitude (error / 4) nonnegative
    quarterPositive
  let contact := ContactPreparations.Request.build sewing.covered budget.path.tolerance budget.path.tolerance_positive
    (max floor fixed.index)
  let chart := SourceChartAreaRequest.build fixed (words.paired.sources sheet)
    (SignedSourceChartRequests.paired_sources_nonloop words.paired sheet)
    (error / 4) quarterPositive
  ⟨count, rfl, magnitude, rfl, budget, contact, chart, max contact.index chart.index, rfl⟩

/-- A uniformly bounded finite Gaussian list has squared-norm sum at most its length times the bound. -/
private theorem normSum_le (values : List Data.Gaussian.Basic.Canonical) {bound : Fraction.Rational}
    (bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq value ≤ bound) :
      Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum values ≤ (values.length : Fraction.Rational) * bound := by
  induction values with
  | nil => change (0 : Fraction.Rational) ≤ 0 * bound; rw [Fraction.Field.zero_mul_direct]
  | cons value tail ih =>
      have countEq : bound + (tail.length : Fraction.Rational) * bound =
          ((value :: tail).length : Fraction.Rational) * bound := by
        rw [List.length_cons, Nat.cast_succ]
        ring1
      rw [Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum,
        ← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (add_le_add (bounded value List.mem_cons_self)
        (ih (fun other member => bounded other (List.mem_cons_of_mem _ member)))).trans_eq countEq

/-- The actual cut-source increments satisfy the retained magnitude budget at every paid face stage. -/
private theorem source_magnitude (request : SheetRequest words sheet word sewing fixed error floor)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (later : fixed.index ≤ stage) :
    Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (word.sources.sources.map (fun source => source.increment
      readings.values)) ≤ request.magnitude := by
  let retainedMagnitude := PuncturedGrid.Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh lifted.mesh) fixed later readings
  rw [word.sources_eq]
  have bound := normSum_le ((words.paired.sources sheet).map (fun source => source.increment readings.values)) (by
    intro value member
    obtain ⟨source, _, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact retainedMagnitude.source_bounded source)
  change Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum ((words.paired.sources sheet).map (fun source =>
    source.increment readings.values)) ≤
    (((words.paired.sources sheet).map (fun source => source.increment readings.values)).length : Fraction.Rational) *
      (4 * fixed.bound) at bound
  rw [List.Map.length_map, ← word.length_eq, ← request.count_eq, ← request.magnitude_eq] at bound
  exact bound

/-- The supplied cut readback and canonical polygon use the same sheet and numerical primitive bank; all occurrence
offsets remain subtracted. -/
theorem accurate (request : SheetRequest words sheet word sewing fixed error floor)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values)
    (readback : CutSourceWord.AreaReadback word surface.sewn.values) (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq ((readback.raw - readback.correction) - RetracingWords.wordArea
      (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      (lifted.edges.indexedEdges lifted.vertices
        (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet)) ≤ error := by
  have contactLater := (Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  have chartLater := (Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have fixedLater := (Nat.Order.le_max_right _ _).trans (request.contact.floor_le.trans contactLater)
  let path := CachedSample.pathSample surface word.sources
  let area := AreaSample.build path
  have locallyAccurate := request.contact.localAccuracy_of_coverage
    (fun _ member => sewing.contacts.entries_eq.symm ▸ member) le_rfl contactLater readings surface.sewn.readings
  have small := request.budget.path.cached_accurate surface locallyAccurate word.sources request.count_eq.symm.le
  have sewn := request.budget.accurate area request.count_eq.symm (request.source_magnitude readings fixedLater) small
  let sample := SingleReadings.ofReadings (owner := SourceChartComparison.ownerFromMesh lifted.mesh) readings
  let chartSources := SourceObservations.realize sample.values (words.paired.sources sheet)
  let chartComparison := request.chart.realize sample chartSources chartLater
  have charts := chartComparison.pay
  rw [chartComparison.residual_readback] at charts
  rw [PairedWalk.sources_project words.paired] at charts
  have source : area.source.area = IncrementArea.pathArea
      ((words.paired.sources sheet).map (fun source => source.increment readings.values)) := by
    rw [area.source_path, word.sources_eq]
  have actual : readback.raw - readback.correction = area.sewn.area :=
    readback.corrected.trans (area.sewn.area_eq.trans (congrArg IncrementArea.pathArea
      (PathSources.Sample.areaPairs_left path))).symm
  rw [actual]
  have oldCharts : Data.Gaussian.Norm.Basic.normSq
      (area.source.area - RetracingWords.wordArea
        (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
        (lifted.edges.indexedEdges lifted.vertices
          (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet)) ≤ error / 4 := by
    have h := source ▸ charts
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via area.sewn.area area.source.area
      (RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
        (lifted.edges.indexedEdges lifted.vertices
        (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet))).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct sewn.le oldCharts) (by decide))
  exact estimate.trans_eq ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end SheetRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.Sewing
