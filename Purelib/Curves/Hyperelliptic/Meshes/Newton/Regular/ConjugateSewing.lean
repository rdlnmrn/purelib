module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Readings.PrimitiveAreaBounds

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedOccurrenceArea
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedSewing
import Purelib.Topology.Surface.Sewing.SewnConjugatePathRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateChartAreaRequests
public import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib

public section

/-! Original regular cut words retain their conjugate area and offset
corrections at the existing geometry-first sewing and chart thresholds. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateSewing

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate

open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)

open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces (CutSourceWord)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedSewing (PairedSheetRequest)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {face : RegularFace original}
  {lifted : LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

namespace PairedSheetRequest

variable {words : Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted} {sheet : Fin 2}
  {word : CutSourceWord lifted.cutPolygon.patch.cut (words.paired.sources sheet)}
  {leftFixed : FaceMagnitudeBank domains leftDifferential} {rightFixed : FaceMagnitudeBank domains rightDifferential}
  {error : Rational} {floor : Nat}
/-- The paired sewn word retains every intermediate increment. Its comparison
to the canonical polygon pays both contact banks and both chart banks. -/
theorem conjugate_accurate (request : PairedSheetRequest words sheet word leftFixed rightFixed error floor)
    {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
      stage domains}
    {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential stage
      domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank lifted.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      lifted.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      leftReadings.values)
    (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      rightReadings.values) (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (word.edges.map (fun edge =>
      (⟨Data.Gaussian.Basic.conj (leftSurface.sewn.values edge.finish - leftSurface.sewn.values edge.start),
        rightSurface.sewn.values edge.finish - rightSurface.sewn.values edge.start⟩ : PrimitivePoint))) -
      Path.PairedIncrementArea.area ((lifted.edges.indexedEdges lifted.vertices
        (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet).map (fun edge =>
          (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
            lifted.mesh leftReadings.values edge),
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh rightReadings.values edge⟩
              : PrimitivePoint)))) ≤ error := open Purelib.Riemann in by
  have contactLater := (Nat.Order.le_max_left _ _).trans later
  have leftLater := (Nat.Order.le_max_left _ _).trans contactLater
  have rightLater := (Nat.Order.le_max_right _ _).trans contactLater
  have fixedLater := (Nat.Order.le_max_right _ _).trans (request.leftContact.floor_le.trans leftLater)
  let retainedLeftMagnitude := PuncturedGrid.Readings.EdgeMagnitude.ofBank
    (owner := Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.ownerFromMesh lifted.mesh) leftFixed
      ((Nat.Order.le_max_left _ _).trans fixedLater) leftReadings
  let retainedRightMagnitude := PuncturedGrid.Readings.EdgeMagnitude.ofBank
    (owner := Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.ownerFromMesh lifted.mesh) rightFixed
      ((Nat.Order.le_max_right _ _).trans fixedLater) rightReadings
  have leftAccurate := request.leftContact.localAccuracy_of_coverage
    (fun _ member => request.leftSewing.contacts.entries_eq.symm ▸ member) le_rfl leftLater leftReadings
      leftSurface.sewn.readings
  have rightAccurate := request.rightContact.localAccuracy_of_coverage
    (fun _ member => request.rightSewing.contacts.entries_eq.symm ▸ member) le_rfl rightLater rightReadings
      rightSurface.sewn.readings
  have bounded : ∀ source ∈ word.sources.sources,
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        (⟨source.increment leftReadings.values, source.increment rightReadings.values⟩ : PrimitivePoint)
          request.magnitude := by
    intro source _
    rw [request.magnitude_eq]
    have leftBound := (retainedLeftMagnitude.source_bounded source).trans
      (Fraction.Order.Basic.le_max_left (4 * leftFixed.bound) (4 * rightFixed.bound))
    have rightBound := (retainedRightMagnitude.source_bounded source).trans
      (Fraction.Order.Basic.le_max_right (4 * leftFixed.bound) (4 * rightFixed.bound))
    constructor
    · change Fraction.Order.Basic.LessEqual _ _ at leftBound ⊢
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      exact leftBound
    · change Fraction.Order.Basic.LessEqual _ _ at rightBound ⊢
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      exact rightBound
  have sewn := Topology.Surface.Sewing.SewnConjugatePathRequests.PathAreaRequest.conjugate_cached_accurate
    request.budget leftSurface rightSurface leftAccurate rightAccurate
    word.sources request.count_eq.symm bounded
  rw [word.sources_eq] at sewn
  let chartsComparison := request.chart.realize .conjugate leftReadings rightReadings ((Nat.Order.le_max_right _
    _).trans later)
  have charts := chartsComparison.pay
  rw [chartsComparison.residual_readback] at charts
  have mapRead : (words.paired.sources sheet).map (fun source =>
      (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
        leftReadings.values (source.project lifted.mesh.triangulation.faces)),
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh rightReadings.values
          (source.project lifted.mesh.triangulation.faces)⟩ : PrimitivePoint)) =
      (lifted.edges.indexedEdges lifted.vertices
        (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet).map (fun edge =>
          (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
            lifted.mesh leftReadings.values edge),
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh rightReadings.values edge⟩
              : PrimitivePoint)) := by
    rw [← words.paired.sources_project sheet, List.Map.map_map]
    rfl
  change Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
    ((words.paired.sources sheet).map (fun source =>
      (⟨Data.Gaussian.Basic.conj (source.increment leftReadings.values), source.increment rightReadings.values⟩ :
        PrimitivePoint))) -
    Path.PairedIncrementArea.area
      ((words.paired.sources sheet).map (fun source =>
        (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
          leftReadings.values (source.project lifted.mesh.triangulation.faces)),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh rightReadings.values
            (source.project lifted.mesh.triangulation.faces)⟩ : PrimitivePoint)))) ≤ error / 4 at charts
  rw [mapRead] at charts
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct sewn.le
      charts) (by decide : (0 : Rational) ≤ 2))
  exact estimate.trans_eq ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- The actual centered conjugate receipt retains all offset corrections
when it is compared to the original canonical polygon. -/
theorem conjugate_corrected_accurate (request : PairedSheetRequest words sheet word leftFixed rightFixed error floor)
    {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
      stage domains}
    {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential stage
      domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank lifted.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      lifted.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      leftReadings.values)
    (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      rightReadings.values) (later : request.index ≤ stage)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
    (sample : Integration.Path.PairedOccurrenceArea pair.values word.edges) :
    Data.Gaussian.Norm.Basic.normSq ((sample.raw - sample.correction) - Path.PairedIncrementArea.area
      ((lifted.edges.indexedEdges lifted.vertices
      (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet).map (fun edge =>
        (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
          leftReadings.values edge),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh rightReadings.values edge⟩ :
            PrimitivePoint)))) ≤ error := by
  rw [sample.corrected]
  have increments : word.edges.map (fun edge => (pair.values edge.finish).sub (pair.values edge.start)) =
      word.edges.map (fun edge =>
        (⟨Data.Gaussian.Basic.conj (leftSurface.sewn.values edge.finish - leftSurface.sewn.values edge.start),
          rightSurface.sewn.values edge.finish - rightSurface.sewn.values edge.start⟩ : PrimitivePoint)) := by
    apply Data.List.Map.map_congr_left
    intro edge _
    exact congrArg₂ PrimitivePoint.mk (pair.increment_left edge) (pair.increment_right edge)
  rw [increments]
  exact conjugate_accurate request leftReadings rightReadings leftSurface rightSurface later

end PairedSheetRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateSewing
