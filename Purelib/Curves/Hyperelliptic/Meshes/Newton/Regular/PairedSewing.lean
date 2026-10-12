module
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Readings.PrimitiveAreaBounds

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.Sewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPairedPathRequests
public import Purelib.Integration.Path.PairedOccurrenceArea
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
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
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

/-! The original regular-cell cut word and its canonical resplit polygon
are compared for two differentials on the same sewn surfaces. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedSewing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate

open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)

open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces (CutSourceWord)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.Sewing (SewingData)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests (PairedChartAreaRequest)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {face : RegularFace original}
  {lifted : LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- A paired sewing and chart request for one original regular-cell cut word.

Both differential contact banks and the original source occurrences are retained with a common magnitude bound and paid
local target. -/
structure PairedSheetRequest (words : Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted) (sheet :
  Fin 2)
    (word : CutSourceWord lifted.cutPolygon.patch.cut (words.paired.sources sheet))
    (leftFixed : FaceMagnitudeBank domains leftDifferential) (rightFixed : FaceMagnitudeBank domains rightDifferential)
    (error : Rational) (floor : Nat) where
  /-- The original left-differential sewing data. -/ leftSewing : SewingData domains leftDifferential
  /-- The original right-differential sewing data. -/ rightSewing : SewingData domains rightDifferential
  /-- The cached original cut-word edge count. -/ count : Nat
  /-- The count equals the length of the actual original cut word. -/ count_eq : count = word.edges.length
  /-- The retained common bound for both original source increments. -/ magnitude : Rational
  /-- The magnitude is the maximum of the two original fourfold bank bounds. -/ magnitude_eq : magnitude = max (4 *
    leftFixed.bound) (4 * rightFixed.bound)
  /-- The paid original sewn-path area request. -/ budget : Topology.Surface.Sewing.SewnPathAreaRequests.PathAreaRequest
    lifted.cutPolygon.patch.assembly count magnitude (error / 4)
  /-- The original left contact request above both magnitude stages and the supplied floor. -/ leftContact :
    Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request leftSewing.covered budget.path.tolerance
    (max floor (max leftFixed.index rightFixed.index))
  /-- The original right contact request above both magnitude stages and the supplied floor. -/ rightContact :
    Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request rightSewing.covered
    budget.path.tolerance
    (max floor (max leftFixed.index rightFixed.index))
  /-- The retained paired chart comparison on the original signed source occurrences. -/ chart : PairedChartAreaRequest
    leftFixed rightFixed (words.paired.sources sheet) (error / 4)

constructive_injectivity PairedSheetRequest

namespace PairedSheetRequest

variable {words : Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted} {sheet : Fin 2}
  {word : CutSourceWord lifted.cutPolygon.patch.cut (words.paired.sources sheet)}
  {leftFixed : FaceMagnitudeBank domains leftDifferential} {rightFixed : FaceMagnitudeBank domains rightDifferential}
  {error : Rational} {floor : Nat}

/-- Prepare both original sewing contact banks and their paired chart comparison at the paid common target. -/
@[expose] def build (words : Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted) (sheet : Fin 2)
    (word : CutSourceWord lifted.cutPolygon.patch.cut (words.paired.sources sheet))
    (leftFixed : FaceMagnitudeBank domains leftDifferential) (rightFixed : FaceMagnitudeBank domains rightDifferential)
    (error : Rational) (positive : 0 < error) (floor : Nat) :
    PairedSheetRequest words sheet word leftFixed rightFixed error floor :=
  let leftSewing := SewingData.build domains leftDifferential
  let rightSewing := SewingData.build domains rightDifferential
  let magnitude := max (4 * leftFixed.bound) (4 * rightFixed.bound)
  have nonnegative : 0 ≤ magnitude := (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    leftFixed.nonnegative).trans (Fraction.Order.Basic.le_max_left _ _)
  have partPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Rational) < 4)
  let budget := Topology.Surface.Sewing.SewnPathAreaRequests.PathAreaRequest.ofProfile leftSewing.profile
    leftSewing.profile_eq word.edges.length magnitude
    (error / 4) nonnegative partPositive
  let leftContact := Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request.build
    leftSewing.covered budget.path.tolerance budget.path.tolerance_positive
    (max floor (max leftFixed.index rightFixed.index))
  let rightContact := Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request.build
    rightSewing.covered budget.path.tolerance budget.path.tolerance_positive
    (max floor (max leftFixed.index rightFixed.index))
  ⟨leftSewing, rightSewing, word.edges.length, rfl, magnitude, rfl, budget, leftContact, rightContact,
    PairedChartAreaRequest.build leftFixed rightFixed (words.paired.sources sheet)
      (Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests.paired_sources_nonloop words.paired sheet) (error /
        4) partPositive⟩

/-- The maximum sufficient stage of the two retained contact requests and chart comparison. -/
@[expose] def index (request : PairedSheetRequest words sheet word leftFixed rightFixed error floor) : Nat :=
  max (max request.leftContact.index request.rightContact.index) request.chart.index

/-- The common sufficient stage respects the original supplied floor. -/
theorem floor_le (request : PairedSheetRequest words sheet word leftFixed rightFixed error floor) : floor ≤
  request.index :=
  (Nat.Order.le_max_left _ _).trans (request.leftContact.floor_le.trans ((Nat.Order.le_max_left _ _).trans
    (Nat.Order.le_max_left _ _)))

/-- The common stage pays the first retained contact request. -/
theorem left_contact_le (request : PairedSheetRequest words sheet word leftFixed rightFixed error floor) :
  request.leftContact.index ≤ request.index :=
  (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _)

/-- The common stage pays the second retained contact request. -/
theorem right_contact_le (request : PairedSheetRequest words sheet word leftFixed rightFixed error floor) :
  request.rightContact.index ≤ request.index :=
  (Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_left _ _)

/-- The common stage pays the retained paired chart comparison. -/
theorem chart_le (request : PairedSheetRequest words sheet word leftFixed rightFixed error floor) :
  request.chart.index ≤ request.index :=
  Nat.Order.le_max_right _ _

/-- The common stage pays the first original magnitude bank's distinct floor. -/
theorem left_magnitude_le (request : PairedSheetRequest words sheet word leftFixed rightFixed error floor) :
  leftFixed.index ≤ request.index :=
  (Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _ _).trans
    (request.leftContact.floor_le.trans request.left_contact_le))

/-- The common stage pays the second original magnitude bank's distinct floor. -/
theorem right_magnitude_le (request : PairedSheetRequest words sheet word leftFixed rightFixed error floor) :
  rightFixed.index ≤ request.index :=
  (Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _ _).trans
    (request.leftContact.floor_le.trans request.left_contact_le))

/-- The paired sewn word retains every intermediate increment. Its comparison
to the canonical polygon pays both contact banks and both chart banks. -/
theorem accurate (request : PairedSheetRequest words sheet word leftFixed rightFixed error floor)
    (readings : SourceChartComparison.PairedReadings
      (owner := SourceChartComparison.ownerFromMesh lifted.mesh) domains
        leftDifferential rightDifferential)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      readings.leftReadings.values)
    (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      readings.rightReadings.values) (later : request.index ≤ readings.stage) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (word.edges.map (fun edge =>
      (⟨leftSurface.sewn.values edge.finish - leftSurface.sewn.values edge.start,
        rightSurface.sewn.values edge.finish - rightSurface.sewn.values edge.start⟩ : PrimitivePoint))) -
      Path.PairedIncrementArea.area ((lifted.edges.indexedEdges lifted.vertices
        (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet).map (fun edge =>
          (⟨edgeValuation lifted.mesh readings.leftReadings.values edge,
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
              readings.rightReadings.values edge⟩
              : PrimitivePoint)))) ≤ error := open Purelib.Riemann in by
  have leftLater := request.left_contact_le.trans later
  have rightLater := request.right_contact_le.trans later
  let retainedLeftMagnitude := readings.leftMagnitude leftFixed (request.left_magnitude_le.trans later)
  let retainedRightMagnitude := readings.rightMagnitude rightFixed (request.right_magnitude_le.trans later)
  have leftAccurate := request.leftContact.localAccuracy_of_coverage
    (fun _ member => request.leftSewing.contacts.entries_eq.symm ▸ member) le_rfl leftLater readings.leftReadings
      leftSurface.sewn.readings
  have rightAccurate := request.rightContact.localAccuracy_of_coverage
    (fun _ member => request.rightSewing.contacts.entries_eq.symm ▸ member) le_rfl rightLater readings.rightReadings
      rightSurface.sewn.readings
  have bounded : ∀ source ∈ word.sources.sources,
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (⟨source.increment readings.leftReadings.values,
        source.increment
        readings.rightReadings.values⟩ : PrimitivePoint) request.magnitude := by
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
  have sewn := Topology.Surface.Sewing.SewnPairedPathRequests.paired_cached_accurate request.budget leftSurface
    rightSurface leftAccurate rightAccurate
    word.sources request.count_eq.symm bounded
  rw [word.sources_eq] at sewn
  let chartsComparison := request.chart.realize .paired readings.leftReadings readings.rightReadings
    (request.chart_le.trans later)
  have charts := chartsComparison.pay
  rw [chartsComparison.residual_readback] at charts
  have mapRead : (words.paired.sources sheet).map (fun source =>
      (⟨edgeValuation lifted.mesh readings.leftReadings.values (source.project lifted.mesh.triangulation.faces),
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.rightReadings.values
          (source.project lifted.mesh.triangulation.faces)⟩ : PrimitivePoint)) =
      (lifted.edges.indexedEdges lifted.vertices
        (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet).map (fun edge =>
          (⟨edgeValuation lifted.mesh readings.leftReadings.values edge,
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
              readings.rightReadings.values edge⟩
              : PrimitivePoint)) := by
    rw [← words.paired.sources_project sheet, List.Map.map_map]
    rfl
  change Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
    ((words.paired.sources sheet).map (fun source =>
      (⟨source.increment readings.leftReadings.values, source.increment readings.rightReadings.values⟩ :
        PrimitivePoint))) -
    Path.PairedIncrementArea.area
      ((words.paired.sources sheet).map (fun source =>
        (⟨edgeValuation lifted.mesh readings.leftReadings.values (source.project lifted.mesh.triangulation.faces),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.rightReadings.values
            (source.project lifted.mesh.triangulation.faces)⟩ : PrimitivePoint)))) ≤ error / 4 at charts
  rw [mapRead] at charts
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct sewn.le
      charts) (by decide : (0 : Rational) ≤ 2))
  exact estimate.trans_eq ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- Offset corrections belong to the actual paired cut-word receipt and
remain subtracted when the canonical polygon comparison is consumed. -/
theorem corrected_accurate (request : PairedSheetRequest words sheet word leftFixed rightFixed error floor)
    (readings : SourceChartComparison.PairedReadings
      (owner := SourceChartComparison.ownerFromMesh lifted.mesh) domains
        leftDifferential rightDifferential)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      readings.leftReadings.values)
    (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      readings.rightReadings.values) (later : request.index ≤ readings.stage)
    (sample : Integration.Path.PairedOccurrenceArea (fun vertex =>
      (⟨leftSurface.sewn.values vertex, rightSurface.sewn.values vertex⟩ : PrimitivePoint)) word.edges) :
    Data.Gaussian.Norm.Basic.normSq ((sample.raw - sample.correction) - Path.PairedIncrementArea.area
      ((lifted.edges.indexedEdges lifted.vertices
      (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet).map (fun edge =>
        (⟨edgeValuation lifted.mesh readings.leftReadings.values edge,
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
            readings.rightReadings.values edge⟩ :
            PrimitivePoint)))) ≤ error := by
  rw [sample.corrected]
  exact request.accurate readings leftSurface rightSurface later

end PairedSheetRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedSewing
