module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Readings.PrimitiveAreaBounds

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPairedPathRequests
public import Purelib.Integration.Path.PairedOccurrenceArea
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
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
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
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
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests

public section

/-! Two actual differentials on the original doubled branch-cell boundary.
The paired receipt retains the offsets of every cut-word occurrence. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests (PairedChartAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (paired_sources_nonloop)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing (IncludedHoleSewing)
open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests (PathAreaRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open _root_.Purelib.Integration.Path (PairedOccurrenceArea)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {current : LiftedPuncturedGrid next} {bank :
    BasedBranchBank lifted}
  {included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid}
  {branch : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {domains :
    FaceDomainBank current.frames
    next.faces.regulars}
  {leftDifferential rightDifferential : Differential genus}

set_option genInjectivity false in
/-- A paid paired-area request on the actual doubled original-cell cut word.

Both differentials share the retained occurrence count, contact bank and path budget, with every cut offset preserved.
-/
structure PairedRequest (geometry : IncludedHoleSewing bank included branch domains leftDifferential)
    (leftFixed : FaceMagnitudeBank domains leftDifferential) (rightFixed : FaceMagnitudeBank domains rightDifferential)
    (error : Rational) (floor : Nat) where
  /-- The second differential preparations on the same retained contact entries. -/ rightCovered :
    ContactBanks.ContactPreparations geometry.contacts.entries rightDifferential domains
  /-- The cached number of actual cut-word occurrences. -/ count : Nat
  /-- The occurrence count is the retained cut word's exact edge count. -/ count_eq : count = geometry.word.edges.length
  /-- The common squared-norm ceiling for both differential source increments. -/ magnitude : Rational
  /-- The magnitude is the maximum of the two retained edge-magnitude bounds. -/ magnitude_eq : magnitude = max (4 *
    leftFixed.bound) (4 * rightFixed.bound)
  /-- The actual sewn path-area budget at one quarter of the target. -/ budget : SewnPathAreaRequests.PathAreaRequest
    current.cutPolygon.patch.assembly count magnitude (error / 4)
  /-- The first differential contact request above the common floor and both magnitude stages. -/ leftContact :
    ContactPreparations.Request geometry.covered budget.path.tolerance
    (max floor (max leftFixed.index rightFixed.index))
  /-- The second differential contact request on the same contact bank and common floor. -/ rightContact :
    ContactPreparations.Request rightCovered budget.path.tolerance
    (max floor (max leftFixed.index rightFixed.index))
  /-- The actual paired source-to-chart comparison at one quarter of the target. -/ chart : PairedChartAreaRequest
    leftFixed rightFixed (geometry.paired.sources 0) (error / 4)

constructive_injectivity PairedRequest

namespace PairedRequest

variable {geometry : IncludedHoleSewing bank included branch domains leftDifferential}
  {leftFixed : FaceMagnitudeBank domains leftDifferential} {rightFixed : FaceMagnitudeBank domains rightDifferential}
  {error : Rational} {floor : Nat}

/-- Prepare both differential contacts, the shared sewn path budget and the paired source-to-chart request on the
retained doubled word. -/
@[expose] def build (geometry : IncludedHoleSewing bank included branch domains leftDifferential)
    (leftFixed : FaceMagnitudeBank domains leftDifferential) (rightFixed : FaceMagnitudeBank domains rightDifferential)
    (error : Rational) (positive : 0 < error) (floor : Nat) : PairedRequest geometry leftFixed rightFixed error floor :=
  let rightCovered := ContactPreparations.ofAssembly geometry.contacts rightDifferential domains
  let magnitude := max (4 * leftFixed.bound) (4 * rightFixed.bound)
  have nonnegative : 0 ≤ magnitude := (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    leftFixed.nonnegative).trans (Fraction.Order.Basic.le_max_left _ _)
  have partPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Rational) < 4)
  let budget := PathAreaRequest.ofProfile geometry.profile geometry.profile_eq geometry.word.edges.length magnitude
    (error / 4) nonnegative partPositive
  let leftContact := ContactPreparations.Request.build geometry.covered budget.path.tolerance
    budget.path.tolerance_positive
    (max floor (max leftFixed.index rightFixed.index))
  let rightContact := ContactPreparations.Request.build rightCovered budget.path.tolerance
    budget.path.tolerance_positive
    (max floor (max leftFixed.index rightFixed.index))
  ⟨rightCovered, geometry.word.edges.length, rfl, magnitude, rfl, budget, leftContact, rightContact,
    PairedChartAreaRequest.build leftFixed rightFixed (geometry.paired.sources 0)
      (SignedSourceChartRequests.paired_sources_nonloop geometry.paired 0) (error / 4) partPositive⟩

/-- The common maximum stage paying both contact banks and the paired chart request. -/
@[expose] def index (request : PairedRequest geometry leftFixed rightFixed error floor) : Nat :=
  max (max request.leftContact.index request.rightContact.index) request.chart.index

/-- The common paired request stage respects the supplied floor. -/
theorem floor_le (request : PairedRequest geometry leftFixed rightFixed error floor) : floor ≤ request.index :=
  (Nat.Order.le_max_left _ _).trans (request.leftContact.floor_le.trans ((Nat.Order.le_max_left _ _).trans
    (Nat.Order.le_max_left _ _)))

/-- The common stage pays the first retained contact request. -/
theorem left_contact_le (request : PairedRequest geometry leftFixed rightFixed error floor) :
  request.leftContact.index ≤ request.index :=
  (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _)

/-- The common stage pays the second retained contact request. -/
theorem right_contact_le (request : PairedRequest geometry leftFixed rightFixed error floor) :
  request.rightContact.index ≤ request.index :=
  (Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_left _ _)

/-- The common stage pays the retained paired chart comparison. -/
theorem chart_le (request : PairedRequest geometry leftFixed rightFixed error floor) : request.chart.index ≤
  request.index :=
  Nat.Order.le_max_right _ _

/-- The common stage pays the first original magnitude bank's distinct floor. -/
theorem left_magnitude_le (request : PairedRequest geometry leftFixed rightFixed error floor) : leftFixed.index ≤
  request.index :=
  (Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _ _).trans
    (request.leftContact.floor_le.trans request.left_contact_le))

/-- The common stage pays the second original magnitude bank's distinct floor. -/
theorem right_magnitude_le (request : PairedRequest geometry leftFixed rightFixed error floor) : rightFixed.index ≤
  request.index :=
  (Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _ _).trans
    (request.leftContact.floor_le.trans request.left_contact_le))

/-- The full paired area of the doubled original-cell boundary is read from the same sewn cut word, after subtracting
its retained occurrence offsets. -/
theorem accurate (request : PairedRequest geometry leftFixed rightFixed error floor)
    (readings : SourceChartComparison.PairedReadings
      (owner := SourceChartComparison.ownerFromMesh current.mesh) domains leftDifferential rightDifferential)
    (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.leftReadings.values)
    (rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.rightReadings.values)
    (readback : Integration.Path.PairedOccurrenceArea (fun vertex =>
      (⟨leftSurface.sewn.values vertex, rightSurface.sewn.values vertex⟩ : PrimitivePoint)) geometry.word.edges)
    (later : request.index ≤ readings.stage) :
    let walk := included.resplit (bank.rows.get branch).boundary ((base.bank.cell branch).anchor_mem (base.bank.cell_mem
      branch))
    Data.Gaussian.Norm.Basic.normSq ((readback.raw - readback.correction) -
      PairedIncrementArea.area ((current.edges.indexedEdges current.vertices (walk.append walk) 0).map (fun edge =>
        (⟨edgeValuation current.mesh readings.leftReadings.values edge,
          CanonicalEdgeValues.edgeValuation current.mesh readings.rightReadings.values edge⟩ : PrimitivePoint)))) ≤
            error := by
  intro walk
  have leftLater := request.left_contact_le.trans later
  have rightLater := request.right_contact_le.trans later
  let retainedLeftMagnitude := readings.leftMagnitude leftFixed (request.left_magnitude_le.trans later)
  let retainedRightMagnitude := readings.rightMagnitude rightFixed (request.right_magnitude_le.trans later)
  have leftAccurate := request.leftContact.localAccuracy_of_coverage
    (fun _ member => geometry.contacts.entries_eq.symm ▸ member) le_rfl leftLater readings.leftReadings
      leftSurface.sewn.readings
  have rightAccurate := request.rightContact.localAccuracy_of_coverage
    (fun _ member => geometry.contacts.entries_eq.symm ▸ member) le_rfl rightLater readings.rightReadings
      rightSurface.sewn.readings
  have bounded : ∀ source ∈ geometry.word.sources.sources,
      PrimitivePoint.Bounded (⟨source.increment readings.leftReadings.values, source.increment
        readings.rightReadings.values⟩ :
        PrimitivePoint) request.magnitude := by
    intro source _
    rw [request.magnitude_eq]
    have leftBound := (retainedLeftMagnitude.source_bounded source).trans
      (Fraction.Order.Basic.le_max_left (4 * leftFixed.bound) (4 * rightFixed.bound))
    have rightBound := (retainedRightMagnitude.source_bounded source).trans
      (Fraction.Order.Basic.le_max_right (4 * leftFixed.bound) (4 * rightFixed.bound))
    constructor
    · change Fraction.Order.Basic.LessEqual _ _ at leftBound ⊢
      rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact leftBound
    · change Fraction.Order.Basic.LessEqual _ _ at rightBound ⊢
      rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact rightBound
  have sewn := SewnPairedPathRequests.paired_cached_accurate request.budget leftSurface rightSurface leftAccurate
    rightAccurate
    geometry.word.sources request.count_eq.symm bounded
  rw [geometry.word.sources_eq] at sewn
  let chartsComparison := request.chart.realize .paired readings.leftReadings readings.rightReadings
    (request.chart_le.trans later)
  have charts := chartsComparison.pay
  rw [chartsComparison.residual_readback] at charts
  have mapRead : (geometry.paired.sources 0).map (fun source =>
      (⟨edgeValuation current.mesh readings.leftReadings.values (source.project current.mesh.triangulation.faces),
        CanonicalEdgeValues.edgeValuation current.mesh readings.rightReadings.values (source.project
          current.mesh.triangulation.faces)⟩ : PrimitivePoint)) =
      (current.edges.indexedEdges current.vertices (walk.append walk) 0).map (fun edge =>
        (⟨edgeValuation current.mesh readings.leftReadings.values edge,
          CanonicalEdgeValues.edgeValuation current.mesh readings.rightReadings.values edge⟩ : PrimitivePoint)) := by
    have projected : (geometry.paired.sources 0).map (fun source => source.project current.mesh.triangulation.faces) =
        current.edges.indexedEdges current.vertices (walk.append walk) 0 := geometry.paired.sources_project 0
    rw [← projected, List.Map.map_map]
    rfl
  change Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area
    ((geometry.paired.sources 0).map (fun source =>
      (⟨source.increment readings.leftReadings.values, source.increment readings.rightReadings.values⟩ :
        PrimitivePoint))) -
    PairedIncrementArea.area
      ((geometry.paired.sources 0).map (fun source =>
        (⟨edgeValuation current.mesh readings.leftReadings.values (source.project current.mesh.triangulation.faces),
          CanonicalEdgeValues.edgeValuation current.mesh readings.rightReadings.values
            (source.project current.mesh.triangulation.faces)⟩ : PrimitivePoint)))) ≤ error / 4 at charts
  rw [mapRead] at charts
  rw [readback.corrected]
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct sewn.le
      charts) (by decide : (0 : Rational) ≤ 2))
  exact estimate.trans_eq ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end PairedRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing
