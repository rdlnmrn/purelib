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

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedOccurrenceArea
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing
import Purelib.Topology.Surface.Sewing.SewnConjugatePathRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateChartAreaRequests
public import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
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
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnConjugatePathRequests

public section

/-! Conjugate branch-boundary areas reuse the existing doubled-word sewing
and chart request, with all occurrence offsets retained. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateHoleSewing

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing (PairedRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
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

namespace PairedRequest

variable {geometry : IncludedHoleSewing bank included branch domains leftDifferential}
  {leftFixed : FaceMagnitudeBank domains leftDifferential} {rightFixed : FaceMagnitudeBank domains rightDifferential}
  {error : Rational} {floor : Nat}
/-- The full paired area of the doubled original-cell boundary is read from the same sewn cut word, after subtracting
its retained occurrence offsets. -/
theorem conjugate_accurate (request : PairedRequest geometry leftFixed rightFixed error floor)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftReadings.values)
    (rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightReadings.values)
    (pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
    (readback : Integration.Path.PairedOccurrenceArea pair.values geometry.word.edges)
    (later : request.index ≤ stage) :
    let walk := included.resplit (bank.rows.get branch).boundary ((base.bank.cell branch).anchor_mem (base.bank.cell_mem
      branch))
    Data.Gaussian.Norm.Basic.normSq ((readback.raw - readback.correction) -
      PairedIncrementArea.area ((current.edges.indexedEdges current.vertices (walk.append walk) 0).map (fun edge =>
        (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values edge),
          CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ : PrimitivePoint)))) ≤ error := by
  intro walk
  have contactLater := (Nat.Order.le_max_left _ _).trans later
  have leftLater := (Nat.Order.le_max_left _ _).trans contactLater
  have rightLater := (Nat.Order.le_max_right _ _).trans contactLater
  have fixedLater := (Nat.Order.le_max_right _ _).trans (request.leftContact.floor_le.trans leftLater)
  let retainedLeftMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh current.mesh) leftFixed ((Nat.Order.le_max_left _ _).trans fixedLater)
      leftReadings
  let retainedRightMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh current.mesh) rightFixed ((Nat.Order.le_max_right _ _).trans
      fixedLater) rightReadings
  have leftAccurate := request.leftContact.localAccuracy_of_coverage
    (fun _ member => geometry.contacts.entries_eq.symm ▸ member) le_rfl leftLater leftReadings leftSurface.sewn.readings
  have rightAccurate := request.rightContact.localAccuracy_of_coverage
    (fun _ member => geometry.contacts.entries_eq.symm ▸ member) le_rfl rightLater rightReadings
      rightSurface.sewn.readings
  have bounded : ∀ source ∈ geometry.word.sources.sources,
      PrimitivePoint.Bounded
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
      rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact leftBound
    · change Fraction.Order.Basic.LessEqual _ _ at rightBound ⊢
      rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact rightBound
  have sewn := PathAreaRequest.conjugate_cached_accurate request.budget leftSurface rightSurface leftAccurate
    rightAccurate
    geometry.word.sources request.count_eq.symm bounded
  rw [geometry.word.sources_eq] at sewn
  let chartsComparison := request.chart.realize .conjugate leftReadings rightReadings ((Nat.Order.le_max_right _
    _).trans later)
  have charts := chartsComparison.pay
  rw [chartsComparison.residual_readback] at charts
  have mapRead : (geometry.paired.sources 0).map (fun source =>
      (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values
        (source.project current.mesh.triangulation.faces)),
        CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values (source.project
          current.mesh.triangulation.faces)⟩ : PrimitivePoint)) =
      (current.edges.indexedEdges current.vertices (walk.append walk) 0).map (fun edge =>
        (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values edge),
          CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ : PrimitivePoint)) := by
    have projected : (geometry.paired.sources 0).map (fun source => source.project current.mesh.triangulation.faces) =
        current.edges.indexedEdges current.vertices (walk.append walk) 0 := geometry.paired.sources_project 0
    rw [← projected, List.Map.map_map]
    rfl
  change Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area
    ((geometry.paired.sources 0).map (fun source =>
      (⟨Data.Gaussian.Basic.conj (source.increment leftReadings.values), source.increment rightReadings.values⟩
        : PrimitivePoint))) -
    PairedIncrementArea.area
      ((geometry.paired.sources 0).map (fun source =>
        (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values
          (source.project current.mesh.triangulation.faces)),
          CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values
            (source.project current.mesh.triangulation.faces)⟩ : PrimitivePoint)))) ≤ error / 4 at charts
  rw [mapRead] at charts
  rw [readback.corrected]
  have increments : geometry.word.edges.map (fun edge => (pair.values edge.finish).sub (pair.values edge.start)) =
      geometry.word.edges.map (fun edge =>
        (⟨Data.Gaussian.Basic.conj (leftSurface.sewn.values edge.finish - leftSurface.sewn.values edge.start),
          rightSurface.sewn.values edge.finish - rightSurface.sewn.values edge.start⟩ : PrimitivePoint)) := by
    apply Map.map_congr_left
    intro edge _
    exact congrArg₂ PrimitivePoint.mk (pair.increment_left edge) (pair.increment_right edge)
  rw [increments]
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct sewn.le
      charts) (by decide : (0 : Rational) ≤ 2))
  exact estimate.trans_eq ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end PairedRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateHoleSewing
