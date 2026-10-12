module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearAreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! Opposite-sheet paired polygon comparison for the actual edge valuation,
including both source-chart errors on the retained walk. -/
section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests (PairedChartAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (paired_sources_nonloop)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearAreaRequests (BilinearAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh : LiftedMesh vertices edges
    base.faces}
  {domains : FaceDomainBank frames
    base.faces.regulars}
  {leftDifferential rightDifferential : Differential genus}
  {start finish : Canonical} {walk : Purelib.Polynomial.Geometry.Grid.Walks.Walk
    base.bank.grid start finish}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests

set_option genInjectivity false in
/-- A paid opposite-sheet polygon comparison on the original paired walk and two differential magnitude references.

The opposite-source and two source/chart requests share the same retained occurrences, each using one tenth of the
target. -/
structure PolygonRequest (leftFixed : FaceMagnitudeBank domains leftDifferential)
    (rightFixed : FaceMagnitudeBank domains rightDifferential) (paired : WalkOccurrences.PairedWalk mesh walk)
    (first last : Fin 2) (error : Fraction.Rational) where
  /-- The opposite-sheet bilinear source-area request on the retained paired walk. -/ opposite : BilinearAreaRequest
    leftFixed rightFixed paired (error / 10)
  /-- The first-sheet paired source/chart area request on those same retained source occurrences. -/ leftChart :
    PairedChartAreaRequest leftFixed rightFixed (paired.sources first) (error / 10)
  /-- The last-sheet paired source/chart area request on those same retained source occurrences. -/ rightChart :
    PairedChartAreaRequest leftFixed rightFixed (paired.sources last) (error / 10)

constructive_injectivity PolygonRequest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests

variable {leftFixed : FaceMagnitudeBank domains leftDifferential} {rightFixed : FaceMagnitudeBank domains
  rightDifferential}
  {paired : PairedWalk mesh walk} {first last :
    Fin 2} {error : Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests.PolygonRequest

/-- Prepare the opposite-source and both source/chart requests with their common one-tenth allowance. -/
@[expose] def build (leftFixed : FaceMagnitudeBank domains leftDifferential) (rightFixed : FaceMagnitudeBank domains
  rightDifferential)
    (paired : WalkOccurrences.PairedWalk mesh walk) (first last : Fin 2) (error : Fraction.Rational) (positive : 0 <
      error) :
    PolygonRequest leftFixed rightFixed paired first last error :=
  have partPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 10)
  ⟨BilinearAreaRequest.build leftFixed rightFixed paired (error / 10) partPositive,
    PairedChartAreaRequest.build leftFixed rightFixed (paired.sources first)
      (SignedSourceChartRequests.paired_sources_nonloop paired first) (error / 10) partPositive,
    PairedChartAreaRequest.build leftFixed rightFixed (paired.sources last)
      (SignedSourceChartRequests.paired_sources_nonloop paired last) (error / 10) partPositive⟩

/-- The common maximum stage paying all three retained polygon comparison requests. -/
@[expose] def index (request : PolygonRequest leftFixed rightFixed paired first last error) : Nat :=
  max request.opposite.index (max request.leftChart.index request.rightChart.index)

/-- The paid polygon stage also pays both original differential magnitude references. -/
theorem fixed_later (request : PolygonRequest leftFixed rightFixed paired first last error)
    {stage : Nat} (later : request.index ≤ stage) : leftFixed.index ≤ stage ∧ rightFixed.index ≤ stage := by
  have common := (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans later)
  exact ⟨(Data.Nat.Order.le_max_left _ _).trans common, (Data.Nat.Order.le_max_right _ _).trans common⟩

/-- All source choices are replaced by the actual projected edge readings before the requested bound is exposed to the
branch comparison. -/
theorem accurate (request : PolygonRequest leftFixed rightFixed paired first last error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (later : request.index ≤ stage) (different : first ≠ last) :
    let value := fun edge => (⟨edgeValuation mesh leftReadings.values edge,
      CanonicalEdgeValues.edgeValuation mesh rightReadings.values edge⟩ : PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((edges.indexedEdges vertices walk first).map
      value) -
      PairedIncrementArea.area ((edges.indexedEdges vertices walk last).map value)) ≤ error := by
  intro value
  let oppositeComparison := request.opposite.realize leftReadings rightReadings ((Data.Nat.Order.le_max_left _ _).trans
    later) first last different
  have opposite := oppositeComparison.pay
  rw [oppositeComparison.residual_readback] at opposite
  have chartsLater := (Data.Nat.Order.le_max_right _ _).trans later
  let leftComparison := request.leftChart.realizeSupplied .paired leftReadings rightReadings
    ((Data.Nat.Order.le_max_left _ _).trans chartsLater) oppositeComparison.leftSources
  have left := leftComparison.pay
  rw [leftComparison.residual_readback] at left
  let rightComparison := request.rightChart.realizeSupplied .paired leftReadings rightReadings
    ((Data.Nat.Order.le_max_right _ _).trans chartsLater) oppositeComparison.rightSources
  have right := rightComparison.pay
  rw [rightComparison.residual_readback] at right
  let source := fun sheet => PairedIncrementArea.area ((paired.sources sheet).map (fun source =>
    (⟨SourceEdge.increment source leftReadings.values, SourceEdge.increment source rightReadings.values⟩ :
      PrimitivePoint)))
  let polygon := fun sheet => PairedIncrementArea.area ((edges.indexedEdges vertices walk sheet).map value)
  have readback (sheet : Fin 2) :
      PairedIncrementArea.area ((paired.sources sheet).map (fun source => value (source.project
        mesh.triangulation.faces))) =
        polygon sheet := by
    unfold polygon
    rw [← paired.sources_project sheet, Map.map_map]
    rfl
  change Data.Gaussian.Norm.Basic.normSq (source first - source last) ≤ error / 10 at opposite
  change Data.Gaussian.Norm.Basic.normSq (source first - PairedIncrementArea.area
    ((paired.sources first).map (fun source => value (source.project mesh.triangulation.faces)))) ≤ error / 10 at left
  change Data.Gaussian.Norm.Basic.normSq (source last - PairedIncrementArea.area
    ((paired.sources last).map (fun source => value (source.project mesh.triangulation.faces)))) ≤ error / 10 at right
  rw [readback first] at left
  rw [readback last] at right
  have reversed : Data.Gaussian.Norm.Basic.normSq (polygon first - source first) ≤ error / 10 := by
    rw [show polygon first - source first = -(source first - polygon first) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg]
    exact left
  have middle : Data.Gaussian.Norm.Basic.normSq (source first - polygon last) ≤ 2 * (error / 10 + error / 10)
    :=
    (Data.Gaussian.Norm.Bounds.normSq_sub_le_via (source first) (source last) (polygon last)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct opposite
        right) (by decide))
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via (polygon first) (source first) (polygon last)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct reversed
      middle) (by decide))
  exact estimate.trans_eq ((by ring1 : 2 * (error / 10 + 2 * (error / 10 + error / 10)) = error / 10 * 10).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests.PolygonRequest

end
