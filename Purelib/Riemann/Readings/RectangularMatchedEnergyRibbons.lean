module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes

import Purelib.Integration.Path.BoundaryRibbon
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
import Purelib.Riemann.Integration.RectangularWholeSideMagnitude
import Purelib.Riemann.Integration.RectangularWholeVerticalSideMagnitude
import Purelib.Integration.Path.EnergyRibbonCombination
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace

@[expose] public section

/-!
# Energy ribbons on complete matched sides

The finite trace count is retained in the bound. Its geometry and depth are
fixed before choosing a later primitive accuracy, so this is a shrinking
numerical error bound, without claiming spatial decay. Open endpoint
corrections remain in the cached ribbon.
-/

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
namespace Purelib.Riemann.Readings.RectangularMatchedEnergyRibbons

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)

namespace RectangularInverseModels

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Box)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
  {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows : Nat} {target : Coordinate}
  {geometry : Geometry columns rows} {bank : Bank polynomial geometry}
  {transitions : Transitions (bank.refine index)} {gauge : Purelib.Topology.Grid.Signs.Gauge transitions.flatGrid}
  {primitives : Primitives (Purelib.Riemann.Branches.RectangularSheetGauge.Transitions.oriented transitions gauge)
    numerator}
  {cuts : GridCuts geometry} {leftBox rightBox : Box}
  {left : ObservationMesh cuts leftBox} {right : ObservationMesh cuts rightBox} {depth : Nat}

namespace ObservationMesh.MatchedHorizontalSide.Trace

open Purelib.Riemann.Readings.RectangularMatchedEnergyRibbons.RectangularInverseModels.ObservationMesh

variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
  {height : Coordinate} {side : MatchedHorizontalSide left right leftRow rightRow height}

open Purelib.Integration in
open Purelib.Integration.Path in
open Purelib.LinearAlgebra in
/-- Retain the energy ribbon between the two actual readings of a complete matched horizontal side.

The original vertex sequence fixes the ribbon count and preserves all endpoint and owner-junction terms. -/
def energyRibbon (trace : side.Trace depth) (anchors : PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) : Path.BoundaryRibbon.Ribbon trace.vertices.rest.length :=
  BoundaryRibbon.Ribbon.build (trace.leftReadings anchors offsets).values (trace.rightReadings anchors offsets).values

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.LinearAlgebra in
open Purelib.Riemann in
open Purelib.Topology in
/-- The ribbon difference equals the two complete energy areas minus the explicit open-endpoint correction.

The exact finite trace retains zero-length physical owner junctions and both actual endpoint readings. -/
theorem energyRibbon_difference (trace : side.Trace depth) (anchors : PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) :
    let values := fun column row point => (⟨Data.Gaussian.Basic.conj (anchors.alignedValue offsets column row point),
      anchors.alignedValue offsets column row point⟩ : Polygon.Stokes.PrimitivePoint)
    let ribbon := Trace.energyRibbon trace anchors offsets
    ribbon.difference = Periods.CenteredBilinearPath.area
        (fun vertex => trace.leftValue values (trace.vertices.indexed vertex)) -
      Periods.CenteredBilinearPath.area (fun vertex => trace.rightValue values (trace.vertices.indexed vertex)) -
      (Path.BoundaryRibbon.area (ribbon.right (Fin.last trace.vertices.rest.length)) (ribbon.left (Fin.last
        trace.vertices.rest.length)) -
        Path.BoundaryRibbon.area (ribbon.right 0) (ribbon.left 0)) := by
  dsimp only
  let ribbon := Trace.energyRibbon trace anchors offsets
  rw [ribbon.difference_eq, ribbon.leftArea_eq, ribbon.rightArea_eq, ribbon.endpointCorrection_eq,
    ribbon.errors_eq, ribbon.errors_eq, Path.BoundaryRibbon.area_sub_self_right,
      Path.BoundaryRibbon.area_sub_self_right]
  apply congrArg (fun area => area - _)
  apply congrArg₂ (fun left right : Gaussian => left - right)
  · apply FiniteSum.Fin.sumFin_congr
    intro edge
    change Path.BoundaryRibbon.area ((trace.leftReadings anchors offsets).values edge.castSucc)
      ((trace.leftReadings anchors offsets).values edge.succ) = _
    rw [trace.leftReadings_value, trace.leftReadings_value]
    rfl
  · apply FiniteSum.Fin.sumFin_congr
    intro edge
    change Path.BoundaryRibbon.area ((trace.rightReadings anchors offsets).values edge.castSucc)
      ((trace.rightReadings anchors offsets).values edge.succ) = _
    rw [trace.rightReadings_value, trace.rightReadings_value]
    rfl

open Purelib.Data.Gaussian.Norm in
open Purelib.Integration in
open Purelib.LinearAlgebra in
open Purelib.Riemann in
open Purelib.Riemann.Branches.RectangularSheetGauge in
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide in
open Purelib.Topology in
/-- Bound the complete matched horizontal energy ribbon by its retained trace count and primitive error.

The fixed geometry, boundary-column count and selected depth determine the magnitude factor; a later primitive accuracy
shrinks the numerical error while preserving the open-endpoint correction. -/
theorem energyRibbon_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Transitions.oriented transitions gauge) numerator}
    (trace : side.Trace depth) (anchors : PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (refines : ∀ column row, (geometry.box column row).Refines
      ambient)
    (small : request.globalBound ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (Trace.energyRibbon trace anchors offsets).difference ≤
      512 * request.globalBound *
        (2 * (boundarySlope bounds + (left.boundaryColumns : Coordinate) ^ 2 * (2 * (4 + boundarySlope bounds))) +
          request.globalBound) *
        (trace.vertices.rest.length : Coordinate) ^ 2 := by
  let ribbon := Trace.energyRibbon trace anchors offsets
  have errors (vertex : Fin (trace.vertices.rest.length + 1)) : Data.Gaussian.Norm.Basic.normSq (ribbon.errors vertex)
    ≤ 4 *
    request.globalBound := by
    rw [ribbon.errors_eq]
    change Data.Gaussian.Norm.Basic.normSq ((trace.leftReadings anchors offsets).values vertex - (trace.rightReadings
      anchors
      offsets).values vertex) ≤ _
    rw [trace.leftReadings_value, trace.rightReadings_value]
    have scalar := request.overlap_bound anchors offsets refines _ _ _ _
      (trace.leftOwner (trace.vertices.indexed vertex)).contains (trace.rightOwner (trace.vertices.indexed
        vertex)).contains
    simpa only [Basic.normSq_eq_canonical, Trace.leftOwner,
      Trace.rightOwner] using scalar
  have centered (vertex : Fin (trace.vertices.rest.length + 1)) : Data.Gaussian.Norm.Basic.normSq (ribbon.right vertex -
    ribbon.right 0) ≤
      2 * (boundarySlope bounds + (left.boundaryColumns : Coordinate) ^ 2 * (2 * (4 + boundarySlope bounds))) :=
    by
      change Data.Gaussian.Norm.Basic.normSq
        ((trace.rightReadings anchors offsets).values vertex - (trace.rightReadings anchors offsets).values 0) ≤ _
      have scalar := Integration.RectangularWholeSideMagnitude.matched_readings_magnitude
        request anchors offsets refines small trace vertex
      simpa only [Basic.normSq_eq_canonical] using scalar
  exact (Path.EnergyRibbonCombination.difference_bound_centered ribbon errors centered).trans_eq (by ring1)

end ObservationMesh.MatchedHorizontalSide.Trace

namespace ObservationMesh.MatchedVerticalSide.Trace

variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {horizontal : Coordinate} {side : MatchedVerticalSide left right leftColumn rightColumn horizontal}

open Purelib.Integration in
open Purelib.Integration.Path in
open Purelib.LinearAlgebra in
/-- Retain the energy ribbon between the two actual readings of a complete matched vertical side.

The original vertex sequence fixes the ribbon count and preserves all endpoint and owner-junction terms. -/
def energyRibbon (trace : side.Trace depth) (anchors : PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) : Path.BoundaryRibbon.Ribbon trace.vertices.rest.length :=
  BoundaryRibbon.Ribbon.build (trace.leftReadings anchors offsets).values (trace.rightReadings anchors offsets).values

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.LinearAlgebra in
open Purelib.Riemann in
open
  Purelib.Riemann.Readings.RectangularMatchedEnergyRibbons.RectangularInverseModels.ObservationMesh.MatchedVerticalSide
  in
open Purelib.Topology in
/-- The ribbon difference equals the two complete energy areas minus the explicit open-endpoint correction.

The exact finite trace retains zero-length physical owner junctions and both actual endpoint readings. -/
theorem energyRibbon_difference (trace : side.Trace depth) (anchors : PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) :
    let values := fun column row point => (⟨Data.Gaussian.Basic.conj (anchors.alignedValue offsets column row point),
      anchors.alignedValue offsets column row point⟩ : Polygon.Stokes.PrimitivePoint)
    let ribbon := Trace.energyRibbon trace anchors offsets
    ribbon.difference = Periods.CenteredBilinearPath.area
        (fun vertex => trace.leftValue values (trace.vertices.indexed vertex)) -
      Periods.CenteredBilinearPath.area (fun vertex => trace.rightValue values (trace.vertices.indexed vertex)) -
      (Path.BoundaryRibbon.area (ribbon.right (Fin.last trace.vertices.rest.length)) (ribbon.left (Fin.last
        trace.vertices.rest.length)) -
        Path.BoundaryRibbon.area (ribbon.right 0) (ribbon.left 0)) := by
  dsimp only
  let ribbon := Trace.energyRibbon trace anchors offsets
  rw [ribbon.difference_eq, ribbon.leftArea_eq, ribbon.rightArea_eq, ribbon.endpointCorrection_eq,
    ribbon.errors_eq, ribbon.errors_eq, Path.BoundaryRibbon.area_sub_self_right,
      Path.BoundaryRibbon.area_sub_self_right]
  apply congrArg (fun area => area - _)
  apply congrArg₂ (fun left right : Gaussian => left - right)
  · apply FiniteSum.Fin.sumFin_congr
    intro edge
    change Path.BoundaryRibbon.area ((trace.leftReadings anchors offsets).values edge.castSucc)
      ((trace.leftReadings anchors offsets).values edge.succ) = _
    rw [trace.leftReadings_value, trace.leftReadings_value]
    rfl
  · apply FiniteSum.Fin.sumFin_congr
    intro edge
    change Path.BoundaryRibbon.area ((trace.rightReadings anchors offsets).values edge.castSucc)
      ((trace.rightReadings anchors offsets).values edge.succ) = _
    rw [trace.rightReadings_value, trace.rightReadings_value]
    rfl

open Purelib.Data.Gaussian.Norm in
open Purelib.Integration in
open Purelib.LinearAlgebra in
open Purelib.Riemann in
open Purelib.Riemann.Branches.RectangularSheetGauge in
open
  Purelib.Riemann.Readings.RectangularMatchedEnergyRibbons.RectangularInverseModels.ObservationMesh.MatchedVerticalSide
  in
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide in
open Purelib.Topology in
/-- Bound the complete matched vertical energy ribbon by its retained trace count and primitive error.

The fixed geometry, boundary-row count and selected depth determine the magnitude factor; a later primitive accuracy
shrinks the numerical error while preserving the open-endpoint correction. -/
theorem energyRibbon_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Transitions.oriented transitions gauge) numerator}
    (trace : side.Trace depth) (anchors : PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (refines : ∀ column row, (geometry.box column row).Refines
      ambient)
    (small : request.globalBound ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (Trace.energyRibbon trace anchors offsets).difference ≤
      512 * request.globalBound *
        (2 * (boundarySlope bounds + (left.boundaryRows : Coordinate) ^ 2 * (2 * (4 + boundarySlope bounds))) +
          request.globalBound) *
        (trace.vertices.rest.length : Coordinate) ^ 2 := by
  let ribbon := Trace.energyRibbon trace anchors offsets
  have errors (vertex : Fin (trace.vertices.rest.length + 1)) : Data.Gaussian.Norm.Basic.normSq (ribbon.errors vertex)
    ≤ 4 *
    request.globalBound := by
    rw [ribbon.errors_eq]
    change Data.Gaussian.Norm.Basic.normSq ((trace.leftReadings anchors offsets).values vertex - (trace.rightReadings
      anchors
      offsets).values vertex) ≤ _
    rw [trace.leftReadings_value, trace.rightReadings_value]
    have scalar := request.overlap_bound anchors offsets refines _ _ _ _
      (trace.leftOwner (trace.vertices.indexed vertex)).contains (trace.rightOwner (trace.vertices.indexed
        vertex)).contains
    simpa only [Basic.normSq_eq_canonical, Trace.leftOwner,
      Trace.rightOwner] using scalar
  have centered (vertex : Fin (trace.vertices.rest.length + 1)) : Data.Gaussian.Norm.Basic.normSq (ribbon.right vertex -
    ribbon.right 0) ≤
      2 * (boundarySlope bounds + (left.boundaryRows : Coordinate) ^ 2 * (2 * (4 + boundarySlope bounds))) :=
    by
      change Data.Gaussian.Norm.Basic.normSq
        ((trace.rightReadings anchors offsets).values vertex - (trace.rightReadings anchors offsets).values 0) ≤ _
      have scalar := Integration.RectangularWholeVerticalSideMagnitude.matched_vertical_readings_magnitude
        request anchors offsets refines small trace vertex
      simpa only [Basic.normSq_eq_canonical] using scalar
  exact (Path.EnergyRibbonCombination.difference_bound_centered ribbon errors centered).trans_eq (by ring1)

end ObservationMesh.MatchedVerticalSide.Trace
end RectangularInverseModels
end Purelib.Riemann.Readings.RectangularMatchedEnergyRibbons
