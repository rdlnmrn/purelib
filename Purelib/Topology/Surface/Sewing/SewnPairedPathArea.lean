module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPathArea
import Purelib.Integration.Path.PairedIncrementComparison
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

public section

/-! Pair the actual retained scalar sewing samples by their common source
route list. This preserves every oriented and repeated occurrence. -/

section

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPathArea.PathSources

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

namespace Purelib.Topology.Surface.Sewing.SewnPairedPathArea

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate FaceBank)
open Purelib.Integration.Path.PairedIncrementArea (area)
open Purelib.Integration.Path.PairedIncrementComparison (area_difference_bound)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources PathTerm OrientedOwner)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources (Sample)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {edges : List (Stokes.OrientedEdge patch.count)}
  {sources : SewnPrimitiveFaces.PathSources patch edges}
  {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {leftValues rightValues : PrimitiveSewing.PrimitiveValues patch.count}
  {leftBank : SewnPrimitiveFaces.FaceBank patch leftLocal leftValues} {rightBank : SewnPrimitiveFaces.FaceBank patch
    rightLocal rightValues}

/-- The original route's actual increment discrepancy is bounded by its retained path-sample allowance. -/
theorem route_error_le (sample : PathSources.Sample sources leftBank) (route : SewnPrimitiveFaces.OrientedOwner patch)
    (member : route ∈ sources.entries) :
    Data.Gaussian.Norm.Basic.normSq ((leftValues route.cutEdge.finish - leftValues route.cutEdge.start) -
      route.sourceEdge.increment leftLocal) ≤ sample.bound := by
  rw [← sample.routes_eq] at member
  obtain ⟨term, inTerms, equal⟩ := Map.mem_map.mp member
  rw [← equal, ← term.increment_eq, ← term.error_eq]
  exact Sample.term_error_le sample term inTerms

/-- The paired entries use source ownership as their shared index. -/
@[expose] def pairedAreaPairs (_left : PathSources.Sample sources leftBank) (_right : PathSources.Sample sources
  rightBank) :
    List (Stokes.PrimitivePoint × Stokes.PrimitivePoint) :=
  sources.entries.map (fun route =>
    (⟨leftValues route.cutEdge.finish - leftValues route.cutEdge.start,
      rightValues route.cutEdge.finish - rightValues route.cutEdge.start⟩,
     ⟨route.sourceEdge.increment leftLocal, route.sourceEdge.increment rightLocal⟩))

/-- Both components of each retained original/source pair are bounded by the larger original sample allowance. -/
theorem pairedAreaPairs_errors (left : PathSources.Sample sources leftBank) (right : PathSources.Sample sources
  rightBank) :
    ∀ pair ∈ pairedAreaPairs left right, (PrimitivePoint.Bounded ((PrimitivePoint.sub pair.1)
      pair.2)) (max left.bound right.bound) := by
  intro pair member
  obtain ⟨route, inRoutes, rfl⟩ := Map.mem_map.mp member
  constructor
  · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (route_error_le left route inRoutes).trans (Fraction.Order.Basic.le_max_left _ _)
  · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (route_error_le right route inRoutes).trans (Fraction.Order.Basic.le_max_right _ _)

/-- Reading actual components recovers the exact original cut-edge increment sequence. -/
theorem pairedAreaPairs_sewn (left : PathSources.Sample sources leftBank) (right : PathSources.Sample sources rightBank)
  :
    (pairedAreaPairs left right).map Prod.fst = edges.map (fun edge =>
      (⟨leftValues edge.finish - leftValues edge.start,
        rightValues edge.finish - rightValues edge.start⟩ : Stokes.PrimitivePoint)) := by
  have equal := congrArg (List.map (fun edge : Stokes.OrientedEdge patch.count =>
    (⟨leftValues edge.finish - leftValues edge.start,
      rightValues edge.finish - rightValues edge.start⟩ : Stokes.PrimitivePoint))) sources.edges_eq
  simpa only [pairedAreaPairs, Map.map_map, Function.comp_def, -eq_self, -iff_self] using equal

/-- Reading source components recovers the exact original ordered source increments. -/
theorem pairedAreaPairs_source (left : PathSources.Sample sources leftBank) (right : PathSources.Sample sources
  rightBank) :
    (pairedAreaPairs left right).map Prod.snd = sources.sources.map (fun source =>
      (⟨source.increment leftLocal, source.increment rightLocal⟩ : Stokes.PrimitivePoint)) := by
  rw [pairedAreaPairs, Map.map_map, sources.sources_eq, Map.map_map]
  rfl

/-- An original magnitude bound and retained error allowance bound the actual Gaussian reading. -/
private theorem perturbed_norm {actual original : Gaussian.Basic.Canonical} {magnitude error :
  SewnPrimitiveFaces.Coordinate}
    (bounded : Data.Gaussian.Norm.Basic.normSq original ≤ magnitude) (accurate : Data.Gaussian.Norm.Basic.normSq
      (actual - original) ≤ error) :
    Data.Gaussian.Norm.Basic.normSq actual ≤ 2 * (magnitude + error) := by
  have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two original (actual - original)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add bounded accurate) (by decide))
  have equal : original + (actual - original) = actual := by ring1
  rwa [equal] at estimate

/-- The complete sewn polygon is compared to the original source polygon. The actual occurrence count and both inherited
sewing allowances remain. -/
theorem paired_area_error_le (left : PathSources.Sample sources leftBank) (right : PathSources.Sample sources rightBank)
    {magnitude : SewnPrimitiveFaces.Coordinate} (nonnegative : 0 ≤ magnitude)
    (bounded : ∀ source ∈ sources.sources,
      (PrimitivePoint.Bounded (⟨source.increment leftLocal, source.increment rightLocal⟩ : Stokes.PrimitivePoint))
        magnitude) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (edges.map (fun edge =>
      (⟨leftValues edge.finish - leftValues edge.start,
        rightValues edge.finish - rightValues edge.start⟩ : Stokes.PrimitivePoint))) -
      PairedIncrementArea.area (sources.sources.map (fun source =>
        (⟨source.increment leftLocal, source.increment rightLocal⟩ : Stokes.PrimitivePoint)))) ≤
      32 * (edges.length : SewnPrimitiveFaces.Coordinate)^4 * max left.bound right.bound *
        (magnitude + max left.bound right.bound) := by
  let error := max left.bound right.bound
  have errorNonnegative : 0 ≤ error := (Sample.bound_nonnegative left).trans (Fraction.Order.Basic.le_max_left _ _)
  have sourceBound : ∀ pair ∈ pairedAreaPairs left right, (PrimitivePoint.Bounded pair.2) magnitude
    := by
    intro pair member
    obtain ⟨route, inRoutes, rfl⟩ := Map.mem_map.mp member
    exact bounded route.sourceEdge (sources.sources_eq ▸ Map.mem_map_of_mem inRoutes)
  have commonNonnegative : 0 ≤ 2 * (magnitude + error) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg nonnegative errorNonnegative)
  have magnitudeLe : magnitude ≤ 2 * (magnitude + error) :=
    (le_add_of_nonneg_right errorNonnegative).trans
      ((le_add_of_nonneg_right (add_nonneg nonnegative errorNonnegative)).trans_eq (by ring1))
  have estimate := PairedIncrementComparison.area_difference_bound (pairedAreaPairs left right)
    errorNonnegative commonNonnegative (pairedAreaPairs_errors left right)
    (by
      intro pair member
      have source := sourceBound pair member
      have errors := pairedAreaPairs_errors left right pair member
      have sourceLeft := source.1
      have sourceRight := source.2
      have errorLeft := errors.1
      have errorRight := errors.2
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at sourceLeft sourceRight errorLeft errorRight
      have leftBound := perturbed_norm sourceLeft errorLeft
      have rightBound := SewnPairedPathArea.perturbed_norm sourceRight errorRight
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at leftBound rightBound
      exact ⟨leftBound, rightBound⟩)
    (by
      intro pair member
      exact ⟨(sourceBound pair member).1.trans magnitudeLe, (sourceBound pair member).2.trans magnitudeLe⟩)
  have count := congrArg List.length sources.edges_eq
  rw [Map.length_map] at count
  rw [pairedAreaPairs_sewn left right,
    pairedAreaPairs_source left right] at estimate
  have pairCount : (pairedAreaPairs left right).length = edges.length := by
    rw [pairedAreaPairs, Map.length_map, count]
  rw [pairCount] at estimate
  exact estimate.trans_eq (by dsimp only [error]; ring1)

end Purelib.Topology.Surface.Sewing.SewnPairedPathArea

end
