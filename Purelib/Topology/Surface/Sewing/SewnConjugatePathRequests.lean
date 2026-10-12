module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
public import Purelib.Topology.Surface.Sewing.SewnPairedPathArea
import Purelib.Topology.Surface.Sewing.SewnPathArea
public import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.SewnPairedPathRequests
import Purelib.Integration.Path.ConjugateIncrementComparison
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

public section

/-! Conjugate path areas reuse the cached scalar sewing samples and the
existing geometry-first path request. -/
section

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPathArea.PathSources

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

namespace Purelib.Topology.Surface.Sewing.SewnConjugatePathRequests.Sample

open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate FaceBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources (Sample)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {edges : List (Stokes.OrientedEdge patch.count)}
  {sources : SewnPrimitiveFaces.PathSources patch edges}
  {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {leftValues rightValues : PrimitiveSewing.PrimitiveValues patch.count}
  {leftBank : SewnPrimitiveFaces.FaceBank patch leftLocal leftValues} {rightBank : SewnPrimitiveFaces.FaceBank patch
    rightLocal rightValues}

/-- A source magnitude bound and retained difference bound control the actual Gaussian reading. -/
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
theorem conjugate_area_error_le (left : PathSources.Sample sources leftBank) (right : PathSources.Sample sources
  rightBank)
    {magnitude : SewnPrimitiveFaces.Coordinate} (nonnegative : 0 ≤ magnitude)
    (bounded : ∀ source ∈ sources.sources,
      (PrimitivePoint.Bounded (⟨source.increment leftLocal, source.increment rightLocal⟩ : Stokes.PrimitivePoint))
        magnitude) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (edges.map (fun edge =>
      (⟨Data.Gaussian.Basic.conj (leftValues edge.finish - leftValues edge.start),
        rightValues edge.finish - rightValues edge.start⟩ : Stokes.PrimitivePoint))) -
      PairedIncrementArea.area (sources.sources.map (fun source =>
        (⟨Data.Gaussian.Basic.conj (source.increment leftLocal), source.increment rightLocal⟩ :
          Stokes.PrimitivePoint)))) ≤
      32 * (edges.length : SewnPrimitiveFaces.Coordinate)^4 * max left.bound right.bound *
        (magnitude + max left.bound right.bound) := by
  let error := max left.bound right.bound
  have errorNonnegative : 0 ≤ error := (Sample.bound_nonnegative left).trans (Fraction.Order.Basic.le_max_left _ _)
  have sourceBound : ∀ pair ∈ SewnPairedPathArea.pairedAreaPairs left right, (PrimitivePoint.Bounded pair.2) magnitude
    := by
    intro pair member
    obtain ⟨route, inRoutes, rfl⟩ := Map.mem_map.mp member
    exact bounded route.sourceEdge (sources.sources_eq ▸ Map.mem_map_of_mem inRoutes)
  have commonNonnegative : 0 ≤ 2 * (magnitude + error) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg nonnegative errorNonnegative)
  have magnitudeLe : magnitude ≤ 2 * (magnitude + error) :=
    (le_add_of_nonneg_right errorNonnegative).trans
      ((le_add_of_nonneg_right (add_nonneg nonnegative errorNonnegative)).trans_eq (by ring1))
  have estimate := ConjugateIncrementComparison.conjugate_area_difference_bound (SewnPairedPathArea.pairedAreaPairs left
    right)
    errorNonnegative commonNonnegative (SewnPairedPathArea.pairedAreaPairs_errors left right)
    (by
      intro pair member
      have source := sourceBound pair member
      have errors := SewnPairedPathArea.pairedAreaPairs_errors left right pair member
      have sourceLeft := source.1
      have sourceRight := source.2
      have errorLeft := errors.1
      have errorRight := errors.2
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at sourceLeft sourceRight errorLeft errorRight
      have leftBound := perturbed_norm sourceLeft errorLeft
      have rightBound := Sample.perturbed_norm sourceRight errorRight
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at leftBound rightBound
      exact ⟨leftBound, rightBound⟩)
    (by
      intro pair member
      exact ⟨(sourceBound pair member).1.trans magnitudeLe, (sourceBound pair member).2.trans magnitudeLe⟩)
  have count := congrArg List.length sources.edges_eq
  rw [Map.length_map] at count
  have sewn := congrArg (List.map ConjugateIncrementComparison.conjugateFirst) (SewnPairedPathArea.pairedAreaPairs_sewn
    left right)
  have original := congrArg (List.map ConjugateIncrementComparison.conjugateFirst)
    (SewnPairedPathArea.pairedAreaPairs_source left right)
  rw [Map.map_map, Map.map_map] at sewn original
  dsimp only [Function.comp_def] at sewn original
  rw [sewn, original] at estimate
  have pairCount : (SewnPairedPathArea.pairedAreaPairs left right).length = edges.length := by
    rw [SewnPairedPathArea.pairedAreaPairs, Map.length_map, count]
  rw [pairCount] at estimate
  exact estimate.trans_eq (by dsimp only [error]; ring1)

end Purelib.Topology.Surface.Sewing.SewnConjugatePathRequests.Sample

namespace Purelib.Topology.Surface.Sewing.SewnConjugatePathRequests.PathAreaRequest
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate FaceBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources)
open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests (PathAreaRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
  {count : Nat} {magnitude target : SewnPrimitiveFaces.Coordinate}
  {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {leftValues rightValues : PrimitiveSewing.PrimitiveValues patch.count}
  {leftBank : SewnPrimitiveFaces.FaceBank patch leftLocal leftValues} {rightBank : SewnPrimitiveFaces.FaceBank patch
    rightLocal rightValues}
  {edges : List (Stokes.OrientedEdge patch.count)} {sources : SewnPrimitiveFaces.PathSources patch edges}

/-- One precomputed budget pays the actual full paired polygon difference. -/
theorem conjugate_accurate (request : SewnPathAreaRequests.PathAreaRequest assembly count magnitude target)
    (left : PathSources.Sample sources leftBank) (right : PathSources.Sample sources rightBank)
    (lengthEq : edges.length = count)
    (bounded : ∀ source ∈ sources.sources,
      (PrimitivePoint.Bounded (⟨source.increment leftLocal, source.increment rightLocal⟩ : Stokes.PrimitivePoint))
        magnitude)
    (leftSmall : left.bound < request.error) (rightSmall : right.bound < request.error) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (edges.map (fun edge =>
      (⟨Data.Gaussian.Basic.conj (leftValues edge.finish - leftValues edge.start),
        rightValues edge.finish - rightValues edge.start⟩ : Stokes.PrimitivePoint))) -
      PairedIncrementArea.area (sources.sources.map (fun source =>
        (⟨Data.Gaussian.Basic.conj (source.increment leftLocal), source.increment rightLocal⟩ :
          Stokes.PrimitivePoint)))) < target := by
  have estimate := SewnConjugatePathRequests.Sample.conjugate_area_error_le left right request.magnitude_nonnegative
    bounded
  rw [lengthEq] at estimate
  exact estimate.trans_lt (request.paid ((Sample.bound_nonnegative left).trans (Fraction.Order.Basic.le_max_left _ _))
    (Fraction.Order.Basic.max_lt leftSmall rightSmall))

/-- Both actual cached surfaces consume the same contact tolerance. -/
theorem conjugate_cached_accurate {sewnPatch : SewingTree.SewnPatch faces}
    (request : SewnPathAreaRequests.PathAreaRequest sewnPatch.assembly count magnitude target)
    (left : SewnPrimitiveSamples.CachedSample sewnPatch leftLocal) (right : SewnPrimitiveSamples.CachedSample sewnPatch
      rightLocal)
    (leftAccurate : SewnPrimitiveRequests.LocalAccuracy request.path.tolerance left.sewn.readings)
    (rightAccurate : SewnPrimitiveRequests.LocalAccuracy request.path.tolerance right.sewn.readings)
    {edges : List (Stokes.OrientedEdge sewnPatch.cut.count)} (sources : SewnPrimitiveFaces.PathSources sewnPatch.cut
      edges)
    (lengthEq : edges.length = count)
    (bounded : ∀ source ∈ sources.sources,
      (PrimitivePoint.Bounded (⟨source.increment leftLocal, source.increment rightLocal⟩ : Stokes.PrimitivePoint))
        magnitude) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (edges.map (fun edge =>
      (⟨Data.Gaussian.Basic.conj (left.sewn.values edge.finish - left.sewn.values edge.start),
        right.sewn.values edge.finish - right.sewn.values edge.start⟩ : Stokes.PrimitivePoint))) -
      PairedIncrementArea.area (sources.sources.map (fun source =>
        (⟨Data.Gaussian.Basic.conj (source.increment leftLocal), source.increment rightLocal⟩ :
          Stokes.PrimitivePoint)))) < target :=
  conjugate_accurate request (CachedSample.pathSample left sources) (CachedSample.pathSample right
    sources) lengthEq bounded
    (request.path.cached_accurate left leftAccurate sources lengthEq.le)
    (request.path.cached_accurate right rightAccurate sources lengthEq.le)

end Purelib.Topology.Surface.Sewing.SewnConjugatePathRequests.PathAreaRequest

end
