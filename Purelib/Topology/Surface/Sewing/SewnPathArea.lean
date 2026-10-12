module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Energy.Polygon
import Purelib.Topology.Chain.PathBoundary

import Purelib.Data.Gaussian.Norm.Sum.Prefix
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Topology.Surface.Sewing.SewnBoundaryMagnitude
import Purelib.Integration.Path.IncrementAreaComparison
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

public section

/-!
# Full path areas with the actual inherited sewing errors

Compare the entire cumulative polygon of original face increments with the
actual sewn path, not just their endpoint sums. The cached path allowances
pay every occurrence and every inherited offset error. Open traces retain
their anchor term; actual closed cut paths have an exact area readback.
-/

section

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Energy

open Purelib.Integration.Path

open Purelib.Integration.Path.IncrementArea

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnBoundaryMagnitude.PathSources

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources

namespace Purelib.Topology.Surface.Sewing.SewnPathArea

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Integration.Path.IncrementArea (pathArea traceArea Summary)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources PathTerm OrientedOwner)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources (Sample)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {values : PrimitiveSewing.PrimitiveValues patch.count} {bank : SewnPrimitiveFaces.FaceBank patch localValues values}
  {edges : List (Stokes.OrientedEdge patch.count)} {sources : SewnPrimitiveFaces.PathSources patch edges}

namespace PathSources.Sample

/-- The retained path-sample error allowance is nonnegative. -/
theorem bound_nonnegative (sample : PathSources.Sample sources bank) : 0 ≤ sample.bound :=
  (Gaussian.Norm.Basic.normSq_nonneg sample.error).trans sample.error_bound

/-- Every original cached path term's error is bounded by the complete retained sample allowance. -/
theorem term_error_le (sample : PathSources.Sample sources bank) (term : SewnPrimitiveFaces.PathTerm bank) (member :
  term ∈ sample.terms) :
    Data.Gaussian.Norm.Basic.normSq term.error ≤ sample.bound := by
  have positive := fun entry (_ : entry ∈ sample.terms) => (Gaussian.Norm.Basic.normSq_nonneg entry.error).trans
    entry.error_bound
  have termLe := Squares.coordinate_le_coordinateSum_map PathTerm.allowance sample.terms positive term member
  have count : 1 ≤ sample.terms.length := by
    cases equal : sample.terms with
    | nil => rw [equal] at member; exact (List.not_mem_nil member).elim
    | cons head tail => exact Nat.succ_le_succ (Nat.zero_le _)
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Cast.Order.natCast_le_direct count) (Squares.coordinateSum_map_nonnegative PathTerm.allowance sample.terms
      positive)
  rw [Nat.cast_one, _root_.one_mul, ← sample.bound_eq] at scaled
  exact term.error_bound.trans (termLe.trans scaled)

/-- Each cached original increment norm is bounded by the full source-increment norm sum. -/
theorem term_increment_le (sample : PathSources.Sample sources bank) (term : SewnPrimitiveFaces.PathTerm bank) (member :
  term ∈ sample.terms) :
    Data.Gaussian.Norm.Basic.normSq term.increment ≤ Gaussian.Norm.Sum.Basic.gaussianNormSqSum (sources.sources.map
      (fun source =>
      source.increment localValues)) := by
  have bound := Squares.coordinate_le_coordinateSum_map (fun entry : SewnPrimitiveFaces.PathTerm bank =>
    Data.Gaussian.Norm.Basic.normSq
    entry.increment) sample.terms
    (fun entry _ => Gaussian.Norm.Basic.normSq_nonneg entry.increment) term member
  rw [Gaussian.Norm.Sum.Basic.gaussianNormSqSum_eq_coordinateSum_map, Sample.increment_normSum_eq sample] at bound
  exact bound

/-- Pair each actual sewn edge with its retained original face increment. -/
@[expose] def areaPairs (sample : PathSources.Sample sources bank) : List (Gaussian.Basic.Canonical ×
  Gaussian.Basic.Canonical) :=
  sample.terms.map (fun term => (values term.route.cutEdge.finish - values term.route.cutEdge.start, term.increment))

/-- The actual side of the retained comparison pairs recovers the original cut-edge increment sequence. -/
theorem areaPairs_left (sample : PathSources.Sample sources bank) :
    (areaPairs sample).map Prod.fst = edges.map (fun edge => values edge.finish - values edge.start) := by
  have equal := congrArg (List.map (fun route : SewnPrimitiveFaces.OrientedOwner patch => values route.cutEdge.finish -
    values route.cutEdge.start))
    sample.routes_eq
  have edgesEqual := congrArg (List.map (fun edge : Stokes.OrientedEdge patch.count => values edge.finish - values
    edge.start)) sources.edges_eq
  simp only [areaPairs, Map.map_map, Function.comp_def, -eq_self, -iff_self] at equal edgesEqual ⊢
  exact equal.trans edgesEqual

/-- The source side of the retained comparison pairs reads the original cached term increments. -/
theorem areaPairs_right (sample : PathSources.Sample sources bank) :
    (areaPairs sample).map Prod.snd = sample.terms.map PathTerm.increment := by
  simp only [areaPairs, Map.map_map, Function.comp_def, -eq_self, -iff_self]
  rfl

/-- The retained area-comparison pairs preserve the original path occurrence count. -/
theorem areaPairs_length (sample : PathSources.Sample sources bank) : (areaPairs sample).length = edges.length :=
  by
  have length := congrArg List.length (Sample.areaPairs_left sample)
  simpa only [Map.length_map, -eq_self, -iff_self] using length

/-- Bound the complete cumulative original/source path-area difference with all count and sewing-error factors retained.
-/
theorem area_difference_bound (sample : PathSources.Sample sources bank) {magnitude : Fraction.Rational}
    (bounded : Gaussian.Norm.Sum.Basic.gaussianNormSqSum (sources.sources.map (fun source => source.increment
      localValues)) ≤ magnitude) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea ((areaPairs sample).map Prod.fst) -
      IncrementArea.pathArea
      ((areaPairs sample).map Prod.snd)) ≤
      32 * (edges.length : Fraction.Rational) ^ 4 * sample.bound * (magnitude + sample.bound) := by
  have magnitudeNonnegative := (Gaussian.Basic.Canonical.Norm.Sum.Prefix.nonnegative _).trans bounded
  have sumNonnegative := add_nonneg magnitudeNonnegative (bound_nonnegative sample)
  have rightBound (term : SewnPrimitiveFaces.PathTerm bank) (member : term ∈ sample.terms) :
      Data.Gaussian.Norm.Basic.normSq term.increment ≤ 2 * (magnitude + sample.bound) :=
    ((term_increment_le sample term member).trans bounded).trans
      ((le_add_of_nonneg_right (bound_nonnegative sample)).trans (by
        have bound := le_add_of_nonneg_right (a := magnitude + sample.bound) sumNonnegative
        exact bound.trans_eq (by ring1)))
  have estimate := IncrementAreaComparison.pathArea_difference_bound (areaPairs sample)
    (bound := 2 * (magnitude + sample.bound)) (bound_nonnegative sample)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) sumNonnegative)
    (by
      intro pair member
      obtain ⟨term, member, equal⟩ := Map.mem_map.mp member
      rw [← equal, ← term.error_eq]
      exact term_error_le sample term member)
    (by
      intro pair member
      obtain ⟨term, member, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two term.error term.increment).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (term_error_le sample term member) ((term_increment_le sample term member).trans
            bounded)) (by decide))
      rw [term.error_eq, sub_add_cancel] at estimate
      exact estimate.trans_eq (by ring1))
    (by
      intro pair member
      obtain ⟨term, member, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      exact rightBound term member)
  rw [areaPairs_length sample] at estimate
  exact estimate.trans_eq (by ring1)

set_option genInjectivity false in
/-- Both full paths are cached. The original side consumes the path sample's already evaluated increments rather than
rerunning local models. -/
structure AreaSample (sample : PathSources.Sample sources bank) where
  /-- Cached cumulative summary of the original retained source increments. -/ source : IncrementArea.Summary
    ((areaPairs sample).map Prod.snd)
  /-- Cached cumulative summary of the actual original cut-edge increments. -/ sewn : IncrementArea.Summary
    ((areaPairs sample).map Prod.fst)

constructive_injectivity AreaSample

namespace AreaSample

variable {sample : PathSources.Sample sources bank}

/-- Cache complete cumulative area summaries for the retained source and actual original increment paths. -/
@[expose] def build (sample : PathSources.Sample sources bank) : AreaSample sample :=
  ⟨Summary.build ((areaPairs sample).map Prod.snd), Summary.build ((areaPairs sample).map Prod.fst)⟩

/-- The source summary total is the original path sample's cached increment value. -/
theorem source_total (area : AreaSample sample) : area.source.total = sample.value := by
  rw [area.source.total_eq, areaPairs_right sample, sample.value_eq]

/-- The source area cache reads the exact original source-increment path in retained order. -/
theorem source_path (area : AreaSample sample) :
    area.source.area = IncrementArea.pathArea (sources.sources.map (fun source => source.increment localValues)) := by
  rw [area.source.area_eq, areaPairs_right sample, sources.sources_eq, ← sample.routes_eq]
  simp only [Map.map_map, Function.comp_def, -eq_self, -iff_self]
  exact congrArg IncrementArea.pathArea (Map.map_congr_left (fun term _ => term.increment_eq))

/-- The two original cached cumulative areas satisfy the complete retained sewing-error bound. -/
theorem difference_bound (area : AreaSample sample) {magnitude : Fraction.Rational}
    (bounded : Gaussian.Norm.Sum.Basic.gaussianNormSqSum (sources.sources.map (fun source => source.increment
      localValues)) ≤ magnitude) :
    Data.Gaussian.Norm.Basic.normSq (area.sewn.area - area.source.area) ≤
      32 * (edges.length : Fraction.Rational) ^ 4 * sample.bound * (magnitude + sample.bound) := by
  rw [area.sewn.area_eq, area.source.area_eq]
  exact area_difference_bound sample bounded

/-- The difference of the original cached endpoint totals is exactly the retained path-sample error. -/
theorem total_error (area : AreaSample sample) : area.sewn.total - area.source.total = sample.error := by
  rw [area.sewn.total_eq, Sample.areaPairs_left sample, area.source_total]
  exact sample.error_eq_difference.symm

open Purelib.Integration.Path.IncrementArea in
/-- A nonzero common origin pays the actual total mismatch. This term is retained even when only the projected path,
rather than the cut path, closes. -/
theorem trace_difference_bound (area : AreaSample sample) (anchor : Gaussian.Basic.Canonical) {magnitude :
  Fraction.Rational}
    (bounded : Gaussian.Norm.Sum.Basic.gaussianNormSqSum (sources.sources.map (fun source => source.increment
      localValues)) ≤ magnitude) :
    Data.Gaussian.Norm.Basic.normSq (traceArea anchor ((areaPairs sample).map Prod.fst) - traceArea anchor
      ((areaPairs
      sample).map Prod.snd)) ≤
      64 * (edges.length : Fraction.Rational) ^ 4 * sample.bound * (magnitude + sample.bound) +
        8 * Data.Gaussian.Norm.Basic.normSq anchor * sample.bound := by
  have equal : traceArea anchor ((areaPairs sample).map Prod.fst) - traceArea anchor ((areaPairs
    sample).map Prod.snd) =
      (area.sewn.area - area.source.area) + BoundaryRibbon.area anchor sample.error := by
    rw [IncrementArea.traceArea_eq, IncrementArea.traceArea_eq,
      ← area.sewn.area_eq, ← area.source.area_eq, ← area.sewn.total_eq, ← area.source.total_eq, ← area.total_error]
    apply Gaussian.Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj, Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
      -eq_self, -iff_self] <;> ring1
  have anchored := (BoundaryRibbon.area_bound anchor sample.error).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sample.error_bound
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Gaussian.Norm.Basic.normSq_nonneg anchor)))
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (area.difference_bound bounded) anchored) (by decide)).trans_eq (by ring1))

end AreaSample
end PathSources.Sample

open Purelib.Integration.Path.IncrementArea in
/-- Literal area readback of a connected cut path; no identification of distinct face offsets or projected endpoints is
made. -/
theorem traceArea_edges {count : Nat} (values : PrimitiveSewing.PrimitiveValues count) :
    ∀ {edges : List (Stokes.OrientedEdge count)} {start finish : Fin count},
      PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish →
      traceArea (values start) (edges.map (fun edge => values edge.finish - values edge.start)) =
        Stokes.edgeListArea (fun vertex => Polygon.energyPrimitivePoint (values vertex)) edges
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons tail => by
      simp only [List.map_cons, traceArea, show ∀ first last : Gaussian.Basic.Canonical, first + (last - first) = last
        by intros; ring1, -eq_self, -iff_self]
      rw [traceArea_edges values tail]
      rfl

/-- A genuinely closed original cut path identifies its cached cumulative area with its primitive edge-list area. -/
theorem PathSources.Sample.AreaSample.closed_area {sample : PathSources.Sample sources bank}
    (area : Sample.AreaSample sample) {anchor : Fin patch.count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) :
    area.sewn.area = Stokes.edgeListArea (fun vertex => Polygon.energyPrimitivePoint (values vertex)) edges := by
  have equal := traceArea_edges values closed
  rw [IncrementArea.traceArea_eq, Sample.telescope values closed, Gaussian.Basic.sub_self,
    IncrementArea.area_zero_right, Gaussian.Basic.add_zero] at equal
  exact area.sewn.area_eq.trans ((congrArg IncrementArea.pathArea (areaPairs_left sample)).trans equal)

/-- The area of the complete actual cut boundary is the sewn cumulative path area, independently of its initial
primitive offset. -/
theorem CachedSample.boundary_pathArea {patch : SewingTree.SewnPatch faces}
    (surface : SewnPrimitiveSamples.CachedSample patch localValues) (sources : SewnPrimitiveFaces.PathSources patch.cut
      patch.cut.boundary)
    (area : SewnPathArea.PathSources.Sample.AreaSample (CachedSample.pathSample surface sources)) : area.sewn.area =
      surface.boundaryArea := by
  have equal (edges : List (Stokes.OrientedEdge patch.cut.count)) :
      Stokes.edgeListArea (fun vertex => Polygon.energyPrimitivePoint (surface.sewn.values vertex)) edges =
        Stokes.edgeListArea surface.energyValues edges := by
    induction edges with
    | nil => rfl
    | cons edge tail ih =>
        rw [Stokes.edgeListArea, Stokes.edgeListArea, surface.energyValues_eq, surface.energyValues_eq, ih]
  exact (area.closed_area patch.cut.closed).trans ((equal patch.cut.boundary).trans surface.boundaryArea_eq.symm)

end Purelib.Topology.Surface.Sewing.SewnPathArea

end
