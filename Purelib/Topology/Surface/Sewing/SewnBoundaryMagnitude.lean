module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Data.Gaussian.Norm.Sum.Prefix
import Purelib.Data.Gaussian.Basic
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

public section

/-!
# Every boundary prefix controlled by one complete sewn word

The complete source norm sum and complete sewing allowance control the
primitive displacement along every prefix. This remains true when the full
boundary sum vanishes. No independent prefix integration is constructed.
-/

section

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Data

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources

namespace Purelib.Topology.Surface.Sewing.SewnBoundaryMagnitude

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources (Sample)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathTerm PathSources OrientedOwner)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {values : PrimitiveSewing.PrimitiveValues patch.count} {bank : SewnPrimitiveFaces.FaceBank patch localValues values}

/-- Bound an actual original sewn edge increment by its retained source norm and sewing allowance. -/
private theorem term_norm_le (term : SewnPrimitiveFaces.PathTerm bank) :
    Data.Gaussian.Norm.Basic.normSq (values term.route.cutEdge.finish - values term.route.cutEdge.start) ≤
      2 * (term.allowance + Data.Gaussian.Norm.Basic.normSq term.increment) := by
  have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two term.error term.increment).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add term.error_bound le_rfl) (by decide))
  rw [term.error_eq, sub_add_cancel] at estimate
  exact estimate

/-- Bound the complete actual increment norm sum by all retained source norms and sewing allowances. -/
private theorem terms_norm_le (terms : List (SewnPrimitiveFaces.PathTerm bank)) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (terms.map (fun term => values term.route.cutEdge.finish - values
      term.route.cutEdge.start)) ≤
      2 * (Purelib.Algebra.FiniteSum.Rational.Squares.coordinateSum (terms.map PathTerm.allowance) +
        Gaussian.Norm.Sum.Basic.gaussianNormSqSum (terms.map PathTerm.increment)) := by
  induction terms with
  | nil => change (0 : Fraction.Rational) ≤ 2 * (0 + 0); exact le_of_eq (by ring1)
  | cons term terms ih =>
      have head := term_norm_le term
      simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at head
      let allowances := Squares.coordinateSum
        (terms.map PathTerm.allowance)
      let increments := Gaussian.Norm.Sum.Basic.gaussianNormSqSum
        (terms.map PathTerm.increment)
      exact (add_le_add head ih).trans_eq (by
        change 2 * (term.allowance + Canonical.normSq term.increment) +
          2 * (allowances + increments) =
          2 * ((term.allowance + allowances) +
            (Canonical.normSq term.increment + increments))
        ring1)

namespace PathSources.Sample

variable {edges : List (Stokes.OrientedEdge patch.count)} {sources : SewnPrimitiveFaces.PathSources patch edges}

/-- Reading original cut edges from the cached terms recovers the exact requested path. -/
private theorem cutEdges_eq (sample : PathSources.Sample sources bank) : sample.terms.map (fun term =>
  term.route.cutEdge) = edges := by
  have equal := congrArg (List.map OrientedOwner.cutEdge) sample.routes_eq
  rw [Map.map_map] at equal
  exact equal.trans sources.edges_eq

/-- The cached increment norm sum equals the complete norm sum of the original retained source readings. -/
theorem increment_normSum_eq (sample : PathSources.Sample sources bank) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (sample.terms.map PathTerm.increment) =
      Gaussian.Norm.Sum.Basic.gaussianNormSqSum (sources.sources.map (fun source => source.increment localValues)) := by
  rw [sources.sources_eq, ← sample.routes_eq, Map.map_map, Map.map_map]
  apply congrArg Gaussian.Norm.Sum.Basic.gaussianNormSqSum
  exact Map.map_congr_left (fun term _ => term.increment_eq)

/-- Squared source norms, not the norm of their possibly cancelling sum, control proper prefixes. The complete path
allowance pays every sewing. -/
theorem prefix_magnitude_bound (sample : PathSources.Sample sources bank)
    (first last : List (Stokes.OrientedEdge patch.count)) (equal : first ++ last = edges)
    {start finish : Fin patch.count} (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish first
      start finish)
    {total : Fraction.Rational} (bounded : Gaussian.Norm.Sum.Basic.gaussianNormSqSum (sources.sources.map (fun source =>
      source.increment localValues)) ≤ total) :
    Data.Gaussian.Norm.Basic.normSq (values finish - values start) ≤ 2 * (sample.bound + (edges.length :
      Fraction.Rational) * total) :=
      by
  have estimatePrefix := Canonical.Norm.Sum.Prefix.prefix_sum_le
    (first.map (fun edge => values edge.finish - values edge.start)) (last.map (fun edge => values edge.finish - values
      edge.start))
  rw [← Map.map_append, equal, Map.length_map, Sample.telescope values path] at estimatePrefix
  have terms := terms_norm_le sample.terms
  have wordEq := congrArg (List.map (fun edge : Stokes.OrientedEdge patch.count => values edge.finish - values
    edge.start)) (cutEdges_eq sample)
  simp only [Map.map_map, Function.comp_def, -eq_self, -iff_self] at wordEq
  rw [wordEq, increment_normSum_eq sample] at terms
  have totalBound := terms.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add le_rfl bounded) (by decide))
  have countEq : sample.terms.length = edges.length := by
    have equal := congrArg List.length (cutEdges_eq sample)
    simpa only [Map.length_map, -eq_self, -iff_self] using equal
  have estimate := estimatePrefix.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalBound
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
  exact estimate.trans_eq (by rw [sample.bound_eq, countEq]; ring1)

end PathSources.Sample
end Purelib.Topology.Surface.Sewing.SewnBoundaryMagnitude

end
