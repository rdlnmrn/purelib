module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Integration.Path.IncrementAreaComparison
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Normalization

/-!
# Full area cost of replacing the retained arc vertices by chart readings

The finite paired-increment estimate pays every vertex and all cross terms.
Its source bound comes from the original comparison before the polynomial
stage is selected. No endpoint chord replaces the intermediate polygon.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.IncrementArea (Summary pathArea)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment Path)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Reading)

/-- Thirty-two is a nonnegative rational coordinate. -/
private theorem thirty_two_nonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ 32 := by decide +kernel

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor index : Nat} {box :
    Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample} {stage : Nat}

namespace Segment

/-- The two retained endpoint reading errors bound their source-versus-chart increment discrepancy by sixteen times the
target. -/
theorem increment_error (segment : VertexPaths.Segment regular model sample target floor stage) :
    Data.Gaussian.Norm.Basic.normSq (segment.sourceIncrement - segment.chartIncrement) < 16 * target := by
  rw [segment.source_eq, segment.chart_eq,
    show segment.last.sourceValue - segment.first.sourceValue - (segment.last.chartValue - segment.first.chartValue) =
      (segment.last.sourceValue - segment.last.chartValue) - (segment.first.sourceValue - segment.first.chartValue) by
        ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct segment.last.accurate segment.first.accurate)).trans_eq (by ring1))

/-- The actual retained segment's source increment satisfies the cached spatial slope bound. -/
theorem source_bound (segment : VertexPaths.Segment regular model sample target floor stage)
    (bounds : ArcCoarsening.SpatialBounds comparison) (source : UniformReciprocalPrimitives.SourcePrimitive data index)
      :
    Data.Gaussian.Norm.Basic.normSq segment.sourceIncrement ≤ bounds.slope := by
  have firstInside := segment.first.prepared.inside
  have lastInside := segment.last.prepared.inside
  have widthNonnegative := Fraction.Order.Arithmetic.sub_nonneg_direct segment.ordered
  have widthLe : segment.lastParameter - segment.firstParameter ≤ 1 := by
    have bounded := Fraction.Order.Arithmetic.sub_le_sub_direct
      (lastInside.2.trans edge.right.inside.2) (edge.left.inside.1.trans firstInside.1)
    simpa only [(show (1 : InverseRootPolynomial.Coordinate) - 0 = 1 from by decide), -eq_self, -iff_self] using bounded
  have widthSq : (segment.lastParameter - segment.firstParameter) ^ 2 ≤ 1 := by
    simpa only [one_pow, -eq_self, -iff_self] using Fraction.Order.Arithmetic.pow_le_pow_direct widthNonnegative widthLe
      2
  have sourceEq : segment.sourceIncrement = (ArcArea.Sample.capValue sample) segment.lastParameter -
    (ArcArea.Sample.capValue sample) segment.firstParameter := by
    rw [segment.source_eq, segment.last.source_eq, segment.first.source_eq]
    unfold ArcArea.Sample.capValue
    ring1
  rw [sourceEq]
  exact (SpatialBounds.increment_bound bounds source sample firstInside lastInside).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthSq bounds.slope_nonnegative).trans_eq
      (Fraction.Field.mul_one_direct _))

/-- For a target at most one, both retained source and chart increments share a stage-independent magnitude bound. -/
theorem both_bounded (segment : VertexPaths.Segment regular model sample target floor stage)
    (bounds : ArcCoarsening.SpatialBounds comparison) (source : UniformReciprocalPrimitives.SourcePrimitive data index)
    (small : target ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq segment.sourceIncrement ≤ 2 * (bounds.slope + 16) ∧
      Data.Gaussian.Norm.Basic.normSq segment.chartIncrement ≤ 2 * (bounds.slope + 16) := by
  have sourceBound := Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea.Segment.source_bound segment bounds source
  have expanded : bounds.slope ≤ 2 * (bounds.slope + 16) := by
    have nonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ bounds.slope + 32 := add_nonneg bounds.slope_nonnegative
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea.thirty_two_nonnegative
    have ordered : bounds.slope ≤ bounds.slope + (bounds.slope + 32) := le_add_of_nonneg_right nonnegative
    exact ordered.trans_eq (by ring1)
  have errorLe : Data.Gaussian.Norm.Basic.normSq (segment.sourceIncrement - segment.chartIncrement) ≤ 16 :=
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea.Segment.increment_error segment).le.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by decide)).trans_eq
      (Fraction.Field.mul_one_direct _))
  refine ⟨sourceBound.trans expanded, ?_⟩
  rw [show segment.chartIncrement = segment.sourceIncrement - (segment.sourceIncrement - segment.chartIncrement) by
    ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add sourceBound errorLe) (by decide))

end Segment

namespace Path

variable {depth : Nat} {first last : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {before : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Reading regular model sample first target
    floor stage}
  {after : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Reading regular model sample last target
    floor stage}

/-- The complete cached chart polygon satisfies the paid fourth-power segment-count area estimate.

The estimate uses every retained increment and its original source bound, including all finite path cross terms. -/
theorem area_error (path : VertexPaths.Path regular model sample target floor stage depth before after)
    (bounds : ArcCoarsening.SpatialBounds comparison) (source : UniformReciprocalPrimitives.SourcePrimitive data index)
    (positive : 0 < target) (small : target ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (path.source.area - path.chart.area) ≤
      (512 * ((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate) ^ 4 * (bounds.slope + 16)) * target := by
  let pairs := path.segments.map (fun segment => (segment.sourceIncrement, segment.chartIncrement))
  have estimate := IncrementAreaComparison.pathArea_difference_bound pairs
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16) positive.le)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      (add_nonneg bounds.slope_nonnegative (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16))) (by
        intro pair member
        obtain ⟨segment, _, equal⟩ := Map.mem_map.mp member
        rw [← equal]
        exact (Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea.Segment.increment_error segment).le) (by
        intro pair member
        obtain ⟨segment, _, equal⟩ := Map.mem_map.mp member
        rw [← equal]
        exact (Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea.Segment.both_bounded segment bounds source
          small).1) (by
        intro pair member
        obtain ⟨segment, _, equal⟩ := Map.mem_map.mp member
        rw [← equal]
        exact (Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea.Segment.both_bounded segment bounds source
          small).2)
  dsimp only [pairs] at estimate
  simp only [Data.List.Map.map_map, Function.comp_def, Data.List.Map.length_map, -eq_self, -iff_self] at estimate
  rw [← path.sourcePath_eq, ← path.chartPath_eq, ← path.source.area_eq, ← path.chart.area_eq, path.count_eq] at estimate
  exact estimate.trans_eq (by ring1)

end Path
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea
