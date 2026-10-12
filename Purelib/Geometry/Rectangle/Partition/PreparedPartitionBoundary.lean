module
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Topology.Polygon.Stokes
public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Data

open Purelib

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.AxisWalks

open Purelib.Topology.Polygon

public section

/-! Exact cancellation of shared sides in a finite rectangular partition.
The exterior keeps the partition cuts and each side's dyadic subdivision. -/

namespace Purelib.Geometry.Rectangle

open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (Gaussian Box)

open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (horizontalBoundary verticalBoundary rectangleBoundary)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Integration
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk)
open Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts (rectangles intervalBox)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

namespace Partition.PreparedPartitionBoundary

/-- The Gaussian sum is additive over concatenation. -/
private theorem sum_append (first last : List PreparedBoxPartitions.Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (first ++ last) = Data.Gaussian.Norm.Sum.Basic.gaussianSum first
      + Data.Gaussian.Norm.Sum.Basic.gaussianSum last := by
  induction first with
  | nil =>
    change Data.Gaussian.Norm.Sum.Basic.gaussianSum last = 0 + Data.Gaussian.Norm.Sum.Basic.gaussianSum last;
      ring1
  | cons head tail ih =>
      change head + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail ++ last) = (head +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum tail) + Data.Gaussian.Norm.Sum.Basic.gaussianSum last
      rw [ih]
      ring1

/-- Reindex the Cartesian rectangle-boundary sum as nested axis sums. -/
private theorem rectangle_sum (primitive : PreparedBoxPartitions.Gaussian → Stokes.PrimitivePoint) (depth : Nat)
    (horizontal vertical : List PreparedAxisPartitions.Interval) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((PreparedRectangleCuts.rectangles horizontal vertical).map
      (PreparedBoxBoundary.rectangleBoundary primitive depth)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (horizontal.map (fun x =>
        Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (vertical.map (fun y => PreparedBoxBoundary.rectangleBoundary primitive depth (PreparedRectangleCuts.intervalBox
          x y))))) := by
  induction horizontal with
  | nil => rfl
  | cons x rest ih =>
      simp only [PreparedRectangleCuts.rectangles, List.Flatten.flatMap_cons, List.Map.map_append, List.Map.map_map] at
        *
      rw [sum_append, ih]
      rfl

/-- Internal horizontal sides cancel along a retained vertical walk.

The remaining terms are the lower and upper horizontal sides and the two vertical side sums. -/
private theorem row_boundary (primitive : PreparedBoxPartitions.Gaussian → Stokes.PrimitivePoint) (depth : Nat)
    (x : PreparedAxisPartitions.Interval) {intervals : List PreparedAxisPartitions.Interval} :
    {first last : PreparedAxisPartitions.Coordinate} → (walk : AxisWalks.IncreasingWalk intervals first last) →
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (walk.edges.map (fun y => PreparedBoxBoundary.rectangleBoundary
      primitive depth (PreparedRectangleCuts.intervalBox x y))) =
      PreparedBoxBoundary.horizontalBoundary primitive depth x.lower x.upper first -
        PreparedBoxBoundary.horizontalBoundary primitive depth x.lower x.upper last +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (walk.edges.map (fun y => PreparedBoxBoundary.verticalBoundary
        primitive depth y.lower y.upper x.upper)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (walk.edges.map (fun y => PreparedBoxBoundary.verticalBoundary
        primitive depth y.lower y.upper x.lower))
  | _, _, .nil _ => by
    simp only [IncreasingWalk.edges, List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum]; ring1
  | _, _, .cons y _ tail => by
      simp only [IncreasingWalk.edges, List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum]
      rw [row_boundary primitive depth x tail]
      simp only [PreparedBoxBoundary.rectangleBoundary, PreparedRectangleCuts.intervalBox, id_eq]
      ring1

/-- Internal vertical sides cancel along a retained horizontal walk.

The result preserves both original axis walks and their dyadically subdivided exterior sides. -/
private theorem columns_boundary (primitive : PreparedBoxPartitions.Gaussian → Stokes.PrimitivePoint) (depth : Nat)
    {vertical horizontal : List PreparedAxisPartitions.Interval} {bottom top : PreparedAxisPartitions.Coordinate}
    (yWalk : AxisWalks.IncreasingWalk vertical bottom top) :
    {first last : PreparedAxisPartitions.Coordinate} → (xWalk : AxisWalks.IncreasingWalk horizontal first last) →
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (xWalk.edges.map (fun x =>
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (yWalk.edges.map (fun y => PreparedBoxBoundary.rectangleBoundary primitive depth
        (PreparedRectangleCuts.intervalBox x y))))) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (xWalk.edges.map (fun x =>
        PreparedBoxBoundary.horizontalBoundary primitive depth x.lower x.upper bottom -
          PreparedBoxBoundary.horizontalBoundary primitive depth x.lower x.upper top)) +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (yWalk.edges.map (fun y => PreparedBoxBoundary.verticalBoundary
        primitive depth y.lower y.upper last)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (yWalk.edges.map (fun y => PreparedBoxBoundary.verticalBoundary
        primitive depth y.lower y.upper first))
  | _, _, .nil _ => by
    simp only [IncreasingWalk.edges, List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum]; ring1
  | _, _, .cons x _ tail => by
      simp only [IncreasingWalk.edges, List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum]
      rw [row_boundary primitive depth x yWalk,
        columns_boundary primitive depth yWalk tail]
      simp only [id_eq]
      ring1

end Partition.PreparedPartitionBoundary

namespace CutPartition

/-- The four exterior sides, segmented at the original partition cuts. -/
@[expose] def boundary
    {box : PreparedBoxPartitions.Box} {points : List PreparedBoxPartitions.Gaussian}
    (partition : CutPartition box points)
    (primitive : PreparedBoxPartitions.Gaussian → Stokes.PrimitivePoint) (depth : Nat) : Gaussian :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (partition.x.intervals.map (fun x =>
    PreparedBoxBoundary.horizontalBoundary primitive depth x.lower x.upper box.yLower -
      PreparedBoxBoundary.horizontalBoundary primitive depth x.lower x.upper box.yUpper)) +
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (partition.y.intervals.map (fun y =>
    PreparedBoxBoundary.verticalBoundary primitive depth y.lower y.upper box.xUpper)) -
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (partition.y.intervals.map (fun y =>
    PreparedBoxBoundary.verticalBoundary primitive depth y.lower y.upper box.xLower))

/-- The sum of cached rectangle boundaries equals the retained segmented exterior boundary. -/
theorem boundary_eq_sum
    {box : PreparedBoxPartitions.Box} {points : List PreparedBoxPartitions.Gaussian}
    (partition : CutPartition box points)
    (primitive : PreparedBoxPartitions.Gaussian → Stokes.PrimitivePoint) (depth : Nat) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (partition.boxes.map (PreparedBoxBoundary.rectangleBoundary primitive
      depth)) = partition.boundary primitive depth := by
  rw [partition.boxes_eq, Geometry.Rectangle.Partition.PreparedPartitionBoundary.rectangle_sum]
  have equal := Geometry.Rectangle.Partition.PreparedPartitionBoundary.columns_boundary primitive depth partition.y.walk
    partition.x.walk
  rw [partition.x.walk_edges, partition.y.walk_edges] at equal
  exact equal

end CutPartition

end Purelib.Geometry.Rectangle
